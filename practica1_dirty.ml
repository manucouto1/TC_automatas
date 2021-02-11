#directory "ocaml-talf/src";;
#load "ocaml-talf/src/talf.cma";;

open Conj;;
open Ergo;;
open Auto;;

let af1 = af_of_file("ocaml-talf/data/ejemplo01.af");;
let af2 = af_of_file("ocaml-talf/data/ejemplo02.af");;
let af3 = af_of_file("ocaml-talf/data/ejemplo03.af");;
let af4 = af_of_file("ocaml-talf/data/ejemplo04.af");;
let af5 = af_of_file("ocaml-talf/data/ejemplo05.af");;
let af6 = af_of_file("ocaml-talf/data/ejemplo06.af");;
let af7 = af_of_file("ocaml-talf/data/ejemplo07.af");;
let af8 = af_of_file("ocaml-talf/data/ejemplo08.af");;

(* Funciones de utilidad 
    - cadena_of_string 
    - cadena_of_file 
    - er_of_string 
    - er_of_file
    - dibuja_af
    - escaner_af : Auto.simbolo list -> Auto.af -> bool
 *)

(* 
 Implementa una función traza_af : Auto.simbolo list -> Auto.af -> bool, o bien
modificando la salida, que no sólo verifique si una cadena de símbolos terminales es aceptada o no por un
autómata finito, sino que además imprima por pantalla todas las configuraciones instantáneas, es decir,
todos los pares de la forma (estados actuales, símbolos pendientes), por los que va pasando el proceso de
reconocimiento de dicha cadena.
 *)

let print_list l = 
  let rec aux x = function 
    | [] -> Printf.printf "%s\n" x
    | h::t -> aux (x^","^h) t 
  in match l with
    | [] -> Printf.printf ""
    | hh::tt -> aux hh tt;;

let get_terminales (Auto.Af (_,_,_,_,x)) = x ;;
let get_estados (Auto.Af (x,_,_,_,_)) = x;;
let get_aristas (Auto.Af (_,_,_,x,_)) = x;;
let get_inicial (Auto.Af (_,_,x,_,_))  = x;;
let get_arco_tupla (Auto.Arco_af (Estado x, Estado y, z)) = (x , y ,z) ;;
let get_arco_estado_destino (Auto.Arco_af (_, x, _)) = x;;
let get_arista_caracter = function | (Terminal x) -> x | (No_terminal x) -> x ;;
let get_automata_tupla (Auto.Af(x,y,z,j,k)) = (x,y,z,j,k);;

  (* | (Auto.Arco_af((Auto.Estado e1),(Auto.Estado x), (Auto.Terminal y))) 
  | (Auto.Arco_af((Auto.Estado e1),(Auto.Estado x), (Auto.No_terminal y))) *)
let get_e_sig et c = function
  | (Auto.Arco_af(e1, x, (Auto.Terminal y))) 
  | (Auto.Arco_af(e1, x, (Auto.No_terminal y))) 
  -> match (c = y && et = e1) with 
    | true -> Some(x)
    | false -> None;;

(* let get_e (Auto.Arco_af((Auto.Estado x),_,_)) = x;; *)

let look_next_state e1 c l = 
  let rec aux = function
    | [] -> None
    | h::t -> match get_e_sig e1 c h with 
      | None -> aux t
      | x -> x 
    in aux l;;

let cut_string_head str = ( (String.make 1 (String.get str 0)), (String.sub str 1 (String.length str -1)));;

let encontrar_indeterminismos pib l =
  let rec aux s2 = function
    | [] -> if (s2 == []) 
      then (conjunto_of_list s2) 
      else (conjunto_of_list s2)
    | h::t -> let ((x, y, z),(x1, y1, z1)) = (get_arco_tupla pib, get_arco_tupla h) in 
      if ((x=x1) && (get_arista_caracter z = get_arista_caracter z1)) 
      then aux (Estado y :: Estado y1 :: s2) t
      else aux s2 t
  in aux [] l;;

let traza_af cadena af = 
  let (Auto.Af(_,_,e1,(Conjunto al), efs)) = af in
  let rec aux et al str = 
    try 
    let Estado(es) = et in (Printf.printf "(%s,%s) \n" es str );
    let (x, y) = cut_string_head str in
      match (look_next_state et x al) with
        | None -> false
        | Some (eNext) -> aux eNext al y
      with e -> (Conj.pertenece et efs)
  in  aux e1 al cadena;;

 (* Dibujar  *)
 Graf.dibuja_af af5;;
 traza_af "ab" af5;;
 traza_af "abaab" af5;;
 traza_af "abacb" af5;;
 traza_af "abab" af5;;
 traza_af "abababa" af5;;
 traza_af "ababsdc" af5;;

 (* Implemente una función afd_of_afn : Auto.af -> Auto.af que reciba como argumento un
autómata finito no determinista, y que devuelva su correspondiente autómata finito determinista.*)

(* TODO falta resolver todos los indeterminismos *)
let afnd1 = Auto.Af
   (Conjunto
     [Auto.Estado "0"; Auto.Estado "1"; Auto.Estado "2"; Auto.Estado "3";
      Auto.Estado "4"],
    Conjunto [Auto.Terminal "a"; Auto.Terminal "b"], Auto.Estado "0",
    Conjunto
     [Auto.Arco_af (Auto.Estado "0", Auto.Estado "1", Auto.Terminal "a");
      Auto.Arco_af (Auto.Estado "0", Auto.Estado "2", Auto.Terminal "a");
      Auto.Arco_af (Auto.Estado "0", Auto.Estado "0", Auto.Terminal "b");
      Auto.Arco_af (Auto.Estado "1", Auto.Estado "1", Auto.Terminal "a");
      Auto.Arco_af (Auto.Estado "1", Auto.Estado "2", Auto.Terminal "b");                                       
      Auto.Arco_af (Auto.Estado "2", Auto.Estado "3", Auto.Terminal "a");
      Auto.Arco_af (Auto.Estado "2", Auto.Estado "0", Auto.Terminal "b");
      Auto.Arco_af (Auto.Estado "3", Auto.Estado "1", Auto.Terminal "a");
      Auto.Arco_af (Auto.Estado "3", Auto.Estado "4", Auto.Terminal "b");
      Auto.Arco_af (Auto.Estado "4", Auto.Estado "4", Auto.Terminal "a");
      Auto.Arco_af (Auto.Estado "4", Auto.Estado "4", Auto.Terminal "b")],
    Conjunto [Auto.Estado "4"]);;


let afnd2 = Auto.Af
  (Conjunto
    [Auto.Estado "0"; Auto.Estado "1"; Auto.Estado "2"; Auto.Estado "3"],
  Conjunto [Auto.Terminal "a"; Auto.Terminal "b"], Auto.Estado "0",
  Conjunto
    [Auto.Arco_af (Auto.Estado "0", Auto.Estado "1", Auto.Terminal "a");
    Auto.Arco_af (Auto.Estado "0", Auto.Estado "2", Auto.Terminal "a");
    Auto.Arco_af (Auto.Estado "2", Auto.Estado "3", Auto.Terminal "b");
    Auto.Arco_af (Auto.Estado "3", Auto.Estado "2", Auto.Terminal "a")],
  Conjunto [Auto.Estado "1"; Auto.Estado "3"]);;


  let nuevo_estado (Conjunto x)  =
    let rec aux s = function 
      | [] -> Estado (s^"}")
      | (Estado h)::t -> aux (s^h) t
    in  aux "{" x;;
  
    let cierres_estado_simbolo (Af (estados, simbolos, _, _, _) as automata) =
      let rec aux s = function
        | [] -> s
        | estado::t -> 
        let rec aux2 s2 = function 
          | [] -> aux s2 t
          | simbolo::tt -> let next = (avanza simbolo (Conjunto [estado]) automata) in
            if(es_vacio next) then aux2 s2 tt else aux2 (agregar (estado, simbolo, next) s2) tt 
        in let Conjunto sl = simbolos in aux2 s sl
      in let Conjunto el = estados in aux (Conjunto []) el;;
  
    let next_target estado cierres =
      let rec aux = function 
        | [] -> None
        | ((e,_,_) as target)::t -> if(e = estado) then Some target else aux t
      in let Conjunto lc = cierres in aux lc;;
  
    let crear_nuevos_estados (Conjunto l) =
      let rec aux c = function 
        | [] -> c
        | (_,_,Conjunto es)::t -> 
          let rec aux2 s = function 
            | [] -> aux (agregar (Estado s) c) t
            | (Estado h)::tt -> aux2 (s^h) tt
          in aux2 "" es
      in aux (Conjunto []) l;;
  
  
    let afd_of_afn (Af (estados, simbolos, inicial, aristas, finales) as automata) =
      let cierres = cierres_estado_simbolo automata in
      let nestados = crear_nuevos_estados cierres in 
      let rec aux ca c = function
        | [] -> (Af (nestados, simbolos, inicial, ca, Conjunto []))
        | (pib, l)::t -> 
          let rec aux2 ccaa cc s = function
            | [] -> aux ccaa cc s
            | hh::tt -> 
              match (next_target hh cc) with
                | None -> aux2 ccaa cc s tt
                | Some ((x,y,z) as tg) ->
                  let cc = suprimir tg cc in 
                  let ne = nuevo_estado z in 
                  let na = Arco_af(pib, ne, y) in
                    aux2 (agregar na ccaa) cc ((ne, z)::s) tt
          in let Conjunto x = l in aux2 ca c t x
      in aux (Conjunto []) cierres [(inicial, Conjunto [inicial])];;
      

(* 
[Ejercicio opcional] Implemente una función afd_of_afne : Auto.af -> Auto.af que reciba
como argumento un autómata finito no determinista con épsilon-transiciones, y que devuelva su
correspondiente autómata finito determinista.
 *)
