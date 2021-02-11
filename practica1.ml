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
    - escaner_af : Auto.simbolo list -> Auto.af -> bool *)

(* Implementa una función traza_af : Auto.simbolo list -> Auto.af -> bool, o bien
  modificando la salida, que no sólo verifique si una cadena de símbolos terminales es aceptada o no por un
  autómata finito, sino que además imprima por pantalla todas las configuraciones instantáneas, es decir,
  todos los pares de la forma (estados actuales, símbolos pendientes), por los que va pasando el proceso de
  reconocimiento de dicha cadena. *)

let rec print_estado_cadenas es cads = 
  let rec aux x = function 
    | [] -> Printf.printf "%s)\n" x
    | Terminal h::t -> aux (x^h) t 
    | No_terminal h::t -> aux (x^h) t 
  in match es with
    | [] -> Printf.printf ""
    | (Estado hh)::tt -> aux ("("^hh^",") cads; print_estado_cadenas tt cads;;

let print_conf_inst es cads = 
  let rec aux x = function 
    | [] -> Printf.printf "%s)\n" x
    | Terminal h::t -> aux (x^h) t 
    | No_terminal h::t -> aux (x^h) t 
  in let rec aux2 x = function 
    | [] -> aux (x^"},") cads;
    | (Estado h)::t -> aux2 (x^","^h) t
  in match es with
    | [] -> Printf.printf ""
    | (Estado h)::t -> aux2 ("({"^h) t;;


let epsilon_cierre estados (Af (_, _, _, Conjunto arcos, _)) =
  let rec aux cambio cierre arcos_pendientes = function
    [] ->
      if cambio then
        aux false cierre [] arcos_pendientes
      else
        cierre
    | (Arco_af (origen, destino, Terminal "") as arco) :: t ->
      if (pertenece origen cierre) then
        aux true (agregar destino cierre) arcos_pendientes t
      else
        aux cambio cierre (arco :: arcos_pendientes) t
    | _ :: t ->
        aux cambio cierre arcos_pendientes t
  in
    aux false estados [] arcos ;;


let avanza simbolo estados (Af (_, _, _, Conjunto arcos, _)) =
  let rec aux destinos = function
    | [] -> destinos
    | Arco_af (origen, destino, s) :: t ->
        if (s = simbolo) && (pertenece origen estados) then
            aux (agregar destino destinos) t
        else
            aux destinos t
  in aux conjunto_vacio arcos;;

let traza_af cadena (Af (_, _, inicial, _, finales) as a) =
  let rec aux = function
      (Conjunto [], _) ->
        false
    | (((Conjunto listActuales) as actuales), []) -> 
      (print_conf_inst listActuales []);
      (not (es_vacio (interseccion actuales finales))); 
    | (((Conjunto listActuales) as actuales), ((simbolo :: t) as simList)) -> 
      (print_conf_inst listActuales simList);
      aux ((epsilon_cierre (avanza simbolo actuales a) a), t)
  in
    aux ((epsilon_cierre (Conjunto [inicial]) a), cadena);;

let simlist1 = [Terminal "a";Terminal "a";Terminal "a"; Terminal "a"; Terminal "a"];;
let simlist2 = [Terminal "c";Terminal "b";Terminal "a"; Terminal "b"];;
let simlist3 = [Terminal "a";Terminal "a";Terminal "b" ];;
let simlist4 = [Terminal "a";Terminal "b";Terminal "b"; Terminal "a"];;
let simlist5 = [Terminal "a";Terminal "b";Terminal "c"; Terminal "d"];;
let simlist6 = [Terminal "a"];;

(* EPSILON_CIERRE ->  parte de un conjunto de estados y devuelve el conjunto de estados alcanzables
    con epsilon transiciones y el caracter que se le pasa *)

traza_af simlist1 af1;;
traza_af simlist2 af1;;
traza_af simlist3 af1;;
traza_af simlist4 af1;;
traza_af simlist5 af1;;
traza_af simlist6 af1;;

Graf.dibuja_af af1;;

 (* Implemente una función afd_of_afn : Auto.af -> Auto.af que reciba como argumento un
autómata finito no determinista, y que devuelva su correspondiente autómata finito determinista.*)

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

let partition piv l = 
  let rec aux left right = function
      | [] -> (left, right)
      | h::t -> if h < piv then aux (h::left) right t else aux left (h::right) t
  in aux [] [] l;;

let rec qsort_qt = function
    | [] | _::[] as l -> l
    | h::t ->  let left, right = partition h t 
               in qsort_qt left @ (h::qsort_qt right);;

let rec qsort = function
    | [] | _::[] as l -> l
    | h::t ->  let right, left = List.partition ((<=) h) t 
               in qsort_qt left @ (h::qsort right);;

let nuevo_estado (Conjunto x)  =
  let rec aux s = function 
    | [] -> Some(Estado (s))
    | (Estado h)::t -> aux (s^h) t
  in 
    match (qsort x) with 
      | [] -> None
      | (Estado h)::t -> aux h t;;

let obtener_destinos agregados (Af (_,(Conjunto simbolos), _, _, _) as automata) =
  let rec aux s = function
    | [] -> s
    | h::t ->
      let ncag = avanza h agregados automata in
      match (nuevo_estado ncag) with 
        | None -> aux s t
        | Some(ne) -> aux (agregar (ne,ncag,h) s) t
  in aux (Conjunto []) simbolos;;

let obtener_arcos origen (Conjunto destinos) = 
  let rec aux s1 s2 = function 
    | [] -> Conjunto s1, Conjunto s2 
    | (ne,ncag,h)::t -> 
      let s11 = (ne,ncag)::s1 in
      let s22 = (Arco_af(origen, ne, h))::s2 in 
        aux s11 s22 t
  in aux [] [] destinos;;

let obtener_nuevos_finales (Conjunto destinos) (Af (_,_, _, _, finales)) =
  let rec aux nf = function 
    | [] -> nf 
    | (ne, Conjunto ncag, h)::t -> 
      let rec aux2 = function 
        | [] -> aux nf t
        | hh::tt -> 
          if(pertenece hh finales) then 
            aux (agregar ne nf) t
          else 
            aux nf t
      in aux2 ncag          
  in aux (Conjunto[]) destinos;;

let afd_of_afn (Af (estados, simbolos, inicial, aristas, finales) as automata) =
  let rec aux ePro aPro fPro = function 
    | [] -> (Af (ePro, simbolos, inicial, aPro, fPro))
    | (e,cag)::t -> 
      if(pertenece e ePro) then
        aux ePro aPro fPro t
      else 
        let dest = obtener_destinos cag automata in
        let nce, naPro = obtener_arcos e dest in 
        let nfPro = obtener_nuevos_finales dest automata in
          aux (agregar e ePro) (union aPro naPro) (union fPro nfPro) (list_of_conjunto (union (Conjunto t) nce))
  in aux (Conjunto []) (Conjunto []) (Conjunto [])  [(inicial, Conjunto [inicial])];;

  Graf.dibuja_af (afnd1);;
  Graf.dibuja_af (afd_of_afn afnd1);;
  Graf.dibuja_af (afnd2);;
  Graf.dibuja_af (afd_of_afn afnd2);; 

(* [Ejercicio opcional] Implemente una función afd_of_afne : Auto.af -> Auto.af que reciba
como argumento un autómata finito no determinista con épsilon-transiciones, y que devuelva su
correspondiente autómata finito determinista. *)

let delta_prima estado simbolo automata = 
  let cierre1 = epsilon_cierre (Conjunto [estado]) automata in
  let cierre2 = avanza simbolo cierre1 automata in epsilon_cierre (cierre2) automata;;

let generar_arcos_destino estado (Conjunto destinos) caracter arcos =
  let rec aux arcos_f = function 
    | [] -> arcos_f
    | destino::t -> aux (agregar (Arco_af( estado, destino, caracter)) arcos_f) t 
  in aux arcos destinos;;

let afn_of_afne (Af (Conjunto estados, Conjunto simbolos, inicial, _, finales) as automata) = 
  let rec aux ar_nuevas = function
    | [] -> (Af (Conjunto estados, Conjunto simbolos, inicial, ar_nuevas, finales))
    | estado::t -> let rec aux2 ar_n2 = function
      | [] -> aux ar_n2 t
      | simbolo::tt -> let destinos = delta_prima estado simbolo automata 
        in aux2 (generar_arcos_destino estado destinos simbolo ar_n2) tt
    in aux2 ar_nuevas simbolos
  in aux (Conjunto []) estados;;  

let afd_of_afne afne = afd_of_afn (afn_of_afne afne);;

(* Ejemplo Clase *)
let afne = Auto.Af
(Conjunto
  [Auto.Estado "0"; Auto.Estado "1"; Auto.Estado "2"; Auto.Estado "3"; Auto.Estado "4"],
Conjunto [Auto.Terminal "a"; Auto.Terminal "b"], Auto.Estado "0",
Conjunto
  [Auto.Arco_af (Auto.Estado "0", Auto.Estado "1", Auto.Terminal "");
  Auto.Arco_af (Auto.Estado "0", Auto.Estado "3", Auto.Terminal "a");
  Auto.Arco_af (Auto.Estado "1", Auto.Estado "2", Auto.Terminal "a");
  Auto.Arco_af (Auto.Estado "1", Auto.Estado "2", Auto.Terminal "");
  Auto.Arco_af (Auto.Estado "3", Auto.Estado "4", Auto.Terminal "b");
  Auto.Arco_af (Auto.Estado "4", Auto.Estado "1", Auto.Terminal "");
  Auto.Arco_af (Auto.Estado "4", Auto.Estado "0", Auto.Terminal "b")
  ],
Conjunto [Auto.Estado "2"]);;


Graf.dibuja_af (afne);;
Graf.dibuja_af (afn_of_afne afne);;
Graf.dibuja_af (afd_of_afne afne);;