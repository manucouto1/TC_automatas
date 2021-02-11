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

let nuevo_estado (Conjunto x)  =
  let rec aux s = function 
    | [] -> Estado (s)
    | (Estado h)::t -> aux (s^h) t
  in  aux "" x;;

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

  let next_targets estado cierres =
    let rec aux s = function 
      | [] -> s
      | ((e,_,_) as target)::t -> if(e = estado) then aux (target::s) t else aux s t
    in let Conjunto lc = cierres in aux [] lc;;

  let crear_nuevos_estados (Conjunto l) =
    let rec aux c = function 
      | [] -> c
      | (_,_,Conjunto es)::t -> 
        let rec aux2 s = function 
          | [] -> aux (agregar (Estado s) c) t
          | (Estado h)::tt -> aux2 (s^h) tt
        in aux2 "" es
    in aux (Conjunto []) l;;

  let obtener_arcos pib arcos stack1 stack2 =
    let rec aux ar stack1 conjunto = function
      | [] -> let rec aux3 aar sst1 = function
        | [] -> aar, sst1
        | (simb, nodos)::tail -> 
          let ne = nuevo_estado nodos in
          let na = Arco_af(pib, ne, simb) in  
            aux3 (agregar na aar) ((ne,nodos)::sst1) tail
        in aux3 ar stack1 (list_of_conjunto conjunto)
      | (ne,c,cn)::t -> 
        if (pertenece (c,cn) conjunto) 
          then
            aux ar stack1 conjunto t
          else 
            let rec aux2 = function 
              | [] -> aux ar stack1 (agregar (c,cn) conjunto) t
              | (cc,ccn)::tt -> 
                if(c = cc) then 
                    if (incluido cn ccn) then 
                      aux ar stack1 conjunto t
                    else if (incluido ccn cn) then
                      aux ar stack1 (agregar (c,cn) (suprimir (cc,ccn) conjunto))t
                    else 
                      aux2 tt
                  else 
                    aux2 tt
            in let Conjunto candidatos = conjunto in aux2 candidatos
    in aux arcos stack1 (Conjunto []) stack2;;

  (* Necesito obtener el conjunto mas grande  *)
  
  let procesar_pib pib cierres arcos stack relaciones =
    let rec aux s s2 = function
      | [] -> 
        if(s2 = [])  then 
          arcos, s
        else 
          obtener_arcos pib arcos s s2
      | hh::tt -> 
        let rec aux2 stack2 = function
          | [] -> aux s stack2 tt
          | (x,y,z)::tail ->  
            let ne = nuevo_estado z in 
              aux2 ((ne, y, z)::stack2) tail
        in aux2 s2 (next_targets hh cierres) 
    in aux stack [] relaciones

  let afd_of_afn (Af (estados, simbolos, inicial, aristas, finales) as automata) =
    let cierres = cierres_estado_simbolo automata in
    let nestados = agregar inicial (crear_nuevos_estados cierres) in 
    let rec aux nce ca = function
      | [] -> (Af (nestados, simbolos, inicial, ca, Conjunto []))
      | (pib, l)::t -> 
        if (pertenece pib nce) 
          then  
            let nnce = (suprimir pib nce) in
            let Conjunto relaciones = l in 
            let pca, ps = procesar_pib pib cierres ca t relaciones in
              aux nnce pca ps
          else 
            aux nce ca t
    in aux nestados (Conjunto []) [(inicial, Conjunto [inicial])];;
    
(* TODO - Generar Aristas *)
(* TODO - Generar Estados finales coherentes *)
  Graf.dibuja_af (afnd1);;
  Graf.dibuja_af (afd_of_afn afnd1);;
  Graf.dibuja_af (afnd2);;
  Graf.dibuja_af (afd_of_afn afnd2);;
  (* 
  avanza (Terminal "a") (Conjunto [Estado "1"; Estado "2"; Estado "4"]) afn ;
  avanza (Terminal "b") (Conjunto [Estado "1"; Estado "2"; Estado "4"]) afn ; 
  *)


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


(* BACK UP 2 *)

let nuevo_estado (Conjunto x)  =
  let rec aux s = function 
    | [] -> Estado (s)
    | (Estado h)::t -> aux (s^h) t
  in  aux "" x;;

let fusionar ((Conjunto le) as estados) (Af (ei, _,_, ((Conjunto la) as ari), ef)) =
  let ne = nuevo_estado estados in
  let rec aux est estf ar = function 
    | [] -> 
      if (igual estf ef) 
        then 
          ((agregar ne est), ar, estf)
        else 
          ((agregar ne est), ar, (agregar ne estf))
    | h::t -> 
      let rec aux2 arr = function 
       | [] -> aux (suprimir h est) (suprimir h estf) arr t 
       | (Arco_af(x,y,z))::tt -> 
        let na = match (pertenece x estados, pertenece y estados) with 
          | true,false -> (Arco_af(ne,y,z))
          | false, true -> (Arco_af(x,ne,z))
          | true, true -> (Arco_af(ne,ne,z))
          | false, false ->  (Arco_af(x,y,z))
        in aux2 (agregar na arr) tt
      in aux2 ar la
  in 
    if (le = []) then 
      (ei, ari, ef)
    else
      aux ei ef (Conjunto []) le;;

  (* let (x,y,z) = fusionar (Conjunto []) afn;; *)

  let afd_of_afn (Af (((Conjunto le)), ((Conjunto ls) as simbolos), inicial, arcos, finales) as automata) =
    let rec aux at = function 
     |  [] -> at
     | h::t -> 
      let rec aux2 at2 = function 
        | [] -> aux at2 t
        | hh::tt -> 
          let ldestinos = avanza hh (Conjunto[h]) at2 in
          let nest, narc, nf = fusionar ldestinos at2 in
          let nat =  Af(nest, simbolos, inicial, narc, nf) in aux2 nat tt 
      in aux2 at ls
    in aux automata le;;