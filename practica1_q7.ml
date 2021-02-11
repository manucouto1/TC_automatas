#directory "ocaml-talf/src";;
#load "ocaml-talf/src/talf.cma";;

open Conj;;
open Ergo;;
open Auto;;

(* implentar una función es_afne: Auto.af -> bool, que reciva un automata finito como
Parámetro de entrada y devuelva true si se encuentra con algún epsilon transición o false si no *)

(* Esta función lee un automata de un fichero de texto *)
let af1 = af_of_file("ocaml-talf/data/ejemplo01.af");;
let af2 = af_of_file("ocaml-talf/data/ejemplo02.af");;
let af3 = af_of_file("ocaml-talf/data/ejemplo03.af");;
let af4 = af_of_file("ocaml-talf/data/ejemplo04.af");;
let af5 = af_of_file("ocaml-talf/data/ejemplo05.af");;
let af6 = af_of_file("ocaml-talf/data/ejemplo06.af");;
let af7 = af_of_file("ocaml-talf/data/ejemplo07.af");;
let af8 = af_of_file("ocaml-talf/data/ejemplo08.af");;

let get_arcos_list (Auto.Af (_,_,_,(Conjunto x),_)) = x ;;

let get_arco_caracter = function
  | (Auto.Arco_af(_,_,(Auto.Terminal x))) -> x
  | (Auto.Arco_af(_,_,(Auto.No_terminal x))) -> x ;;

let es_afne x = 
  let rec aux = function
    | [] -> false;
    | h::t -> match (get_arco_caracter h) with "" -> true | _ -> aux t 
  in aux(get_arcos_list x);;

(* Validado que devuelve true para af1 y false para af2 *)
es_afne af1;;
es_afne af2;;

(* Implemente una función es_afn : Auto.af -> bool que reciba como argumento un autómata
finito, y que devuelva true si se trata de un autómata que presenta algún tipo de no determinismo
(excepto épsilon-transiciones), o false en caso contrario. *)
let afnd1 =
  Auto.Af
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

let get_origin_char = function
    (Auto.Arco_af((Auto.Estado y),_,(Auto.Terminal x))) -> (x^y)
  | (Auto.Arco_af((Auto.Estado y),_,(Auto.No_terminal x))) -> (x^y) ;;

let es_afn x = 
  let rec aux c = function
    | [] -> false
    | h::t -> match get_arco_caracter h with
      | "" -> aux c t
      | _  -> match (pertenece (get_origin_char h) c) with
        | true -> true
        | false -> aux (agregar (get_origin_char h) c) t 
  in aux (Conjunto []) (get_arcos_list x);;

(* Valido que af1 es false y afnd1 es true *)
es_afn af1;;
es_afn afnd1;;

  (* Implemente una función es_afd : Auto.af -> bool que reciba como argumento un autómata
finito, y que devuelva true si se trata de un autómata totalmente determinista, o false en caso contrario. *)

let es_afd x =
  let rec aux c = function
    | [] -> true
    | h::t -> match get_arco_caracter h with
      | "" -> false
      | _  -> match (pertenece (get_origin_char h) c) with
        | true -> false
        | false -> aux (agregar (get_origin_char h) c) t 
  in aux (Conjunto []) (get_arcos_list x);;

(* Valido que af1 es nodeterminista y af2 es no determinista *)
es_afd af1;;
es_afd af2;;


(*  *)