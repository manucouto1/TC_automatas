#directory "ocaml-talf/src";;
#load "ocaml-talf/src/talf.cma";;

open Conj;;
open Ergo;;
open Auto;;

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

let fusionar_arcos pib arcos stack stack2 = 
  let rec aux c = function
    | [] -> 
      let rec aux3 na ns = function 
        | [] -> na, ns
        | (a,c)::tail -> 
          let ne = nuevo_estado c in
          let nns = (ne,c) in 
          let nna = Arco_af(pib, ne, a) in
            aux3 (agregar nna na) (nns::ns) tail
      in aux3 arcos stack c
    | (arista, destinos)::t -> 
      let rec aux2 s = function
        | [] -> aux ((arista, destinos)::s) t 
        | (a,d)::tt -> 
        if(a = arista) then
          aux2 ((a, (union destinos d))::s)  tt        
        else 
          aux2 ((a,d)::s) tt
      in aux2 [] c
  in aux [] stack2;;

let procesar_pib pib cierres arcos stack relaciones =
  let rec aux s2 = function
    | [] -> 
      if(s2 = [])  then 
        arcos, stack
      else 
        fusionar_arcos pib arcos stack s2
    | hh::tt -> 
      let rec aux2 stack2 = function
        | [] -> aux stack2 tt
        | (x,arista, destinos)::tail ->  aux2 ((arista, destinos)::stack2) tail
      in aux2 s2 (next_targets hh cierres) 
  in aux [] relaciones

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