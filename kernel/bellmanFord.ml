open Univ
open Util
       
exception Todo

let error_inconsistency o u v (p:explanation option) =
  raise (UniverseInconsistency (o,Universe.make u,Universe.make v,p))

            
(* open Universe *)

module UMap = LMap

type t = ((Level.t * int) list) UMap.t

type universes = t

type 'a check_function = universes -> 'a -> 'a -> bool

let check_leq : universe check_function
  = raise Todo
let check_eq : universe check_function
  = raise Todo
let check_eq_level : universe_level check_function
  = raise Todo

(** The empty graph of universes *)
let empty_universes : universes
  = UMap.empty

(** The initial graph of universes: Prop < Set *)
let initial_universes : universes
  = let g = empty_universes in
    let g = UMap.add Level.prop [(Level.set , -1 )] g in
    UMap.add Level.set [] g

let is_initial_universes : universes -> bool
  = raise Todo

let sort_universes : universes -> universes
  = raise Todo


(* val add_edge : Level.t -> Level.t -> int -> graph -> graph *)
let add_edge u v w g =
  (* todo: tester si v déjà là *)
  UMap.modify u (fun _ l -> (v, w) :: l) g


exception AlreadyDeclared

(* val add_universe : universe_level -> bool -> universes -> universes *)
let add_universe l b g =
  if UMap.mem l g then
    raise AlreadyDeclared
  else
    add_edge (if b then Level.set else Level.prop) l (-1) g

             
exception NegativeCycleDetected

(* val detect_neg_cycle : graph -> graph *)
let detect_neg_cycle g =
  let s = Level.prop in
  let d : (int ref) UMap.t = UMap.empty in   (* distance from s to u *)
  let d = UMap.add s (ref 0) d in
  let n = UMap.cardinal g in
  for _ = 1 to n - 1 do
    UMap.iter (fun u l ->
        List.iter (fun (v, w) ->
            let du = UMap.get u d in
            let dv = UMap.get v d in
            if !dv > !du + w
            then dv := !du + w
          ) l) g
  done;
  UMap.iter (fun u l ->
      List.iter (fun (v, w) ->
          let du = UMap.get u d in
          let dv = UMap.get v d in
          if !dv > !du + w
          then raise NegativeCycleDetected
        ) l) g;
  g

             
let enforce_constraint : univ_constraint -> universes -> universes
  = function
  | (u, Le n, v) -> add_edge u v n %> detect_neg_cycle
  | (u, Eq, v) -> add_edge u v 0 %> add_edge v u 0 %> detect_neg_cycle

let merge_constraints c g =
  Constraint.fold enforce_constraint c g

let check_constraint g (l,d,r) =
  raise Todo

let check_constraints c g =
  Constraint.for_all (check_constraint g) c

let check_eq_instances =
  raise Todo

open Pp

let pr_arc prl (u, (v, w)) =
  prl u  ++ str " <= " ++ prl v ++ str " + " ++ int w ++ fnl ()

        
let pr_universes prl g =
  let graph = UMap.fold (fun u a l -> (u,a)::l) g [] in
  prlist (pr_arc prl) graph

let dump_universes =
  raise Todo
        
let () =
  (* let g *)
  print_string "toto"
