open Pp
open Util
open Univ
       
exception Todo of string

let error_inconsistency o u v (p:explanation option) =
  raise (UniverseInconsistency (o,Universe.make u,Universe.make v,p))

            
(* open Universe *)

module UMap = LMap

type 'a matrix = ('a UMap.t) UMap.t

(* Invariants : *)
(*      1 - no negative cycle *)
(*      2 - dist u v is the min dist between u and v *)
(*      3 - max one edge between two nodes *)
(*      4 - all levels have an edge from Prop to them (except Prop!) *)
type t = { graph : int matrix ; dist : (int ref) matrix }

type universes = t


(* val check_universes_invariants : universes -> unit *)
let check_universes_invariants g =
  ()

let big_rank = 10000000

exception NegativeCycleDetected

let nodes (g : 'a matrix) : LSet.t =
  UMap.fold (fun u vs -> LSet.union (UMap.domain vs)) g (UMap.domain g)
  
  (* LSet.add Level.prop ( *)
  (*            try UMap.domain (UMap.find Level.prop g) with *)
  (*            | Not_found -> LSet.empty) *)


let print_dist (d : ((int ref) UMap.t) UMap.t) : unit =
  Feedback.msg_info (str "print_dist");
  UMap.iter (fun u vs ->
      UMap.iter (fun v w ->
          Feedback.msg_info (str "d(" ++ Level.pr u ++ str "," ++ Level.pr v ++ str ") = " ++ int !w)) vs) d
  
let recompute_dist (g : int matrix) : universes =
  let nodes = nodes g in
  let dist : (int ref) matrix
    = UMap.bind (fun u ->
          UMap.bind (fun v ->
              ref (try UMap.find v (UMap.find u g)
                   with Not_found -> big_rank)
            ) nodes) nodes in
  (* print_dist dist; *)
  let w u v =
    UMap.find v (UMap.find u dist) in
  LSet.iter (fun uk ->
  LSet.iter (fun ui ->
  LSet.iter (fun uj ->
      let r  = w ui uj in
      r := min !r (!(w ui uk) + !(w uk uj))
    ) nodes) nodes) nodes;
  (* print_dist dist; *)
  { graph = g ; dist = dist }

(* big_rank if there is no path *)
let dist (g : universes) u v =
  try !(UMap.find v (UMap.find u g.dist)) with
  | Not_found -> big_rank

(* val insert_edge : Level.t -> Level.t -> int -> graph -> graph *)
let insert_edge u v w (g : universes) : universes =
  Feedback.msg_info (str "Inserting (" ++ Level.pr u ++ str "," ++ Level.pr v ++ str "," ++ int w ++ str ").");
  if dist g v u < -w then
    raise NegativeCycleDetected
  else
    (* u has some successors *)
    try let vs = UMap.find u g.graph in
        (* there were yet an edge between u and v *)
        try let wg = UMap.find v vs in
            if wg <= w then g
            else
              let g' = UMap.update u (UMap.add v w vs) g.graph
              in recompute_dist g'
        (* there were no edge between u and v *)
        with
        | Not_found ->
           let g' = UMap.update u (UMap.add v w vs) g.graph
           in recompute_dist g'
    (* u has not any successor *)
    with Not_found -> 
         let g' = UMap.add u (UMap.singleton v w) g.graph in
         recompute_dist g'


exception AlreadyDeclared

(* val add_universe : universe_level -> bool -> universes -> universes *)
let add_universe l b (g : universes) =
  (* if UMap.mem l (UMap.find Level.prop g.graph) then *)
  if LSet.mem l (nodes g.graph) then
    raise AlreadyDeclared
  else
    insert_edge (if b then Level.set else Level.prop) l (-1) g

(* val detect_neg_cycle : graph -> graph *)
(* let detect_neg_cycle g = *)
(*   let s = Level.prop in *)
(*   let d : (int ref) UMap.t = UMap.empty in   (\* distance from s to u *\) *)
(*   let d = UMap.add s (ref 0) d in *)
(*   let n = UMap.cardinal g in *)
(*   for _ = 1 to n - 1 do *)
(*     UMap.iter (fun u l -> *)
(*         List.iter (fun (v, w) -> *)
(*             let du = UMap.get u d in *)
(*             let dv = UMap.get v d in *)
(*             if !dv > !du + w *)
(*             then dv := !du + w *)
(*           ) l) g *)
(*   done; *)
(*   UMap.iter (fun u l -> *)
(*       List.iter (fun (v, w) -> *)
(*           let du = UMap.get u d in *)
(*           let dv = UMap.get v d in *)
(*           if !dv > !du + w *)
(*           then raise NegativeCycleDetected *)
(*         ) l) g; *)
(*   g *)


(** First, checks on universe levels *)
                                                    
let check_equal g u v =
  dist g u v = 0 && dist g v u = 0
    
let check_eq_level g u v = u == v || check_equal g u v

(* check if u <= v + n *)
let check_smaller g n u v =
  (* let b = *)
  if n = 0 then
    Level.is_prop u
    || (Level.is_set u && not (Level.is_prop v))
    || dist g u v <= 0
  else
    (* (Feedback.msg_info (str "dist: " ++ int (dist g u v)); *)
    dist g u v <= n
    (* ) in Feedback.msg_info (str "ckeck_smaller (" ++ Level.pr u ++ str ", " ++ Level.pr v ++ str ", " ++ int n ++ str "): " ++ bool b); b *)

(** Then, checks on universes *)

type 'a check_function = universes -> 'a -> 'a -> bool

let check_smaller_expr g n (u,m) (v,m') =
  check_smaller g (m' - m + n) u v

let exists_bigger g n ul l =
  Universe.exists (fun ul' -> 
    check_smaller_expr g n ul ul') l

let real_check_leq g n u v =
  Universe.for_all (fun ul -> exists_bigger g n ul v) u
    
let check_leq g u v =
  Universe.equal u v ||
    is_type0m_univ u ||
    real_check_leq g 0 u v

let check_eq_univs g l1 l2 =
  real_check_leq g 0 l1 l2 && real_check_leq g 0 l2 l1

let check_eq g u v =
  Universe.equal u v || check_eq_univs g u v


(** The empty graph of universes *)
let empty_universes0 : universes
  = { graph = (* UMap.add Level.prop UMap.empty *) UMap.empty; dist = UMap.empty }

(** The initial graph of universes: Prop < Set *)
let initial_universes : universes =
  (* insert_edge Level.set Level.prop 1 *)
              (insert_edge Level.prop Level.set (-1) empty_universes0)

let empty_universes = initial_universes
              
let is_initial_universes (g : universes) : bool =
  UMap.equal (UMap.equal (==)) g.graph initial_universes.graph

let enforce_constraint : univ_constraint -> universes -> universes
  (* = function *)
  (* | (u, Le, v) -> insert_edge u v 0 *)
  (* | (u, Lt, v) -> insert_edge u v (-1) *)
  (* | (u, Eq, v) -> insert_edge u v 0 %> insert_edge v u 0 *)
  = fun cst g -> match cst with
    | (u,Lt,v) -> Feedback.msg_info (str "Enforce (" ++ Level.pr u ++ str "," ++ Level.pr v ++ str ", <= )."); insert_edge u v (-1) g
    | (u,Le,v) -> Feedback.msg_info (str "Enforce (" ++ Level.pr u ++ str "," ++ Level.pr v ++ str ", < )."); insert_edge u v 0 g
    | (u,Eq,v) -> Feedback.msg_info (str "Enforce (" ++ Level.pr u ++ str "," ++ Level.pr v ++ str ", = )."); insert_edge u v 0 (insert_edge v u 0 g)

let merge_constraints c g =
  (* Feedback.msg_info (str "Merge " ++ (pr_constraints Level.pr c)); *)
  Constraint.fold enforce_constraint c g

let check_constraint g (l,d,r) =
  match d with
  | Eq -> check_equal g l r
  | Le -> check_smaller g 0 l r
  | Lt -> check_smaller g (-1) l r

let check_constraints c g =
  Constraint.for_all (check_constraint g) c

                     
let constraints_of_universes (g : universes) : constraints =
  let constraints_of u v w =
    let typ = match w with
      | -1 -> Lt
      | 0 -> Le
      | _ -> failwith "pas possble" (* todo *)
    in Constraint.add (u, typ, v)
  in
  UMap.fold (fun u vs ->
      UMap.fold (fun v w -> constraints_of u v w) vs) g.graph
            Constraint.empty


let sort_universes : universes -> universes
  = fun g -> g (* todo *)

             

             



let check_eq_instances g t1 t2 =
  let t1 = Instance.to_array t1 in
  let t2 = Instance.to_array t2 in
  t1 == t2 ||
    (Int.equal (Array.length t1) (Array.length t2) &&
        let rec aux i =
          (Int.equal i (Array.length t1)) || (check_eq_level g t1.(i) t2.(i) && aux (i + 1))
        in aux 0)

let pr_arc prl (u, v, w) =
  prl u  ++ str " <= " ++ prl v ++ str " + " ++ int w ++ fnl ()

        
let pr_universes prl (g : universes) =
  let graph = UMap.fold (fun u lu l ->
                  UMap.fold (fun v w l -> (u, v, w) :: l) lu l)
                        g.graph [] in
  prlist (pr_arc prl) graph

let dump_universes output g =
  let dump_arc u v w =
    let typ = match w with
      | -1 -> Lt
      | 0 -> Le
      | _ -> failwith "pas possble2" (* todo *)
    in output typ (Level.to_string u) (Level.to_string v)
  in
  UMap.iter (fun u vs ->
      UMap.iter (fun v w -> dump_arc u v w) vs) g.graph


(** Profiling *)

let merge_constraints = 
  if Flags.profile then 
    let key = Profile.declare_profile "merge_constraints" in
      Profile.profile2 key merge_constraints
  else merge_constraints
let check_constraints =
  if Flags.profile then
    let key = Profile.declare_profile "check_constraints" in
      Profile.profile2 key check_constraints
  else check_constraints

let check_eq = 
  if Flags.profile then
    let check_eq_key = Profile.declare_profile "check_eq" in
      Profile.profile3 check_eq_key check_eq
  else check_eq

let check_leq = 
  if Flags.profile then 
    let check_leq_key = Profile.declare_profile "check_leq" in
      Profile.profile3 check_leq_key check_leq
  else check_leq
