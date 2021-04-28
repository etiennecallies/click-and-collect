(*** Backward proof search in LL (LLF) ***)

open Sequent
open Proof

type llf_rule =
  | One_intro
  | Top_intro
  | Bottom_intro
  | Par_intro
  | With_intro
  | Tensor_intro of formula list * formula list
  | Plus_left_intro
  | Plus_right_intro
  | Ofcourse_intro
  | Whynot_intro
  | Axiom_central
  | Axiom_exponential
  | Focusing_central of formula * formula list
  | Focusing_exponential of formula
  | Async_on_pos
  | Sync_on_neg

module Set_formula =
  Set.Make(struct type t = formula let compare = compare end)

type llf_sequent =
  | Async of Set_formula.t * formula list * formula list
  | Sync of Set_formula.t * formula list * formula

type llf_proof =
  | Node of llf_sequent * llf_rule * llf_proof list
  | Null

(* [is_async f] checks if [f] is asynchronous. *)
let is_async = function
  | With _ | Par _ | Top | Bottom | Whynot _ -> true
  | _ -> false

(* [is_neg f] checks if [f] is a negative atom. *)
let is_dual = function
  | Dual _ -> true
  | _ -> false

(* [is_atom f] checks if [f] is an atom. *)
let is_atom = function
  | Litt _ | Dual _ -> true
  | _ -> false

(* [is_atom f] checks if the top-level connective of [f] is binary. *)
let is_binop = function
  | Tensor _ | Plus _ | With _ | Par _ -> true
  | _ -> false

(* [left_sync f] checks if [f] is left-synchronous (for ILLF). *)
let left_sync = function
  | With _ | Top | Litt _ -> true
  | _ -> false

(* [right_sync f] checks if [f] is right-synchronous (for ILLF). *)
let right_sync = function
  | Tensor _ | Zero | One | Ofcourse _ | Litt _ | Plus _ -> true
  | _ -> false

(* [left_async f] checks if [f] is left-asynchronous (for ILLF). *)
let left_async = function
  | Tensor _ | Zero | One | Ofcourse _ | Plus _ -> true
  | _ -> false

(* [right_async f] checks if [f] is right-asynchronous (for ILLF). *)
let right_async = function
  | With _ | Top -> true
  | _ -> false

(* [whynot_height f] returns the whynot-height of [f]. *)
let rec whynot_height = function
  | Litt _ | Dual _ | One | Zero | Top | Bottom -> 0
  | Ofcourse f -> whynot_height f
  | Whynot f -> whynot_height f + 1
  | Tensor (f, g) | Plus (f, g) | With (f, g) | Par (f, g) ->
      max (whynot_height f) (whynot_height g)

(** Functions for manipulating LLF sequents **)

let map_wn = List.map (fun x -> Whynot x)

(** Manipulation of the type ['a option] **)

exception NoValue

let get_op = function
  | Some x -> x
  | None -> raise NoValue

(** Functions for splitting contexts **)

let rec split_list_aux (acc1, acc2) l k = match l with
  | [] -> acc1, acc2
  | hd :: tl ->
      if k mod 2 = 0 then split_list_aux (acc1, hd :: acc2) tl (k / 2)
      else split_list_aux (hd :: acc1, acc2) tl (k / 2)

let split_list l k =
  split_list_aux ([], []) l k

let rec fast_exp_aux acc m k =
    if k = 0 then acc
    else
      if k = 1 then m * acc
      else
        if k mod 2 = 1 then
          fast_exp_aux (acc * m) (m*m) (k / 2)
        else
          fast_exp_aux acc (m*m) (k/2)

let fast_exp_2 k =
  fast_exp_aux 1 2 k

let fast_exp m k =
  fast_exp_aux 1 m k

let rec choose_kth_from_list k l = match l with
  | [] -> assert false
  | [x] -> x, []
  | hd :: tl ->
      if k = 0 then hd, tl
      else
        let x, tl' = choose_kth_from_list (k - 1) tl in
        x, hd :: tl'

(* [bl] indicates if the (pseudo-)bound on the number of applications of the D2
   rule is reached. *)
let bl = ref false

(* [sort_whynot l] sorts the list of formulas [l] in ascending order using
   [whynot_height f] as the key of [f]. *)
let sort_whynot l =
  List.sort (fun x y -> whynot_height y - whynot_height x) l

(* [prove sequent select_d2 max_d2] attempts to prove the sequent [sequent]
   where [select_d2] contains the candidates for the D2 rule and [max_d2]
   is a (pseudo-)bound on the number of applications of the D2 rule. *)
let rec prove sequent select_d2 max_d2 = match sequent with
  | Async (theta, gamma, l) -> begin match l with
      | [] ->
          let rec apply_d1 k =
            if k = List.length gamma then None
            else
              let f, gamma' = choose_kth_from_list k gamma in
              if is_dual f then apply_d1 (k + 1)
              else
                try
                  let p = get_op (prove (Sync (theta, gamma', f)) select_d2 max_d2) in
                  Some (Node (sequent, Focusing_central (f, gamma'), [p]))
                with NoValue -> apply_d1 (k + 1) in
          begin try
            Some (get_op (apply_d1 0))
          with NoValue ->
            let rec apply_d2 select_d2 max_d2 =
              let f = List.hd select_d2 in
              try
                let p =
                  get_op (prove (Sync (theta, gamma, f))
                    (List.tl select_d2) max_d2) in
                Some (Node (sequent, Focusing_exponential f, [p]))
              with NoValue ->
                apply_d2' (List.tl select_d2) max_d2
            and apply_d2' select_d2 max_d2 =
              if select_d2 = [] then begin
                (if max_d2 = 0 then (bl := true; raise NoValue));
                let select_d2' =
                  sort_whynot (List.filter (fun x -> not (is_dual x))
                  (Set_formula.elements theta)) in
                if select_d2' = [] then None
                else
                  apply_d2 select_d2' (max_d2 - 1) end
              else
                apply_d2 select_d2 max_d2
            in
            begin try
              if Set_formula.for_all is_dual theta then None
              else
                Some (get_op (apply_d2' select_d2 max_d2))
            with NoValue -> None end end
      | hd :: tl ->
          begin match hd with
          | Bottom ->
              begin try
                let p = get_op (prove (Async (theta, gamma, tl)) select_d2 max_d2) in
                Some (Node (sequent, Bottom_intro, [p]))
              with NoValue -> None end
          | Top -> Some (Node (sequent, Top_intro, [Null]))
          | With (f, g) ->
              if whynot_height f > whynot_height g then
                try
                  let pg = get_op (prove (Async (theta, gamma, g :: tl)) select_d2 max_d2) in
                  let pf = get_op (prove (Async (theta, gamma, f :: tl)) select_d2 max_d2) in
                  Some (Node (sequent, With_intro, [pf; pg]))
                with NoValue -> None
              else
                begin try
                  let pf = get_op (prove (Async (theta, gamma, f :: tl)) select_d2 max_d2) in
                  let pg = get_op (prove (Async (theta, gamma, g :: tl)) select_d2 max_d2) in
                  Some (Node (sequent, With_intro, [pf; pg]))
              with NoValue -> None end
          | Par (f, g) ->
              begin try
                let p = get_op (prove (Async (theta, gamma, f :: g :: tl)) select_d2 max_d2) in
                Some (Node (sequent, Par_intro, [p]))
              with NoValue -> None end
          | Whynot g ->
              begin try
                let p =
                  get_op
                    (prove (Async (Set_formula.add g theta, gamma, tl))
                    select_d2 max_d2) in
                Some (Node (sequent, Whynot_intro, [p]))
              with NoValue ->
                None end
          | _ ->
              try
                let p = get_op (prove (Async (theta, hd :: gamma, tl)) select_d2 max_d2) in
                Some (Node (sequent, Async_on_pos, [p]))
              with NoValue -> None
           end end
  | Sync (theta, gamma, f) ->
      match f with
      | _ when is_async f || is_dual f ->
          begin try
            let p = get_op (prove (Async (theta, gamma, [f])) select_d2 max_d2) in
            Some (Node (sequent, Sync_on_neg, [p]))
          with NoValue -> None end
      | One ->
          if List.length gamma = 0 then
            Some (Node (sequent, One_intro, [Null]))
          else
            None
      | Plus (g, h) ->
          if whynot_height g > whynot_height h then
            try
              let p = get_op (prove (Sync (theta, gamma, h)) select_d2 max_d2) in
              Some (Node (sequent, Plus_right_intro, [p]))
            with NoValue ->
              try
                let p = get_op (prove (Sync (theta, gamma, g)) select_d2 max_d2) in
                Some (Node (sequent, Plus_left_intro, [p]))
              with NoValue -> None
          else
            begin try
              let p = get_op (prove (Sync (theta, gamma, g)) select_d2 max_d2) in
              Some (Node (sequent, Plus_left_intro, [p]))
            with NoValue ->
              try
                let p = get_op (prove (Sync (theta, gamma, h)) select_d2 max_d2) in
                Some (Node (sequent, Plus_right_intro, [p]))
              with NoValue -> None end
      | Tensor (g, h) ->
          let rec split_gamma k =
            if k = -1 then None
            else
              let gamma1, gamma2 = split_list gamma k in
              try
                if whynot_height g > whynot_height h then
                  let ph =
                    get_op (prove (Sync (theta, gamma2, h)) select_d2 max_d2) in
                  let pg =
                    get_op (prove (Sync (theta, gamma1, g)) select_d2 max_d2) in
                  Some (Node (sequent, Tensor_intro (gamma1, gamma2), [pg; ph]))
                else
                  let pg =
                    get_op (prove (Sync (theta, gamma1, g)) select_d2 max_d2) in
                  let ph =
                    get_op (prove (Sync (theta, gamma2, h)) select_d2 max_d2) in
                  Some (Node (sequent, Tensor_intro (gamma1, gamma2), [pg; ph]))
              with NoValue ->
                split_gamma (k - 1) in
          let k = fast_exp_2 (List.length gamma) - 1 in
          split_gamma k
      | Ofcourse g ->
          if gamma = [] then
            try
              let p = get_op (prove (Async (theta, gamma, [g])) select_d2 max_d2) in
              Some (Node (sequent, Ofcourse_intro, [p]))
            with NoValue -> None
          else
            None
      | Litt atom ->
          if gamma = [Dual atom] then
            Some (Node (sequent, Axiom_central, [Null]))
          else
            if gamma = [] && Set_formula.mem (Dual atom) theta then
              Some (Node (sequent, Axiom_exponential, [Null]))
            else
              None
      | _ -> None

(* [prove_sequent sequent cst_max_d2] attempts to prove [sequent] and returns
   the result [(res, proof, time)].
   [res] = None if the bound [cst_max_d2] is reached, and [res] = (Some b)
   when the proof search has been finished and b indicates the provability of
   [sequent]. When the sequent is provable, [proof] contains the proof found.
   *)
let prove_focused_sequent focused_sequent cst_max_d2 =
  bl := false;
  let t = Sys.time () in
  match prove focused_sequent [] cst_max_d2 with
    | None ->
        let exec_time = Sys.time () -. t in
        if !bl then (None, None, exec_time)
        else
          (Some false, None, exec_time)
    | Some proof ->
        let exec_time = Sys.time () -. t in
        (Some true, Some proof, exec_time)

(* FOCUSED <-> NOT FOCUSED *)
exception NotFound

let rec double_list = function
    | [] -> []
    | e :: tail -> e :: e :: double_list tail

let rec head_tail formula = function
    | [] -> raise NotFound
    | e :: formula_list -> if e = formula then [], formula_list
        else let head, tail = head_tail formula formula_list in e :: head, tail

let rec index_list offset = function
    | [] -> []
    | e :: tail -> (e, offset) :: index_list (offset + 1) tail

let rec head_index_tail element = function
    | [] -> raise NotFound
    | (e, i) :: l -> if e = element then [], i, l
        else let head, index, tail = head_index_tail element l in
        (e, i) :: head, index, tail

let rec get_mixed_permutation indexed1 indexed2 = function
    | [] -> []
    | e :: tail ->
        try let head1, i1, tail1 = head_index_tail e indexed1 in
            i1 :: (get_mixed_permutation (head1 @ tail1) indexed2 tail)
        with NotFound -> let head2, i2, tail2 = head_index_tail e indexed2 in
            i2 :: (get_mixed_permutation indexed1 (head2 @ tail2) tail)

let rec weaken proof l1 l2 = function
    | [] -> proof
    | e :: tail -> Weakening_proof (l1, e, map_wn tail @ l2, weaken proof l1 l2 tail)

let rec contract proof head tail = function
    | [] -> proof
    | e :: l -> Contraction_proof (map_wn head, e, (map_wn l) @ tail, contract proof (head @ [e; e]) tail l)

let rec unfocus_proof = function
    | Null -> raise (Failure "Focused proof is null")
    | Node (focused_sequent, rule, focused_premises) ->
        match rule with
            | One_intro -> begin match focused_sequent with
                | Sync (theta, [], One) ->
                    weaken One_proof [] [One] (map_wn (Set_formula.elements theta))
                | _ -> raise (Failure "sync formula with only one expected") end
            | Top_intro -> begin match focused_sequent with
                | Async (theta, gamma, Top :: tail) ->
                    Top_proof (map_wn (Set_formula.elements theta) @ gamma, tail)
                | _ -> raise (Failure "async with top expected") end
            | Bottom_intro -> begin match focused_sequent with
                | Async (theta, gamma, Bottom :: tail) ->
                    Bottom_proof (map_wn (Set_formula.elements theta) @ gamma, tail, unfocus_proof (List.hd focused_premises))
                | _ -> raise (Failure "async with bottom expected") end
            | Par_intro -> begin match focused_sequent with
                | Async (theta, gamma, Par (e1, e2) :: tail) ->
                    Par_proof (map_wn (Set_formula.elements theta) @ gamma, e1, e2, tail, unfocus_proof (List.hd focused_premises))
                | _ -> raise (Failure "async with par expected") end
            | With_intro -> begin match focused_sequent with
                | Async (theta, gamma, With (e1, e2) :: tail) ->
                    let premise1 = unfocus_proof (List.hd focused_premises) in
                    let premise2 = unfocus_proof (List.nth focused_premises 1) in
                    With_proof (map_wn (Set_formula.elements theta) @ gamma, e1, e2, tail, premise1, premise2)
                | _ -> raise (Failure "async with with expected") end
            | Tensor_intro (gamma1, gamma2) -> begin match focused_sequent with
                | Sync (theta, gamma, Tensor (e1,e2)) ->
                    let premise1 = unfocus_proof (List.hd focused_premises) in
                    let premise2 = unfocus_proof (List.nth focused_premises 1) in
                    let theta_elements = Set_formula.elements theta in
                    let n_theta = List.length theta_elements in
                    let n1 = List.length gamma1 in
                    let n2 = List.length gamma2 in
                    let permutation = [n_theta + n2] @ List.init (n_theta + n2) (fun k -> k) in
                    let exchanged_premise2 = Exchange_proof (map_wn theta_elements @ gamma2 @ [e2], permutation, premise2) in
                    let tensor_proof = Tensor_proof (map_wn theta_elements @ gamma1, e1, e2, map_wn theta_elements @ gamma2, premise1, exchanged_premise2) in
                    let new_sequent = map_wn theta_elements @ gamma1 @ [Tensor (e1,e2)] @ map_wn theta_elements @ gamma2 in
                    let indexed_gamma1 = index_list n_theta gamma1 in
                    let indexed_gamma2 = index_list (n_theta + n1 + 1 + n_theta) gamma2 in
                    let gamma_permutation = get_mixed_permutation indexed_gamma1 indexed_gamma2 gamma in
                    let permutation = List.init n_theta (fun k -> k)
                        @ List.init n_theta (fun k -> n_theta + n1 + 1 + k)
                        @ gamma_permutation
                        @ [n_theta + n1] in
                    let exchanged_tensor = Exchange_proof (new_sequent, permutation, tensor_proof) in
                    let new_sequent = map_wn theta_elements @ map_wn theta_elements @ gamma @ [Tensor (e1,e2)] in
                    let indexed_theta1 = index_list 0 theta_elements in
                    let indexed_theta2 = index_list n_theta theta_elements in
                    let theta_permutation = get_mixed_permutation indexed_theta1 indexed_theta2 (double_list theta_elements) in
                    let permutation = theta_permutation
                        @ List.init (n1 + n2 + 1) (fun k -> 2 * n_theta + k) in
                    let exponentials_together = Exchange_proof (new_sequent, permutation, exchanged_tensor) in
                    contract exponentials_together [] (gamma @ [Tensor (e1,e2)]) theta_elements
                | _ -> raise (Failure "sync tensor expected") end
            | Plus_left_intro -> begin match focused_sequent with
                | Sync (theta, gamma, Plus (e1, e2)) ->
                    Plus_left_proof (map_wn (Set_formula.elements theta) @ gamma, e1, e2, [], unfocus_proof (List.hd focused_premises))
                | _ -> raise (Failure "async with plus expected") end
            | Plus_right_intro -> begin match focused_sequent with
                | Sync (theta, gamma, Plus (e1, e2)) ->
                    Plus_right_proof (map_wn (Set_formula.elements theta) @ gamma, e1, e2, [], unfocus_proof (List.hd focused_premises))
                | _ -> raise (Failure "async with plus expected") end
            | Ofcourse_intro -> begin match focused_sequent with
                | Sync (theta, [], Ofcourse e) ->
                   Promotion_proof (Set_formula.elements theta, e, [], unfocus_proof (List.hd focused_premises))
                | _ -> raise (Failure "sync with ofcourse expected") end
            | Whynot_intro -> begin match focused_sequent with
                | Async (theta, gamma, (Whynot e) :: tail) ->
                    if Set_formula.mem e theta then
                      Weakening_proof (map_wn (Set_formula.elements theta) @ gamma, e, tail, unfocus_proof (List.hd focused_premises))
                    else 
                      let premise = unfocus_proof (List.hd focused_premises) in
                      let theta_head, theta_tail = head_tail e (Set_formula.elements theta) in
                      let new_sequent = map_wn theta_head @ map_wn theta_tail @ gamma @ [Whynot e] @ tail in
                      let n_theta_head = List.length theta_head in
                      let n_theta_tail = List.length theta_tail in
                      let n_gamma = List.length gamma in
                      let n_tail = List.length tail in
                      let permutation = List.init n_theta_head (fun k -> k)
                        @ List.init (n_theta_tail + n_gamma) (fun k -> n_theta_head + 1 + k)
                        @ [n_theta_head]
                        @ List.init n_tail (fun k -> n_theta_head + n_theta_tail + n_gamma + 1 + k) in
                      Exchange_proof (new_sequent, permutation, premise)
                | _ -> raise (Failure "async formula with whynot expected") end
            | Axiom_central -> begin match focused_sequent with
                | Sync (theta, [Dual s], Litt t) when s = t ->
                    weaken (Axiom_proof (Dual s)) [] [Dual s; Litt s] (Set_formula.elements theta)
                | _ -> raise (Failure "sync formula expected") end
            | Axiom_exponential -> begin match focused_sequent with
                | Sync (theta, [], Litt s) ->
                    let axiom_proof = Axiom_proof (Dual s) in
                    let dereliction_proof = Dereliction_proof ([], Dual s, [Litt s], axiom_proof) in
                    let head, tail = head_tail (Dual s) (Set_formula.elements theta) in
                    let weakening_tail_proof = weaken dereliction_proof [Whynot (Dual s)] [Litt s] tail in
                      weaken weakening_tail_proof [] ([Whynot (Dual s)] @ map_wn tail @ [Litt s]) head
                | _ -> raise (Failure "sync formula with empty gamma expected") end
            | Focusing_central (formula, _) -> begin match focused_sequent with
                | Async (theta, gamma, []) ->
                    let premise = unfocus_proof (List.hd focused_premises) in
                    let head, tail = head_tail formula gamma in
                    let new_sequent = map_wn (Set_formula.elements theta) @ head @ tail @ [formula] in
                    let n_theta = Set_formula.cardinal theta in
                    let n_head = List.length head in
                    let n_tail = List.length tail in
                    let permutation = List.init (n_theta + n_head) (fun k -> k)
                        @ [n_theta + n_head + n_tail]
                        @ List.init n_tail (fun k -> n_theta + n_head + k) in
                    Exchange_proof (new_sequent, permutation, premise)
                | _ -> raise (Failure "async empty expected") end
            | Focusing_exponential formula -> begin match focused_sequent with
                | Async (theta, gamma, []) ->
                    let premise = unfocus_proof (List.hd focused_premises) in
                    let wn_theta_elements = map_wn (Set_formula.elements theta) in
                    let dereliction = Dereliction_proof (wn_theta_elements @ gamma, formula, [], premise) in
                    let head, tail = head_tail (Whynot formula) wn_theta_elements in
                    let new_sequent = wn_theta_elements @ gamma @ [Whynot formula] in
                    let n_head = List.length head in
                    let n_tail = List.length tail in
                    let n_gamma = List.length gamma in
                    let permutation = List.init n_head (fun k -> k)
                        @ [n_head]
                        @ [n_head + 1 + n_tail + n_gamma]
                        @ List.init n_tail (fun k -> n_head + 1 + k)
                        @ List.init n_gamma (fun k -> n_head + 1 + n_tail + k) in
                    let exchange = Exchange_proof (new_sequent, permutation, dereliction) in
                    Contraction_proof (head, formula, tail @ gamma, exchange)
                | _ -> raise (Failure "async empty expected") end
            | Async_on_pos -> begin match focused_sequent with
                | Async (theta, gamma, e :: tail) ->
                    let premise = unfocus_proof (List.hd focused_premises) in
                    let new_sequent = map_wn (Set_formula.elements theta) @ (e :: gamma) @ tail in
                    let n_theta = Set_formula.cardinal theta in
                    let n_gamma = List.length gamma in
                    let permutation = List.init n_theta (fun k -> k)
                        @ List.init n_gamma (fun k -> n_theta + 1 + k)
                        @ [n_theta]
                        @ List.init (List.length tail) (fun k -> n_theta + n_gamma + 1 + k) in
                    Exchange_proof (new_sequent, permutation, premise)
                | _ -> raise (Failure "async formula expected") end
            | Sync_on_neg -> unfocus_proof (List.hd focused_premises)

let sequent_to_focused_sequent sequent =
    Async (Set_formula.empty, [], sequent)

let proof_from_focused_proof focused_proof =
    let proof = unfocus_proof focused_proof in
    commute_permutations proof []

exception NonProvableSequent
exception NonAutoProvableSequent

let prove_sequent sequent =
    let focused_sequent = sequent_to_focused_sequent sequent in
    match prove_focused_sequent focused_sequent 3 with
    | Some true, Some focused_proof, _ -> proof_from_focused_proof focused_proof
    | Some false, _, _ -> raise NonProvableSequent
    | _ -> raise NonAutoProvableSequent