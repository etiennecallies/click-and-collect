open Sequent
open Proof
open Proof_with_notations
open Transform_request
open Permutations

exception Transform_exception of string;;
exception Pedagogic_exception of string;;

(* PROOF -> TRANSFORM OPTION *)

let rec can_commute_with_cut length_to_formula cut_context notations = function
    | Axiom_proof _ -> true, "Eliminate ax-cut"
    | Top_proof (head, _tail) when length_to_formula <> List.length head -> true, "Commute with ⊤ rule"
    | Bottom_proof (head, _tail, _) when length_to_formula <> List.length head -> true, "Commute with ⊥ rule"
    | Tensor_proof (head, _, _, _tail, _, _) when length_to_formula <> List.length head -> true, "Commute with ⊗ rule"
    | Par_proof (head, _, _, _tail, _) when length_to_formula <> List.length head -> true, "Commute with ⅋ rule"
    | With_proof (head, _, _, _tail, _, _) when length_to_formula <> List.length head -> true, "Commute with & rule"
    | Plus_left_proof (head, _, _, _tail, _) when length_to_formula <> List.length head -> true, "Commute with ⊕ rule"
    | Plus_right_proof (head, _, _, _tail, _) when length_to_formula <> List.length head -> true, "Commute with ⊕ rule"
    | Dereliction_proof (head, _, _tail, _) when length_to_formula <> List.length head -> true, "Commute with ?d rule"
    | Weakening_proof (head, _, _tail, _) when length_to_formula <> List.length head -> true, "Commute with ?w rule"
    | Contraction_proof (head, _, _tail, _) when length_to_formula <> List.length head -> true, "Commute with ?c rule"
    | Promotion_proof (head, _, _tail, _p)
        when has_whynot_context cut_context && length_to_formula <> List.length head -> true, "Commute with ! rule"
    | Unfold_litt_proof (head, s, _tail, _)
    | Unfold_dual_proof (head, s, _tail, _)
        when List.mem_assoc s notations && length_to_formula <> List.length head -> true, "Commute with def rule"
    | Weakening_proof (_head, _, _tail, _) when has_whynot_context cut_context -> true, "Eliminate ?w-cut"
    | Contraction_proof (_head, _, _tail, _) when has_whynot_context cut_context -> true, "Split ?c-cut"
    | Cut_proof (_head, _, _tail, _, _) -> true, "Commute with cut rule"
    | Exchange_proof (_, _display_permutation, permutation, p)
        -> can_commute_with_cut (List.nth permutation length_to_formula) cut_context notations p
    | _ -> false, "Commute with rule";;

let rec can_cut_key_case length1 length2 notations p1 p2 = match p1, p2 with
    | One_proof, Bottom_proof (head, _, _) when length2 = List.length head ->
        true, "Eliminate 1/⊥ key-case"
    | Bottom_proof (head, _, _), One_proof when length1 = List.length head ->
        true, "Eliminate ⊥/1 key-case"
    | Tensor_proof (head1, _, _, _, _, _), Par_proof (head2, _, _, _, _)
        when length1 = List.length head1 && length2 = List.length head2 ->
        true, "Eliminate ⊗/⅋ key-case"
    | Par_proof (head1, _, _, _, _), Tensor_proof (head2, _, _, _, _, _)
        when length1 = List.length head1 && length2 = List.length head2 ->
        true, "Eliminate ⅋/⊗ key-case"
    | With_proof (head1, _, _, _, _, _), Plus_left_proof (head2, _, _, _, _)
        when length1 = List.length head1 && length2 = List.length head2 ->
        true, "Eliminate &/⊕ key-case"
    | Plus_left_proof (head1, _, _, _, _), With_proof (head2, _, _, _, _, _)
        when length1 = List.length head1 && length2 = List.length head2 ->
        true, "Eliminate ⊕/& key-case"
    | With_proof (head1, _, _, _, _, _), Plus_right_proof (head2, _, _, _, _)
        when length1 = List.length head1 && length2 = List.length head2 ->
        true, "Eliminate &/⊕ key-case"
    | Plus_right_proof (head1, _, _, _, _), With_proof (head2, _, _, _, _, _)
        when length1 = List.length head1 && length2 = List.length head2 ->
        true, "Eliminate ⊕/& key-case"
    | Promotion_proof (head1, _, _, _), Dereliction_proof (head2, _, _, _)
        when length1 = List.length head1 && length2 = List.length head2 ->
        true, "Eliminate !/?d key-case"
    | Dereliction_proof (head1, _, _, _), Promotion_proof (head2, _, _, _)
        when length1 = List.length head1 && length2 = List.length head2 ->
        true, "Eliminate ?d/! key-case"
    | Unfold_litt_proof (head1, s, _, _), Unfold_dual_proof (head2, _s, _, _)
        when List.mem_assoc s notations && length1 = List.length head1 && length2 = List.length head2 ->
        true, "Eliminate def/def key-case"
    | Unfold_dual_proof (head1, s, _, _), Unfold_litt_proof (head2, _s, _, _)
        when List.mem_assoc s notations && length1 = List.length head1 && length2 = List.length head2 ->
        true, "Eliminate def/def key-case"
    | Exchange_proof (_, _display_permutation, permutation, p), p2 ->
        can_cut_key_case (List.nth permutation length1) length2 notations p p2
    | p1, Exchange_proof (_, _display_permutation, permutation, p) ->
        can_cut_key_case length1 (List.nth permutation length2) notations p1 p
    | _ -> false, "Eliminate key-case";;

let get_transform_options notations not_cyclic = function
    | Axiom_proof f -> let expand_axiom_enabled = match f with
        | Litt s | Dual s -> List.mem_assoc s notations
        | _ -> true in
        [Expand_axiom, (expand_axiom_enabled, "One step axiom expansion");
        Expand_axiom_full, (expand_axiom_enabled && not_cyclic, "Full axiom expansion")]
    | Cut_proof (head, _formula, tail, p1, p2) ->
        let commute_left, commute_left_message = can_commute_with_cut (List.length head) tail notations p1 in
        let commute_right, commute_right_message = can_commute_with_cut 0 head notations p2 in
        let cut_key_case, cut_key_case_message = can_cut_key_case (List.length head) 0 notations p1 p2 in
        let cut_full = not_cyclic && (commute_left || commute_right || cut_key_case) in
        [Eliminate_cut_left, (commute_left, commute_left_message ^ " on the left");
        Eliminate_cut_key_case, (cut_key_case, cut_key_case_message);
        Eliminate_cut_right, (commute_right, commute_right_message ^ " on the right");
        Eliminate_cut_full, (cut_full, "Fully eliminate this cut")]
    | _ -> [];;

let can_commute_on_left notations = function
    | Cut_proof (head, _formula, tail, p1, _p2) -> let enabled, _ = can_commute_with_cut (List.length head) tail notations p1 in enabled
    | _ -> false

let can_commute_on_right notations = function
    | Cut_proof (head, _formula, _tail, _p1, p2) -> let enabled, _ = can_commute_with_cut 0 head notations p2 in enabled
    | _ -> false

let can_eliminate_key_case notations = function
    | Cut_proof (head, _formula, _tail, p1, p2) -> let enabled, _ = can_cut_key_case (List.length head) 0 notations p1 p2 in enabled
    | _ -> false

let identity_head_tail head tail =
    identity (List.length head + 1 + List.length tail)

let get_ancestors_lists = function
    | Axiom_proof _ -> []
    | One_proof -> []
    | Top_proof (_, _) -> []
    | Bottom_proof (head, tail, _) -> [remove_nth_element (List.length head) (identity_head_tail head tail)]
    | Tensor_proof (head, _, _, tail, _, _) ->
        let h = List.length head in
        let t = List.length tail in
        [(identity (h + 1)); List.map (fun n -> n + h) (identity (1 + t))]
    | Par_proof (head, _, _, tail, _) -> [duplicate_nth_element (List.length head) (identity_head_tail head tail)]
    | With_proof (head, _, _, tail, _, _) -> [identity_head_tail head tail; identity_head_tail head tail]
    | Plus_left_proof (head, _, _, tail, _) -> [identity_head_tail head tail]
    | Plus_right_proof (head, _, _, tail, _) -> [identity_head_tail head tail]
    | Promotion_proof (head_without_whynot, _, tail_without_whynot, _) -> [identity_head_tail head_without_whynot tail_without_whynot]
    | Dereliction_proof (head, _, tail, _) -> [identity_head_tail head tail]
    | Weakening_proof (head, _, tail, _) -> [remove_nth_element (List.length head) (identity_head_tail head tail)]
    | Contraction_proof (head, _, tail, _) -> [duplicate_nth_element (List.length head) (identity_head_tail head tail)]
    | Exchange_proof (_, _, permutation, _) -> [permutation_inverse permutation]
    | Cut_proof (head, _, tail, _, _) ->
        let h = List.length head in
        let t = List.length tail in
        [(identity h) @ [-1]; [-1] @ List.map (fun n -> n + h) (identity t)]
    | Unfold_litt_proof (head, _, tail, _) -> [identity_head_tail head tail]
    | Unfold_dual_proof (head, _, tail, _) -> [identity_head_tail head tail]
    | Hypothesis_proof _ -> [];;

let get_transform_options_as_json notations not_cyclic proof =
    let transform_options = get_transform_options notations not_cyclic proof in
    [
        "transformOptions", `List (List.map (fun (transform_option, (enabled, title)) -> `Assoc [
            ("transformation", `String (Transform_request.to_string transform_option));
            ("enabled", `Bool enabled);
            ("title", `String title)
            ]) transform_options);
        "ancestorsLists", `List (List.map (fun l -> `List (List.map (fun x -> `Int x) l)) (get_ancestors_lists proof))]

let rec has_cut_that_can_be_eliminated notations not_cyclic proof =
    let transform_options = get_transform_options notations not_cyclic proof in
    if List.mem_assoc Eliminate_cut_full transform_options
        && let enabled, _ = List.assoc Eliminate_cut_full transform_options in enabled
    then true
    else List.exists (has_cut_that_can_be_eliminated notations not_cyclic) (get_premises proof)

(* AXIOM EXPANSION *)

let expand_axiom notations = function
    | One -> Bottom_proof ([One], [], One_proof)
    | Bottom -> Bottom_proof ([], [One], One_proof)
    | Top -> Top_proof ([], [Zero])
    | Zero -> Top_proof ([Zero], [])
    | Litt s when List.mem_assoc s notations ->
        let f = Raw_sequent.to_formula (List.assoc s notations) in
        Unfold_litt_proof ([], s, [Dual s], Unfold_dual_proof ([f], s, [], Axiom_proof f))
    | Dual s when List.mem_assoc s notations ->
        let f = Raw_sequent.to_formula (List.assoc s notations) in
        Unfold_dual_proof ([], s, [Litt s], Unfold_litt_proof ([dual f], s, [], Axiom_proof (dual f)))
    | Litt s -> Axiom_proof (Litt s)
    | Dual s -> Axiom_proof (Dual s)
    | Tensor (e1, e2) ->
         let e1' = dual e1 in
         let e2' = dual e2 in
         let tensor_proof = Tensor_proof ([e1'], e1, e2, [e2'], Axiom_proof e1', Axiom_proof e2) in
         let permutation = [1; 0; 2] in
         let exchange_proof = build_exchange [e1'; Tensor (e1, e2); e2'] permutation tensor_proof in
         Par_proof ([Tensor (e1, e2)], e1', e2', [], exchange_proof)
    | Par (e1, e2) ->
        let e1' = dual e1 in
        let e2' = dual e2 in
        let tensor_proof = Tensor_proof ([e1], e1', e2', [e2], Axiom_proof e1, Axiom_proof e2') in
        let permutation = [0; 2; 1] in
        let exchange_proof = build_exchange [e1; Tensor (e1', e2'); e2] permutation tensor_proof in
        Par_proof ([], e1, e2, [Tensor (e1', e2')], exchange_proof)
    | With (e1, e2) ->
        let e1' = dual e1 in
        let e2' = dual e2 in
        let plus_left_proof = Plus_left_proof ([e1], e1', e2', [], Axiom_proof e1) in
        let plus_right_proof = Plus_right_proof ([e2], e1', e2', [], Axiom_proof e2) in
        With_proof ([], e1, e2, [Plus (e1', e2')], plus_left_proof, plus_right_proof)
    | Plus (e1, e2) ->
       let e1' = dual e1 in
       let e2' = dual e2 in
       let plus_left_proof = Plus_left_proof ([], e1, e2, [e1'], Axiom_proof e1) in
       let plus_right_proof = Plus_right_proof ([], e1, e2, [e2'], Axiom_proof e2) in
       With_proof ([Plus (e1, e2)], e1', e2', [], plus_left_proof, plus_right_proof)
    | Ofcourse e ->
       let e' = dual e in
       Promotion_proof ([], e, [e'], Dereliction_proof ([e], e', [], Axiom_proof e))
    | Whynot e ->
        let e' = dual e in
        Promotion_proof ([e], e', [], Dereliction_proof ([], e, [e'], Axiom_proof e))
    ;;

let rec expand_axiom_on_proof notations = function
    | Axiom_proof f -> expand_axiom notations f
    | Exchange_proof (s, display_permutation, exchange_permutation, p) ->
        merge_exchange (Exchange_proof (s, display_permutation, exchange_permutation, expand_axiom_on_proof notations p))
    | _ -> raise (Transform_exception ("Can only expand axiom on Axiom_proof or Exchange_proof"))

let rec expand_axiom_full notations proof =
    let new_proof =
        try expand_axiom_on_proof notations proof
        with Transform_exception _ -> proof in
    set_premises new_proof (List.map (expand_axiom_full notations) (get_premises new_proof))

(* CUT ELIMINATION LEFT / RIGHT *)

let rec minus_last = function
    | [] -> raise (Failure "empty list")
    | [_e] -> []
    | e :: tail -> e :: (minus_last tail)

let minus_n n l =
    let head, _, tail = head_formula_tail n l in
    head @ tail

let head_tail_permuted head tail permutation is_left =
    let connector_position = List.length head in
    let head_perm, tail_perm = head_tail connector_position permutation in
    let head_perm' = perm_minus_element connector_position head_perm in
    let tail_perm' = perm_minus_element connector_position tail_perm in
    let new_head, new_tail = permute (head @ tail) head_perm', permute (head @ tail) tail_perm' in
    if is_left
        then new_head, minus_last new_tail
        else List.tl new_head, new_tail

let cut_elimination_tensor cut_head cut_formula cut_tail other_proof is_left permutation head e1 e2 tail p1 p2 cut_trans =
    if is_left
    then let cut_formula_position = List.nth permutation (List.length cut_head) in
        let permutation_without_cut_formula = perm_minus_element cut_formula_position permutation
            @ List.init (List.length cut_tail) (fun n -> List.length cut_head + n) in
        if cut_formula_position < List.length head
        then let head' = minus_n cut_formula_position head in
            (*        head @ [e1]           *)
            (* ------------------------- Ex *)
            (* head' @ [e1; cut_formula]    *)
            let new_p1 = move_right cut_formula_position 0 p1 in

            (* head' @ [e1; cut_formula]  [dual(cut_formula)] @ cut_tail     *)
            (* --------------------------------------------------------- Cut *)
            (*                 head' @ [e1] @ cut_tail                       *)
            let new_cut = cut_trans (Cut_proof (head' @ [e1], cut_formula, cut_tail, new_p1, other_proof)) in

            (* head' @ [e1] @ cut_tail    *)
            (* ----------------------- Ex *)
            (* head' @ cut_tail @ [e1]    *)
            let exchange_proof = move_right (List.length head') 0 new_cut in

            (* head' @ cut_tail @ [e1]  [e2] @ tail   *)
            (* ------------------------------------ ⊗ *)
            (* head' @ cut_tail @ [e1 ⊗ e2] @ tail    *)
            let tensor_proof = Tensor_proof (head' @ cut_tail, e1, e2, tail, exchange_proof, p2) in

            (* head' @ cut_tail @ [e1 ⊗ e2] @ tail    *)
            (* ----------------------------------- Ex *)
            (* head' @ [e1 ⊗ e2] @ tail @ cut_tail    *)
            let shifted_proof = shift_block (List.length head') (List.length cut_tail) (1 + List.length tail) tensor_proof in

            (* head' @ [e1 ⊗ e2] @ tail @ cut_tail    *)
            (* ----------------------------------- Ex *)
            (*        cut_head @ cut_tail             *)
            merge_exchange (build_exchange (head' @ [Tensor (e1, e2)] @ tail @ cut_tail) permutation_without_cut_formula shifted_proof)
        else let cut_formula_position_in_tail = cut_formula_position - List.length head - 1 in
            let tail' = minus_n cut_formula_position_in_tail tail in
            (*          [e2] @ tail            *)
            (* ---------------------------- Ex *)
            (* [e2] @ tail' @ [cut_formula]    *)
            let new_p2 = move_right (1 + cut_formula_position_in_tail) 0 p2 in

            (* [e2] @ tail' @ [cut_formula]  [dual(cut_formula)] @ cut_tail     *)
            (* ------------------------------------------------------------ Cut *)
            (*                  [e2] @ tail' @ cut_tail                         *)
            let new_cut = cut_trans (Cut_proof ([e2] @ tail', cut_formula, cut_tail, new_p2, other_proof)) in

            (* head @ [e1]  [e2] @ tail' @ cut_tail   *)
            (* ------------------------------------ ⊗ *)
            (* head @ [e1 ⊗ e2] @ tail' @ cut_tail    *)
            let tensor_proof = Tensor_proof (head, e1, e2, tail' @ cut_tail, p1, new_cut) in

            (* head @ [e1 ⊗ e2] @ tail' @ cut_tail    *)
            (* ----------------------------------- Ex *)
            (*        cut_head @ cut_tail             *)
            build_exchange (head @ [Tensor (e1, e2)] @ tail' @ cut_tail) permutation_without_cut_formula tensor_proof
    else let dual_cut_formula_position = List.nth permutation 0 in
        let permutation_without_dual_cut_formula = List.init (List.length cut_head) (fun n -> n)
            @ List.map (fun n -> List.length cut_head + n) (perm_minus_element dual_cut_formula_position permutation) in
        if dual_cut_formula_position < List.length head
        then let head' = minus_n dual_cut_formula_position head in
            (*            head @ [e1]                *)
            (* ---------------------------------- Ex *)
            (* [dual (cut_formula)] @ head' @ [e1]   *)
            let new_p1 = move_left 0 (List.length head - dual_cut_formula_position) p1 in

            (* cut_head @ [cut_formula]  [dual (cut_formula)] @ head' @ [e1]     *)
            (* ------------------------------------------------------------- Cut *)
            (*                 cut_head @ head' @ [e1]                           *)
            let new_cut = cut_trans (Cut_proof (cut_head, cut_formula, head' @ [e1], other_proof, new_p1)) in

            (* cut_head @ head' @ [e1]  [e2] @ tail   *)
            (* ------------------------------------ ⊗ *)
            (* cut_head @ head' @ [e1 ⊗ e2] @ tail    *)
            let tensor_proof = Tensor_proof (cut_head @ head', e1, e2, tail, new_cut, p2) in

            (* cut_head @ head' @ [e1 ⊗ e2] @ tail    *)
            (* ----------------------------------- Ex *)
            (*        cut_head @ cut_tail             *)
            build_exchange (cut_head @ head' @ [Tensor (e1, e2)] @ tail) permutation_without_dual_cut_formula tensor_proof
        else let dual_cut_formula_position_in_tail = dual_cut_formula_position - List.length head - 1 in
            let tail' = minus_n dual_cut_formula_position_in_tail tail in
            (*          [e2] @ tail                *)
            (* -------------------------------- Ex *)
            (* [dual (cut_formula); e2] @ tail'    *)
            let new_p2 = move_left 0 (List.length tail' - dual_cut_formula_position_in_tail) p2 in

            (* cut_head @ [cut_formula]  [dual (cut_formula); e2] @ tail'     *)
            (* ---------------------------------------------------------- Cut *)
            (*              cut_head @ [e2] @ tail'                           *)
            let new_cut = cut_trans (Cut_proof (cut_head, cut_formula, [e2] @ tail', other_proof, new_p2)) in

            (* cut_head @ [e2] @ tail'    *)
            (* ----------------------- Ex *)
            (* [e2] @ tail' @ cut_head    *)
            let shifted_proof = shift_block 0 (List.length cut_head) (List.length tail) new_cut in

            (* head @ [e1]  [e2] @ tail' @ cut_head   *)
            (* ------------------------------------ ⊗ *)
            (* head @ [e1 ⊗ e2] @ tail' @ cut_head    *)
            let tensor_proof = Tensor_proof (head, e1, e2, tail' @ cut_head, p1, shifted_proof) in

            (* head @ [e1 ⊗ e2] @ tail' @ cut_head    *)
            (* ----------------------------------- Ex *)
            (* cut_head @ head @ [e1 ⊗ e2] @ tail'    *)
            let shifted_proof = shift_block 0 (List.length cut_tail) (List.length cut_head) tensor_proof in

            (* cut_head @ head @ [e1 ⊗ e2] @ tail'    *)
            (* ----------------------------------- Ex *)
            (*        cut_head @ cut_tail             *)
            merge_exchange (build_exchange (cut_head @ head @ [Tensor (e1, e2)] @ tail') permutation_without_dual_cut_formula shifted_proof)

let cut_elimination_cut cut_head cut_formula cut_tail other_proof is_left permutation head formula tail p1 p2 cut_trans =
    if is_left
    then let cut_formula_position = List.nth permutation (List.length cut_head) in
        let permutation_without_cut_formula = perm_minus_element cut_formula_position permutation
            @ List.init (List.length cut_tail) (fun n -> List.length cut_head + n) in
        if cut_formula_position < List.length head
        then let head' = minus_n cut_formula_position head in
            (*        head @ [formula]           *)
            (* ------------------------------ Ex *)
            (* head' @ [formula; cut_formula]    *)
            let new_p1 = move_right cut_formula_position 0 p1 in

            (* head' @ [formula; cut_formula]  [dual(cut_formula)] @ cut_tail     *)
            (* -------------------------------------------------------------- Cut *)
            (*                 head' @ [formula] @ cut_tail                       *)
            let new_cut = cut_trans (Cut_proof (head' @ [formula], cut_formula, cut_tail, new_p1, other_proof)) in

            (* head' @ [formula] @ cut_tail    *)
            (* ---------------------------- Ex *)
            (* head' @ cut_tail @ [formula]    *)
            let exchange_proof = move_left (List.length head') 0 new_cut in

            (* head' @ cut_tail @ [formula]  [dual(formula)] @ tail     *)
            (* ---------------------------------------------------- Cut *)
            (*                  head' @ cut_tail @ tail                 *)
            let cut_proof = Cut_proof (head' @ cut_tail, formula, tail, exchange_proof, p2) in

            (* head' @ cut_tail @ tail    *)
            (* ----------------------- Ex *)
            (* head' @ tail @ cut_tail    *)
            let shifted_proof = shift_block (List.length head') (List.length cut_tail) (List.length tail) cut_proof in

            (* head' @ tail @ cut_tail    *)
            (* ----------------------- Ex *)
            (*   cut_head @ cut_tail      *)
            merge_exchange (build_exchange (head' @ tail @ cut_tail) permutation_without_cut_formula shifted_proof)
        else let cut_formula_position_in_tail = cut_formula_position - List.length head in
            let tail' = minus_n cut_formula_position_in_tail tail in
            (*         [dual(formula)] @ tail            *)
            (* -------------------------------------- Ex *)
            (* [dual(formula)] @ tail' @ [cut_formula]   *)
            let new_p2 = move_right (1 + cut_formula_position_in_tail) 0 p2 in

            (* [dual(formula)] @ tail' @ [cut_formula]  [dual(cut_formula)] @ cut_tail     *)
            (* ----------------------------------------------------------------------- Cut *)
            (*                  [dual(formula)] @ tail' @ cut_tail                         *)
            let new_cut = cut_trans (Cut_proof ([dual formula] @ tail', cut_formula, cut_tail, new_p2, other_proof)) in

            (* head @ [formula]  [dual(formula)] @ tail' @ cut_tail     *)
            (* ---------------------------------------------------- Cut *)
            (*            head @ tail' @ cut_tail                       *)
            let cut_proof = Cut_proof (head, formula, tail' @ cut_tail, p1, new_cut) in

            (* head @ tail' @ cut_tail    *)
            (* ----------------------- Ex *)
            (*   cut_head @ cut_tail      *)
            build_exchange (head @ tail' @ cut_tail) permutation_without_cut_formula cut_proof
    else let dual_cut_formula_position = List.nth permutation 0 in
        let permutation_without_dual_cut_formula = List.init (List.length cut_head) (fun n -> n)
            @ List.map (fun n -> List.length cut_head + n) (perm_minus_element dual_cut_formula_position permutation) in
        if dual_cut_formula_position < List.length head
        then let head' = minus_n dual_cut_formula_position head in
            (*            head @ [formula]                 *)
            (* ---------------------------------------- Ex *)
            (* [dual (cut_formula)] @ head' @ [formula]    *)
            let new_p1 = move_left 0 (List.length head - dual_cut_formula_position) p1 in

            (* cut_head @ [cut_formula]  [dual (cut_formula)] @ head' @ [formula]     *)
            (* ------------------------------------------------------------------ Cut *)
            (*                 cut_head @ head' @ [formula]                           *)
            let new_cut = cut_trans (Cut_proof (cut_head, cut_formula, head' @ [formula], other_proof, new_p1)) in

            (* cut_head @ head' @ [formula]  [dual(formula)] @ tail     *)
            (* ---------------------------------------------------- Cut *)
            (*                cut_head @ head' @ tail                   *)
            let cut_proof = Cut_proof (cut_head @ head', formula, tail, new_cut, p2) in

            (* cut_head @ head' @ tail    *)
            (* ----------------------- Ex *)
            (*   cut_head @ cut_tail      *)
            build_exchange (cut_head @ head' @ tail) permutation_without_dual_cut_formula cut_proof
        else let dual_cut_formula_position_in_tail = dual_cut_formula_position - List.length head in
            let tail' = minus_n dual_cut_formula_position_in_tail tail in
            (*         [dual(formula)] @ tail                *)
            (* ------------------------------------------ Ex *)
            (* [dual (cut_formula); dual(formula)] @ tail'   *)
            let new_p2 = move_left 0 (List.length tail' - dual_cut_formula_position_in_tail) p2 in

            (* cut_head @ [cut_formula]  [dual (cut_formula); dual(formula)] @ tail'     *)
            (* --------------------------------------------------------------------- Cut *)
            (*              cut_head @ [dual(formula)] @ tail'                           *)
            let new_cut = cut_trans (Cut_proof (cut_head, cut_formula, [dual formula] @ tail', other_proof, new_p2)) in

            (* cut_head @ [dual(formula)] @ tail'    *)
            (* ---------------------------------- Ex *)
            (* [dual(formula)] @ tail' @ cut_head    *)
            let shifted_proof = shift_block 0 (List.length cut_head) (List.length tail) new_cut in

            (* head @ [formula]  [dual(formula)] @ tail' @ cut_head     *)
            (* ---------------------------------------------------- Cut *)
            (*                head @ tail' @ cut_head                   *)
            let cut_proof = Cut_proof (head, formula, tail' @ cut_head, p1, shifted_proof) in

            (* head @ tail' @ cut_head    *)
            (* ----------------------- Ex *)
            (* cut_head @ head @ tail'    *)
            let shifted_proof = shift_block 0 (List.length cut_tail) (List.length cut_head) cut_proof in

            (* cut_head @ head @ tail'    *)
            (* ----------------------- Ex *)
            (*   cut_head @ cut_tail      *)
            merge_exchange (build_exchange (cut_head @ head @ tail') permutation_without_dual_cut_formula shifted_proof)

let rec cut_elimination_with_permutation cut_head cut_formula cut_tail other_proof is_left permutation notations cut_trans = function
    | Axiom_proof _f -> other_proof
    | Top_proof (head, tail) ->
        let new_head, new_tail = head_tail_permuted head tail permutation is_left in
        if is_left
        then Top_proof (new_head, new_tail @ cut_tail)
        else Top_proof (cut_head @ new_head, new_tail)
    | Bottom_proof (head, tail, p) ->
        let new_head, new_tail = head_tail_permuted head tail permutation is_left in
        let new_permutation = perm_minus_element (List.length head) permutation in
        let new_proof = build_exchange (get_conclusion p) new_permutation p in
        if is_left
        then Bottom_proof (new_head, new_tail @ cut_tail, cut_trans (Cut_proof (new_head @ new_tail, cut_formula, cut_tail, new_proof, other_proof)))
        else Bottom_proof (cut_head @ new_head, new_tail, cut_trans (Cut_proof (cut_head, cut_formula, new_head @ new_tail, other_proof, new_proof)))
    | Tensor_proof (head, e1, e2, tail, p1, p2) ->
        cut_elimination_tensor cut_head cut_formula cut_tail other_proof is_left permutation head e1 e2 tail p1 p2 cut_trans
    | Par_proof (head, e1, e2, tail, p) ->
        let new_head, new_tail = head_tail_permuted head tail permutation is_left in
        let new_permutation = perm_plus_element (List.length head) permutation in
        let new_proof = build_exchange (get_conclusion p) new_permutation p in
        if is_left
        then Par_proof (new_head, e1, e2, new_tail @ cut_tail, cut_trans (Cut_proof (new_head @ [e1; e2] @ new_tail, cut_formula, cut_tail, new_proof, other_proof)))
        else Par_proof (cut_head @ new_head, e1, e2, new_tail, cut_trans (Cut_proof (cut_head, cut_formula, new_head @ [e1; e2] @ new_tail, other_proof, new_proof)))
    | With_proof (head, e1, e2, tail, p1, p2) ->
        let new_head, new_tail = head_tail_permuted head tail permutation is_left in
        let new_p1 = build_exchange (get_conclusion p1) permutation p1 in
        let new_p2 = build_exchange (get_conclusion p2) permutation p2 in
        if is_left
        then With_proof (new_head, e1, e2, new_tail @ cut_tail,
            cut_trans (Cut_proof (new_head @ [e1] @ new_tail, cut_formula, cut_tail, new_p1, other_proof)),
            cut_trans (Cut_proof (new_head @ [e2] @ new_tail, cut_formula, cut_tail, new_p2, other_proof)))
        else With_proof (cut_head @ new_head, e1, e2, new_tail,
            cut_trans (Cut_proof (cut_head, cut_formula, new_head @ [e1] @ new_tail, other_proof, new_p1)),
            cut_trans (Cut_proof (cut_head, cut_formula, new_head @ [e2] @ new_tail, other_proof, new_p2)))
    | Plus_left_proof (head, e1, e2, tail, p) ->
        let new_head, new_tail = head_tail_permuted head tail permutation is_left in
        let new_proof = build_exchange (get_conclusion p) permutation p in
        if is_left
        then Plus_left_proof (new_head, e1, e2, new_tail @ cut_tail, cut_trans (Cut_proof (new_head @ [e1] @ new_tail, cut_formula, cut_tail, new_proof, other_proof)))
        else Plus_left_proof (cut_head @ new_head, e1, e2, new_tail, cut_trans (Cut_proof (cut_head, cut_formula, new_head @ [e1] @ new_tail, other_proof, new_proof)))
    | Plus_right_proof (head, e1, e2, tail, p) ->
        let new_head, new_tail = head_tail_permuted head tail permutation is_left in
        let new_proof = build_exchange (get_conclusion p) permutation p in
        if is_left
        then Plus_right_proof (new_head, e1, e2, new_tail @ cut_tail, cut_trans (Cut_proof (new_head @ [e2] @ new_tail, cut_formula, cut_tail, new_proof, other_proof)))
        else Plus_right_proof (cut_head @ new_head, e1, e2, new_tail, cut_trans (Cut_proof (cut_head, cut_formula, new_head @ [e2] @ new_tail, other_proof, new_proof)))
    | Promotion_proof (head_without_whynot, e, tail_without_whynot, p) -> begin
        let new_head_without_whynot, new_tail_without_whynot = head_tail_permuted head_without_whynot tail_without_whynot permutation is_left in
        let new_head, new_tail = add_whynot new_head_without_whynot, add_whynot new_tail_without_whynot in
        let new_proof = build_exchange (get_conclusion p) permutation p in
        try if is_left
            then Promotion_proof (new_head_without_whynot, e, new_tail_without_whynot @ (remove_whynot cut_tail),
                cut_trans (Cut_proof (new_head @ [e] @ new_tail, cut_formula, cut_tail, new_proof, other_proof)))
            else Promotion_proof ((remove_whynot cut_head) @ new_head_without_whynot, e, new_tail_without_whynot,
                cut_trans (Cut_proof (cut_head, cut_formula, new_head @ [e] @ new_tail, other_proof, new_proof)))
        with Not_whynot -> raise (Transform_exception "Cut context is not whynot context") end
    | Dereliction_proof (head, e, tail, p) ->
        let new_head, new_tail = head_tail_permuted head tail permutation is_left in
        let new_proof = build_exchange (get_conclusion p) permutation p in
        if is_left
        then Dereliction_proof (new_head, e, new_tail @ cut_tail, cut_trans (Cut_proof (new_head @ [e] @ new_tail, cut_formula, cut_tail, new_proof, other_proof)))
        else Dereliction_proof (cut_head @ new_head, e, new_tail, cut_trans (Cut_proof (cut_head, cut_formula, new_head @ [e] @ new_tail, other_proof, new_proof)))
    | Weakening_proof (head, e, tail, p) ->
        let new_permutation = perm_minus_element (List.length head) permutation in
        let new_proof = build_exchange (get_conclusion p) new_permutation p in
        let cut_formula_position = List.nth permutation (if is_left then List.length cut_head else 0) in
        if cut_formula_position = List.length head
        then
            try
                if is_left
                then weaken new_proof cut_head [] (remove_whynot cut_tail)
                else weaken new_proof [] cut_tail (remove_whynot cut_head)
            with Not_whynot -> raise (Transform_exception "Can not eliminate cut on this weakening since the other side doesn't have whynot context")
        else
            let new_head, new_tail = head_tail_permuted head tail permutation is_left in
            if is_left
            then Weakening_proof (new_head, e, new_tail @ cut_tail, cut_trans (Cut_proof (new_head @ new_tail, cut_formula, cut_tail, new_proof, other_proof)))
            else Weakening_proof (cut_head @ new_head, e, new_tail, cut_trans (Cut_proof (cut_head, cut_formula, new_head @ new_tail, other_proof, new_proof)))
    | Contraction_proof (head, e, tail, p) ->
        let new_permutation = perm_plus_element (List.length head) permutation in
        let new_proof = build_exchange (get_conclusion p) new_permutation p in
        let cut_formula_position = List.nth permutation (if is_left then List.length cut_head else 0) in
        if cut_formula_position = List.length head then
            if is_left
            then
                let second_cut = cut_trans (Cut_proof (cut_head @ [cut_formula], cut_formula, cut_tail, new_proof, other_proof)) in
                let second_exchange_proof = move_right (List.length cut_head) 0 second_cut in
                let first_cut = cut_trans (Cut_proof (cut_head @ cut_tail, cut_formula, cut_tail, second_exchange_proof, other_proof)) in
                let sort_perm = List.init (List.length cut_head) (fun n -> n)
                    @ List.init (2 * List.length cut_tail) (fun n -> (List.length cut_head) + n / 2 + (n mod 2) * (List.length cut_tail)) in
                let first_exchange = build_exchange (cut_head @ cut_tail @ cut_tail) sort_perm first_cut in
                try contract first_exchange cut_head [] (remove_whynot cut_tail)
                with Not_whynot -> raise (Transform_exception "Can not eliminate cut on this contraction since cut_tail doesn't have whynot context")
            else
                let second_cut = cut_trans (Cut_proof (cut_head, cut_formula, [dual cut_formula] @ cut_tail, other_proof, new_proof)) in
                let second_exchange_proof = move_left 0 (List.length cut_tail) second_cut in
                let first_cut = cut_trans (Cut_proof (cut_head, cut_formula, cut_head @ cut_tail, other_proof, second_exchange_proof)) in
                let sort_perm = List.init (2 * List.length cut_head) (fun n -> n / 2 + (n mod 2) * (List.length cut_head))
                    @ List.init (List.length cut_tail) (fun n -> 2 * List.length cut_head + n) in
                let first_exchange = build_exchange (cut_head @ cut_head @ cut_tail) sort_perm first_cut in
                try contract first_exchange [] cut_tail (remove_whynot cut_head)
                with Not_whynot -> raise (Transform_exception "Can not eliminate cut on this contraction since cut_head doesn't have whynot context")
        else
            let new_head, new_tail = head_tail_permuted head tail permutation is_left in
            if is_left
            then Contraction_proof (new_head, e, new_tail @ cut_tail, cut_trans (Cut_proof (new_head @ [Whynot e; Whynot e] @ new_tail, cut_formula, cut_tail, new_proof, other_proof)))
            else Contraction_proof (cut_head @ new_head, e, new_tail, cut_trans (Cut_proof (cut_head, cut_formula, new_head @ [Whynot e; Whynot e] @ new_tail, other_proof, new_proof)))
    | Unfold_litt_proof (head, s, tail, p) when List.mem_assoc s notations ->
            let new_head, new_tail = head_tail_permuted head tail permutation is_left in
            let new_proof = build_exchange (get_conclusion p) permutation p in
            let formula = Raw_sequent.to_formula (List.assoc s notations) in
            if is_left
            then Unfold_litt_proof (new_head, s, new_tail @ cut_tail, cut_trans (Cut_proof (new_head @ [formula] @ new_tail, cut_formula, cut_tail, new_proof, other_proof)))
            else Unfold_litt_proof (cut_head @ new_head, s, new_tail, cut_trans (Cut_proof (cut_head, cut_formula, new_head @ [formula] @ new_tail, other_proof, new_proof)))
    | Unfold_dual_proof (head, s, tail, p) when List.mem_assoc s notations ->
            let new_head, new_tail = head_tail_permuted head tail permutation is_left in
            let new_proof = build_exchange (get_conclusion p) permutation p in
            let formula = dual (Raw_sequent.to_formula (List.assoc s notations)) in
            if is_left
            then Unfold_dual_proof (new_head, s, new_tail @ cut_tail, cut_trans (Cut_proof (new_head @ [formula] @ new_tail, cut_formula, cut_tail, new_proof, other_proof)))
            else Unfold_dual_proof (cut_head @ new_head, s, new_tail, cut_trans (Cut_proof (cut_head, cut_formula, new_head @ [formula] @ new_tail, other_proof, new_proof)))
    | Cut_proof (head, formula, tail, p1, p2) ->
        cut_elimination_cut cut_head cut_formula cut_tail other_proof is_left permutation head formula tail p1 p2 cut_trans
    | Exchange_proof (_, _display_permutation, exchange_permutation, p) ->
        cut_elimination_with_permutation cut_head cut_formula cut_tail other_proof is_left (permute permutation exchange_permutation) notations cut_trans p
    | _ -> raise (Transform_exception "Can not eliminate cut on this side")


let rec cut_elimination is_left notations cut_trans = function
    | Cut_proof (cut_head, cut_formula, cut_tail, cut_p1, cut_p2) -> begin
        if is_left
        then cut_elimination_with_permutation cut_head cut_formula cut_tail cut_p2 is_left (identity (List.length cut_head + 1)) notations cut_trans cut_p1
        else cut_elimination_with_permutation cut_head cut_formula cut_tail cut_p1 is_left (identity (List.length cut_tail + 1)) notations cut_trans cut_p2
    end
    | Exchange_proof (s, display_permutation, exchange_permutation, p) ->
        merge_exchange (Exchange_proof (s, display_permutation, exchange_permutation, cut_elimination is_left notations cut_trans p))
    | _-> raise (Transform_exception "Can only eliminate cut on Cut_proof or Exchange_proof")


(* CUT ELIMINATION KEY CASE *)

let cut_element head1 tail1 head2 tail2 e p1 p2 permutation_without_cut_formula cut_trans =
    let new_p1 = move_right (List.length head1) 0 p1 in
    let new_p2 = move_left 0 (List.length tail2) p2 in
    let cut_e = cut_trans (Cut_proof (head1 @ tail1, e, head2 @ tail2, new_p1, new_p2)) in
    build_exchange (head1 @ tail1 @ head2 @ tail2) permutation_without_cut_formula cut_e

let rec eliminate_cut_key_case cut_head cut_formula cut_tail cut_p1 cut_p2 perm1 perm2 notations cut_trans =
    let cut_formula_position1 = List.nth perm1 (List.length cut_head) in
    let cut_formula_position2 = List.nth perm2 0 in
    let permutation_without_cut_formula = perm_minus_element cut_formula_position1 perm1
        @ List.map (fun n -> List.length cut_head + n) (perm_minus_element cut_formula_position2 perm2) in

    match cut_p1, cut_p2 with
    | One_proof, Bottom_proof (head, tail, p) | Bottom_proof (head, tail, p), One_proof ->
        build_exchange (head @ tail) permutation_without_cut_formula p
    | Tensor_proof (head1, e1, e2, tail1, p1, p2), Par_proof (head2, _dual_e1, _dual_e2, tail2, p) ->
        (* head2 @ [dual e1] @ [dual e2] @ tail2    *)
        (* ------------------------------------- Ex *)
        (* [dual e2] @ head2 @ [dual e1] @ tail2    *)
        let new_p = move_left 0 (List.length tail2) p in

        (* [e2] @ tail1     *)
        (* ------------- Ex *)
        (* tail1 @ [e2]     *)
        let new_p2 = move_right 0 0 p2 in

        (* tail1 @ [e2]  [dual e2] @ head2 @ [dual e1] @ tail2     *)
        (* --------------------------------------------------- Cut *)
        (*              tail1 @ head2 @ [dual e1] @ tail2          *)
        let cut_e2 = cut_trans (Cut_proof (tail1, e2, head2 @ [dual e1] @ tail2, new_p2, new_p)) in

        (* tail1 @ head2 @ [dual e1] @ tail2    *)
        (* --------------------------------- Ex *)
        (* [dual e1] @ tail1 @ head2 @ tail2    *)
        let exchange_proof = move_left 0 (List.length tail2) cut_e2 in

        (* head1 @ [e1]  [dual e1] @ tail1 @ head2 @ tail2     *)
        (* ----------------------------------------------- Cut *)
        (*             head1 @ tail1 @ head2 @ tail2           *)
        let cut_e1 = cut_trans (Cut_proof (head1, e1, tail1 @ head2 @ tail2, p1, exchange_proof)) in

        (* head1 @ tail1 @ head2 @ tail2    *)
        (* ----------------------------- Ex *)
        (*       cut_head @ cut_tail        *)
        build_exchange (head1 @ tail1 @ head2 @ tail2) permutation_without_cut_formula cut_e1
    | Par_proof (head1, e1, e2, tail1, p), Tensor_proof (head2, _dual_e1, _dual_e2, tail2, p1, p2) ->
        (* head1 @ [e1; e2] @ tail1       *)
        (* --------------------------- Ex *)
        (* head1 @ [e2] @ tail1 @ [e1]    *)
        let new_p = move_right (List.length head1) 0 p in

        (* head2 @ [dual e1]    *)
        (* ----------------- Ex *)
        (* [dual e1] @ head2    *)
        let new_p1 = move_left 0 0 p1 in

        (* head1 @ [e2] @ tail1 @ [e1]  [dual e1] @ head2     *)
        (* ---------------------------------------------- Cut *)
        (*            head1 @ [e2] @ tail1 @ head2            *)
        let cut_e1 = cut_trans (Cut_proof (head1 @ [e2] @ tail1, e1, head2, new_p, new_p1)) in

        (* head1 @ [e2] @ tail1 @ head2    *)
        (* ---------------------------- Ex *)
        (* head1 @ tail1 @ head2 @ [e2]    *)
        let exchange_proof = move_right (List.length head1) 0 cut_e1 in

        (* head1 @ tail1 @ head2 @ [e2]  [dual e2] @ tail2     *)
        (* ----------------------------------------------- Cut *)
        (*             head1 @ tail1 @ head2 @ tail2           *)
        let cut_e2 = cut_trans (Cut_proof (head1 @ tail1 @ head2, e2, tail2, exchange_proof, p2)) in

        (* head1 @ tail1 @ head2 @ tail2    *)
        (* ----------------------------- Ex *)
        (*       cut_head @ cut_tail        *)
        build_exchange (head1 @ tail1 @ head2 @ tail2) permutation_without_cut_formula cut_e2
    | With_proof (head1, e1, _e2, tail1, p1, _p2), Plus_left_proof (head2, _dual_e1, _dual_e2, tail2, p) ->
        cut_element head1 tail1 head2 tail2 e1 p1 p permutation_without_cut_formula cut_trans
    | With_proof (head1, _e1, e2, tail1, _p1, p2), Plus_right_proof (head2, _dual_e1, _dual_e2, tail2, p) ->
        cut_element head1 tail1 head2 tail2 e2 p2 p permutation_without_cut_formula cut_trans
    | Plus_left_proof (head1, e1, _e2, tail1, p), With_proof (head2, _dual_e1, _dual_e2, tail2, p1, _p2) ->
        cut_element head1 tail1 head2 tail2 e1 p p1 permutation_without_cut_formula cut_trans
    | Plus_right_proof (head1, _e1, e2, tail1, p), With_proof (head2, _dual_e1, _dual_e2, tail2, _p1, p2) ->
        cut_element head1 tail1 head2 tail2 e2 p p2 permutation_without_cut_formula cut_trans
    | Promotion_proof (head_without_whynot, formula, tail_without_whynot, p1), Dereliction_proof (head2, _dual_formula, tail2, p2) ->
        let head1 = add_whynot head_without_whynot in
        let tail1 = add_whynot tail_without_whynot in
        cut_element head1 tail1 head2 tail2 formula p1 p2 permutation_without_cut_formula cut_trans
    | Dereliction_proof (head1, formula, tail1, p1), Promotion_proof (head_without_whynot, _dual_formula, tail_without_whynot, p2) ->
        let head2 = add_whynot head_without_whynot in
        let tail2 = add_whynot tail_without_whynot in
        cut_element head1 tail1 head2 tail2 formula p1 p2 permutation_without_cut_formula cut_trans
    | Unfold_litt_proof (head1, s, tail1, p1), Unfold_dual_proof (head2, _s, tail2, p2) when List.mem_assoc s notations ->
        let formula = Raw_sequent.to_formula (List.assoc s notations) in
        cut_element head1 tail1 head2 tail2 formula p1 p2 permutation_without_cut_formula cut_trans
    | Unfold_dual_proof (head1, s, tail1, p1), Unfold_litt_proof (head2, _s, tail2, p2) when List.mem_assoc s notations ->
        let formula = dual (Raw_sequent.to_formula (List.assoc s notations)) in
        cut_element head1 tail1 head2 tail2 formula p1 p2 permutation_without_cut_formula cut_trans
    | Exchange_proof (_, _display_permutation, exchange_permutation, p), _ ->
        eliminate_cut_key_case cut_head cut_formula cut_tail p cut_p2 (permute perm1 exchange_permutation) perm2 notations cut_trans
    | _, Exchange_proof (_, _display_permutation, exchange_permutation, p) ->
        eliminate_cut_key_case cut_head cut_formula cut_tail cut_p1 p perm1 (permute perm2 exchange_permutation) notations cut_trans
    | _ -> raise (Failure "Can not eliminate cut key-case on these two proofs")

let rec cut_elimination_key_case notations cut_trans = function
    | Cut_proof (cut_head, cut_formula, cut_tail, cut_p1, cut_p2) ->
        eliminate_cut_key_case cut_head cut_formula cut_tail cut_p1 cut_p2 (identity (List.length cut_head + 1)) (identity (List.length cut_tail + 1)) notations cut_trans
    | Exchange_proof (s, display_permutation, exchange_permutation, p) ->
        merge_exchange (Exchange_proof (s, display_permutation, exchange_permutation, cut_elimination_key_case notations cut_trans p))
    | _-> raise (Transform_exception "Can only eliminate cut key-case on Cut_proof or Exchange_proof")

(* ELIMINATE CUT FULL *)

let eliminate_cut notations cut_head cut_formula cut_tail cut_p1 cut_p2 cut_trans =
    let cut_proof = Cut_proof (cut_head, cut_formula, cut_tail, cut_p1, cut_p2) in
    if can_commute_on_left notations cut_proof
    then cut_elimination true notations cut_trans cut_proof
    else if can_commute_on_right notations cut_proof
    then cut_elimination false notations cut_trans cut_proof
    else if can_eliminate_key_case notations cut_proof
    then cut_elimination_key_case notations cut_trans cut_proof
    else cut_proof

let rec eliminate_cut_full acyclic_notations = function
    | Cut_proof (cut_head, cut_formula, cut_tail, cut_p1, cut_p2) ->
        eliminate_cut acyclic_notations cut_head cut_formula cut_tail cut_p1 cut_p2 (eliminate_cut_full acyclic_notations)
    | Exchange_proof (s, display_permutation, exchange_permutation, p) ->
        merge_exchange (Exchange_proof (s, display_permutation, exchange_permutation, eliminate_cut_full acyclic_notations p))
    | _-> raise (Transform_exception "Can only eliminate cut full on Cut_proof or Exchange_proof")

(* ELIMINATE ALL CUTS *)

let rec eliminate_all_cuts_in_proof acyclic_notations = function
    | Cut_proof (cut_head, cut_formula, cut_tail, cut_p1, cut_p2) ->
        let p1 = eliminate_all_cuts_in_proof acyclic_notations cut_p1 in
        let p2 = eliminate_all_cuts_in_proof acyclic_notations cut_p2 in
        eliminate_cut acyclic_notations cut_head cut_formula cut_tail p1 p2 (eliminate_cut_full acyclic_notations)
    | Exchange_proof (s, display_permutation, exchange_permutation, p) ->
        merge_exchange (Exchange_proof (s, display_permutation, exchange_permutation, eliminate_all_cuts_in_proof acyclic_notations p))
    | proof -> set_premises proof (List.map (eliminate_all_cuts_in_proof acyclic_notations) (get_premises proof))

(* COMMUTE DOWN REVERSIBLE RULES *)

let replace_at_length position formulas offset head tail =
    if position < List.length head then
         let head1, _, head2 = head_formula_tail position head in
         head1 @ formulas @ head2, tail, position
    else let tail1, _, tail2 = head_formula_tail (position - List.length head - 1) tail in
        head, tail1 @ formulas @ tail2, position + offset

let rec commute_down_reversible position formulas is_left_with notations = function
    | Axiom_proof e -> commute_down_reversible position formulas is_left_with notations (expand_axiom notations e)
    | One_proof -> raise (Failure "One_proof not expected")
    | Top_proof (head, tail) ->
        let new_head, new_tail, _ = replace_at_length position formulas 0 head tail in
        Top_proof (new_head, new_tail)
    | Bottom_proof (head, tail, p) ->
        if List.length head = position
        then p
        else let new_head, new_tail, new_position = replace_at_length position formulas (-1) head tail in
            Bottom_proof (new_head, new_tail, commute_down_reversible new_position formulas is_left_with notations p)
    | Tensor_proof (head, e1, e2, tail, p1, p2) ->
        let new_head, new_tail, _ = replace_at_length position formulas 0 head tail in
        if position < List.length head then
            Tensor_proof (new_head, e1, e2, tail, commute_down_reversible position formulas is_left_with notations p1, p2)
        else Tensor_proof (head, e1, e2, new_tail, p1, commute_down_reversible (position - List.length head) formulas is_left_with notations p2)
    | Par_proof (head, e1, e2, tail, p) ->
        if List.length head = position
        then p
        else let new_head, new_tail, new_position = replace_at_length position formulas 1 head tail in
            Par_proof (new_head, e1, e2, new_tail, commute_down_reversible new_position formulas is_left_with notations p)
    | With_proof (head, e1, e2, tail, p1, p2) ->
        if List.length head = position
        then if is_left_with then p1 else p2
        else let new_head, new_tail, new_position = replace_at_length position formulas 0 head tail in
            let new_p1 = commute_down_reversible new_position formulas is_left_with notations p1 in
            let new_p2 = commute_down_reversible new_position formulas is_left_with notations p2 in
            With_proof (new_head, e1, e2, new_tail, new_p1, new_p2)
    | Plus_left_proof (head, e1, e2, tail, p) ->
        let new_head, new_tail, new_position = replace_at_length position formulas 0 head tail in
        Plus_left_proof (new_head, e1, e2, new_tail, commute_down_reversible new_position formulas is_left_with notations p)
    | Plus_right_proof (head, e1, e2, tail, p) ->
        let new_head, new_tail, new_position = replace_at_length position formulas 0 head tail in
        Plus_right_proof (new_head, e1, e2, new_tail, commute_down_reversible new_position formulas is_left_with notations p)
    | Promotion_proof (head_without_whynot, _e, _tail_without_whynot, p) ->
        if List.length head_without_whynot = position
        then p
        else raise (Failure "Promotion_proof not expected")
    | Dereliction_proof (head, e, tail, p) ->
        let new_head, new_tail, new_position = replace_at_length position formulas 0 head tail in
        Dereliction_proof (new_head, e, new_tail, commute_down_reversible new_position formulas is_left_with notations p)
    | Weakening_proof (head, e, tail, p) ->
        let new_head, new_tail, new_position = replace_at_length position formulas (-1) head tail in
        Weakening_proof (new_head, e, new_tail, commute_down_reversible new_position formulas is_left_with notations p)
    | Contraction_proof (head, e, tail, p) ->
        let new_head, new_tail, new_position = replace_at_length position formulas 1 head tail in
        Contraction_proof (new_head, e, new_tail, commute_down_reversible new_position formulas is_left_with notations p)
    | Unfold_litt_proof (head, s, tail, p) ->
        let new_head, new_tail, new_position = replace_at_length position formulas 0 head tail in
        Unfold_litt_proof (new_head, s, new_tail, commute_down_reversible new_position formulas is_left_with notations p)
    | Unfold_dual_proof (head, s, tail, p) ->
        let new_head, new_tail, new_position = replace_at_length position formulas 0 head tail in
        Unfold_dual_proof (new_head, s, new_tail, commute_down_reversible new_position formulas is_left_with notations p)
    | Cut_proof (head, f, tail, p1, p2) ->
        let new_head, new_tail, _ = replace_at_length position formulas 0 head tail in
        if position < List.length head then
            Cut_proof (new_head, f, tail, commute_down_reversible position formulas is_left_with notations p1, p2)
        else Cut_proof (head, f, new_tail, p1, commute_down_reversible (position - List.length head + 1) formulas is_left_with notations p2)
    | Exchange_proof (_, _display_permutation, permutation, p) ->
        let new_position = List.nth permutation position in
        let new_perm = match formulas with
        | [] -> perm_minus_element new_position permutation
        | [_] -> permutation
        | [_; _] -> perm_plus_element new_position permutation
        | _ -> raise (Failure "formulas with more than 2 elements") in
        let new_proof = commute_down_reversible new_position formulas is_left_with notations p in
        Exchange_proof (get_conclusion new_proof, new_perm, new_perm, new_proof)
    | Hypothesis_proof sequent -> let new_sequent, _, _ = replace_at_length position formulas 0 sequent [] in
        Hypothesis_proof new_sequent

let apply_reversible_first notations rule_request proof =
    let sequent = get_conclusion proof in
    match rule_request with
    | Rule_request.Bottom formula_position -> begin
        let head, formula, tail = head_formula_tail formula_position sequent in
        match formula with
        | Bottom -> Bottom_proof (head, tail, commute_down_reversible formula_position [] false notations proof)
        | _ -> raise (Transform_exception "Can not apply 'bottom' rule")
    end
    | Rule_request.Top formula_position -> begin
        let head, formula, tail = head_formula_tail formula_position sequent in
        match formula with
        | Top -> Top_proof (head, tail)
        | _ -> raise (Transform_exception "Can not apply 'top' rule")
    end
    | Rule_request.Par formula_position -> begin
        let head, formula, tail = head_formula_tail formula_position sequent in
        match formula with
        | Par (e1, e2) -> Par_proof (head, e1, e2, tail, commute_down_reversible formula_position [e1; e2] false notations proof)
        | _ -> raise (Transform_exception "Can not apply 'par' rule")
    end
    | Rule_request.With formula_position -> begin
        let head, formula, tail = head_formula_tail formula_position sequent in
        match formula with
        | With (e1, e2) -> let p1 = commute_down_reversible formula_position [e1] true notations proof in
            let p2 = commute_down_reversible formula_position [e2] false notations proof in
            With_proof (head, e1, e2, tail, p1, p2)
        | _ -> raise (Transform_exception "Can not apply 'with' rule")
    end
    | Rule_request.Promotion formula_position -> begin
        let head, formula, tail = head_formula_tail formula_position sequent in
        try let head_without_whynot = remove_whynot head in
            let tail_without_whynot = remove_whynot tail in
            match formula with
            | Ofcourse e -> Promotion_proof (head_without_whynot, e, tail_without_whynot, commute_down_reversible formula_position [e] false notations proof)
            | _ -> raise (Transform_exception "Can not apply 'promotion' rule on non Ofcourse formula")
        with Not_whynot -> raise (Pedagogic_exception "Can not apply 'promotion' rule: the context must contain formulas starting by '?' only.")
    end
    | _ -> raise (Transform_exception "Not a reversible rule")

(* OPERATIONS *)

let get_transformation_options_json proof notations not_cyclic =
    Proof.to_json ~add_options:(get_transform_options_as_json notations not_cyclic) proof;;

let check_all_cuts_elimination notations not_cyclic proof=
    not_cyclic && has_cut_that_can_be_eliminated notations not_cyclic proof

let check_simplification proof =
    proof <> Proof_simplification.simplify proof

let apply_transformation_with_exceptions proof cyclic_notations acyclic_notations = function
    | Expand_axiom -> expand_axiom_on_proof (cyclic_notations @ acyclic_notations) proof
    | Expand_axiom_full -> expand_axiom_full acyclic_notations proof
    | Eliminate_cut_left -> cut_elimination true (cyclic_notations @ acyclic_notations) (fun p -> p) proof
    | Eliminate_cut_right -> cut_elimination false (cyclic_notations @ acyclic_notations) (fun p -> p) proof
    | Eliminate_cut_key_case -> cut_elimination_key_case (cyclic_notations @ acyclic_notations) (fun p -> p) proof
    | Eliminate_cut_full -> eliminate_cut_full acyclic_notations proof
    | Eliminate_all_cuts -> eliminate_all_cuts_in_proof acyclic_notations proof
    | Simplify -> Proof_simplification.simplify proof
    | Substitute (alias, raw_formula) -> Proof.replace_in_proof alias (Raw_sequent.to_formula raw_formula) proof
    | Apply_reversible_first rule_request -> apply_reversible_first (cyclic_notations @ acyclic_notations) rule_request proof
    ;;

let apply_transformation_on_notations notations = function
    | Substitute (alias, raw_formula) -> Notations.replace_in_notations alias raw_formula notations
    | _ -> notations
    ;;

(* HANDLERS *)

let get_proof_transformation_options request_as_json =
    try let proof_with_notations = Proof_with_notations.from_json request_as_json in
        let proof_variables = Proof.get_unique_variable_names proof_with_notations.proof in
        let cyclic_notations, _ = Notations.split_cyclic_acyclic proof_with_notations.notations (Some proof_variables) in
        let not_cyclic = (List.length cyclic_notations = 0) in
        let proof_with_transformation_options = get_transformation_options_json proof_with_notations.proof proof_with_notations.notations not_cyclic in
        let can_eliminate_all_cuts = check_all_cuts_elimination proof_with_notations.notations not_cyclic proof_with_notations.proof in
        let can_simplify = check_simplification proof_with_notations.proof in
        let notations_as_string = Notations.to_json ~stringify:true proof_with_notations.notations in
        true, `Assoc [
            "proofWithTransformationOptions", proof_with_transformation_options;
            "canSimplify", `Bool can_simplify;
            "canEliminateAllCuts", `Bool can_eliminate_all_cuts;
            "notationsAsString", notations_as_string]
    with Proof_with_notations.Json_exception m -> false, `String ("Bad request: " ^ m);;

let apply_transformation request_as_json =
    try let proof_with_notations = Proof_with_notations.from_json request_as_json in
        let transform_request_as_json = Request_utils.get_key request_as_json "transformRequest" in
        let transform_request = Transform_request.from_json transform_request_as_json in
        let cyclic_notations, acyclic_notations = Notations.split_cyclic_acyclic proof_with_notations.notations None in
        let proof = apply_transformation_with_exceptions proof_with_notations.proof cyclic_notations acyclic_notations transform_request in
        let notations = apply_transformation_on_notations proof_with_notations.notations transform_request in
        true, `Assoc ["proof", Proof.to_json proof; "notations", Notations.to_json notations]
    with Proof_with_notations.Json_exception m -> false, `String ("Bad proof with notations: " ^ m)
        | Request_utils.Bad_request_exception m -> false, `String ("Bad request: " ^ m)
        | Transform_request.Json_exception m -> false, `String ("Bad transformation request: " ^ m)
        | Transform_exception m -> false, `String ("Transform exception: " ^ m)
        | Pedagogic_exception m -> true, `Assoc ["error_message", `String m];;
