open Sequent
open Proof

let rec build_exchange sequent perm p =
    if perm = List.init (List.length perm) (fun n -> n)
    then p
    else merge_exchange (Exchange_proof (sequent, perm, perm, p))

and merge_exchange = function
    | Exchange_proof (_s, _dperm, perm, Exchange_proof (s', _dperm', perm', p)) ->
        let new_perm = permute perm' perm in
        build_exchange s' new_perm p
    | proof -> proof

let move_left left_offset right_offset proof =
    let sequent = get_conclusion proof in
    let n = List.length sequent in
    if left_offset >= n - right_offset then proof
    else let permutation = List.init left_offset (fun k -> k)
            @ [n - right_offset - 1]
            @ List.init (n - right_offset - left_offset - 1) (fun k -> left_offset + k)
            @ List.init right_offset (fun k -> n - right_offset + k) in
        build_exchange sequent permutation proof

let move_right left_offset right_offset proof =
    let sequent = get_conclusion proof in
    let n = List.length sequent in
    if left_offset >= n - right_offset then proof
    else let permutation = List.init left_offset (fun k -> k)
            @ List.init (n - right_offset - left_offset - 1) (fun k -> left_offset + 1 + k)
            @ [left_offset]
            @ List.init right_offset (fun k -> n - right_offset + k) in
        build_exchange sequent permutation proof

let shift_block start offset length proof =
    if offset = 0
    then proof
    else let sequent = get_conclusion proof in
        let n = List.length sequent in
        let permutation = List.init start (fun k -> k)
            @ List.init length (fun k -> start + offset + k)
            @ List.init offset (fun k -> start + k)
            @ List.init (n - start - length - offset) (fun k -> start + offset + length + k) in
        build_exchange sequent permutation proof

let perm_minus_element n perm =
    List.map (fun k -> if k > n then k - 1 else k) (List.filter (fun k -> k <> n) perm)

let perm_plus_element n perm =
    List.concat_map (fun k -> if k = n then [n; n + 1] else if k > n then [k + 1] else [k]) perm

let remove_nth_element n perm =
    List.filter (fun k -> k <> n) perm

let duplicate_nth_element n perm =
    List.concat_map (fun k -> if k = n then [n; n] else [k]) perm

(* HEAD / TAIL *)

let rec head_tail element = function
    | [] -> raise (Failure "element not found")
    | e :: l -> if e = element then [], l else let head, tail = head_tail element l in e :: head, tail

let head_tail_perm head perm =
    let n_head = List.length head in
    head_tail n_head perm


(* PERMUTE PROOF *)

let rec index_list offset = function
    | [] -> []
    | e :: tail -> (e, offset) :: index_list (offset + 1) tail

let rec head_index_tail element = function
    | [] -> raise (Failure "Could not find element in list")
    | (e, i) :: l -> if e = element then [], i, l
        else let head, index, tail = head_index_tail element l in
        (e, i) :: head, index, tail

let rec get_permutation indexed_list = function
    | [] -> []
    | e :: l -> let head, i, tail = head_index_tail e indexed_list in i :: (get_permutation (head @ tail) l)

let permute_proof proof sequent_below =
    let sequent = get_conclusion proof in
    let indexed_sequent = index_list 0 sequent in
    let permutation = get_permutation indexed_sequent sequent_below in
    build_exchange sequent permutation proof

(* REC WEAKENINGS AND CONTRACTIONS *)

let rec weaken proof head tail = function
    | [] -> proof
    | e :: l -> Weakening_proof (head, e, add_whynot l @ tail, weaken proof head tail l)

let rec contract proof head tail = function
    | [] -> proof
    | e :: l -> Contraction_proof (head, e, (add_whynot l) @ tail, contract proof (head @ [Whynot e; Whynot e]) tail l)