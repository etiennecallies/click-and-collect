exception Bad_request_exception of string

let get_key d k =
    let value =
        try Yojson.Basic.Util.member k d
        with Yojson.Basic.Util.Type_error (_, _) -> raise (Bad_request_exception ("Body must be a json object"))
    in
    if value = `Null
    then raise (Bad_request_exception ("required argument " ^ k ^" is missing"))
    else value

let get_string d k =
    let value = get_key d k in
    try Yojson.Basic.Util.to_string value
    with Yojson.Basic.Util.Type_error (_, _) -> raise (Bad_request_exception ("argument " ^ k ^" must be a string"))

let get_int d k =
    let value = get_key d k in
    try Yojson.Basic.Util.to_int value
    with Yojson.Basic.Util.Type_error (_, _) -> raise (Bad_request_exception ("argument " ^ k ^" must be an int"))

let get_list d k =
    let value = get_key d k in
    try Yojson.Basic.Util.to_list value
    with Yojson.Basic.Util.Type_error (_, _) -> raise (Bad_request_exception ("argument " ^ k ^" must be a list"))

let apply_rule_with_exceptions request_as_json =
    let rule = get_string request_as_json "rule" in
    let sequent_as_json = get_key request_as_json "sequent" in
    let formula_position = get_int request_as_json "formulaPosition" in
    let sequent = Linear_logic.json_to_sequent sequent_as_json in
    Linear_logic.apply_rule rule sequent formula_position

let apply_rule request_as_json =
    try let sequent_list = apply_rule_with_exceptions request_as_json in
        true, `List (List.map Linear_logic.sequent_to_json sequent_list)
    with
        | Bad_request_exception m -> false, `String m
        | Linear_logic.Bad_sequent_json_exception m -> false, `String  ("Bad formula json: " ^ m)
        | Linear_logic.Apply_rule_exception m -> false, `String  m