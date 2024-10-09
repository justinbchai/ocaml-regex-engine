open P3.Nfa
open P3.Regexp
open OUnit2

(* general helpers *)
let assert_true x = assert_equal true x

let assert_false x = assert_equal false x

let assert_pass () = assert_equal true true

let assert_fail () = assert_equal false false

let string_of_int_list l =
  Printf.sprintf "[%s]" @@ String.concat "; " @@ List.map string_of_int l

let string_of_int_list_list l =
  Printf.sprintf "[%s]" @@ String.concat "; " @@ List.map string_of_int_list l

let assert_dfa m =
  let nondet =
    List.fold_left
      (fun res (q, c, _) ->
        match c with
        | None -> true
        | Some _ ->
            let others =
              List.filter (fun (q', c', _) -> q' = q && c' = c) m.delta
            in
            res || List.length others > 1 )
      false m.delta
  in
  if nondet then (assert_equal true false ~msg:"not a dfa")

let re_to_str r =
  let surround l = ("(" :: l) @ [")"] in
  let rec r2str = function
    | Empty_String -> ["E"]
    | Char c -> [String.make 1 c]
    | Union (r1, r2) ->
        let l1 = surround @@ r2str r1 and l2 = surround @@ r2str r2 in
        l1 @ ("|" :: l2)
    | Concat (r1, r2) ->
        let l1 = surround @@ r2str r1 and l2 = surround @@ r2str r2 in
        l1 @ l2
    | Star r1 ->
        let l1 = surround @@ r2str r1 in
        l1 @ ["*"]
  in
  String.concat "" (r2str r)

(* WRAPPERS *)

(************************)
(* (char, int list) NFA *)
(************************)

let str_of_int_lst_fsm fsm = 
  let {sigma;qs;q0;fs;delta} = fsm in 
  let rec string_of_list strfunc str lst delim = match lst with
    [] -> str
   |x::xs -> string_of_list strfunc (str ^ (strfunc x) ^ delim) xs delim in
  let sigstr = "sigma: [" ^ (string_of_list (fun x -> String.make 1 x) "" sigma ";") ^ "]\n" in
  let rec fold f a l = match l with
  [] -> a
  |x::xs -> fold f (f a x) xs in
  let qsstr = "qs: [" ^ (fold (fun a x -> a ^ "["^(string_of_list string_of_int "" x ";") ^ "];") "" qs) ^ "]\n" in
  let q0str = "q0: " ^ (string_of_list string_of_int ""  q0 ";") ^ "\n" in
  let fsstr = "fs: [" ^ (fold (fun a x -> a ^ "["^(string_of_list string_of_int "" x ";") ^ "];") "" fs) ^ "]\n" in
  let trans = "trans: [\n\t" ^ 
    (string_of_list (fun (s,opt,d) -> ((string_of_list string_of_int "" s ";") ^ "-" ^ 
      (match opt with
        None -> "ε"
       |Some(x) -> String.make 1 x
      ) ^ "->" ^ (string_of_list string_of_int "" d ";"))
    ) "" delta "\n\t") ^
    "]" in
  sigstr ^ qsstr ^ q0str ^ fsstr ^ trans


(***********************)
(*** (char, int) NFA ***)
(***********************)

(*** NFA TO STRING ***)
let str_of_int_fsm fsm = 
  let {sigma;qs;q0;fs;delta} = fsm in 
  let rec string_of_list strfunc str lst delim = match lst with
    [] -> str
   |x::xs -> string_of_list strfunc (str ^ (strfunc x) ^ delim) xs delim in
  let sigstr = "sigma: [" ^ (string_of_list (fun x -> String.make 1 x) "" sigma ";") ^ "]\n" in
  let qsstr = "qs: [" ^ (string_of_list string_of_int "" qs ";") ^ "]\n" in
  let q0str = "q0: " ^ (string_of_int q0) ^ "\n" in
  let fsstr = "f0: [" ^ (string_of_list string_of_int "" fs ";") ^ "]\n" in
  let trans = "trans: [\n\t" ^ 
    (string_of_list (fun (s,opt,d) -> ((string_of_int s) ^ "-" ^ 
      (match opt with
        None -> "ε"
       |Some(x) -> String.make 1 x
      ) ^ "->" ^ (string_of_int d))
    ) "" delta "\n\t") ^
    "]" in
  sigstr ^ qsstr ^ q0str ^ fsstr ^ trans

(***************)
(*** ANY FSM ***)
(***************)

(***********************)
(*** EPSILON CLOSURE ***)
(***********************)

let wrapper_eclosure m expects results printer= 
  let rec test_eclosure_aux e r = match (e,r) with
  ([],[]) -> true
  |_::_,[] -> (failwith ("Don't think this should happen - null set generated a eclosure"))
  |[],x::_ -> (failwith ("Don't think this should happen - "^ string_of_int_list x ^ "did not generate an eclosure"))
  |x::xs,y::ys -> 
    let _ = (assert_equal x y 
            ~msg:((printer m)^"\nThe eclosure of : " ^ string_of_int_list y ^ 
                " is " ^ string_of_int_list x ^ "' when it shouldn't be")) in
    test_eclosure_aux xs ys in
  test_eclosure_aux expects results

(************************)
(*** GENERALIZED MOVE ***)
(************************)

let wrapper_move m expects results printer= 
  let rec test_move_aux e r = match (e,r) with
  ([],[]) -> true
  |_::_,[] -> (failwith ("Don't think this should happen - null moved on a symbol"))
  |[],x::_ -> (failwith ("Don't think this should happen - "^ string_of_int_list x ^ "did not generate a move"))
  |x::xs,y::ys -> 
    let _ = (assert_equal x y 
            ~msg:((printer m)^"\nMoving on : " ^ string_of_int_list y ^ 
                "was supposed to result in " ^ string_of_int_list x ^ "' but it did not, or did so on the wrong character")) in
    test_move_aux xs ys in
  test_move_aux expects results

(**********************)
(*** ACCEPT THE FSM ***)
(**********************)


(*********************)
(*** ACCEPT A LIST ***)
(*********************)
let wrapper_accept m expects results printer= 
  let rec test_accept_aux e r = match (e,r) with
  ([],[]) -> true
  |x::_,[] -> (failwith ("accept failed to accept " ^ x))
  |[],x::_ -> (failwith ("accepted " ^ x ^ " when it should not have"))
  |x::xs,y::ys -> 
    let _ = (assert_equal x y 
            ~msg:((printer m)^"\neither does not accept '" ^ x ^ 
                "' or is accepting '" ^ y ^ "' when it shouldn't")) in
    test_accept_aux xs ys in
  test_accept_aux expects results

(*********************)
(*** ACCEPT SINGLE ***)
(*********************)
let wrapper_accept_sig m expects f s printer = 
    assert_equal expects (f m s)
            ~msg:((printer m)^
              if expects then 
              "\ndid not accept '" ^ s ^ "' when it should have" 
              else "\naccepted '" ^ s ^ "' when it shouldn't have");;

let wrapper_accept_s f m s p = wrapper_accept_sig m true  f s p;;
let wrapper_deny_s   f m s p = wrapper_accept_sig m false f s p;;
(********************)
(*** CHECK IF DFA ***)
(********************)

let wrapper_assert_dfa m printer =
  let nondet =
    List.fold_left
      (fun res (q, c, _) ->
        match c with
        | None -> true
        | Some _ ->
            let others =
              List.filter (fun (q', c', _) -> q' = q && c' = c) m.delta
            in
            res || List.length others > 1 )
      false m.delta
  in
  if nondet then (assert_equal true false ~msg:((printer m)^"\nis not a dfa"))

let wrapper_assert_dfas ms p = let _ = List.map (fun x -> wrapper_assert_dfa x p) ms in ()

(* Helpers for clearly testing the accept function *)
let assert_nfa_accept nfa input =
  if not @@ accept nfa input then
    assert_failure
    @@ Printf.sprintf "NFA should have accept string '%s', but did not" input

let assert_nfa_deny nfa input =
  if accept nfa input then
    assert_failure
    @@ Printf.sprintf "NFA should not have accepted string '%s', but did" input

let assert_nfa_closure nfa ss es =
  let es = List.sort compare es in
  let rcv = List.sort compare @@ e_closure nfa ss in
  if not (es = rcv) then
    assert_failure
    @@ Printf.sprintf "Closure failure: Expected %s, received %s"
         (string_of_int_list es) (string_of_int_list rcv)

let assert_nfa_move nfa ss mc es =
  let es = List.sort compare es in
  let rcv = List.sort compare @@ move nfa ss mc in
  if not (es = rcv) then
    assert_failure
    @@ Printf.sprintf "Move failure: Expected %s, received %s"
         (string_of_int_list es) (string_of_int_list rcv)

let assert_set_set_eq lst1 lst2 =
  let es l = List.sort_uniq compare (List.map (List.sort compare) l) in
  assert_equal (es lst1) (es lst2)

let assert_trans_eq lst1 lst2 =
  let es l =
    List.sort_uniq compare
      (List.map
         (fun (l1, t, l2) -> (List.sort compare l1, t, List.sort compare l2))
         l)
  in
  assert_equal (es lst1) (es lst2)

let assert_set_eq lst1 lst2 =
  let es = List.sort_uniq compare in
  assert_equal (es lst1) (es lst2)

let assert_regex_string_equiv rxp =
  assert_equal rxp @@ string_to_regexp @@ re_to_str rxp
