open List
open Sets

(*********)
(* Types *)
(*********)

type ('q, 's) transition = 'q * 's option * 'q

type ('q, 's) nfa_t = {
  sigma : 's list;
  qs : 'q list;
  q0 : 'q;
  fs : 'q list;
  delta : ('q, 's) transition list;
}

(***********)
(* Utility *)
(***********)

(* explode converts a string to a character list *)
let explode (s : string) : char list =
  let rec exp i l = if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

(****************)
(* Part 1: NFAs *)
(****************)

(* for each transition in nfa.delta, match it with (src, char, dest). if src is in qs and char = s,
   add dest to res *)
let move (nfa : ('q, 's) nfa_t) (qs : 'q list) (s : 's option) : 'q list =
  let sigma = map (fun y -> Some y) nfa.sigma in
  if s != None && not (elem s sigma) then []
  else
    fold_left
      (fun acc t ->
        match t with
        | src, None, dest ->
            if s = None && elem src qs then insert dest acc else acc
        | src, char, dest ->
            if char = s && elem src qs then insert dest acc else acc)
      [] nfa.delta

(* while the set is larger than before, call move with s = None *)
let e_closure (nfa : ('q, 's) nfa_t) (qs : 'q list) : 'q list =
  let rec e_closure_aux acc prev_size =
    let acc = union acc (move nfa acc None) in
    if List.length acc = prev_size then acc
    else e_closure_aux acc (List.length acc)
  in
  e_closure_aux qs 0

let accept (nfa : ('q, char) nfa_t) (s : string) : bool =
  let c_arr = explode s in
  let rec accept_aux qs c_arr =
    match c_arr with
    | [] -> length (intersection qs nfa.fs) > 0
    | h :: t -> accept_aux (e_closure nfa (move nfa qs (Some h))) t
  in
  accept_aux (e_closure nfa [nfa.q0]) c_arr

(*******************************)
(* Part 2: Subset Construction *)
(*******************************)

(* form a list of state lists, each a set of states we could be moving from initial states on each
   symbol from alphabet. then loop through that list, and return a list of the e-closures of the
   entries in that list *)
let new_states (nfa : ('q, 's) nfa_t) (qs : 'q list) : 'q list list =
  (* nfa.sigma is type 's list but move expects 's option, so convert to list of option types and
     put it into sigma *)
  let sigma = map (fun y -> Some y) nfa.sigma in
  map
    (fun x -> e_closure nfa x)
    (fold_left (fun acc s -> move nfa qs s :: acc) [] sigma)

(* find a way to connect new_states to qs on transitions *)
(* for each symbol s, let state = e_closure nfa (move nfa qs Some s). add (qs, s, state)
   to list *)
let new_trans (nfa : ('q, 's) nfa_t) (qs : 'q list) :
    ('q list, 's) transition list =
  fold_left
    (fun acc s ->
      let state = e_closure nfa (move nfa qs s) in
      (qs, s, state) :: acc)
    []
    (map (fun y -> Some y) nfa.sigma)

let new_finals (nfa : ('q, 's) nfa_t) (qs : 'q list) : 'q list list =
  if length (intersection qs nfa.fs) > 0 then [ qs ] else []

(* take the first element of work list and find the new states. make the new transitions and add
   them to dfa.delta. then add all new_states that arent already in dfa.qs. add any new finals
   to dfa.fs *)

let rec nfa_to_dfa_step (nfa : ('q, 's) nfa_t) (dfa : ('q list, 's) nfa_t)
    (work : 'q list list) (visited : 'q list list): ('q list, 's) nfa_t =
  if visited = dfa.qs then dfa
  else
    match work with 
    |h::t -> 
      if elem h visited then nfa_to_dfa_step nfa dfa t visited
      else
      let new_states = new_states nfa h in
      let new_transitions = new_trans nfa h in
      let new_finals = new_finals nfa h in
      let new_dfa ={
        sigma = dfa.sigma;
        qs = union dfa.qs new_states;
        q0 = dfa.q0;
        fs = union dfa.fs new_finals;
        delta = union dfa.delta new_transitions;
      } in
      nfa_to_dfa_step nfa new_dfa (union (diff new_states visited) t) (insert h visited)
    |[] -> dfa

let nfa_to_dfa (nfa : ('q, 's) nfa_t) : ('q list, 's) nfa_t =
  let init_state = e_closure nfa [nfa.q0] in
  let dfa =
    {
      sigma = nfa.sigma;
      qs = [init_state];
      q0 = init_state;
      fs = [];
      delta = [];
    }
  in
  nfa_to_dfa_step nfa dfa [init_state] []