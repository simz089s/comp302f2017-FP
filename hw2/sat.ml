(* Elvric Trombert ID: 260673394
 * Simon Zheng ID: 260744353 *)
 
(* The data-type for Propositional logic *)

type prop = Atom of string
          | Not of prop
          | And of prop * prop
          | Or of prop * prop

(* Two synthetic connectives *)

let impl (p, q) = Or(Not p, q)
let iff (p, q) = And (impl (p,q), impl (q, p))


let rec to_nnf = function
  | Atom a -> Atom a
  | Not (Atom a) -> Not (Atom a)
  | Not (Not p) -> p
  | Not (And (p, q)) -> to_nnf (Or (Not p, Not q))
  | Not (Or (p, q)) -> to_nnf (And (Not p, Not q))
  | And (p, q) -> And (to_nnf p, to_nnf q)
  | Or (p, q) -> Or (to_nnf p, to_nnf q)


(* let mp_nnf = to_nnf mp *)

(* let ra_nnf = to_nnf ra *)

let rec distribute : prop * prop -> prop = function
  | p, And (q, r) -> And(distribute (p, q), distribute (p, r))
  | And(q, r), p ->  And(distribute (q, p), distribute (r, p))
  | p, q -> Or (p, q)

let rec nnf_to_cnf: prop -> prop = function
  | And(p, q) -> And (nnf_to_cnf p, nnf_to_cnf q)
  | Or(p, q) -> distribute (nnf_to_cnf p, nnf_to_cnf q)
  | Atom a -> Atom a
  | Not p -> Not p

let cnf p = nnf_to_cnf (to_nnf p)

(* Modus ponens: (P ∧ (P ⇒ Q)) ⇒ Q *)
let mp = impl (And (Atom "P",
                    impl (Atom "P", Atom "Q"))
              , Atom "Q")

(* And it can be put in CNF form using this expression: *)
let mp_in_cnf = cnf mp

(* Proof by contradiction (reduction ad absurdum): ((¬ P) ⇒ Q) ∧ ((¬ P) ⇒ (¬ Q)) ⇒ P *)
let ra = impl (
             And (impl (Not (Atom "P"),
                        Atom "Q"),
                  impl (Not (Atom "P"),
                        Not (Atom "Q"))),
             Atom "P")
let ra_in_cnf = cnf ra


let rec positives = function
  | Atom a -> [a]
  | Not (Atom _) -> []
  | Or (p, q) -> positives p @ positives q
  | _ -> raise (Invalid_argument "Not in NNF form")

let rec negatives = function
  | Atom _ -> []
  | Not (Atom a) -> [a]
  | Or (p, q) -> negatives p @ negatives q
  | _ -> raise (Invalid_argument "Not in NNF form")


(* Q1.1: Implement a function: intersection : 'a list -> 'a list -> 'a
   list

  The returns the intersection of the elements of both lists. That is,
   those elements that are present in both lists at the same time. *)
let rec intersection (l1 : 'a list) (l2 : 'a list) : 'a list =
  let rec find (x : 'a) (li : 'a list) : bool = match li with
    | [] -> false
    | hd :: tl -> if x = hd then true else find x tl
  in
  let rec intersection' (l1 : 'a list) (l2 : 'a list) acc = match l1 with
    | [] -> acc
    | hd :: tl ->
      if find hd l2 && not (find hd acc) then intersection' tl l2 (hd :: acc)
      else intersection' tl l2 acc
  in
  if l2 = [] then []
  else intersection' l1 l2 []


let rec cnf_tautology = function
  | And (p, q) -> cnf_tautology p && cnf_tautology q
  | p -> not ([] = intersection (positives p) (negatives p))


let mp_taut = mp |> cnf |> cnf_tautology

let ra_taut = ra |> cnf |> cnf_tautology

let taut p = cnf_tautology (cnf p)
let unsat p = taut (Not p)
let sat p = not (unsat p)


(* Some examples *)

let nc = Not (And (Atom "P", Not (Atom "P")))
let nc_taut = taut nc
