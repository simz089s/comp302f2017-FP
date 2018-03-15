(* Elvric Trombert ID: 260673394
 * Simon Zheng ID: 260744353 *)
type prop = Atom of string
          | Not of prop
          | And of prop * prop
          | Or of prop * prop

let impl (p, q) = Or(Not p, q)
let iff (p, q) = And (impl (p,q), impl (q, p))

let mp = impl (And (Atom "P", impl (Atom "P", Atom "Q")), Atom "Q")

(* Proof by contradiction (reduction ad absurdum): ((¬ P) ⇒ Q) ∧ ((¬ P) ⇒ (¬ Q)) ⇒ P *)
let ra = impl (
           And (impl (Not (Atom "P"),
                      Atom "Q"),
                impl (Not (Atom "P"),
                      Not (Atom "Q"))),
           Atom "P")

(* Atoms and their negations *)
type signed_atom = PosAtom of string
                 | NegAtom of string

(* In NNF negations can only be applied to atoms, this datatype only
   allows for propositions in NNF *)
type nnf = AndN of nnf * nnf
         | OrN of nnf * nnf
         | AtomN of signed_atom

(* Q1.2: Write the function nnf that converts propositions into NNF,
   notice that the typechecker will guide you in your answer as the
   type forces the result to be in NNF. Your job is to not forget any
   sub-parts of the proposition in the conversion. *)
let rec to_nnf : prop -> nnf = function
  | Atom a -> AtomN (PosAtom a)
  | Not (Atom a) -> AtomN (NegAtom a)
  | Not (Not p) -> to_nnf p
  | Not (And (p, q)) -> to_nnf (Or (Not p, Not q))
  | Not (Or (p, q)) -> to_nnf (And (Not p, Not q))
  | And (p, q) -> AndN (to_nnf p, to_nnf q)
  | Or (p, q) -> OrN (to_nnf p, to_nnf q)


(* Q1.3: Write a datatype cnf that represents only propositions in
   cnf. Hint: You might want to use more than one type to be able to
   represent sub-expressions.*)
(* We created two types. Since disjunction of conjunctions are not possible in cnf, by making a disjunction subtype, 
we guarantee that it cannot happen. *)
type djn = OrD of djn * djn
         | AtomD of signed_atom

type cnf = AndC of cnf * cnf
         | DjnC of djn
      (* | AtomC of djn *)

(* Q1.4: Write the distribute and nnf_to_cnf functions using the new
   datatype. Hint: you may need more than one helper function. *)
let rec distribute : cnf * cnf -> cnf = function
  | p, AndC (q, r) -> AndC (distribute (p, q), distribute (p, r))
  | AndC (q, r), p ->  AndC (distribute (q, p), distribute (r, p))
  | DjnC p, DjnC q -> DjnC (OrD (p, q))

let rec nnf_to_cnf : nnf -> cnf = function
  | AndN (p, q) -> AndC (nnf_to_cnf p, nnf_to_cnf q)
  | OrN (p, q) -> distribute (nnf_to_cnf p, nnf_to_cnf q)
  | AtomN a -> DjnC (AtomD a)

let to_cnf (p :prop) : cnf = nnf_to_cnf (to_nnf p)

(* Q1.5: Write the new positives and negative atoms function as in the
   previous version *)

(* We left the exceptions there for testing purposes and to get an exhaustive pattern match,
but they should not happen with our new cnf type. *)
let rec positives = function
  | DjnC (AtomD (PosAtom a)) -> [a]
  | DjnC (AtomD (NegAtom _)) -> []
  | DjnC (OrD (p, q)) -> positives (DjnC p) @ positives (DjnC q)
  | _ -> raise (Invalid_argument "Not in CNF form")

let rec negatives = function
  | DjnC (AtomD (PosAtom _)) -> []
  | DjnC (AtomD (NegAtom a)) -> [a]
  | DjnC (OrD (p, q)) -> negatives (DjnC p) @ negatives (DjnC q)
  | _ -> raise (Invalid_argument "Not in CNF form")

(* Fill in the code for the intersection function from Q1.1 *)
let rec intersection l1 l2 =
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

(* Q1.6: Write the new cnf_tautology function *)
let rec cnf_tautology : cnf -> bool = function
  | AndC (p, q) -> cnf_tautology p && cnf_tautology q
  | p -> not ([] = intersection (positives p) (negatives p))

let taut (p : prop) : bool = cnf_tautology (to_cnf p)
let unsat (p : prop) : bool = taut (Not p)
let sat (p : prop) : bool = not (unsat p)
