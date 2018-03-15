(*
 * Simon Zheng         260744353
 * Jacob Sanz-Robinson 260706158
 *)

(* Q1: A Rose by any Other Name Would Smell as Sweet *)

type 'a rose_tree = Node of 'a * ('a rose_tree) list

(* TEST *)
let rt = Node(1,[Node(2,[Node(3,[]);Node(4,[Node(5,[]);Node(6,[])])])])
let test_find f tree = List.iter (fun x -> match f ((=)x) tree with
                                        None -> Printf.printf "%d:None " x
                                      | Some n -> Printf.printf "%d:%d " x n
                            ) [-1;0;1;2;3;4;5;6;7;8]
let test_find_all f fn tree = List.iter (fun x -> print_int x) (f fn tree)
(* TEST *)

(* Find with exceptions *)

exception BackTrack

(* Q1.1 write a function that finds an element of the tree using backtracking with exceptions *)

let rec find_e (p : 'a -> bool) (t : 'a rose_tree) : 'a = (* Function with exceptions *)
  let rec rose_tree_iter = function
    | [] -> raise BackTrack
    | t' :: ts' -> try find_e p t' with BackTrack -> rose_tree_iter ts'
  in
  match t with
    | Node (v, ts) ->
      if p v then v
      else rose_tree_iter ts

(* Q1.1: write this function and it helper functions *)
let find (p : 'a -> bool)  (t : 'a rose_tree) : 'a option =
  (* call find_e and handle the exceptions *)
  try Some (find_e p t)
  with BackTrack -> None

(* Find with failure continuations *)

let rec find_k (p : 'a -> bool) (t : 'a rose_tree) (k : unit -> 'a option) : 'a option =
  let rec rose_tree_iter = function
    | [] -> k ()
    | t' :: ts' -> find_k p t' (fun () -> rose_tree_iter ts')
  in
  match t with
    | Node (v, ts) ->
      if p v then Some v
      else rose_tree_iter ts

(* Q1.2: write this function and it helper functions *)
let find' (p : 'a -> bool)  (t : 'a rose_tree) : 'a option = (*  call find_k with the appropriate inital continuation *)
  find_k p t (fun () -> None)

(* Find all with continuations *)

let rec find_all_k  (p : 'a -> bool) (t : 'a rose_tree) (k : 'a list -> 'b) : 'b =
  let rec rose_tree_iter = function
    | [] -> k []
    | t' :: ts' -> find_all_k p t' (fun l -> l @ rose_tree_iter ts')
  in
  match t with
    | Node (v, ts) ->
      if p v then v :: rose_tree_iter ts
      else rose_tree_iter ts

(* Q1.3: write this function and it helper functions *)
let find_all p t = find_all_k p t (fun l -> l)

(* An example to use *)

let example = Node (7, [ Node (1, [])
                         ; Node (2, [Node (16, [])])
                         ; Node (4, [])
                         ; Node (9, [])
                         ; Node (11, [])
                         ; Node (15, [])
                         ])

let is_big x =  x > 10


(* Q2 : Rational Numbers Two Ways *)

type fraction = int * int

module type Arith =
  sig
    type t
    val epsilon : t             (* A suitable tiny value, like epsilon_float for floats *)

    val plus : t -> t -> t      (* Addition *)
    val minus : t -> t -> t     (* Substraction *)
    val prod : t -> t -> t      (* Multiplication *)
    val div : t -> t -> t       (* Division *)
    val abs : t -> t            (* Absolute value *)
    val lt : t -> t -> bool     (* < *)
    val le : t -> t -> bool     (* <= *)
    val gt : t -> t -> bool     (* > *)
    val ge : t -> t -> bool     (* >= *)
    val eq : t -> t -> bool     (* = *)
    val from_fraction : fraction -> t (* conversion from a fraction type *)
    val to_string : t -> string        (* generate a string *)
  end

module FloatArith : Arith =
struct
  type t = float
  let epsilon = epsilon_float
  let from_fraction (num, den) = float_of_int num /. float_of_int den

  let plus = (+.)
  let minus = (-.)
  let prod = ( *. )
  let div = ( /. )
  let abs = abs_float
  let lt = (<)
  let le = (<=)
  let gt = (>)
  let ge = (>=)
  let eq = (=)
  let to_string x = string_of_float x
end

(* Q2.1: Implement the Arith module using rational numbers (t = fraction) *)

module FractionArith : Arith =
  struct
    type t = fraction
    let epsilon = (1, 1000000)
    
    let simplify (num, den) =
      let rec gcd m n =
        if n = 0 then m
        else gcd n (m mod n)
      in
      let gcd_val = gcd num den in
      (num / gcd_val, den / gcd_val)

    let plus (a,b) (x,y) = simplify ((a*y)+(x*b), (b*y))
    let minus (a,b) (x,y) = simplify ((a*y)-(x*b), (b*y))
    let prod (a,b) (x,y) = simplify (a*x, b*y)
    let div (a,b) (x,y) = simplify (a*y, b*x)
    let abs (a,b) = (abs a, abs b)
    let lt (a,b) (x,y) = (a*y) < (x*b)
    let le (a,b) (x,y) = (a*y) <= (x*b)
    let gt (a,b) (x,y) = (a*y) > (x*b)
    let ge (a,b) (x,y) = (a*y) >= (x*b)
    let eq (a,b) (x,y) = (a*y) = (x*b)
    let from_fraction (num, den) = simplify (num, den)
    let to_string (a,b) = String.concat " / " [string_of_int a; string_of_int b]
  end

(* TEST *)
let f_pl = FractionArith.plus
let f_mn = FractionArith.minus
let f_pr = FractionArith.prod
let f_dv = FractionArith.div
let f_abs = FractionArith.abs
let frac = FractionArith.from_fraction
let f_s = FractionArith.to_string

let f1 = FractionArith.from_fraction (1,2) (* 3 / 6 *)
let f2 = FractionArith.from_fraction (2,3) (* 4 / 6 *)
(* TEST *)

module type NewtonSolver =
  sig
    type t

    val square_root : t -> t
  end

(* Q2.2: Implement a function that approximates the square root using  the Newton-Raphson method *)

module Newton (A : Arith) : (NewtonSolver with type t = A.t) =
  struct
    type t = A.t

    let rec square_root a =
      let integer n = A.from_fraction (n,1) in
      let rec findroot x acc =
        let x' = A.div (A.plus (A.div a x) x) (integer 2) in
        let d = A.abs (A.minus x x') in
        if A.lt d acc then A.abs x' else findroot x' acc
      in
      findroot (integer 1) A.epsilon
  end

(* Examples *)

module FloatNewton = Newton (FloatArith)
module RationalNewton = Newton (FractionArith)

let sqrt2 = FloatNewton.square_root (FloatArith.from_fraction (2, 1))
let sqrt2_r = RationalNewton.square_root (FractionArith.from_fraction (2, 1))

(* Q3 : Real Real Numbers, for Real! *)

type 'a stream = { head : 'a  ; tail : unit -> 'a stream}

let rec nth z = function
  | 0 -> z.head
  | n -> nth (z.tail()) (n - 1)

let rec constant x = {head = x ; tail = fun () -> constant x }

(* Some examples *)

let sqrt2 =
  {head = 1 ; tail = fun () -> constant 2} (* 1,2,2,2,2... *)

let golden_ratio = constant 1   (* 1,1,1,1,1,1 *)

let rec take n z =
  if n = 1 then [z.head]
  else z.head::(take (n-1) (z.tail()))

(* TEST *)
let nats =
  let rec nats n = {head = n ; tail = fun () -> nats (n + 1)} in
  nats 0 (* This one includes 0. *)

let rec stream_of_list = function
  | [] -> constant 0
  | h::t -> {head = h ; tail = fun () -> stream_of_list t}

let picofr = stream_of_list [3; 7; 15; 1; 292; 1; 1; 1; 2; 1; 3; 1; 14; 2; 1; 1; 2; 2; 2; 2; 1; 84; 2; 1; 1; 15; 3; 13; 1; 4; 2; 6; 6; 99; 1; 2; 2; 6; 3; 5; 1; 1; 6; 8; 1; 7; 1; 2; 3; 7; 1; 2; 1; 1; 12; 1; 1; 1; 3; 1; 1; 8; 1; 1; 2; 1; 6; 1; 1; 5; 2; 2; 3; 1; 2; 4; 4; 16; 1; 161; 45; 1; 22; 1; 2; 2; 1; 4; 1; 2; 24; 1; 2; 1; 3; 1; 2; 1]

let ecofr = stream_of_list [2; 1; 2; 1; 1; 4; 1; 1; 6; 1; 1; 8; 1; 1; 10; 1; 1; 12; 1; 1; 14; 1; 1; 16; 1; 1; 18; 1; 1; 20; 1; 1; 22; 1; 1; 24; 1; 1; 26; 1; 1; 28; 1; 1; 30; 1; 1; 32; 1; 1; 34; 1; 1; 36; 1; 1; 38; 1; 1; 40; 1; 1; 42; 1; 1; 44; 1; 1; 46; 1; 1; 48; 1; 1; 50; 1; 1; 52; 1; 1; 54; 1; 1; 56; 1; 1; 58; 1; 1; 60; 1; 1; 62; 1; 1; 64; 1; 1; 66]
(* TEST *)

(* Q3.1: implement the function q as explained in the pdf *)
let rec q z n = assert (n >= 0);
  let rec q' z a b = function
    | 0 -> b
    | n -> q' (z.tail()) (z.head * a + b) a (n - 1)
  in
  q' ((z.tail()).tail()) (z.tail()).head 1 n

(* Q3.2: implement the function r as in the notes *)
let rec r z n = assert (n >= 0);
  let rec r' acc sgn qn = function
    | k when k = n -> acc
    | k ->
      let qn' = q z (k + 1) in
      if qn' = 0 then acc else
      let acc' = float_of_int sgn /. float_of_int (qn * qn') in
      r' (acc +. acc') (0 - sgn) qn' (k + 1)
  in
  r' (float_of_int z.head) 1 1 0 (* acc=x0, sgn=-1^(1-1), qn=q0, z=stream, k=0..n *)

(* Q3.3: implement the error function *)
let error z n = assert (n > 0);
  let qn = q z n in
  if qn = 0 then 0. else
  1. /. float_of_int (qn * (qn + q z (n - 1)))

(* Q3.4: implement a function that computes a rational approximation of a real number *)
let rat_of_real z approx = assert (approx > 0.);
  let rec rat_of_real prev_err n =
    let err = error z n in
    if err < approx || err = 0. then r z n
    else if err > prev_err then r z (n + 1)
    else rat_of_real err (n + 1)
  in
  rat_of_real infinity 1

let real_of_int n = { head = n ; tail = fun () -> constant 0}

(* Q3.5: implement a function that computes the real representation of a rational number   *)
let rec real_of_rat r =
  let int_part_head = int_of_float @@ floor r in
  let diff = r -. float_of_int int_part_head in
  if diff = 0. || diff < epsilon_float then
    {head = int_part_head ; tail = fun () -> constant 0}
  else let reciprocal = 1. /. diff in
    {head = int_part_head ; tail = fun () -> real_of_rat reciprocal}


(* Examples *)

(* Approximations of the  irrational numbers we have *)

let sqrt_2_rat = rat_of_real sqrt2 1.e-5
let golden_ratio_rat = rat_of_real golden_ratio 1.e-5

(* To test the representation of rationals we can try this *)
let to_real_and_back n = rat_of_real (real_of_rat n) 0.0001

(* e1 should be very close to 10 (it is exactly 10 in the model solution) *)
let e1 = to_real_and_back 10.0

(* this is the float approximation of pi, not the real number pi *)
let not_pi = 2. *. acos 0.

(* This should share the same 4 decimals with not_pi *)
let not_pi' = to_real_and_back not_pi
