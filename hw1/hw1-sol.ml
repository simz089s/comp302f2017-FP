(* First, some utility functions that you can use. Be sure to check
   Ocaml's documentation to find more functions available to you.

   You can start checking the documentation at:
   https://caml.inria.fr/pub/docs/manual-ocaml/libref/Pervasives.html
   *)

(* the value of pi *)
let pi : float =  acos ~-.1.0

(* a function to compare floats that allows for some imprecision *)
let cmp n m = abs_float (n -. m) < 0.0001

(* a simple test of positivity *)
let positive a = a > 0.0

(* a function to check if a is multiple of b *)
let is_multiple_of (a : float) (b : float) : bool =
  let m = a /. b in
  cmp (m -. floor m) 0.0

(* a function to check if a is between plus/minus b *)
let abs_btwn a b = a < b && a > ~-.b

(* Question 2: Triangles are the best *)

type side = float

type tr_by_sides = side * side * side

type tr_kind
  = Scalene
  | Equilateral
  | Isosceles

(* Question 2.1 *)
let well_formed_by_sides (a, b, c : tr_by_sides) : bool =
  positive a && positive b && positive c &&
    abs_btwn (((a *. a +. b *. b) -. (c *. c))/.(2.0*.a*.b)) 1.0

(* Question 2.2 *)
let create_triangle (kind : tr_kind) (area : float) : tr_by_sides =
  let equilateral (area : float) : tr_by_sides  =
    (* equilateral triangles have a constant rate between base and height *)
    let side = sqrt(area *. 4.0 /.(sqrt 3.0)) in
    (side, side, side)
  in

  let isoceles (area : float) : tr_by_sides =
    (* A possible solution is the isoceles right triangle of this area *)
    let base = sqrt(2.0 *. area) in
    let side = sqrt(2.0 *. base *. base) in
    (base, base, side)
  in

  let scalene (area : float) : tr_by_sides =
    (* A possible solution is the ritgt triangle where short leg is twice the long leg *)
    let base = sqrt area in
    let height = 2.0 *. base in
    let hyp = hypot base height in
  (base, height, hyp)
  in
  match kind with
  | Scalene -> scalene area
  | Equilateral -> equilateral area
  | Isosceles -> isoceles area

(* Extra marks, how would you improve the representation so it is easy only valid triangles are represented *)

type angle = float

type tr_by_angle = side * side * angle

let well_formed_by_angle (a, b, gamma) : bool =
  (positive a && positive b && positive gamma) &&
    (not (is_multiple_of gamma pi))

(* Question 2.3 *)
let sides_to_angle (a, b, c : tr_by_sides) : tr_by_angle option =
  if well_formed_by_sides (a, b, c) then
    let gamma = acos (((a *. a +. b *. b) -. (c *. c))/.(2.0*.a*.b))  in
    Some (a, b, gamma)
  else
    None

let angle_to_sides (a, b, gamma) =
if well_formed_by_angle (a, b, gamma) then
  Some (a, b, sqrt(a *. a +. b *. b -. 2.0 *. a *. b *. cos gamma))
else
  None


(* Now that you implemented Q2.2 and saw the new representation of
   triangles by two sides and the angle between them, also ponder on
   how one represent Q2.2 using this representation. The idea is to
   think about how the representation helps make illegal states hard
   to represent and how easy and hard it is to implement the
   algorithm. *)

(* Question 3: Flexing recursion and lists *)

let even (n : int) : bool = n mod 2 = 0

(* Question 3.1 *)
let evens_first (l : int list) : int list =
  let rec evens_first = function
    | [] -> [], []
    | x::xs ->
       let evens, odds = evens_first xs in
       if even x then
         x::evens, odds
       else
         evens, x::odds
  in
  let evens, odds = evens_first l in
  evens @ odds

let ex_1 = evens_first [7 ; 5 ; 2; 4; 6; 3; 4; 2; 1]
(* val ex_1 : int list = [2; 4; 6; 4; 2; 7; 5; 3; 1] *)

(* Question 3.2 *)
let even_streak (l : int list) : int =
  let rec even_streak l n max =
    let max' = if n > max then n else max in
    match l with
    | [] -> max'
    | x::xs when even x -> even_streak xs (n+1) max'
    | x::xs -> even_streak xs 0 max'
  in
  even_streak l 0 0

let even_streak (l : int list) : int =
  let rec even_streak l n max =
    let max' = if n > max then n else max in
    match l with
    | [] -> max'
    | x::xs -> if even x then even_streak xs (n+1) max' else even_streak xs 0 max'
  in
  even_streak l 0 0

let ex_2 = even_streak [7; 2; 4; 6; 3; 4; 2; 1]

(* val ex_2 : int = 3 *)


(* Question 3.3 *)

type nucleobase = A | G | C | T

let compress (l : nucleobase list) : (int * nucleobase) list =
  let rec get_head h n = function
    | [] -> (n, h) , []
    | x:: xs when x = h -> get_head h (n+1) xs
    | xs -> (n, h), xs
 in
 let rec compress = function
   | [] -> []
   | x::xs ->
      let x', xs' = get_head x 1 xs in
      x' :: compress xs'
 in
 compress l

let rec decompress (l : (int * nucleobase) list) : nucleobase list =
  let rec repeat h = function
    | 0 -> []
    | n -> h::repeat h (n - 1)
  in
  match l with
  | [] -> []
  | (n, h)::xs -> repeat h n @ decompress xs


let sample_dna : nucleobase list = [A;A;A;A;G;G;A;T;T;T;C;T;C]

let ex_3 = compress sample_dna

let ex_4 = decompress ex_3

let res_3_4 = sample_dna = ex_4
