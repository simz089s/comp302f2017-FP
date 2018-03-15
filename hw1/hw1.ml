(* Student information:

   Enter your name, and if you chose to work in pairs, the name of the
   student you worked with (both students MUST submit the solution to
   myCourses):

   Name: Simon Zheng
   McGill ID: 260744353

   If you worked in pairs, the name of the other student.

   Name: Jacob Sanz-Robinson
   McGill ID: 260706158


 *)

(* Notice: by submitting as part of team, you declare that you worked
   together on the solution. Submissions in pairs are allowed to
   foster team work, they have to be developed by both students *)

(* Homework 1 - Questions 2 and 3 *)

(* First, some utility functions and declarations that you can use. Be
   sure to check Ocaml's documentation to find more functions
   available to you.

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
(* Uses triangle inequality theorem *)
let well_formed_by_sides (a, b, c : tr_by_sides) : bool =
  let f (a, b, c : tr_by_sides) : bool =
    a < b +. c && b < c +. a && c < a +. b
  in
  if (positive a) && (positive b) && (positive c) then
    f (a, b, c)
  else false


(* Question 2.2 *)
let create_triangle (kind : tr_kind) (area : float) : tr_by_sides =
  match kind with
  | Scalene ->
    (* Method 1 :
       let b = 1.0 in
       let cAngle = 1.0 in
       let a = 2.0 *. area /. (sin (pi /. 3.0)) in
       let c = sqrt ((a ** 2.0) +. (b ** 2.0) -. (2.0 *. a *. b *. (cos cAngle))) in
     * Method 2 : *)
    let angle = pi /. 3.0 in
    let h = area *. (sin angle) in
    let b = 2.0 *. area /. h in
    let c = sqrt (
        (area ** 2.0) +. (b ** 2.0) -. (2.0 *. area *. b *. (cos angle))
      ) in
    (area, b, c)
  | Equilateral ->
    let a = sqrt (sqrt ((4.0 *. (area ** 2.0)) /. 0.75)) in
    let b = a in
    let c = a in
    (a, b, c)
  | Isosceles ->
    (* Method 1 : set base and solve for leg
       let base = 0.2 in
       let leg = ((area ** 2.0) |> ( *. ) 16.0 |> ( +. ) (base ** 4.0)) /. 4.0 /.
              (base ** 2.0) |> sqrt in
     * Method 2 : set angle and solve for all sides *)
    let angle = 0.8 in
    let leg = (sqrt area) *. (sqrt (1.0 /. (sin angle))) *.
              (sqrt (1.0 /. cos angle)) in
    let base = 2.0 *. leg *. (cos angle) in
    (leg, base, leg)

(* Question 2.3 *)
type angle = float

type tr_by_angle = side * side * angle

let well_formed_by_angle (a, b, gamma : tr_by_angle) : bool =
  (positive a && positive b && positive gamma) &&
    (not (is_multiple_of gamma pi))

(* Uses convert function if triangle is valid, else None *)
let sides_to_angle (a, b, c : tr_by_sides) : tr_by_angle option =
  let convert (a, b, c) =
    let angle = acos ( ((c *. c) -. (a *. a) -. (b *. b)) /. (-2.0 *. a *. b ) ) in
    Some (a, b, angle)
  in
  if well_formed_by_sides (a, b, c) then
    convert (a, b, c)
  else None

(* Same as previous *)
let angle_to_sides (a, b, gamma : tr_by_angle) : tr_by_sides option =
  let convert (a, b, gamma) =
    let c = sqrt ((a *. a) +. (b *. b) -. (2.0 *. a *. b *. cos gamma)) in
    Some (a, b, c)
  in
  if well_formed_by_angle (a, b, gamma) then
    convert (a, b, gamma)
  else None

(* Now that you implemented Q2.2 and saw the new representation of
   triangles by two sides and the angle between them, also ponder on
   how one represents Q2.2 using this representation. The idea is to
   think about how the representation helps make illegal states hard
   to represent and how easy and hard it is to implement the
   algorithm. *)

(* Question 3: Flexing recursion and lists *)

let even (n : int) : bool =  n mod 2 = 0

(* Question 3.1 *)
(* Go through list and distribute even and odd numbers to respective lists
 * before concatenating them at the end. *)
let evens_first (l : int list) : int list =
  let rec f (evens : int list) (odds : int list) (li : int list) = match li with
    | [] -> (List.rev evens) @ (List.rev odds)
    | head :: tail ->
      if even head then
        f (head :: evens) odds tail
      else
        f evens (head :: odds) tail
  in
  f [] [] l
(* One-liner version (not tail-recursive) :
   match List.partition even l with (li1, li2) -> List.concat [li1; li2] *)

let ex_1 = evens_first [7 ; 5 ; 2; 4; 6; 3; 4; 2; 1]
(* val ex_1 : int list = [2; 4; 6; 4; 2; 7; 5; 3; 1] *)

(* Question 3.2 *)
(* Go through list counting even streaks and stores and updates longest *)
let even_streak (l : int list) : int =
  let rec f (longest : int) (current : int) (li : int list) = match li with
    | [] -> max longest current
    | head :: tail ->
      if even head then f longest (current + 1) tail
      else
        if longest < current then f current 0 tail
        else f longest 0 tail
  in
  f 0 0 l

let ex_2 = even_streak [7; 2; 4; 6; 3; 4; 2; 1]

(* val ex_2 : int = 3 *)


(* Question 3.3 *)

type nucleobase = A | G | C | T

(* Go through list and create a tuple for each streak that is incremented
 * until the streak is done, in which case the tuple is prepended to the
 * accumulator list. Reverses it at the end to get the right order. *)
let compress (l : nucleobase list) : (int * nucleobase) list =
  let rec f (acc : (int * nucleobase) list) (li : nucleobase list) =
    match li with
    | [] -> acc
    | head :: tail -> match acc with
      | [] -> [(0, head)]
      | (x, n) :: acc_tl ->
        if head = n then f ((x + 1, n) :: acc_tl) tail
        else f ((1, head) :: (x, n) :: acc_tl) tail
  in
  match l with
  | [] -> []
  | hd :: tl -> List.rev (f [(0, hd)] l)

(* Go through each tuple by calling the untuple function which expands the
 * tuple into a list and append this list to the accumulator. *)
let rec decompress (l : (int * nucleobase) list) : nucleobase list =
  let rec untuple acc = function
    | (0, n) -> acc
    | (x, n) -> untuple (n :: acc) (x - 1, n)
  in
  let rec expand acc = function
    | [] -> acc
    | head :: tail -> expand (acc @ untuple [] head) tail
  in
  expand [] l

let sample_dna : nucleobase list = [A;A;A;A;G;G;A;T;T;T;C;T;C]

let ex_3 = compress sample_dna

let ex_4 = decompress ex_3

let res_3_4 = sample_dna = ex_4 (* This should be true if everything went well *)
