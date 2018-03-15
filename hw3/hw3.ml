(* Students :
 * Simon Zheng     260744353
 * Elvric Trombert 260673394
 *)

(* Question 1 - Unfolding *)

(* This is the function unfold, take some time to compare it it fold.
   If fold_left and fold_right take lists to generate a value, this
   function takes a value that will generate a list. The relation
   between folds and unfolds is the beginning of a wonderful tale in
   computer science. But let's not get ahead of ourselves.

   Unfold takes a function that from a seed value it generates a new
   element of the list, and the seed for the next element, and another
   function to stop the generation, and an initial seed.
*)

let rec unfold (f: 'seed -> ('a * 'seed)) (stop : 'b -> bool) (b : 'seed) : 'a list =
  if stop b then []
  else let x, b' = f b in
      x :: (unfold f stop b')

let nats max = unfold (fun b -> b, b + 1) (fun x -> x > max) 0

(* Q1.1: Return the even numbers up-to max *)
let evens (max : int): int list = unfold (fun n -> n, n + 2) (( < ) max) 0

(* Q1.2: Return the Fibonacci sequence up-to max *)
let fib (max : int): int list = unfold (fun (a,b) -> (a , (b,a+b))) (fun (a,_) -> a > max) (1,1)

(* Q1.3: Return the list of rows of the Pascal triangle that are shorter than max *)
let pascal (max : int): int list list =
  let rec get_row_from_prev r =
    1 :: unfold (function [] -> raise (Failure "This should not happen")
                        | h :: [] -> h, []
                        | h1 :: h2 :: t -> h1 + h2, h2 :: t
                ) (function l -> l = []) r
  in
  unfold (fun r -> (r, get_row_from_prev r)) (fun row -> List.length row >= max) [1]

let rec zip (l1 : 'a list) (l2 : 'b list) :  ('a * 'b) list =
  match l1, l2 with
    | [], _ -> []
    | _, [] -> []
    | x::xs, y::ys -> (x, y):: zip xs ys

(* (Extra credit) Optional: implement zip with a single call to unfold *)
let zip' l1 l2 =
  unfold (function _,[] | [],_ -> raise @@ Failure "This should not happen"
                 | (x::xs,y::ys) -> (x,y), (xs,ys)
         ) (fun (l1,l2) -> l1 = [] || l2 = []) (l1,l2)
(* Technically the empty list match cases would never happen because of
 * the stop predicate function, but the compiler does not check that far *)

(* Question 2 *)

let ugly x =
  let rec ackermann m n = match (m , n) with
    | 0 , n -> n+1
    | m , 0 -> ackermann (m-1) 1
    | m , n -> ackermann (m-1) (ackermann m (n-1))
  in
  ackermann 3 x

let memo_zero (f : 'a -> 'b) : 'a -> 'b = f

(* Q2.1: Write a function that memoizes the last value called. *)
let memo_one (f : 'a -> 'b) : ('a -> 'b) =
  let cache = ref None in
  (fun x ->
    match !cache with
      | Some (x', y) when x' = x -> y
      | _ -> let y = f x in cache := Some (x, y); y
  )

(* Example usage:

  let ugly' = memo_one ugly

  let u1 = ugly' 3                (* this one calls ugly with 3 *)
  let u2 = ugly' 3                (* this one uses the stored value *)
  let u3 = ugly' 1                (* the stored value is for 3 so it calls ugly *)
  let u4 = ugly' 2                (* the stored value is for 1 so it calls ugly *)
  let u5 = ugly' 10               (* the stored value is for 2 so it calls ugly and takes a couple of seconds *)
  let u6 = ugly' 10               (* the one uses the stored value and returns immediately *)

*)

(* Q2.2: Write a function that memoizes the last value called. *)
(* Using fixed list cache and filling up to n without updating after *)
let memo_many (n : int) (f : 'a -> 'b) : 'a -> 'b =
  let cache = ref [] in
  (fun x ->
    try
      List.assoc x !cache (* Can also use assoc_opt for options instead *)
    with Not_found ->
      if List.length !cache < n then
        let y = f x in
        (cache := !cache @ [(x, y)]; y)
      else
        match !cache with
          | [] -> raise (Failure "This should not happen")
          | h :: t -> let y = f x in (cache := t @ [(x, y)]; y)
  )

(* Using a hash table (Hashtbl grows so does not stop at n elements) *)
let memo_many (n : int) (f : 'a -> 'b) : 'a -> 'b =
  let cache = Hashtbl.create n in
  (fun x ->
    try
      Hashtbl.find cache x
    with Not_found ->
      let y = f x in
      Hashtbl.add cache x y;
      y
  )

(* Using an array as a FIFO buffer *)
let memo_many (n : int) (f : 'a -> 'b) : 'a -> 'b =
  (* Personal lookup function just in case, but fold technique below is used *)
  (* let lookup k arr =
    let n = Array.length arr in
    let rec lookup' k arr = function
      | i when i = n -> None
      | i ->
        match arr.(i) with
          | Some (k',v) when k' = k -> Some v
          | _ -> lookup' k arr (i + 1)
    in
    lookup' k arr 0
  in *)
  let cache = Array.make n None in
  let avail_ptr = ref 0 in (* Index of next available cache space (oldest is overwritten) *)
  (fun x ->
    (* Accumulator y becomes value if key found, else stays None *)
    let y = Array.fold_left ( fun y pair -> match pair with
                                              | Some (k,v) when k = x -> Some v
                                              | _ -> y ) None cache
    in
    match y with
      | None ->
        let y' = f x in
        cache.(!avail_ptr) <- Some (x,y');
        avail_ptr := (!avail_ptr + 1) mod n; (* Update available cache space pointer *)
        y'
      | Some y' -> y'
  )

(* Question 3: Doubly-linked circular lists  *)

(* Circular doubly linked lists *)

(* The type of a cell (a non-empty circular list) *)
type 'a cell = { mutable p : 'a cell; data : 'a ; mutable n : 'a cell}

(* The type of possibly empty circular lists *)
type 'a circlist = 'a cell option

(* An empty circular list *)
let empty :'a circlist = None

(* A singleton list that contains a single element *)
let singl (x : 'a) : 'a circlist =
  let rec pointer = {p = pointer ; data = x ; n = pointer} in
  Some pointer

(* Rotate a list to next element *)
let next : 'a circlist -> 'a circlist = function
  | None -> None
  | Some cl -> Some (cl.n)

(* Rotate a list to previous element *)
let prev : 'a circlist -> 'a circlist = function
  | None -> None
  | Some cl -> Some (cl.p)

(* Q3.1: Write a function that add a new element at the beginning of a list *)
let cons (x : 'a)  (xs : 'a circlist) : 'a circlist = match xs with
  | None -> singl x
  | Some head -> let current = {p = head.p; data = x; n = head} in
    head.p.n <- current;
    head.p <- current;
    Some head

(* Q3.2: Write a function that computes the length of a list (Careful with the infinite loops)  *)
let rec length (l : 'a circlist) : int =
  let rec length' head count current = match current with
    | _ when current.n == head -> count + 1
    | _ -> length' head (count + 1) (current.n)
  in
  match l with
    | None -> 0
    | Some l' -> length' l' 0 l'

(* Q3.3: Write a function that produces an immutable list from a circular list *)
let to_list (l : 'a circlist)  : 'a list =
  let rec to_list' head li = function
    | current when current.n == head -> current.data :: li
    | current -> to_list' head (current.data :: li) (current.n)
  in
  match l with
    | None -> []
    | Some l' -> List.rev @@ to_list' l' [] l'

(* Once you've written cons you can use this function to quickly populate your lists *)
let rec from_list : 'a list -> 'a circlist = function
  | [] -> empty
  | x::xs -> cons x (from_list xs)

(* Q3.4: Write a function that reverses all the directions of the list *)
let rev (l : 'a circlist) : 'a circlist =
  let rec rev' head current =
    let n' = current.n in
    current.n <- current.p;
    current.p <- n';
    if n' == head then head else rev' head n'
  in
  match l with
    | None -> l
    | Some l' -> Some (rev' l' l')

(* (Extra credit) OPTIONAL: Write the map function as applied to lists *)
let map (f : 'a -> 'b) : 'a circlist -> ' b circlist =
  let rec map' f head copy current =
    if current.n == head then copy
    else begin
      let copy = cons (f current.n.data) copy in
      map' f head copy current.n
    end
  in
  function
    | None -> None
    | Some l' ->
      let copy = singl (f l'.data) in map' f l' copy l'

(* Some possibly useful functions (Wink, wink!) *)

(* A function that returns the Greatest Common Denominator of two numbers *)
let rec gcd (u : int) (v : int) : int =
  if v <> 0 then (gcd v (u mod v))
  else (abs u)

(* A function that returns the least common multiple of two numbers *)
let lcm (m : int) (n : int) : int  =
  match m, n with
    | 0, _ | _, 0 -> 0
    | m, n -> abs (m * n) / (gcd m n)


(* (Extra credit) OPTIONAL A function that compares two lists ignoring the rotation *)
let eq (l1 : 'a circlist) (l2 : 'a circlist) : bool =
  (* [a;b;c] and [a;b;c;a;b;c] are equal so we simply check if lcm of their
   * lengths is equal to the longest as if longer is not multiple of shorter
   * then they cannot match one to one.
   * If [a;b;c;a;b;c] and [a;b;c;a;b;c;a;b;c], or [a;a] and [a;a;a] are not
   * supposed to be the same, simply un-comment the lcm check. *)
  let len1 = length l1 in
  let len2 = length l2 in
  (* let lcms = lcm len1 len2 in *)
  match l1,l2 with
    | None, None -> true
    | None, _ -> false
    | _, None -> false
    (* | _, _ when lcms <> len1 && lcms <> len2 -> false *)
    | Some l1', Some l2' -> (* Functions declared below so they aren't created
                             * if the lists do not pass the easy cases checks *)
      (* 3. Actual equality checking function *)
      let eq' l1' l2' =
      (* 3.5 Actual actual equality checking function to keep track of the
       * original head *)
        let rec eq'' head l1' l2' =
          if l1'.data <> l2'.data then false
          else if l2' == head then true
          else eq'' head l1'.n l2'.n
        in
        eq'' l2' l1'.n l2'.n (* rot_match took care of the head *)
      in
      (* 2. Since [a;b;c] is equal to [b;c;a] and [c;a;b] *)
      let rec rot_match l1' l2' = function
        | 0 -> false
        | n ->
          if l1'.data = l2'.data then
            if eq' l1' l2' then true
            else rot_match l1'.n l2' (n - 1)
          else rot_match l1'.n l2' (n - 1)
      in
      (* 1. Put shorter as first argument *)
      let rec swap_len l1' l2' =
        if len1 < len2 then rot_match l1' l2' len1
        else rot_match l2' l1' len2
      in
      swap_len l1' l2'

(* Some examples *)
(*
let ex = cons 12 (cons 43 (cons 34 (singl 3)))
let lex = to_list ex

let l1 = from_list [true; true ; false]
let l3 = from_list [true; true ; false ; true; true ; false]

let l4 = from_list ['a'; 'b'; 'a'; 'b']
let l5 = from_list ['a'; 'b'; 'a'; 'b'; 'a'; 'b']

let l6 = from_list ['a'; 'a']
let l7 = from_list ['a'; 'a'; 'a']

let l8 = from_list [1 ; 2 ; 3]
let l9 = from_list [3 ; 1 ; 2]  (* eq l8 l9 = true *)

let l10 = from_list [1 ; 2 ; 3]
let l11 = from_list [3 ; 2 ; 1]  (* eq l10 l11 = false *)
(**)

let l12 = from_list [1;2;3;1;4]
let l13 = from_list [1;4;1;2;3]

let l14 = from_list [1;1;1;1;1;1;1;1]
let l15 = from_list [1;1;1;1;1;1]

let l16 = from_list [1;2;3;1]
let l17 = from_list [1;2;3]

let () = assert ( (eq l1 l3) && (eq l4 l5) && (eq l6 l7) && (eq l8 l9) && not (eq l10 l11) && (eq l12 l13) && (eq l14 l15) && not (eq l16 l17) )
*)
