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

(* Homework 1 - Question 1 *)

(*
   Purpose: inc the number n by k
            assumes n >= 0

   Examples:
   inc 0  5 ==> 5
   inc 3  5 ==> 8


*)

let rec inc (n:int) (k:int) = match n with
  | 0 -> (k:int)
  | _ ->  k + (inc (n - 1) 0) + 1

(* Pupose: compute the nth element of the Fibonacci sequence:

   1, 1, 2, 3, 5, ..., fib (n-1) + fib (n -2)

  assumes n >= 0

  Examples:

  fib 0 => 1
  fib 10 => 89

*)

let rec fib (n : int) = match n with
    0 -> 1
  | 1 -> 1
  | n -> fib (n - 1) + fib (n - 2)
