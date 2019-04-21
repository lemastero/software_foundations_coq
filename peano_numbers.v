(*
Translation of
Programming Language Foundations in Agda,
Philip Wadler, Wen Kokke
Chaper Naturals: Natural numbers
https://plfa.github.io/Naturals/

into Coq
*)

(*

types
-----

N datatype of natural numbers

0 has type N
1 has type N
2 has type N
...

0 : N
1 : N
2 : N
....

inference rule
--------------


 m : N        <- hypothesis (zero or more judements)  
------------
 Succ m : N   <- conclusion (singe judgement)

we read:
if m has type N
then Succ m has type N

*)



(*
PEANO NUMBERS

1888 Richard Dedekind “Was sind und was sollen die Zahlen?”
1889 Giuseppe Peano “Arithmetices principia, nova methodo exposita”

see: Basic Peano arithmetic: https://coq.inria.fr/stdlib/index.html

This is unary representation of natural numbers (coputer use binary,
most common by humans decimal)


natural numbrers - inductive datatype
-------------------------------------
Definition of infinite set of natural numbers using inference rules:

----------
 Zero : N

 m : N
------------
 Succ m : N



Succ and Zero are datatype constructors
                  ---------------------


base case - Zero is a natural number
---------
inductive case - If m is a natural number then Succ m is a natural number
--------------


Inductive process:
-----------------

first step - we have natural number:
Zero

next step - we have natural numbers:
Zero
Succ Zero

next step - we have natural numbers:
Zero
Succ Zero
Succ (Succ Zero)

...

*)


Inductive natural : Set :=
  | Zero : natural
  | Succ : natural -> natural.


(*

nautural - name of the datatype

signatures of constructors

  | Zero : natural
  | Succ : natural -> natural.

*)


(* Addition

0 + n = n
(1 + m) + n = 1 + (m + n)


 n : N
--------------
 Zero + n = n

 m + n = p
-----------------------
 (Succ m) + n = Succ p


*)

Fixpoint add (n m : natural) : natural :=
  match n with
    | Zero => m
    | Succ n2 => Succ (add n2 m)
  end.
(*
Recursive definition
---------

definition is well founded because on RHS numbers in add are smaller
              ------------
*)

Example example_2_plus_3_is_5 :
  add
    (Succ (Succ Zero))
    (Succ (Succ (Succ Zero))) =
  (Succ (Succ (Succ (Succ (Succ Zero))))).
Proof. reflexivity. Qed.

(* Multiplication

0 * m = 0
(1 + n) * m = m + (n * m) 
*)
Fixpoint multi (n m : natural) : natural :=
  match n with
    | Zero => Zero
    | Succ n2 => add m (multi n2 m)
  end.

Example example_2_times_3_is_6 :
  multi
    (Succ (Succ Zero))
    (Succ (Succ (Succ Zero))) =
  (Succ (Succ (Succ (Succ (Succ (Succ Zero)))))).
Proof. reflexivity. Qed.

(* Exponentation

n ^ 0 = 1
n ^ (1 + m) = n * (n ^ m)
*)
Fixpoint exp (n m : natural) : natural :=
  match m with
    | Zero => Succ Zero
    | Succ m2 => multi n (exp n m2)
  end.

Example example_2_exp_3_is_8 :
  exp
    (Succ (Succ Zero))
    (Succ (Succ (Succ Zero))) =
  (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero)))))))).
Proof. reflexivity. Qed.

(* Monus - minus that round at 0

m - 0 = m
0 - (1 + n) = 0
(1 + m) - (1 + n) = m - n
*)

Fixpoint monus (n m : natural) : natural :=
  match (n,m) with
    | (n2, Zero) => n2 
    | (Zero, Succ m2) => Zero
    | (Succ n2, Succ m2) => monus n2 m2
  end.

Example example_2_monus_3_is_0 :
  monus
    (Succ (Succ Zero))
    (Succ (Succ (Succ Zero))) = Zero.
Proof. reflexivity. Qed.

Example example_3_monus_2_is_1 :
  monus
    (Succ (Succ (Succ Zero)))
    (Succ (Succ Zero))
     = (Succ Zero).
Proof. reflexivity. Qed.

(* Binary natural numbers as bitstring
TODO this seems wired, mix list with binary numbers
maybe just binary numbers with B0 B1 should be enough
*)

Inductive bitstring_nat : Set :=
  | Nil : bitstring_nat
  | X0 : bitstring_nat -> bitstring_nat
  | X1 : bitstring_nat -> bitstring_nat.

(*
TODO how to use currying (in add multi exp monus) in Coq?
1930 Haskell Curry
1920 Moses Schönfinkel
1879 Gottlob Frege, Begriffschrift
*)
