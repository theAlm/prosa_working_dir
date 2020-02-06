From mathcomp Require Import ssrbool ssrnat div.

Definition div_floor (x y: nat) : nat := x %/ y.
Definition div_ceil (x y: nat) := if y %| x then x %/ y else (x %/ y).+1.