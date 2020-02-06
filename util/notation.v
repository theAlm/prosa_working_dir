From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* Here we define a more verbose notation for projections of pairs... *)
Section Pair.

  Context {A B: Type}.
  Variable p: A * B.
  Definition pair_1st := fst p.
  Definition pair_2nd := snd p.

End Pair.

(* ...and triples. *)
Section Triple.

  Context {A B C: Type}.
  Variable p: A * B * C.
  Definition triple_1st (p: A * B * C) := fst (fst p).
  Definition triple_2nd := snd (fst p).
  Definition triple_3rd := snd p.

End Triple.

(* Define a wrapper from an element to a singleton list. *)
Definition make_sequence {T: Type} (opt: option T) :=
  match opt with
    | Some j => [:: j]
    | None => [::]
  end.

(* Next we define a notation for the big concatenation operator.*)
  
Reserved Notation "\cat_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
   format "'[' \cat_ ( m <= i < n ) '/ ' F ']'").

Notation "\cat_ ( m <= i < n ) F" :=
  (\big[cat/[::]]_(m <= i < n) F%N) : nat_scope.

Reserved Notation "\cat_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, P at level 41, i, m, n at level 50,
   format "'[' \cat_ ( m <= i < n | P ) '/ ' F ']'").

Notation "\cat_ ( m <= i < n | P ) F" :=
  (\big[cat/[::]]_(m <= i < n | P) F%N) : nat_scope.

Reserved Notation "\cat_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
   format "'[' \cat_ ( i < n ) '/ ' F ']'").

Notation "\cat_ ( i < n ) F" :=
  (\big[cat/[::]]_(i < n) F%N) : nat_scope.

Reserved Notation "\cat_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
   format "'[' \cat_ ( i < n | P ) '/ ' F ']'").

Notation "\cat_ ( i < n | P ) F" :=
  (\big[cat/[::]]_(i < n | P) F%N) : nat_scope.
  
(* Let's define big operators for lists of pairs. *)

Reserved Notation "\sum_ ( ( m , n ) <- r ) F"
  (at level 41, F at level 41, m, n at level 50,
   format "'[' \sum_ ( ( m , n ) <- r ) '/ ' F ']'").

Notation "\sum_ ( ( m , n ) <- r ) F" :=
  (\sum_(i <- r) (let '(m,n) := i in F)) : nat_scope.

Reserved Notation "\sum_ ( ( m , n ) <- r | P ) F"
  (at level 41, F at level 30, P at level 41, m, n at level 50,
   format "'[' \sum_ ( ( m , n ) <- r | P ) '/ ' F ']'").

Notation "\sum_ ( ( m , n ) <- r | P ) F" :=
  (\sum_(i <- r | (let '(m,n) := i in P))
    (let '(m,n) := i in F)) : nat_scope.

Reserved Notation "\max_ ( ( m , n ) <- r ) F"
  (at level 41, F at level 41, m, n at level 50,
   format "'[' \max_ ( ( m , n ) <- r ) '/ ' F ']'").

Notation "\max_ ( ( m , n ) <- r ) F" :=
  (\max_(i <- r) (let '(m,n) := i in F)) : nat_scope.

Reserved Notation "\max_ ( ( m , n ) <- r | P ) F"
  (at level 41, F at level 30, P at level 41, m, n at level 50,
   format "'[' \max_ ( ( m , n ) <- r | P ) '/ ' F ']'").

Notation "\max_ ( ( m , n ) <- r | P ) F" :=
  (\max_(i <- r | (let '(m,n) := i in P))
    (let '(m,n) := i in F)) : nat_scope.

Notation "[ 'seq' ( x , y ) <- s | C ]" :=
  (filter (fun i => let '(x,y) := i in C%B) s)
 (at level 0, x at level 99,
  format "[ '[hv' 'seq' ( x , y ) <- s '/ ' | C ] ']'") : seq_scope.

(* In case we use an (option list T), we can define membership
   without having to match the option type. *)
Reserved Notation "x \In A"
  (at level 70, format "'[hv' x '/ ' \In A ']'", no associativity).
Notation "x \In A" :=
  (if A is Some B then in_mem x (mem B) else false) : bool_scope.
