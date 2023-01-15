From Coq Require Import Lists.List.
Import ListNotations.

(* how do i import this? i had to copy it from the standard library... *)
Inductive Permutation {A : Type} : list A -> list A -> Prop :=
| perm_nil: Permutation nil nil
| perm_skip: forall (x:A) (l l':list A), Permutation l l' -> Permutation (cons x l) (cons x l')
| perm_swap: forall (x y:A) (l:list A), Permutation (cons y (cons x l)) (cons x (cons y l))
| perm_trans: forall (l l' l'':list A), Permutation l l' -> Permutation l' l'' -> Permutation l l''.
