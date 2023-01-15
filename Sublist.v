From Coq Require Import Lists.List.
Import ListNotations.

Inductive sublist {T : Type} : list T -> nat -> nat -> list T -> Prop :=
| SHeadIncluded head tail j subtail : sublist subtail 0 j tail ->
                                        sublist (head::subtail) 0 (S j) (head::tail)
| SHeadExcluded head tail i j sub :   sublist sub i j tail ->
                                        sublist sub (S i) (S j) (head::tail)
| SNil i lst :                        sublist [] i i lst.

Lemma nil_sublist {X : Type} (i j : nat) {xs : list X} :
  sublist [] i j xs -> i = j.
Proof. Admitted.

Lemma sublist_trans {X : Type} {xs ys zs : list X} {i j k l : nat} :
    sublist xs i j ys ->
    sublist ys k l zs ->
  sublist xs k (k + length xs) zs.
Proof. Admitted.

Lemma sublist_app {X : Type} {xs ys : list X} :
  sublist xs 0 (length xs) (xs ++ ys).
Proof. Admitted.

Lemma sublist_of_app_sublist_left {X : Type} {xs ys zs : list X} {i j : nat} :
    sublist (xs ++ ys) i j zs ->
  sublist xs i (i + length xs) zs.
Proof. Admitted.

Lemma sublist_of_app_sublist_right {X : Type} {xs ys zs : list X} {i j : nat} :
    sublist (xs ++ ys) i j zs ->
  sublist ys (i + length xs) j zs.
Proof. Admitted.