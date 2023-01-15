(* i get a syntax error when i do [Variables {X : Type} (rel : X -> X -> Prop).] (even inside a section) *)

Inductive star {X : Type} (rel : X -> X -> Prop) : X -> X -> Prop :=
  | StarRefl x :     star rel x x
  | StarCons x y z :   rel x y ->
                       star rel y z ->
                     star rel x z.

Arguments StarRefl {X rel x}.
Arguments StarCons {X rel x y z}.

Inductive star_count {X : Type} (rel : X -> X -> Prop) : nat -> X -> X -> Prop :=
  | StarCountRefl x :       star_count rel 0 x x
  | StarCountCons n x y z :   rel x y ->
                              star_count rel n y z ->
                            star_count rel (S n) x z.

Arguments StarCountRefl {X rel x}.
Arguments StarCountCons {X rel n x y z}.

Definition deterministic {X : Type} (rel : X -> X -> Prop) : Prop :=
  forall x y y', rel x y -> rel x y' -> y = y'.

Definition final {X : Type} (rel : X -> X -> Prop) (x : X) : Prop :=
  forall y, ~rel x y.

Lemma star_trans {X : Type} {rel : X -> X -> Prop} {x y z : X} :
    star rel x y ->
    star rel y z ->
  star rel x z.
Proof. Admitted.

Lemma star_count_trans {X : Type} {rel : X -> X -> Prop} {x y z : X} {n m : nat} :
    star_count rel n x y ->
    star_count rel m y z ->
  star_count rel (n + m) x z.
Proof. Admitted.

Lemma star_from_middle_of_deterministic_of_final_count
           {X : Type} {rel : X -> X -> Prop} {first middle last : X} {n m : nat} :
  deterministic rel ->
  final rel last ->
  star_count rel n first middle ->
  star_count rel m first last -> 
  n <= m /\ star_count rel (m - n) middle last.
Proof. Admitted.

