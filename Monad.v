(* this file is a simplified version of https://github.com/coq-community/coq-ext-lib/blob/master/theories/Structures/Monad.v *)

From PetitC Require Import Ids.

From Coq Require Import Lists.List.
Import ListNotations.

Class Monad (m : Type -> Type)  : Type := {
  ret : forall {T : Type}, T -> m T;
  bind : forall {S T : Type}, m S -> (S -> m T) -> m T
}.

Notation "m >>= f" := (bind m f)            (at level 58, left associativity).
Notation "f =<< m" := (bind f m)            (at level 61, right associativity).
Notation "f >=> g" := (fun x => f x >>= g)  (at level 61, right associativity).
Notation "m ;; x" := (m >>= fun _ => x)     (at level 61, right associativity).

Notation "x <- m ;; n" := (m >>= fun x => n)
    (at level 61, m at next level, right associativity).
Notation "' pat <- m ;; n" := (m >>= fun x => match x with pat => n end)
    (at level 61, pat pattern, m at next level, right associativity).

Global Instance option_Monad : Monad option := {
  ret := @Some;
  bind := fun _ _ o f => match o with
                         | None => None
                         | Some x => f x
                         end
}.

Definition state (State T : Type) := State -> T * State.

Global Instance state_Monad {State : Type} : Monad (state State) := {
  ret := fun _ x state => (x, state);
  bind := fun _ _ m f s => match m s with (x, s') => f x s' end
}.

Definition get {State : Type} : state State State := fun s => (s, s).

Definition put {State : Type} (s : State) : state State unit := fun _ => (tt, s).

Definition state_option (State T : Type) := State -> option T * State.

Global Instance state_option_Monad {State : Type} : Monad (state_option State) := {
  ret := fun _ x s => (Some x, s);
  bind := fun _ _ m f s => match m s with
                           | (Some x, s') => f x s'
                           | (None, s')   => (None, s')
                           end
}.

(* Definition geto {State : Type} : state_option State State := fun s => (Some s, s).

Definition puto {State : Type} (s : State) : state_option State unit := fun _ => (Some tt, s). *)

Definition ret_None {State T : Type} : state_option State T := fun s => (None, s).

Definition monad_map {S T : Type} {m : Type -> Type} `{Monad m}
                     (f : S -> m T) (l : list S) : m (list T) :=
  fold_left (fun monad_acc elt => acc <- monad_acc;;
                                  f_elt <- f elt;;
                                  ret (f_elt::acc))
                 l
                 (ret []).
