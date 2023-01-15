From Coq Require Import FSets.FMapAVL FSets.FSetAVL Structures.OrderedTypeEx Lists.List.
Import ListNotations.

Definition var_id := nat.
Definition func_id := nat.
Definition block_id := nat.
(* Opaque var_id func_id block_id label. *)

Module VarIdMap := FMapAVL.Make Nat_as_OT.
Module FuncIdMap := FMapAVL.Make Nat_as_OT.
Module BlockIdMap := FMapAVL.Make Nat_as_OT.

Fixpoint FuncIdMap_of_assoc_list {T : Type} (assoc_list : list (func_id * T)) : FuncIdMap.t T :=
  match assoc_list with
  | (id, x)::tail => FuncIdMap.add id x (FuncIdMap_of_assoc_list tail)
  | []            => FuncIdMap.empty _
  end.

(* Module PairNat_as_OT <: UsualOrderedType.
  Definition t := (nat * nat)%type.

  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Inductive lt' : t -> t -> Prop :=
    | LtFst : forall x y x' y', x < x' ->
        lt' (x, y) (x', y')
    | LtSnd : forall x y y', y < y' ->
        lt' (x, y) (x, y').

  Definition lt := lt'.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof. Admitted.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof. Admitted.

  Definition compare x y : OrderedType.Compare lt eq x y.
  Admitted.

  Definition eq_dec : forall n m : (nat * nat), {n = m} + {n <> m}.
  Admitted.
End PairNat_as_OT. *)
