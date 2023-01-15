From PetitC Require Import Memory Ids Tactics.

From Coq Require Import Lists.List Lia ZArith.

Lemma init_le_fold_max {X : Type} (xs : list X) (f : X -> nat) (init : nat) :
  init <= fold_left (fun acc x => max (f x) acc) xs init.
Proof.
  generalize dependent init.
  induction xs; intros.
  - reflexivity.
  - transitivity (max (f a) init).
    + lia.
    + apply IHxs.
Qed.

Lemma mem_le_fold_max {X : Type} (xs : list X) (f : X -> nat) (init : nat) (x : X) :
    In x xs ->
  f x <= fold_left (fun acc x => max (f x) acc) xs init.
Proof.
  generalize dependent init.
  induction xs; intros.
  - inv H.
  - inv H.
    + transitivity (max (f x) init).
      * lia.
      * simpl. apply init_le_fold_max.
    + apply IHxs. assumption.
Qed.

Lemma In_of_InA_of_unique {X : Type} (eqX : X -> X -> Prop) (xs : list X) (x : X)
    (Hunique : forall y, eqX x y -> x = y) :
  SetoidList.InA eqX x xs -> In x xs.
Proof.
  intro HInA.
  rewrite SetoidList.InA_alt in HInA. destruct HInA. destruct H.
  apply Hunique in H. subst. assumption.
Qed.

Lemma unused_block_id_not_In heap :
  ~BlockIdMap.In (unused_block_id heap) heap.
Proof.
  unfold unused_block_id. rewrite BlockIdMap.fold_1.
  intros [bl contra].
  apply BlockIdMap.elements_1 in contra.
  unfold BlockIdMap.eq_key_elt in contra.
  unfold BlockIdMap.Raw.Proofs.PX.eqke in contra.
  apply In_of_InA_of_unique in contra;
  try (intros y H0; destruct y; destruct H0; f_equal; assumption).
  apply (Nat.nle_succ_diag_l _ (mem_le_fold_max _ (fun p => 1 + fst p) 0 _ contra)).
Qed.
