From PetitC Require Import Values.

From Coq Require Import Logic.ProofIrrelevance.

Lemma int_value_to_Z_eq : forall int_value int_value',
    int_value_to_Z int_value = int_value_to_Z int_value' ->
  int_value = int_value'.
Proof.
  intros [value Hvalue] [value' Hvalue'] Heq. simpl in Heq.
  revert Hvalue'. rewrite <- Heq. intro Hvalue'.
  f_equal. apply proof_irrelevance.
Qed.