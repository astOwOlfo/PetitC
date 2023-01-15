From PetitC Require Import InbuiltFunc InbuiltFuncSemantics Memory Output Values Tactics.

From Coq Require Import ZArith.

Lemma inbuilt_func_deterministic :
  forall inbuilt_func arg_vals return_val_option return_val_option' mem out mem' out' mem'' out'',
      inbuilt_func_step inbuilt_func arg_vals return_val_option mem out mem' out' ->
      inbuilt_func_step inbuilt_func arg_vals return_val_option' mem out mem'' out'' ->
      mem' = mem'' /\ out' = out'' /\ return_val_option = return_val_option'.
Proof.
  intros.
  inv H; inv H0;
  repeat split; try reflexivity;
  rewrite <- H1 in H3; apply Nat2Z.inj in H3; subst;
  rewrite <- H2 in H4; injection H4; intros; subst; reflexivity.
Qed.
