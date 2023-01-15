From PetitC Require Import Semantics TypedTree Values Memory Ids Star Tactics InbuiltFuncLemmas.
Import TypedTree.

From Coq Require Import ZArith Lia Program.Basics Lists.List Logic.FunctionalExtensionality.
Open Scope nat.

Ltac inv H := (inversion H; subst; clear H).

Lemma map_injective {X Y : Type} (f : X -> Y) (Hinj : forall x x', f x = f x' -> x = x')
      (xs xs' : list X) :
    map f xs = map f xs' ->
  xs = xs'.
Proof.
  generalize dependent xs'.
  induction xs; intros; destruct xs'; try discriminate.
  - reflexivity.
  - injection H; intros.
    f_equal.
    + apply Hinj. assumption.
    + apply IHxs. assumption.
Qed.

Lemma combine_injective_of_same_length {X Y : Type} (xs xs' : list X) (ys ys' : list Y) :
    length xs = length ys ->
    length xs' = length ys' ->
    combine xs ys = combine xs' ys' ->
  xs = xs' /\ ys = ys'.
Proof.
  generalize dependent xs'. generalize dependent ys. generalize dependent ys'.
  induction xs; intros;
  destruct xs'; destruct ys; destruct ys'; try discriminate.
  - split; reflexivity.
  - injection H. intros. injection H0. intros. injection H1. intros. subst.
    split; f_equal.
    + eapply proj1; apply IHxs; eassumption.
    + eapply proj2; apply IHxs; eassumption.
Qed.

Lemma cast_reduction_deterministic : forall ty_from val_from ty_to val_to val_to',
    cast_reduction ty_from val_from ty_to val_to ->
    cast_reduction ty_from val_from ty_to val_to' ->
  val_to = val_to'.
Proof.
  intros.
  inv H; inv H0; reflexivity.
Qed.

Lemma int_arith_binop_reduction_deterministic : forall op lhs rhs result result',
    int_arith_binop_reduction op lhs rhs result ->
    int_arith_binop_reduction op lhs rhs result' ->
  result = result'.
Proof.
  intros. inv H; inv H0; reflexivity.
Qed.

Lemma comparison_reduction_determimnistic : forall comparison lhs rhs result result',
    comparison_reduction comparison lhs rhs result ->
    comparison_reduction comparison lhs rhs result' ->
  result = result'.
Proof.
  intros. inv H; inv H0; reflexivity.
Qed.

Lemma binop_reduction_deterministic :
  forall op lhs rhs result result',
      binop_reduction op lhs rhs result ->
      binop_reduction op lhs rhs result' ->
    result = result'.
Proof.
  intros.
  inv H; inv H0;
  try (inv H1; inv H2; inv H3; inv H5; inv H6; inv H7;
       reflexivity).
  - inv H1; inv H4;
    f_equal;
    apply int_value_to_Z_eq;
    etransitivity; eassumption || (symmetry; eassumption).
  - inv H1; inv H4;
    reflexivity.
  - inv H4; inv H10;
    inv H1; inv H2; inv H7; inv H8;
    reflexivity.
  - inv H1; inv H2; inv H5; inv H6;
    f_equal; apply int_value_to_Z_eq;
    eapply Z.mul_reg_l;
    try (etransitivity; eassumption || (symmetry; eassumption));
    unfold word_size; lia.
Qed.

Lemma short_circuit_reduction_first_deterministic : forall short_circuit_op lhs result result',
    short_circuit_reduction_first short_circuit_op lhs result ->
    short_circuit_reduction_first short_circuit_op lhs result' ->
  result = result'.
Proof.
  intros. inv H; inv H0; reflexivity.
Qed.

Lemma short_circuit_reduction_second_deterministic :
  forall short_circuit_op lhs rhs result result',
      short_circuit_reduction_second short_circuit_op lhs rhs result ->
      short_circuit_reduction_second short_circuit_op lhs rhs result' ->
    result = result'.
Proof.
  intros. inv H; inv H0; reflexivity.
Qed.

Lemma short_circuit_reduction_not_first_and_second :
  forall short_circuit_op lhs rhs result result',
      short_circuit_reduction_first short_circuit_op lhs result ->
      short_circuit_reduction_second short_circuit_op lhs rhs result' ->
    False.
Proof.
  intros. inv H; inv H0.
Qed.

Lemma bool_to_value_injective : forall b b',
    bool_to_value b = bool_to_value b' ->
  b = b'.
Proof.
  intros [|] [|]; reflexivity || discriminate.
Qed.

Lemma incr_or_decr_reduction_deterministic : forall ty incr_or_decr val result result',
    incr_or_decr_reduction ty incr_or_decr val result ->
    incr_or_decr_reduction ty incr_or_decr val result' ->
  result = result'.
Proof.
  intros.
  inv H; inv H0; repeat f_equal.
  - apply int_value_to_Z_eq.
    etransitivity; eassumption || (symmetry; eassumption).
  - apply bool_to_value_injective; symmetry; assumption.
Qed.

Lemma write_deterministic : forall mem ptr value mem' mem'',
    write mem ptr value mem' ->
    write mem ptr value mem'' ->
  mem' = mem''.
Proof.
  intros.
  inv H; inv H0; repeat f_equal.
  rewrite H1 in H8. injection H8. intros. subst. reflexivity.
Qed.

Lemma read_deterministic : forall mem ptr value value',
    read mem ptr value ->
    read mem ptr value' ->
  value = value'.
Proof.
  intros.
  inv H; inv H0.
  - rewrite H1 in H5. injection H5. intros. subst. reflexivity.
  - rewrite H1 in H7. injection H7. intros. subst.
    rewrite H2 in H8. injection H8. intros. subst. reflexivity.
Qed.

Lemma expr_head_reduction_determinisntic :
  forall var_ptrs state expr state' expr' state'' expr'',
      expr_head_reduction var_ptrs (state, expr) (state', expr') ->
      expr_head_reduction var_ptrs (state, expr) (state'', expr'') ->
    state' = state'' /\ expr' = expr''.
Proof.
  intros.
  inv H; inv H0.
  - split; try reflexivity; repeat f_equal.
    eapply cast_reduction_deterministic; eassumption.
  - split; reflexivity.
  - split; try reflexivity; repeat f_equal.
    eapply binop_reduction_deterministic; eassumption.
  - split; try reflexivity; repeat f_equal.
    apply bool_to_value_injective in H4. subst.
    eapply short_circuit_reduction_first_deterministic; eassumption.
  - split; try reflexivity; repeat f_equal.
    apply bool_to_value_injective in H4. subst.
    exfalso. eapply short_circuit_reduction_not_first_and_second; eassumption.
  - split; try reflexivity; repeat f_equal.
    apply bool_to_value_injective in H4. subst.
    exfalso. eapply short_circuit_reduction_not_first_and_second; eassumption.
  - split; try reflexivity; repeat f_equal.
    apply bool_to_value_injective in H4.
    apply bool_to_value_injective in H5. subst.
    eapply short_circuit_reduction_second_deterministic; eassumption.
  - split; try reflexivity; repeat f_equal.
    apply bool_to_value_injective. symmetry. assumption.
  - assert (Hbefore : before = before0).
    { eapply read_deterministic; eassumption. }
    subst.
    assert (Hafter : after = after0).
    { eapply incr_or_decr_reduction_deterministic; eassumption. }
    subst.
    split; try reflexivity; repeat f_equal.
    eapply write_deterministic; eassumption.
  - split; try reflexivity; repeat f_equal.
    eapply write_deterministic; eassumption.
  - assert (Heq : mem' = mem'0 /\ out' = out'0 /\ returned = returned0);
    try (destruct Heq as [Heq0 [Heq1 Heq2]]; subst; split; reflexivity).
    assert (Hargs : args = args0).
    { apply list_to_list_annotated_expr_injective in H5.
      apply map_injective in H5;
      try (intros [] [] H; injection H; intros; subst; reflexivity).
      apply combine_injective_of_same_length in H5; try assumption.
      destruct H5. symmetry. assumption. }
    subst.
    eapply inbuilt_func_deterministic; eassumption.
  - split; try reflexivity; repeat f_equal.
    rewrite H2 in H1. injection H1. intros. subst. reflexivity.
Qed.

Definition reducible (expr : annotated_expr) : Prop :=
  (exists var_ptrs state state' expr',
    expr_head_reduction var_ptrs (state, expr) (state', expr')).

Lemma expr_head_reduction_context_injective : forall ctx expr expr',
    expr_context ctx ->
    ctx expr = ctx expr' ->
  expr = expr'.
Proof.
  intros.
  generalize dependent expr'. generalize dependent expr0.
  revert H. generalize dependent ctx.
  apply (expr_context_mutual_ind
    (fun ctx => forall expr expr', ctx expr = ctx expr' -> expr = expr')
    (fun ctx => forall expr expr', ctx expr = ctx expr' -> expr = expr')
    (fun ctx => forall expr expr', ctx expr = ctx expr' -> expr = expr'));
  intros;
  assumption || apply H0; injection H1 as H1; assumption.
Qed.

Ltac inv_context :=
  match goal with
  | H : expr_context _ |- _      => inv H; try discriminate; try reflexivity
  | H : lvalue_context _ |- _    => inv H; try discriminate; try reflexivity
  | H : list_expr_context _ |- _ => inv H; try discriminate; try reflexivity
  end.

Ltac destruct_reducible :=
  match goal with
  | H : reducible _ |- _ =>
    let var_ptrs := fresh "var_ptrs" in
    let state := fresh "state" in
    let state' := fresh "state" in
    let expr := fresh "expr" in
    destruct H as [var_ptrs [state [state' [expr H]]]];
    inv H; try discriminate; try reflexivity
  end.

Lemma not_arg_exprs_eq_subst_call : forall ctx arg_vals arg_rich_types func_id arg_exprs return_ty,
    list_expr_context ctx ->
    list_to_list_annotated_expr (map (fun '(val, ty) => Const val <: ty)
                                     (combine arg_vals arg_rich_types))
    = ctx (Call func_id arg_exprs <: return_ty) ->
  False.
Proof.
  intros. generalize dependent arg_vals. generalize dependent arg_rich_types.
  induction H; intros;
  destruct arg_vals; destruct arg_rich_types; try discriminate.
  - inv H; discriminate.
  - injection H0. intros. subst.
    eapply IHlist_expr_context. eassumption.
Qed.

Lemma not_arg_exprs_eq_subst_head_reducible :
  forall ctx arg_vals arg_rich_types var_ptrs state state' expr expr',
      list_expr_context ctx ->
      expr_head_reduction var_ptrs (state, expr) (state', expr') ->
      list_to_list_annotated_expr (map (fun '(val, ty) => Const val <: ty)
                                      (combine arg_vals arg_rich_types))
      = ctx expr ->
    False.
Proof.
  intros. generalize dependent arg_vals. generalize dependent arg_rich_types.
  induction H; intros;
  destruct arg_vals; destruct arg_rich_types; try discriminate.
  - inv H; try discriminate.
    inv H0; discriminate.
  - injection H1. intros. subst.
    eapply IHlist_expr_context. eassumption.
Qed.


Lemma expr_head_reduction_context_unique : forall ctx expr ctx' expr',
    reducible expr ->
    reducible expr' ->
    expr_context ctx ->
    expr_context ctx' ->
    ctx expr = ctx' expr' ->
  ctx = ctx'.
Proof.
  (* this takes a few minutes and a few gigabytes of ram *)
  intros. revert H3. revert H2. revert H0. revert H. revert expr'. revert ctx'. revert expr0.
  revert H1. revert ctx.
  apply (expr_context_mutual_ind
    (fun ctx => forall expr ctx' expr', reducible expr -> reducible expr' ->
      expr_context ctx' -> ctx expr = ctx' expr' -> ctx = ctx')
    (fun ctx => forall expr ctx' expr', reducible expr -> reducible expr' ->
      lvalue_context ctx' -> ctx expr = ctx' expr' -> ctx = ctx')
    (fun ctx => forall expr ctx' expr', reducible expr -> reducible expr' ->
      list_expr_context ctx' -> ctx expr = ctx' expr' -> ctx = ctx'));
  intros;
  try (inv H3;
       try (injection H4; intros; subst;
           assert (Hctx : ctx = ctx0); try (rewrite Hctx; reflexivity);
           (apply (H0 expr0 ctx0 expr') || apply (H0 expr1 ctx0 expr')); assumption);
      inv_context; repeat destruct_reducible;
      fail);
  try (inv_context;
       try (injection H4; intros; subst;
            assert (Hctx : ctx = ctx0); try (rewrite Hctx; reflexivity);
            (apply (H0 expr0 ctx0 expr') || apply (H0 expr1 ctx0 expr')); assumption;
            fail);
       try (destruct_reducible; destruct H1 as [var_ptrs [state [state' [expr' H1]]]];
            injection H5; intros;
            exfalso; eapply not_arg_exprs_eq_subst_head_reducible; eassumption);
       try (inv H5; inv H3; destruct_reducible; fail);
       try (repeat destruct_reducible; inv_context; fail);
       try (inv H; repeat destruct_reducible; fail);
       try (inv_context; inv_context; repeat destruct_reducible; fail);
       try (inv H; inv H3; repeat destruct_reducible; fail);
       fail).
  repeat destruct_reducible;
  try (inv_context; inv_context; inv_context; fail);
  inv_context;
  injection H2; intros;
  exfalso;
  try (eapply (not_arg_exprs_eq_subst_head_reducible _ _ _ var_ptrs state0 state0) ||
       eapply (not_arg_exprs_eq_subst_head_reducible _ _ _ var_ptrs (mem, out) (mem', out)) ||
       eapply (not_arg_exprs_eq_subst_head_reducible _ _ _ var_ptrs (mem', out') (mem'0, out'0));
       eassumption || (econstructor; eassumption)).
  eapply (not_arg_exprs_eq_subst_head_reducible _ _ _ var_ptrs (mem, out) (mem', out'));
  eassumption || (econstructor; eassumption).
Qed.

Lemma expr_func_reduction_context_unique :
  forall ctx ctx' func_id return_ty arg_vals arg_rich_types
                  func_id' return_ty' arg_vals' arg_rich_types',
    expr_context ctx ->
    expr_context ctx' ->
    let arg_exprs := list_to_list_annotated_expr
      (map (fun '(val, ty) => Const val <: ty)
           (combine arg_vals arg_rich_types)) in
    let call_expr := Call func_id arg_exprs <: return_ty in
    let arg_exprs' := list_to_list_annotated_expr
      (map (fun '(val, ty) => Const val <: ty)
           (combine arg_vals' arg_rich_types')) in
    let call_expr' := Call func_id' arg_exprs' <: return_ty' in
    ctx call_expr = ctx' call_expr' ->
  ctx = ctx'.
Proof.
  intros. generalize dependent ctx'. generalize dependent ctx.
  apply (expr_context_mutual_ind
    (fun ctx => forall ctx',
      expr_context ctx' -> ctx call_expr = ctx' call_expr' -> ctx = ctx')
    (fun ctx => forall ctx',
      lvalue_context ctx' -> ctx call_expr = ctx' call_expr' -> ctx = ctx')
    (fun ctx => forall ctx',
      list_expr_context ctx' -> ctx call_expr = ctx' call_expr' -> ctx = ctx'));
  intros;
  unfold call_expr in *; unfold call_expr' in *;
  try (inv H1; try discriminate;
       try (inv H; try discriminate; inv H1; discriminate);
       try (inv H3; try discriminate; inv H1; discriminate);
       injection H2; intros; subst;
       assert (Hctx : ctx = ctx0); try (rewrite Hctx; reflexivity);
       apply H0; assumption).
  - unfold arg_exprs in *.
    inv H; try discriminate; try reflexivity.
    injection H0; intros.
    exfalso. eapply not_arg_exprs_eq_subst_call; eassumption.
  - inv H1; try discriminate.
    + injection H2; intros.
      unfold arg_exprs' in *.
      exfalso. eapply not_arg_exprs_eq_subst_call.
      * eassumption.
      * symmetry. eassumption.
    + injection H2. intros. subst.
      assert (Hctx : ctx = ctx0); try (rewrite Hctx; reflexivity).
      apply H0; assumption.
Qed.

Lemma expr_func_reduction_context_injective :
  forall ctx,
    expr_context ctx ->
  forall func_id return_ty arg_vals arg_rich_types
         func_id' return_ty' arg_vals' arg_rich_types',
    let arg_exprs := list_to_list_annotated_expr
      (map (fun '(val, ty) => Const val <: ty)
           (combine arg_vals arg_rich_types)) in
    let call_expr := Call func_id arg_exprs <: return_ty in
    let arg_exprs' := list_to_list_annotated_expr
      (map (fun '(val, ty) => Const val <: ty)
           (combine arg_vals' arg_rich_types')) in
    let call_expr' := Call func_id' arg_exprs' <: return_ty' in
    ctx call_expr = ctx call_expr' ->
  call_expr = call_expr'.
Proof.
  apply (expr_context_mutual_ind
    (fun ctx => forall func_id return_ty arg_vals arg_rich_types
                       func_id' return_ty' arg_vals' arg_rich_types',
        let arg_exprs := list_to_list_annotated_expr
          (map (fun '(val, ty) => Const val <: ty)
              (combine arg_vals arg_rich_types)) in
        let call_expr := Call func_id arg_exprs <: return_ty in
        let arg_exprs' := list_to_list_annotated_expr
          (map (fun '(val, ty) => Const val <: ty)
              (combine arg_vals' arg_rich_types')) in
        let call_expr' := Call func_id' arg_exprs' <: return_ty' in
        ctx call_expr = ctx call_expr' ->
      call_expr = call_expr')
  (fun ctx => forall func_id return_ty arg_vals arg_rich_types
                     func_id' return_ty' arg_vals' arg_rich_types',
        let arg_exprs := list_to_list_annotated_expr
          (map (fun '(val, ty) => Const val <: ty)
              (combine arg_vals arg_rich_types)) in
        let call_expr := Call func_id arg_exprs <: return_ty in
        let arg_exprs' := list_to_list_annotated_expr
          (map (fun '(val, ty) => Const val <: ty)
              (combine arg_vals' arg_rich_types')) in
        let call_expr' := Call func_id' arg_exprs' <: return_ty' in
        ctx call_expr = ctx call_expr' ->
      call_expr = call_expr')
  (fun ctx => forall func_id return_ty arg_vals arg_rich_types
                     func_id' return_ty' arg_vals' arg_rich_types',
        let arg_exprs := list_to_list_annotated_expr
          (map (fun '(val, ty) => Const val <: ty)
              (combine arg_vals arg_rich_types)) in
        let call_expr := Call func_id arg_exprs <: return_ty in
        let arg_exprs' := list_to_list_annotated_expr
          (map (fun '(val, ty) => Const val <: ty)
              (combine arg_vals' arg_rich_types')) in
        let call_expr' := Call func_id' arg_exprs' <: return_ty' in
        ctx call_expr = ctx call_expr' ->
      call_expr = call_expr'));
  intros;
  assumption || apply H0; injection H1 as H1; assumption.
Qed.

Lemma not_subst_call_expr_eq_subst_head_reducible :
  forall ctx,
    expr_context ctx ->
  forall ctx' arg_vals arg_rich_types func_id return_ty var_ptrs expr expr' state state',
    expr_context ctx' ->
    expr_head_reduction var_ptrs (state, expr) (state', expr') ->
    let arg_exprs := list_to_list_annotated_expr
      (map (fun '(val, ty) => Const val <: ty)
          (combine arg_vals arg_rich_types)) in
    let call_expr := Call func_id arg_exprs <: return_ty in
    ctx call_expr = ctx' expr ->
  False.
Proof.
  apply (expr_context_mutual_ind
    (fun ctx =>
      forall ctx' arg_vals arg_rich_types func_id return_ty var_ptrs expr expr' state state',
        expr_context ctx' ->
        expr_head_reduction var_ptrs (state, expr) (state', expr') ->
        let arg_exprs := list_to_list_annotated_expr
          (map (fun '(val, ty) => Const val <: ty)
              (combine arg_vals arg_rich_types)) in
        let call_expr := Call func_id arg_exprs <: return_ty in
        ctx call_expr = ctx' expr ->
      False)
    (fun ctx =>
      forall ctx' arg_vals arg_rich_types func_id return_ty var_ptrs expr expr' state state',
        lvalue_context ctx' ->
        expr_head_reduction var_ptrs (state, expr) (state', expr') ->
        let arg_exprs := list_to_list_annotated_expr
          (map (fun '(val, ty) => Const val <: ty)
              (combine arg_vals arg_rich_types)) in
        let call_expr := Call func_id arg_exprs <: return_ty in
        ctx call_expr = ctx' expr ->
      False)
    (fun ctx =>
      forall ctx' arg_vals arg_rich_types func_id return_ty var_ptrs expr expr' state state',
        list_expr_context ctx' ->
        expr_head_reduction var_ptrs (state, expr) (state', expr') ->
        let arg_exprs := list_to_list_annotated_expr
          (map (fun '(val, ty) => Const val <: ty)
              (combine arg_vals arg_rich_types)) in
        let call_expr := Call func_id arg_exprs <: return_ty in
        ctx call_expr = ctx' expr ->
      False));
  intros;
  try (inv H1; try discriminate;
       (inv H2; try discriminate; inv H; discriminate) ||
       (inv H; inv H2; inv H1; discriminate) ||
       (injection H3; intros; subst; eapply H0; eassumption) ||
       (inv H4; try discriminate; inv H2; discriminate) ||
       (inv H4; inv H1; try discriminate; inv H2; discriminate)).
  - unfold call_expr in *. inv H; try discriminate.
    + inv H0; discriminate.
    + injection H1. intros. subst.
      eapply not_arg_exprs_eq_subst_head_reducible; eassumption.
  - inv H1; try discriminate.
    + assert (H2' := H2).
      inv H2; try discriminate.
      injection H4. intros. subst.
      unfold call_expr in *. unfold arg_exprs in *.
      eapply not_arg_exprs_eq_subst_call; eassumption.
    + injection H3. intros.
      eapply H0; eassumption.
Qed.

Lemma assign_vars_deterministic : forall var_ptrs mem var_ids vals mem' mem'',
    assign_vars var_ptrs mem var_ids vals mem' ->
    assign_vars var_ptrs mem var_ids vals mem'' ->
  mem' = mem''.
Proof.
  intros.
  generalize dependent mem''.
  induction H; intros.
  - inv H0. reflexivity.
  - inv H0. inv H1. inv H10.
    rewrite H2 in H0. injection H0. intros. subst.
    assert (Heq : mem' = mem'0).
    { apply IHassign_vars. assumption. }
    subst.
    eapply write_deterministic; eassumption.
Qed.

Lemma allocate_vars_deterministic :
  forall mem var_ptrs var_ids mem' var_ptrs' mem'' var_ptrs'',
      allocate_vars mem var_ptrs var_ids mem' var_ptrs' ->
      allocate_vars mem var_ptrs var_ids mem'' var_ptrs'' ->
    (mem', var_ptrs') = (mem'', var_ptrs'').
Proof.
  intros.
  generalize dependent var_ptrs''. generalize dependent mem''.
  induction H; intros.
  - inv H0. reflexivity.
  - inv H1.
    apply IHallocate_vars in H6.
    injection H6. intros. subst.
    rewrite <- H0 in H9.
    injection H9. intros. subst. reflexivity.
Qed.

Lemma call_var_ptrs_and_mem_deterministic :
  forall var_ptrs mem arg_var_ids arg_vals var_ptrs' mem' var_ptrs'' mem'',
    call_var_ptrs_and_mem
      var_ptrs mem arg_var_ids arg_vals var_ptrs' mem' ->
    call_var_ptrs_and_mem
      var_ptrs mem arg_var_ids arg_vals var_ptrs'' mem'' ->
  (var_ptrs', mem') = (var_ptrs'', mem'').
Proof.
  intros.
  inv H. inv H0.
  assert (Heq : (mem'0, var_ptrs') = (mem'1, var_ptrs'')).
  { eapply allocate_vars_deterministic; eassumption. }
  injection Heq. intros. subst.
  f_equal.
  eapply assign_vars_deterministic; eassumption.
Qed.

Theorem continued_step_deterministic' :
  forall funcs var_ptrs var_ptrs' var_ptrs'' state state' state'' cont cont' cont'',
      continued_step funcs (var_ptrs, state, cont) (var_ptrs', state', cont') ->
      continued_step funcs (var_ptrs, state, cont) (var_ptrs'', state'', cont'') ->
    (var_ptrs', state', cont') = (var_ptrs'', state'', cont'').
Proof.
  intros; inv H; inv H0; try reflexivity;
  try (f_equal; f_equal; inv_context; inv H8; discriminate);
  try (apply bool_to_value_injective in H3; subst; reflexivity).
  - assert (Hctx: ctx0 = ctx).
    { eapply expr_head_reduction_context_unique;
      eassumption || (repeat eexists); eassumption. }
    subst.
    apply expr_head_reduction_context_injective in H4; try assumption. subst.
    f_equal; f_equal.
    + eapply proj1. eapply expr_head_reduction_determinisntic; eassumption.
    + f_equal. eapply proj2. eapply expr_head_reduction_determinisntic; eassumption.
  - eapply not_subst_call_expr_eq_subst_head_reducible in H2; try eassumption.
    destruct H2.
  - symmetry in H3.
    eapply not_subst_call_expr_eq_subst_head_reducible in H3; try eassumption.
    destruct H3.
  - assert (H3' := H3).
    eapply expr_func_reduction_context_unique in H3'; try assumption. subst.
    apply expr_func_reduction_context_injective in H3; try assumption.
    injection H3. intros. subst.
    rewrite H6 in H4. injection H4. intros. subst.
    apply list_to_list_annotated_expr_injective in H0.
    apply map_injective in H0.
    + apply combine_injective_of_same_length in H0; try assumption.
      destruct H0. subst.
      f_equal.
      assert (Heq : (var_ptrs', mem') = (var_ptrs'', mem'0)).
      { eapply call_var_ptrs_and_mem_deterministic; eassumption. }
      injection Heq. intros. subst. reflexivity.
    + intros. destruct x. destruct x'. injection H1. intros. subst. reflexivity.
Qed.

Fixpoint csubst (outer inner : continuation_after_cmd) :
                       continuation_after_cmd :=
  match outer with
  | KStop => inner
  | KSeq cmd cont                 => KSeq cmd (csubst cont inner)
  | KWhileAfterCmd expr cmd cont  => KWhileAfterCmd expr cmd (csubst cont inner)
  | KCall ctx var_ptrs cont       => KCall ctx var_ptrs (esubst cont inner)
  end
  
with esubst (outer : continuation_after_expr) (inner : continuation_after_cmd) :
                   continuation_after_expr :=
  match outer with
  | KExpr cont                    => KExpr (csubst cont inner)
  | KIf cmd cmd' cont             => KIf cmd cmd' (csubst cont inner)
  | KWhileAfterExpr expr cmd cont => KWhileAfterExpr expr cmd (csubst cont inner)
  end.

Lemma Skip_KStop_final funcs var_ptrs state :
  final (continued_step funcs) (var_ptrs, state, ContinuedCmd Skip KStop).
Proof.
  intros y H. inv H.
Qed.

Lemma continued_step_deterministic funcs :
  deterministic (continued_step funcs).
Proof.
  intro. intros.
  destruct x. destruct y. destruct y'. destruct p. destruct p0. destruct p1.
  eapply continued_step_deterministic'; eassumption.
Qed.

Lemma continued_step_same_continuation_of_continued_step_SKip_KStop funcs nb_steps var_ptrs state
                                                                    var_ptrs' state' cmd cont :
  star_count (continued_step funcs) nb_steps (var_ptrs, state, ContinuedCmd cmd cont)
                                             (var_ptrs', state', ContinuedCmd Skip KStop) ->
  exists nb_steps' var_ptrs'' state'', nb_steps' <= nb_steps /\
    star_count (continued_step funcs) nb_steps' (var_ptrs, state, ContinuedCmd cmd cont)
                                                (var_ptrs'', state'', ContinuedCmd Skip cont).
Proof. Admitted.

Lemma continued_step_KStop_of_continued_step_Skip_same_cont
        funcs nb_steps var_ptrs var_ptrs' state state' cmd cont :
  star_count (continued_step funcs) nb_steps (var_ptrs, state, ContinuedCmd cmd cont)
                                             (var_ptrs', state', ContinuedCmd Skip cont) ->
  exists nb_steps' var_ptrs'' state'', nb_steps' <= nb_steps /\
    star_count (continued_step funcs) nb_steps' (var_ptrs, state, ContinuedCmd cmd KStop)
                                                (var_ptrs'', state'', ContinuedCmd Skip KStop).
Proof. Admitted.

Lemma continued_step_csubst_of_continued_step
        nb_steps funcs var_ptrs state var_ptrs' state' cmd cmd' cont cont' sub_cont :
  star_count (continued_step funcs) nb_steps
    (var_ptrs, state, ContinuedCmd cmd cont)
    (var_ptrs', state', ContinuedCmd cmd' cont) ->
  star_count (continued_step funcs) nb_steps
    (var_ptrs, state, ContinuedCmd cmd (csubst cont sub_cont))
    (var_ptrs', state', ContinuedCmd cmd' (csubst cont' sub_cont)).
Proof. Admitted.

Lemma continued_step_KStop_and_cont_of_continued_step_Skip_same_cont
        funcs nb_steps var_ptrs var_ptrs' state state' cmd cont :
  star_count (continued_step funcs) nb_steps (var_ptrs, state, ContinuedCmd cmd cont)
                                             (var_ptrs', state', ContinuedCmd Skip cont) ->
  exists nb_steps' var_ptrs'' state'', nb_steps' <= nb_steps /\
    star_count (continued_step funcs) nb_steps' (var_ptrs, state, ContinuedCmd cmd KStop)
                                                (var_ptrs'', state'', ContinuedCmd Skip KStop) /\
    star_count (continued_step funcs) nb_steps' (var_ptrs, state, ContinuedCmd cmd cont)
                                                (var_ptrs'', state'', ContinuedCmd Skip cont).
Proof.
  intros.
  destruct (continued_step_KStop_of_continued_step_Skip_same_cont _ _ _ _ _ _ _ _ H)
    as [nb_steps' [var_ptrs'' [state'' [Hle Hstar_count]]]].
  exists nb_steps'. exists var_ptrs''. exists state''.
  repeat split; try assumption.
  assert (Heq_subst : cont = csubst KStop cont). { reflexivity. }
  rewrite Heq_subst.
  apply continued_step_csubst_of_continued_step.
  assumption.
Qed.

Lemma continued_step_KStop_and_cont_of_continued_step_Skip_KStop
        funcs nb_steps var_ptrs var_ptrs' state state' cmd cont :
  star_count (continued_step funcs) nb_steps (var_ptrs, state, ContinuedCmd cmd cont)
                                             (var_ptrs', state', ContinuedCmd Skip KStop) ->
  exists nb_steps' var_ptrs'' state'', nb_steps' <= nb_steps /\
    star_count (continued_step funcs) nb_steps' (var_ptrs, state, ContinuedCmd cmd KStop)
                                                (var_ptrs'', state'', ContinuedCmd Skip KStop) /\
    star_count (continued_step funcs) nb_steps' (var_ptrs, state, ContinuedCmd cmd cont)
                                                (var_ptrs'', state'', ContinuedCmd Skip cont).
Proof.
  intros.
  destruct (continued_step_same_continuation_of_continued_step_SKip_KStop _ _ _ _ _ _ _ _ H)
      as [nb_steps' [var_ptrs'' [state'' [Hle Hstar_count]]]].
  destruct
    (continued_step_KStop_and_cont_of_continued_step_Skip_same_cont _ _ _ _ _ _ _ _ Hstar_count)
    as [nb_steps0 [var_ptrs0 [state0 [Hineq [Hstar_count0 Hstar_count1]]]]].
  exists nb_steps0. exists var_ptrs0. exists state0.
  repeat split; try assumption. lia.
Qed.

Lemma continued_step_KExpr_of_continued_step_KStop
  nb_steps funcs var_ptrs var_ptrs' state state' expr :
    star_count (continued_step funcs) nb_steps
                    (var_ptrs, state, ContinuedExpr expr (KExpr KStop))
                    (var_ptrs', state', ContinuedCmd Skip KStop) ->
    exists val ty,
      star_count (continued_step funcs) (nb_steps-1)
                      (var_ptrs, state, ContinuedExpr expr (KExpr KStop))
                      (var_ptrs', state', ContinuedExpr (Const val <: ty) (KExpr KStop)).
Proof. Admitted.

Lemma continued_step_KStop_and_cont_of_continued_step_Expr_const_KStop
        funcs nb_steps var_ptrs var_ptrs' state state' expr cont :
  star_count (continued_step funcs) nb_steps
                    (var_ptrs, state, ContinuedExpr expr cont)
                    (var_ptrs', state', ContinuedCmd Skip KStop) ->
  exists nb_steps' var_ptrs'' state'' val ty, nb_steps' <= nb_steps /\
    star_count (continued_step funcs) nb_steps'
                      (var_ptrs, state, ContinuedExpr expr (KExpr KStop))
                      (var_ptrs'', state'', ContinuedExpr (Const val <: ty) (KExpr KStop)) /\
    star_count (continued_step funcs) nb_steps'
                      (var_ptrs, state, ContinuedExpr expr cont)
                      (var_ptrs'', state'', ContinuedExpr (Const val <: ty) cont).
Proof. Admitted.