From PetitC Require Import Codegen Asm TypedTree Memory Output Semantics AsmSemantics SemanticsLemmas
                           MemoryEquivalence Values Ids Monad Star Tactics Sublist.
Import TypedTree. (* why do i have to import TypedTree? all the definitions are on top level there *)

From Coq Require Import Lists.List Nat ZArith Program.Utils Wellfounded Nat Lia.
Import ListNotations.
Open Scope nat.

Section CodegenLemmas.

Variables (funcs : list (func_id * func))
          (func_labels : FuncIdMap.t label)
          (func_depths : FuncIdMap.t nat)
          (var_rbp_offsets : VarIdMap.t offset)
          (var_depths : VarIdMap.t nat).

Definition toplevel_accessible_var_ids_opt (func_id : func_id) : option (list var_id) :=
  assoc func_id funcs >>= fun func =>
  Some ((f_local_var_ids func) ++ (f_arg_var_ids func)).

Fixpoint toplevel_accessible_var_ids_opt_of_list (func_ids : list func_id) :
           option (list var_id) :=
  match func_ids with
  | id::ids => toplevel_accessible_var_ids_opt id >>= fun func_var_ids =>
               toplevel_accessible_var_ids_opt_of_list ids >>= fun func_var_ids' =>
               Some (func_var_ids ++ func_var_ids')
  | []      => Some []
  end.

Definition accessible_var_ids_opt (func_id : func_id) : option (list var_id) :=
  assoc func_id funcs >>= fun func =>
  toplevel_accessible_var_ids_opt func_id >>= fun var_ids =>
  toplevel_accessible_var_ids_opt_of_list (f_parent_func_ids func) >>= fun parent_var_ids =>
  Some (var_ids ++ parent_var_ids).

Definition accessible_var_ids (func_id : func_id) (var_ids : list var_id) :=
  accessible_var_ids_opt func_id = Some var_ids.

Definition parent_rbp (stack : stack) (rbp : offset) (parent_rbp : offset) : Prop :=
  OffsetMap.find (rbp + Z.of_nat word_size)%Z stack = Some (PtrValue (StackPtr parent_rbp)).

Inductive ancestor_rbp (stack : stack) : nat -> offset -> offset -> Prop :=
  | ARZero (rbp : offset) :
      ancestor_rbp stack 0%nat rbp rbp
  | ARSucc (depth : nat) (rbp parent_rbp' ancestor_rbp' : offset) : (* primes to avoid name clashes *)
        parent_rbp stack rbp parent_rbp' ->
        ancestor_rbp stack depth parent_rbp' ancestor_rbp' ->
      ancestor_rbp stack (S depth) rbp ancestor_rbp'.

Definition asm_var_ptr (stack : stack) (rbp : offset)
                            (var_id : var_id) (ptr : ptr_value) : Prop :=
  exists depth ancestor_rbp' rbp_offset,
    VarIdMap.find var_id var_depths = Some depth /\
    VarIdMap.find var_id var_rbp_offsets = Some rbp_offset /\
    ancestor_rbp stack depth rbp ancestor_rbp' /\
    ptr = StackPtr (ancestor_rbp' + rbp_offset)%Z.

Definition asm_accessible_var_ptrs (stack : stack) (rbp : offset) (func_id : func_id)
                                        (var_ptrs : VarIdMap.t ptr_value) : Prop :=
  exists var_ids, accessible_var_ids func_id var_ids /\
                  (forall var_id, In var_id var_ids <-> VarIdMap.In var_id var_ptrs) /\
                  forall var_id ptr, VarIdMap.find var_id var_ptrs = Some ptr ->
                                     asm_var_ptr stack rbp var_id ptr.

Definition VarIdMap_combine {X Y : Type}
                            (m : VarIdMap.t X) (m' : VarIdMap.t Y) (l : list (X * Y)) : Prop :=
  NoDup l /\
  (forall id, VarIdMap.In id m <-> VarIdMap.In id m') /\
  (forall x y, In (x, y) l <->
                exists id, VarIdMap.find id m = Some x /\ VarIdMap.find id m' = Some y).

Definition states_equivalent (rbp : offset) (func_id : func_id) (c_var_ptrs : VarIdMap.t ptr_value)
                             (c_state asm_state : memory * output) : Prop :=
  let '(c_mem, c_out) := c_state in
  let '((asm_stack, asm_heap) as asm_mem, asm_out) := asm_state in
  c_out = asm_out /\
  exists asm_var_ptrs,
    asm_accessible_var_ptrs asm_stack rbp func_id asm_var_ptrs /\
    (forall var_id, VarIdMap.In var_id c_var_ptrs <-> VarIdMap.In var_id asm_var_ptrs) /\
    exists corresponding_ptrs,
      VarIdMap_combine c_var_ptrs asm_var_ptrs corresponding_ptrs /\
      accessible_equivalent corresponding_ptrs c_mem asm_mem.

(* Definition compile_cmd' (args : compile_args) (depth : nat) (cmd : cmd)
                        (break_lbl continue_lbl : label) (label_counter : label_counter) :
                        option asm :=
  let compiled := compile_cmd (ca_func_depths args) depth (ca_var_rbp_offsets args)
                              (ca_var_depths args) break_lbl continue_lbl cmd [] label_counter in
  match compiled with
  | (Some asm, _) => Some asm
  | (None, _)     => None
  end. *)

Lemma compile_cmd_eq_cons_tail_asm fd d vro vd bl cl lc lc' cmd tail_asm asm_app_tail :
  compile_cmd fd d vro vd bl cl cmd tail_asm lc = (Some asm_app_tail, lc') ->
  exists asm,
    asm_app_tail = asm ++ tail_asm /\
    compile_cmd fd d vro vd bl cl cmd [] lc = (Some asm, lc').
Proof. Admitted.

Lemma compile_expr_eq_cons_tail_asm fd d vro vd lc lc' cmd tail_asm asm_app_tail :
  compile_expr fd d vro vd cmd tail_asm lc = (Some asm_app_tail, lc') ->
  exists asm,
    asm_app_tail = asm ++ tail_asm /\
    compile_expr fd d vro vd cmd [] lc = (Some asm, lc').
Proof. Admitted.

Definition cmd_compiles_to fd vro vd (depth : nat) (cmd : cmd) (asm : asm) : Prop :=
  exists  cl bl label_counter label_counter',
    compile_cmd fd depth vro vd bl cl cmd [] label_counter = (Some asm, label_counter').

Definition expr_compiles_to fd vro vd (depth : nat) (expr : annotated_expr) (asm : asm) : Prop :=
  exists  label_counter label_counter',
    compile_expr fd depth vro vd expr [] label_counter = (Some asm, label_counter').

(* Definition subprogram
    (prog : prog) (func_id : func_id) (first_instr_index last_instr_index : nat) (asm : asm) :=
  exists func_asm, FuncIdMap.find func_id prog = Some func_asm /\
                   sublist asm first_instr_index last_instr_index func_asm. *)

Definition backward_simulates
    (nb_steps : nat) (funcs : list (func_id * func)) (prog : prog) (func_id : func_id)
    (cmd : cmd) (asm : asm) (first_instr_index last_instr_index : nat) : Prop :=
  forall c_var_ptrs c_var_ptrs' c_state c_state' asm_state regs rbp,
    star_count (continued_step funcs) nb_steps (c_var_ptrs, c_state, ContinuedCmd cmd KStop)
                                               (c_var_ptrs', c_state', ContinuedCmd Skip KStop) ->
    r_rbp regs = PtrValue (StackPtr rbp) ->
    states_equivalent rbp func_id c_var_ptrs c_state asm_state ->
    exists regs' asm_state' rbp',
      r_rbp regs' = PtrValue (StackPtr rbp') /\
      states_equivalent rbp' func_id c_var_ptrs' c_state' asm_state' /\
      star (instr_step prog) (asm_state, (func_id, first_instr_index), regs)
                             (asm_state', (func_id, last_instr_index), regs').


Definition backward_simulates_expr
    (nb_steps : nat) (funcs : list (func_id * func)) (prog : prog) (func_id : func_id)
    (expr : annotated_expr) (asm : asm) (first_instr_index last_instr_index : nat) : Prop :=
  forall c_var_ptrs c_var_ptrs' c_state c_state' asm_state regs rbp val ty,
    star_count (continued_step funcs) nb_steps
                  (c_var_ptrs, c_state, ContinuedExpr expr (KExpr KStop))
                  (c_var_ptrs', c_state', ContinuedExpr (Const val <: ty) (KExpr KStop)) ->
    r_rbp regs = PtrValue (StackPtr rbp) ->
    states_equivalent rbp func_id c_var_ptrs c_state asm_state ->
    exists regs' asm_state' rbp',
      r_rbp regs' = PtrValue (StackPtr rbp') /\
      r_rax regs' = val /\
      states_equivalent rbp' func_id c_var_ptrs' c_state' asm_state' /\
      star (instr_step prog) (asm_state, (func_id, first_instr_index), regs)
                             (asm_state', (func_id, last_instr_index), regs').


Ltac destruct_compile_cmd cmd :=
  let a := fresh "asm" in
  let lc := fresh "label_counter" in
  let H := fresh "Hcompile" in
  destruct (compile_cmd _ _ _ _ _ _ cmd _ _) as [[a | ] lc] eqn:H; try discriminate.

Ltac destruct_compile_expr expr :=
  let a := fresh "asm" in
  let lc := fresh "label_counter" in
  let H := fresh "Hcompile" in
  destruct (compile_expr _ _ _ _ expr _ _) as [[a | ] lc] eqn:H; try discriminate.

Ltac elim_tail_asm cmd :=
  match goal with
  | [ H : compile_cmd _ _ _ _ _ _ cmd _ _ = (Some _, _) |- _ ] =>
      let asm := fresh "asm" in
      let Hasm_app := fresh "Hasm_app" in
      let Hcompile := fresh "Hcompile" in
      apply compile_cmd_eq_cons_tail_asm in H;
      destruct H as [asm [Hasm_app Hcompile]];
      clear H; subst
  end.

Ltac elim_tail_asm_expr expr :=
  match goal with
  | [ H : compile_expr _ _ _ _ expr _ _ = (Some _, _) |- _ ] =>
      let asm := fresh "asm" in
      let Hasm_app := fresh "Hasm_app" in
      let Hcompile_expr := fresh "Hcompile" in
      apply compile_expr_eq_cons_tail_asm in H;
      destruct H as [asm [Hasm_app Hcompile_expr]];
      clear H; subst
  end.

Ltac separate_first cmd cont cmd' cont' :=
  match goal with
  | [ Hstar_continued_step : star_count (continued_step _) _
                                (_, _, _ cmd cont)
                                (_, _, _ cmd' cont') |- _] =>
    let Hstar_continued_step' := fresh "Hstar_continued_step" in
    let Hstar_continued_step'' := fresh "Hstar_continued_step" in
    let Hcontinued_step := fresh "continued_step" in
    let Hineq := fresh "Hineq" in
    let nb_steps := fresh "nb_steps" in
    let nb_steps' := fresh "nb_steps" in
    let x := fresh "x" in
    let y := fresh "y" in
    inversion Hstar_continued_step
      as [nb_steps x | nb_steps' x y z Hcontinued_step Hstar_continued_step']; subst;
    inversion Hcontinued_step; subst;
    destruct (star_from_middle_of_deterministic_of_final_count
                  (continued_step_deterministic _) (Skip_KStop_final _ _ _)
                  (StarCountCons Hcontinued_step StarCountRefl) Hstar_continued_step)
        as [Hineq Hstar_continued_step'']
  end.

Ltac separate_last expr :=
  match goal with
  | [ Hstar_continued_step : star_count (continued_step _) _
                                          (_, _, ContinuedExpr expr (KExpr KStop))
                                          (_, _, ContinuedCmd Skip KStop) |- _ ] =>
  let val := fresh "val" in let ty := fresh "ty" in
  let Hstar_continued_step' := fresh "Hstar_continued_step" in
  destruct (continued_step_KExpr_of_continued_step_KStop _ _ _ _ _ _ _ Hstar_continued_step)
    as [val [ty Hstar_continued_step']]
  end.

Ltac from_middle cmd cont cmd' cont' :=
  match goal with
  | [ Hstar_continued_step : star_count (continued_step _) _ _ (_, _, _ cmd cont),
      Hstar_continued_step' : star_count (continued_step _) _ _ (_, _, _ cmd' cont') |- _ ] =>
    let Hstar_continued_step'' := fresh "Hstar_continued_step" in
    let Hstar_continued_step''' := fresh "Hstar_continued_step" in
    let Hineq := fresh "Hineq" in
    destruct (star_from_middle_of_deterministic_of_final_count
                (continued_step_deterministic _) (Skip_KStop_final _ _ _)
                Hstar_continued_step Hstar_continued_step')
      as [Hineq Hstar_continued_step''']
  end.

Ltac fastest_same_cont_skip_full cmd cont :=
  match goal with
  | [ Hstar_continued_step : star_count (continued_step _) _
                                (_, _, ContinuedCmd cmd cont)
                                (_, _, ContinuedCmd Skip KStop) |- _ ] =>
    let Hstar_continued_step' := fresh "Hstar_continued_step" in
    let Hstar_continued_step'' := fresh "Hstar_continued_step" in
    let nb_steps := fresh "nb_steps" in
    let var_ptrs := fresh "var_ptrs" in
    let Hineq := fresh "Hineq" in
    let H := fresh "H" in  
    assert (H := Hstar_continued_step);
    apply continued_step_KStop_and_cont_of_continued_step_Skip_KStop in H;
    destruct H as [nb_steps [var_ptrs [state [Hineq [Hstar_continued_step' Hstarcontinued_step'']]]]];
    from_middle Skip cont Skip KStop
  end.

Ltac fastest_same_cont_skip_full_expr expr cont :=
  match goal with
  | [ Hstar_continued_step : star_count (continued_step _) _
                                (_, _, ContinuedExpr expr cont)
                                (_, _, ContinuedCmd Skip KStop) |- _ ] =>
    let Hstar_continued_step' := fresh "Hstar_continued_step" in
    let Hstar_continued_step'' := fresh "Hstar_continued_step" in
    let nb_steps := fresh "nb_steps" in
    let var_ptrs := fresh "var_ptrs" in
    let Hineq := fresh "Hineq" in
    let val := fresh "val" in
    let ty := fresh "ty" in
    let H := fresh "H" in  
    assert (H := Hstar_continued_step);
    apply continued_step_KStop_and_cont_of_continued_step_Expr_const_KStop in H;
    destruct H as [nb_steps [var_ptrs [state [val [ty [Hineq [Hstar_continued_step' Hstarcontinued_step'']]]]]]];
    from_middle (Const val <: ty) cont Skip KStop
  end.

Ltac simulate_cmd IH nb_steps cmd asm_state Hrbp Hstates_equivalent Hstar_continued_step :=
  let Hsimulation := fresh "Hsimulation" in
  let regs' := fresh "regs" in
  let asm_state' := fresh "asm_state" in
  let rbp' := fresh "rbp" in
  let Hrbp' := fresh "Hrbp" in
  let Hstates_equivalent' := fresh "Hstates_equivalent" in
  let Hstar_instr_step' := fresh "Hstar_instr_step" in
  eassert (Hsimulation : backward_simulates nb_steps _ _ _ cmd _ _ _);
  try ( eapply IH; try (eexists; repeat eexists; eassumption); try eassumption; try lia;
        (eapply sublist_of_app_sublist_left; eassumption) ||
        (eapply sublist_of_app_sublist_right; eassumption) );
  destruct (Hsimulation _ _ _ _ asm_state _ _ Hstar_continued_step Hrbp Hstates_equivalent)
    as [regs' [asm_state' [rbp' [Hrbp' [Hstates_equivalent' Hstar_instr_step']]]]].

Ltac simulate_cmd' IH nb_steps cmd asm_state Hrbp Hstates_equivalent Hstar_continued_step :=
  let Hsimulation := fresh "Hsimulation" in
  let regs' := fresh "regs" in
  let asm_state' := fresh "asm_state" in
  let rbp' := fresh "rbp" in
  let Hrbp' := fresh "Hrbp" in
  let Hstates_equivalent' := fresh "Hstates_equivalent" in
  let Hstar_instr_step' := fresh "Hstar_instr_step" in
  eassert (Hsimulation : backward_simulates nb_steps _ _ _ cmd _ _ _) (* ;
  try ( eapply IH; try (eexists; repeat eexists; eassumption); try eassumption; try lia;
        (eapply sublist_of_app_sublist_left; eassumption) ||
        (eapply sublist_of_app_sublist_right; eassumption) );
  destruct (Hsimulation _ _ _ _ asm_state _ _ Hstar_continued_step Hrbp Hstates_equivalent)
    as [regs' [asm_state' [rbp' [Hrbp' [Hstates_equivalent' Hstar_instr_step']]]]]. *).

Ltac simulate_expr IH nb_steps expr asm_state Hrbp Hstates_equivalent Hstar_continued_step :=
  let Hsimulation := fresh "Hsimulation" in
  let regs' := fresh "regs" in
  let asm_state' := fresh "asm_state" in
  let rbp' := fresh "rbp" in
  let Hrbp' := fresh "Hrbp" in
  let Hrax' := fresh "Hrax" in
  let Hstates_equivalent' := fresh "Hstates_equivalent" in
  let Hstar_instr_step' := fresh "Hstar_instr_step" in
  eassert (Hsimulation : backward_simulates_expr nb_steps _ _ _ expr _ _ _);
  try ( eapply IH; try (eexists; repeat eexists; eassumption); try eassumption; try lia;
        (eapply sublist_of_app_sublist_left; eassumption) ||
        (eapply sublist_of_app_sublist_right; eassumption) );
  destruct (Hsimulation _ _ _ _ asm_state _ _ _ _  Hstar_continued_step Hrbp Hstates_equivalent)
    as [regs' [asm_state' [rbp' [Hrbp' [Hrax' [Hstates_equivalent' Hstar_instr_step']]]]]].

Theorem backward_simulation_aux nb_steps :
  ( forall funcs prog func_id func func_asm fd vro vd cmd cmd_asm first_instr_index last_instr_index,
      compile_file funcs = Some prog ->
      In (func_id, func) funcs ->
      FuncIdMap.find func_id prog = Some func_asm ->
      cmd_compiles_to fd vro vd (depth func) cmd cmd_asm ->
      sublist cmd_asm first_instr_index last_instr_index func_asm ->
      backward_simulates nb_steps funcs prog func_id cmd
                         cmd_asm first_instr_index last_instr_index ) /\
  ( forall funcs prog func_id func func_asm fd vro vd expr expr_asm first_instr_index last_instr_index,
      compile_file funcs = Some prog ->
      In (func_id, func) funcs ->
      FuncIdMap.find func_id prog = Some func_asm ->
      expr_compiles_to fd vro vd (depth func) expr expr_asm ->
      backward_simulates_expr nb_steps funcs prog func_id expr
                              expr_asm first_instr_index last_instr_index ).
Proof.
  induction (lt_wf nb_steps) as [n _ IH].

  assert (IHCmd := fun nb_steps Hnb_steps => proj1 (IH nb_steps Hnb_steps)).
  assert (IHExpr := fun nb_steps Hnb_steps => proj2 (IH nb_steps Hnb_steps)).
  clear IH.

  split.

  - (* Case : show that commands are compiled correctly *)
    intros funcs0 prog func_id func func_asm fd vro vd cmd cmd_asm first_instr_index last_instr_index
          Hcompile_file Hfunc_In Hfunc_asm [bl [cl [lc [lc' Hcompile]]]] Hsublist
          c_var_ptrs c_var_ptrs' c_state c_state' asm_state regs rbp
          Hstar_continued_step Hrbp Hstates_equivalent.

    destruct cmd as [ | cmd1 cmd2 | expr | cond_expr then_cmd else_cmd | | | | | ];
    simpl in Hcompile.

    + (* Case : cmd = Skip *)
      injection Hcompile as Hcompile. subst.
      inv Hstar_continued_step.

      * (* Zero C small steps. *)
        (* Since there are zero c steps, we can show that the c states before and after are equal
            and that the o compiled command is Skip.
          Then, by executing no instructions the assembly program transitions to the same state
            in zero steps. *)
        exists regs. exists asm_state. exists rbp.
        repeat split; try assumption.
        apply nil_sublist in Hsublist. subst.
        apply StarRefl.

      * (* At least one C small step. *)
        (* This is impossible: no step can be made from [ContinuedInstr Skip KStop] *)
        inv H.

    + (* Case: cmd = Seq cmd1 cmd2 *)
      destruct_compile_cmd cmd2. destruct_compile_cmd cmd1.
      injection Hcompile. intros. subst.
      elim_tail_asm cmd1.

      separate_first (Seq cmd1 cmd2) KStop Skip KStop.
      fastest_same_cont_skip_full cmd1 (KSeq cmd2 KStop).
      separate_first Skip (KSeq cmd2 KStop) Skip KStop.

      simulate_cmd IHCmd nb_steps cmd1 asm_state Hrbp Hstates_equivalent Hstar_continued_step2.
      simulate_cmd IHCmd (S nb_steps0-1-nb_steps-1) cmd2 asm_state0 Hrbp0 Hstates_equivalent0
                     Hstar_continued_step5.
      
      exists regs1. exists asm_state1. exists rbp1.
      repeat split; try assumption.
      eapply star_trans; eassumption.

    + (* Case : cmd = Expr expr *)
      separate_first (Expr expr) KStop Skip KStop.
      separate_last expr.

      simulate_expr IHExpr (S nb_steps0-1-1) expr asm_state Hrbp Hstates_equivalent Hstar_continued_step2.
      exists regs0. exists asm_state0. exists rbp0.
      repeat split; eassumption.

    + (* Case : cmd = If cond_expr then_cmd else_cmd *)
      destruct_compile_cmd else_cmd. destruct_compile_cmd then_cmd.
      destruct_compile_expr cond_expr.
      elim_tail_asm_expr cond_expr. elim_tail_asm then_cmd. elim_tail_asm else_cmd.
      injection Hcompile. intros. subst.

      separate_first (If cond_expr then_cmd else_cmd) KStop Skip KStop.
      fastest_same_cont_skip_full_expr cond_expr (KIf then_cmd else_cmd KStop).
      separate_first (Const val <: ty) (KIf then_cmd else_cmd KStop) Skip KStop;
      try (inv H6; discriminate);
      try (inv continued_step0; inv H2; try discriminate; inv H10; discriminate).
      
      eassert (Hsublist1 : sublist asm1 (2 + first_instr_index + length asm2)
                                   (2 + first_instr_index + length asm2 + length asm1) func_asm).
      { admit. (* This is just a tideous manipulation on lists *) }

      simulate_expr IHExpr nb_steps cond_expr asm_state Hrbp Hstates_equivalent Hstar_continued_step2.

      destruct bool.
      * (* The condition is true, the then branch is executed *)
Abort.
 
(* Theorem backward_simulation_aux nb_steps :
  forall funcs prog func_id func func_asm fd vro vd cmd cmd_asm first_instr_index last_instr_index,
    compile_file funcs = Some prog ->
    In (func_id, func) funcs ->
    FuncIdMap.find func_id prog = Some func_asm ->
    cmd_compiles_to fd vro vd (depth func) cmd cmd_asm ->
    sublist cmd_asm first_instr_index last_instr_index func_asm ->
    backward_simulates nb_steps funcs prog func_id cmd cmd_asm first_instr_index last_instr_index.
Proof.
  induction (lt_wf nb_steps) as [n _ IH].

  intros funcs0 prog func_id func func_asm fd vro vd cmd cmd_asm first_instr_index last_instr_index
         Hcompile_file Hfunc_In Hfunc_asm [bl [cl [lc [lc' Hcompile]]]] Hsublist
         c_var_ptrs c_var_ptrs' c_state c_state' asm_state regs rbp
         Hstar_continued_step Hrbp Hstates_equivalent.

  destruct cmd;
  simpl in Hcompile.

  - (* Case : cmd = Skip *)
    injection Hcompile as Hcompile. subst.

    inv Hstar_continued_step.

  + (* Zero C small steps. *)
    (* Since there are zero c steps, we can show that the c states before and after are equal
         and that the o compiled command is Skip.
       Then, by executing no instructions the assembly program transitions to the same state
         in zero steps. *)
    exists regs. exists asm_state. exists rbp.
    repeat split; try assumption.
    apply nil_sublist in Hsublist. subst.
    apply StarRefl.

  + (* At least one C small step. *)
    (* This is impossible: no step can be made from [ContinuedInstr Skip KStop] *)
    inv H.


  - (* Case: cmd = Seq cmd1 cmd2 *)
    destruct_compile_cmd cmd2. destruct_compile_cmd cmd1.
    injection Hcompile. intros. subst.
    elim_tail_asm cmd1.

    inversion Hstar_continued_step; subst. (* necessarily at least one step *)
    inversion H. subst.
    destruct (star_from_middle_of_deterministic_of_final_count
                  (continued_step_deterministic _) (Skip_KStop_final _ _ _)
                  (StarCountCons H StarCountRefl) Hstar_continued_step)
        as [Hineq Hstar_continued_step'].

    apply continued_step_same_continuation_of_continued_step_SKip_KStop in Hstar_continued_step'.
    destruct Hstar_continued_step' as [n' [var_ptrs'' [state'' [Hineq' Hstar_continued_step']]]].
    apply continued_step_KStop_of_continued_step_Skip_same_cont in Hstar_continued_step'.
    destruct Hstar_continued_step' as [n'' [var_ptrs''' [state''' [Hineq'' Hstar_continued_step'']]]].

    (* we state and show by induction hypothesis that the compiled cmd1 is emulated correctly *)
    assert (Hemulation_cmd1 : exists regs' asm_state' rbp',
      r_rbp regs' = PtrValue (StackPtr rbp') /\
      states_equivalent rbp' func_id var_ptrs''' state''' asm_state' /\
      star (instr_step prog)
        (asm_state, (func_id, first_instr_index), regs)
        (asm_state', (func_id, first_instr_index + length asm0), regs')).
    { eapply IH with (cmd := cmd1) (c_var_ptrs' := var_ptrs''') (y := n''); try eassumption.
      + lia.
      + econstructor; repeat eexists. eassumption.
      + eapply sublist_of_app_sublist_left; eassumption. }

    destruct Hemulation_cmd1 as
      [regs1 [asm_state1 [rbp1 [Hrbp1 [Hstates_equivalent1 Hstar_instr_step1]]]]].
    
    assert (Hstar_continued_step''' := H0).
    apply continued_step_same_continuation_of_continued_step_SKip_KStop in H0.
    destruct H0 as [nb_steps0 [var_ptrs' [state0 [Hineq0 Hstar_continued_step0]]]].
    assert (Hcontinued_step0 : star_count (continued_step funcs0) (S nb_steps0)
                                (c_var_ptrs, c_state, ContinuedCmd cmd1 (KSeq cmd2 KStop))
                                (var_ptrs', c_state, ContinuedCmd cmd2 (KStop))).
   {  assert (Harith : S nb_steps0 = nb_steps0 + 1). { lia. }
      rewrite Harith.
      eapply star_count_trans.
     + eassumption. 
     + repeat econstructor. }
    

  assert (h := star_from_middle_of_deterministic_of_final_count
    (continued_step_deterministic _) (Skip_KStop_final _ _ _) .......).
    
  

Theorem backward_simulation_aux nb_steps :
  forall fd vro vd funcs prog func_id func func_asm cmd cmd_asm first_instr_index last_instr_index
         c_state c_state' c_var_ptrs c_var_ptrs' asm_state regs rbp,
    compile_file funcs = Some prog ->
    In (func_id, func) funcs ->
    compile_func fd (depth func) vro vd (f_body func) = Some func_asm ->
    cmd_compiles_to fd vro vd (depth func) cmd cmd_asm ->
    sublist cmd_asm first_instr_index last_instr_index func_asm ->
    r_rbp regs = PtrValue (StackPtr rbp) ->
    states_equivalent rbp func_id c_var_ptrs c_state asm_state ->
    star_count (continued_step funcs) nb_steps (c_var_ptrs, c_state, ContinuedCmd cmd KStop)
                                               (c_var_ptrs', c_state', ContinuedCmd Skip KStop) ->
    exists regs' asm_state' rbp',
      r_rbp regs' = PtrValue (StackPtr rbp') /\
      states_equivalent rbp' func_id c_var_ptrs' c_state' asm_state' /\
      star (instr_step prog) (asm_state, (func_id, first_instr_index), regs)
                             (asm_state', (func_id, last_instr_index), regs').

Proof.

  induction (lt_wf nb_steps) as [n _ IH].

  intros fd vro vd funcs0 prog func_id func func_asm cmd cmd_asm first_instr_index last_instr_index
         c_state c_state' c_var_ptrs c_var_ptrs' asm_state regs rbp
         Hcompile_file Hcompile_func Hfunc_In Hcompile Hsublist Hrbp Hstates_equivalent
         Hstar_continued_step.
  
  destruct cmd;

  (* simplify Hcompile *)
  inv Hcompile; inv H; inv H0; inv H; simpl in H0; rename H0 into Hcompile;
  rename x into break_lbl; rename x0 into continue_lbl;
  rename x1 into label_counter; rename x2 into label_counter'.

  - (* Case : cmd = Skip *)

    injection Hcompile as Hcompile. subst.

    inv Hstar_continued_step.

    + (* Zero C small steps. *)
      (* Since there are zero c steps, we can show that the c states before and after are equal
           and that the o compiled command is Skip.
         Then, by executing no instructions the assembly program transitions to the same state
           in zero steps. *)
      exists regs. exists asm_state. exists rbp.
      repeat split; try assumption.
      apply nil_sublist in Hsublist. subst.
      apply StarRefl.

    + (* At least one C small step. *)
      (* This is impossible: no step can be made from [ContinuedInstr Skip KStop] *)
      inv H.

  - (* Case: cmd = Seq cmd1 cmd2 *)

    destruct_compile_cmd cmd2. destruct_compile_cmd cmd1.
    injection Hcompile. intros. subst.
    elim_tail_asm cmd1.

    inversion Hstar_continued_step; subst. (* necessarily at least one step *)
    inversion H. subst.
    destruct (star_from_middle_of_deterministic_of_final_count
                  (continued_step_deterministic _) (Skip_KStop_final _ _ _)
                  (StarCountCons H StarCountRefl) Hstar_continued_step)
        as [Hineq Hstar_continued_step'].

    apply continued_step_same_continuation_of_continued_step_SKip_KStop in Hstar_continued_step'.
    destruct Hstar_continued_step' as [n' [var_ptrs'' [state'' [Hineq' Hstar_continued_step']]]].
    apply continued_step_KStop_of_continued_step_Skip_same_cont in Hstar_continued_step'.
    destruct Hstar_continued_step' as [n'' [var_ptrs''' [state''' [Hineq'' Hstar_continued_step'']]]].

    (* we state and show by induction hypothesis that the compiled cmd1 is emulated correctly *)
    assert (Hemulation_cmd1 : exists regs' asm_state' rbp',
      r_rbp regs' = PtrValue (StackPtr rbp') /\
      states_equivalent rbp' func_id var_ptrs''' state''' asm_state' /\
      star (instr_step prog)
        (asm_state, (func_id, first_instr_index), regs)
        (asm_state', (func_id, first_instr_index + length asm0), regs')).
    { eapply IH with (cmd := cmd1) (c_var_ptrs' := var_ptrs''') (y := n''); try eassumption.
      + lia.
      + econstructor; repeat eexists. eassumption.
      + eapply sublist_of_app_sublist_left; eassumption. }

    destruct Hemulation_cmd1 as
      [regs1 [asm_state1 [rbp1 [Hrbp1 [Hstates_equivalent1 Hstar_instr_step1]]]]].

Qed.
    *)

End CodegenLemmas.