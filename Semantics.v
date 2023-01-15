From PetitC Require Import Ids Values TypedTree Memory Output InbuiltFunc InbuiltFuncSemantics.
Import TypedTree.

From Coq Require Import ZArith Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint assoc {X : Type} (id : func_id) (assoc_list : list (func_id * X)) : option X :=
  match assoc_list with
  | (id', x)::tail => if (id' =? id)%nat
                      then Some x
                      else assoc id tail
  | []             => None
  end.

Definition write_goes_wrong (mem : memory) (ptr : ptr_value) : Prop :=
  ~exists val st', write mem ptr val st'.

Definition read_goes_wrong (mem : memory) (ptr : ptr_value) : Prop :=
  ~exists val, read mem ptr val.

Definition allocate_var (mem : memory) (var_ptrs : VarIdMap.t ptr_value)
    (id : var_id) : memory * VarIdMap.t ptr_value :=
  let (ptr, mem') := allocate_stack mem in
  (mem', VarIdMap.add id ptr var_ptrs).

Inductive allocate_vars : memory -> VarIdMap.t ptr_value -> list var_id ->
                          memory -> VarIdMap.t ptr_value -> Prop :=

  | AVNil : forall mem var_ptrs,
      allocate_vars mem var_ptrs [] mem var_ptrs
      
  | AVCons : forall mem mem' mem'' var_ptrs var_ptrs' var_ptrs'' id ids_tail,
        allocate_vars mem var_ptrs ids_tail mem' var_ptrs' ->
        (mem'', var_ptrs'') = allocate_var mem' var_ptrs' id ->
      allocate_vars mem var_ptrs (id::ids_tail)mem'' var_ptrs''.

Inductive assign_var (var_ptrs : VarIdMap.t ptr_value) :
      memory -> var_id -> value -> memory -> Prop :=
  | AssignVar : forall mem id ptr val mem',
        VarIdMap.find id var_ptrs = Some ptr ->
        write mem ptr val mem' ->
      assign_var var_ptrs mem id val mem'.

Inductive assign_vars (var_ptrs : VarIdMap.t ptr_value) :
      memory -> list var_id -> list value -> memory -> Prop :=

  | AssignVarsNil : forall mem,
      assign_vars var_ptrs mem [] [] mem
    
  | AssignVarsCons : forall mem mem' mem'' id val ids vals,
        assign_vars var_ptrs mem ids vals mem' ->
        assign_var var_ptrs mem' id val mem'' ->
      assign_vars var_ptrs mem (id::ids) (val::vals) mem''.

Inductive call_var_ptrs_and_mem : VarIdMap.t ptr_value -> memory -> list var_id -> list value ->
                                  VarIdMap.t ptr_value -> memory -> Prop :=
  | CVITPAS : forall var_ptrs var_ptrs' mem mem' mem'' var_ids vals,
        allocate_vars mem var_ptrs var_ids mem' var_ptrs' ->
        assign_vars var_ptrs' mem' var_ids vals mem'' ->
      call_var_ptrs_and_mem var_ptrs mem var_ids vals var_ptrs' mem''.

Inductive expr_context : (annotated_expr -> annotated_expr) -> Prop :=
  | CHole :
      expr_context (fun e => e)
  | CCast ctx ty ty' ty'' :
        expr_context ctx ->
      expr_context (fun e => Cast ty ty' (ctx e) <: ty'')
  | CLvalue ctx ty :
        lvalue_context ctx ->
      expr_context (fun e => LValue (ctx e) <: ty)
  | CAddressOf ctx ty :
        lvalue_context ctx ->
      expr_context (fun e => AddressOf (ctx e) <: ty)
  | CBinOpLeft binop ctx ty expr :
        expr_context ctx ->
      expr_context (fun e => BinOp binop (ctx e) expr <: ty)
  | CBinOpRight binop ctx ty ty' value :
        expr_context ctx ->
      expr_context (fun e => BinOp binop (Const value <: ty) (ctx e) <: ty')
  | CNot ctx ty :
        expr_context ctx ->
      expr_context (fun e => Not (ctx e) <: ty)
  | CIncrOrDecr incr_or_decr pre_or_post ctx ty :
        lvalue_context ctx ->
      expr_context (fun e => IncrOrDecr ty incr_or_decr pre_or_post (ctx e) <: ty)
  | CAssignLeft ctx expr ty :
        lvalue_context ctx ->
      expr_context (fun e => Assign (ctx e) expr <: ty)
  | CAssignRight ctx ptr ty ty' complete_ty :
        expr_context ctx ->
      expr_context (fun e =>
        Assign (Dereference (Const ptr <: ty) <l: complete_ty)
               (ctx e)
        <: ty'
      )
  | CCall ctx func_id ty :
        list_expr_context ctx ->
      expr_context (fun e => Call func_id (ctx e) <: ty)
  | CCallInbuilt ctx inbuilt_func ty :
        list_expr_context ctx ->
      expr_context (fun e => CallInbuilt inbuilt_func (ctx e) <: ty)
      
with lvalue_context : (annotated_expr -> annotated_lvalue) -> Prop :=
  | CDereference ctx complete_ty :
      expr_context ctx ->
    lvalue_context (fun e => Dereference (ctx e) <l: complete_ty)
    
with list_expr_context : (annotated_expr -> list_annotated_expr) -> Prop :=
  | CHead ctx tail :
        expr_context ctx ->
      list_expr_context (fun e => LAECons (ctx e) tail)
  | CTail ctx value ty :
        list_expr_context ctx ->
      list_expr_context (fun e => LAECons (Const value <: ty) (ctx e)).

Scheme expr_context_mutual_ind := Minimality for expr_context Sort Prop
with lvalue_context_mutual_ind := Minimality for lvalue_context Sort Prop
with list_expr_context_mutual_ind := Minimality for list_expr_context Sort Prop.

Definition bool_to_value (b : bool) : value :=
  if b then IntValue one_int_value else IntValue zero_int_value.

Inductive cast_reduction : rich_type -> value -> rich_type -> value  -> Prop :=
  | CRSame value rich_ty ty :
        Some ty = of_rich rich_ty ->
        can_have_type value ty ->
      cast_reduction rich_ty     value
                     rich_ty     value
  | CRIntToBool int_value :
      cast_reduction RInt       (IntValue int_value)
                     RBool      (bool_to_value (negb (Z.eqb (int_value_to_Z int_value) 0)))
  | CRBoolToInt int_value :
      cast_reduction RBool      (IntValue int_value)
                     RInt       (IntValue int_value)
  | CRHeapPtrToBool ty ptr :
      cast_reduction (RPtr ty)  (PtrValue ptr)
                     RBool      (bool_to_value (negb (ptr_value_beq ptr NullPtr)))
  | CRPtrToPtr ptr ty ty' :
      cast_reduction (RPtr ty)  (PtrValue ptr)
                     (RPtr ty') (PtrValue ptr).

Definition cast_reduction_goes_wrong
    (ty_from : rich_type) (val_from : value) (ty_to : rich_type) : Prop :=
  ~exists val_to, cast_reduction ty_from val_from ty_to val_to.

Inductive int_arith_binop_reduction : int_arith_binop -> Z -> Z -> Z -> Prop :=
  | IABRPlusIntInt n m :
      int_arith_binop_reduction PlusIntInt n m (n + m)
  | IABRMinusIntInt n m :
      int_arith_binop_reduction MinusIntInt n m (n - m)
  | IABRTimes n m :
      int_arith_binop_reduction Times n m (n * m)
  | IABRDiv n m :
      m <> 0%Z -> (* division and modulo by zero is undefined behavior *)
      int_arith_binop_reduction Div n m (Z.abs n / Z.abs m * Z.sgn n * Z.sgn n)
  | IABRMod n m :
      m <> 0%Z ->
      int_arith_binop_reduction Mod n m ((Z.abs n mod Z.abs m) * Z.sgn n * Z.sgn m).

Inductive comparison_reduction : comparison -> Z -> Z -> bool -> Prop :=
  | CRBEq n m : comparison_reduction Eq n m (n =? m)%Z
  | CRBLt n m : comparison_reduction Lt n m (n <? m)%Z.

Inductive binop_reduction : binop -> value -> value -> value -> Prop :=
  | BRIntArithBinop (op : int_arith_binop) (lhs rhs result : int_value) :
        int_arith_binop_reduction op (int_value_to_Z lhs)
                                     (int_value_to_Z rhs)
                                     (int_value_to_Z result) ->
      binop_reduction (IntArithBinop op) (IntValue lhs) (IntValue rhs) (IntValue result)

  | BRComparisonInt (comp : comparison) (lhs rhs : int_value) (result : bool) :
        comparison_reduction comp (int_value_to_Z lhs) (int_value_to_Z rhs) result ->
      binop_reduction (Comparison comp) (IntValue lhs) (IntValue rhs) (bool_to_value result)

  | BRComparisonPtr (comp : comparison) (lhs rhs : ptr_value) (lhs_offset rhs_offset : offset)
                    (result : bool) :
        has_offset lhs lhs_offset ->
        has_offset rhs rhs_offset ->
        same_block lhs rhs ->
        comparison_reduction comp lhs_offset rhs_offset result ->
      binop_reduction (Comparison comp) (PtrValue lhs) (PtrValue rhs) (bool_to_value result)

  | BRPlusPtrInt (lhs : ptr_value) (rhs : int_value) (result : ptr_value)
                 (lhs_offset result_offset : offset) :
        has_offset lhs lhs_offset ->
        has_offset result result_offset ->
        same_block lhs result ->
        lhs_offset + Z.of_nat word_size * int_value_to_Z rhs = result_offset ->
      binop_reduction PlusPtrInt (PtrValue lhs) (IntValue rhs) (PtrValue result)

  | BRPlusIntPtr (lhs : int_value) (rhs result : ptr_value) (rhs_offset result_offset : offset) :
        has_offset rhs rhs_offset ->
        has_offset result result_offset ->
        same_block rhs result ->
        Z.of_nat word_size * int_value_to_Z lhs + rhs_offset = result_offset ->
      binop_reduction PlusPtrInt (IntValue lhs) (PtrValue rhs) (PtrValue result)

  | BRMinusPtrInt (lhs : ptr_value) (rhs : int_value) (result : ptr_value)
                  (lhs_offset result_offset : offset) :
        has_offset lhs lhs_offset ->
        has_offset result result_offset ->
        same_block lhs result ->
        lhs_offset * Z.of_nat word_size * int_value_to_Z rhs = result_offset ->
      binop_reduction MinusPtrInt (PtrValue lhs) (IntValue rhs) (PtrValue result)

  | BRMinusPtrPtr (lhs rhs : ptr_value) (result : int_value) (lhs_offset rhs_offset : offset) :
        has_offset lhs lhs_offset ->
        has_offset rhs rhs_offset ->
        lhs_offset - rhs_offset = Z.of_nat word_size * int_value_to_Z result ->
      binop_reduction MinusPtrPtr (PtrValue lhs) (PtrValue rhs) (IntValue result).
        
Definition binop_reduction_goes_wrong (op : binop) (lhs rhs : value) : Prop :=
  ~exists result, binop_reduction op lhs rhs result.

Inductive short_circuit_reduction_first : short_circuit_op -> bool -> bool -> Prop :=
  | SCRFFalseAnd : short_circuit_reduction_first And false false
  | SCRFTrueOr   : short_circuit_reduction_first Or  true  true.

Inductive short_circuit_reduction_second : short_circuit_op -> bool -> bool -> bool -> Prop :=
  | SCRSTrueAnd (b : bool) : short_circuit_reduction_second And true  b b
  | SCRSFalseOr (b : bool) : short_circuit_reduction_second Or  false b b.

Definition to_plus_or_minus_one (iod : incr_or_decr) : Z :=
  match iod with
  | Incr => 1
  | Decr => -1
  end.

Inductive incr_or_decr_reduction : incr_or_decr -> rich_type -> value -> value -> Prop :=
  | IRInt (incr_or_decr : incr_or_decr) (before after : int_value) :
        (int_value_to_Z after = int_value_to_Z before + to_plus_or_minus_one incr_or_decr)%Z ->
      incr_or_decr_reduction incr_or_decr RInt
        (IntValue before)
        (IntValue after)

  | IRIncrPtr (incr_or_decr : incr_or_decr) (block_id : block_id) (offset : offset) (ty : rich_type) :
      incr_or_decr_reduction incr_or_decr (RPtr ty)
        (PtrValue (HeapPtr block_id offset))
        (PtrValue (HeapPtr block_id
                           (offset + Z.of_nat word_size * to_plus_or_minus_one incr_or_decr) % Z))

  | IRIncrBool : forall (b : bool),
      incr_or_decr_reduction Incr RBool
        (bool_to_value b)
        (bool_to_value true)

  | IRDecrBool : forall (b : bool),
      incr_or_decr_reduction Decr (RBool)
        (bool_to_value b)
        (bool_to_value (negb b)).

Section ExprHeadReduction.

Variable (var_ptrs : VarIdMap.t ptr_value).

Inductive expr_head_reduction : (memory * output) * annotated_expr ->
                                (memory * output) * annotated_expr -> Prop :=
                                
  | HRCast (state : memory * output) (val val' : value) (ty ty' : rich_type) :
        cast_reduction ty val ty' val' ->
      expr_head_reduction
        (state, Cast ty ty' (Const val <: ty) <: ty')
        (state, Const val' <: ty')

  | HRAddressOf (state : memory * output) (ptr : ptr_value) (ty : rich_type) :
      expr_head_reduction
        (state, AddressOf (Dereference (Const (PtrValue ptr) <: RPtr ty) <l: ty) <: RPtr ty)
        (state, Const (PtrValue ptr) <: RPtr ty)

  | HRBinOp (state : memory * output) (op : binop) (lhs rhs result : value)
            (lhs_ty rhs_ty result_ty : rich_type) :
        binop_reduction op lhs rhs result ->
      expr_head_reduction
        (state, BinOp op (Const lhs <: lhs_ty) (Const rhs <: rhs_ty) <: result_ty)
        (state, Const result <: result_ty)

  | HRShortCircuitFirst (state : memory * output) (op : short_circuit_op) (lhs : bool)
                        (rhs : annotated_expr) (result : bool) :
        short_circuit_reduction_first op lhs result ->
      expr_head_reduction
        (state, ShortCircuit op (Const (bool_to_value lhs) <: RBool) rhs <: RBool)
        (state, Const (bool_to_value result) <: RBool)

  | HRShortCircuitSecond (state : memory * output) (op : short_circuit_op) (lhs rhs result : bool) :
        short_circuit_reduction_second op lhs rhs result ->
      expr_head_reduction
        (state, ShortCircuit op (Const (bool_to_value lhs) <: RBool)
                                       (Const (bool_to_value rhs) <: RBool) <: RBool)
        (state, Const (bool_to_value result) <: RBool)

  | HRNot state (b : bool) :
      expr_head_reduction
        (state, Not (Const (bool_to_value b) <: RBool) <: RBool)
        (state, Const (bool_to_value (negb b)) <: RBool)

  | HRIncrOrDecr (mem mem' : memory) (out : output) (iod : incr_or_decr) (pop : pre_or_post)
                 (ptr : ptr_value) (before after : value) (ty : rich_type) :
        incr_or_decr_reduction iod ty before after ->
        read mem ptr before ->
        write mem ptr after mem' ->
      expr_head_reduction
        ((mem,  out), (IncrOrDecr ty iod pop
                                  (Dereference (Const (PtrValue ptr) <: RPtr ty) <l: ty)) <: ty)
        ((mem', out), Const (match pop with | Pre => after | Post => before end) <: ty)

  | HRAssign (mem mem' : memory) (out : output) (ptr : ptr_value) (val : value) (ty : rich_type) :
        write mem ptr val mem' ->
      expr_head_reduction
        ((mem,  out), (Assign (Dereference (Const (PtrValue ptr) <: RPtr ty) <l: ty)
                         (Const val <: ty) <: ty))
        ((mem', out), Const val <: ty)

  (* calls are not reduced here, they are reduced by continuation_step *)

  | HRInbuiltFunc (func : inbuilt_func) (mem mem' : memory) (out out' : output)
                  (args : list value) (arg_tys : list rich_type)
                  (returned : option value) (return_ty : rich_type) :
        inbuilt_func_step func args returned mem out mem' out' ->
        length args = length arg_tys ->
      expr_head_reduction
        ((mem,  out),  CallInbuilt func
                          (list_to_list_annotated_expr
                            (map (fun '(val, ty) => Const val <: ty)
                                 (combine args arg_tys)))
                          <: return_ty)
        ((mem', out'), (match returned with
                           | Some val => Const val
                           | None     => Unit end)
                          <: return_ty)

  | HRVar (state : memory * output) (var_id : var_id) (ptr : ptr_value) (ty : rich_type) :
        VarIdMap.find var_id var_ptrs = Some ptr ->
      expr_head_reduction
        (state, LValue (Var var_id <l: ty) <: ty)
        (state, LValue (Dereference (Const (PtrValue ptr) <: RPtr ty) <l: ty) <: ty).

End ExprHeadReduction.

(* Inductive expr_head_reduction_goes_wrong : memory * output * annotated_expr -> Prop :=
  | HRWBinop : forall state op lhs_val lhs_ty rhs_val rhs_ty result_ty,
        binop_reduction_goes_wrong op lhs_ty lhs_val rhs_ty rhs_val ->
      expr_head_reduction_goes_wrong
        (state, BinOp op (Const lhs_val <: lhs_ty) (Const rhs_val <: rhs_ty) <: result_ty)
        
  | HRWAssign : forall state value value ty,
        write_mem_goes_wrong state value ->
      expr_head_reduction_goes_wrong
        (state,  (Assign (Dereference (Const (PtrValue value) <: RPtr ty) <l: ty)
                         (Const value <: ty) <: ty)). *)


Inductive continuation_after_cmd : Type :=
  | KStop
      (* do the command, then stop *)
  | KSeq (c : cmd) (k : continuation_after_cmd)
      (* do the command, then do [i], then do [k] *)
  | KWhileAfterCmd (e : annotated_expr) (c : cmd) (k : continuation_after_cmd)
      (* do the command as if in the body of the while, then do [while (e) { c }],
         then do [k] *)
  | KCall (ctx : annotated_expr -> annotated_expr)
          (caller_var_ptrs : VarIdMap.t ptr_value)
          (k : continuation_after_expr)
      (* reduce the command until its [return const],
         then do [ContinuedExpr (ctx const) k] *)
  
with continuation_after_expr : Type :=
  | KExpr (k : continuation_after_cmd)
      (* evaluate the expression, discard its result, then do [k] *)
  | KIf (c_then c_else : cmd) (k : continuation_after_cmd)
      (* evaluate the expression,
         do [c_then] if it evaluates to true or [c_else] if it evaluates to false,
         then do [k] *)
  | KWhileAfterExpr (e : annotated_expr) (c : cmd) (k : continuation_after_cmd)
      (* evaluate the expression,
         do [while (e) { c }] without evaluating the conditing for the first time
                              using the result of the expression instead,
         then do [k] *).

Inductive continued : Type :=
  | ContinuedExpr : annotated_expr -> continuation_after_expr -> continued
  | ContinuedCmd : cmd -> continuation_after_cmd -> continued.

Section ContinuedStep.

Variable (funcs : list (func_id * func)).

Inductive continued_step : VarIdMap.t ptr_value * (memory * output) * continued ->
                           VarIdMap.t ptr_value * (memory * output) * continued -> Prop :=
  
  | CSSkipSeq var_ptrs state cmd cont :
      continued_step
        (var_ptrs, state,  ContinuedCmd Skip (KSeq cmd cont))
        (var_ptrs, state,  ContinuedCmd cmd cont)
      
  | CSSkipWhileAfterCmd var_ptrs state expr cmd cont :
      continued_step
        (var_ptrs, state,  ContinuedCmd Skip (KWhileAfterCmd expr cmd cont))
        (var_ptrs, state,  ContinuedCmd Skip (KSeq (While expr cmd) cont))
    
  | CSSeq var_ptrs state cmd1 cmd2 cont :
      continued_step
        (var_ptrs, state,  ContinuedCmd (Seq cmd1 cmd2) cont)
        (var_ptrs, state,  ContinuedCmd cmd1 (KSeq cmd2 cont))
        
  | CSExpr var_ptrs state expr cont :
      continued_step
        (var_ptrs, state,  ContinuedCmd (Expr expr) cont)
        (var_ptrs, state,  ContinuedExpr expr (KExpr cont))
        
  | CSIf var_ptrs state expr cmd_then cmd_else cont :
      continued_step
        (var_ptrs, state,  ContinuedCmd (If expr cmd_then cmd_else) cont)
        (var_ptrs, state,  ContinuedExpr expr (KIf cmd_then cmd_else cont))

  | CSWhile var_ptrs state expr cmd cont :
      continued_step
        (var_ptrs, state,  ContinuedCmd (While expr cmd) cont)
        (var_ptrs, state,  ContinuedExpr expr (KWhileAfterExpr expr cmd cont))
        
  | CSBreakSeq var_ptrs state cmd cont :
      continued_step
        (var_ptrs, state,  ContinuedCmd Break (KSeq cmd cont))
        (var_ptrs, state,  ContinuedCmd Break cont)

  | CSBreakWhile var_ptrs state expr cmd cont :
      continued_step
        (var_ptrs, state,  ContinuedCmd Break (KWhileAfterCmd expr cmd cont))
        (var_ptrs, state,  ContinuedCmd Skip cont)
        
  | CSContinueSeq var_ptrs state cmd cont :
      continued_step
        (var_ptrs, state,  ContinuedCmd Continue (KSeq cmd cont))
        (var_ptrs, state,  ContinuedCmd Continue cont)
        
  | CSContinueWhile var_ptrs state expr cmd cont :
      continued_step
        (var_ptrs, state,  ContinuedCmd Continue (KWhileAfterCmd expr cmd cont))
        (var_ptrs, state,  ContinuedCmd (While expr cmd) cont)
        
      (* we capitalize the E and R at the end of calle and caller so they are harder to confuse *)
  | CSReturn var_ptrs_calleE var_ptrs_calleR state val ty ctx cont :
      continued_step
        (var_ptrs_calleE, state, ContinuedCmd (Return (Const val <: ty))
                                                     (KCall ctx var_ptrs_calleR cont))
        (var_ptrs_calleR, state, ContinuedExpr (ctx (Const val <: ty)) cont)
        
  | CSExprConst var_ptrs state val ty cont :
      continued_step
        (var_ptrs, state,  ContinuedExpr (Const val <: ty) (KExpr cont))
        (var_ptrs, state,  ContinuedCmd Skip cont)

  | CSExprIf var_ptrs state bool cmd_then cmd_else cont :
      continued_step
        (var_ptrs, state,  ContinuedExpr (Const (bool_to_value bool) <: RBool)
                                              (KIf cmd_then cmd_else cont))
        (var_ptrs, state,  ContinuedCmd (if bool then cmd_then else cmd_else) cont)
  
  | CSExprWhile var_ptrs state bool expr cmd cont :
      continued_step
        (var_ptrs, state,  ContinuedExpr  (Const (bool_to_value bool) <: RBool)
                                               (KWhileAfterExpr expr cmd cont))
        (var_ptrs, state,  if bool
                                then ContinuedCmd cmd (KWhileAfterCmd expr cmd cont)
                                else ContinuedCmd Skip cont)

  | CSExprHeadReduction var_ptrs state state' ctx expr expr' cont :
        expr_context ctx ->
        expr_head_reduction var_ptrs (state, expr) (state', expr') ->
      continued_step
        (var_ptrs, state,  ContinuedExpr (ctx expr) cont)
        (var_ptrs, state', ContinuedExpr (ctx expr') cont)

      (* we capitalize the E and R at the end of calle and caller so they are harder to confuse *)
  | CSExprCall var_ptrs_calleE var_ptrs_calleR mem mem' out func func_id arg_vals ctx cont :
        assoc func_id funcs = Some func ->
        expr_context ctx ->
        let sig := f_signature func in
        length arg_vals = length (fs_arg_rich_types sig) ->
        let arg_exprs := list_to_list_annotated_expr
          (map (fun '(val, ty) => Const val <: ty)
               (combine arg_vals (fs_arg_rich_types sig))) in
        let call_expr := (Call func_id arg_exprs <: fs_rich_return_type sig) in
        call_var_ptrs_and_mem var_ptrs_calleR mem (f_arg_var_ids func) arg_vals
                              var_ptrs_calleE mem' ->
      continued_step
        (var_ptrs_calleR, (mem,  out),  ContinuedExpr (ctx call_expr) cont)
        (var_ptrs_calleE, (mem', out), ContinuedCmd (f_body func)
                                                      (KCall ctx var_ptrs_calleR cont)).

End ContinuedStep.

(* Inductive continued_step_goes_wrong : IdMap.t value * state * continued -> Prop :=
  | CSWExprHeadReduction : forall var_ptrs state ctx expr cont,
        expr_context ctx ->
        expr_head_reduction_goes_wrong (state, expr) ->
      continued_step_goes_wrong
        (var_ptrs, state,  ContinuedExpr (ctx expr) cont). *)
