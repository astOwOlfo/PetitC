From PetitC Require Import Values InbuiltFunc Ids.

From Coq Require Import Lists.List.
Import ListNotations.

Module TypedTree.

Inductive rich_type : Set :=
  | RInt
  | RBool
  | RPtr : rich_type -> rich_type
  | RVoid.

Definition of_rich (ty : rich_type) : option type :=
  match ty with
  | RInt   => Some Int
  | RBool  => Some Bool
  | RPtr _ => Some Ptr
  | RVoid  => None
  end.

Definition to_rich (ty : type) : rich_type :=
  match ty with
  | Int  => RInt
  | Bool => RBool
  | Ptr  => RPtr RVoid
  end.

Record func_signature : Set := {
  fs_rich_return_type : rich_type;
  fs_arg_rich_types : list rich_type
}.

Record env : Type := {
  env_var_types : VarIdMap.t rich_type;
  env_func_signatures : FuncIdMap.t func_signature
}.

Inductive int_arith_binop := PlusIntInt | MinusIntInt | Times | Div | Mod.
Inductive comparison := Eq | Lt.
Inductive binop :=
  | IntArithBinop : int_arith_binop -> binop
  | Comparison : comparison -> binop
  | PlusPtrInt
  | PlusIntPtr
  | MinusPtrInt
  | MinusPtrPtr.

Inductive short_circuit_op : Set := And | Or.

Inductive incr_or_decr := Incr | Decr.
Inductive pre_or_post := Pre | Post.

Definition inbuilt_func_signature (func : inbuilt_func) : func_signature :=
  match func with
  | Malloc  => {| fs_rich_return_type := RPtr RVoid;
                  fs_arg_rich_types   := [RInt] |}
  | Putchar => {| fs_rich_return_type := RVoid;
                  fs_arg_rich_types   := [RInt] |}
  end.

Inductive annotated_expr : Set :=
  | AnnotatedExpr : expr -> rich_type -> annotated_expr

with annotated_lvalue : Set :=
  | AnnotatedLvalue : lvalue -> rich_type -> annotated_lvalue

with expr : Set :=
  | Const : value -> expr
  | Unit : expr
  | Cast : rich_type -> rich_type -> annotated_expr -> expr
  | LValue : annotated_lvalue -> expr
  | AddressOf : annotated_lvalue -> expr
  | BinOp : binop -> annotated_expr -> annotated_expr -> expr
  | ShortCircuit : short_circuit_op -> annotated_expr -> annotated_expr -> expr
  | Not : annotated_expr -> expr
  | IncrOrDecr : rich_type -> incr_or_decr -> pre_or_post -> annotated_lvalue -> expr
  | Assign : annotated_lvalue -> annotated_expr -> expr
  | Call : func_id -> list_annotated_expr -> expr
  | CallInbuilt : inbuilt_func -> list_annotated_expr -> expr

with list_annotated_expr : Set :=
  | LAENil : list_annotated_expr
  | LAECons : annotated_expr -> list_annotated_expr -> list_annotated_expr
  
with lvalue : Set :=
  | Dereference : annotated_expr -> lvalue
  | Var : var_id -> lvalue.

Fixpoint list_annotated_expr_to_list (exprs : list_annotated_expr) : list annotated_expr :=
  match exprs with
  | LAENil            => []
  | LAECons head tail => head :: list_annotated_expr_to_list tail
  end.

Fixpoint list_to_list_annotated_expr (exprs : list annotated_expr) : list_annotated_expr :=
  match exprs with
  | []         => LAENil
  | head::tail => LAECons head (list_to_list_annotated_expr tail)
  end.

Lemma list_annotated_expr_to_list_injective : forall lae lae',
    list_annotated_expr_to_list lae = list_annotated_expr_to_list lae' ->
  lae = lae'.
Proof.
  intro lae. induction lae; intros;
  destruct lae'; try discriminate.
  - reflexivity.
  - injection H. intros. subst.
    f_equal. apply IHlae. assumption.
Qed.

Lemma list_to_list_annotated_expr_injective : forall l l',
    list_to_list_annotated_expr l = list_to_list_annotated_expr l' ->
  l = l'.
Proof.
  intro l. induction l; intros;
  destruct l'; try discriminate.
  - reflexivity.
  - injection H. intros. subst.
    f_equal. apply IHl. assumption.
Qed.

Notation "E '<:' T" := (AnnotatedExpr E T)
  (at level 70, no associativity).
Notation "E '<l:' T" := (AnnotatedLvalue E T)
  (at level 70, no associativity).

Inductive cmd : Set :=
  | Skip : cmd
  | Seq : cmd -> cmd -> cmd
  | Expr : annotated_expr -> cmd
  | If : annotated_expr -> cmd -> cmd -> cmd
  | While : annotated_expr -> cmd -> cmd
  | For : annotated_expr -> list_annotated_expr -> cmd -> cmd (* no declaration *)
  | Break : cmd
  | Continue : cmd
  | Return : annotated_expr -> cmd.

Record func : Set := {
  f_signature : func_signature;
  f_local_var_ids : list var_id;
  f_local_var_types : list rich_type;
  f_arg_var_ids : list var_id;
  f_body : cmd;
  f_parent_func_ids : list func_id
}.

Inductive can_cast : rich_type -> rich_type -> Prop :=
  | CCSame :      forall ty,      can_cast ty ty
  | CCIntToBool :                 can_cast RInt RBool
  | CCBoolToInt :                 can_cast RBool RInt
  | CCPtrToBool : forall ty,      can_cast (RPtr ty) RBool
  | CCPtrToPtr :  forall ty1 ty2, can_cast (RPtr ty1) (RPtr ty2).

Inductive can_subtract_ptrs_to : rich_type -> rich_type -> Prop :=
  | CSPTSame : forall ty,     can_subtract_ptrs_to ty        ty
  | CSPTPtr :  forall ty ty', can_subtract_ptrs_to (RPtr ty) (RPtr ty').

Inductive binop_well_typed : binop -> rich_type -> rich_type -> rich_type -> Prop :=
  | BWTIntArithBinop : forall op,
      binop_well_typed (IntArithBinop op) RInt RInt RInt
  | BWTComparisonIntInt : forall comp,
      binop_well_typed (Comparison comp) RInt RInt RBool
  | BWTComparisonPtrPtr : forall comp ty ty',
      binop_well_typed (Comparison comp) (RPtr ty) (RPtr ty') RBool
  | BWTPlusPtrInt : forall ty,
      binop_well_typed PlusPtrInt (RPtr ty) RInt (RPtr ty)
  | BWTPlusIntPtr : forall ty,
      binop_well_typed PlusIntPtr RInt (RPtr ty) (RPtr ty)
  | BWTMinusPtrInt : forall ty,
      binop_well_typed MinusPtrInt (RPtr ty) RInt (RPtr ty)
  | BWTMinusPtrPtr : forall ty ty', can_subtract_ptrs_to ty ty' ->
      binop_well_typed MinusPtrPtr (RPtr ty) (RPtr ty') RInt.

Section ExprWellTyped.

Variable (environment : env).

Inductive expr_well_typed : annotated_expr -> Prop :=
  | EWTConst : forall val ty,
        can_have_type val ty ->
      expr_well_typed (Const val <: to_rich ty)
  | AEWUnit :
      expr_well_typed (Unit <: RVoid)
  | EWTCast : forall expr ty_from ty_to,
        can_cast ty_from ty_to ->
      expr_well_typed (Cast ty_from ty_to expr <: ty_to)
  | EWTLvalue : forall lvalue ty,
        lvalue_well_typed (lvalue <l: ty) ->
      expr_well_typed (LValue (lvalue <l: ty) <: ty)
  | EWTAddressOf : forall lvalue ty,
        lvalue_well_typed (lvalue <l: ty) ->
      expr_well_typed (AddressOf (lvalue <l: ty) <: RPtr ty)
  | EWTBinOp : forall binop lhs_expr lhs_ty rhs_expr rhs_ty result_ty,
        binop_well_typed binop lhs_ty rhs_ty result_ty ->
        expr_well_typed (lhs_expr <: lhs_ty) ->
        expr_well_typed (rhs_expr <: rhs_ty) ->
      expr_well_typed (BinOp binop (lhs_expr <: lhs_ty) (rhs_expr <: rhs_ty) <: result_ty)
  | EWTShortCircuit : forall short_circuit_op lhs_expr rhs_expr,
        expr_well_typed (lhs_expr <: RBool) ->
        expr_well_typed (rhs_expr <: RBool) ->
      expr_well_typed (ShortCircuit short_circuit_op (lhs_expr <: RBool) (rhs_expr <: RBool) <: RBool)
  | EWTNot : forall expr,
        expr_well_typed (expr <: RBool) ->
      expr_well_typed (Not (expr <: RBool) <: RBool)
  | EWTIncrOrDecr : forall incr_or_decr pre_or_post lvalue ty, ty <> RVoid ->
        lvalue_well_typed (lvalue <l: ty) ->
      expr_well_typed
        (IncrOrDecr ty incr_or_decr pre_or_post (lvalue <l: ty) <: ty)
  | EWTAssign : forall lvalue expr ty, ty <> RVoid ->
        lvalue_well_typed (lvalue <l: ty) ->
        expr_well_typed (expr <: ty) ->
      expr_well_typed (Assign (lvalue <l: ty) (expr <: ty)
                                <: ty)
  | EWTCall : forall func_id signature args,
        FuncIdMap.find func_id (env_func_signatures environment) = Some signature ->
        list_expr_well_typed args ->
        Forall2 (fun '(_ <: ty') ty => ty' = ty)
                (list_annotated_expr_to_list args) (fs_arg_rich_types signature) ->
      expr_well_typed (Call func_id args <: fs_rich_return_type signature)
  | EWTCallInbuilt : forall inbuilt_func args,
        list_expr_well_typed args ->
        Forall2 (fun '(_ <: ty') ty => ty' = ty)
                (list_annotated_expr_to_list args)
                (fs_arg_rich_types (inbuilt_func_signature inbuilt_func)) ->
      expr_well_typed (CallInbuilt inbuilt_func args <:
                                fs_rich_return_type (inbuilt_func_signature inbuilt_func))

with lvalue_well_typed : annotated_lvalue -> Prop :=
  | LWTVar : forall var_id ty,
        VarIdMap.find var_id (env_var_types environment) = Some ty ->
      lvalue_well_typed (Var var_id <l: ty)
  | LWTDereference : forall expr ty,
        expr_well_typed (expr <: RPtr (ty)) ->
      lvalue_well_typed (Dereference (expr <: RPtr (ty)) <l: ty)

with list_expr_well_typed : list_annotated_expr -> Prop :=
  | LEWTNil :
      list_expr_well_typed LAENil
  | LEWTCons : forall head tail,
        expr_well_typed head ->
        list_expr_well_typed tail ->
      list_expr_well_typed (LAECons head tail).

End ExprWellTyped.

Inductive in_loop : Set := InLoop | NotInLoop.

Section CmdWellTyped.

Variables (environment : env) (return_type : rich_type).

Inductive cmd_well_typed : in_loop -> cmd -> Prop :=
  | IWTSkip : forall in_loop,
      cmd_well_typed in_loop Skip
  | IWTSeq : forall in_loop cmd1 cmd2,
        cmd_well_typed in_loop cmd1 ->
        cmd_well_typed in_loop cmd2 ->
      cmd_well_typed in_loop (Seq cmd1 cmd2)
  | IWTExpr : forall in_loop expr,
        expr_well_typed environment expr ->
      cmd_well_typed in_loop (Expr expr)
  | IWTIf : forall in_loop condition then_body else_body,
        expr_well_typed environment (condition <: RBool) ->
        cmd_well_typed in_loop then_body ->
        cmd_well_typed in_loop else_body ->
      cmd_well_typed in_loop (If (condition <: RBool) then_body else_body)
  | IWTWhile : forall in_loop condition body,
        expr_well_typed environment (condition <: RBool) ->
        cmd_well_typed in_loop body ->
      cmd_well_typed in_loop (While (condition <: RBool) body)
  | IWTFor : forall in_loop condition increments body,
        expr_well_typed environment (condition <: RBool) ->
        Forall (expr_well_typed environment) (list_annotated_expr_to_list increments) ->
        cmd_well_typed InLoop body ->
      cmd_well_typed in_loop (For (condition <: RBool) increments body)
  | IWTBreak :
      cmd_well_typed InLoop Break
  | IWTContinue :
      cmd_well_typed InLoop Continue
  | IWTReturn : forall in_loop expr,
        expr_well_typed environment (expr <: return_type) ->
      cmd_well_typed in_loop (Return (expr <: return_type)).

End CmdWellTyped.

End TypedTree.
