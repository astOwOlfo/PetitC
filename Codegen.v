From PetitC Require Import TypedTree Asm Memory Values Ids Monad.
Import TypedTree. (* why do I need to do this import? all names in TypedTree.v are on top level *)

From Coq Require Import Lists.List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition label_counter : Set := label.

Definition init_label_counter : label_counter := 0%nat.

Definition fresh_label_no_option : state label_counter label :=
  lbl_counter <- get;;
  put (S lbl_counter);;
  ret (lbl_counter).

Definition fresh_label : state_option label_counter label :=
  lbl <- fresh_label_no_option;;
  ret (Some lbl).

Fixpoint compile_parent_var_address (rbp_offset : offset) (depth_minus_one : nat)
                                      (tail_asm : asm) : asm :=
  match depth_minus_one with
  | O                 => Leaq (Offset Rax rbp_offset) (Reg Rax) ::
                         tail_asm
  | S depth_minus_two => Movq (Offset Rax (Z.of_nat (2 * word_size))) (Reg Rax) ::
                         compile_parent_var_address rbp_offset depth_minus_two tail_asm
  end.

Definition compile_var_address (rbp_offset : offset) (depth : nat) (tail_asm : asm) : asm :=
  match depth with
  | O        => Leaq (Offset Rbp rbp_offset) (Reg Rax) ::
                tail_asm
  | S depth' => Movq (Offset Rbp (2 * Z.of_nat word_size)) (Reg Rax) ::
                compile_parent_var_address rbp_offset depth' tail_asm
  end.

  (* E and R in calleR and calleE are capitalize so they are less easy to confuse *)
Fixpoint compile_parent_rbp_callE_not_deeper_than_calleR
                (calleR_depth_minus_calleE_depth : nat) (tail_asm : asm) : asm :=
  match calleR_depth_minus_calleE_depth with
  | O   => Movq (Offset Rbp (2 * Z.of_nat word_size)) (Reg Rax) ::
           tail_asm
  | S d => compile_parent_rbp_callE_not_deeper_than_calleR d
           ( Movq (Offset Rax (2 * Z.of_nat word_size)) (Reg Rax) ::
             tail_asm )
  end.

  (* E and R in calleR and calleE are capitalize so they are less easy to confuse *)
Definition compile_parent_rbp (calleR_depth calleE_depth : nat) (tail_asm : asm) : asm :=
  if (calleR_depth <? calleE_depth)%nat
  then Movq (Reg Rbp) (Reg Rax) ::
       tail_asm
  else compile_parent_rbp_callE_not_deeper_than_calleR (calleR_depth - calleE_depth) tail_asm.

Definition log2_word_size : nat := 3.

Lemma word_size_log2_word_size : word_size = (2 ^ log2_word_size)%nat.
Proof. unfold word_size. unfold log2_word_size. reflexivity. Qed.

Definition compile_binop_rax_rbx (op : binop) : asm :=
  match op with
  | IntArithBinop PlusIntInt  => [ Addq  (Reg Rbx) (Reg Rax) ]
  
  | IntArithBinop MinusIntInt => [ Subq  (Reg Rbx) (Reg Rax) ]

  | IntArithBinop Times       => [ Imulq (Reg Rbx) ]

  | IntArithBinop Div         => [ Subq  (Reg Rdx) (Reg Rdx);
                                   Idivq (Reg Rbx) ]

  | IntArithBinop Mod         => [ Subq  (Reg Rdx) (Reg Rdx);
                                   Idivq (Reg Rbx);
                                   Movq  (Reg Rdx) (Reg Rax) ]

  | Comparison comp           => [ Movq  (Reg Rax) (Reg Rdx);
                                   Subq  (Reg Rax) (Reg Rax);
                                   Cmpq  (Reg Rbx) (Reg Rdx);
                                   SetL  (match comp with
                                          | Eq => Zero
                                          | Lt => StrictlyNegative end)
                                          (Reg Rax) ]
                                  (* there might be some problems for Lt when operands are int_max or int_min *)

  | PlusPtrInt                => [ Salq  log2_word_size (Reg Rbx);
                                   Addq  (Reg Rbx) (Reg Rax) ]

  | PlusIntPtr                => [ Salq  log2_word_size (Reg Rax);
                                   Addq  (Reg Rbx) (Reg Rax) ]

  | MinusPtrInt               => [ Salq  log2_word_size (Reg Rbx);
                                   Subq  (Reg Rbx) (Reg Rax) ]

  | MinusPtrPtr               => [ Subq  (Reg Rbx) (Reg Rax);
                                   Sarq  log2_word_size (Reg Rax) ]
  end.

Definition compile_incr_or_decr (ty : rich_type) (incr_or_decr : incr_or_decr) : asm :=
  match ty, incr_or_decr with
  | RInt,   Incr => [ Incrq (Mem Rax) ]
  | RInt,   Decr => [ Decrq (Mem Rax) ]
  | RBool,  Incr => [ Movq  (ConstInt 1) (Mem Rax) ]
  | RBool,  Decr => [ Subq  (Reg Rbx) (Reg Rbx);
                     Cmpq   (Mem Rax) (Reg Rbx);
                     SetL   Zero (Reg Rbx);
                     Movq   (Reg Rbx) (Mem Rax) ]
  | RPtr _, Incr => [ Addq  (ConstInt (Z.of_nat word_size)) (Mem Rax) ]
  | RPtr _, Decr => [ Subq  (ConstInt (Z.of_nat word_size)) (Mem Rax) ]
  | RVoid,  _    => [] (* unreachable when compiling a well typed asmram *)
  end.

Section Compile.

Variables (func_depths : FuncIdMap.t nat)
          (depth : nat)
          (var_rbp_offsets : VarIdMap.t offset)
          (var_depths : VarIdMap.t nat).

Definition get_func_depth (id : func_id) : state_option label_counter nat :=
  ret (FuncIdMap.find id func_depths).
Definition get_var_rbp_offset (id : var_id) : state_option label_counter offset :=
  ret (VarIdMap.find id var_rbp_offsets).
Definition get_var_depth (id : var_id) : state_option label_counter nat :=
  ret (VarIdMap.find id var_depths).

Fixpoint compile_expr (expr : annotated_expr) (tail_asm : asm) :
                      state_option label_counter asm :=
  match expr with
  | Const (IntValue val) <: _ =>
      ret (Movq (ConstInt (int_value_to_Z val)) (Reg Rax) :: tail_asm)

  | Const (PtrValue NullPtr) <: _ =>
      ret (Movq ConstNullPtr (Reg Rax) :: tail_asm)

  | Unit <: RVoid =>
      ret tail_asm

  | Cast RInt RInt expr1 <: _
  | Cast RBool (RBool | RInt) expr1 <: _
  | Cast (RPtr _) (RPtr _) expr1 <: RPtr _ =>
      compile_expr expr1 tail_asm

  | Cast (RInt | RPtr _) RBool expr1 <: _ =>
      compile_expr expr1
        (Movq  (Reg Rax) (Reg Rbx) ::
         Subq  (Reg Rax) (Reg Rax) ::
         Andq  (Reg Rbx) (Reg Rbx) ::
         SetL  NotZero (Reg Rax) ::
         tail_asm)

  | LValue lval <: _ =>
      compile_lvalue_address lval
        (Movq (Mem Rax) (Reg Rax) ::
         tail_asm)

  | AddressOf lval <: _ =>
      compile_lvalue_address lval tail_asm
    
  | BinOp op lhs_expr rhs_expr <: _ =>
      tail <- compile_expr rhs_expr
                ( Movq (Reg Rax) (Reg Rbx) ::
                  Popq (Reg Rax) ::
                  compile_binop_rax_rbx op ++
                  tail_asm );;
      compile_expr lhs_expr
        ( Pushq (Reg Rax) ::
          tail )

  | ShortCircuit op lhs_expr rhs_expr <: _ =>
      exit_lbl <- fresh_label;;
      tail <- compile_expr rhs_expr
                ( Label exit_lbl ::
                  tail_asm );;
      compile_expr lhs_expr 
        ( Andq (Reg Rax) (Reg Rax) ::
          Jcc  (match op with And => Zero | Or => NotZero end) exit_lbl ::
          tail )

  | Not expr1 <: _ =>
      compile_expr expr1
        ( Andq  (Reg Rax) (Reg Rax) ::
          SetL Zero (Reg Rax) ::
          tail_asm)

  | IncrOrDecr ty incr_or_decr Pre lval <: _ =>
      compile_lvalue_address lval
        ( compile_incr_or_decr ty incr_or_decr ++
          Movq (Mem Rax) (Reg Rax) ::
          tail_asm )
      
  | IncrOrDecr ty incr_or_decr Post lval <: _ =>
      compile_lvalue_address lval
        ( Movq (Mem Rax) (Reg Rdx) ::
          compile_incr_or_decr ty incr_or_decr ++
          Movq (Reg Rdx) (Reg Rax) ::
          tail_asm )

  | Assign lval expr1 <: _ =>
      tail <- compile_expr expr1
                ( Popq (Reg Rbx) ::
                  Movq (Reg Rax) (Mem Rbx) ::
                  tail_asm );;
      compile_lvalue_address lval
        ( Pushq (Reg Rax) ::
          tail )

  | Call func_id args <: _ =>
      calleE_depth <- get_func_depth func_id;;
      let nb_pushed := (Z.of_nat (word_size * (1 + length (list_annotated_expr_to_list args)))) in
      compile_push_list_expr args
        ( compile_parent_rbp depth calleE_depth
            ( Pushq (Reg Rax) ::
              ICall func_id ::
              Addq (ConstInt nb_pushed) (Reg Rsp) ::
              tail_asm ))

  | CallInbuilt inbuilt_func args <: _ =>
      let nb_pushed := (Z.of_nat (word_size * (length (list_annotated_expr_to_list args)))) in
      compile_push_list_expr args
      ( ICallInbuilt inbuilt_func ::
        Addq (ConstInt nb_pushed) (Reg Rsp) ::
        tail_asm )

  | _ => ret_None
  end
  
with compile_lvalue_address (lval : annotated_lvalue) (tail_asm : asm) :
                            state_option label_counter asm :=
  match lval with
  | Dereference expr1 <l: _ =>
      compile_expr expr1 tail_asm

  | Var var_id <l: _ =>
      rbp_offset <- get_var_rbp_offset var_id;;
      var_depth <- get_var_depth var_id;;
      ret (compile_var_address rbp_offset (depth - var_depth) tail_asm)
  end
  
with compile_push_list_expr (exprs : list_annotated_expr) (tail_asm : asm) :
                            state_option label_counter asm :=
  match exprs with
  | LAENil =>
      ret tail_asm

  | LAECons head_expr tail_exprs =>
      tail <- compile_push_list_expr tail_exprs tail_asm;;
      compile_expr head_expr
        ( Pushq (Reg Rax) ::
          tail )
  end.

Fixpoint compile_ignore_list_expr (exprs : list_annotated_expr) (tail_asm : asm) :
                                    state_option label_counter asm :=
  match exprs with
  | LAENil =>
      ret tail_asm
    
  | LAECons head_expr tail_exprs =>
      tail <- compile_ignore_list_expr tail_exprs tail_asm;;
      compile_expr head_expr tail
  end.

Fixpoint compile_cmd (break_lbl continue_lbl : label) (cmd : cmd) (tail_asm : asm) :
                        state_option label_counter asm :=
  match cmd with
  | Skip =>
      ret tail_asm
    
  | Seq cmd1 cmd2 =>
      tail <- compile_cmd break_lbl continue_lbl cmd2 tail_asm;;
      compile_cmd break_lbl continue_lbl cmd1 tail
    
  | Expr expr =>
      compile_expr expr tail_asm

  | If cond_expr then_cmd else_cmd =>
      else_lbl <- fresh_label;;
      exit_lbl <- fresh_label;;
      tail <- compile_cmd break_lbl continue_lbl else_cmd
                ( Label exit_lbl ::
                  tail_asm);;
      tail' <- compile_cmd break_lbl continue_lbl then_cmd
                 ( Jmp exit_lbl ::
                   Label else_lbl ::
                   tail );;
      compile_expr cond_expr
        ( Andq (Reg Rax) (Reg Rax) ::
          Jcc Zero else_lbl ::
          tail' )

  | While cond_expr body_cmd =>
      cond_lbl <- fresh_label;;
      exit_lbl <- fresh_label;;
      tail   <- compile_cmd exit_lbl cond_lbl body_cmd
                  ( Jmp cond_lbl ::
                    Label exit_lbl ::
                    tail_asm );;
      tail'  <- compile_expr cond_expr
                  ( Andq (Reg Rax) (Reg Rax) ::
                    Jcc Zero exit_lbl ::
                    tail );;
      ret ( Label cond_lbl ::
            tail' )

  | For cond_expr incr_list_expr body_cmd =>
      cond_lbl <- fresh_label;;
      incr_lbl <- fresh_label;;
      exit_lbl <- fresh_label;;
      tail   <- compile_ignore_list_expr incr_list_expr
                  ( Jmp cond_lbl ::
                    Label exit_lbl ::
                    tail_asm );;
      tail'  <- compile_cmd exit_lbl incr_lbl body_cmd
                  ( Label incr_lbl ::
                    tail );;
      tail'' <- compile_expr cond_expr
                  ( Jcc Zero exit_lbl ::
                    tail' );;
      ret ( Label cond_lbl ::
            tail'' )

  | Break =>
      ret ( Jmp break_lbl ::
            tail_asm )

  | Continue =>
      ret ( Jmp continue_lbl ::
            tail_asm )

  | Return expr =>
      compile_expr expr
        ( Movq (Reg Rbp) (Reg Rsp) ::
          Popq (Reg Rbp) ::
          Ret ::
          tail_asm )
  end.

Definition compile_func (body : cmd) (local_var_rbp_offsets : VarIdMap.t offset) : option asm :=
  match compile_cmd 0%nat 0%nat body [] init_label_counter with
  | (None, _) => None
  | (Some tail, _) =>
    let vars_on_stack_size := VarIdMap.fold (fun _ => Z.min) local_var_rbp_offsets 0 in
    Some ( Pushq (Reg Rbp) ::
          Movq  (Reg Rsp) (Reg Rbp) ::
          Subq  (ConstInt (-vars_on_stack_size)) (Reg Rsp) ::
          tail )
  end.

End Compile.

Definition depth (func : func) : nat :=
  length (f_parent_func_ids func).

Fixpoint func_depths (funcs : list (func_id * func)) : FuncIdMap.t nat :=
  match funcs with
  | (id, func)::tail => FuncIdMap.add id (depth func) (func_depths tail)
  | []               => FuncIdMap.empty _
  end.

Fixpoint enumuerate_start {T : Type} (first_index : nat) (l : list T) : list (nat * T) :=
  match l with
  | x::xs => (first_index, x) :: enumuerate_start (S first_index) xs
  | []    => []
  end.

Definition enumerate {T : Type} : list T -> list (nat * T) :=
  enumuerate_start 0.

Fixpoint VarIdMap_add_list {T : Type} (l : list (var_id * T)) (m: VarIdMap.t T) : VarIdMap.t T :=
  match l with
  | (id, x)::tail => VarIdMap_add_list tail (VarIdMap.add id x m)
  | []            => m
  end.

Fixpoint mem (y : var_id) (xs : list var_id) : bool :=
  match xs with
  | x::xs => if (x =? y)%nat then true else mem y xs
  | []    => false
  end.

Definition var_rbp_offsets_of_func (func : func) (tail_var_rbp_offsets : VarIdMap.t offset) :
                                   VarIdMap.t offset :=
  let arg_rbp_offsets   := map (fun '(i, var_id) => (var_id, Z.of_nat (word_size * (i + 3))))
                               (enumerate (rev (f_arg_var_ids func))) in
  let local_rbp_offsets := map (fun '(i, var_id) => (var_id, - Z.of_nat (word_size * (i + 1))))
                               (enumerate (filter
                                            (fun id => negb (mem id (f_arg_var_ids func)))
                                            (f_local_var_ids func))) in
  VarIdMap_add_list (arg_rbp_offsets ++ local_rbp_offsets) tail_var_rbp_offsets.

Fixpoint var_rbp_offsets (funcs : list (func_id * func)) : VarIdMap.t offset :=
  match funcs with
  | (_, f)::fs => var_rbp_offsets_of_func f (var_rbp_offsets fs)
  | []         => VarIdMap.empty _
  end.

Definition var_depths_of_func (func : func) (tail_var_depths : VarIdMap.t nat) : VarIdMap.t nat :=
  let arg_depths   := map (fun var_id => (var_id, depth func))
                          (f_arg_var_ids func) in
  let local_depths := map (fun var_id => (var_id, depth func))
                          (f_local_var_ids func) in
  VarIdMap_add_list (arg_depths ++ local_depths) tail_var_depths.

Fixpoint var_depths (funcs : list (func_id * func)) : VarIdMap.t nat :=
  match funcs with
  | (_, f)::fs => var_depths_of_func f (var_depths fs)
  | []    => VarIdMap.empty _
  end.

Record compile_args : Type := {
  ca_func_depths :     FuncIdMap.t nat;
  ca_var_rbp_offsets : VarIdMap.t offset;
  ca_var_depths :      VarIdMap.t nat
}.

Definition file_compile_args (funcs : list (func_id * func)) : compile_args := {|
  ca_func_depths := func_depths funcs;
  ca_var_rbp_offsets := var_rbp_offsets funcs;
  ca_var_depths := var_depths funcs
|}.

(* Definition compile_func' (args : compile_args) (depth : nat) (body : cmd) : option asm :=
  compile_func (ca_func_depths args) depth (ca_var_rbp_offsets args) (ca_var_depths args) body. *)

Definition compile_file_assoc_list (funcs : list (func_id * func)) :
                option (list (func_id * asm)) :=
  let func_depths := func_depths funcs in
  let var_rbp_offsets := var_rbp_offsets funcs in
  let var_depths := var_depths funcs in
  compiled <- monad_map
    (fun '(id, func) =>
      asm <- compile_func func_depths (depth func) var_rbp_offsets var_depths
                          (f_body func) (var_rbp_offsets_of_func func (VarIdMap.empty _));;
      ret (id, asm))
    funcs;;
  ret compiled.

Definition compile_file (funcs : list (func_id * func)) : option prog :=
  assoc_list_prog <- compile_file_assoc_list funcs;;
  ret (FuncIdMap_of_assoc_list assoc_list_prog).

From PetitC Require Import InbuiltFunc.

(* Eval compute in (compile_file_assoc_list [(0%nat,
{| f_signature := {| fs_arg_rich_types := []; fs_rich_return_type := RVoid |};
   f_local_var_ids := [0%nat];
   f_local_var_types := [RPtr RInt];
   f_arg_var_ids := [];
   f_body := Seq (Expr (Assign (Var 0%nat <l: RPtr RInt) ((Cast (RPtr RInt) (RPtr RVoid) (Const (PtrValue NullPtr) <: RPtr RVoid)) <: RPtr RInt) <: RPtr RInt))
                 (Expr (CallInbuilt Putchar (LAECons (LValue (Dereference (LValue (Var 0%nat <l: RPtr RInt) <: RPtr RInt) <l: RInt) <: RInt) LAENil) <: RVoid));
   f_parent_func_ids := [] |})]).
m
Eval compute in (compile_expr (FuncIdMap.add 0%nat 0%nat (FuncIdMap.empty _)) (0%nat) (VarIdMap.add 0%nat (Z.of_nat word_size) (VarIdMap.empty _)) (VarIdMap.add 0%nat word_size (VarIdMap.empty _))
 (CallInbuilt Putchar (LAECons (LValue (Dereference (LValue (Var 0%nat <l: RPtr RInt) <: RPtr RInt) <l: RInt) <: RInt) LAENil) <: RVoid)
 [] 0%nat).

Eval compute in (compile_expr (FuncIdMap.add 0%nat 0%nat (FuncIdMap.empty _)) (0%nat) (VarIdMap.add 0%nat (Z.of_nat word_size) (VarIdMap.empty _)) (VarIdMap.add 0%nat word_size (VarIdMap.empty _))
 (LValue (Dereference (LValue (Var 0%nat <l: RPtr RInt) <: RPtr RInt) <l: RInt) <: RInt)
 [] 0%nat).

Eval compute in (compile_push_list_expr (FuncIdMap.add 0%nat 0%nat (FuncIdMap.empty _)) (0%nat) (VarIdMap.add 0%nat (Z.of_nat word_size) (VarIdMap.empty _)) (VarIdMap.add 0%nat word_size (VarIdMap.empty _))
(LAECons (LValue (Dereference (LValue (Var 0%nat <l: RPtr RInt) <: RPtr RInt) <l: RInt) <: RInt) LAENil)
 [] 0%nat). *)
(*
Eval compute in (compile_file_assoc_list [(0%nat,
 {| f_signature := {| fs_arg_rich_types := []; fs_rich_return_type := RVoid |};
    f_local_var_ids := [0%nat];
    f_local_var_types := [RInt];
    f_arg_var_ids := [];
    f_body := While (Cast RInt RBool (IncrOrDecr RInt Decr Pre (Var 0%nat <l: RInt) <: RInt) <: RBool)
              (Expr (CallInbuilt Putchar (LAECons (BinOp (IntArithBinop PlusIntInt) (Const (IntValue one_int_value) <: RInt) (LValue (Var 0%nat <l: RInt) <: RInt) <: RInt) LAENil) <: RVoid));
    f_parent_func_ids := [] |})]).

Eval compute in (compile_file_assoc_list [(0%nat,
{| f_signature := {| fs_arg_rich_types := []; fs_rich_return_type := RVoid |};
   f_local_var_ids := [0%nat];
   f_local_var_types := [RInt];
   f_arg_var_ids := [];
   f_body := Expr (CallInbuilt Putchar (LAECons (Const (IntValue zero_int_value) <: RInt) LAENil) <: RVoid);
   f_parent_func_ids := [] |})]). *)