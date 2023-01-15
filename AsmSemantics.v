From PetitC Require Import Asm Memory Output Values Ids.

From Coq Require Import Lists.List ZArith.
Import ListNotations.
Open Scope Z_scope.

Inductive flag_value : Set := FTrue | FFalse | FUndef.

Record flag := {
  f_zero : flag_value;
  f_strictly_positive : flag_value
}.

Record regs := {
  r_rax : value;
  r_rbx : value;
  r_rdx : value;
  r_rbp : value;
  r_rsp : value;
  r_flag : flag
}.

Definition get_reg (reg : reg) (regs : regs) : value :=
  match reg with
  | Rax => r_rax regs
  | Rbx => r_rbx regs
  | Rdx => r_rdx regs
  | Rbp => r_rbp regs
  | Rsp => r_rsp regs
  end.

Definition set_reg (reg : reg) (val : value) (r : regs) : regs :=
  match reg with
  | Rax =>
      {| r_rax := val;    r_rbx := r_rbx r; r_rdx := r_rdx r; r_rbp := r_rbp r; r_rsp := r_rsp r;
         r_flag := r_flag r |}
  | Rbx =>
      {| r_rax := r_rax r; r_rbx := val;    r_rdx := r_rdx r; r_rbp := r_rbp r; r_rsp := r_rsp r;
         r_flag := r_flag r |}
  | Rdx =>
      {| r_rax := r_rax r; r_rbx := r_rbx r; r_rdx := val;    r_rbp := r_rbp r; r_rsp := r_rsp r;
         r_flag := r_flag r |}
  | Rbp =>
      {| r_rax := r_rax r; r_rbx := r_rbx r; r_rdx := r_rdx r; r_rbp := val;     r_rsp := r_rsp r;
         r_flag := r_flag r |}
  | Rsp =>
      {| r_rax := r_rax r; r_rbx := r_rbx r; r_rdx := r_rdx r; r_rbp := r_rbp r; r_rsp := val;
         r_flag := r_flag r |}
  end.

Definition set_flag (flag : flag) (r : regs) : regs :=
  {| r_rax := r_rax r; r_rbx := r_rbx r; r_rdx := r_rdx r; r_rbp := r_rbp r; r_rsp := r_rsp r;
     r_flag := flag |}.

Definition flag_of_value (val : value) : flag :=
  match val with
  | IntValue int_val =>
      let n := int_value_to_Z int_val in
      {| f_zero              := if n =? 0 then FTrue else FFalse;
         f_strictly_positive := if n >? 0 then FTrue else FFalse |}

  | PtrValue (StackPtr _ | HeapPtr _ _) =>
      {| f_zero              := FFalse;
         f_strictly_positive := FFalse |}

  | PtrValue NullPtr =>
      {| f_zero              := FTrue;
         f_strictly_positive := FUndef |}

  | Undef | InstrIndexValue _ =>
      {| f_zero              := FUndef;
         f_strictly_positive := FUndef |}
  end.

Definition set_flag_of_value (val : value) (r : regs) : regs :=
  set_flag (flag_of_value val) r.

Inductive operand_address : regs -> operand -> ptr_value -> Prop :=
  | OAMem reg regs ptr :
        get_reg reg regs = PtrValue ptr ->
      operand_address regs (Mem reg) ptr
  | OAOffset reg regs ptr shifter_ptr ptr_offset immediate_offset :
        get_reg reg regs = PtrValue ptr ->
        has_offset ptr ptr_offset ->
        has_offset shifter_ptr immediate_offset ->
        same_block ptr shifter_ptr ->
      operand_address regs (Offset reg immediate_offset) shifter_ptr.

Inductive read_operand : memory -> regs -> operand -> value -> Prop :=
  | ROReg mem regs reg :
      read_operand mem regs (Reg reg) (get_reg reg regs)
  | ROConstInt mem regs int_val int :
        int_value_to_Z int_val = int ->
      read_operand mem regs (ConstInt int) (IntValue int_val)
  | ROConstNullPtr mem regs :
      read_operand mem regs ConstNullPtr (PtrValue NullPtr)
  | ROAddress mem regs operand ptr val :
        operand_address regs operand ptr ->
        read mem ptr val ->
      read_operand mem regs operand val.

Inductive write_operand : memory -> regs -> operand -> value -> memory -> regs -> Prop :=
  | WOReg mem regs reg val :
      write_operand mem regs (Reg reg) val mem (set_reg reg val regs)
  | WOAddress mem mem' regs operand ptr val :
        operand_address regs operand ptr ->
        write mem ptr val mem' ->
      write_operand mem regs operand val mem' regs.

Section InstrStep.

Variable (prog : prog).

Inductive add_values : value -> value -> value -> Prop :=
  | AVIntInt (lhs rhs result : int_value) :
        int_value_to_Z lhs + int_value_to_Z rhs = int_value_to_Z result ->
      add_values (IntValue lhs) (IntValue rhs) (IntValue result)

  | AVIntPtr (lhs : int_value) (rhs result : ptr_value) (rhs_offset result_offset : offset) :
        same_block rhs result ->
        has_offset rhs rhs_offset ->
        has_offset result result_offset ->
        int_value_to_Z lhs + rhs_offset = result_offset ->
      add_values (IntValue lhs) (PtrValue rhs) (PtrValue result)
      
  | AVPtrInt (lhs : ptr_value) (rhs : int_value) (result : ptr_value)
             (lhs_offset result_offset : offset) :
        same_block lhs result ->
        has_offset lhs lhs_offset ->
        has_offset result result_offset ->
        lhs_offset + int_value_to_Z rhs = result_offset ->
      add_values (PtrValue lhs) (IntValue rhs) (PtrValue result).

Inductive subtract_values : value -> value -> value -> Prop :=
  | SVIntInt (lhs rhs result : int_value) :
        int_value_to_Z lhs - int_value_to_Z rhs = int_value_to_Z result ->
      subtract_values (IntValue lhs) (IntValue rhs) (IntValue result)

  | SVPtrInt (lhs : ptr_value) (rhs : int_value) (result : ptr_value)
             (lhs_offset result_offset : offset) :
        same_block lhs result ->
        has_offset lhs lhs_offset ->
        has_offset result result_offset ->
        lhs_offset - int_value_to_Z rhs = result_offset ->
      subtract_values (PtrValue lhs) (IntValue rhs) (PtrValue result)
    
  | SVPtrPtr (lhs rhs : ptr_value) (result : int_value) (lhs_offset rhs_offset : offset) :
        same_block lhs rhs ->
        has_offset lhs lhs_offset ->
        has_offset rhs rhs_offset ->
        lhs_offset - rhs_offset = int_value_to_Z result ->
      subtract_values (PtrValue lhs) (PtrValue rhs) (IntValue result).

Definition flag_value_not (fv : flag_value) : flag_value :=
  match fv with
  | FTrue  => FFalse
  | FFalse => FTrue
  | FUndef => FUndef
  end.

Definition flag_value_or (lhs rhs : flag_value) : flag_value :=
  match lhs, rhs with
  | FTrue, FFalse | FFalse, FTrue | FTrue, FTrue => FTrue
  | FFalse, FFalse                              => FFalse
  | FUndef, _ | _, FUndef                       => FUndef
  end.

Definition eval_condition_flag_value (cond : condition) (flag : flag) : flag_value :=
  match cond with
  | Zero             => f_zero flag
  | NotZero          => flag_value_not (f_zero flag)
  | StrictlyNegative => flag_value_not (flag_value_or (f_zero flag) (f_strictly_positive flag))
  end.

Inductive eval_condition : condition -> flag -> bool -> Prop :=
  | ECTrue cond flag :
      eval_condition_flag_value cond flag = FTrue ->
      eval_condition cond flag true
  | ECFalse cond flag :
      eval_condition_flag_value cond flag = FFalse ->
      eval_condition cond flag false.

Definition set_lowest_byte (lowest_byte : Z) (n : Z) : Z :=
  n / 256 * 256 + (lowest_byte mod 256).

Inductive instr_step : ((memory * output) * instr_index * regs) ->
                       ((memory * output) * instr_index * regs) -> Prop :=
  | ISLabel mem out idx regs lbl :
        instr_at prog idx = Some (Label lbl) ->
      instr_step ((mem, out), idx, regs)
                 ((mem, out), next idx, regs)

  | ISMovq mem mem' out idx regs regs' val (source destination : operand) :
        instr_at prog idx = Some (Movq source destination) ->
        read_operand mem regs source val ->
        write_operand mem regs destination val mem' regs' ->
      instr_step ((mem, out), idx, regs)
                 ((mem', out), next idx, regs')

  | ISLeaq mem mem' out idx regs regs' ptr (source destination : operand) :
        instr_at prog idx = Some (Leaq source destination) ->
        operand_address regs source ptr ->
        write_operand mem regs destination (PtrValue ptr) mem' regs' ->
      instr_step ((mem, out), idx, regs)
                 ((mem', out), next idx, regs')
                 
  | ISAddq mem mem' out idx regs regs' src_val dst_val result_val (source destination : operand) :
        instr_at prog idx = Some (Addq source destination) ->
        read_operand mem regs source src_val ->
        read_operand mem regs destination dst_val ->
        add_values dst_val src_val result_val ->
        write_operand mem regs destination result_val mem' regs' ->
      instr_step ((mem, out), idx, regs)
                 ((mem', out), next idx, set_flag_of_value result_val regs')
                 
  | ISSubq mem mem' out idx regs regs' src_val dst_val result_val (source destination : operand) :
        instr_at prog idx = Some (Subq source destination) ->
        read_operand mem regs source src_val ->
        read_operand mem regs destination dst_val ->
        subtract_values dst_val src_val result_val ->
        write_operand mem regs destination result_val mem' regs' ->
      instr_step ((mem, out), idx, regs)
                 ((mem', out), next idx, set_flag_of_value result_val regs')
          
      (* we only define what and does on two equal operands because
         that's the only way we use this instruction *)
  | ISAndq mem out idx regs val (source destination : operand) :
        instr_at prog idx = Some (Andq source destination) ->
        read_operand mem regs source val ->
        read_operand mem regs destination val ->
      instr_step ((mem, out), idx, regs)
                 ((mem, out), next idx, set_flag_of_value val regs)
                 
  | ISCmpq mem out idx regs src_val dst_val result_val (source destination : operand) :
        instr_at prog idx = Some (Cmpq source destination) ->
        read_operand mem regs source src_val ->
        read_operand mem regs destination dst_val ->
        subtract_values dst_val src_val result_val ->
      instr_step ((mem, out), idx, regs)
                 ((mem, out), next idx, set_flag_of_value result_val regs)
                 
      (* we only define what happens if there is no overflow *)
  | ISImulq mem out idx regs (src dst result : int_value) (source : operand) :
        instr_at prog idx = Some (Imulq source) ->
        read_operand mem regs source (IntValue src) ->
        read_operand mem regs (Reg Rax) (IntValue dst) ->
        int_value_to_Z src * int_value_to_Z dst = int_value_to_Z result ->
      instr_step ((mem, out), idx, regs)
                 ((mem, out), next idx, set_reg Rdx (IntValue zero_int_value)
                                             (set_reg Rax (IntValue dst) regs))
          
      (* we only define what happens if rdx is zero *)
  | ISIdivq mem out idx regs (src dst quotient remainder : int_value) (source : operand) :
        instr_at prog idx = Some (Idivq source) ->
        read_operand mem regs source (IntValue src) ->
        read_operand mem regs (Reg Rax) (IntValue dst) ->
        read_operand mem regs (Reg Rdx) (IntValue zero_int_value) ->
        ( let src_Z := int_value_to_Z src in
          let dst_Z := int_value_to_Z dst in
          let quotient_Z := int_value_to_Z quotient in
          let remainder_Z := int_value_to_Z remainder in
            src_Z <> 0 /\
            Z.abs dst_Z   /  Z.abs src_Z  * Z.sgn dst_Z * Z.sgn src_Z = quotient_Z /\
            (Z.abs dst_Z mod Z.abs dst_Z) * Z.sgn src_Z * Z.sgn dst_Z = remainder_Z ) ->
            (* there might be a problem like the quotient fits but the remainder doesn't,
               especially with max_int and min_int *)
      instr_step ((mem, out), idx, regs)
                 ((mem, out), next idx, set_reg Rdx (IntValue remainder)
                                             (set_reg Rax (IntValue quotient) regs))
                                             
  | ISSalq mem mem' out idx regs regs' (val val' : int_value) (count : nat) (oper : operand) :
        instr_at prog idx = Some (Salq count oper) ->
        read_operand mem regs oper (IntValue val) ->
        write_operand mem regs oper (IntValue val') mem' regs' ->
        int_value_to_Z val * Z.of_nat (2 ^ count) = int_value_to_Z val' ->
      instr_step ((mem, out), idx, regs)
                 ((mem', out), next idx, regs')
                 
  | ISSarq mem mem' out idx regs regs' (val val' : int_value) (count : nat) (oper : operand) :
        instr_at prog idx = Some (Salq count oper) ->
        read_operand mem regs oper (IntValue val) ->
        write_operand mem regs oper (IntValue val') mem' regs' ->
        int_value_to_Z val / Z.of_nat (2 ^ count) = int_value_to_Z val' ->
      instr_step ((mem, out), idx, regs)
                 ((mem', out), next idx, regs')
                 
  | ISSetL mem mem' out idx regs regs' (val val' : int_value) (cond : condition) (cond_bool : bool)
           (oper : operand) :
        instr_at prog idx = Some (SetL cond oper) ->
        read_operand mem regs oper (IntValue val) ->
        write_operand mem regs oper (IntValue val') mem' regs' ->
        eval_condition cond (r_flag regs) cond_bool ->
        set_lowest_byte (if cond_bool then 1 else 0) (int_value_to_Z val) = int_value_to_Z val' ->
      instr_step ((mem, out), idx, regs)
                 ((mem', out), next idx, regs')
        
  | ISIncrq mem mem' out idx regs regs' val val' (oper : operand) :
        instr_at prog idx = Some (Incrq oper) ->
        read_operand mem regs oper val ->
        write_operand mem regs oper val' mem' regs' ->
        add_values val (IntValue one_int_value) val' ->
      instr_step ((mem, out), idx, regs)
                 ((mem', out), next idx, regs')
        
  | ISDecrq mem mem' out idx regs regs' val val' (oper : operand) :
        instr_at prog idx = Some (Decrq oper) ->
        read_operand mem regs oper val ->
        write_operand mem regs oper val' mem' regs' ->
        subtract_values val (IntValue one_int_value) val' ->
      instr_step ((mem, out), idx, regs)
                 ((mem', out), next idx, regs')
                
      (* what happens when i push or pop an operand that depends on rsp?
         i should just forbid using such instructions *) 
  | ISPushq mem mem' out idx regs val ptr ptr' offset (source : operand) :
        instr_at prog idx = Some (Pushq source) ->
        read_operand mem regs source val ->
        r_rsp regs = PtrValue ptr ->
        same_block ptr ptr' ->
        has_offset ptr offset ->
        has_offset ptr' (offset - Z.of_nat word_size) ->
        write mem ptr' val mem' ->
      instr_step ((mem, out), idx, regs)
                 ((mem', out), next idx, set_reg Rsp (PtrValue ptr') regs)
                 
  | ISPopq mem mem' out idx regs regs' val ptr ptr' offset (destination : operand) :
        instr_at prog idx = Some (Popq destination) ->
        read mem ptr val ->
        r_rsp regs = PtrValue ptr ->
        same_block ptr ptr' ->
        has_offset ptr offset ->
        has_offset ptr' (offset + Z.of_nat word_size) ->
        write_operand mem regs destination val mem' regs' ->
      instr_step ((mem, out), idx, regs)
                 ((mem', out), next idx, set_reg Rsp (PtrValue ptr') regs')
                 
  | ISJmp mem out idx idx' regs lbl :
        instr_at prog idx = Some (Jmp lbl) ->
        instr_at prog idx' = Some (Label lbl) ->
      instr_step ((mem, out), idx, regs)
                 ((mem, out), idx, regs)
                 
  | ISJcc mem out idx idx' regs lbl (cond : condition) (cond_bool : bool) :
        instr_at prog idx = Some (Jcc cond lbl) ->
        instr_at prog idx' = Some (Label lbl) ->
        eval_condition cond (r_flag regs) cond_bool ->
      instr_step ((mem, out), idx, regs)
                 ((mem, out), if cond_bool then idx' else next idx, regs)
                 
  | ISCall mem mem' out idx idx' regs lbl ptr ptr' offset :
        instr_at prog idx = Some (ICall lbl) ->
        instr_at prog idx' = Some (Label lbl) ->
        r_rsp regs = PtrValue ptr ->
        same_block ptr ptr' ->
        has_offset ptr offset ->
        has_offset ptr' (offset - Z.of_nat word_size) ->
        write mem ptr' (InstrIndexValue idx) mem' ->
      instr_step ((mem, out), idx, regs)
                 ((mem', out), idx', set_reg Rsp (PtrValue ptr') regs)
                 
  | ISRet mem out idx idx' regs ptr ptr' offset :
        instr_at prog idx = Some Ret ->
        r_rsp regs = PtrValue ptr ->
        read mem ptr (InstrIndexValue idx') ->
        same_block ptr ptr' ->
        has_offset ptr offset ->
        has_offset ptr' (offset - Z.of_nat word_size) ->
      instr_step ((mem, out), idx, regs)
                 ((mem, out), idx', set_reg Rsp (PtrValue ptr') regs).

End InstrStep.