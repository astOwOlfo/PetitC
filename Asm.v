From PetitC Require Import Values Ids InbuiltFunc Monad.

From Coq Require Import Lists.List ZArith.

Definition label : Set := nat.

Definition instr_index : Set := func_id * nat.

Definition next (idx : instr_index) : instr_index :=
  let '(func_id, i) := idx in
  (func_id, S i).

Definition add_to_instr_index (idx : instr_index) (n : nat) : instr_index :=
  let '(func_id, i) := idx in
  (func_id, i + n).

Inductive reg : Set := Rax | Rbx | Rdx | Rbp | Rsp.

Inductive operand : Set :=
  | Reg : reg -> operand
  | ConstInt : Z -> operand
  | ConstNullPtr : operand
  | Mem : reg -> operand
  | Offset : reg -> offset -> operand.

Inductive condition : Set := Zero | NotZero | StrictlyNegative.

Inductive instr : Set :=
  | Label (lbl : label)
  | Movq  (source destination : operand)
  | Leaq  (source destination : operand)
  | Addq  (source destination : operand)
  | Subq  (source destination : operand)
  | Andq  (source destination : operand)
  | Cmpq  (source1 source2 : operand)
  | Imulq (source : operand)
  | Idivq (source : operand)
  | Salq  (count : nat) (operand : operand)
  | Sarq  (count : nat) (operand : operand)
  | SetL  (cond : condition) (destination : operand)
  | Incrq (operand : operand)
  | Decrq (operand : operand)
  | Pushq (source : operand)
  | Popq  (destination : operand)
  | Jmp   (lbl : label)
  | Jcc   (cond : condition) (lbl : label)
  | ICall (func_id : func_id)
  | ICallInbuilt (func : inbuilt_func)
  | Ret.

Definition asm := list instr.

Definition prog := FuncIdMap.t asm.

Definition instr_at (prog : prog) (idx : instr_index) : option instr :=
  let '(func_id, i) := idx in
  func_instrs <- FuncIdMap.find func_id prog;;
  nth_error func_instrs i.