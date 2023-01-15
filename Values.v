From PetitC Require Import Ids.

From Coq Require Import ZArith Psatz Logic.ProofIrrelevance.

Definition int_min : Z := -2^63.
Definition int_max : Z := 2^63-1.

Definition int_value : Set := { value & (int_min <= value <= int_max)%Z }.

Definition int_value_to_Z : int_value -> Z := @projT1 _ _.

Definition block_id := nat.
Definition offset := Z.

Inductive ptr_value : Set :=
  | HeapPtr : block_id -> offset -> ptr_value
  | StackPtr : offset -> ptr_value
  | NullPtr : ptr_value.

Scheme Equality for ptr_value.

Inductive has_offset : ptr_value -> offset -> Prop :=
  | HOHeap  block_id offset : has_offset (HeapPtr block_id offset) offset
  | HOStack offset :          has_offset (StackPtr offset)         offset.

Inductive same_block : ptr_value -> ptr_value -> Prop :=
  | SBHeap  block_id offset offset' : same_block (HeapPtr block_id offset)
                                                 (HeapPtr block_id offset')
  | SBStack offset offset' :          same_block (StackPtr offset)
                                                 (StackPtr offset').

Inductive value : Set :=
  | IntValue : int_value -> value
  | PtrValue : ptr_value -> value
  | InstrIndexValue : (func_id * nat) -> value
  | Undef : value.

Inductive type : Set := Int | Bool | Ptr.

Inductive can_have_type : value -> type -> Prop :=
  | CHTInt      int_value :       can_have_type (IntValue int_value)                 Int
  | CHTHeapPtr  block_id offset : can_have_type (PtrValue (HeapPtr block_id offset)) Ptr
  | CHTStackPtr offset :          can_have_type (PtrValue (StackPtr offset))         Ptr
  | CHTNullPtr :                  can_have_type (PtrValue NullPtr)                   Ptr.

Definition Z_to_int_value (value : Z) : option int_value.
destruct ((Z.leb int_min value)%Z) eqn:H0.
- destruct ((value <=? int_max)%Z) eqn:H1.
  + apply Some.
    apply (existT _ value).
    split;
    apply Z.leb_le;
    assumption.
  + exact None.
- exact None.
Defined.

Lemma zero_in_range : (int_min <= 0)%Z /\ (0 <= int_max)%Z.
Proof. unfold int_min. unfold int_max. lia. Qed.

Lemma one_in_range : (int_min <= 1)%Z /\ (1 <= int_max)%Z.
Proof. unfold int_min. unfold int_max. lia. Qed.

Lemma eight_in_range : (int_min <= 1)%Z /\ (1 <= int_max)%Z.
Proof. unfold int_min. unfold int_max. lia. Qed.

Definition zero_int_value : int_value :=
  existT _ 0%Z zero_in_range.

Definition one_int_value : int_value :=
  existT _ 1%Z zero_in_range.

Definition eight_int_value : int_value :=
  existT _ 8%Z zero_in_range.  

Lemma int_value_to_Z_eq : forall int_value int_value',
  int_value_to_Z int_value = int_value_to_Z int_value' ->
int_value = int_value'.
Proof.
intros [value Hvalue] [value' Hvalue'] Heq. simpl in Heq.
revert Hvalue'. rewrite <- Heq. intro Hvalue'.
f_equal. apply proof_irrelevance.
Qed.
