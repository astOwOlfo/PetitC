From PetitC Require Import Ids Values Tactics.

From Coq Require Import FSets.FMapAVL Structures.OrderedTypeEx ZArith Program.Wf Lia Lists.List.

Module OffsetMap := FMapAVL.Make Z_as_OT.

Definition heap_block : Type := OffsetMap.t value.

Definition stack : Type := OffsetMap.t value.

Definition heap : Type := BlockIdMap.t heap_block.

Definition memory : Type := stack * heap.

Inductive read : memory -> ptr_value -> value -> Prop :=
  | ReadStack offset value stack heap :
        OffsetMap.find offset stack = Some value ->
      read (stack, heap) (StackPtr offset) value

  | ReadHeap block_id block offset value stack heap :
        BlockIdMap.find block_id heap = Some block ->
        OffsetMap.find offset block = Some value ->
    read (stack, heap) (HeapPtr block_id offset) value.

Definition word_size : nat := 8.

Definition divisible (x y : Z) : Prop := exists q, (y = x * q)%Z.

Definition alligned (offset : offset) : Prop := divisible (Z.of_nat word_size) offset.

Inductive write : memory -> ptr_value -> value -> memory -> Prop :=
  | WriteStack offset value stack heap :
        (offset <= 0)%Z ->
        alligned offset ->
      write (stack, heap) (StackPtr offset) value (OffsetMap.add offset value stack, heap)

  | WriteHeap block_id block offset value stack heap :
        BlockIdMap.find block_id heap = Some block ->
        OffsetMap.In offset block ->
      write (stack, heap) (HeapPtr block_id offset) value
        (stack, BlockIdMap.add block_id (OffsetMap.add offset value block) heap).

Program Fixpoint fresh_heap_block (size : nat) {measure size}: heap_block :=
  match size with
  | 0 => OffsetMap.empty _
  | _ => if size <? word_size
         then OffsetMap.empty _
         else OffsetMap.add (Z.of_nat (size / word_size * word_size))
                            Undef
                            (fresh_heap_block (size - word_size))
  end.

Next Obligation. unfold word_size. lia. Qed.

Definition unused_block_id (heap : heap) : block_id :=
  BlockIdMap.fold (fun block_id _ acc => max (1 + block_id) acc) heap 0.

Definition unused_offset (stack : stack) : offset :=
  OffsetMap.fold (fun offset _ acc => Z.min (offset - Z.of_nat word_size)%Z acc) stack 0%Z.

Definition malloc (mem : memory) (size : nat) : ptr_value * memory :=
  let '(stack, heap) := mem in
  let block_id := (unused_block_id heap) in
  let new_heap := BlockIdMap.add block_id (fresh_heap_block size) heap in
  (HeapPtr block_id 0%Z, (stack, new_heap)).

Definition allocate_stack (mem : memory) : ptr_value * memory :=
  let '(stack, heap) := mem in
  let offset := unused_offset stack in
  let new_stack := OffsetMap.add offset Undef stack in
  (StackPtr offset, (new_stack, heap)).
