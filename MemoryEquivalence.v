From PetitC Require Import Memory Output Values Ids Permutation.

From Coq Require Import Lists.List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition zero_offset_if_on_heap (ptr : ptr_value) : Prop :=
  match ptr with
  | HeapPtr _ offset     => offset = 0
  | StackPtr _ | NullPtr => True
  end.

Definition valid_ptr (mem : memory) (ptr : ptr_value) : Prop :=
  exists value, read mem ptr value.

Inductive in_block : memory -> ptr_value -> value -> Prop :=
  | IBStack stack heap offset value :
        OffsetMap.find offset stack = Some value ->
      in_block (stack, heap) (StackPtr offset) value
  | IBHeap stack heap block_id block offset offset' value :
        BlockIdMap.find block_id heap = Some block ->
        OffsetMap.find offset block = Some value ->
      in_block (stack, heap) (HeapPtr block_id offset') value.

Definition closed_under_access (mem : memory) (ptrs : list ptr_value) : Prop :=
  forall ptr ptr',
    In ptr ptrs ->
    in_block mem ptr (PtrValue ptr') ->
      In ptr' ptrs.

Section SubsetEquivalent.

Variable (corresponding_ptrs : list (ptr_value * ptr_value)).

Inductive values_equivalent : value -> value -> Prop :=
  | VEIntValue (val val' : int_value) :
      values_equivalent (IntValue val)
                        (IntValue val')

  | VEUndef :
      values_equivalent Undef
                        Undef

  | VEHeapPtr block_id block_id' offset :
        In (HeapPtr block_id 0, HeapPtr block_id' 0) corresponding_ptrs ->
      values_equivalent (PtrValue (HeapPtr block_id offset))
                        (PtrValue (HeapPtr block_id' offset))

  | VEStackPtr offset offset' :
        In (StackPtr offset, StackPtr offset') corresponding_ptrs ->
      values_equivalent (PtrValue (StackPtr offset))
                        (PtrValue (StackPtr offset')).

Inductive blocks_equivalent : memory -> ptr_value -> memory -> ptr_value -> Prop :=
  | BEStack heap heap' stack stack' offset offset' value value' :
        OffsetMap.find offset stack = Some value ->
        OffsetMap.find offset' stack' = Some value' ->
        values_equivalent value value' ->
      blocks_equivalent (stack, heap) (StackPtr offset)
                        (stack', heap') (StackPtr offset')

  | BEHeap heap heap' stack stack' block_id block_id' block block' ptr_offset ptr_offset' :
        BlockIdMap.find block_id heap = Some block ->
        BlockIdMap.find block_id' heap' = Some block' ->
        forall offset, (OffsetMap.In offset block <-> OffsetMap.In offset block') /\
                       (forall value value', OffsetMap.find offset block = Some value ->
                                             OffsetMap.find offset block' = Some value' ->
                                               values_equivalent value value') ->
      blocks_equivalent (stack, heap) (HeapPtr block_id ptr_offset)
                        (stack', heap') (HeapPtr block_id' ptr_offset').

Definition memory_subsets_equivalent (mem mem' : memory) : Prop :=
  let '(stack, heap) := mem in
  let '(stack', heap') := mem' in
  let ptrs  := map fst corresponding_ptrs in
  let ptrs' := map snd corresponding_ptrs in
  Forall (valid_ptr mem) ptrs /\
  Forall (valid_ptr mem') ptrs' /\
  Forall zero_offset_if_on_heap ptrs /\
  Forall zero_offset_if_on_heap ptrs' /\
  NoDup ptrs /\
  NoDup ptrs' /\
  Permutation ptrs ptrs' /\
  Forall (fun '(ptr, ptr') => blocks_equivalent mem ptr mem' ptr')
         corresponding_ptrs.

End SubsetEquivalent.

Definition accessible_equivalent (corresponding_access_ptrs : list (ptr_value * ptr_value))
                                 (mem mem' : memory) : Prop :=
  exists additional_corresponding_ptrs,
    let corresponding_ptrs := corresponding_access_ptrs ++ additional_corresponding_ptrs in
    closed_under_access mem  (map fst corresponding_ptrs) /\
    closed_under_access mem' (map snd corresponding_ptrs) /\
    memory_subsets_equivalent corresponding_ptrs mem mem'.
