From PetitC Require Import InbuiltFunc Memory Output Values.

From Coq Require Import Lists.List ZArith.
Import ListNotations.

Inductive inbuilt_func_step : inbuilt_func -> list value -> option value ->
                              memory -> output -> memory -> output -> Prop :=

      (* i should check if there's a defined behavior on memory overflow *)
  | IFSMalloc : forall size_nat size_int_value ptr mem mem' out,
        Z.of_nat size_nat = int_value_to_Z size_int_value ->
        (ptr, mem') = malloc mem size_nat ->
      inbuilt_func_step Malloc [IntValue size_int_value]
                               (Some (PtrValue ptr))
                               mem out mem' out

  | IFSPutchar : forall char_int_value mem out,
      inbuilt_func_step Putchar [IntValue char_int_value] None
                                mem out mem (char_int_value::out).
