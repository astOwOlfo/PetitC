From PetitC Require Import Codegen Values TypedTree.
Import TypedTree.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

From Coq Require Import ZArith.

Extraction Blacklist List String Int.

(* since nat is only used for ids, there won't be overflows *)
Extract Inductive nat => "int" [ "0" "(fun n -> n + 1)" ]
  "(fun fO fS n -> if n = 0 then fO () else fS (n - 1))".

(* Extract Inductive Z => "Big_int.big_int" ["Big_int.zero" "(fun n -> n)" "(fun n -> Big_int.minus_big_int n)"]
  "(fun f0 fPos fNeg n -> if n = Big_int.zero then f0 () else if Big_int.le_big_int n Big_int.zero then fNeg (Big_int.minus_big_int n) else fPos n)".

Extract Inductive positive => "Big_int.big_int" [ "(fun n -> Big_int.add_big_int (Big_int.add_big_int n n) (Big_int.of_int 1))" "(fun n -> Big_int.add_big_int (Big_int.add_big_int n n))" "Big_int.one" ]
  . *)

Extraction  "Codegen.ml" compile_file_assoc_list zero_int_value list_to_list_annotated_expr eight_int_value one_int_value.