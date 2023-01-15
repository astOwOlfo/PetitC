open Printf
open Codegen
open TypeChecker

let print_reg (fmt : out_channel) : reg -> unit = function
| Rax -> fprintf fmt "%%rax"
| Rbx -> fprintf fmt "%%rbx"
| Rdx -> fprintf fmt "%%rdx"
| Rbp -> fprintf fmt "%%rbp"
| Rsp -> fprintf fmt "%%rsp"

let rec print_operand (fmt : out_channel) : operand -> unit = function
| Reg reg              -> print_reg fmt reg
| ConstInt n           -> fprintf fmt "$%s" (Int64.to_string (z_to_int64 n))
| ConstNullPtr         -> fprintf fmt "$0"
| Mem reg              -> fprintf fmt "(";
                          print_reg fmt reg;
                          fprintf fmt ")"
| Offset (reg, offset) -> fprintf fmt "%s" (Int64.to_string (z_to_int64 offset));
                          print_operand fmt (Mem reg)

let print_label (fmt : out_channel) (func_id : func_id) (lbl : label) : unit =
  fprintf fmt "F%dL%d" func_id lbl

let print_func_label (fmt : out_channel) (func_id : func_id) : unit =
  fprintf fmt "F%d" func_id

let print_jump_memonic (fmt : out_channel) : condition -> unit = function
| Zero             -> fprintf fmt "jz"
| NotZero          -> fprintf fmt "jnz"
| StrictlyNegative -> fprintf fmt "js"

let print_setl_mnemonic (fmt : out_channel) : condition -> unit = function
| Zero             -> fprintf fmt "setz"
| NotZero          -> fprintf fmt "setnz"
| StrictlyNegative -> fprintf fmt "sets"

let print_setl_operand (fmt : out_channel) : operand -> unit = function
| Reg Rax -> fprintf fmt "%%al"
| Reg Rbx -> fprintf fmt "%%bl"
| _       -> failwith "invalid assembly instruction"

let print_inbuilt_func_label (fmt : out_channel) : inbuilt_func -> unit = function
| Malloc  -> fprintf fmt "malloc_allign"
| Putchar -> fprintf fmt "putchar_allign"

let print_instr' (fmt : out_channel) (mnemonic : string) (operands : operand list) : unit =
  fprintf fmt "\t%s" mnemonic;
  fprintf fmt " ";
  print_operand fmt (List.hd operands);
  List.iter (fun oper -> fprintf fmt ", "; print_operand fmt oper) (List.tl operands);
  fprintf fmt "\n"

let print_instr (fmt : out_channel) (func_id : func_id) : instr -> unit = function
| Label lbl            -> print_label fmt func_id lbl;
                          fprintf fmt ":\n"
| Movq (oper1, oper2)  -> print_instr' fmt "movq" [oper1; oper2]
| Addq (oper1, oper2)  -> print_instr' fmt "addq" [oper1; oper2]
| Subq (oper1, oper2)  -> print_instr' fmt "subq" [oper1; oper2]
| Andq (oper1, oper2)  -> print_instr' fmt "andq" [oper1; oper2]
| Cmpq (oper1, oper2)  -> print_instr' fmt "cmpq" [oper1; oper2]
| Leaq (oper1, oper2)  -> print_instr' fmt "leaq" [oper1; oper2]
| Imulq oper           -> print_instr' fmt "imulq" [oper]
| Idivq oper           -> print_instr' fmt "idivq" [oper]
| Salq (n, oper)       -> fprintf fmt "\tsalq $%d, " n;
                          print_operand fmt oper;
                          fprintf fmt "\n"
| Sarq (n, oper)       -> fprintf fmt "\tsarq, $%d " n;
                          print_operand fmt oper;
                          fprintf fmt "\n"
| SetL (cond, oper)    -> fprintf fmt "\t";
                          print_setl_mnemonic fmt cond;
                          fprintf fmt " ";
                          print_setl_operand fmt oper;
                          fprintf fmt "\n"
| Incrq oper           -> print_instr' fmt "incq" [oper]
| Decrq oper           -> print_instr' fmt "decq" [oper]
| Pushq oper           -> print_instr' fmt "pushq" [oper]
| Popq oper            -> print_instr' fmt "popq" [oper]
| Jmp lbl              -> fprintf fmt "\tjmp ";
                          print_label fmt func_id lbl;
                          fprintf fmt "\n"
| Jcc (condition, lbl) -> fprintf fmt "\t";
                          print_jump_memonic fmt condition;
                          fprintf fmt " ";
                          print_label fmt func_id lbl;
                          fprintf fmt "\n"
| ICall func_id        -> fprintf fmt "\tcallq ";
                          print_func_label fmt func_id;
                          fprintf fmt "\n"
| ICallInbuilt inbuilt_func ->
                          fprintf fmt "\tcallq ";
                          print_inbuilt_func_label fmt inbuilt_func;
                          fprintf fmt "\n"
| Ret                  -> fprintf fmt "\tret\n"

let print_func (fmt : out_channel) (func_id : func_id) (func_id_of_main) (asm : asm) : unit =
  if func_id = func_id_of_main then
    fprintf fmt "main:\n"
  else begin
    print_func_label fmt func_id;
    fprintf fmt ":\n"
  end;
  List.iter (print_instr fmt func_id) asm

let print_prelude (fmt : out_channel) =
  fprintf fmt ".global main\n";
  List.iter (fun (inbuilt_func, name) ->
    print_inbuilt_func_label fmt inbuilt_func;
    fprintf fmt ":\n";
    fprintf fmt "\tmovq 8(%%rsp), %%rdi\n";
    fprintf fmt "\tmovq %%rsp, %%rax\n";
    fprintf fmt "\tandq $8, %%rax\n";
    fprintf fmt "\tjz  %s_alligned\n" name;
    fprintf fmt "\tpushq %%rax\n";
    fprintf fmt "\tmovb $0, %%al\n";
    fprintf fmt "\tcallq %s\n" name;
    fprintf fmt "\tpopq %%rbx\n";
    fprintf fmt "\tret\n";
    fprintf fmt "%s_alligned:\n" name;
    fprintf fmt "\tmovb $0, %%al\n";
    fprintf fmt "\tcallq %s\n" name;
    fprintf fmt "\tret\n")
    [(Malloc, "malloc"); (Putchar, "putchar")]


let print_prog (fmt : out_channel) (prog : (func_id * asm) list) (func_id_of_main : func_id) : unit =
  print_prelude fmt;
  List.iter (fun (id, asm) -> print_func fmt id func_id_of_main asm) prog
  