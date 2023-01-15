open Lexing
open Lexer
open Parser
open TypeChecker
open Format
open Codegen
open AsmPrinter

let print_position (pos : Lexing.position) : unit =
  printf "File \"%s\", line %d, characters %d-%d:\n"
    (pos.pos_fname) (pos.pos_lnum)
    (pos.pos_cnum) (pos.pos_cnum + 1)

let print_loc (loc : Lexing.position * Lexing.position) : unit =
  printf "File \"%s\", line %d, characters %d-%d:\n"
    ((fst loc).pos_fname) ((fst loc).pos_lnum)
    ((fst loc).pos_cnum) ((snd loc).pos_cnum)

  (* transform "path/to/name.c" into "name.s" *)

let asm_filename (c_filename : string) : string =
  let len = String.length c_filename in
  String.sub c_filename 0 (len - 2) ^ ".s"

(* let asm_filename (c_filename : string) : string =
  let len = String.length c_filename in
  if String.contains c_filename '/' then
    let start = String.rindex_from c_filename (len - 1) '/' in
    String.sub c_filename (start + 1) (len - start - 3) ^ ".s"
  else 
    String.sub c_filename 0 (len - 2) ^ ".s" *)

let () =
  let parse_only = Array.mem "--parse-only" Sys.argv in
  let type_only = Array.mem "--type-only" Sys.argv in
  match List.filter
    (fun a -> not (List.mem a ["--parse-only"; "--type-only"]))
    (List.tl (Array.to_list Sys.argv)) with
  | [] | _::_::_ ->
      print_endline "Usage: petitc [--parse-only] [--type-only] <filename.c>";
      exit 3
  | [filename] ->
      if parse_only && type_only then begin
        print_endline "Cannot have both --parse-only and --type-only at the same time.";
        exit 3
      end (**);
      let file = open_in filename in
      let buf = Lexing.from_channel ~with_positions:true file in
      Lexing.set_position buf {Lexing.pos_fname = filename; pos_lnum = 1; pos_bol = 0; pos_cnum = 0};
      Lexing.set_filename buf filename;
      (* let buf = Lexing.from_channel file in *)
      try
        let file_ast = Parser.file Lexer.token buf  in
        close_in file;
        if not parse_only then begin
          try
            let (funcs, id_of_main) = typecheck_file file_ast in
            if type_only then
              exit 0
            else
              let prog = compile_file_assoc_list funcs in
              match prog with
              | None -> failwith "unreachable (compile_file returned none)"
              | Some prog -> let out = open_out (asm_filename filename) in
                             print_prog out prog id_of_main
          with
            | Typing_error (loc, msg) ->
                print_loc loc;
                printf "Typing error: %s\n" msg;
                exit 1
            | Linking_error msg ->
                printf "Linking error: %s\n" msg;
                exit 1
        end
      with
        (* | Lexer_error pos ->
            print_pos s;
            printf "Syntax error." *)
        | Custom_lexing_error (loc, msg) ->
            print_loc loc;
            printf "Syntax error: %s\n" msg;
            exit 1
        | Parser.Error -> printf "Parsing error\n"; (* to do: how do i get the position? *)
               exit 1