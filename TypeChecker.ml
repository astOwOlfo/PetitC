open Codegen
open TypedTree
open Z
type ident = string

exception Typing_error of Ast.loc * string
let err loc msg = raise (Typing_error (loc, msg))
exception Linking_error of string

module IdentMap = Map.Make(String)
module IdentSet = Set.Make(String)
module IdMap = Map.Make(Int)

(* convert int64 to the coq representation of integers *)
let rec positive_of_int64 (n : int64) : positive =
  if n = Int64.one then
    XH
  else if Int64.rem n (Int64.of_int 2) = Int64.zero then
    XO (positive_of_int64 (Int64.div n (Int64.of_int 2)))
  else XI (positive_of_int64 (Int64.div n (Int64.of_int 2)))

let z_of_int64 (n : int64) : z =
  if n = Int64.zero then
    Z0
  else if Int64.compare n Int64.zero > 0 then
    Zpos (positive_of_int64 n)
  else
    Zneg (positive_of_int64 (Int64.neg n))

let rec positive_to_int64 : positive -> int64 = function
  | XH   -> Int64.one
  | XO n -> Int64.mul (Int64.of_int 2) (positive_to_int64 n)
  | XI n -> Int64.add Int64.one (Int64.mul (Int64.of_int 2) (positive_to_int64 n))

let z_to_int64 : z -> int64 = function
  | Z0     -> Int64.zero
  | Zpos n -> positive_to_int64 n
  | Zneg n -> Int64.neg (positive_to_int64 n)

(* convert an int64 into the coq representation of integer values between -2^63 and 2^63-1 *)
let int_value_of_int64 (n : int64) : int_value =
  ExistT (z_of_int64 n, (let rec f _ = Obj.repr f in Obj.repr f))

(* maps variable and function names to variable and function ids *)
type name_map = {
  nm_var_ids : var_id IdentMap.t;
  nm_func_ids : func_id IdentMap.t
}

let empty_name_map = {
  nm_var_ids = IdentMap.empty;
  nm_func_ids = IdentMap.empty
}

let name_map_add_var (name : ident) (id : var_id) (names : name_map) : name_map =
  { nm_var_ids = IdentMap.add name id names.nm_var_ids;
    nm_func_ids = IdentMap.remove name names.nm_func_ids }

let name_map_add_func (name : ident) (id : func_id) (names : name_map) : name_map =
  { nm_func_ids = IdentMap.add name id names.nm_func_ids;
    nm_var_ids = IdentMap.remove name names.nm_var_ids }

type env = {
  env_var_types : rich_type IdMap.t;
  env_func_sigs : func_signature IdMap.t;
  env_max_var_id : var_id;
  env_max_func_id : var_id
}

let empty_env = {
  env_var_types = IdMap.empty;
  env_func_sigs = IdMap.empty;
  env_max_var_id = 0;
  env_max_func_id = 0
}

let env_add_var (id : int) (ty : rich_type) (env : env) : env =
  { env with env_var_types = IdMap.add id ty env.env_var_types }

let env_add_func (id : int) (_sig : func_signature) (env : env) : env =
  { env with env_func_sigs = IdMap.add id _sig env.env_func_sigs }

let new_func_id (env : env ref) : func_id =
  let id = (!env).env_max_func_id + 1 in
  env := { !env with env_max_func_id = id };
  id

let new_var_id (env : env ref) : var_id =
  let id = (!env).env_max_var_id + 1 in
  env := { !env with env_max_var_id = id };
  id

let inbuilt_funcs : inbuilt_func IdentMap.t =
  IdentMap.of_seq (List.to_seq [ ("malloc", Malloc);
                                 ("putchar", Putchar) ])

(* returns annotated expression resulting from casting
   annotated expression `annot` to type `ty`
   raises a Typing_error if this conversion is not legal *)
let cast (ty : rich_type) (annot : annotated_expr) (loc : Ast.loc) : annotated_expr =
  match annot with (AnnotatedExpr (_, ty')) -> begin
    match ty, ty' with
    | ty, ty' when ty = ty' -> annot
    | RInt,       RBool      -> AnnotatedExpr (Cast (RBool, RInt, annot), RInt)
    | RBool,      RInt       -> AnnotatedExpr (Cast (RInt, RBool, annot), RBool)
    | RBool,      RPtr ty    -> AnnotatedExpr (Cast ((RPtr ty), RBool, annot), RPtr ty)
    | RPtr ty2,   RPtr ty1 when ty1 = ty2 -> AnnotatedExpr (Cast ((RPtr ty'), (RPtr ty), annot), RPtr ty)
    | RPtr _,     RPtr RVoid
    | RPtr RVoid, RPtr _     -> AnnotatedExpr (Cast ((RPtr ty'), (RPtr ty), annot), RPtr ty)
    | _, _                   -> err loc "cannot convert"
  end

(* types to which the first and second arguments should be cast
   and result type of operator ast_op applied to arguments of type
   arg1_ty arg2_ty, in this order *)
let binoprich_types (ast_op : Ast.binop) (arg1_ty : rich_type) (arg2_ty : rich_type) :
    rich_type * rich_type * rich_type =
  match ast_op, arg1_ty, arg2_ty with
  | Ast.Assign, ty, _ ->
      (ty, ty, ty)
  | Ast.Plus, RPtr ty, _ ->
      (RPtr ty, RInt, RPtr ty)
  | Ast.Plus, _, RPtr ty ->
      (RInt, RPtr ty, RPtr ty)
  | Ast.Plus, _, _ ->
      (RInt, RInt, RInt)
  | Ast.Minus, RPtr RInt, RPtr RInt
  | Ast.Minus, RPtr RBool, RPtr RBool
  | Ast.Minus, RPtr RVoid, RPtr RVoid
  | Ast.Minus, RPtr (RPtr _), RPtr (RPtr _) ->
      (arg1_ty, arg2_ty, RInt)
  | Ast.Minus, RPtr ty, _ ->
      (RPtr ty, RInt, RPtr ty)
  | Ast.Minus, _, _ ->
      (RInt, RInt, RInt)
  | (Ast.Times | Ast.Div | Ast.Mod), _, _ ->
      (RInt, RInt, RInt)
  | (Ast.Eq | Ast.Ne | Ast.Lt | Ast.Le | Ast.Gt | Ast.Ge), RPtr ty1, RPtr ty2 ->
      (RPtr RVoid, RPtr RVoid, RBool)
  | (Ast.Eq | Ast.Ne), _, _ ->
      (RInt, RInt, RBool)
  | (Ast.Lt | Ast.Le | Ast.Gt | Ast.Ge), _, _ ->
      (RInt, RInt, RBool)
  | (Ast.And | Ast.Or), _, _ ->
      (RBool, RBool, RBool)

(* a value that will be returned if the return statement is ommitted *)
let default_return_value : rich_type -> annotated_expr = function
  | RVoid   -> AnnotatedExpr (Unit, RVoid)
  | RInt    -> AnnotatedExpr (Const (IntValue zero_int_value), RInt)
  | RBool   -> AnnotatedExpr (Cast (RInt, RBool, AnnotatedExpr (Const (IntValue zero_int_value), RInt)), RBool)
  | RPtr ty -> AnnotatedExpr (Cast (RPtr RVoid, RPtr ty, AnnotatedExpr (Const (PtrValue NullPtr), RPtr RVoid)), RPtr ty)

(* if the annotated expression `annot` is an lvalue, cast it
   to the type `annotated_lvalue` of annotated lvalues,
   otherwise, raise a Typing_expression *)
let rec annotated_expr_to_annotated_lvalue (annot : annotated_expr) (loc : Ast.loc) : annotated_lvalue =
  match annot with
  | AnnotatedExpr (LValue annotated_lvalue, _) -> annotated_lvalue
  | _                         -> err loc "expected lvalue"

(* maps expression `ex` to an expression annotated with types,
   see documentations of env and name_map *)
let rec typecheck_expr (env : env) (names : name_map) (ex : Ast.expr) : annotated_expr =
  match ex with
  | Ast.Const (loc, n) ->
      AnnotatedExpr (Const (IntValue (int_value_of_int64 n)), RInt)

  | Ast.Null loc ->
      AnnotatedExpr (Const (PtrValue NullPtr), RPtr RVoid)

  | Ast.Var (loc, name) ->
      begin match (IdentMap.find_opt name (names.nm_var_ids)) with
      | Some id ->
          let ty = IdMap.find id env.env_var_types in
          AnnotatedExpr (LValue (AnnotatedLvalue (Var id, ty)), ty)
      | None ->
          err loc "unknown variable name"
      end

  | Ast.UnOp (_, ast_op, ast_ex1) ->
      let loc = Ast.expr_loc ast_ex1 in
      let (AnnotatedExpr (_, ty1) as annot1) = typecheck_expr env names ast_ex1 in
      let (cast_annot1, result_ty) =
        begin match ast_op, ty1 with
        | Ast.Dereference, RPtr RVoid ->
            err loc "Cannot dereference pointer to void."
        | Ast.Dereference, RPtr ty ->
            (annot1, ty)
        | Ast.Dereference, _ ->
            err loc "expected pointer"
        | Ast.AddressOf, ty ->
            (annot1, RPtr ty)
        | (Ast.UnaryPlus | Ast.UnaryMinus), _ ->
            (cast RInt annot1 loc, RInt)
        | Ast.Not, _ ->
            (cast RBool annot1 loc, RBool)
        | (Ast.PreIncrement | Ast.PostIncrement | Ast.PreDecrement
              | Ast.PostDecrement), RVoid ->
            err loc "expected an integer, a boolean, or a pointer, got void"
        | (Ast.PreIncrement | Ast.PostIncrement | Ast.PreDecrement
              | Ast.PostDecrement), ty ->
          (annot1, ty)
        end in
          begin match ast_op with
          | Ast.Dereference ->
              AnnotatedExpr (LValue (AnnotatedLvalue (Dereference cast_annot1, result_ty)), result_ty)
          | Ast.AddressOf ->
              let annotated_lvalue = annotated_expr_to_annotated_lvalue cast_annot1 loc in
              AnnotatedExpr (AddressOf annotated_lvalue, result_ty)
          | Ast.UnaryPlus ->
              cast_annot1
          | Ast.UnaryMinus ->
              AnnotatedExpr (BinOp (IntArithBinop MinusIntInt, (AnnotatedExpr (Const (IntValue zero_int_value), RInt)), cast_annot1), result_ty)
          | Ast.Not ->
              AnnotatedExpr (Not cast_annot1, result_ty)
          | Ast.PreIncrement ->
              let annotated_lvalue = annotated_expr_to_annotated_lvalue cast_annot1 loc in
              AnnotatedExpr (IncrOrDecr (result_ty, Incr, Pre, annotated_lvalue), result_ty)
          | Ast.PostIncrement ->
              let annotated_lvalue = annotated_expr_to_annotated_lvalue cast_annot1 loc in
              AnnotatedExpr (IncrOrDecr (result_ty, Incr, Post, annotated_lvalue), result_ty)
          | Ast.PreDecrement ->
              let annotated_lvalue = annotated_expr_to_annotated_lvalue cast_annot1 loc in
              AnnotatedExpr (IncrOrDecr (result_ty, Decr, Pre, annotated_lvalue), result_ty)
          | Ast.PostDecrement ->
              let annotated_lvalue = annotated_expr_to_annotated_lvalue cast_annot1 loc in
              AnnotatedExpr (IncrOrDecr (result_ty, Decr, Post, annotated_lvalue), result_ty)
        end

  | Ast.BinOp (loc, ast_op, ast_ex1, ast_ex2) ->
      let (AnnotatedExpr (ex1, ty1) as annot1) = typecheck_expr env names ast_ex1 in
      let (AnnotatedExpr (ex2, ty2) as annot2) = typecheck_expr env names ast_ex2 in
      let (expected_ty1, expected_ty2, result_ty) = binoprich_types ast_op ty1 ty2 in
      let cast_annot1 = cast expected_ty1 annot1 (Ast.expr_loc ast_ex1) in
      let cast_annot2 = cast expected_ty2 annot2 (Ast.expr_loc ast_ex2) in
        begin match ast_op with
        | Ast.Assign ->
            let annotated_lvalue1 = annotated_expr_to_annotated_lvalue annot1 (Ast.expr_loc ast_ex1) in
              AnnotatedExpr (Assign (annotated_lvalue1, cast_annot2), result_ty)
        | Ast.Plus ->
            let plus  = match expected_ty1, expected_ty2 with
                        | RInt,   RInt    -> IntArithBinop PlusIntInt
                        | RPtr _, RInt    -> PlusPtrInt
                        | RPtr _, RPtr _  -> PlusIntPtr
                        | _               -> failwith "unreachable" in
            AnnotatedExpr (BinOp (plus, cast_annot1, cast_annot2), result_ty)
        | Ast.Minus ->
          let minus = match expected_ty1, expected_ty2 with
                      | RInt,   RInt    -> IntArithBinop MinusIntInt
                      | RPtr _, RInt    -> MinusPtrInt
                      | RPtr _, RPtr _  -> MinusPtrPtr
                      | _               -> failwith "unreachable" in
            AnnotatedExpr (BinOp (minus, cast_annot1, cast_annot2), result_ty)
        | Ast.Times ->
            AnnotatedExpr (BinOp (IntArithBinop Times, cast_annot1, cast_annot2), result_ty)
        | Ast.Div ->
            AnnotatedExpr (BinOp (IntArithBinop Div, cast_annot1, cast_annot2), result_ty)
        | Ast.Mod ->
            AnnotatedExpr (BinOp (IntArithBinop Mod, cast_annot1, cast_annot2), result_ty)
        | Ast.Eq ->
            AnnotatedExpr (BinOp (Comparison Eq, cast_annot1, cast_annot2), result_ty)
        | Ast.Ne ->
            AnnotatedExpr (Not (AnnotatedExpr (BinOp (Comparison Eq, cast_annot1, cast_annot2), RBool)), result_ty)
        | Ast.Lt ->
            AnnotatedExpr (BinOp (Comparison Lt, cast_annot1, cast_annot2), result_ty)
        | Ast.Le ->
            AnnotatedExpr (Not (AnnotatedExpr (BinOp (Comparison Lt, cast_annot2, cast_annot1), RBool)), result_ty)
        | Ast.Gt ->
            AnnotatedExpr (BinOp (Comparison Lt, cast_annot2, cast_annot1), result_ty)
        | Ast.Ge ->
            AnnotatedExpr (Not (AnnotatedExpr (BinOp (Comparison Lt, cast_annot1, cast_annot2), RBool)), result_ty)
        | Ast.And ->
            AnnotatedExpr (ShortCircuit (And, cast_annot1, cast_annot2), result_ty)
        | Ast.Or ->
            AnnotatedExpr (ShortCircuit (Or, cast_annot1, cast_annot2), result_ty)
        end

  | Ast.Call (loc, name, ast_args) ->
      begin match IdentMap.find_opt name names.nm_func_ids with
      | None ->
          err loc "unknown function name"
      | Some id ->
          let _sig = IdMap.find id env.env_func_sigs in
          let arg_annots = typecheck_args env names _sig.fs_arg_rich_types ast_args loc in
          let arg_annots = list_to_list_annotated_expr arg_annots in
          if IdentMap.mem name inbuilt_funcs then
            let func = IdentMap.find name inbuilt_funcs in
            AnnotatedExpr (CallInbuilt (func, arg_annots), _sig.fs_rich_return_type)
          else
            AnnotatedExpr (Call (id, arg_annots), _sig.fs_rich_return_type)
      end

  | Ast.Sizeof (loc, ty) ->
      begin match ty with
      | Ast.Void _ -> err loc "sizeof(void) is illegal"
      | _          -> AnnotatedExpr (Const (IntValue eight_int_value), RInt)
      end
  
and typecheck_args (env : env) (names : name_map) (argrich_types : rich_type list)
    (ast_args : Ast.expr list) (loc : Ast.loc) : annotated_expr list =
  match ast_args, argrich_types with
  | [], [] -> []
  | (ast_ex::ast_exs), (ty::tys) ->
      let annot = typecheck_expr env names ast_ex in
      let cast_annot = cast ty annot loc in
      let args = typecheck_args env names tys ast_exs loc in
      (cast_annot::args)
  | [], _ -> err loc "too few arguments"
  | _, [] -> err loc "too many arguments"


let rec ast_type_to_rich_type : Ast._type -> rich_type = function
  | Ast.Int _       -> RInt
  | Ast.Bool _      -> RBool
  | Ast.Void _      -> RVoid
  | Ast.Ptr (_, ty) -> RPtr (ast_type_to_rich_type ty)

(* convert an ast type to a  *)
let ast_type_to_complete_rich_type : Ast._type -> rich_type = function
  | Ast.Int _       -> RInt
  | Ast.Bool _      -> RBool
  | Ast.Ptr (_, ty) -> RPtr (ast_type_to_rich_type ty)
  | Ast.Void loc    -> err loc "incomplete type"

let typecheck_file (file : Ast.file) : (func_id * func) list * func_id =
  (* we keep those two "global" variables, the command type
     checker will add elemenst to them when it reads declarations *)

  (* maps variable ids to their types and function ids to thier signatures *)
  let env = ref empty_env in

  (* maps function ids to their bodies *)
  (* let func_bodies : cmd IdMap.t ref = ref IdMap.empty in *)

  let funcs : func IdMap.t ref = ref IdMap.empty in

  let rec typecheck_instr (parent_func_ids : func_id list) (local_var_ids : (var_id, unit) Hashtbl.t) (names : name_map) (unredefinable_names : IdentSet.t)
      (in_loop : bool) (return_ty : rich_type) : Ast.instr -> cmd = function
    | Ast.Expr (_, ast_expr) ->
        Expr (typecheck_expr !env names ast_expr)

    | Ast.If (loc, ast_cond, ast_body) ->
        typecheck_instr parent_func_ids local_var_ids names unredefinable_names in_loop return_ty
          (Ast.IfElse (loc, ast_cond, ast_body, Ast.NOP loc))

    | Ast.IfElse (loc, ast_cond, ast_then_body, ast_else_body) ->
        let cond = typecheck_expr !env names ast_cond in
        let then_body = typecheck_instr parent_func_ids local_var_ids names unredefinable_names in_loop return_ty ast_then_body in
        let else_body = typecheck_instr parent_func_ids local_var_ids names unredefinable_names in_loop return_ty ast_else_body in
        let cast_cond = cast RBool cond (Ast.expr_loc ast_cond) in
        If (cast_cond, then_body, else_body)

    | Ast.While (loc, ast_cond, ast_body) ->
        let cond = typecheck_expr !env names ast_cond in
        let body = typecheck_instr parent_func_ids local_var_ids names unredefinable_names true return_ty ast_body in
        let cast_cond = cast RBool cond (Ast.expr_loc ast_cond) in
        While (cast_cond, body)
    
    | Ast.For (loc, ast_var_decl_option, ast_cond_option, ast_incrs, ast_body) ->
        let (init_instr, body_names, body_unredefinable_names) =
          begin match ast_var_decl_option with
          | Some ast_var_decl -> typecheck_var_decl local_var_ids names IdentSet.empty ast_var_decl
          | None              -> (Skip, names, IdentSet.empty)
          end in
        let cond, cond_loc =
          begin match ast_cond_option with
          | Some ast_cond -> (typecheck_expr !env body_names ast_cond, Ast.expr_loc ast_cond)
          | None          -> (AnnotatedExpr (Const (IntValue one_int_value), RInt), loc)
          end in
        let cast_cond = cast RBool cond cond_loc in
        let incrs = List.map (typecheck_expr !env body_names) ast_incrs in
        let body = typecheck_instr parent_func_ids local_var_ids body_names body_unredefinable_names true return_ty ast_body in
        Seq (init_instr, For (cast_cond, list_to_list_annotated_expr incrs, body))

    | Ast.Break loc ->
        if in_loop
        then Break
        else err loc "break outside of loop"
    
    | Ast.Continue loc ->
        if in_loop
        then Continue
        else err loc "continue outside of loop"

    | Ast.Block (_, cmds_decls) ->
        typecheck_sequence parent_func_ids local_var_ids names IdentSet.empty in_loop return_ty cmds_decls

    | Ast.Return loc ->
        (* with default settings, an empty from a non void function
           is accepted by gcc but not by clang *)
        Return (default_return_value return_ty)

    | Ast.ReturnExpr (loc, ast_expr) ->
        let annot = typecheck_expr !env names ast_expr in
        let cast_annot = cast return_ty annot (Ast.expr_loc ast_expr) in
        Return cast_annot
      
    | Ast.NOP _ ->
        Skip

  (* typecheck a list of commands or declarations *)
  and typecheck_sequence (parent_func_ids : func_id list) (local_var_ids : (var_id, unit) Hashtbl.t) (names : name_map) (unredefinable_names : IdentSet.t)
      (in_loop : bool) (return_ty : rich_type) :
        Ast.instr_or_decl list -> cmd = function
    | [] -> Skip

    | Ast.DeclVar (_, decl) :: tail ->
        let (assign_instr, names_after, unredefinable_names_after) =
          typecheck_var_decl local_var_ids names unredefinable_names decl in
        Seq (assign_instr,
             typecheck_sequence parent_func_ids local_var_ids names_after unredefinable_names_after
                        in_loop return_ty tail)

    | Ast.DeclFunc (_, decl) :: tail ->
        let (names_after, unredefinable_names_after) =
          typecheck_func_decl parent_func_ids names unredefinable_names decl in
        typecheck_sequence parent_func_ids local_var_ids names_after unredefinable_names_after
            in_loop return_ty tail

    | Instr (_, cmd) :: tail ->
        Seq (typecheck_instr parent_func_ids local_var_ids names unredefinable_names in_loop return_ty
                    cmd,
             typecheck_sequence parent_func_ids local_var_ids names unredefinable_names in_loop return_ty
                    tail)

  and typecheck_var_decl (local_var_ids : (var_id, unit) Hashtbl.t) (names : name_map) (unredefinable_names : IdentSet.t) :
      Ast.var_decl -> cmd * name_map * IdentSet.t = function
    | Ast.VarDecl (loc, ast_ty, name, ast_def_option) ->
        if IdentSet.mem name unredefinable_names then
          err loc "cannot define variable, name already used"
        else begin
          let ty = ast_type_to_complete_rich_type ast_ty in
          let id = new_var_id env in
          Hashtbl.add local_var_ids id ();
          env := env_add_var id ty !env;
          let assign_instr =
            match ast_def_option with
            | Some ast_def ->
                let value =
                  cast ty (typecheck_expr !env names ast_def) (Ast.expr_loc ast_def) in
                Expr (AnnotatedExpr (Assign (AnnotatedLvalue (Var id, ty), value), ty))
            | None ->
                Skip in
          let new_names = name_map_add_var name id names in
          let new_unredefinable_names = IdentSet.add name unredefinable_names in
          (assign_instr, new_names, new_unredefinable_names)
        end

  and typecheck_func_decl (parent_func_ids : func_id list) (names : name_map) (unredefinable_names : IdentSet.t) :
      Ast.func_decl -> name_map * IdentSet.t = function
    | Ast.FuncDecl (loc, ast_ty, name, ast_arg_decls, ast_body) ->
        if IdentSet.mem name unredefinable_names then
          err loc "cannot define function, name already used"
        else begin
          let ty = ast_type_to_rich_type ast_ty in
          let id = new_func_id env in
          let local_var_ids : (var_id, unit) Hashtbl.t = Hashtbl.create 42 in
          let (names_inside, unredefinable_names_inside) =
            List.fold_left
              (fun (names, unredef) (ast_ty, name) ->
                let (_, names', unredef') =
                  typecheck_var_decl local_var_ids names unredef (Ast.VarDecl (loc, ast_ty, name, None)) in
                (names', unredef'))
              (names, IdentSet.singleton name)
              ast_arg_decls in
          let names_inside = name_map_add_func name id names_inside in
          let args =
            List.map
              (fun (ast_ty, name) ->
                let ty = ast_type_to_rich_type ast_ty in
                (ty, IdentMap.find name names_inside.nm_var_ids))
              ast_arg_decls in
          let _sig = { fs_rich_return_type = ast_type_to_rich_type ast_ty;
                       fs_arg_rich_types = map fst args } in
          env := env_add_func id _sig !env;
          let body_instr =
            typecheck_sequence (id::parent_func_ids) local_var_ids names_inside unredefinable_names_inside false ty ast_body in
          let body_instr = Seq (body_instr, Return (default_return_value ty)) in
          let local_var_ids_list = List.of_seq (Seq.map (fun (id, ()) -> id) (Hashtbl.to_seq local_var_ids)) in
          let func = { f_signature = _sig;
                        f_local_var_ids = local_var_ids_list;
                        f_local_var_types = List.map (fun id -> IdMap.find id (!env).env_var_types)
                                                     local_var_ids_list;
                        f_arg_var_ids = map snd args;
                        f_body = body_instr;
                        f_parent_func_ids = parent_func_ids } in
          funcs := IdMap.add id func !funcs;
          ( name_map_add_func name id names,
            IdentSet.add name unredefinable_names )
        end in
      
  let z = Ast.zero_loc in
  let malloc_decl = Ast.FuncDecl (z, (Ast.Ptr (z, Ast.Void z)), "malloc", [(Ast.Int z, "size")], [Ast.Instr (z, (Ast.NOP z))]) in
  let putchar_decl = Ast.FuncDecl (z, (Ast.Void z), "putchar", [(Ast.Int z, "char")], [Ast.Instr (z, (Ast.NOP z))]) in

  let (names, _) =
    List.fold_left
      (fun (names, unredef) decl -> typecheck_func_decl [] names unredef decl)
      (empty_name_map, IdentSet.empty)
      (malloc_decl::putchar_decl::file) in

  if not (IdentMap.mem "main" names.nm_func_ids)
  then raise (Linking_error "no function named main");

  Seq.iter (fun (id, func) -> print_int id; List.iter print_int func.f_arg_var_ids; print_newline ()) (IdMap.to_seq !funcs);
  Seq.iter (fun (id, func) -> print_int id; List.iter print_int func.f_local_var_ids; print_newline ()) (IdMap.to_seq !funcs);
  

  ( List.of_seq (IdMap.to_seq !funcs),
    IdentMap.find "main" names.nm_func_ids )
