open Ast
open Astlib
open Tctxt

(* Error Reporting ---------------------------------------------------------- *)
(* NOTE: Use type_error to report error messages for ill-typed programs. *)

exception TypeError of string

let type_error (l : 'a node) err =
  let (_, (s, e), _) = l.loc in
  raise (TypeError (Printf.sprintf "[%d, %d] %s" s e err))


(* initial context: G0 ------------------------------------------------------ *)
(* The Oat types of the Oat built-in functions *)
let builtins =
  [ "array_of_string",  ([TRef RString],  RetVal (TRef(RArray TInt)))
  ; "string_of_array",  ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", ([TRef RString],  RetVal TInt)
  ; "string_of_int",    ([TInt], RetVal (TRef RString))
  ; "string_cat",       ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     ([TRef RString],  RetVoid)
  ; "print_int",        ([TInt], RetVoid)
  ; "print_bool",       ([TBool], RetVoid)
  ]

(* binary operation types --------------------------------------------------- *)
let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)
  | Eq | Neq -> failwith "typ_of_binop called on polymorphic == or !="

(* unary operation types ---------------------------------------------------- *)
let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* subtyping ---------------------------------------------------------------- *)
(* Decides whether H |- t1 <: t2
    - assumes that H contains the declarations of all the possible struct types

    - you will want to introduce addition (possibly mutually recursive)
      helper functions to implement the different judgments of the subtyping
      relation. We have included a template for subtype_ref to get you started.
      (Don't forget about OCaml's 'and' keyword.)
*)

let rec subtype (c : Tctxt.t) (t1 : Ast.ty) (t2 : Ast.ty) : bool =
  match t1, t2 with
  | TBool, TBool -> true
  | TInt, TInt -> true
  | TRef rty1, TRef rty2 -> subtype_rty c rty1 rty2
  | TNullRef rty1, TNullRef rty2 -> subtype c (TRef rty1) (TRef rty2)
  | TRef rty1, TNullRef rty2 -> subtype c (TRef rty1) (TRef rty2)
  | _, _ -> false

(* Decides whether H |-r ref1 <: ref2 *)
and subtype_rty (c : Tctxt.t) (t1 : Ast.rty) (t2 : Ast.rty) : bool =
  match t1, t2 with
  | RString, RString -> true
  | RStruct id1, RStruct id2 ->
    let s1 = lookup_struct_option id1 c in
    let s2 = lookup_struct_option id2 c in
    begin
      match s1, s2 with
    | (Some fields1), (Some fields2) -> subtype_width c fields1 fields2 true
    | _ -> false
    end
  | RArray ty1, RArray ty2 ->
    begin
      match ty1, ty2 with
      | TRef(RArray _), TRef (RArray _) -> subtype c ty1 ty2
      | _ -> ty1 == ty2
    end
  | RFun (args1, t1), RFun (args2, t2) ->
    (args_subtype c args1 args2) && (subtype_ret_ty c t1 t2)
  | _, _ -> false

and subtype_width c fields1 fields2 flag : bool =
  match fields1, fields2 with
  | _, [] -> flag
  | h1 :: t1, h2 :: t2 ->
    if ((compare h1.fieldName h2.fieldName) == 0) && (h1.ftyp == h2.ftyp)
    then subtype_width c t1 t2 true
    else false
  | _, _ -> false

and args_subtype c args1 args2 : bool =
  if (List.length args1 == List.length args2)
  then List.fold_left2 (fun acc h1 h2 -> acc && (subtype c h2 h1)) true args1 args2
  else false

and subtype_ret_ty (c : Tctxt.t) (t1 : Ast.ret_ty) (t2 : Ast.ret_ty) : bool =
  match t1, t2 with
  | RetVoid, RetVoid -> true
  | RetVal t1, RetVal t2 -> subtype c t1 t2
  | _, _ ->  false



(* well-formed types -------------------------------------------------------- *)
(* Implement a (set of) functions that check that types are well formed according
   to the H |- t and related inference rules. Intuitively, this check can fail if an undefined reference appears as a component of `t`.

    - the function should succeed by returning () if the type is well-formed
      according to the rules

    - l is just an ast node that provides source location information for
      generating error messages (it's only needed for the type_error generation)

    - the function should fail using the "type_error" helper function if the
      type is not well formed. Use `l` to indicate the location in the error.

    - tc contains the structure definition context
 *)
let rec typecheck_ty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ty) : unit =
  match t with
  | TBool -> ()
  | TInt -> ()
  | TRef rty -> typecheck_rty l tc rty
  | TNullRef rty -> typecheck_rty l tc rty

and typecheck_rty (l : 'a Ast.node) (tc : Tctxt.t) (rty : Ast.rty) : unit =
  match rty with
  | RString -> ()
  | RStruct id ->
    let a = lookup_struct_option id tc in
    begin
      match a with
      | Some _ -> ()
      | None -> type_error l "ill-formed struct type"
    end
  | RArray ty -> typecheck_ty l tc ty
  | RFun (args, ret) ->
    List.fold_left (fun acc arg -> typecheck_ty l tc arg) () args;
    typecheck_ret_ty l tc ret


and typecheck_ret_ty (l : 'a Ast.node) (tc : Tctxt.t) (ret : Ast.ret_ty) : unit =
  match ret with
  | RetVoid -> ()
  | RetVal ty -> typecheck_ty l tc ty


(* A helper function to determine whether a type allows the null value *)
let is_nullable_ty (t : Ast.ty) : bool =
  match t with
  | TNullRef _ -> true
  | _ -> false

(* typechecking expressions ------------------------------------------------- *)
(* Typechecks an expression in the typing context c, returns the type of the
   expression.  This function should implement the inference rules given in the
   oat.pdf specification.  There, they are written:

       H; G; L |- exp : t

   See tctxt.ml for the implementation of the context c, which represents the
   four typing contexts: H - for structure definitions G - for global
   identifiers L - for local identifiers

   Returns the (most precise) type for the expression, if it is type correct
   according to the inference rules.

   Uses the type_error function to indicate a (useful!) error message if the
   expression is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   Notes: - Structure values permit the programmer to write the fields in any
   order (compared with the structure definition).  This means that, given the
   declaration struct T { a:int; b:int; c:int } The expression new T {b=3; c=4;
   a=1} is well typed.  (You should sort the fields to compare them.)

*)
let rec typecheck_exp (c : Tctxt.t) (e : Ast.exp node) : Ast.ty =
  match e.elt with
  | CBool _ -> TBool
  | CInt _ -> TInt
  | CNull rty -> let a = TNullRef rty in typecheck_ty e c a; a
  | CStr _ -> TRef RString
  | Id id ->
    begin
    match lookup_option id c with
      | Some x -> x
      | None -> type_error e ("wrong id " ^ id)
  end
  | CArr (ty, elist) ->
    typecheck_ty e c ty;
    let _ = List.fold_left (fun ty e ->
        let ty' = typecheck_exp c e in
        if (subtype c ty' ty)
        then ty
        else type_error e "array element is of wrong type")
        ty elist in
    TRef (RArray ty)
  | NewArr (ty, size) ->
    typecheck_ty e c ty;
    let size_ty = typecheck_exp c size in
    if size_ty == TInt
    then
    begin
      match ty with
      | TBool
      | TInt -> TRef (RArray ty)
      | TNullRef _ -> TRef (RArray ty)
      | _ -> type_error e "wrong type for NewArr"
    end
    else type_error e "non-integer array length"
  | NewArrInit (t1, e1, id, e2) ->
    typecheck_ty e c t1;
    let t2 = typecheck_exp c e1 in
    let c2 = add_local c id TInt in
    let t3 = typecheck_exp c2 e2 in
    if t2 = TInt
    then (if subtype c2 t3 t1
          then TRef (RArray t1)
          else type_error e  "wrong type for array initializer")
      else type_error e "non-integer length for newarrinit"
  | Index (arr, idx) ->
    let t1 = typecheck_exp c arr in
    let t2 = typecheck_exp c idx in
    begin
    match t1, t2 with
    | (TRef (RArray ty)), TInt -> ty
    | _, _ ->  type_error e "wrong types for array indexing"
  end
  | Length e ->
    begin
    match typecheck_exp c e with
    | TRef (RArray ty) -> TInt
    | _ -> type_error e "length for non-array"
  end
  | CStruct (id1, fields1) ->
    let a = lookup_struct_option id1 c in
    begin
    match a with
      | Some fields2 ->
        let m = List.fold_left
            (fun acc h ->
               let ty = typecheck_exp c (snd h) in
               let f = {fieldName= (fst h); ftyp = ty} in
               f :: acc) [] fields1 in
        let x = List.sort compare m in
        let y = List.sort compare fields2 in
        if List.length x == List.length y
        then
          begin
            let check = List.fold_left2 (fun flag h1 h2 ->
            let flag' = ((compare h1.fieldName h2.fieldName) == 0) &&
                        (subtype c h1.ftyp h2.ftyp) in
            flag' && flag) true x y in
            if check
            then TRef (RStruct id1)
            else type_error e ("fields do not match" ^ id1)
      end
        else type_error e ("number of fields does not match" ^ id1)
      | None -> type_error e "wrong struct type"
  end
  | Proj (e1, fname) ->
    let ty = typecheck_exp c e1 in
    begin
    match ty with
    | TRef(RStruct id) ->
      let s1 = lookup_struct_option id c in
      begin
        match s1 with
        | Some fields ->
          let a = lookup_field_option id fname c in
          (match a with
           | Some ty -> ty
           | None -> type_error e "field does't exist in struct" )
        | None -> type_error e "struct for field does not exist"
      end
    | _ -> type_error e "field of non-struct"
  end
  | Call (e1, elist) -> (* REVISIT RETURN TYPE*)
    let f = typecheck_exp c e1 in
    begin
    match f with
    | TRef (RFun (args1, ret)) ->
      let args2 = List.map (fun exp -> typecheck_exp c exp) elist in
      if (args_subtype c args1 args2)
      then
        match ret with
        | RetVal ty -> ty
        | _ ->  type_error e "expression does not return"
      else type_error e "wrong type for function arguments"
    | _ -> type_error e "non-function is called"
  end
  | Bop (bop, e1, e2) ->
    let ty1, ty2 = (typecheck_exp c e1), (typecheck_exp c e2) in
    begin
      match bop with
      | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr ->
        if ((ty1 == TInt) && (ty2 == TInt))
        then TInt
        else  type_error e "integer binary operation applied on non-integer"
      | Lt | Lte | Gt | Gte ->
        if ((ty1 == TInt) && (ty2 == TInt))
        then TBool
        else  type_error e "integer binary operation applied on non-integer"
      | And | Or ->
        if ((ty1 == TBool) && (ty2 == TBool))
        then TBool
        else  type_error e "boolean binary operation applied on non-boolean"
      | Eq | Neq ->
        if (subtype c ty2 ty1) && (subtype c ty1 ty2)
        then TBool
        else  type_error e "equality comparison applied to expressions of two different types"
    end
  | Uop (uop, e) ->
    let ty = typecheck_exp c e in
    let a, b = typ_of_unop uop in
    if ty == a then b else type_error e "uop applied to wrong type"

(* statements --------------------------------------------------------------- *)

(* Typecheck a statement
   This function should implement the statment typechecking rules from oat.pdf.

   Inputs:
    - tc: the type context
    - s: the statement node
    - to_ret: the desired return type (from the function declaration)

   Returns:
     - the new type context (which includes newly declared variables in scope
       after this statement)

     - A boolean indicating the return behavior of a statement:
        false:  might not return
        true:   definitely returns

        in the branching statements, the return behavior of the branching
        statement is the conjunction of the return behavior of the two
        branches: both both branches must definitely return in order for
        the whole statement to definitely return.

        Intuitively: if one of the two branches of a conditional does not
        contain a return statement, then the entire conditional statement might
        not return.

        looping constructs never definitely return

   Uses the type_error function to indicate a (useful!) error message if the
   statement is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   - You will probably find it convenient to add a helper function that implements the
     block typecheck rules.
*)

let rec typecheck_stmt (tc : Tctxt.t) (s:Ast.stmt node) (to_ret:ret_ty) : Tctxt.t * bool =
  match s.elt with
  | Assn(lhs, exp) ->
    begin
    match lhs.elt with
      | Id id ->
        let t1 = typecheck_exp tc lhs in
        begin
          match lookup_local_option id tc with
          | None ->
            begin
              match lookup_global_option id tc with
              | Some (TRef (RFun _)) -> type_error s "lhs is a global function id"
              | _ -> let t2 = typecheck_exp tc exp in
                if (subtype tc t2 t1)
                then tc, false
                else  type_error s ("lhs and exp of different types in id assignment " ^ id)
        end
          | _ -> let t2 = typecheck_exp tc exp in
            if (subtype tc t2 t1)
            then tc, false
            else  type_error s ("lhs and exp of different types in id assignment " ^ id)
        end
      | Index (e1, e2) ->
        let t1 = typecheck_exp tc lhs in
        let t2 = typecheck_exp tc exp in
        if  (subtype tc t2 t1)
        then tc, false
        else  type_error s "lhs and exp of different types in index assignment"
      | Proj (e1, id) ->
        let t1 = typecheck_exp tc lhs in
        let t2 = typecheck_exp tc exp in
        if  (subtype tc t2 t1)
        then tc, false
        else  type_error s "lhs and exp of different types in struct assignment"
      | _ -> type_error s "assignment to wrong type"
  end
  | Decl (id, e) ->
    begin
    match lookup_local_option id tc with
    | Some _ -> type_error s "variable already exists"
    | None -> let ty = typecheck_exp tc e in
      let tc' = add_local tc id ty in
      tc', false
  end
  | Ret (e_opt) ->
    begin
      match e_opt with
      | Some exp ->
        begin
        match to_ret with
        | RetVoid ->  type_error s "function does not return"
        | RetVal ty ->
          let ty' = typecheck_exp tc exp in
          if (subtype tc ty' ty)
          then (tc, true)
          else  type_error s "type of exp different from return type"
      end
      | None ->
        begin
        match to_ret with
        | RetVoid ->  tc, true
        | RetVal ty -> type_error s "return expression not provided"
      end
    end
  | SCall (e1, elist) -> (* REVISIT not sure if return is same as overall return*)
    let f = typecheck_exp tc e1 in
    begin
    match f with
    | TRef (RFun (args1, ret)) ->
      let args2 = List.map (fun exp -> typecheck_exp tc exp) elist in
      if (args_subtype tc args1 args2)
      then
        begin
          if ret = RetVoid
          then tc, false
          else  type_error s "wrong return type"
        end
      else type_error s "wrong type for function arguments"
    | _ -> type_error s "non-function is called"
  end
  | If (e1, block1, block2) ->
    let ty1 = typecheck_exp tc e1 in
    if ty1 == TBool
    then
      begin
        let _, r1 = typecheck_block tc block1 to_ret in
        let _, r2 = typecheck_block tc block2 to_ret in
        let u = (r1 && r2) in
        tc, u
      end
    else  type_error s "condition for if is non-boolean"
  | While (exp, block) ->
    let ty1 = typecheck_exp tc exp in
    if ty1 == TBool
    then let _ = typecheck_block tc block to_ret in
      tc, false
    else type_error s "condition for while is non-boolean"
  | For (vlist, exp, s', block) ->
    let ds = List.map (fun d -> no_loc (Decl d)) vlist in
    let c1, r = typecheck_block tc ds to_ret in
    let guard = match exp with Some e -> e | None -> no_loc (CBool true) in
    let after = match s' with Some s -> [s] | None -> [] in
    let ty1 = typecheck_exp c1 guard in
    if ty1 == TBool
    then
      begin
        let _ = typecheck_block c1 block to_ret in
        let _ = typecheck_block c1 after to_ret in
        tc, false
      end
    else type_error s "condition for for-loop is non-boolean"
  | Cast (rty, id, e, block1, block2) ->
    let ty = typecheck_exp tc e in
    let rty2 = match ty with TNullRef a -> a | _ -> type_error s "exp is not nullable" in
    if (subtype tc (TRef rty2) (TRef rty))
    then
      begin
        let tc' = add_local tc id (TRef rty2) in
        let _, r1 = typecheck_block tc' block1 to_ret in
        let _, r2 = typecheck_block tc block2 to_ret in
        let u = (r1 && r2) in
        tc, u
      end
    else type_error s "wrong rty for cast"

and typecheck_block (tc : Tctxt.t) (block:Ast.block) (to_ret:ret_ty) : Tctxt.t * bool =
  let ctxt, rlist =
    List.fold_left (fun (c, flags) s ->
        let c', flag' = typecheck_stmt c s to_ret in
        (c', flag' :: flags)) (tc, []) block in
  ctxt, check_return (List.rev rlist)

and check_return lst =
  match lst with
  | [] -> false
  | [h] -> h
  | h :: t -> (*h || check_return t *)
    if h then raise (TypeError "early return") else check_return t

(* struct type declarations ------------------------------------------------- *)
(* Here is an example of how to implement the TYP_TDECLOK rule, which is
   is needed elswhere in the type system.
 *)

(* Helper function to look for duplicate field names *)
let rec check_dups fs =
  match fs with
  | [] -> false
  | h :: t -> (List.exists (fun x -> x.fieldName = h.fieldName) t) || check_dups t

let typecheck_tdecl (tc : Tctxt.t) id fs  (l : 'a Ast.node) : unit =
  if check_dups fs
  then type_error l ("Repeated fields in " ^ id)
  else List.iter (fun f -> typecheck_ty l tc f.ftyp) fs

(* function declarations ---------------------------------------------------- *)
(* typecheck a function declaration
    - extends the local context with the types of the formal parameters to the
      function
    - typechecks the body of the function (passing in the expected return type
    - checks that the function actually returns
*)

let rec check_dups_fdecl arg_names =
  match arg_names with
  | [] -> false
  | h :: t -> (List.exists (fun x -> (snd x) = (snd h)) t) || check_dups_fdecl t

let typecheck_fdecl (tc : Tctxt.t) (f : Ast.fdecl) (l : 'a Ast.node) : unit =
  if check_dups_fdecl f.args
  then type_error l ("Repeated args in " ^ f.fname)
  else
    begin
      let tc2 = List.fold_left (fun tc' h -> add_local tc' (snd h) (fst h)) tc f.args in
      let tc3, r = typecheck_block tc2 f.body f.frtyp in
      if r then () else type_error l ("function does not return: " ^ f.fname)
    end

(* creating the typchecking context ----------------------------------------- *)

(* The following functions correspond to the
   judgments that create the global typechecking context.

   create_struct_ctxt: - adds all the struct types to the struct 'S'
   context (checking to see that there are no duplicate fields

     H |-s prog ==> H'


   create_function_ctxt: - adds the the function identifiers and their
   types to the 'G' context (ensuring that there are no redeclared
   function identifiers)

     H ; G1 |-f prog ==> G2


   create_global_ctxt: - typechecks the global initializers and adds
   their identifiers to the 'G' global context

     H ; G1 |-g prog ==> G2


   NOTE: global initializers may mention function identifiers as
   constants, but can mention only other global values that were declared earlier
*)

let g0 = List.map (fun (id, (args, ret)) -> id, (TRef (RFun (args, ret)))) builtins

let create_struct_ctxt (p:Ast.prog) : Tctxt.t =
  List.fold_left (fun tc p ->
      match p with
      | Gtdecl ({elt=(id, fs)} as l) ->
        begin
        match lookup_struct_option id tc with
          | Some _  -> type_error l ("struct already exists" ^ id)
          | None -> add_struct tc id fs
      end
      | _ -> tc) ({locals = [];
                  globals = g0;
                   structs = []}) p

let get_f  (l : 'a Ast.node) (tc : Tctxt.t) (f:fdecl): id * ty =
  let id = f.fname in
  let ret = f.frtyp in
  let args = List.map fst f.args in
  typecheck_ret_ty l tc ret;
  List.iter (typecheck_ty l tc) args;
  id, (TRef (RFun (args, ret)))

let create_function_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  List.fold_left (fun tc' p ->
      match p with
      | Gfdecl ({elt=f} as l) ->
        let id, ty = get_f l tc' f in
        begin
        match lookup_global_option id tc' with
          | Some _  ->  type_error l ("function already exists: " ^ f.fname)
          | None -> add_global tc' id ty
      end
      | _ -> tc') tc p

let create_global_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  List.fold_left (fun tc' p ->
      match p with
      | Gvdecl ({elt=g} as l) ->
        let id = g.name in
        let ty = typecheck_exp tc' g.init in
        begin
        match lookup_global_option id tc' with
          | Some _  ->  type_error l ("global variable already exists: " ^ id)
          | None -> add_global tc' id ty
      end
      | _ -> tc') tc p


(* This function implements the |- prog and the H ; G |- prog
   rules of the oat.pdf specification.
*)
let typecheck_program (p:Ast.prog) : unit =
  let sc = create_struct_ctxt p in
  let fc = create_function_ctxt sc p in
  let tc = create_global_ctxt fc p in
  List.iter (fun p ->
    match p with
    | Gfdecl ({elt=f} as l) -> typecheck_fdecl tc f l
    | Gtdecl ({elt=(id, fs)} as l) -> typecheck_tdecl tc id fs l
    | _ -> ()) p
