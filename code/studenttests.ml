open Assert
open Ast
open Typechecker
open Ll

(* These tests are provided by you -- they will be graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)




let aiman_unit_tests = [
  "typecheck_for loop good",
  (fun () ->
     let id = "x" in
     let vlist = [id, (no_loc (CInt Int64.zero))] in
     let exp = no_loc (Ast.Bop (Ast.Lt, (no_loc (Ast.Id id)),
                                (no_loc (CInt (Int64.of_int 10)))  )) in
     let stmt = no_loc (Assn ((no_loc (Ast.Id id)),
                           no_loc (Bop (Add, (no_loc (Ast.Id id)),
                                        (no_loc (CInt Int64.one)))) )) in
     let slist = [] in
     let for_stmt = no_loc (Ast.For (vlist, Some exp, Some stmt, slist)) in
     let check = Typechecker.typecheck_stmt Tctxt.empty for_stmt (RetVal TInt) in
     if not (snd check) then ()  else failwith "should not fail"
  ); ("typecheck_for loop bad",
  (fun () ->
     let id = "x" in
     let vlist = [id, (no_loc (CInt Int64.zero))] in
     let exp = no_loc (Ast.Bop (Ast.Add, (no_loc (Ast.Id id)),
                                (no_loc (CInt (Int64.of_int 1)))  )) in
     let stmt = no_loc (Assn ((no_loc (Ast.Id id)),
                           no_loc (Bop (Add, (no_loc (Ast.Id id)),
                                        (no_loc (CInt Int64.one)))) )) in
     let slist = [] in
     let for_stmt = no_loc (Ast.For (vlist, Some exp, Some stmt, slist)) in
     try
       if snd (Typechecker.typecheck_stmt Tctxt.empty for_stmt (RetVal TInt))
       then failwith "Should not succeed"
     with
       _ -> ()
     ))
  ]

(*let aiman_oat_test =
  [("hw5programs/array_test.oat", "", "00")]*)

let provided_tests : suite = [
    Test("Unit tests", aiman_unit_tests);
    (*    Test("Array Test", executed_oat_file aiman_oat_test *)
]


