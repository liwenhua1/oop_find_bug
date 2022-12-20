(******************************************)
(* command line processing                *)
(******************************************)
open Iparser
open Iprinter
open Ilexer
open Globals
open Iast

exception Foo of string


(******************************************)
(* main function                          *)
(******************************************)

let parse_file_full file_name : Iast.prog_decl = 
  let org_in_chnl = open_in file_name in
  let input = Lexing.from_channel org_in_chnl in
    try
		print_string "Parsing... ";
		let prog = Iparser.program (Ilexer.tokenizer file_name) input in
		  close_in org_in_chnl;
			prog 
    with
		End_of_file -> exit 0	  

let kind_of_Exp exp : string = 
	match exp with 
	| Return _ -> "Return"
	| Assert _ -> "Assert"
  | Assign _ -> "Assign"
  | Binary _ -> "Binary"
  | Bind _ -> "Bind"
  | Block _ -> "Block"
  | BoolLit _ -> "BoolLit"
  | Break _ -> "Break"
  | CallRecv _ -> "CallRecv"
  | CallNRecv _ -> "CallNRecv"
  | Cast _ -> "Cast"
  | Cond _ -> "Cond"
  | ConstDecl _ -> "ConstDecl"
  | Continue _ -> "Continue"
  | Debug _ -> "Debug"
  | Dprint _ -> "Dprint"

  | Empty _ -> "Empty"
  | FloatLit _ -> "FloatLit"
  | IntLit _ -> "IntLit"
  | Java _ -> "Java"
  | Member _ -> "Member"
  | New _ -> "New"
  | Null _ -> "Null"
  | Seq _ -> "Seq"
  | This _ -> "This"
(*  | Throw of exp_throw *)
  | Unary _ -> "Unary"
  | Unfold _ -> "Unfold"
  | Var _ -> "Var"
  | VarDecl _ -> "VarDecl"
  | While _ -> "While"


let rec oop_verification_method_aux env decl expr current : (specs * specs) list = 
	match expr with
	| _ -> print_string (kind_of_Exp expr); current 


(*
	| _ -> raise (Foo ("oop_verification_method_aux not yet " ^ kind_of_Exp expr))

	| Return rtn -> 
	| Assert of exp_assert
  | Assign of exp_assign
  | Binary of exp_binary
  | Bind of exp_bind
  | Block of exp_block
  | BoolLit of exp_bool_lit
  | Break of loc
  | CallRecv of exp_call_recv
  | CallNRecv of exp_call_nrecv
  | Cast of exp_cast
  | Cond of exp_cond
  | ConstDecl of exp_const_decl
  | Continue of loc
  | Debug of exp_debug
  | Dprint of exp_dprint
  | Empty of loc
  | FloatLit of exp_float_lit
  | IntLit of exp_int_lit
  | Java of exp_java
  | Member of exp_member
  | New of exp_new
  | Null of loc
  | Seq of exp_seq
  | This of exp_this
(*  | Throw of exp_throw *)
  | Unary of exp_unary
  | Unfold of exp_unfold
  | Var of exp_var
  | VarDecl of exp_var_decl
  | While of exp_while
	*)

	;;

let oop_verification_method (env:Iast.data_decl) (decl: Iast.proc_decl) : string = 
	match decl.proc_body with 
	| None -> raise (Foo "oop_verification_method not yet")
	| Some exp -> 
		let initalState = decl.proc_static_specs in 
		let startTimeStamp = Unix.time() in
		let final = oop_verification_method_aux env decl exp initalState in
		let startTimeStamp01 = Unix.time() in 
		("\n\n========== Module: "^ decl.proc_name ^ " in Object " ^ env.data_name ^" ==========\n" ^
		"[Pre  Condition] " ^ string_of_form_list decl.proc_static_specs ^"\n"^ 
		"[Post Condition] " ^ string_of_form_list decl.proc_dynamic_specs ^"\n"^ 
		"[Inferred Post Effects] " ^ string_of_form_list final  ^"\n"^
		"[Reasoning Time] " ^ string_of_float ((startTimeStamp01 -. startTimeStamp) *.1000000.0)^ " us" ^"\n" 
		)

	;;

let oop_verification_object (decl: Iast.data_decl) = 
	let rec helper li = 
		match li with 
		| [] -> ""
		| meth :: restMeth -> 
			let msg = oop_verification_method decl meth in 
			msg ^ helper restMeth
	in print_string (helper decl.data_methods)
;;


let oop_verification (decl:Iast.prog_decl) = 
	print_string ("Verifying... \n");
	List.map (fun a -> oop_verification_object a) decl.prog_data_decls 
;;
	


	  
let () =
	let source_files = ["test.ss"] in
  let r = List.map parse_file_full source_files in
	(* let r1 = List.map Astsimp.trans_prog prog in *)
  let _ = List.map print_string (List.map Iprinter.string_of_program r) in 
	let _ = List.map (fun a -> oop_verification a) r in 
	(* Tpdispatcher.print_stats (); *)
	()
	
	  

