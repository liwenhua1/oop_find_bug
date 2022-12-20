(******************************************)
(* command line processing                *)
(******************************************)
open Iparser
open Iprinter
open Ilexer
open Globals
open Iast


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

let oop_verification_aux (decl: Iast.proc_decl) = 
	let {proc_name; _ } = decl in 
	print_string (proc_name)
;;


let oop_verification (decl:Iast.prog_decl) = 
	print_string ("lalalallallalal\n");
	let {prog_data_decls; prog_enum_decls; prog_view_decls;  prog_proc_decls; _ } =  decl in 
	List.map (fun a -> oop_verification_aux a) prog_proc_decls 
;;
	


	  
let () =
	let source_files = ["test.ss"] in
  let r = List.map parse_file_full source_files in
	(* let r1 = List.map Astsimp.trans_prog prog in *)
  let _ = List.map print_string (List.map Iprinter.string_of_program r) in 
	let _ = List.map (fun a -> oop_verification a) r in 
	(* Tpdispatcher.print_stats (); *)
	()
	
	  

