(******************************************)
(* command line processing                *)
(******************************************)
open Iparser
open Iprinter
open Ilexer
open Globals

(******************************************)
(* main function                          *)
(******************************************)

let parse_file_full file_name = 
  let org_in_chnl = open_in file_name in
  let input = Lexing.from_channel org_in_chnl in
    try
		print_string "Parsing... ";
		let prog = Iparser.program (Ilexer.tokenizer file_name) input in
		  close_in org_in_chnl;
			prog 
    with
		End_of_file -> exit 0	  

	  
let () =
	let source_files = ["test.ss"] in
  let r = List.map parse_file_full source_files in
	(* let r1 = List.map Astsimp.trans_prog prog in *)
  let _ = List.map print_string (List.map Iprinter.string_of_program r) in 
	(* Tpdispatcher.print_stats (); *)
	()
	
	  

