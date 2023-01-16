let rec input_lines file =
  match try [input_line file] with End_of_file -> [] with
   [] -> []
  | [line] -> (String.trim line) :: input_lines file
  | _ -> failwith "Weird input_line return value"

let helper key = 
  (if String.compare key "1" == 0 then 
"ERROR : fixcalc cannot be found!!

!!! **src/tpdispatcher.ml#492:init_tp by default:
!!! **src/tpdispatcher.ml#391:set_tp z3Starting z3...

!!! **WARNING****src/sleek.ml#494:[./prelude.slk,examples/working/sleek/oop.slk]
Entail 1: Fail.(must) cause: true |-  false. LOCS:[0] (RHS: contradiction)

Residue:

 MustErr Context:
   fe_kind: MUST
   fe_name: logical bug
   fe_locs: {
     fc_message:  true |-  false. LOCS:[0] (RHS: contradiction)
     fc_current_lhs_flow: {FLOW,(4,5)=__norm#E}
   }
 [[empty]]
 CEX:false

Stop z3... 2 invocations
SAT Count   : 1
SAT % Hit   : 0.%
IMPLY Count : 2
IMPLY % Hit : 50.%
Time(cache overhead) : 0.000426 (seconds)

0 false contexts at: ()"

else "ERROR : fixcalc cannot be found!!

!!! **src/tpdispatcher.ml#492:init_tp by default:
!!! **src/tpdispatcher.ml#391:set_tp z3Starting z3...

!!! **WARNING****src/sleek.ml#494:[./prelude.slk,examples/working/sleek/oop.slk]
Entail 1: Valid.

Residue:


Starting Omega.../usr/local/bin/oc
 <1>emp&temp=v & temp1=v+1&{FLOW,(4,5)=__norm#E}[]
[[ SEARCH ==>  Match(this,this)]]



Stop z3... 5 invocations
Stop Omega... 2 invocations
SAT Count   : 2
SAT % Hit   : 0.%
IMPLY Count : 3
IMPLY % Hit : 0.%
Time(cache overhead) : 0.000754 (seconds)

0 false contexts at: ()

!!! log(small):(0.010177,8)
!!!
 log(bigger)(>4s)(1):(5.,[(simplify:6<1:Z3,5.)])
Total verification time: 0.067782 second(s)
        Time spent in main process: 0.055134 second(s)
        Time spent in child processes: 0.012648 second(s)")



let _ = (*print_endline "Hello world!" in *)
  let inputfile = (Sys.getcwd () ^ "/" ^ Sys.argv.(1)) in
  let ic = open_in inputfile in
  try
      let lines =  (input_lines ic ) in 
      let line = List.fold_right (fun x acc -> acc ^ "" ^ x) (List.rev lines) "" in
      let getPrint = helper line in 
      print_string (getPrint ^"\n");
      flush stdout;                (* 现在写入默认设备 *)
      close_in ic                  (* 关闭输入通道 *)

    with e ->                      (* 一些不可预见的异常发生 *)
      close_in_noerr ic;           (* 紧急关闭 *)
      raise e                      (* 以出错的形式退出: 文件已关闭,但通道没有写入东西 *)

   ;;

      







  