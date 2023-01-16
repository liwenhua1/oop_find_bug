

let rec input_lines file =
  match try [input_line file] with End_of_file -> [] with
   [] -> []
  | [line] -> (String.trim line) :: input_lines file
  | _ -> failwith "Weird input_line return value"


let postprocess (source: string) : string = source

  (*let partitions = Str.split (Str.regexp "Entail 1:") source in 
  match partitions with 
  | [] -> raise (Foo "no entaimemt results")
  | [x] -> raise (Foo "no entaimemt results")
  | _::x::rest ->  
    (
      let partitions1 = Str.split (Str.regexp "Stop z3") x in 
      match partitions1 with 
      | [] -> raise (Foo "no stopping z3")
      | x :: rest -> x 
    )
*)



let _ = 
  let inFile =  "sleek_inp.slk" in
  let outFile = Sys.getcwd () ^ "/answerSleek.txt" in 
  
  let oc = open_out inFile in    (* 新建或修改文件,返回通道 *)
      (*print_string (declear^assertions^"\n************\n");   (* 写一些东西 *)
*)
      close_out oc;                (* 写入并关闭通道 *)
      ignore (Sys.command ("./sleek "^ inFile ^" > " ^ outFile));
      let ic = open_in outFile in
      try 
        let lines =  (input_lines ic ) in 
        let line = List.fold_right (fun x acc -> acc ^ "\n" ^ x) (List.rev lines) "" in
        print_string (postprocess line);
        close_in ic ;                 (* 关闭输入通道 *) 

      with e ->                      (* 一些不可预见的异常发生 *)
      close_in_noerr ic;           (* 紧急关闭 *)
      raise e                      (* 以出错的形式退出: 文件已关闭,但通道没有写入东西 *)
      
;;