(******************************************)
(* command line processing                *)
(******************************************)
open Iparser
open Iprinter
open Ilexer
open Globals
open Iast
open Ipure


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
  | Instance _ -> "Instance"


(* let lookup_Field_In_Object obj (field:ident) : int = 
  let ctx = obj.data_fields in 
  let rec helper li (acc:int) = 
    match li with 
    | [] -> raise (Foo (field ^ " does not exits in " ^ obj.data_name ))
    | ((_, x), _) :: xs -> if String.compare x field == 0 then acc else helper xs (acc +1 )
  in helper ctx (0)
;;

let retriveValueFromCurrent (spec:Iast.F.formula) index: P.exp = 
  match spec with 
  | Iast.F.Base {formula_base_heap; _ } -> 
    (match formula_base_heap with
    | Heapdynamic {h_formula_heap_node; h_formula_heap_content; _ } -> 
      let rec helper (li:(P.exp list)) acc :P.exp = 
       (
          match li with 
          | [] -> raise (Foo "mismatched filed")
          | p :: xs -> if acc = 0 then p 
          else helper xs (acc-1)
        )
      in helper (snd (List.hd h_formula_heap_content)) index 

    | _ -> raise (Foo "retriveValueFromCurrent-Base")
    )


  | _ -> raise (Foo "retriveValueFromCurrent")
  ;; *)

  let rec retriveContentfromNode (spec:Iast.F.h_formula) name = 
    match spec with 
     | Heapdynamic {h_formula_heap_node; h_formula_heap_content; _ } -> 
        if (String.compare (fst h_formula_heap_node) name == 0) then (true, h_formula_heap_content)
        else (false, h_formula_heap_content)
     | Star {h_formula_star_h1; h_formula_star_h2;_} -> 
      let (r1,r2) = retriveContentfromNode h_formula_star_h1 name in
        if r1 == true then (true, r2)
        else let (r1,r2) = retriveContentfromNode h_formula_star_h2 name in
             if r1 == true then (true, r2)
             else (false, r2)
     | _ -> raise (Foo "retriveValueFromCurrent")
    ;;

let rec retriveContentfromPure (spec:formula) name =
      match spec with
       | Ipure.BForm (Eq (Var ((v1,pr),p1), b, p2))  -> if (String.compare v1 name == 0) then (true, b) else (false, b )
       | Ipure.BForm a -> (false, Null {
        pos_fname = "";
        pos_lnum =1;
        pos_bol =1;
        pos_cnum =1;
      } )
       | Ipure.And (a,b,_) -> let (r1 ,r2) = retriveContentfromPure a name in 
            if r1 == true then (true, r2) else let (r1 ,r2) = retriveContentfromPure b name in
            if r1 == true then (true, r2) else (false, r2)
       | Ipure.Or (a,b,_) -> let (r1 ,r2) = retriveContentfromPure a name in 
            if r1 == true then (true, r2) else let (r1 ,r2) = retriveContentfromPure b name in
            if r1 == true then (true, r2) else (false, r2)
       | _ ->  raise (Foo ( "other Pure formula "))

       ;;

let up_down_cast spec type_to_ckeck = 
      match type_to_ckeck with 
       | Named a -> List.fold_right (fun (x,y) rs -> if Iast.sub_type (Named x) (Named a) then (rs && true) else false) spec true
       | _ -> raise (Foo "writeToCurrentSpec mismatched filed")
      ;;

let update_pure (spec:Iast.F.formula) (formu:Ipure.formula) po=
  match spec with
   | Base { formula_base_heap = h; formula_base_pure = p; formula_base_pos = po } -> let new_p = Ipure.And (p, formu, po)  in
     Iast.F.Base {formula_base_heap = h; formula_base_pure = new_p; formula_base_pos = po }
   | _ -> raise (Foo "writeToCurrentSpec mismatched filed")
   ;;

let retrive_content_from_list node feild = 
  let helper c_list f=  List.fold_right (fun (a,b) acc -> if (String.compare a f == 0) then [b] @ acc else acc ) c_list []  in
  List.hd (List.fold_right (fun (a,b) res -> let r = helper b feild in if List.length r == 1 then r else []) node [])

let update_content_list c_list feild value = 
  List.fold_right (fun (a,b) acc -> if (String.compare a feild == 0) then [(a,value)] @ acc else [(a,b)] @ acc) c_list [] 
let rec update_heap (spec:Iast.F.h_formula) var f value = 
  match spec with 
     | Heapdynamic {h_formula_heap_node = n; h_formula_heap_content = c; h_formula_heap_pos = po } -> 
        if (String.compare (fst n) var == 0) then 
          let res = List.fold_right (fun (a,b) acc -> acc @ [(a, update_content_list b f value)]) c [] in
          Iast.F.Heapdynamic {h_formula_heap_node = n; h_formula_heap_content = res; h_formula_heap_pos = po }
        else spec
     | Star {h_formula_star_h1 = h1; h_formula_star_h2 = h2; h_formula_star_pos=po} -> 
       Iast.F.Star {h_formula_star_h1 = update_heap h1 var f value; h_formula_star_h2 = update_heap h2 var f value; h_formula_star_pos=po}
     | _ -> raise (Foo "retriveValueFromCurrent")
    ;;

(*let writeToCurrentSpec (spec:Iast.F.formula) (index:int) (value:P.exp) : Iast.F.formula = 
  match spec with 
  | Iast.F.Base {formula_base_heap; formula_base_pure; formula_base_pos} -> 
    (match formula_base_heap with
    | Heapdynamic {h_formula_heap_node; h_formula_heap_content; h_formula_heap_pos } -> 

      let rec helper (li:(P.exp list)) acc :(P.exp list) = 
       (
          match li with 
          | [] -> raise (Foo "writeToCurrentSpec mismatched feild")
          | p :: xs -> if acc = 0 then value :: xs 
          else p :: (helper xs (acc-1))
        )
      in 
        let temp = helper (snd (List.hd h_formula_heap_content)) index in 

        let heap' = (fst (List.hd h_formula_heap_content) , temp) :: (List.tl h_formula_heap_content) in 
        Iast.F.Base{formula_base_heap= Heapdynamic{ h_formula_heap_node=h_formula_heap_node; h_formula_heap_content=heap' ; h_formula_heap_pos=h_formula_heap_pos}; formula_base_pure=formula_base_pure; formula_base_pos=formula_base_pos}
      

    | _ -> raise (Foo "writeToCurrentSpec-Base")
    )


  | _ -> raise (Foo "writeToCurrentSpec")
  ;; *)

(* let (stack:((ident * P.exp) list ref)) = ref []   *)


(* let updateStack id (value:P.exp) = 
  let temp = !stack in 
  let rec helper (li: (ident * P.exp) list) : (ident * P.exp) list  = 
    match li with 
    | [] -> [(id, value)]
    | (y, id') :: xs -> 
      if String.compare y id == 0 then (y, value) :: xs
      else (y, id') :: (helper xs)
  in stack := helper temp 
  ;;

let retriveStack exp_var_name : P.exp = 
  let temp = !stack in 
  let rec helper (li: (ident * P.exp) list) : P.exp = 
    match li with 
    | [] -> raise (Foo (exp_var_name ^ " is undefined "))
    | (y, id') :: xs -> 
      if String.compare y exp_var_name == 0 then id' 
      else (helper xs)
  in helper temp 
;; *)

let retriveheap (spec:Iast.F.formula) = match spec with 
    | Iast.F.Base {formula_base_heap; _ } -> formula_base_heap
    | _ -> raise (Foo ( "other F formula "))
;;

let retrivepure (spec:Iast.F.formula) = match spec with 
    | Iast.F.Base {formula_base_pure} -> formula_base_pure
    | _ -> raise (Foo ( "other F formula "))
;;

let null_test spec var_name = 
  let (r1,r2) = retriveContentfromNode (retriveheap spec) var_name in
  if r1 == false then let (res1,res2) = retriveContentfromPure (retrivepure spec) var_name in
     if res1 == true then if Ipure.is_null res2 then true else false
     else false
  else false 
;;

let rec oop_verification_method_aux obj decl expr (current:specs) : specs = 
match current with 
| Err a -> Err a
| Ok current' -> 

	(match expr with
  
  | Block {exp_block_body; _ } -> oop_verification_method_aux obj decl exp_block_body current
  
  | Seq {exp_seq_exp1; exp_seq_exp2; _ } -> 
    let temp = oop_verification_method_aux obj decl exp_seq_exp1 current in 
    oop_verification_method_aux obj decl exp_seq_exp2 temp 

  (* Read *)
  | VarDecl {exp_var_decl_type; exp_var_decl_decls; _} -> 
    let (id, expO, loc) = List.hd exp_var_decl_decls in 
    (match expO with 
    | None -> let form = Ipure.BForm (Eq (Var ((id , Unprimed), loc), Null loc, loc)) in
          (Ok (update_pure current' form loc))
    | Some expRHS -> 
      (match expRHS with
      | Member {exp_member_base; exp_member_fields; _ } -> 
         let var1 = kind_of_Exp exp_member_base in
         let var = if (String.compare var1 "This" == 0) then "this" else var1 in
         let field = List.hd exp_member_fields in 
         let (r1,r2) = (retriveContentfromNode (retriveheap current') var) in
         if r1 == true then let value = retrive_content_from_list r2 field in
         let form = Ipure.BForm (Eq (Var ((id , Unprimed), loc), value, loc)) in
             (Ok (update_pure current' form loc))
         else raise (Foo ("Var not in spec"))
        (* if String.compare (kind_of_Exp exp_member_base) "This" == 0 then 
          
          let index = lookup_Field_In_Object obj field in 
          let value = retriveValueFromCurrent current' index in 
          let () = updateStack id value in 
          current 
        else raise (Foo ("VarDecl-expRHS-Member: " ^ kind_of_Exp expRHS)) *)

      | Binary {exp_binary_op; exp_binary_oper1; exp_binary_oper2} -> 
        (match exp_binary_op, exp_binary_oper1, exp_binary_oper2 with 
          | (OpPlus, Var a, Var b) -> let form = Ipure.BForm (Eq (Var ((id,Unprimed),loc),Add (Var ((a.exp_var_name,Unprimed),loc), Var ((b.exp_var_name,Unprimed),loc),loc),loc)) in
          (Ok (update_pure current' form loc))
          | (OpPlus, Var a, IntLit b) -> let form = Ipure.BForm (Eq (Var ((id,Unprimed),loc),Add (Var ((a.exp_var_name,Unprimed),loc), IConst (b.exp_int_lit_val,loc),loc),loc)) in
          (Ok (update_pure current' form loc))
          | (OpPlus, IntLit b, Var a) -> let form = Ipure.BForm (Eq (Var ((id,Unprimed),loc),Add (Var ((a.exp_var_name,Unprimed),loc), IConst (b.exp_int_lit_val,loc),loc),loc)) in
          (Ok (update_pure current' form loc))
          | (OpMinus, Var a, Var b) -> let form = Ipure.BForm (Eq (Var ((id,Unprimed),loc),Subtract (Var ((a.exp_var_name,Unprimed),loc), Var ((b.exp_var_name,Unprimed),loc),loc),loc)) in
          (Ok (update_pure current' form loc))
          | (OpMinus, Var a, IntLit b) -> let form = Ipure.BForm (Eq (Var ((id,Unprimed),loc),Subtract (Var ((a.exp_var_name,Unprimed),loc), IConst (b.exp_int_lit_val,loc),loc),loc)) in
          (Ok (update_pure current' form loc))
          | (OpMinus, IntLit b, Var a) -> let form = Ipure.BForm (Eq (Var ((id,Unprimed),loc),Subtract (Var ((a.exp_var_name,Unprimed),loc), IConst (b.exp_int_lit_val,loc),loc),loc)) in
          (Ok (update_pure current' form loc))


        | _ -> raise (Foo ("VarDecl-expRHS-Binary: " ^ kind_of_Exp exp_binary_oper1 ^ " " ^ kind_of_Exp exp_binary_oper2 ))
        )

      | _ -> raise (Foo ("VarDecl-expRHS: " ^ kind_of_Exp expRHS))
      )
    
    )
  
  

    (* Write *)
  | Assign {exp_assign_op; exp_assign_lhs; exp_assign_rhs; _ } -> 
      let (lhs, rhs) = (exp_assign_lhs, exp_assign_rhs) in 
      (match (lhs, rhs) with 
      | (VarDecl _, VarDecl _ ) -> raise (Foo "bingo!")
      | (Member {exp_member_base=v1; exp_member_fields = f; _ }, a) ->
        (match v1 with
        | Var {exp_var_name = v2; _ } -> let null_write = null_test current' v2 in
             if null_write == true then let _ = print_string "NPE detected: null write " in (Err current')
             else (match a with 
             | Var {exp_var_name = v3; exp_var_pos = po } -> let (r1,r2) = retriveContentfromPure (retrivepure current') v3 in
               if r1 == true then let res = update_heap (retriveheap current') v2 (List.hd f) r2 in
                  (Ok (Iformula.Base {formula_base_heap = res;
                  formula_base_pure = retrivepure current';
                  formula_base_pos= po }))
               else let (r1,r2) = retriveContentfromNode (retriveheap current') v3 in
                 if r1 == true then 
                  let value = Ipure.Var ((v3, Unprimed), po) in 
                  let res = update_heap (retriveheap current') v2 (List.hd f) value in
                  (Ok (Iformula.Base {formula_base_heap = res;
                  formula_base_pure = retrivepure current';
                  formula_base_pos= po }))
                 else raise (Foo ("Var not found"))
             | IntLit { exp_int_lit_val = i; exp_int_lit_pos = po  } -> let value = Ipure.IConst (i, po) in 
             let res = update_heap (retriveheap current') v2 (List.hd f) value in
             (Ok (Iformula.Base {formula_base_heap = res;
             formula_base_pure = retrivepure current';
             formula_base_pos= po }))
             |_ -> raise (Foo ("Exp not support 1")))
        | This _ -> 
          (* let null_write = null_test current' "this" in
          if null_write == true then let _ = print_string "NPE detected" in (Err current') 
          else *)
              (match a with 
               |Var {exp_var_name = v2; exp_var_pos = po } -> let (r1,r2) = retriveContentfromPure (retrivepure current') v2 in
                 if r1 == true then let res = update_heap (retriveheap current') "this" (List.hd f) r2 in
                    (Ok (Iformula.Base {formula_base_heap = res;
                    formula_base_pure = retrivepure current';
                    formula_base_pos= po }))
                 else let (r1,r2) = retriveContentfromNode (retriveheap current') v2 in
                   if r1 == true then 
                    let value = Ipure.Var ((v2, Unprimed), po) in 
                    let res = update_heap (retriveheap current') "this" (List.hd f) value in
                    (Ok (Iformula.Base {formula_base_heap = res;
                    formula_base_pure = retrivepure current';
                    formula_base_pos= po }))
                   else raise (Foo ("Var not found"))
               | IntLit { exp_int_lit_val = i; exp_int_lit_pos = po  } -> let value = Ipure.IConst (i, po) in 
               let res = update_heap (retriveheap current') "this" (List.hd f) value in
               (Ok (Iformula.Base {formula_base_heap = res;
               formula_base_pure = retrivepure current';
               formula_base_pos= po }))
               |_ -> raise (Foo (kind_of_Exp expr ^ " " ^ "Exp not support 2")))
     
        | _ -> raise (Foo ("Only support variables"))
          )
      | (Var {exp_var_name = v1; _ }, Member {exp_member_base=v2; exp_member_fields; _ }) ->
        (match v2 with
        | Var {exp_var_name = v3; exp_var_pos = po } -> let null_read = null_test current' v3 in
             if null_read == true then let _ = print_string "NPE detected: null read " in (Err current')
             else raise (Foo ("Todo"))
              (* let (r1,r2) = retriveContentfromPure (retrivepure current') v3 in
                 if r1 == true then let value =  
                    |_ -> raise (Foo ("Int"))
          
        | This _ -> 
          (* let null_write = null_test current' "this" in
          if null_write == true then let _ = print_string "NPE detected" in (Err current') 
          else *)
              match a with 
               |Var {exp_var_name; exp_var_pos } -> 
                 let (value:P.exp) = retriveStack exp_var_name in 
                 let (field:ident) = List.hd exp_member_fields in 
                 let index = lookup_Field_In_Object obj field in 
                 (Ok (writeToCurrentSpec current' index value))
               |_ -> raise (Foo ("Int")) *)
     
        | _ -> raise (Foo ("Only support variables"))
          )

      | (Var {exp_var_name = v1; exp_var_pos = po }, Cast { exp_cast_target_type ; exp_cast_body ; _ } )-> 
        (match exp_cast_body with
        | Var { exp_var_name = v2 ;_ } -> (match current' with 
          | Iast.F.Base {formula_base_heap; _ } -> let (r1,r2) = retriveContentfromNode formula_base_heap v2 in
             if r1 == true then let res = up_down_cast r2 exp_cast_target_type in
                 if res == true then let form = Ipure.BForm (Eq (Var ((v1 , Unprimed), po), Var ((v2 , Unprimed), po), po)) in
                  (Ok (update_pure current' form po)) else let _ = print_string "cast_error_detected " in (Err current')
             else raise (Foo ("Variable " ^ v2 ^" not in spec"))
          |_ -> raise (Foo ("Other heap formula: cast")))
        | _ ->  raise (Foo (" not a var_exp for casting ")))
      | (Var { exp_var_name = v1 ; exp_var_pos = p }, Instance { exp_instance_var; exp_intance_type=t ;_ }) -> (match current' with 
          | Iast.F.Base {formula_base_heap; _ } -> ( match exp_instance_var with
            | Var { exp_var_name = v2;_ } -> let (r1,r2) = retriveContentfromNode formula_base_heap v2 in
                if r1 == true then let res = up_down_cast r2 t in 
                   if res == true then let form = Ipure.BForm (Eq (Var ((v1 , Unprimed), p), IConst (1, p), p)) in
                      (Ok (update_pure current' form p))
                   else let form = Ipure.BForm (Eq (Var ((v1 , Unprimed), p), IConst (0, p), p)) in
                      (Ok (update_pure current' form p))
                else raise (Foo ("Variable " ^ v2 ^" not in spec"))
            | _ -> raise (Foo ("not a var_exp for instanceof "))
                )
                 
          |_ -> raise (Foo ("Other heap formula: instanceof ")))
         
      
      | _ -> raise (Foo ("Assign: "^kind_of_Exp lhs ^ " " ^ kind_of_Exp rhs)) 
      
      )
    (* match exp_cast_body with
    | Var { exp_var_name ;_ } -> match current' with 
       | Iast.F.Base {formula_base_heap; _ } -> let (r1,r2) = retriveContentfromNode formula_base_heap exp_var_name in
         if r1 == true then (Ok current')
         else (Err current')
       | _ -> raise (Foo ("Assign-Member-Var: "))
    |_ *)

  | _ -> print_string (kind_of_Exp expr ^ " "); current 
  )

(*
	| Return rtn -> 

	| _ -> raise (Foo ("oop_verification_method_aux not yet " ^ kind_of_Exp expr))



	| Assert of exp_assert
  | Binary of exp_binary
  | Bind of exp_bind

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
  | This of exp_this
(*  | Throw of exp_throw *)
  | Unary of exp_unary
  | Unfold of exp_unfold
  | Var of exp_var
  | While of exp_while
	*)

	;;

let oop_verification_method (obj:Iast.data_decl) (decl: Iast.proc_decl) : string = 
	match decl.proc_body with 
	| None -> raise (Foo "oop_verification_method not yet")
	| Some exp -> 
		let initalState = (fst(List.hd (decl.proc_static_specs))) in 
		let startTimeStamp = Unix.time() in
		let final = oop_verification_method_aux obj decl exp initalState in
		let startTimeStamp01 = Unix.time() in 
		("\n\n========== Module: "^ decl.proc_name ^ " in Object " ^ obj.data_name ^" ==========\n" ^
		"[Static  Pre ] " ^ string_of_spec (fst (List.hd decl.proc_static_specs)) ^"\n"^ 
		"[Static  Post] " ^ string_of_spec (snd (List.hd decl.proc_static_specs)) ^"\n"^ 
    "[Dynamic Pre ] " ^ string_of_spec (fst (List.hd decl.proc_dynamic_specs)) ^"\n"^ 
		"[Dynamic Post] " ^ string_of_spec (snd (List.hd decl.proc_dynamic_specs)) ^"\n"^ 
		"[Reason  Post] " ^ string_of_spec final  ^"\n"^
		"[Reason  Time] " ^ string_of_float ((startTimeStamp01 -. startTimeStamp) *.1000000.0)^ " us" ^"\n" 
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
  let inputfile = (Sys.getcwd () ^ "/" ^ Sys.argv.(1)) in
	let source_files = [inputfile] in
  let r = List.map parse_file_full source_files in
	let r1 = List.hd r in 
  let _ = Iast.build_hierarchy r1 in
  let res = Iast.sub_type (Named "FastCnt") (Named "Cnt") in
  let _ = print_string (Bool.to_string res) in
  (*let _ = List.map print_string (List.map Iprinter.string_of_program r) in *)
	let _ = List.map (fun a -> oop_verification a) r in 
	(* Tpdispatcher.print_stats (); *)
	()
	
	  

