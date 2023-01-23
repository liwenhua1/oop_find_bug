(******************************************)
(* command line processing                *)
(******************************************)
open Iparser
open Iprinter
open Ilexer
open Globals
open Iast
open Ipure
open Asksleek

exception Foo of string


(******************************************)
(* main function                          *)
(******************************************)
let program = ref (None:prog_decl option)
let verified_method = ref ([]: (ident*ident*(Iast.specs*Iast.specs)*(Iast.specs*Iast.specs)) list)
let temp_var = ref ([]: string list)
let spec_with_ex_no_ok_err s= 
  let rec helper slist = match slist with
  |[]-> ""
  |x::[] -> x ^ ": "
  |x::y::xs -> x ^ ", " ^ helper (y::xs)
  in "(exists "^ helper !temp_var ^ string_of_formula s ^")"
let spec_with_ex spec =
   match spec with
  |Ok a -> "ok: "^ spec_with_ex_no_ok_err a
  |Err a -> "err: "^ spec_with_ex_no_ok_err a

let print_verified_method = 
  let helper list =
    match list with
    | [] -> print_string ""
    | x :: xs -> let (a,b,c,d) = x in 
                   print_string (a^" "^" "^b^" "^ string_of_spec (fst c) ^string_of_spec (snd c)^ string_of_spec (fst d) ^string_of_spec (snd d)^"\n") in
    helper !verified_method;;
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

  let remove_ok_err spec =
    match spec with
    |Ok a-> a
    |Err a -> a
let retriveheap (spec:Iast.F.formula) = match spec with 
  | Iast.F.Base {formula_base_heap} -> formula_base_heap
  | _ -> raise (Foo ( "other F formula 1 "))
;;

let retrivepure (spec:Iast.F.formula) = match spec with 
  | Iast.F.Base {formula_base_pure} -> formula_base_pure
  | _ -> raise (Foo ( "other F formula "))
;;

let retrivepo (spec:Iast.F.formula) = match spec with 
  | Iast.F.Base {formula_base_pos} -> formula_base_pos
  | _ -> raise (Foo ( "other F formula "))
;;
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
let write_content s = 
    List.fold_right (fun r1 res -> "int "^r1^";"^" "^res) s ""

let rec write_field s = 
  match s with
  | [] -> []
  | a::xs -> fst a :: write_field xs

let take_data h = 
  let s = (List.hd h) in
  (fst s, write_field (snd s)) 
let rec get_data heap = 
  match heap with
  |Iformula.Heapdynamic a -> [(take_data a.h_formula_heap_content)]
  |Iformula.Star a -> (get_data a.h_formula_star_h1) @ (get_data a.h_formula_star_h2)
  |Iformula.HTrue -> []
  |_ ->  raise (Foo "Other F1 ")
let rec notinside e alist = 
  match alist with
  | [] -> true
  | x::xs -> if (String.compare (fst e) (fst x) == 0) then false else notinside e xs

let merge d1 d2 = let x = d1 @ d2 in
  let res = List.fold_right (fun a acc -> if (notinside a acc) then a::acc else acc) x [] in
  res
let find_data heap1 heap2 = 
  let data_1 = get_data heap1 in
  let data_2 = get_data heap2 in
  merge data_1 data_2


let type_restriction spec t = 
  let (r1,r2) = List.fold_right (fun (a,b) (x,y) -> if x == false then (if (String.compare a t == 0) then (true, y @ b) else (false, y @ b)) else (x,y)) (List.rev spec) (false, []) in
  let rec process s r = match s with
                      |x::xs -> if (String.compare (fst x) t == 0) then ((fst x, r) :: xs) else process xs r 
                      |[] -> raise (Foo "not matched") in
  process spec r2



let string_of_da alist= 
  List.fold_right (fun (a,b) acc -> acc^"data "^a^" {"^ write_content b^"}."^"\n") alist ""
let data_message s1 s2= let r1 = retriveheap s1 in
   let r2 = retriveheap s2 in
   let res = find_data r1 r2 in
   string_of_da res
 
let write_sleek_file name spec1 spec2= 
  let file = name in
  let header = data_message spec1 spec2 in 
  let content = header ^"\n"^"checkentail "^string_of_formula spec1 ^" |- "^ (if (List.length !temp_var == 0) then string_of_formula spec2 else spec_with_ex_no_ok_err spec2) ^"."^ "\n" ^ "print residue." in
  let oc = open_out file in
  (* create or truncate file, return channel *)
  Printf.fprintf oc "%s\n" content;
  (* write something *)
  close_out oc;
;;

let write_sleek_file_method_call name spec1 spec2= 
  let file = name in
  let header = data_message spec1 spec2 in 
  let content = header ^"\n"^"checkentail "^(if (List.length !temp_var == 0) then string_of_formula spec1 else spec_with_ex_no_ok_err spec1)^" |- "^ (if (List.length !temp_var == 0) then string_of_formula spec2 else spec_with_ex_no_ok_err spec2) ^"."^ "\n" ^ "print residue." in
  let oc = open_out file in
  (* create or truncate file, return channel *)
  Printf.fprintf oc "%s\n" content;
  (* write something *)
  close_out oc;
;;

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
let up_down_cast s t= 
  let rec helper1 sp ty=
     match sp with
     | [] -> []
     | (a,b)::xs -> if (not (Iast.sub_type (Named a) t)) then (a,b) :: (helper1 xs ty) else helper1 xs ty in
  let res = helper1 s t in
  let rec helper spec type_to_ckeck = 
      match spec with
      | [] -> []
      | x::[] -> if Iast.sub_type (Named (fst x)) type_to_ckeck then [x] else []
      | x::y::xs -> if Iast.sub_type (Named (fst x)) type_to_ckeck then x::xs else let spec = type_restriction (x::y::xs) (fst y) in 
          helper spec type_to_ckeck in
  let res2 = helper s t in (res2,res)
       
      (* List.fold_right (fun (x,y) rs -> if Iast.sub_type (Named x) type_to_ckeck then (rs && true) else false) spec true *)
     
      ;;

let update_pure (spec:Iast.F.formula) (formu:Ipure.formula) po=
  match spec with
   | Base { formula_base_heap = h; formula_base_pure = p; formula_base_pos = po } -> let new_p = Ipure.And (p, formu, po)  in
     Iast.F.Base {formula_base_heap = h; formula_base_pure = new_p; formula_base_pos = po }
   | _ -> raise (Foo "writeToCurrentSpec mismatched field")
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
          Iast.F.Heapdynamic {h_formula_heap_node = n; h_formula_heap_content = (List.rev res); h_formula_heap_pos = po }
        else spec
     | Star {h_formula_star_h1 = h1; h_formula_star_h2 = h2; h_formula_star_pos=po} -> 
       Iast.F.Star {h_formula_star_h1 = update_heap h1 var f value; h_formula_star_h2 = update_heap h2 var f value; h_formula_star_pos=po}
     | _ -> raise (Foo "retriveValueFromCurrent")
    ;;
let update_node_content spec node_name content=
  let rec replace heap n c = 
    match heap with
    | Iformula.Heapdynamic a -> if (String.compare (fst a.h_formula_heap_node) n == 0) then Iformula.Heapdynamic {h_formula_heap_node = a.h_formula_heap_node ; h_formula_heap_content = c; h_formula_heap_pos = a.h_formula_heap_pos} else Iformula.Heapdynamic a
    | Star {h_formula_star_h1 = h1; h_formula_star_h2 = h2; h_formula_star_pos=po} -> 
      Iast.F.Star {h_formula_star_h1 = replace h1 n c ; h_formula_star_h2 = replace h2 n c; h_formula_star_pos=po}
    | _ -> raise (Foo "not210") in
  match spec with 
  |Ok a -> let h = retriveheap a in Ok (Base { formula_base_heap = replace h node_name content;
  formula_base_pure = retrivepure a;
  formula_base_pos = retrivepo a})
  |Err a -> let h = retriveheap a in Err (Base { formula_base_heap = replace h node_name content;
  formula_base_pure = retrivepure a;
  formula_base_pos = retrivepo a})
(*let writeToCurrentSpec (spec:Iast.F.formula) (index:int) (value:P.exp) : Iast.F.formula = 
  match spec with 
  | Iast.F.Base {formula_base_heap; formula_base_pure; formula_base_pos} -> 
    (match formula_base_heap withprint residue.
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



let null_test spec var_name = 
  let (r1,r2) = retriveContentfromNode (retriveheap spec) var_name in
  if r1 == false then let (res1,res2) = retriveContentfromPure (retrivepure spec) var_name in
     if res1 == true then if Ipure.is_null res2 then true else false
     else false
  else false 
;;

(* let find_residue os1 os2=
    let s1 = retriveheap os1 in
    let s2 = retriveheap (remove_ok_err os2) in
    let rec helper spec1 spec2 =
         match spec1 with
         | Iformula.Heapdynamic a -> let (r1,r2) = retriveContentfromNode spec2 (fst a.h_formula_heap_node) in if (r1 == false) then Iformula.Heapdynamic a else Iformula.HTrue
         | Iformula.Star a -> Iformula.Star {h_formula_star_h1 = helper a.h_formula_star_h1 spec2; h_formula_star_h2 = helper a.h_formula_star_h2 spec2; h_formula_star_pos = a.h_formula_star_pos}
         | _ -> raise (raise (Foo ("Other H F"))) in
    helper s1 s2 *)
let find_var var_exp = 
  match var_exp with
  |Iast.Var a -> a.exp_var_name
  |Iast.This a -> "this"
  | _ -> (raise (Foo ("Receiver need to be var"))) 

let all_arg m_call = 
  let start = [find_var m_call.exp_call_recv_receiver] in
  List.fold_right (fun a acc -> let res = find_var a in [res] @ acc ) m_call.exp_call_recv_arguments start            
let find_residue spec1 method_call = 
    let arg_list = all_arg method_call in
    let rec not_in s slist = match slist with
                            | [] -> true
                            | x::xs -> if String.compare x s == 0 then false else not_in s xs in
    let rec helper heap = 
      match heap with
      |Iformula.Heapdynamic a -> if not_in (fst (a.h_formula_heap_node)) arg_list then (Iformula.Heapdynamic a, Iformula.HTrue) else (Iformula.HTrue, Iformula.Heapdynamic a)
      |Star a -> (Iformula.Star {h_formula_star_h1= fst (helper a.h_formula_star_h1);h_formula_star_h2=(fst (helper a.h_formula_star_h2));h_formula_star_pos=a.h_formula_star_pos},
      Iformula.Star {h_formula_star_h1= snd (helper a.h_formula_star_h1);h_formula_star_h2 = snd (helper a.h_formula_star_h2);h_formula_star_pos=a.h_formula_star_pos})
      | _ -> raise (Foo "other Heap F") in
      helper spec1
let unification_pure (mth_call:exp_call_recv) (mth_dec:proc_decl) = 
  let p = mth_call.exp_call_recv_pos in
  let receiver = find_var (mth_call.exp_call_recv_receiver) in
  let head = Ipure.BForm (Eq (Var (("this",Unprimed),p), Var ((receiver,Unprimed),p),p)) in
  let rec find_para (alist:param list) = match alist with
         | [] -> []
         | x::xs -> x.param_name :: find_para xs in
  let rec find_var_list (alist:Iast.exp list) = match alist with
    |[]-> []
    |x::xs -> let var = find_var x in var :: find_var_list xs in
  let para_list = find_para mth_dec.proc_args in
  let rec helper (alist:ident list) (blist:ident list) = 
    match (alist,blist) with
    |([],[]) -> Ipure.mkTrue p
    |(x::xs,y::ys) -> 
      Ipure.And (Ipure.BForm (Eq (Var ((y,Unprimed),p), Var ((x,Unprimed),p),p)),helper xs ys,p) 
    | _ -> raise (Foo "parameter unmatched") in
     Ipure.And (head ,helper (find_var_list mth_call.exp_call_recv_arguments) para_list,p) 

let return_heap_uni (var_eq:P.b_formula) p1 p2 = 
  let flatten_list (alist: (ident * (ident * P.exp) list) list) =
    List.fold_left (fun acc (a,b) -> acc @ b) [] alist in
  let rec helper alist blist po= 
     match (alist, blist) with
       |([],[]) -> Ipure.mkTrue po
       |(x::xs,y::ys) -> if String.compare (fst x) (fst y) == 0 then Ipure.And (Ipure.BForm (Eq (snd x, snd y,po)), helper xs ys po,po) else raise (Foo "field unmatched")
       | _ -> raise (Foo "parameter unmatched") in
  match var_eq with
  | Eq (Var a, Var b, c) -> let node1 = retriveContentfromNode p2 (fst (fst a)) in 
                            if (fst node1 == false) then Ipure.mkTrue c
                            else  let node2 = retriveContentfromNode p1 (fst (fst b)) in
                                  let (dec, pre) = (flatten_list (snd node1), flatten_list (snd node2)) in
                            helper dec pre c
  | Ipure.BConst (true,a) -> Ipure.mkTrue a
  |_ -> raise (Foo "var Eq required")


let rec unification_heap pre pre_dec var_uni=
      (* print_string ((string_of_pure_formula var_uni)^"\n"); *)
      match var_uni with
      | Ipure.BForm a -> return_heap_uni a pre pre_dec
      | Ipure.And (a,b,c) -> Ipure.And (unification_heap pre pre_dec a, unification_heap pre pre_dec b,c)
      | _ -> raise (Foo "other pure F")
    
let rec search_replace (var: ident * P.exp) formu = 
  let rec helper exp1 exp2=
       (match exp1 with
         | Ipure.Var s -> if String.compare (fst (fst (fst exp2))) (fst (fst s)) == 0 then (true, snd exp2) else (false, exp1)
         | Ipure.Add (x,y,z) -> let (r1,r2) = helper x exp2 in if r1 == true then (true, Ipure.Add (r2,y,z)) else let (r3,r4) = helper y exp2 in if r3 == true then (true, Ipure.Add (x,r4,z)) else (false, exp1)
         | Ipure.Subtract (x,y,z) -> let (r1,r2) = helper x exp2 in if r1 == true then (true, Ipure.Subtract (r2,y,z)) else let (r3,r4) = helper y exp2 in if r3 == true then (true, Ipure.Subtract (x,r4,z)) else (false, exp1)
         | _ -> raise (Foo "other pure")) in
  match formu with 
  | Ipure.BForm (BConst (true,a)) -> (false, var)
  | Ipure.And (a,b,c) -> let (r1,r2) = (search_replace var a) in if r1 == true then (true, r2) else (search_replace var b)
  | Ipure.BForm Eq (Var a,b,c) -> let content = snd var in let (r1,r2) = helper content (a,b) in if r1 == true then (true, (fst var, r2)) else (false, var)
  |_ -> raise (Foo "other pureF1")
 let refine state formula =  
  let h1 (node: (ident * P.exp) list) form = 
      List.fold_left (fun acc a -> let (r1, r2) = search_replace a form in if (r1 == true) then acc @ [r2] else acc @ [a]) [] node in
    let process node form = 
      List.fold_left (fun acc (a,b)-> let res = h1 b form in acc @ [(a,res)]) [] node in 
  let rec helper name p = 
        (* print_string ((string_of_pure_formula p)^"\n"); *)
        match p with 
        | Ipure.BForm (BConst (true,a)) -> (false, name)
        | Ipure.And (a,b,c) -> let (r1,r2) = (helper name a) in if r1 == true then (true, r2) else (helper name b)
        | Ipure.BForm Eq (Var a,Var b,c) -> if String.compare (fst (fst a)) name == 0 then (true, (fst (fst b))) else (false, name) 
        | Ipure.BForm Eq (Var a,_,c) -> (false, name) 
        |_ -> raise (Foo "other pureF2") in
  let check_head name1 p1 = 
    let (r1,r2) = helper name1 p1 in if r1 == true then r2 else name1 in
  let rec helper1 s p = 
    match s with
    | Iformula.HTrue -> Iformula.HTrue
    | Iformula.Heapdynamic a -> let head = check_head (fst a.h_formula_heap_node) p in let res = process a.h_formula_heap_content p in Iformula.Heapdynamic {h_formula_heap_node=(head, Unprimed);h_formula_heap_content=res;h_formula_heap_pos=a.h_formula_heap_pos}
    | Iformula.Star a -> Iformula.Star {h_formula_star_h1= helper1 a.h_formula_star_h1 p;h_formula_star_h2 = helper1 a.h_formula_star_h2 p;h_formula_star_pos = a.h_formula_star_pos}
    | _ -> raise (Foo "other heapF") in
  let finished_heap = helper1 (retriveheap state) formula in
  let rec check_replace_pure pu fo =
    let rec h3 exp f = 
      match exp with
      | Ipure.Var a -> let res = check_head (fst (fst a)) f in Ipure.Var ((res,Unprimed), snd a)
      | Ipure.Add (a,b,c) -> Ipure.Add ((h3 a f),(h3 b f),c)
      | Ipure.Subtract (a,b,c) -> Ipure.Subtract ((h3 a f),(h3 b f),c)
      | Ipure.IConst a -> Ipure.IConst a
      | _ -> raise (Foo "not support") in
    match pu with
    | Ipure.BForm BConst (true,a) -> Ipure.BForm (BConst (true,a))
    | Ipure.And (a,b,c) ->Ipure.And (check_replace_pure a fo,check_replace_pure b fo,c)
    | Ipure.BForm (Eq (a,b,c)) -> Ipure.BForm (Eq (h3 a fo,h3 b fo,c))
    |_ -> raise (Foo "other pureF3") in 
  let finished_pure = check_replace_pure (retrivepure state) formula in
  Iformula.Base {formula_base_heap =finished_heap; formula_base_pure = finished_pure; formula_base_pos = retrivepo state}


let entail_checking name sp1 sp2 = match sp1 with
  |Ok a -> (match sp2 with 
           | Ok b -> write_sleek_file name a b
           | Err b -> print_string "entailment failed")
  |Err a -> (match sp2 with 
           | Err b -> write_sleek_file name a b
           | Ok b -> print_string "entailment failed") 

let entail_checking_method_call name sp1 sp2 = match sp1 with
           |Ok a -> (match sp2 with 
                    | Ok b -> write_sleek_file_method_call name a b
                    | Err b -> print_string "entailment failed")
           |Err a -> (match sp2 with 
                    | Err b -> write_sleek_file_method_call name a b
                    | Ok b -> print_string "entailment failed")

let find_meth_dec obj_name mth_name = 
  let p = match !program with
  |None -> (raise (Foo ("Impossible")))
  |Some a -> a in
  let obj_list = p.prog_data_decls in
  let rec helper alist name= match alist with
  | [] -> (raise (Foo ("Unknown obj")))
  | x::xs -> if String.compare x.data_name name == 0 then x else helper xs name in
  let obj = helper obj_list obj_name in
  let rec helper2 (alist:proc_decl list) name= match alist with
  | [] -> (raise (Foo ("Unknown method")))
  | x::xs -> if String.compare x.proc_name name == 0 then x else helper2 xs name in
  helper2 obj.data_methods mth_name


let rec oop_verification_method_aux obj decl expr (current:specs) : specs = 

match current with 
| Err a -> Err a
| Ok current' -> 

  (* let (r1,r2) = retriveContentfromNode (retriveheap current') "this" in let z = type_restriction r2 "FastCnt" in let () = print_string ((string_of_dynamic_content z)^"end") in *)

	(match expr with
  
  | Block {exp_block_body; _ } -> oop_verification_method_aux obj decl exp_block_body current
  
  | Seq {exp_seq_exp1; exp_seq_exp2; _ } -> 
    let temp = oop_verification_method_aux obj decl exp_seq_exp1 current in 
    oop_verification_method_aux obj decl exp_seq_exp2 temp 

  (* Read *)
  | VarDecl {exp_var_decl_type; exp_var_decl_decls; _} -> 
    let (id, expO, loc) = List.hd exp_var_decl_decls in 
    temp_var := id::!temp_var;
    (match expO with 
    | None -> let form = Ipure.BForm (Eq (Var ((id , Unprimed), loc), Null loc, loc)) in
          (Ok (update_pure current' form loc))
    | Some expRHS -> 
      (match expRHS with
      | Member {exp_member_base = ee; exp_member_fields; _ } -> 
         let var = match ee with
         | Var a -> a.exp_var_name
         | This _-> "this"  
         | _ -> raise (Foo ("Not a var")) in
         let null_read = null_test current' var in
         if null_read == true then let _ = print_string "NPE detected: null read \n" in (Err current') else
         (let field = List.hd exp_member_fields in 
         let (r1,r2) = (retriveContentfromNode (retriveheap current') var) in
         if r1 == true then let value = retrive_content_from_list r2 field in
         let form = Ipure.BForm (Eq (Var ((id , Unprimed), loc), value, loc)) in
             (Ok (update_pure current' form loc))
         else (raise (Foo ("Var not in spec"))))
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
      | Var a -> let form = Ipure.BForm (Eq (Var ((id,Unprimed),loc), Var ((a.exp_var_name,Unprimed),loc),loc)) in
           (Ok (update_pure current' form loc))

      | Instance { exp_instance_var; exp_intance_type=t ;_ }-> (match current' with 
          | Iast.F.Base {formula_base_heap; _ } -> ( match exp_instance_var with
             | Var { exp_var_name = v2;_ } -> let (r1,r2) = retriveContentfromNode formula_base_heap v2 in
              if r1 == true then let res = up_down_cast r2 t in 
                 if (List.length (fst res) > 0) then let form = Ipure.BForm (Eq (Var ((id , Unprimed), loc), IConst (1, loc), loc)) in
                    update_node_content (Ok (update_pure current' form loc)) v2 (fst res)
                 else let form = Ipure.BForm (Eq (Var ((id , Unprimed), loc), IConst (0, loc), loc)) in
                    (Ok (update_pure current' form loc))
              else raise (Foo ("Variable " ^ v2 ^" not in spec"))
          | _ -> raise (Foo ("not a var_exp for instanceof "))
              )
               
        |_ -> raise (Foo ("Other heap formula: instanceof ")))
       
        | Cast { exp_cast_target_type ; exp_cast_body ; _ }-> 
          (match exp_cast_body with
          | Var { exp_var_name = v2 ;_ } -> (match current' with 
            | Iast.F.Base {formula_base_heap; _ } -> let (r1,r2) = retriveContentfromNode formula_base_heap v2 in
               if r1 == true then let res = up_down_cast r2 exp_cast_target_type in
                   if (List.length (snd res) > 0) then let _ = print_string "cast_error_detected \n" in (Err (remove_ok_err (update_node_content (Ok current') v2 (snd res))))
                   else let form = Ipure.BForm (Eq (Var ((id , Unprimed), loc), Var ((v2 , Unprimed), loc), loc)) in
                    (Ok (update_pure current' form loc))  
               else raise (Foo ("Variable " ^ v2 ^" not in spec"))
            |_ -> raise (Foo ("Other heap formula: cast")))
          | _ ->  raise (Foo (" not a var_exp for casting ")))

          | IntLit { exp_int_lit_val = i; exp_int_lit_pos = po  } -> let value = Ipure.IConst (i, po) in 
          let form = Ipure.BForm (Eq (Var ((id , Unprimed), loc), value , loc)) in
          Ok (update_pure current' form loc)
          
      
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
             if null_write == true then let _ = print_string "NPE detected: null write \n" in (Err current')
             else (match a with 
             | Var {exp_var_name = v3; exp_var_pos = po } -> let (r1,r2) = retriveContentfromPure (retrivepure current') v3 in
               if r1 == true then let res = update_heap (retriveheap current') v2 (List.hd f) r2 in
                  let result = (Iformula.Base {formula_base_heap = res;
                  formula_base_pure = retrivepure current';
                  formula_base_pos= po }) in (Ok result)
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
             if null_read == true then let _ = print_string "NPE detected: null read \n" in (Err current')
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

      (* | (Var {exp_var_name = v1; exp_var_pos = po }, Cast { exp_cast_target_type ; exp_cast_body ; _ } )-> 
        (match exp_cast_body with
        | Var { exp_var_name = v2 ;_ } -> (match current' with 
          | Iast.F.Base {formula_base_heap; _ } -> let (r1,r2) = retriveContentfromNode formula_base_heap v2 in
             if r1 == true then let res = up_down_cast r2 exp_cast_target_type in
                 if res == true then let form = Ipure.BForm (Eq (Var ((v1 , Unprimed), po), Var ((v2 , Unprimed), po), po)) in
                  (Ok (update_pure current' form po)) else let _ = print_string "cast_error_detected " in (Err current')
             else raise (Foo ("Variable " ^ v2 ^" not in spec"))
          |_ -> raise (Foo ("Other heap formula: cast")))
        | _ ->  raise (Foo (" not a var_exp for casting "))) *)
      (* | (Var { exp_var_name = v1 ; exp_var_pos = p }, Instance { exp_instance_var; exp_intance_type=t ;_ }) -> (match current' with 
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
                 
          |_ -> raise (Foo ("Other heap formula: instanceof "))) *)
         
      
      | _ -> raise (Foo ("Assign: "^kind_of_Exp lhs ^ " " ^ kind_of_Exp rhs)) 
      
      )
    (* match exp_cast_body with
    | Var { exp_var_name ;_ } -> match current' with 
       | Iast.F.Base {formula_base_heap; _ } -> let (r1,r2) = retriveContentfromNode formula_base_heap exp_var_name in
         if r1 == true then (Ok current')
         else (Err current')
       | _ -> raise (Foo ("Assign-Member-Var: "))
    |_ *)
    | Cond a -> let sp = (match a.exp_cond_condition with
              | Var b -> let form = Ipure.BForm (Eq (Var ((b.exp_var_name , Unprimed), b.exp_var_pos), IConst (1, b.exp_var_pos), b.exp_var_pos)) in
                 Ok (update_pure current' form b.exp_var_pos)
              |_ -> raise (Foo ("Condition needs to be Var"))
              ) in oop_verification_method_aux obj decl a.exp_cond_then_arm sp 
    | Return a ->
                (match a.exp_return_val with
                   |None -> Ok current'
                   |Some exp -> match exp with
                   | Var a -> let form = Ipure.BForm (Eq (Var (("res",Unprimed),a.exp_var_pos), Var ((a.exp_var_name,Unprimed),a.exp_var_pos),a.exp_var_pos)) in
                   (Ok (update_pure current' form a.exp_var_pos))
                   | _ -> raise (Foo ("Only return var"))
                
                )
    | CallRecv a -> let h = retriveheap current' in let res = find_residue h a in 
      let obj_name =fst (List.hd (snd (retriveContentfromNode (retriveheap current') (find_var a.exp_call_recv_receiver)))) in let meth_dec = find_meth_dec obj_name a.exp_call_recv_method in
      let uni_pre_pure = unification_pure a meth_dec in 
      let (_,_,c,d) = List.hd !verified_method in 
      let spec_selection = fst d in
      let uni_pre_heap = unification_heap (retriveheap current') (retriveheap (remove_ok_err spec_selection)) uni_pre_pure in
      let uni = Ipure.And (uni_pre_pure ,uni_pre_heap,a.exp_call_recv_pos) in
      let form = Ipure.And (retrivepure current' ,uni,a.exp_call_recv_pos) in
      let pre_pure = Ipure.And ( (Ipure.And (retrivepure (remove_ok_err spec_selection) ,uni,a.exp_call_recv_pos)), retrivepure current', a.exp_call_recv_pos) in
      let pre_condition = Ok (Iformula.Base {formula_base_heap = retriveheap (remove_ok_err spec_selection);formula_base_pure = pre_pure;formula_base_pos = a.exp_call_recv_pos}) in
      let current_state = Iformula.Base {formula_base_heap = snd res;formula_base_pure = form;formula_base_pos = a.exp_call_recv_pos} in
      entail_checking_method_call "method_call.slk" pre_condition (Ok current_state); 
      let content_slk = Asksleek.asksleek "method_call.slk" in
      let res1 = Asksleek.entail_res content_slk in
      let post_condition = refine (remove_ok_err (snd d)) uni in
      let post_state = Iformula.Base {formula_base_heap = Iformula.Star {h_formula_star_h1 = fst res;h_formula_star_h2 =retriveheap post_condition;h_formula_star_pos = retrivepo current'}; 
                                    formula_base_pure = Ipure.And (retrivepure current',retrivepure post_condition,retrivepo current');formula_base_pos = retrivepo current'} in
      if res1 == true then match (snd d) with
        |Ok a -> Ok post_state
        |Err a -> Err post_state
      (* let post_state = refine post_condition uni_pre_heap unification_pure in  *)
      else raise (Foo ("COuld not call method" ^ a.exp_call_recv_method))
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
  let singlised_heap spec =
    let heap = retriveheap (remove_ok_err spec) in 
    let pure = retrivepure (remove_ok_err spec) in 
    let po = retrivepo (remove_ok_err spec) in 
    match spec with
    | Ok a -> Ok (Iformula.Base {formula_base_heap=Iprinter.normalise_formula_base_heap heap;
                                 formula_base_pure = pure;
                                 formula_base_pos = po})
    | Err a -> Err (Iformula.Base {formula_base_heap=Iprinter.normalise_formula_base_heap heap;
                                 formula_base_pure = pure;
                                 formula_base_pos = po})
  
let subsumption_check_single_method s1 s2 d1 d2 = 
  let this_type = (fst (List.hd (snd (retriveContentfromNode (retriveheap (remove_ok_err s1)) "this" )))) in
  let normal_dynamic = update_node_content d1 "this" (type_restriction (snd (retriveContentfromNode (retriveheap (remove_ok_err d1)) "this")) this_type) in
  let () = entail_checking "pre_check.slk" (singlised_heap s1) (singlised_heap normal_dynamic) in
  let content = Asksleek.asksleek "pre_check.slk" in
  let res = Asksleek.entail_res content in
  let () = if (res == true) then print_string "precondition entailment valid \n" else print_string "precondition entailment fail\n" in
  let this_type1 = (fst (List.hd (snd (retriveContentfromNode (retriveheap (remove_ok_err s2)) "this" )))) in
  let normal_dynamic2 = update_node_content d2 "this" (type_restriction (snd (retriveContentfromNode (retriveheap (remove_ok_err d2)) "this")) this_type1) in
  entail_checking "post_check.slk" (singlised_heap normal_dynamic2) (singlised_heap s2);
  let content1 = Asksleek.asksleek "post_check.slk" in
  let res1 = Asksleek.entail_res content1 in
  let () = if (res1 == true) then print_string "postcondition entailment valid\n" else print_string "postcondition entailment fail\n" in
  res && res1
;;

let subsumption_check_dynamic_method s1 s2 d1 d2 = 
  let () = entail_checking "pre_dynamic_check.slk" s1 d1 in
  let content = Asksleek.asksleek "pre_dynamic_check.slk" in
  let res = Asksleek.entail_res content in
  let () = if (res == true) then print_string "dynamic precondition entailment valid \n" else print_string "dynamic precondition entailment fail\n" in
  entail_checking "post_dynamic_check.slk" d2 s2;
  let content1 = Asksleek.asksleek "post_dynamic_check.slk" in
  let res1 = Asksleek.entail_res content1 in
  let () = if (res1 == true) then print_string "dynamic postcondition entailment valid\n" else print_string "dynamic postcondition entailment fail\n" in
  (res && res1)
;;

let retrive_parent_dynamic_spec pclas proc = 
  let rec helper list = match list with
  | [] -> raise (Foo ("method in parent class is not verified"))
  | (a,b,c,d)::xs -> if ((String.compare a pclas == 0) && (String.compare b proc == 0)) then d else helper xs in
   helper !verified_method;;
  


let entail_for_dynamic s1 s2 d1 d2 self parent_class proc_name = 
  let rec not_in s slist = match slist with
        | [] -> true
        | x::xs -> if (String.compare x s) == 0 then false else not_in s xs in 
  let (pd1,pd2) = retrive_parent_dynamic_spec parent_class proc_name in
  let node = snd (retriveContentfromNode (retriveheap (remove_ok_err pd1)) "this") in
  let type_info = List.fold_right (fun (a,b) acc -> a :: acc) node [] in
  let node1 = snd (retriveContentfromNode (retriveheap (remove_ok_err d1)) "this") in
  let new_node = List.fold_right (fun (a,b) acc -> if (not_in a type_info) then acc else (a,b) :: acc) node1 [] in
  let new_d1 = update_node_content d1 "this" new_node in 
  let node2 = snd (retriveContentfromNode (retriveheap (remove_ok_err d2)) "this") in
  let new_node2 = List.fold_right (fun (a,b) acc -> if (not_in a type_info) then acc else (a,b) :: acc) node2 [] in
  let new_d2 = update_node_content d1 "this" new_node2 in 
  let res =subsumption_check_dynamic_method (singlised_heap pd1) (singlised_heap pd2) (singlised_heap new_d1) (singlised_heap new_d2) in
  if (res == true) then (verified_method := (self,proc_name,(s1,s2),(d1,d2)):: !verified_method) ;;
 


let oop_verification_method (obj:Iast.data_decl) (decl: Iast.proc_decl) : string = 
  let () = print_string ("\n\n========== Module: "^ decl.proc_name ^ " in Object " ^ obj.data_name ^" ==========\n") in
	match decl.proc_body with 
	| None -> raise (Foo "oop_verification_method not yet")
	| Some exp -> 
		let initalState = (fst(List.hd (decl.proc_static_specs))) in 
		let startTimeStamp = Unix.time() in
		let final = oop_verification_method_aux obj decl exp initalState in
    let string_of_final =if (List.length !temp_var == 0) then string_of_spec final else spec_with_ex final in
    let static_pre = (fst (List.hd decl.proc_static_specs)) in
    let static_post = (snd (List.hd decl.proc_static_specs)) in
    entail_checking "postconditon_check.slk" (singlised_heap static_post) (singlised_heap final);
    let content = Asksleek.asksleek "postconditon_check.slk" in
    let res = Asksleek.entail_res content in
    temp_var := [];
    let dynamic_pre = (fst (List.hd decl.proc_dynamic_specs)) in
    let dynamic_post = (snd (List.hd decl.proc_dynamic_specs)) in
    if (res == true) then print_string "postcondition satisfied \n" else print_string "cannot prove postcondition \n";
    let entail_for_static = subsumption_check_single_method static_pre static_post dynamic_pre dynamic_post in
    if (String.compare (decl.proc_type) "virtual" == 0) then (if (res == true && entail_for_static == true) then (verified_method := (obj.data_name,decl.proc_name,(static_pre,static_post),(dynamic_pre,dynamic_post)):: !verified_method))
    else (if (res == true && entail_for_static == true) then entail_for_dynamic static_pre static_post dynamic_pre dynamic_post obj.data_name obj.data_parent_name decl.proc_name);
		let startTimeStamp01 = Unix.time() in 
		( 
		"[Static  Pre ] " ^ string_of_spec static_pre^"\n"^ 
		"[Static  Post] " ^ string_of_spec  static_post^"\n"^ 
    "[Dynamic Pre ] " ^ string_of_spec dynamic_pre ^"\n"^ 
		"[Dynamic Post] " ^ string_of_spec  dynamic_post^"\n"^ 
		"[Post  state ] " ^ string_of_final ^"\n"^
		"[Running Time] " ^ string_of_float ((startTimeStamp01 -. startTimeStamp) *.1000000.0)^ " us" ^"\n" 
		)

	;;

  
let oop_verification_object (decl: Iast.data_decl) = 
	let rec helper li = 
		match li with 
		| [] -> ""
		| meth :: restMeth -> 
			let msg = oop_verification_method decl meth in 
			print_string msg ; helper restMeth
	in helper decl.data_methods;  
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
  program := Some r1;
  let _ = Iast.build_hierarchy r1 in
  (* let res = Iast.sub_type (Named "FastCnt1") (Named "Cnt1") in
  let _ = print_string (Bool.to_string res) in *)
  (*let _ = List.map print_string (List.map Iprinter.string_of_program r) in *)
	let _ = List.map (fun a -> oop_verification a) r in 
  
  ()
	(* Tpdispatcher.print_stats (); *)
	
	
	  

