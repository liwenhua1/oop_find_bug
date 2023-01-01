%{
  (* Parser for a more expressive language *)

  open Globals
  open Iast

  module F = Iformula
  module P = Ipure

  type type_decl =
	| Data of data_decl
	| Enum of enum_decl
	| View of view_decl
		
  type decl = 
    | Type of type_decl
    | Proc of proc_decl
	| Coercion of coercion_decl
		
  type member = 
	| Field of (typed_ident * loc)
	| Inv of F.formula
	| Method of proc_decl
		
  type spec_qualifier =
	| Static
	| Dynamic 
	(*| Static_u
	| Dynamic_u
	*)

  type ann =
	| AnnMode of mode
	| AnnType of typ
		
  let get_pos (i : int) = Parsing.rhs_start_pos i

  let rec get_mode (anns : ann list) : mode = match anns with
	| ann :: rest -> begin
		match ann with
		  | AnnMode m -> m
		  | _ -> get_mode rest
	  end
	| [] -> ModeOut (* default to ModeOut if there is no annotation. *)

  let rec get_modes (anns : ann list list) : mode list = 
	match anns with
	  | alist :: rest ->
		  let m_rest = get_modes rest in
		  let m = get_mode alist in
			m :: m_rest
	| [] -> []

	
  let expand_exp_list mk l r pos =
	let b, oe = l in
	  match oe with
		| Some e ->
			let tmp = P.build_relation mk e r pos in
			let res = P.mkAnd b tmp pos in
			  (res, Some r)
		| None -> report_error pos ("parse error in lhs of relational operator")

  let rec split_members mbrs = match mbrs with
	| mbr :: rest -> begin
		let fields, invs, meths = split_members rest in
		  match mbr with
			| Field f -> (f :: fields, invs, meths)
			| Inv i -> (fields, i :: invs, meths)
			| Method m ->
				(fields, invs, m :: meths)
	  end
	| [] -> ([], [], [])

  let rec split_specs specs = match specs with
	| sp :: rest -> begin
		let sspecs, dspecs= split_specs rest in
		  match sp with
			| (Static, pre, post) -> ((pre, post) :: sspecs, dspecs)
			| (Dynamic, pre, post) -> (sspecs, (pre, post) :: dspecs)
	  end
	| [] -> ([],[])

  let rec remove_spec_qualifier (_, pre, post) = (pre, post)
  let rec remove_spec_property (pre, post) = match pre with
												| Ok a -> (match post with
															| Ok b -> (a,b)
															| Err b -> (a,b))
											    | Err a -> (match post with
															| Ok b -> (a,b)
															| Err b -> (a,b))
(*
let rec process_heap_node ide fields position= 
		 match fields with
		   | [(a,b)] -> let h = F.HeapNode { F.h_formula_heap_node = ide;
						 F.h_formula_heap_name = a;
						 F.h_formula_heap_full = false;
						 F.h_formula_heap_with_inv = false;
						 F.h_formula_heap_pseudo_data = false;
						 F.h_formula_heap_arguments = b;
						 F.h_formula_heap_pos = position } in
	                      { F.formula_base_heap = h;
					        F.formula_base_pure = P.mkTrue position;
					        F.formula_base_pos : position }
						 

		   | (a,b) :: tail -> let h = F.HeapNode { F.h_formula_heap_node = ide;
						 F.h_formula_heap_name = a;
						 F.h_formula_heap_full = false;
						 F.h_formula_heap_with_inv = false;
						 F.h_formula_heap_pseudo_data = false;
						 F.h_formula_heap_arguments = b;
						 F.h_formula_heap_pos = position } in
						 let f =  { F.formula_base_heap = h;
					        F.formula_base_pure = P.mkTrue position;
					        F.formula_base_pos : position } in 
	                     F.mkOr f (process_heap_node ide tail position) position

*)
%}

%token AND
%token ANDAND
%token ASSERT
%token ASSUME
%token AT
%token BIND
%token BOOL
%token BREAK
%token CASE
%token CBRACE
%token CLASS
%token COERCION
%token COLON
%token COLONCOLON
%token COMMA
%token CONSEQ
%token CONST
%token CONTINUE
%token CPAREN
%token CSQUARE
%token DATA
%token DDEBUG
%token DIFF
%token DISTR
%token DIV
%token DOLLAR
%token DOT
%token DOUBLEQUOTE
%token DYNAMIC
%token DYNAMIC_U
%token ERR
%token ELSE
%token ENUM
%token EOF
%token EQ
%token EQEQ
%token EQUIV
%token EXISTS
%token EXTENDS
%token FALSE
%token FLOAT
%token FORALL
%token GT
%token GTE
%token HASH
%token <string> IDENTIFIER
%token IF
%token IMPLIES
%token IMPLY
%token IMPORT
%token IN
%token <string> JAVA
%token LEFTARROW
%token <float> LITERAL_FLOAT
%token <int> LITERAL_INTEGER
%token NOTIN
%token BAGMAX
%token BAGMIN
%token FOLD
%token INT
%token INTERR
%token INTERSECT
%token INSTANCEOF
%token INV
%token LT
%token LTE
%token MAX
%token MINUS
%token MIN
%token NEQ
%token NEW
%token NOT
%token NULL
%token OBRACE
%token OFF
%token OPAREN
%token ON
%token OK
%token OP_ADD_ASSIGN
%token OP_DEC
%token OP_DIV_ASSIGN
%token OP_INC
%token OP_MOD_ASSIGN
%token OP_MULT_ASSIGN
%token OP_SUB_ASSIGN
%token OR
%token OROR
%token ORWORD
%token OSQUARE
%token PERCENT
%token PLUS
%token PRIME
%token PRINT
%token REF
%token <string> RES
%token RETURN
%token RIGHTARROW
%token <string> SELF
%token SEMICOLON
%token SPLIT
%token STAR
%token STATIC
%token STATIC_U
%token SUBSET
%token THEN
%token <string> THIS
%token TO
%token TRUE
%token VIEW
%token VOID
%token UNFOLD
%token UNION
%token WHERE
%token WHILE
%token PRESUMES
%token ACHIEVES

%nonassoc LOWER_THAN_ELSE
%nonassoc ELSE

/*%nonassoc LOWER_THAN_SEMICOLON*/
%left SEMICOLON
%left OR 
%left AND
%left STAR
%right NOT
%left EQ NEQ GT GTE LT LTE
%left PLUS MINUS
%left UMINUS

%nonassoc LOWER_THAN_DOT_OP
%nonassoc OP_DEC OP_INC
%left DOT

%start program
%type <Iast.prog_decl> program

%%

program
  : opt_decl_list {
    let data_defs = ref ([] : data_decl list) in
	let enum_defs = ref ([] : enum_decl list) in
	let view_defs = ref ([] : view_decl list) in
    let proc_defs = ref ([] : proc_decl list) in
	let coercion_defs = ref ([] : coercion_decl list) in
    let choose d = match d with
      | Type tdef -> begin
		  match tdef with
			| Data ddef -> data_defs := ddef :: !data_defs
			| Enum edef -> enum_defs := edef :: !enum_defs
			| View vdef -> view_defs := vdef :: !view_defs
		end
      | Proc pdef -> proc_defs := pdef :: !proc_defs 
	  | Coercion cdef -> coercion_defs := cdef :: !coercion_defs in
    let _ = List.map choose $1 in
	let obj_def = { data_name = "Object";
					data_fields = [];
					data_parent_name = "";
					data_invs = []; (* F.mkTrue no_pos; *)
					data_methods = [] } in
	let string_def = { data_name = "String";
					   data_fields = [];
					   data_parent_name = "";
					   data_invs = []; (* F.mkTrue no_pos; *)
					   data_methods = [] } in
      { prog_data_decls = obj_def :: string_def :: !data_defs;
		prog_enum_decls = !enum_defs;
		prog_view_decls = !view_defs;
		prog_proc_decls = !proc_defs;
		prog_coercion_decls = !coercion_defs; }
  }
;

opt_decl_list
  : { [] }
  | decl_list { $1 }
;

decl_list
  : decl { [$1] }
  | decl_list decl { $2 :: $1 }
;

decl
  : type_decl { Type $1 }
  | proc_decl { Proc $1 }
  | coercion_decl { Coercion $1 }
;

type_decl
  : data_decl { Data $1 }
  | class_decl { Data $1 }
  | enum_decl { Enum $1 }
  | view_decl { View $1 }
;

class_decl
  : CLASS IDENTIFIER extends_opt OBRACE member_list_opt CBRACE {
	let t1, t2, t3 = split_members $5 in
	let cdef = { data_name = $2;
				 data_parent_name = $3;
				 data_fields = t1;
				 data_invs = t2; (*List.fold_left 
							   (fun f1 -> fun f2 -> F.mkAnd f1 f2 (F.pos_of_formula f2)) (F.mkTrue (get_pos 1)) *) 
				 data_methods = t3 } in
	let _ = List.map (fun d -> set_proc_data_decl d cdef) t3 in
	  cdef
  }
;

extends_opt
  : { "Object" }
  | EXTENDS IDENTIFIER { $2 }
;

member_list_opt
  : { [] }
  | member_list { List.rev $1 }
;

member_list
  : member { [$1] }
  | member_list member { $2 :: $1 }
;

member
  : typ IDENTIFIER SEMICOLON { Field (($1, $2), get_pos 2) }
  | INV constr SEMICOLON { Inv $2 }
  | proc_decl { Method $1 }
  | constructor_decl { Method $1 }
;

data_decl
  : data_header data_body {
	  { data_name = $1;
		data_fields = $2;
		data_parent_name = "Object";
		data_invs = []; (* F.mkTrue (get_pos 1); *)
		data_methods = [] }
	}
;

data_header
  : DATA IDENTIFIER { $2 }
;

data_body
  : OBRACE opt_field_list CBRACE { $2 }
;

opt_field_list
  : { [] }
  | field_list opt_semicolon { List.rev $1 }
;

opt_semicolon
  : {}
  | SEMICOLON {}
;

field_list
  : typ IDENTIFIER { [(($1, $2), get_pos 1)] }
  | field_list SEMICOLON typ IDENTIFIER { 
			if List.mem $4 (List.map (fun f -> snd (fst f)) $1) then
				report_error (get_pos 4) ($4 ^ " is duplicated")
			else
				(($3, $4), get_pos 3) :: $1 
		}
;

enum_decl
  : enum_header enum_body {
	{ enum_name = $1;
	  enum_fields = $2 }
  }
;

enum_header
  : ENUM IDENTIFIER { $2 }
;

enum_body
  : OBRACE enum_list CBRACE { List.rev $2 }
;

enum_list
  : enumerator { [$1] }
  | enum_list COMMA enumerator { $3 :: $1 }
;

enumerator
  : IDENTIFIER { ($1, None) }
  | IDENTIFIER EQ LITERAL_INTEGER { ($1, Some $3) }
;

/********** Views **********/

view_decl
  : view_header EQEQ view_body opt_inv SEMICOLON {
	{ $1 with view_formula = $3; view_invariant = $4 }
  }
  | view_header EQ error {
	  report_error (get_pos 2) ("use == to define a view")
	}
;

opt_inv
  : { P.mkTrue no_pos }
  | INV pure_constr { $2 }
;

view_header
  : IDENTIFIER LT opt_ann_cid_list GT {
	let cids, anns = List.split $3 in
	  if List.exists 
		(fun x -> match snd x with | Primed -> true | Unprimed -> false) cids 
	  then
		report_error (get_pos 1) 
		  ("variables in view header are not allowed to be primed")
	  else
		let modes = get_modes anns in
		  { view_name = $1;
			view_data_name = "";
			view_vars = List.map fst cids;
			view_modes = modes;
			view_typed_vars = [];
			view_formula = F.mkTrue (get_pos 1);
			view_invariant = P.mkTrue (get_pos 1) }
  }
;

cid
  : IDENTIFIER { ($1, Unprimed) }
  | IDENTIFIER PRIME { ($1, Primed) }
  | RES { (res, Unprimed) }
  | SELF { (self, Unprimed) }
  | THIS { (this, Unprimed) }
;

view_body
  : constr { $1 }
;

/********** Constraints **********/

/*
opt_heap_arg_list
  : { [] }
  | heap_arg_list { List.rev $1 }
;
*/

heap_arg_list
  : { [] }
  | heap_arg_list_aux { List.rev $1 }
;

heap_arg_list_aux
  : heap_arg { [$1] }
  | heap_arg_list_aux COMMA heap_arg { $3 :: $1}
;

heap_arg
  : cexp { $1 (* including variables. to be resolved later *) }
;

opt_heap_arg_list2
  : { [] }
  | heap_arg_list2 { List.rev $1 }
;

heap_arg_list2
	: heap_arg2 { [$1] }
	| heap_arg_list2 COMMA heap_arg2 { 
			if List.mem (fst $3) (List.map fst $1) then
				report_error (get_pos 3) ((fst $3) ^ " is duplicated")
			else 
				$3 :: $1 
		}
;

heap_arg2
	: IDENTIFIER EQ cexp { ($1, $3) }
;

opt_cid_list
  : { 
	[] : (ident * primed) list 
  }
  | cid_list {
	  List.rev $1 : (ident * primed) list 
	}
;

cid_list
  : cid { 
	([$1]) : (ident * primed) list 
  }
  | cid_list COMMA cid {
	  if List.mem (fst $3) (List.map fst $1) then
		report_error (get_pos 3) ("identifier " ^ (fst $3) ^ " is duplicated")
	  else
		($3 :: $1) : (ident * primed) list
	}
;


/* annotated cid list */
opt_ann_cid_list 
  : { [] }
  | ann_cid_list {
	  List.rev $1
	}

ann_cid_list 
  : ann_cid {
	[$1]
  }
  | ann_cid_list COMMA ann_cid {
	  $3 :: $1
	}
;

ann_cid 
  : cid opt_ann_list {
	($1, $2)
  }
;

opt_ann_list
  : { 
	[] 
  }
  | ann_list { 
	  List.rev $1 
	}
;

ann_list
  : ann {
	[$1]
  }
  | ann_list ann {
	  $2 :: $1
	}
;

ann
  : AT IN {
	AnnMode ModeIn
  }
  | AT IDENTIFIER {
	if $2 = "out" then AnnMode ModeOut
	else report_error (get_pos 2) ("unrecognized mode: " ^ $2)
  }
;

constr
  : disjunctive_constr { $1 }
;

disjunctive_constr
  : case_constr { (* each case of a view definition *)
	$1
  }
  | disjunctive_constr ORWORD case_constr {
	  F.mkOr $1 $3 (get_pos 2)
	}
  | error {
	  report_error (get_pos 1) ("parse error in constraints")
	}
;

case_constr
  : core_constr { $1 }
  | EXISTS error { (* opt_typed_cid_list DOT OPAREN core_constr CPAREN *)
	  report_error (get_pos 1)
		("explicit existential quantifiers are disallowed as they are inserted automatically")
	}
;

core_constr
  : heap_constr { F.formula_of_heap $1 (get_pos 1) }
  | pure_constr { F.formula_of_pure $1 (get_pos 1) }
  | heap_constr AND pure_constr { F.mkBase $1 $3 (get_pos 2) }
;

heap_constr
  : simple_heap_constr { $1 }
  | heap_constr STAR simple_heap_constr { F.mkStar $1 $3 (get_pos 2) }
;

simple_heap_constr
  : cid COLONCOLON all_class_field {
	let h = F.Heapdynamic {
      h_formula_heap_node = $1;
      h_formula_heap_content = List.rev $3;
      h_formula_heap_pos = get_pos 2
	} in
	    h
  }
  /*
  | cid COLONCOLON IDENTIFIER LT opt_heap_arg_list2 GT {
	  let h = F.HeapNode2 { F.h_formula_heap2_node = $1;
							F.h_formula_heap2_name = $3;
							F.h_formula_heap2_full = false;
							F.h_formula_heap2_with_inv = false;
							F.h_formula_heap2_pseudo_data = false;
							F.h_formula_heap2_arguments = $5;
							F.h_formula_heap2_pos = get_pos 2 } in
		h
	
	} */

;

/*
  : cid COLONCOLON IDENTIFIER LT heap_arg_list GT {
	let h = F.HeapNode { F.h_formula_heap_node = $1;
						 F.h_formula_heap_name = $3;
						 F.h_formula_heap_full = false;
						 F.h_formula_heap_with_inv = false;
						 F.h_formula_heap_pseudo_data = false;
						 F.h_formula_heap_arguments = $5;
						 F.h_formula_heap_pos = get_pos 2 } in
	  h
  }
  | cid COLONCOLON IDENTIFIER LT opt_heap_arg_list2 GT {
	  let h = F.HeapNode2 { F.h_formula_heap2_node = $1;
							F.h_formula_heap2_name = $3;
							F.h_formula_heap2_full = false;
							F.h_formula_heap2_with_inv = false;
							F.h_formula_heap2_pseudo_data = false;
							F.h_formula_heap2_arguments = $5;
							F.h_formula_heap2_pos = get_pos 2 } in
		h
	}*/

all_class_field 
  : class_field {[$1]}
  | all_class_field class_field {$2 :: $1}

class_field
  : IDENTIFIER LT heap_arg_list GT {($1,$3)}
;
/*
  | cid COLONCOLON IDENTIFIER LT opt_heap_arg_list GT DOLLAR {
		let h = F.HeapNode { F.h_formula_heap_node = $1;
							 F.h_formula_heap_name = $3;
							 F.h_formula_heap_full = true;
							 F.h_formula_heap_with_inv = false;
							 F.h_formula_heap_pseudo_data = false;
							 F.h_formula_heap_arguments = $5;
							 F.h_formula_heap_pos = get_pos 2 } in
		  h
	  }
  | cid COLONCOLON IDENTIFIER LT opt_heap_arg_list GT HASH {
		let h = F.HeapNode { F.h_formula_heap_node = $1;
							 F.h_formula_heap_name = $3;
							 F.h_formula_heap_full = false;
							 F.h_formula_heap_with_inv = true;
							 F.h_formula_heap_pseudo_data = false;
							 F.h_formula_heap_arguments = $5;
							 F.h_formula_heap_pos = get_pos 2 } in
		  h
	  }
  | cid COLONCOLON IDENTIFIER HASH LT opt_heap_arg_list GT {
		let h = F.HeapNode { F.h_formula_heap_node = $1;
							 F.h_formula_heap_name = $3;
							 F.h_formula_heap_full = false;
							 F.h_formula_heap_with_inv = false;
							 F.h_formula_heap_pseudo_data = true;
							 F.h_formula_heap_arguments = $6;
							 F.h_formula_heap_pos = get_pos 2 } in
		  h
	  }
*/
;

pure_constr
  : simple_pure_constr { $1 }
  | pure_constr AND simple_pure_constr { P.mkAnd $1 $3 (get_pos 2) }
;

disjunctive_pure_constr
  : pure_constr OR pure_constr { P.mkOr $1 $3 (get_pos 2) }
  | disjunctive_pure_constr OR pure_constr { P.mkOr $1 $3 (get_pos 2) }
;

simple_pure_constr
  : lbconstr {
	fst $1
  }
  | OPAREN disjunctive_pure_constr CPAREN { 
	  $2 
	}
  | EXISTS OPAREN opt_cid_list COLON pure_constr CPAREN {
	  let qf f v = P.mkExists [v] f (get_pos 1) in
	  let res = List.fold_left qf $5 $3 in
		res
	}
  | FORALL OPAREN opt_cid_list COLON pure_constr CPAREN {
	  let qf f v = P.mkForall [v] f (get_pos 1) in
	  let res = List.fold_left qf $5 $3 in
		res
	}
  | TRUE {
	  P.mkTrue (get_pos 1)
	}
  | FALSE {
	  P.mkFalse (get_pos 1)
	}
  | cid {
	  P.BForm (P.mkBVar $1 (get_pos 1))
	}
  | NOT cid {
	  P.mkNot (P.BForm (P.mkBVar $2 (get_pos 2))) (get_pos 1)
	}
;

lbconstr
  : bconstr {
	(fst $1, snd $1)
  }
  | lbconstr NEQ cexp_list {
	  expand_exp_list P.mkNeq $1 $3 (get_pos 2)
	}
  | lbconstr EQ cexp_list {
	  expand_exp_list P.mkEq $1 $3 (get_pos 2)
	}
  | lbconstr LT cexp_list {
	  expand_exp_list P.mkLt $1 $3 (get_pos 2)
	}
  | lbconstr LTE cexp_list {
	  expand_exp_list P.mkLte $1 $3 (get_pos 2)
	}
  | lbconstr GT cexp_list {
	  expand_exp_list P.mkGt $1 $3 (get_pos 2)
	}
  | lbconstr GTE cexp_list {
	  expand_exp_list P.mkGte $1 $3 (get_pos 2)
	}
;

bconstr
  : cexp_list LT cexp_list {
	let p = P.build_relation P.mkLt $1 $3 (get_pos 2) in
	  (p, Some $3)
  }
  | cexp_list LTE cexp_list {
	  let p = P.build_relation P.mkLte $1 $3 (get_pos 2) in
		(p, Some $3)
	}
  | cexp_list GT cexp_list { 
	  let p = P.build_relation P.mkGt $1 $3 (get_pos 2) in
		(p, Some $3)
	}
  | cexp_list GTE cexp_list { 
	  let p = P.build_relation P.mkGte $1 $3 (get_pos 2) in
		(p, Some $3)
	}
  | cexp_list EQ cexp_list { 
	  let p = P.build_relation P.mkEq $1 $3 (get_pos 2) in
		(p, Some $3)
	}
  | cexp_list NEQ cexp_list {
	  let p = P.build_relation P.mkNeq $1 $3 (get_pos 2) in
		(p, Some $3)
	}
	/* bag_constr */
  | cid IN cexp {
	  (P.BForm (P.BagIn ($1, $3, get_pos 2)), None)
	}
  | cid NOTIN cexp {
	  (P.BForm (P.BagNotIn ($1, $3, get_pos 2)), None)
	}
  | cexp SUBSET cexp {
	  (P.BForm (P.BagSub ($1, $3, get_pos 2)), None)
	}
  | BAGMAX OPAREN cid COMMA cid CPAREN {
	  (P.BForm (P.BagMax ($3, $5, get_pos 2)), None)
	}
  | BAGMIN OPAREN cid COMMA cid CPAREN {
	  (P.BForm (P.BagMin ($3, $5, get_pos 2)), None)
	}
;

/* constraint expressions */

cexp
  : cid {
		P.Var ($1, get_pos 1)
  }
  | LITERAL_INTEGER {
	  P.IConst ($1, get_pos 1)
	}
  | LITERAL_INTEGER cid {
	  P.mkMult $1 (P.Var ($2, get_pos 2)) (get_pos 1)
	}
  | cexp PLUS cexp {
	  P.mkAdd $1 $3 (get_pos 2)
	}
  | cexp MINUS cexp {
	  P.mkSubtract $1 $3 (get_pos 2)
	}
  | MINUS cexp %prec UMINUS {
	  P.mkSubtract (P.IConst (0, get_pos 1)) $2 (get_pos 1)
	}
  | MAX OPAREN cexp COMMA cexp CPAREN {
	  P.mkMax $3 $5 (get_pos 1)
	}
  | MIN OPAREN cexp COMMA cexp CPAREN {
	  P.mkMin $3 $5 (get_pos 1)
	}
  | NULL {
	  P.Null (get_pos 1)
	}
	/* bags */
  | OBRACE opt_cexp_list CBRACE {
	  P.Bag ($2, get_pos 1)
	}
  | UNION OPAREN opt_cexp_list CPAREN {
	  P.BagUnion ($3, get_pos 1)
	}
  | INTERSECT OPAREN opt_cexp_list CPAREN {
	  P.BagIntersect ($3, get_pos 1)
	}
  | DIFF OPAREN cexp COMMA cexp CPAREN {
	  P.BagDiff ($3, $5, get_pos 1)
	}
	
;

opt_cexp_list
  : { [] }
  | cexp_list { $1 }
;

cexp_list
  : cexp_list_rec { 
	List.rev $1
  }
;

cexp_list_rec
  : cexp {
	[$1]
  }
  | cexp_list_rec COMMA cexp { 
	  $3 :: $1
	}
;

/********** Procedures and Coercion **********/

proc_decl
  : proc_header proc_body {
	{ $1 with proc_body = Some $2 }
  }
  | proc_header { $1 }
;
  
proc_header
  : typ IDENTIFIER OPAREN opt_formal_parameter_list CPAREN opt_pre_post_list {
	  let static_specs, dynamic_specs = split_specs $6 in
		{ proc_name = $2;
		  proc_mingled_name = ""; (* mingle_name $2 (List.map (fun p -> p.param_type) $4); *)
		  proc_data_decl = None;
		  proc_constructor = false;
		  proc_args = $4;
		  proc_return = $1;
		  proc_static_specs = static_specs;
		  proc_dynamic_specs = dynamic_specs;
		  proc_loc = get_pos 1;
		  proc_body = None }
	}
  | VOID IDENTIFIER OPAREN opt_formal_parameter_list CPAREN opt_pre_post_list {
		let static_specs, dynamic_specs = split_specs $6 in
		  { proc_name = $2;
			proc_mingled_name = ""; (* mingle_name $2 (List.map (fun p -> p.param_type) $4); *)
			proc_data_decl = None;
			proc_constructor = false;
			proc_args = $4;
			proc_return = void_type;
			proc_static_specs = static_specs;
			proc_dynamic_specs = dynamic_specs;
			proc_loc = get_pos 1;
			proc_body = None }
  }
;

constructor_decl
  : constructor_header proc_body {
	  { $1 with proc_body = Some $2 }
	}
  | constructor_header { $1 }
;

constructor_header
  : IDENTIFIER OPAREN opt_formal_parameter_list CPAREN opt_pre_post_list {
	  let static_specs, dynamic_specs= split_specs $5 in
		if Util.empty dynamic_specs then
		  { proc_name = $1;
			proc_mingled_name = ""; (* mingle_name $2 (List.map (fun p -> p.param_type) $4); *)
			proc_data_decl = None;
			proc_constructor = true;
			proc_args = $3;
			proc_return = Named $1;
			proc_static_specs = static_specs;
			proc_dynamic_specs = dynamic_specs;
			proc_loc = get_pos 1;
			proc_body = None }
		else
		  report_error (get_pos 1) ("constructors have only static speficiations");
	}
;

coercion_decl
  : COERCION opt_name constr coercion_direction constr SEMICOLON {  
	{ coercion_type = $4;
	  coercion_name = $2;
	  coercion_head = $3;
	  coercion_body = $5;
	  coercion_proof = Return ({ exp_return_val = None;
								 exp_return_pos = get_pos 1 })
	}
  }
/*
  | COERCION opt_name constr coercion_direction constr proof_block {
	  { coercion_type = $4;
		coercion_name = $2;
		coercion_head = $3;
		coercion_body = $5;
		coercion_proof = $6 }
	}
*/
;

coercion_direction
  : LEFTARROW { Left }
  | EQUIV { Equiv }
  | RIGHTARROW { Right }
;

/*
proof_block 
  : OBRACE proof_script CBRACE {}
;

proof_script
  : proof_command {}
  | proof_script proof_command {}
;

 fold is sound when done on the only antecedent 
proof_command 
  : UNFOLD cid SEMICOLON { }
  | CONSEQ UNFOLD cid SEMICOLON {}
  | FOLD cid SEMICOLON {} 
  | IF OPAREN pure_constr CPAREN proof_block ELSE proof_block {}
  | IDENTIFIER EQ cid DOT IDENTIFIER IN proof_script {}
;
*/

opt_name
  : { "" }
  | DOUBLEQUOTE IDENTIFIER DOUBLEQUOTE { $2 }
;

opt_pre_post_list
  : { [] }
  | pre_post_list /*%prec LOWER_THAN_SEMICOLON*/ { List.rev $1 }
;

pre_post_list
  : pre_post_pair { [$1] }
  | pre_post_list pre_post_pair { $2 :: $1 }
;

pre_post_pair
  : spec_qualifier_opt PRESUMES constr ACHIEVES constr SEMICOLON { ($1, Ok $3, Ok $5) }
  | spec_qualifier_opt PRESUMES constr ACHIEVES OK constr SEMICOLON { ($1, Ok $3, Ok $6) }
  | spec_qualifier_opt PRESUMES constr ACHIEVES ERR constr SEMICOLON { ($1, Ok $3, Err $6) }
  | spec_qualifier_opt PRESUMES OK constr ACHIEVES OK constr SEMICOLON { ($1, Ok $4, Ok $7) }
  | spec_qualifier_opt PRESUMES OK constr ACHIEVES ERR constr SEMICOLON { ($1, Ok $4, Err $7) }
;

spec_qualifier_opt
  : { Static }
  | STATIC { Static }
  | DYNAMIC { Dynamic }
;

opt_formal_parameter_list
  : { [] }
  | formal_parameter_list { List.rev $1 }
;

formal_parameter_list
  : formal_parameter { [$1] }
  | formal_parameter_list COMMA formal_parameter { $3 :: $1 }
;

formal_parameter
  : fixed_parameter { $1 }
;

fixed_parameter
  : opt_parameter_modifier typ IDENTIFIER {
	{ param_mod = $1;
	  param_type = $2;
	  param_loc = get_pos 3;
	  param_name = $3 }
  }
;

opt_parameter_modifier
  : { NoMod }
  | REF { RefMod }
;

proc_body
  : block { $1 }
;

/*
typ
  : INT { int_type }
  | FLOAT { float_type }
  | BOOL { bool_type }
  | IDENTIFIER { Named $1 }
;
*/

typ
  : non_array_type { $1 }
  | array_type { $1 }
;

non_array_type
  : INT { int_type }
  | FLOAT { float_type }
  | BOOL { bool_type }
  | IDENTIFIER { Named $1 }
;

array_type
  : array_type rank_specifier { Array (int_type, None) }
  | non_array_type rank_specifier { Array (int_type, None) }
;

rank_specifier
  : OSQUARE comma_list_opt CSQUARE {}
;

comma_list_opt
  : {}
  | comma_list {}
;

comma_list
  : COMMA {}
  | comma_list COMMA {}
;

/********** Statements **********/

block
  : OBRACE opt_statement_list CBRACE {
	match $2 with
	  | Empty _ -> Block { exp_block_body = Empty (get_pos 1);
						   exp_block_pos = get_pos 1 }
	  | _ -> Block { exp_block_body = $2;
					 exp_block_pos = get_pos 1 }
  }
;

opt_statement_list
  : { Empty no_pos }
  | statement_list { $1 }
;

statement_list
  : statement { $1 }
  | statement_list statement { Seq { exp_seq_exp1 = $1;
									 exp_seq_exp2 = $2;
									 exp_seq_pos = get_pos 1 } }
  | error { report_error (get_pos 1) ("parse error") }
;

statement
  : declaration_statement { $1 }
  | valid_declaration_statement { $1 }
;

declaration_statement
  : local_variable_declaration SEMICOLON { $1 }
  | local_constant_declaration SEMICOLON { $1 }
;

local_variable_type
  : typ { $1 }
;

local_variable_declaration
  : local_variable_type variable_declarators {
	let var_decls = List.rev $2 in
	  mkVarDecl $1 var_decls (get_pos 1)
  }
;

local_constant_declaration
  : CONST local_variable_type constant_declarators {
	let const_decls = List.rev $3  in
	  mkConstDecl $2 const_decls (get_pos 1)
  }
;

variable_declarators
  : variable_declarator { [$1] }
  | variable_declarators COMMA variable_declarator { $3 :: $1 }
;

variable_declarator
  : IDENTIFIER EQ variable_initializer { ($1, Some $3, get_pos 1) }
  | IDENTIFIER { ($1, None, get_pos 1) }
;

variable_initializer
  : expression { $1 }
;

constant_declarators
  : constant_declarator { [$1] }
  | constant_declarators COMMA constant_declarator { $3 :: $1 }
;

constant_declarator
  : IDENTIFIER EQ constant_expression { ($1, $3, get_pos 1) }
;

valid_declaration_statement
  : block { $1 }
  | empty_statement { $1 }
  | expression_statement { $1 }
  | selection_statement { $1 }
  | iteration_statement { $1 }
  | java_statement { $1 }
  | jump_statement { $1 }
  | assert_statement { $1 }
  | dprint_statement { $1 }
  | debug_statement { $1 }
  | bind_statement { $1 }
  | unfold_statement { $1 }
/*
  | fold_statement { $1 } 
  | split_statement { $1 }
*/
;

/*
fold_statement
  : FOLD cid SEMICOLON { 
	Fold { exp_fold_var = $2;
		   exp_fold_pos = get_pos 1 } }
;
*/

unfold_statement 
  : UNFOLD cid SEMICOLON { 
	Unfold { exp_unfold_var = $2;
			 exp_unfold_pos = get_pos 1 } }
;

/*
split_statement 
  : SPLIT boolean_expression SEMICOLON {
	Cond { exp_cond_condition = $2;
		   exp_cond_then_arm = Empty (get_pos 1);
		   exp_cond_else_arm = Empty (get_pos 1);
		   exp_cond_pos = get_pos 1 }
  }
;
*/

assert_statement
  : ASSERT constr SEMICOLON {
	Assert { exp_assert_asserted_formula = Some $2;
			 exp_assert_assumed_formula = None;
			 exp_assert_pos = get_pos 1 }
  }
  | ASSERT constr ASSUME SEMICOLON {
	  Assert { exp_assert_asserted_formula = Some $2;
			   exp_assert_assumed_formula = Some $2;
			   exp_assert_pos = get_pos 1 }
	}
  | ASSUME constr SEMICOLON {
	  Assert { exp_assert_asserted_formula = None;
			   exp_assert_assumed_formula = Some $2;
			   exp_assert_pos = get_pos 1 }
	}
  | ASSERT constr ASSUME constr SEMICOLON {
	  Assert { exp_assert_asserted_formula = Some $2;
			   exp_assert_assumed_formula = Some $4;
			   exp_assert_pos = get_pos 1 }
    }
;

debug_statement 
  : DDEBUG ON {
	Debug { exp_debug_flag = true;
			exp_debug_pos = get_pos 2 }
  }
  | DDEBUG OFF {
	  Debug { exp_debug_flag = false;
			  exp_debug_pos = get_pos 2 }
	}
;

dprint_statement
  : PRINT SEMICOLON { Dprint ({exp_dprint_string = "";
							   exp_dprint_pos = (get_pos 1)}) }
  | PRINT IDENTIFIER SEMICOLON { Dprint ({exp_dprint_string = $2;
							   exp_dprint_pos = (get_pos 1)}) }
;

empty_statement
  : SEMICOLON { Empty (get_pos 1) }
;

bind_statement
  : BIND IDENTIFIER TO OPAREN id_list_opt CPAREN IN block { 
	Bind { exp_bind_bound_var = $2;
		   exp_bind_fields = $5;
		   exp_bind_body = $8;
		   exp_bind_pos = get_pos 1 }
  }
;

id_list_opt
  : { [] }
  | id_list { List.rev $1 }
;

id_list
  : IDENTIFIER { [$1] }
  | id_list COMMA IDENTIFIER { $3 :: $1 }
;

java_statement 
  : JAVA {
	Java { exp_java_code = $1;
		   exp_java_pos = get_pos 1 }
  }

expression_statement
  : statement_expression SEMICOLON { $1 }
;

statement_expression
  : invocation_expression { $1 }
  | object_creation_expression { $1 }
  | assignment_expression { $1 }
  | post_increment_expression { $1 }
  | post_decrement_expression { $1 }
  | pre_increment_expression { $1 }
  | pre_decrement_expression { $1 }
;

selection_statement
  : if_statement { $1 }
;

embedded_statement
  : valid_declaration_statement { $1 }
;

if_statement
  : IF OPAREN boolean_expression CPAREN embedded_statement %prec LOWER_THAN_ELSE {
	  Cond { exp_cond_condition = $3;
			 exp_cond_then_arm = $5;
			 exp_cond_else_arm = Empty (get_pos 1);
			 exp_cond_pos = get_pos 1 }
	}
  | IF OPAREN boolean_expression CPAREN embedded_statement ELSE embedded_statement {
		Cond { exp_cond_condition = $3;
			   exp_cond_then_arm = $5;
			   exp_cond_else_arm = $7;
			   exp_cond_pos = get_pos 1 }
	  }
;

iteration_statement
  : while_statement { $1 }
;

while_statement
  : WHILE OPAREN boolean_expression CPAREN embedded_statement {
	  While { exp_while_condition = $3;
			  exp_while_body = $5;
			  exp_while_specs = [(F.mkTrue no_pos, F.mkTrue no_pos)];
			  exp_while_pos = get_pos 1 }
	}
  | WHILE OPAREN boolean_expression CPAREN pre_post_list embedded_statement {
		While { exp_while_condition = $3;
				exp_while_body = $6;
				exp_while_specs = List.map remove_spec_property (List.map remove_spec_qualifier $5);
				exp_while_pos = get_pos 1 }
	  }
;

jump_statement
  : return_statement { $1 }
  | break_statement { $1 }
  | continue_statement { $1 }
;

break_statement
  : BREAK SEMICOLON { Break (get_pos 1) }
;

continue_statement
  : CONTINUE SEMICOLON { Continue (get_pos 1) }
;

return_statement
  : RETURN opt_expression SEMICOLON { Return { exp_return_val = $2;
											   exp_return_pos = get_pos 1 } }
;

opt_expression
  : { None }
  | expression { Some $1 }
;

/********** Expressions **********/

object_creation_expression
  : object_or_delegate_creation_expression { $1 }
;

object_or_delegate_creation_expression
  : NEW IDENTIFIER OPAREN opt_argument_list CPAREN {
	New { exp_new_class_name = $2;
		  exp_new_arguments = $4;
		  exp_new_pos = get_pos 1 }
  }
;

new_expression
  : object_or_delegate_creation_expression { $1 }
;

opt_argument_list
  : { [] }
  | argument_list { List.rev $1 }
;

argument_list
  : argument { [$1] }
  | argument_list COMMA argument { $3 :: $1 }
;

argument
  : expression { $1 }
;

expression
  : conditional_expression { $1 }
  | assignment_expression { $1 }
;

constant_expression
  : expression {
	$1
  }
;

boolean_expression
  : expression {
	(* check type *)
	$1
  }
;

assignment_expression
  : prefixed_unary_expression EQ expression {
	  mkAssign OpAssign $1 $3 (get_pos 2)
	}
  | prefixed_unary_expression OP_MULT_ASSIGN expression {
		mkAssign OpMultAssign $1 $3 (get_pos 2)
	  }
  | prefixed_unary_expression OP_DIV_ASSIGN expression {
		mkAssign OpDivAssign $1 $3 (get_pos 2)
	  }
  | prefixed_unary_expression OP_MOD_ASSIGN expression {
		mkAssign OpModAssign $1 $3 (get_pos 2)
	  }
  | prefixed_unary_expression OP_ADD_ASSIGN expression {
		mkAssign OpPlusAssign $1 $3 (get_pos 2)
	  }
  | prefixed_unary_expression OP_SUB_ASSIGN expression {
		mkAssign OpMinusAssign $1 $3 (get_pos 2)
	  }
;

conditional_expression
  : conditional_or_expression { $1 }
  | conditional_or_expression INTERR expression COLON expression {
	  Cond { exp_cond_condition = $1;
			 exp_cond_then_arm = $3;
			 exp_cond_else_arm = $5;
			 exp_cond_pos = get_pos 2 }
	}
;

conditional_or_expression
  : conditional_and_expression { $1 }
  | conditional_or_expression OROR conditional_and_expression {
	  mkBinary OpLogicalOr $1 $3 (get_pos 2)
	}
;

conditional_and_expression
  : inclusive_or_expression { $1 }
  | conditional_and_expression ANDAND inclusive_or_expression {
		mkBinary OpLogicalAnd $1 $3 (get_pos 2)
	  }
;

inclusive_or_expression /* bitwise, not used */
  : exclusive_or_expression { $1 }
;

exclusive_or_expression /* bitwise */
  : and_expression { $1 }
;

and_expression /* bitwise */
  : equality_expression { $1 }
;

equality_expression
  : relational_expression { $1 }
  | equality_expression EQEQ relational_expression {
		mkBinary OpEq $1 $3 (get_pos 2)
	  }
  | equality_expression NEQ relational_expression {
		mkBinary OpNeq $1 $3 (get_pos 2)
	  }
;

relational_expression
  : shift_expression { $1 }
  | relational_expression LT shift_expression {
		mkBinary OpLt $1 $3 (get_pos 2)
	  }
  | relational_expression GT shift_expression {
		mkBinary OpGt $1 $3 (get_pos 2)
	  }
  | relational_expression LTE shift_expression {
		mkBinary OpLte $1 $3 (get_pos 2)
	  }
  | relational_expression GTE shift_expression {
		mkBinary OpGte $1 $3 (get_pos 2)
	  }
;

shift_expression
  : additive_expression { $1 }
; 

additive_expression
  : multiplicative_expression { $1 }
  | additive_expression PLUS multiplicative_expression {
	  mkBinary OpPlus $1 $3 (get_pos 2)
	}
  | additive_expression MINUS multiplicative_expression {
	  mkBinary OpMinus $1 $3 (get_pos 2)
	}
;

multiplicative_expression
  : unary_expression { $1 }
  | multiplicative_expression STAR prefixed_unary_expression {
	  mkBinary OpMult $1 $3 (get_pos 2)
	}
  | multiplicative_expression DIV prefixed_unary_expression {
	  mkBinary OpDiv $1 $3 (get_pos 2)
	}
  | multiplicative_expression PERCENT prefixed_unary_expression {
	  mkBinary OpMod $1 $3 (get_pos 2)
	}
;

prefixed_unary_expression
  : unary_expression { $1 }
/*
  | MINUS prefixed_unary_expression {
	  mkBinary OpMinus (IntLit { exp_int_lit_val = 0; exp_int_lit_pos = get_pos 1}) $2 (get_pos 1)
	  (* Unary (OpUMinus, $2, get_pos 1) *)
	}
*/
;

pre_increment_expression
  : OP_INC prefixed_unary_expression {
	  mkUnary OpPreInc $2 (get_pos 1)
	}
;

pre_decrement_expression
  : OP_DEC prefixed_unary_expression {
	  mkUnary OpPreDec $2 (get_pos 1)
	}
;

post_increment_expression
  : primary_expression OP_INC {
	  mkUnary OpPostInc $1 (get_pos 2)
	}
;

post_decrement_expression
  : primary_expression OP_DEC {
	  mkUnary OpPostDec $1 (get_pos 2)
	}
;

unary_expression
  : unary_expression_not_plusminus { $1 }
  | PLUS unary_expression { 
		let zero = IntLit { exp_int_lit_val = 0;
							exp_int_lit_pos = get_pos 1 }
		in
		  mkBinary OpPlus zero $2 (get_pos 1)
	  
	  }
  | MINUS unary_expression {
		let zero = IntLit { exp_int_lit_val = 0;
							exp_int_lit_pos = get_pos 1 }
		in
		  mkBinary OpMinus zero $2 (get_pos 1)
	  }
  | pre_increment_expression { $1 }
  | pre_decrement_expression { $1 }
;

unary_expression_not_plusminus
  : postfix_expression { $1 }
  | NOT prefixed_unary_expression {
		mkUnary OpNot $2 (get_pos 1)
	  }
  | cast_expression { $1 }
  | instanceof_expression { $1 }
;

postfix_expression
  : primary_expression { $1 }
  | post_increment_expression { $1 }
  | post_decrement_expression { $1}
;

instanceof_expression 
  : member_name INSTANCEOF typ { Instance { exp_instance_var = $1; (*TODO: fix this *)
						  exp_intance_type = $3;
						  exp_instance_pos = get_pos 1 }}

cast_expression
  : OPAREN expression CPAREN unary_expression_not_plusminus { 
	  match $2 with
		| Var v -> Cast { exp_cast_target_type = Named v.exp_var_name; (*TODO: fix this *)
						  exp_cast_body = $4;
						  exp_cast_pos = get_pos 1 }
		| _ -> report_error (get_pos 2) ("Expecting a type")
	}
  | OPAREN INT CPAREN unary_expression { 
		Cast { exp_cast_target_type = Prim Int;
			   exp_cast_body = $4;
			   exp_cast_pos = get_pos 1 }
	  }
  | OPAREN BOOL CPAREN unary_expression { 
		Cast { exp_cast_target_type = Prim Bool;
			   exp_cast_body = $4;
			   exp_cast_pos = get_pos 1 }
	  }
  | OPAREN FLOAT CPAREN unary_expression { 
		Cast { exp_cast_target_type = Prim Float;
			   exp_cast_body = $4;
			   exp_cast_pos = get_pos 1 }
	  }
;

invocation_expression
  : qualified_identifier OPAREN opt_argument_list CPAREN {
	  CallRecv { exp_call_recv_receiver = fst $1;
				 exp_call_recv_method = snd $1;
				 exp_call_recv_arguments = $3;
				 exp_call_recv_pos = get_pos 1 }
	}
  | IDENTIFIER OPAREN opt_argument_list CPAREN {
		CallNRecv { exp_call_nrecv_method = $1;
					exp_call_nrecv_arguments = $3;
					exp_call_nrecv_pos = get_pos 1 }
	  }
;

qualified_identifier
  : primary_expression DOT IDENTIFIER { ($1, $3) }
;

member_access
  : primary_expression DOT IDENTIFIER {
	Member { exp_member_base = $1;
			 exp_member_fields = [$3];
			 exp_member_pos = get_pos 3 }
  }
;

literal
  : boolean_literal { BoolLit { exp_bool_lit_val = $1;
								exp_bool_lit_pos = get_pos 1 } }
  | integer_literal { IntLit { exp_int_lit_val = $1;
							   exp_int_lit_pos = get_pos 1 } }
  | real_literal { FloatLit { exp_float_lit_val = $1;
							  exp_float_lit_pos = get_pos 1 } }
  | NULL { Null (get_pos 1) }
;

real_literal
  : LITERAL_FLOAT { $1 }
;

integer_literal
  : LITERAL_INTEGER { $1 }
;

boolean_literal
  : TRUE { true }
  | FALSE { false }
;

primary_expression
  : parenthesized_expression { $1 }
  | primary_expression_no_parenthesis { $1 }
;

parenthesized_expression
  : OPAREN expression CPAREN { $2 }
;

primary_expression_no_parenthesis
  : literal { $1 }
  | member_name { $1 }
  | member_access { $1 }
  | invocation_expression { $1 }
  | new_expression { $1}
;

member_name
  : IDENTIFIER { Var { exp_var_name = $1;
					   exp_var_pos = get_pos 1 } }
  | THIS { This ({exp_this_pos = get_pos 1}) }
;

%%
