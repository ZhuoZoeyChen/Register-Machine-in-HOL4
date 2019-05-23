open HolKernel Parse boolLib bossLib;

val _ = new_theory "registerMachine";

val _ = type_abbrev("reg", “:num”);
val _ = type_abbrev("state", “:num”);

val _ = Datatype ` action = Inc num (state option) | Dec num (state option) (state option) `


(*
    Q : state set (each one represented with a number); 
    tf : state -> action (returns the action inside the state);
    q0 : state (initial state);
    I : reg set (input registers, each represetned with a number);
    O : reg set (output registers, each represetned with a number);
*)

val _ = Datatype‘
  rm = <|
    Q : state set ; 
    tf : state -> action ;
    q0 : state ;
    In : reg list ;
    Out : reg ;
  |>
’;

(* Initialise *)
val init_machine_def = Define `
	init_machine m i = 
		((λn. if findi n m.In = LENGTH m.In then 0
            else EL (findi n m.In) i)
		,
        SOME m.q0)
`;


(* run machine :: machine -> (registers, state option) ->  (registers, state option) 
state here is a number *)
val run_machine_1_def = Define `
    (run_machine_1 m (rs, NONE) = (rs, NONE)) 
    ∧
	(run_machine_1 m (rs, SOME s) = case m.tf s of
		| Inc r so => ( rs (| r |-> rs r + 1 |), so )
		| Dec r so1 so2 => if rs r > 0 then ( rs (| r |-> rs r - 1 |) , so1)
		                      else ( rs, so2))
`;

val run_machine_def = Define `
	(run_machine m = WHILE (λ(rs, so). so ≠ NONE) (run_machine_1 m)) 
`;

val RUN_def = Define `
  RUN m i = FST (run_machine m (init_machine m i)) m.Out
`;

val const_def = Define `
  (const 0 = )
    ∧ (const 1 = ) 
      ∧ (const (SUC n) = let m = const n in ...
                tf := m.tf (| ... |-> ... |) 
                )
`;
(* (run_machine m (rs, NONE) = init_machine m rs) 
	∧ 
	*)

(* ------------ examples ------------
   ---------------------------------- 
   ----------------------------------
   ----------------------------------*)


val empty_def = Define `
	empty = <| 
      Q := {1} ; 
      tf := (λn. Dec 0 (SOME 1) NONE) ;
      q0 := 1 ;
      In := [0] ;
      Out := 0 ;
	|>
`;

val empty_lemma = EVAL `` run_machine empty (init_machine empty [3])``

val transfer_def = Define `
	transfer = <| 
      Q := {1 ; 2} ; 
      tf := (λn. case n of 
      			| 1 => Dec 0 (SOME 2) NONE 
      			| 2 => Inc 1 (SOME 1)
      		) ;
      q0 := 1 ;
      In := [0] ;
      Out := 1 ;
	|>
`;

val transfer_lemma = EVAL `` run_machine transfer (init_machine transfer [10])``

val addition_def = Define `
	addition = <| 
      Q := {1; 2; 3; 4; 5} ; 
      tf := (λn. case n of 
      			| 1 => Dec 0 (SOME 2) (SOME 4)
      			| 2 => Inc 1 (SOME 3)
      			| 3 => Inc 2 (SOME 1)
      			| 4 => Dec 2 (SOME 5) NONE
      			| 5 => Inc 0 (SOME 4)
      		) ;
      q0 := 1 ;
      In := [0; 1] ; (* include the accumulator or not ?*)
      Out := 1 ;
	|>
`;

val addition_0 = EVAL ``init_machine addition [15; 23]``

val addition_lemma = EVAL `` run_machine addition (init_machine addition [15; 23])``

val R_addition = EVAL ``RUN addition [15; 23]``

val multiplication_def = Define `
	 multiplication = <| 
      Q := {1; 2; 3; 4; 5; 6} ; 
      tf := (λn. case n of 
      			| 1 => Dec 0 (SOME 2) NONE
      			| 2 => Dec 1 (SOME 3) (SOME 5)
      			| 3 => Inc 2 (SOME 4) 
      		    | 4 => Inc 3 (SOME 2)
      		    | 5 => Dec 3 (SOME 6) (SOME 1)
      		    | 6 => Inc 1 (SOME 5) 
      		 );
      q0 := 1 ;
      In := [0;1] ;
      Out := 2 ;
	|>
`;

val multiplication_lemma = EVAL `` run_machine multiplication (init_machine multiplication [3; 4])``

val double_def = Define `
  double = <|
    Q := {1; 2; 3};
    tf := (λs. case s of 
            | 1 => Dec 0 (SOME 2) NONE
            | 2 => Inc 1 (SOME 3) 
            | 3 => Inc 1 (SOME 1)
            );
    q0 := 1;
    In := [0];
    Out := 1;
    |>
  `;

  val foo = EVAL ``RUN double [15]``

 (* ------------ END examples ------------
   -------------------------------------- 
   --------------------------------------
   -------------------------------------- *)


(* Machine and math operation returns the same output *)
val correct2_def = Define `
	correct2 f m ⇔ ∀a b. ∃rs. (run_machine m (init_machine m [a;b]) = (rs, NONE)) ∧ (rs m.Out = f a b)
`;

Theorem addition_correct:
	correct2 (+) addition 
Proof
  rw[correct2_def, init_machine_def, run_machine_1_def] >>
  rw[run_machine_def, addition_def] >>
  metis_tac[] >>
QED


(* WANT : runM (seq m1 m2) rs_so =  runM m2 (runM m1 rs_so) {same result}*)

val seq_def = Define `
	seq m1 m2 = <|
	    Q := { s1*2+2 | s1 ∈ m1.Q } UNION { s2*2+3 | s2 ∈ m2.Q } ;
   	    tf := (λs. if s = 0  
                      then Dec (m1.Out*2) (SOME 1) (SOME (m2.q0*2+3))
   	               else if s = 1 
                      then Inc ((HD m2.In)*2+1) (SOME 0)  
   	               else if EVEN s then (case (m1.tf ((s-2) DIV 2)) of 
   	    	                  | Dec x (SOME y) NONE     => Dec (x*2) (SOME (y*2+2)) (SOME 0)
   	    		  				      | Inc x NONE              => Inc (x*2) (SOME 0)
   	    	      						| Dec x (SOME y) (SOME z) => Dec (x*2) (SOME $ y*2+2) (SOME $ z*2+2)
   	    	      						| Inc x (SOME y)          => Inc (x*2) (SOME $ y*2+2))
   	    	              else (case (m2.tf ((s-3) DIV 2)) of 
   	    	      		    	| Dec x (SOME y) (SOME z) => Dec (x*2+1) (SOME $ y*2+3) (SOME $ y*2+3) 
   	    	      		      | Dec x (SOME y) NONE     => Dec (x*2+1) (SOME $ y*2+3) NONE
   	    	      		      | Inc x (SOME y)          => Inc (x*2+1) (SOME $ y*2+3)
   	    	      		      | Inc x NONE              => Inc (x*2+1) NONE)

   	    	   ) ;
  	    q0 := m1.q0 * 2 + 2;
   	    In := MAP (λn. n*2) m1.In;
        Out := m2.Out * 2 + 1;
	|>
`; 

val seq_add_trans_lemma = EVAL `` RUN (seq addition double) [15; 27]``



(* val wfrm_def = Define `
`;
*)

(*
TODOS:
3. define well formed register machine
4. add return state to all existing functions
*)


(*

TODOS 9. May . 2019
1. Prove addition is correct
2. Fix seq *)

(*

tf: regs -> num -> num # regs

nm : num -> action 

if regs n = 0 then 
	regs1 = regs
else 
	regs2 = regs (| n |-> regs n - 1 |)

nm : num -> action

(| Q 
	nm: state -> action
	rm
	apply : cstate -> regs -> regs * cstate option

	|)

*)

(* 
Notes 20.05.2019

How about using hashmap for registers?

*)

(*
TODO 23.May
1. const
2. binary composition 
  (x+1)*(y+3)
    RUN (Bn m [m1; m2])
3. Cn
    RUN (Cn m [ms]) [inputs]
4. Well formness 
*)

val _ = export_theory ()