open HolKernel Parse boolLib bossLib;

val _ = new_theory "registerMachine";

val _ = type_abbrev("reg", “:num”);
val _ = type_abbrev("state", “:num”);

val _ = Datatype ` action = Inc num (state option) | Dec num (state option) (state option) `


(*
    Q : state set (each one represented with a number); 
    tf : state -> action (returns the action inside the state);
    q0 : state (initial state);
    I : reg list (input regs);
    O : reg (output register);
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


(*val init_machine_def = Define `
  init_machine m i = 
    ((λn. if n > LENGTH i then 0
            else if n = 0 then 0
            else EL (n-1) i)
    ,
        SOME m.q0)
`;
*)

(* run machine :: machine -> (registers, state option) ->  (registers, state option) 
state here is a number *)
val run_machine_1_def = Define `
    (run_machine_1 m (rs, NONE) = (rs, NONE)) 
    ∧
	(run_machine_1 m (rs, SOME s) = if s ∉ m.Q then (rs ,NONE) 
   else case m.tf s of
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
    (const 0 = 
    <|
       Q := {1} ;
       tf := (λn. Inc 0 NONE) ; (* Do I need the λn here?*)
       q0 := 1 ; 
       In := [0] ;
       Out := 1 ;
    |>)
  ∧
    (const (SUC 0) = 
    <|
       Q := {1} ;
       tf := (λn. case n of 
                | 1 => Inc 1 NONE
              );
       q0 := 1 ;
       In := [0] ;
       Out := 1 ;
    |>) 
  ∧ 
    (const (SUC n) =
       let m = const n
     in 
      (<|
         Q  := {s | (s = SUC n) ∨ s IN m.Q } ;
         tf := m.tf (| SUC n |-> Inc 1 (SOME n) |) ;
         q0 := SUC n ;
         In := [0] ;
         Out := 1 ;
      |>)
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
(* val correct2_def = Define `
	correct2 f m ⇔ ∀a b. ∃rs. (run_machine m (init_machine m [a;b]) = (rs, NONE)) ∧ (rs m.Out = f a b)
`;

Theorem addition_correct:
	correct2 (+) addition 
Proof
  rw[correct2_def, init_machine_def, run_machine_1_def] >>
  rw[run_machine_def, addition_def] >>
  metis_tac[] >>
QED
*)

(* WANT : runM (seq m1 m2) rs_so =  runM m2 (runM m1 rs_so) {same result}*)

val seq_def = Define `
	seq m1 m2 = <|
	    Q := { s1*2+2 | s1 ∈ m1.Q } ∪ { s2*2+3 | s2 ∈ m2.Q } ∪ {0;1};
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
TODO 23.May
1. const
2. binary composition 
  (x+1)*(y+3)
    RUN (Bn m [m1; m2])
3. Cn
    RUN (Cn m [ms]) [inputs]
4. Well formness 
*)


(*
Binary Composition 
state 1-10 : duplicating x, y into m1.In
state 11-20 : duplicating x, y into m2.In
state 21-22 : move m1.out to m.in
state 23-24 : move m2.out to m.in
*)

val bn_def = Define `
  bn m m1 m2 = <| 
    Q := {s * 3 + 25 | s ∈ m.Q} ∪ {s1 * 3 + 26 | s1 ∈ m1.Q} ∪ {s2 * 3 + 27 | s2 ∈ m2.Q} ∪ {x | x > 0 ∧ x < 25} ∪ {0};
    tf := (λs. case s of 
               | 1 => Dec 1 (SOME 2) (SOME 4)
               | 2 => Inc ((EL 0 m1.In)*3+4) (SOME 3)
               | 3 => Inc 0 (SOME 1) 
               | 4 => Dec 0 (SOME 5) (SOME 6)
               | 5 => Inc 1 (SOME 4)
               | 6 => Dec 2 (SOME 7) (SOME 9)
               | 7 => Inc ((EL 1 m1.In)*3+4) (SOME 8)
               | 8 => Inc 0 (SOME 6)
               | 9 => Dec 0 (SOME 10) (SOME 11)
               | 10 => Inc 2 (SOME 9)
               | 11 => Dec 1 (SOME 12) (SOME 14)
               | 12 => Inc ((EL 0 m2.In)*3+5) (SOME 13)
               | 13 => Inc 0 (SOME 11) 
               | 14 => Dec 0 (SOME 15) (SOME 16)
               | 15 => Inc 1 (SOME 14)
               | 16 => Dec 2 (SOME 17) (SOME 19)
               | 17 => Inc ((EL 1 m2.In)*3+5) (SOME 18)
               | 18 => Inc 0 (SOME 16)
               | 19 => Dec 0 (SOME 20) (SOME (m1.q0*3+26))
               | 20 => Inc 2 (SOME 19)
               | 21 => Dec (m1.Out*3+4) (SOME 22) (SOME (m2.q0*3+27))
               | 22 => Inc ((EL 0 m.In)*3+3) (SOME 21)
               | 23 => Dec (m2.Out*3+5) (SOME 24) (SOME (m.q0*3+25))
               | 24 => Inc ((EL 1 m.In)*3+3) (SOME 23)
               | _  => if s MOD 3 = 0
                           then (case (m2.tf ((s-27) DIV 3)) of 
                            | Dec x (SOME y) NONE     => Dec (x*3+5) (SOME (y*3+27)) (SOME 23)
                            | Inc x NONE              => Inc (x*3+5) (SOME 23)
                            | Dec x (SOME y) (SOME z) => Dec (x*3+5) (SOME $ y*3+27) (SOME $ z*3+27)
                            | Inc x (SOME y)          => Inc (x*3+5) (SOME $ y*3+27))
                       else if s MOD 3 = 1
                          then (case (m.tf ((s-25) DIV 3)) of 
                            | Dec x (SOME y) NONE     => Dec (x*3+3) (SOME (y*3+25)) NONE
                            | Inc x NONE              => Inc (x*3+3) NONE
                            | Dec x (SOME y) (SOME z) => Dec (x*3+3) (SOME $ y*3+25) (SOME $ z*3+25)
                            | Inc x (SOME y)          => Inc (x*3+3) (SOME $ y*3+25))
                       else (case (m1.tf ((s-26) DIV 3)) of 
                            | Dec x (SOME y) NONE     => Dec (x*3+4) (SOME (y*3+26)) (SOME 21)
                            | Inc x NONE              => Inc (x*3+4) (SOME 21)
                            | Dec x (SOME y) (SOME z) => Dec (x*3+4) (SOME $ y*3+26) (SOME $ z*3+26)
                            | Inc x (SOME y)          => Inc (x*3+4) (SOME $ y*3+26) )
            );
    q0 := m1.q0 * 3 + 5;
    In := [1; 2];
    Out := m.Out;
  |>
`;


val dup_def = Define `
  dup r1 r2 r3= <| 
    Q := {1;2;3;4;5};
    tf := (λs. case s of 
            | 1 => Dec r1 (SOME 2) (SOME 4)
            | 2 => Inc r2 (SOME 3)
            | 3 => Inc r3 (SOME 1) 
            | 4 => Dec r3 (SOME 5) NONE
            | 5 => Inc r1 (SOME 4)
            );
    q0 := 1;
    In := [r1];
    Out := r2;
  |>
`;

(*
Cn
    RUN (Cn m [ms]) [inputs]
*)
val cn_def = Define `

`;

(*30 may
1. Cn using link and dup and ..
2. use number for states
*)

val _ = export_theory ()