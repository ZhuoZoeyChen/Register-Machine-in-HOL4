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

 (*qr : state *);  

val init_machine_def = Define `
	init_machine m i = 
		((λn. if n < LENGTH i then EL n i else 0)
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
      In := {0} ;
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
      In := {0} ;
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
      In := {0; 1} ; (* include the accumulator or not ?*)
      Out := 1 ;
	|>
`;

val addition_0 = EVAL ``init_machine addition [15; 23]``

val addition_lemma = EVAL `` run_machine addition (init_machine addition [15; 23])``

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
      In := {0;1} ;
      Out := 2 ;
	|>
`;

val multiplication_lemma = EVAL `` run_machine multiplication (init_machine multiplication [3; 4])``

 (* ------------ END examples ------------
   -------------------------------------- 
   --------------------------------------
   -------------------------------------- *)


val correct2_def = Define `
	correct2 f m ⇔ ∀a b. ∃rs. (run_machine m (init_machine m [a;b]) = (rs, NONE)) ∧ (rs m.Out = f a b)
`;

Theorem addition_correct:
	correct2 (+) addition 
Proof
cheat
QED


(* WANT : runM (seq m1 m2) rs_so =  runM m2 (runM m1 rs_so) {same result}*)


val seq_def = Define `
	seq m1 m2 = <|
	    Q := { r1*2+2 | r1 ∈ m1.Q } UNION { r2*2+3 | r2 ∈ m2.Q } ;
   	    tf := (λs. if s = 0  then (*transfer, (m2.q0 * 2 + 1)*)
   	               else if s = 1 then (*transfer, (m2.q0 * 2 + 1)*)
   	              else if EVEN s then (case (m1.tf (s DIV 2)) of 
   	    	                            | Dec x (SOME y) NONE     => Dec (x*2) (SOME (y*2)) (SOME 0)
   	    		  				        | Inc x NONE              => Inc (x*2) (SOME 0)
   	    	      						| Dec x (SOME y) (SOME z) => Dec (x*2) (SOME $ y*2) (SOME $ z*2)
   	    	      						| Inc x (SOME y)          => Inc (x*2) (SOME $ y*2))
   	    	      else (case (m2.tf (s DIV 2)) of 
   	    	      			| Dec x (SOME y) (SOME z) => Dec (x*2+1) (SOME $ y*2+1) (SOME $ y*2+1) 
   	    	      		    | Dec x (SOME y) NONE     => Dec (x*2+1) (SOME $ y*2+1) NONE
   	    	      		    | Inc x (SOME y)          => Inc (x*2+1) (SOME $ y*2+1)
   	    	      		    | Inc x NONE              => Inc (x*2+1) NONE)

   	    	   ) ;
  	    q0 := m1.q0 * 2;
   	    In := m1.In ;
        Out := m2.Out ;
	|>
`; 

val seq_def = Define `
	seq m1 m2 = <|
	    Q := { r1, r2 + m1.qr + 1 | r1 ∈ m1.Q ∧ r2 ∈ m2.Q } ; 
   	    tf := (λs. case s of
   	    		  | m1.qr => case m1.qr of 
   	    		  				 Dec x (SOME y) NONE => Dec x (SOME y) (SOME (m2.q0 + m1.qr + 1))
   	    		  				 _                   => m1.qr
   	    	   
   	    	      | n , n < qr => m1.tf s (*syntax?? *)
   	    	      | case m2.tf s of 
   	    	      		Inc x (SOME y) => Inc 
   	    	   ) ;
  	    q0 := m1.q0 ;
   	    I := m1.I ;
        O := m2.O ;
        qr := m2.qr ;
	|>
`; 




(* val wfrm_def = Define `
`;
*)

(*
TODOS:
1. define and test more example register machines from the book
2. think about combining machines (addition and multiplication for example)
 (hint: define a function which combines different machines)
WANT
	runM (seq m1 m2) rs_so
	= runM m2 (runM m1 rs_so)
(make all states in m1 even and all states in m2 odd)
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


val _ = export_theory ()