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


val dup0_def = Define `
  dup0 r1 r2 r3= <| 
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

val upd_def = Define `
  (upd NONE d = SOME d) 
    ∧
  (upd (SOME d0) d = SOME d0)
`;

val end_link_def = Define `
  (end_link (Inc q d0) d = Inc q (upd d0 d))
    ∧
  (end_link (Dec q d1 d2) d = Dec q (upd d1 d) (upd d2 d))
`;

val link_def = Define`
  link m1 m2 = <|
    Q := m1.Q ∪ m2.Q;
    tf := (λs. if s ∈ m1.Q then end_link (m1.tf s) m2.q0
                else m2.tf s);
    q0 := m1.q0;
    In := m1.In;
    Out := m2.Out;
  |>
`;

(*
val link_all_def = Define`
  link_all ms = case ms of 
    | [x::y] => link x y
    | x::y::ys => link_all (link x y)::ys
`;
*)

val link_all_def = Define`
  link_all ms = FOLDL (λa m. link a m) identity ms
`;
(* if LENGTH ms = 0 then identity 
                else if LENGTH ms = 1 then link identity (HD ms)
                else link_all (link (HD ms) (EL 1 ms))::(delN 0 (delN 0 ms))*)
val identity_def = Define `
  identity = <|
  Q := {1; 2};
  tf := (λs. case s of 
                | 1 => Inc 0 (SOME 2)
                | 2 => Dec 0 NONE NONE
        );
  q0 := 1;
  In := [0];
  Out := 0;
  |>
`;

val feed_main_def = Define `
  feed_main m ms size = MAPi (λi mm. dup ((LENGTH ms - 1)*(size+1)*5+5*(LENGTH (HD ms).In)+i*5) mm.Out (EL i m.In) 0) ms
`;

set_mapped_fixity {
  term_name = "link",
  tok = "⇨",
  fixity = Infixl 500
}

val rlnst_def = Define `
  (rlnst mul ds dr (Inc r s) = Inc (mul*r+dr) (OPTION_MAP (λs. s*mul + ds) s))
    ∧
  (rlnst mul ds dr (Dec r s1 s2) = Dec (mul*r+dr) (OPTION_MAP (λs. s*mul + ds) s1) (OPTION_MAP (λs. s*mul + ds)  s2))
`;

(* Can prove the behavior of renamed machine is the same as original (given mul != 0)*)
val rename_def = Define `
  rename mul ds dr m = <|
    Q := {ds + s * mul | s ∈ m.Q};
    tf := (λs. rlnst mul ds dr (m.tf ((s - ds) DIV mul)));
    q0 := m.q0*mul + ds;
    In := MAP (λn. n*mul + dr) m.In;
    Out := m.Out*mul + dr;
  |>
`;

val test_rename_1 = EVAL `` RUN (rename 3 2 1 addition) [2; 5]``

val dup_def = Define `
  dup s0 ro rd rt = <|
    Q := {s0; s0+1; s0+2; s0+3; s0+4};
    tf := (λs. if s = s0 then Dec ro (SOME $ s0+1) (SOME $ s0+3)
                else if s = (s0+1) then Inc rd (SOME $ s0+2)
                else if s = (s0+2) then Inc rt (SOME s0)
                else if s = (s0+3) then Dec rt (SOME $ s0+4) NONE
                else Inc ro (SOME $ s0+3)

    );
    q0 := s0;
    In := [ro];
    Out := rd;
  |>
`;

(*
val pip_def = Define`
  pip m1s m2 m 
  (* pass m1s.Out to m.in 
    then link to m2 *)
  (*end_link (m1.tf s) m2.q0
`;

val par_def = Define `
  par m ms size = <|
    Q := {s | (∃mm. s ∈ mm.Q ∧ MEM mm ms) ∨ (s ∈ m.Q)};
    tf := (λs. let cm = HD $ FILTER (λmm. s ∈ mm.Q) ms in 
                if findi cm ms = LENGTH ms - 1 then pip (cm.tf s) m
                else pip s cm (EL ((findi cm ms) + 1) ms)
                );
    q0 := (HD ms).q0;
    In := GENLIST SUC size;
    Out := m.Out;
  |>
`;
*)

(*
Cn
    RUN (Cn m [ms]) [inputs]
*)

(*
val end_state_def = Define `
  end_state s = if s = NONE then true else false
`;
*)

val cn_def = Define `
  cn m ms ms' input_size = <|
    Q := {s | (∃mm. s ∈ mm.Q ∧ MEM mm ms) ∨ (s ∈ m.Q)};
    tf := (λs. if s = NONE then 
                  let m' = feed_main m ms size 
                    in
                      m.'tf m'.q0
              else ms'.tf s);
    q0 := (HD ms).q0;
    In := GENLIST SUC input_size;
    Out := m.Out;
  |>
`;

val top_cn_def = Define `
  top_cn m ms input_size = let ds = (LENGTH ms) * (input_size + 1) * 5; 
                          msr =  MAPi (λi mm. rename (LENGTH ms + 1) (ds+i+1) (input_size+1+i) mm) ms;
                            mdups mi mm = MAPi (λi r. dup (mi*(size+1)*5+5*i) (i+1) r 0) mm.In; 
                              ms' = MAPi (λi mm. mdups i mm) msr;
                                m' = rename (LENGTH ms + 1) ds dr m 
                                  in 
                                   cn m' ms' (link_all ms') input_size
`;

(* 30 may
1. Cn using link and dup and ..
2. use number for states
*)

val _ = export_theory ()