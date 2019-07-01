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
    Q : state set; 
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


(* run machine :: machine -> (registers, state option) ->  (registers, state option) *)
val run_machine_1_def = Define `
    (run_machine_1 m (rs, NONE) = (rs, NONE)) 
    ∧
	(run_machine_1 m (rs, SOME s) = if s ∉ m.Q then (rs, NONE) 
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

Definition conv:
  (conv (SOME s) = s+1) ∧
  (conv NONE = 0)
End

Definition strip_state:
  strip_state action = case action of 
     | Inc _ so => [conv so]
     | Dec _ so1 so2 => conv so1::[conv so2]
End

val st = EVAL ``strip_state (Inc 5 (SOME 4))``
val st2 = EVAL ``strip_state (Inc 5 NONE)``
val st3 = EVAL ``strip_state (Dec 199 (SOME 4) NONE)``
val stf = EVAL ``FOLDL (λe s. e ∧ ((s-1 ∈ {1}) ∨ (s = 0))) T st2``


val wfrm_def = Define `
  wfrm m ⇔ 
    FINITE m.Q ∧
    m.q0 ∈ m.Q ∧
    (∀s. s ∈ m.Q ⇒ FOLDL (λe s. e ∧ ((s-1 ∈ m.Q) ∨ (s = 0))) T (strip_state $ m.tf s)) 
`;

val wfep = EVAL ``wfrm empty``
val wfad = EVAL ``wfrm addition``

(* ------------ Simple Machines ------------
   ---------------------------------- 
   ----------------------------------
   ----------------------------------*)


val const_def = Define `
    (const 0 = 
    <|
       Q := {1} ;
       tf := K $ Inc 0 NONE;
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
         Q  := {s | (s = SUC n) ∨ s IN m.Q} ;
         tf := m.tf (| SUC n |-> Inc 1 (SOME n) |) ;
         q0 := SUC n ;
         In := [0] ;
         Out := 1 ;
      |>)
      )
`;

(*val test_const = EVAL ``RUN (const 1) [10]``;*)

val identity_def = Define `
  identity = <|
  Q := {0;1};
  tf := (λs. case s of 
                | 0 => Inc 0 (SOME 1)
                | 1 => Dec 0 NONE NONE
        );
  q0 := 0;
  In := [0];
  Out := 0;
  |>
`;

val test_iden = EVAL ``RUN identity [5]``;

val identity2_def = Define `
  identity2 = <|
  Q := {10;11};
  tf := (λs. case s of 
                | 10 => Inc 10 (SOME 11)
                | 11 => Dec 10 NONE NONE
        );
  q0 := 10;
  In := [10];
  Out := 10;
  |>
`;

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
      Q := {1;2} ; 
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

Definition simp_add_def:
  simp_add = <|
    Q := {1;2};
    tf := (λs. case s of 
            | 1 => Dec 2 (SOME 2) NONE
            | 2 => Inc 1 (SOME 1)
            | otherwise => ARB
          );
    q0 := 1;
    In := [2; 1];
    Out := 1;
  |>
End

val s_adR = EVAL ``RUN simp_add [15; 23]``;
val s_adr = EVAL ``run_machine simp_add (init_machine simp_add [15;27])``;

val addition_def = Define `
	addition = <| 
      Q := {1;2;3;4;5} ; 
      tf := (λn. case n of 
      			| 1 => Dec 5 (SOME 2) (SOME 4)
      			| 2 => Inc 1 (SOME 3)
      			| 3 => Inc 2 (SOME 1)
      			| 4 => Dec 2 (SOME 5) NONE
      			| 5 => Inc 5 (SOME 4)
      		) ;
      q0 := 1 ;
      In := [5; 1] ; 
      Out := 1 ;
	|>
`;

val addition = EVAL ``addition``;
val addition_0 = EVAL ``init_machine addition [15; 23]``;
val addition_lemma = EVAL `` run_machine addition (init_machine addition [15; 23])``;
val R_addition = EVAL ``RUN addition [15; 23]``;

val multiplication_def = Define `
	 multiplication = <| 
      Q := {1;2;3;4;5;6} ; 
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
val multiplication_RUN = EVAL ``RUN multiplication [2; 15]``;

val double_def = Define `
  double = <|
    Q := {1;2;3};
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

val test_double = EVAL ``RUN double [15]``


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

val test_dup0 = EVAL ``RUN (dup0 14 15 0) [27]``;

 (* ------------ END simple machines ------------
   -------------------------------------- 
   --------------------------------------
   -------------------------------------- *)


 (* ------------ Combining simple machines ------------
   -------------------------------------- 
   --------------------------------------
   -------------------------------------- *)

val rInst_def = Define `
  (rInst mnum (Inc r sopt) = Inc (npair mnum r) sopt)
    ∧
  (rInst mnum (Dec r sopt1 sopt2) = Dec (npair mnum r) sopt1 sopt2)
`;

val mrInst_def = Define `
  mrInst mnum m = <|
    Q := m.Q;
    tf := rInst mnum o m.tf ;
    q0 := m.q0;
    In := MAP (λr. npair mnum r) m.In;
    Out := npair mnum m.Out;
  |>
`;

val test_mrInst_add = EVAL``RUN (mrInst 3 addition) [15; 26]``;

val test_mrInst_constr = EVAL ``mrInst 3 addition``;

val test_mrInst_add2 = EVAL 
  ``run_machine (mrInst 3 addition) (init_machine (mrInst 3 addition) [15; 26])``;

val sInst_def = Define `
  (sInst mnum (Inc r sopt) = Inc r (OPTION_MAP (npair mnum) sopt))
    ∧
  (sInst mnum (Dec r sopt1 sopt2) = 
      Dec r (OPTION_MAP (npair mnum) sopt1) (OPTION_MAP (npair mnum) sopt2))
`;

fun teval n t = 
  let 
    val i = ref n
    fun stop t = if !i <= 0 then true else (i := !i - 1; false)
  in
    with_flag (computeLib.stoppers, SOME stop) (computeLib.WEAK_CBV_CONV computeLib.the_compset) t
  end;

val msInst_def = Define `
  msInst mnum m = <|
    Q := IMAGE (npair mnum) m.Q;
    tf := sInst mnum o m.tf o nsnd;
    q0 := npair mnum m.q0;
    In := m.In;
    Out := m.Out;
  |>
`;

val test_msInst_RUN = EVAL``RUN (msInst 3 addition) [15; 26]``;

val test_msInst_add = teval 1000 ``(msInst 2 addition)``;

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


val linktf_def = Define`
  linktf m1Q tf1 tf2 m2init s = 
     if s ∈ m1Q then end_link (tf1 s) m2init
     else tf2 s
`;

val link_def = Define`
  link m1 m2 = <|
    Q := m1.Q ∪ m2.Q;
    tf := linktf m1.Q m1.tf m2.tf m2.q0;
    q0 := m1.q0;
    In := m1.In;
    Out := m2.Out;
  |>
`;

val _ = set_mapped_fixity {
  term_name = "link",
  tok = "⇨",
  fixity = Infixl 500
}


val link_all_def = Define`
  (link_all [] = identity) ∧     
  (link_all (m::ms) = FOLDL (λa mm. a ⇨ mm) m ms)
`;



val test_lka = EVAL``link_all [(mrInst 1 (msInst 1 identity)); (mrInst 2 (msInst 2 identity))]``;

val test_link_out = EVAL ``RUN (link_all [identity;identity2]) [5]``;


val test_id2 = EVAL ``RUN identity2 [15]``;

val test_link = EVAL `` RUN (msInst 0 identity ⇨ msInst 2 (dup0 0 10 1 ) ⇨ msInst 1 identity2) [15] ``;

val test_link_ddd = teval 10000 ``(MAPi msInst [double; double])``;

val test_link_run = EVAL ``
    let ma = (let m = MAPi (λi m. (mrInst (i+1) m)) [double;double];
                                 dup = dup0 (HD m).Out (HD (LAST m).In) 0;
                                 mix = MAPi msInst [HD m ; dup ; LAST m]
               in 
                 link_all mix)
    in 
      run_machine ma (init_machine ma [2])
``;

val test_link_RUN = EVAL ``RUN (let m = MAPi (λi m. (mrInst (i+1) m)) [double;double];
                                 dup = dup0 (HD m).Out (HD (LAST m).In) 0;
                                 mix = MAPi msInst [HD m ; dup ; LAST m]
               in 
                 link_all mix) [5]``;

val test_1 = computeLib.RESTR_EVAL_CONV [``$o``] `` let m = MAPi (λi m. (mrInst (i+1) m)) [double;double];
                                 dup = dup0 (HD m).Out (HD (LAST m).In) 0;
                                 mix = MAPi msInst [HD m ; dup ; LAST m]
               in 
                 link_all mix``;

val _ = computeLib.set_skip computeLib.the_compset ``COND`` (SOME 1);

val Cn_def = Define `
  Cn m ms = 
    let isz = LENGTH (HD ms).In;
        mms = MAPi (λi mm. mrInst (i+2) mm) (m::ms);
        m' = HD mms;
        ms' = TL mms;
        ics = FLAT (MAP (λmm. MAPi (λi r. dup0 (npair 0 i) r (npair 1 0)) mm.In) ms');
        ocs = MAPi (λi mm. dup0 mm.Out (EL i m'.In) (npair 1 0)) ms';
        mix = ics++ms'++ocs++[m'];
        mix' = MAPi msInst mix;
    in 
      link_all mix' with In := MAP (npair 0) (GENLIST I isz)
`;

val test_Cn_iden = EVAL ``RUN (Cn identity [identity]) [5]``;

val test_Cn_add = EVAL ``RUN (Cn addition [addition; addition]) [2;2]``;


 (* ------------ END Combining simple machines ------------
   -------------------------------------- 
   --------------------------------------
   -------------------------------------- *)


(*----------------
````PROVING`````
----------------*)

(* Machine and math operation returns the same output *)
(* TODO *)

val correct2_def = Define `
  correct2 f m ⇔ ∀a b. RUN m [a;b] = f a b
`;

Theorem simp_add_correct:
  correct2 (+) simp_add
Proof
  rw[simp_add_def, correct2_def, init_machine_def, run_machine_def, RUN_def] >>
  qmatch_abbrev_tac `FST (WHILE gd (r m) init) 1 = a + b` >>
  `∀rs0. FST (WHILE gd (r m) (rs0, SOME 1)) 1 = rs0 1 + rs0 2`
    suffices_by rw[Abbr`init`, indexedListsTheory.findi_def] >>
  gen_tac >> 
  Induct_on `rs0 2`
    >- (rw[Once whileTheory.WHILE, Abbr`r`, Abbr`m`, run_machine_1_def] >>
        rw[Once whileTheory.WHILE, Abbr`gd`])
    >> rw[] >> rw[Once whileTheory.WHILE, Abbr`r`, Abbr`m`, run_machine_1_def, Abbr`gd`] 
    >> Cases_on `rs0 2` >> fs[] >> 
    rw[Once whileTheory.WHILE, run_machine_1_def, combinTheory.APPLY_UPDATE_THM]
QED

(*
TODO 1 July
2. Prove addition_correct
*)

Theorem addition_correct:
  correct2 (+) addition 
Proof
  (*rw[correct2_def, init_machine_def, run_machine_1_def] >>
  rw[run_machine_def, addition_def] >>
  metis_tac[] >>*)
  cheat
QED


val _ = export_theory ()