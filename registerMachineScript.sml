open HolKernel Parse boolLib bossLib;
open arithmeticTheory;
open combinTheory;
open whileTheory;
open indexedListsTheory;
open numeralTheory;

val _ = new_theory "registerMachine";


val _ = type_abbrev("reg", “:num”);
val _ = type_abbrev("state", “:num”);

val _ = Datatype ` action = Inc num (state option) | Dec num (state option) (state option) `


(* 
   ---------------------------------- 
   ----- Register Machine Model -----
   ----------------------------------
   *)


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

val rsf_def = Define ` 
  rsf m i = FST (run_machine m (init_machine m i))
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

(* Definition of wellformedness of a register machine :
      Has finite states initial state(q0) is in that machine's set of all states(Q),
      and a valid state only transits to a valid state or NONE.
*)
val wfrm_def = Define `
  wfrm m ⇔ 
    FINITE m.Q ∧
    m.q0 ∈ m.Q ∧
    (∀s. s ∈ m.Q ⇒ FOLDL (λe s. e ∧ ((s-1 ∈ m.Q) ∨ (s = 0))) T (strip_state $ m.tf s)) 
`;

val wfep = EVAL ``wfrm empty``
val wfad = EVAL ``wfrm addition``


(* 
   ---------------------------------- 
   -------- Simple Machines ---------
   ----------------------------------
   *)

(* Returns the given constant by putting it in register 0 *)
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

val test_iden = EVAL ``RUN identity [5; 6]``;

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
            | 1 => Dec 2 (SOME 2) (SOME 4)
            | 2 => Inc 1 (SOME 3)
            | 3 => Inc 3 (SOME 1)
            | 4 => Dec 3 (SOME 5) NONE
            | 5 => Inc 2 (SOME 4)
          ) ;
      q0 := 1 ;
      In := [1;2] ; 
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

(* swapping r1 and r2 for multiplication part can make the machine faster *)
Definition exponential_def:
  exponential  = <|
    Q := {1;2;3;4;5;6;7;8;9;10;11;12;13};
    tf := (λs. case s of 
            | 1 => Dec 0 (SOME 2) NONE
            | 2 => Dec 1 (SOME 3) (SOME 9)
            | 3 => Inc 5 (SOME 4)
            | 4 => Dec 2 (SOME 5) (SOME 7)
            | 5 => Inc 3 (SOME 6)
            | 6 => Inc 4 (SOME 4)
            | 7 => Dec 4 (SOME 8) (SOME 2)
            | 8 => Inc 2 (SOME 7)
            | 9 => Dec 5 (SOME 10) (SOME 11)
            | 10 => Inc 1 (SOME 9)
            | 11 => Dec 2 (SOME 11) (SOME 12)
            | 12 => Dec 3 (SOME 13) (SOME 1)
            | 13 => Inc 2 (SOME 12)
            );
    q0 := 1;
    In := [1;0;2];
    Out := 2;
  |>
End

val exp_t1 = EVAL``RUN exponential [2;3;1]``


Theorem exp_facts[simp]:
  (exponential.In = [1; 0; 2]) ∧
  (exponential.Out = 2) ∧
  (exponential.q0 = 1) ∧
  (exponential.Q = {1;2;3;4;5;6;7;8;9;10;11;12;13}) ∧
  (exponential.tf 1 = Dec 0 (SOME 2) NONE) ∧
  (exponential.tf 2 = Dec 1 (SOME 3) (SOME 9)) ∧
  (exponential.tf 3 = Inc 5 (SOME 4))
Proof
  simp[exponential_def]
QED

Theorem exp_loop1_1:
  WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 exponential) (rs, SOME 4) 
  = WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 exponential) 
    (rs (| 2 |-> 0; 
           3 |-> rs 3 + rs 2;
           4 |-> rs 4 + rs 2 |) 
     , SOME 7) 
Proof
  Induct_on `rs 2` >> rw[] 
    >- (rw[Once whileTheory.WHILE, run_machine_1_def, exponential_def] >>
          `rs 2 = 0` by simp[] >> fs[] >> rw[combinTheory.APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >> 
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >>
          rw[] >> rw[])
    >> qmatch_abbrev_tac`_ = goal` >>
      rw[Ntimes whileTheory.WHILE 3, run_machine_1_def, exponential_def] >>
      rw[combinTheory.APPLY_UPDATE_THM] >>
      `rs 2 = SUC v` by simp[] >> fs[] >> 
      fs[exponential_def, combinTheory.APPLY_UPDATE_THM] >> 
      rw[Abbr`goal`] >> qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
      `rs1 = rs2` suffices_by simp[] >>
      simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
QED

Theorem exp_loop1_2:
  WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 exponential) (rs, SOME 7) 
  = WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 exponential) 
    (rs (| 2 |-> rs 2 + rs 4; 
           4 |-> 0 |) 
     , SOME 2) 
Proof
  Induct_on `rs 4` >> rw[] 
    >- (rw[Once whileTheory.WHILE, run_machine_1_def, exponential_def] >>
          `rs 4 = 0` by simp[] >> fs[] >> rw[combinTheory.APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >> 
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >>
          rw[] >> rw[])
    >> rw[SimpLHS, Ntimes whileTheory.WHILE 2, run_machine_1_def, exponential_def] >>
      rw[combinTheory.APPLY_UPDATE_THM] >>
      `rs 4 = SUC v` by simp[] >> fs[] >> 
      fs[exponential_def, combinTheory.APPLY_UPDATE_THM] >> 
      qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
      `rs1 = rs2` suffices_by simp[] >>
      simp[Abbr `rs1`, Abbr`rs2`] >>
      simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
QED

Theorem exp_loop1:
  (rs 4 = 0) ⇒ (WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 exponential) (rs, SOME 2) 
  = WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 exponential) 
    (rs (| 1 |-> 0; 
           2 |-> rs 4 + rs 2;
           3 |-> rs 3 + rs 1 * rs 2;
           5 |-> rs 5 + rs 1 |) 
     , SOME 9))
Proof
  Induct_on `rs 1` >> rw[] 
    >- (rw[Once whileTheory.WHILE, run_machine_1_def, exponential_def] >>
          `rs 1 = 0` by simp[] >> fs[] >> rw[combinTheory.APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >> 
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >>
          rw[] >> rw[]) 
    >> rw[SimpLHS, Ntimes whileTheory.WHILE 2, run_machine_1_def]
    >> rw[exp_loop1_1, combinTheory.APPLY_UPDATE_THM]
    >> rw[exp_loop1_2, combinTheory.APPLY_UPDATE_THM]
    >> `rs 1 = SUC v` by simp[] >> fs[]
    >> fs[exponential_def, combinTheory.APPLY_UPDATE_THM] 
    >> qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` 
    >> `rs1 = rs2` suffices_by simp[] >> simp[Abbr `rs1`, Abbr`rs2`]
    >> fs[arithmeticTheory.ADD1] 
    >> `(rs 2 + v * rs 2) = rs 2 * (v + 1)` by simp[]
    >> simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] 
    >> rw[]
    >> `0 = rs 4` by simp[]
QED


Theorem exp_loop2:
  WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 exponential) (rs, SOME 9) 
  = WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 exponential) 
    (rs (| 1 |-> rs 1 + rs 5; 
           5 |-> 0 |) 
     , SOME 11) 
Proof
  Induct_on `rs 5` >> rw[] 
    >- (rw[Once whileTheory.WHILE, run_machine_1_def, exponential_def] >>
          `rs 5 = 0` by simp[] >> fs[] >> rw[combinTheory.APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >> 
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >>
          rw[] >> rw[])
    >> rw[SimpLHS, Ntimes whileTheory.WHILE 2, run_machine_1_def, exponential_def] >>
      rw[combinTheory.APPLY_UPDATE_THM] >>
      `rs 5 = SUC v` by simp[] >> fs[] >> 
      fs[exponential_def, combinTheory.APPLY_UPDATE_THM] >> 
      qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
      `rs1 = rs2` suffices_by simp[] >>
      simp[Abbr `rs1`, Abbr`rs2`] >>
      simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
QED

Theorem exp_loop3:
  WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 exponential) (rs, SOME 11) 
  = WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 exponential) 
    (rs (| 2 |-> 0 |) 
     , SOME 12) 
Proof
  Induct_on `rs 2` >> rw[] 
    >- (rw[Once whileTheory.WHILE, run_machine_1_def, exponential_def] >>
          `rs 2 = 0` by simp[] >> fs[] >> rw[combinTheory.APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >> 
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >>
          rw[] >> rw[])
    >> rw[SimpLHS, Once whileTheory.WHILE, run_machine_1_def, exponential_def] >>
      rw[combinTheory.APPLY_UPDATE_THM] >>
      `rs 2 = SUC v` by simp[] >> fs[] >> 
      fs[exponential_def, combinTheory.APPLY_UPDATE_THM] >> 
      qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
      `rs1 = rs2` suffices_by simp[] >>
      simp[Abbr `rs1`, Abbr`rs2`] >>
      simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
QED

Theorem exp_loop4:
WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 exponential) (rs, SOME 12) 
  = WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 exponential) 
    (rs (| 2 |-> rs 2 + rs 3; 
           3 |-> 0 |) 
     , SOME 1)  
Proof
  Induct_on `rs 3` >> rw[] 
    >- (rw[Once whileTheory.WHILE, run_machine_1_def, exponential_def] >>
          `rs 3 = 0` by simp[] >> fs[] >> rw[combinTheory.APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >> 
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >>
          rw[] >> rw[])
    >> rw[SimpLHS, Ntimes whileTheory.WHILE 2, run_machine_1_def, exponential_def] >>
      rw[combinTheory.APPLY_UPDATE_THM] >>
      `rs 3 = SUC v` by simp[] >> fs[] >> 
      fs[exponential_def, combinTheory.APPLY_UPDATE_THM] >> 
      qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
      `rs1 = rs2` suffices_by simp[] >>
      simp[Abbr `rs1`, Abbr`rs2`] >>
      simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
QED

Theorem exp_correct:
  ∀a b. RUN exponential [a;b;1] = a ** b 
Proof
  rw[init_machine_def, run_machine_def, RUN_def] >>
  qmatch_abbrev_tac `FST (WHILE gd (r m) init) 2 = a ** b` >>
  `∀rs0. ((rs0 4 = 0) ∧ (rs0 3 = 0) ∧ (rs0 5 = 0)) ⇒
     (FST (WHILE gd (r m) (rs0, SOME 1)) 2 = (rs0 1 ** rs0 0) * rs0 2)`
     suffices_by rw[Abbr`init`, indexedListsTheory.findi_def] >> rw[] >> 
  Induct_on `rs0 0` 
    >- (rw[exponential_def, Ntimes whileTheory.WHILE 2, Abbr`gd`, Abbr`r`, Abbr`m`, run_machine_1_def] >>
        `rs0 0 = 0` by simp[] >> fs[])
    >> rw[]
    >> rw[Once whileTheory.WHILE, run_machine_1_def, Abbr`gd`, Abbr`r`, Abbr`m`]
    >> rw[APPLY_UPDATE_THM, exp_loop1]
    >> rw[APPLY_UPDATE_THM, exp_loop2]
    >> rw[APPLY_UPDATE_THM, exp_loop3]
    >> rw[APPLY_UPDATE_THM, exp_loop4]
    >> `rs0 0 = SUC v` by simp[] >> fs[]
    >> rw[EXP]
QED

(*
Definition gt2_def:
  gt2 = <||>
End
*)

(* 0: input; 1: acc;*)
Definition factorial_def:
  factorial = <|
    Q := {0;1;2;3;4;5;6;7;8;9;10};
    tf := (λn. case n of 
            | 0 => Inc 1 (SOME 1)
            | 1 => Dec 0 (SOME 2) NONE
            | 2 => Inc 2 (SOME 3)
            | 3 => Dec 1 (SOME 4) (SOME 9)
            | 4 => Dec 2 (SOME 5) (SOME 7)
            | 5 => Inc 3 (SOME 6)
            | 6 => Inc 4 (SOME 4) 
            | 7 => Dec 4 (SOME 8) (SOME 3)
            | 8 => Inc 2 (SOME 7)
            | 9 => Dec 3 (SOME 10) (SOME 1)
            | 10 => Inc 1 (SOME 9)
           );
      q0 := 0 ;
      In := [0] ;
      Out := 1 ;
      |>
End

val fac_t1 = EVAL ``RUN factorial [0]``;
val fac_t1 = EVAL ``RUN factorial [1]``;
val fac_t1 = EVAL ``RUN factorial [3]``;
val fac_t1 = EVAL ``RUN factorial [5]``;


Theorem fac_facts[simp]:
  (factorial.In = [0]) ∧
  (factorial.Out = 1) ∧
  (factorial.q0 = 0) ∧
  (factorial.Q = {0;1;2;3;4;5;6;7;8;9;10}) ∧
  (factorial.tf 0 = Inc 1 (SOME 1)) ∧
  (factorial.tf 1 = Dec 0 (SOME 2) NONE) ∧
  (factorial.tf 2 = Inc 2 (SOME 3)) ∧
  (factorial.tf 3 = Dec 1 (SOME 4) (SOME 9))
Proof
  simp[factorial_def]
QED

Theorem fac_loop1_1:
  WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 factorial) (rs, SOME 4) 
  = WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 factorial) 
    (rs (| 2 |-> 0; 
           3 |-> rs 3 + rs 2;
           4 |-> rs 4 + rs 2 |) 
     , SOME 7) 
Proof
  Induct_on `rs 2` >> rw[] 
    >- (rw[Once whileTheory.WHILE, run_machine_1_def, factorial_def] >>
          `rs 2 = 0` by simp[] >> fs[] >> rw[combinTheory.APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >> 
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >>
          rw[] >> rw[])
    >> qmatch_abbrev_tac`_ = goal` >>
      rw[Ntimes whileTheory.WHILE 3, run_machine_1_def, factorial_def] >>
      rw[combinTheory.APPLY_UPDATE_THM] >>
      `rs 2 = SUC v` by simp[] >> fs[] >> 
      fs[factorial_def, combinTheory.APPLY_UPDATE_THM] >> 
      rw[Abbr`goal`] >> qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
      `rs1 = rs2` suffices_by simp[] >>
      simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
QED

Theorem fac_loop1_2:
  WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 factorial) (rs, SOME 7) 
  = WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 factorial) 
    (rs (| 2 |-> rs 2 + rs 4; 
           4 |-> 0 |) 
     , SOME 3) 
Proof
  Induct_on `rs 4` >> rw[] 
    >- (rw[Once whileTheory.WHILE, run_machine_1_def, factorial_def] >>
          `rs 4 = 0` by simp[] >> fs[] >> rw[combinTheory.APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >> 
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >>
          rw[] >> rw[])
    >> rw[SimpLHS, Ntimes whileTheory.WHILE 2, run_machine_1_def, factorial_def] >>
      rw[combinTheory.APPLY_UPDATE_THM] >>
      `rs 4 = SUC v` by simp[] >> fs[] >> 
      fs[factorial_def, combinTheory.APPLY_UPDATE_THM] >> 
      qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
      `rs1 = rs2` suffices_by simp[] >>
      simp[Abbr `rs1`, Abbr`rs2`] >>
      simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
QED


Theorem fac_loop1:
  (rs 4 = 0) ⇒ (WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 factorial) (rs, SOME 3) 
  = WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 factorial) 
    (rs (| 1 |-> 0; 
           2 |-> rs 4 + rs 2;
           3 |-> rs 3 + rs 1 * rs 2|) 
     , SOME 9))
Proof
  Induct_on `rs 1` >> rw[] 
    >- (rw[Once whileTheory.WHILE, run_machine_1_def, factorial_def] >>
          `rs 1 = 0` by simp[] >> fs[] >> rw[combinTheory.APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >> 
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >>
          rw[] >> rw[]) 
    >> rw[Once WHILE, run_machine_1_def]
    >> rw[fac_loop1_1, combinTheory.APPLY_UPDATE_THM]
    >> rw[fac_loop1_2, combinTheory.APPLY_UPDATE_THM]
    >> `rs 1 = SUC v` by simp[] >> fs[]
    >> rw[factorial_def] 
    >> qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` 
    >> `rs1 = rs2` suffices_by simp[] >> simp[Abbr `rs1`, Abbr`rs2`]
    >> fs[arithmeticTheory.ADD1] 
    >> `(rs 2 + v * rs 2) = rs 2 * (v + 1)` by simp[]
    >> simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] 
    >> rw[]
    >> `0 = rs 4` by simp[]
QED

Theorem fac_loop2:
  WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 factorial) (rs, SOME 9) 
  = WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 factorial) 
    (rs (| 1 |-> rs 1 + rs 3; 
           3 |-> 0 |) 
     , SOME 1) 
Proof
  Induct_on `rs 3` >> rw[] 
    >- (rw[Once whileTheory.WHILE, run_machine_1_def, factorial_def] >>
          `rs 3 = 0` by simp[] >> fs[] >> rw[combinTheory.APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >> 
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >>
          rw[] >> rw[])
    >> rw[SimpLHS, Ntimes whileTheory.WHILE 2, run_machine_1_def, factorial_def] >>
      rw[combinTheory.APPLY_UPDATE_THM] >>
      `rs 3 = SUC v` by simp[] >> fs[] >> 
      fs[factorial_def, combinTheory.APPLY_UPDATE_THM] >> 
      qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
      `rs1 = rs2` suffices_by simp[] >>
      simp[Abbr `rs1`, Abbr`rs2`] >>
      simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
QED

Theorem fac_loop:
  ((rs 4 = 0) ∧ (rs 3 = 0)) 
  ⇒
  (WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 factorial) (rs, SOME 1) 
  = (rs (| 0 |-> 0;
           1 |-> rs 1 * ((FACT (rs 2 + rs 0)) DIV (FACT (rs 2))); 
           2 |-> rs 0 + rs 2|) 
     , NONE) )
Proof
  Induct_on `rs 0` >> rw[] 
    >- (rw[APPLY_UPDATE_THM, factorial_def, Ntimes whileTheory.WHILE 2, run_machine_1_def] >>
        `rs 0 = 0` by simp[] >> fs[] >> 
         rw[APPLY_UPDATE_ID, DIVMOD_ID, FACT_LESS] >>
         rw[FUN_EQ_THM, APPLY_UPDATE_THM] >> Cases_on `x` >> simp[]
        )
    >> rw[Once WHILE, run_machine_1_def]
    >> rw[Once WHILE, run_machine_1_def]
    >> rw[APPLY_UPDATE_THM, fac_loop1]
    >> rw[APPLY_UPDATE_THM, fac_loop2]

    >> rw[FUN_EQ_THM, APPLY_UPDATE_THM]
    >> Cases_on `x` >> simp[]  
       >> Cases_on `n` 
          >- (simp[] >> `rs 0 = SUC v` by simp[] >> fs[] >>
              `rs 2 + SUC v = rs 2 + v + 1` by simp[] >> rw[] >>

              rw[FACT, DIVMOD_ID, numeral_fact] >> 
              `FACT (SUC (rs 2)) = `) 


    >> ` rs 1 * (rs 2 + 1) * (FACT (rs 0 + rs 2) DIV FACT (rs 2 + 1)) = rs 1 * (FACT (rs 0 + rs 2) DIV FACT (rs 2))`
    suffices_by rw[FUN_EQ_THM, APPLY_UPDATE_THM, APPLY_UPDATE_ID] >> rw[] >> fs[]
    `rs 1 * (FACT (rs 0 + rs 2) DIV FACT (rs 2)) =rs 1 * (rs 2 + 1) * (FACT (rs 0 + rs 2) DIV FACT (rs 2 + 1)) ` by simp[]>>  Cases_on `1 = x` >> fs[]
    >> `rs 0 = SUC v` by simp[] >> fs[] >> fs[ADD1]
    >> `rs2 + 1 = SUC rs2` by simp[ADD1] >> fs[] `0 = rs 3` by simp[]
    >> `FACT (rs 2 + 1) =(rs 2 + 1) * FACT (rs 2) ` by simp[FACT, ADD1]


    
    >> rw[APPLY_UPDATE_THM, APPLY_UPDATE_ID, ADD1, FACT, UPDATE_APPLY, UPDATE_APPLY_ID, UPDATE_APPLY_IMP_ID]

    >> rw[SimpLHS, Ntimes WHILE 2, run_machine_1_def, APPLY_UPDATE_THM, fac_loop1, fac_loop2]
    >> rw[factorial_def]
    >> rw[APPLY_UPDATE_THM, APPLY_UPDATE_ID, ADD1, FACT]
QED

Theorem fac_correct:
  ∀a. RUN factorial [a] = FACT a 
Proof
  rw[RUN_def, run_machine_def, init_machine_def] >>
  qmatch_abbrev_tac `FST (WHILE gd (r m) init) 1 = _` >>
  `∀rs0. ((rs0 4 = 0) ∧ (rs0 3 = 0) ∧ (rs0 1 = 0) ∧ (rs0 2 = 0)) ⇒
     (FST (WHILE gd (r m) (rs0, SOME 0)) 1 = FACT (rs0 0))`
     suffices_by rw[Abbr`init`, indexedListsTheory.findi_def] >>
  rw[Abbr`r`, Abbr`m`, Abbr`gd`] >> 
  rw[Once WHILE, run_machine_1_def] >>
  Induct_on `rs0 0` 
    >- (rw[APPLY_UPDATE_THM, factorial_def, Ntimes whileTheory.WHILE 2, run_machine_1_def] >>
        `rs0 0 = 0` by simp[] >> fs[] >> rw[numeralTheory.numeral_fact])
    >> rw[]
    >> rw[Ntimes WHILE 2, run_machine_1_def, APPLY_UPDATE_THM, fac_loop1, fac_loop2]
    >> rw[APPLY_UPDATE_THM, fac_loop1]
    >> rw[APPLY_UPDATE_THM, fac_loop2]
    >> `rs0 0 = SUC v` by simp[] >> fs[]
    >> rw[APPLY_UPDATE_THM]
QED


Theorem exp_correct:
  ∀a b. RUN exponential [a;b;1] = a ** b 
Proof
  rw[init_machine_def, run_machine_def, RUN_def] >>
  qmatch_abbrev_tac `FST (WHILE gd (r m) init) 2 = a ** b` >>
  `∀rs0. ((rs0 4 = 0) ∧ (rs0 3 = 0) ∧ (rs0 5 = 0)) ⇒
     (FST (WHILE gd (r m) (rs0, SOME 1)) 2 = (rs0 1 ** rs0 0) * rs0 2)`
     suffices_by rw[Abbr`init`, indexedListsTheory.findi_def] >> rw[] >> 
  Induct_on `rs0 0` 
    >- (rw[exponential_def, Ntimes whileTheory.WHILE 2, Abbr`gd`, Abbr`r`, Abbr`m`, run_machine_1_def] >>
        `rs0 0 = 0` by simp[] >> fs[])
    >> rw[]
    >> rw[Once whileTheory.WHILE, run_machine_1_def, Abbr`gd`, Abbr`r`, Abbr`m`]
    >> rw[APPLY_UPDATE_THM, exp_loop1]
    >> rw[APPLY_UPDATE_THM, exp_loop2]
    >> rw[APPLY_UPDATE_THM, exp_loop3]
    >> rw[APPLY_UPDATE_THM, exp_loop4]
    >> `rs0 0 = SUC v` by simp[] >> fs[]
    >> rw[EXP]
QED



(* 
   ---------------------------------- 
   ------      Projection      ------
   ----------------------------------
   *)

(* Returns the n-th element of the list ns, indexing from 0 *)
Definition Pi_def:
  Pi n ns = <|
      Q := {0;1};
      tf := (λs. case s of 
                | 0 => Inc 0 (SOME 1)
                | 1 => Dec 0 NONE NONE
        );
      q0 := 1;
      In := GENLIST I ns;
      Out := n;
    |>
End
 (* 
   -------------------------------------- 
   ------------ Composition  ------------
   -------------------------------------- 
   *)

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
        m'  = HD mms;
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

(*
val Cnd_def = Define `
  Cnd m ms =  
    let mms = MAPi (λi mm. mrInst (i+2) mm) (m::ms);
        m' = HD mms;
        ms' = TL mms;
        ics = FLAT (MAP (λmm. MAPi (λi r. dup0 (npair 0 i) r (npair 1 0)) mm.In) ms');
        ocs = MAPi (λi mm. dup0 mm.Out (EL i m'.In) (npair 1 0)) ms';
        mix = ics++ms'++ocs++[m'];
        mix' = MAPi msInst mix;
    in 
      link_all mix' with In := MAP (λm. MAP (npair 0) m.In) ms
`;
*)



(* 
   ---------------------------------- 
   ------ Primitive Recursion  ------
   ----------------------------------
*)


val end_plink_def = Define `
  (end_plink (Inc q d0) d = Inc q (upd d0 d))
    ∧
  (end_plink (Dec q d1 d2) d = Dec q (upd d1 d) d2)
`;


val plinktf_def = Define`
  linktf m1Q tf1 tf2 m2init s = 
     if s ∈ m1Q then end_plink (tf1 s) m2init
     else tf2 s
`;

(* Partial link - only links state option 1 of m1 to m2 *)
Definition plink:
  plink m1 m2 = <|
    Q := m1.Q ∪ m2.Q;
    tf := plinktf m1.Q m1.tf m2.tf m2.q0;
    q0 := m1.q0;
    In := m1.In;
    Out := m2.Out;
  |>
End

(* Recursive call function, k stands for k-th iteration *)
Definition Rc_def:
  Rc gd step k = 
      gd' = rename gd k
      step' = rename step k 
      copy = copy gd' output to step' input 
      mix = plink gd' copy step'

End

(* Pr.In is in the form of ``accumulator :: counter :: limit :: inputs``.
   base: machine which computes the base case of the premitive recursion.
   step  : the recursive step which checks the guard then perform action
     followed by recursive call
   *)
Definition Pr_def:
  Pr base step = 
      let base' = mrInst 0 base;
          step' = mrInst 1 step;
          ics = FLAT (MAP (λmm. MAPi (λi r. dup0 (npair 0 i) r (npair 1 0)) mm.In) gdstep');
          copy acc step.In 0
          copy counter step.In 1
          copy  drop step.In 2
    in 
      In := MAP (npair 0) (GENLIST I $ LENGTH base.In + 1)

End

RUN (Pr base step) [...] 

Pr guard [i1...in]
base [i1...in]
step counter acc [i1...in]

val Cn_def = Define `
  Cn m ms = 
    let isz = LENGTH (HD ms).In;
        mms = MAPi (λi mm. mrInst (i+2) mm) (m::ms);
        m'  = HD mms;
        ms' = TL mms;
        ics = FLAT (MAP (λmm. MAPi (λi r. dup0 (npair 0 i) r (npair 1 0)) mm.In) ms');
        ocs = MAPi (λi mm. dup0 mm.Out (EL i m'.In) (npair 1 0)) ms';
        mix = ics++ms'++ocs++[m'];
        mix' = MAPi msInst mix;
    in 
      link_all mix' with In := MAP (npair 0) (GENLIST I isz)
`;

(* 
   ---------------------------------- 
   ------         Mu           ------
   ----------------------------------
*)


Definition Mu_def:

End


(* 
   ---------------------------------- 
   --------     Proving     ---------
   ----------------------------------
   *)


(* Machine and math operation returns the same output *)

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
  rw[Abbr`r`, Abbr`m`, Abbr`gd`] >> 
  Induct_on `rs0 2` >>
  rw[Ntimes whileTheory.WHILE 2, run_machine_1_def, combinTheory.APPLY_UPDATE_THM] 
QED


Theorem addition_correct:
  correct2 (+) addition 
Proof
  rw[addition_def, correct2_def, init_machine_def, run_machine_def, RUN_def] >>
  qmatch_abbrev_tac `FST (WHILE gd (r m) init) 1 = a + b` >>
  `∀rs0. FST (WHILE gd (r m) (rs0, SOME 1)) 1 = rs0 1 + rs0 2`
    suffices_by rw[Abbr`init`, indexedListsTheory.findi_def] >>
  gen_tac >>
  Induct_on `rs0 2` 
    >- (`∀rs0. FST (WHILE gd (r m) (rs0, SOME 4)) 1 = rs0 1` 
          suffices_by (rw[] >> rw[Once whileTheory.WHILE, Abbr`r`, Abbr`m`, run_machine_1_def]) 
        >> gen_tac
        >> Induct_on `rs0 3`
        >> rw[Abbr`gd`, Abbr`r`, Abbr`m`]
        >> rw[Ntimes whileTheory.WHILE 2, run_machine_1_def, combinTheory.APPLY_UPDATE_THM])
    >> rw[Abbr`r`, Abbr`m`, Abbr`gd`] 
    >> rw[Ntimes whileTheory.WHILE 3, run_machine_1_def, combinTheory.APPLY_UPDATE_THM] 
QED

     
Theorem mult_loop1:
  WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 multiplication) (rs, SOME 2) 
  = WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 multiplication) 
    (rs (| 1 |-> 0; 
           2 |-> rs 2 + rs 1; 
           3 |-> rs 3 + rs 1 |) 
     , SOME 5) 
Proof
  Induct_on `rs 1` >> rw[] 
    >- (rw[Once whileTheory.WHILE, run_machine_1_def, multiplication_def] >>
          `rs 1 = 0` by simp[] >> fs[] >> rw[combinTheory.APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >> 
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >>
          rw[] >> rw[])
    >> qmatch_abbrev_tac`_ = goal` >>
      rw[Ntimes whileTheory.WHILE 3, run_machine_1_def, multiplication_def] >>
      rw[combinTheory.APPLY_UPDATE_THM] >>
      `rs 1 = SUC v` by simp[] >> fs[] >> 
      fs[multiplication_def, combinTheory.APPLY_UPDATE_THM] >> 
      rw[Abbr`goal`] >> qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
      `rs1 = rs2` suffices_by simp[] >>
      simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
QED

Theorem mult_loop2:
  WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 multiplication) (rs, SOME 5) 
  = WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 multiplication) 
    (rs (| 1 |-> rs 1 + rs 3; 
           3 |-> 0 |) 
     , SOME 1) 
Proof
  Induct_on `rs 3` >> rw[] 
    >- (rw[Once whileTheory.WHILE, run_machine_1_def, multiplication_def] >>
          `rs 3 = 0` by simp[] >> fs[] >> rw[combinTheory.APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >> 
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >>
          rw[] >> rw[])
    >> rw[SimpLHS, Ntimes whileTheory.WHILE 2, run_machine_1_def, multiplication_def] >>
      rw[combinTheory.APPLY_UPDATE_THM] >>
      `rs 3 = SUC v` by simp[] >> fs[] >> 
      fs[multiplication_def, combinTheory.APPLY_UPDATE_THM] >> 
      qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
      `rs1 = rs2` suffices_by simp[] >>
      simp[Abbr `rs1`, Abbr`rs2`] >>
      simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
QED

Theorem mult_facts[simp]:
  (multiplication.In = [0; 1]) ∧
  (multiplication.Out = 2) ∧
  (multiplication.q0 = 1) ∧
  (multiplication.Q = {1;2;3;4;5;6}) ∧
  (multiplication.tf 1 = Dec 0 (SOME 2) NONE)
Proof
  simp[multiplication_def]
QED
        

Theorem multi_correct:
  correct2 $* multiplication
Proof  
  rw[correct2_def, init_machine_def, run_machine_def, RUN_def] >>
  qmatch_abbrev_tac `FST (WHILE gd (r m) init) 2 = a * b` >>
  `∀rs0. (rs0 3 = 0) ⇒ (FST (WHILE gd (r m) (rs0, SOME 1)) 2 = rs0 0 * rs0 1 + rs0 2)` 
    suffices_by rw[Abbr`init`, indexedListsTheory.findi_def] >> rw[] >>
  Induct_on `rs0 0` >> rw[]
    >- (rw[multiplication_def, Ntimes whileTheory.WHILE 2, Abbr`gd`, Abbr`r`, Abbr`m`, run_machine_1_def] >>
        `rs0 0 = 0` by simp[] >> fs[])
    >> rw[Once whileTheory.WHILE, run_machine_1_def, Abbr`gd`, Abbr`r`, Abbr`m`, mult_loop1]
    >> rw[mult_loop2]
    >> rw[combinTheory.APPLY_UPDATE_THM] >> `rs0 0 = SUC v` by simp[] >> fs[]
    >> fs[arithmeticTheory.ADD1]
QED


Theorem dup0_correct:
  ∀a b c. (rsf dup0 a b c) a = a 
Proof

QED

Theorem link_correct:
  ∀m1 m2 i. RUN (link m1 m2) i = run_machine m2 (rsf m1 i, SOME m2.q0)
Proof
  
QED

Definition correct1_def:
  correct1 f m ⇔ ∀a. RUN m [a] = f a   
End

Theorem double_correct:
  correct1 ( *2 ) double
Proof

QED

Theorem identity_correct:
  correct1 
Proof

QED

Theorem rename1r_correct:
  ∀mnum. correct1 f m ⇒ correct1 f (mrInst mnum m)
Proof
  rw[mrInst_def, correct1_def, RUN_def, run_machine_def, init_machine_def] >>
  qmatch_abbrev_tac `FST (WHILE gd (r m) init) pair = f a` >>
  rw[rInst_def] >>

QED

Theorem rename2r_correct:
Proof
QED

Theorem rename1s_correct:
Proof
QED

Theorem rename2s_correct:
Proof
QED

(*
TODO  1 July
3. Prove 
      correct1 f m1 /\ correct1 g m2 
      ==> correct1 (f o g) (Cn m1 m2)
  even more general -> a list of ms  ...
*)

Theorem Cn1_correct:
  correct1 f1 m1 ∧ correct1 f2 m2 ⇒ ∀n. RUN (Cn m1 [m2]) [n] = (f1 o f2) n  
Proof
  rw[correct1_def, init_machine_def, run_machine_def, RUN_def, rsf_def] >>
  rw[Cn_def] >>

QED

(*
Code :
  1. Comment out unfinished proofs or cheat
  2. one machine one proof
  3. How much should i try to finish 
  4. better to open theory or just use Theorey.theorem

Report:
  1. Is using stones to describe the change of numbers in the register a good way or 
  is it not formal enough.
  2. call theorem or lemma
  3. to describe the theorem, using words or math format
  4. smaller machines: describe in report or comment or both?
  5. make transfer and empty more general?
 *)

val _ = export_theory ()