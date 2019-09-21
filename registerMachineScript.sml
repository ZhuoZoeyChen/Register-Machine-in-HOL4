open HolKernel Parse boolLib bossLib;
open arithmeticTheory;
open combinTheory;
open whileTheory;
open indexedListsTheory;
open numeralTheory;
open primrecfnsTheory;
open listTheory;

val _ = new_theory "registerMachine";


Type reg = “:num”;
Type state = “:num”;

Datatype:
  action = Inc num (state option) | Dec num (state option) (state option) 
End


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
Datatype:
  rm = <|
    Q : state set; 
    tf : state -> action ;
    q0 : state ;
    In : reg list ;
    Out : reg 
  |>
End

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


(* 
   ---------------------------------- 
   -------- Simple Machines ---------
   ----------------------------------
*)

(* Returns the given constant by putting it in register 0 *)
Definition const_def:
  const n =
    if n = 0 then  <|
       Q := {1} ;
       tf := (λs. Inc 0 NONE);
       q0 := 1 ; 
       In := [0] ;
       Out := 1 ;
    |>
    else 
      if n = 1 then <|
         Q := {1} ;
         tf := (λn. case n of 
                | 1 => Inc 1 NONE
              );
         q0 := 1 ;
         In := [0] ;
         Out := 1 ;
        |>
    else let m = const (n-1)
     in 
      <|
         Q  := {n} ∪ m.Q ;
         tf := m.tf (| n |-> Inc 1 (SOME (n-1)) |) ;
         q0 := n ;
         In := [0] ;
         Out := 1 ;
      |>
End


val identity_def = Define `
  identity = <|
  Q := {0;1};
  tf := (λs. case s of 
                | 0 => Inc 1 (SOME 1)
                | 1 => Dec 1 NONE NONE
        );
  q0 := 0;
  In := [0];
  Out := 0;
  |>
`;


val identity'_def = Define `
  identity' = <|
  Q := {0;1};
  tf := (λs. case s of 
                | 0 => Inc 0 (SOME 1)
                | 1 => Dec 0 NONE NONE
        );
  q0 := 0;
  In := [1;0;2];
  Out := 0;
  |>
`;

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

val empty'_def = Define `
  empty' m = <| 
      Q := {0} ; 
      tf := (λn. Dec m (SOME 0) NONE) ;
      q0 := 0;
      In := [m] ;
      Out := m ;
  |>
`;

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

(* 
   ---------------------------------- 
   -----    Helper Functions    -----
   ----------------------------------
*)

Definition correct1_def:
  correct1 f m ⇔ ∀a. RUN m [a] = f a 
End

val correct2_def = Define `
  correct2 f m ⇔ ∀a b. RUN m [a;b] = f a b
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

val dup_def = Define `
  dup r1 r2 r3= <| 
    Q := {0;1;2;3;4;5};
    tf := (λs. case s of 
            | 0 => Dec r2 (SOME 0) (SOME 1)
            | 1 => Dec r1 (SOME 2) (SOME 4)
            | 2 => Inc r2 (SOME 3)
            | 3 => Inc r3 (SOME 1) 
            | 4 => Dec r3 (SOME 5) NONE
            | 5 => Inc r1 (SOME 4)
            );
    q0 := 0;
    In := [r1];
    Out := r2;
  |>
`;


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


val sInst_def = Define `
  (sInst mnum (Inc r sopt) = Inc r (OPTION_MAP (npair mnum) sopt))
    ∧
  (sInst mnum (Dec r sopt1 sopt2) = 
      Dec r (OPTION_MAP (npair mnum) sopt1) (OPTION_MAP (npair mnum) sopt2))
`;

val msInst_def = Define `
  msInst mnum m = <|
    Q := IMAGE (npair mnum) m.Q;
    tf := sInst mnum o m.tf o nsnd;
    q0 := npair mnum m.q0;
    In := m.In;
    Out := m.Out;
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


(* 
   -------------------------------------------------------------   
   -------- More Complicated machines and their proofs ---------
   -------------------------------------------------------------  
*)

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


(* swapping r1 and r2 for multiplication part can make the machine faster *)
Definition exponential_def:
  exponential  = <|
    Q := {1;2;3;4;5;6;7;8;9;10;11;12;13;14};
    tf := (λs. case s of 
            | 14 => Inc 2 (SOME 1)
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
    q0 := 14;
    In := [1;0];
    Out := 2;
  |>
End


Theorem exp_facts[simp]:
  (exponential.In = [1; 0]) ∧
  (exponential.Out = 2) ∧
  (exponential.q0 = 14) ∧
  (exponential.Q = {1;2;3;4;5;6;7;8;9;10;11;12;13;14}) ∧
  (exponential.tf 1 = Dec 0 (SOME 2) NONE) ∧
  (exponential.tf 2 = Dec 1 (SOME 3) (SOME 9)) ∧
  (exponential.tf 3 = Inc 5 (SOME 4)) ∧
  (exponential.tf 14 = Inc 2 (SOME 1))
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
    >> fs[ADD1] 
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
  ∀a b. RUN exponential [a;b] = a ** b 
Proof
  rw[init_machine_def, run_machine_def, RUN_def, findi_def] >> 
  rw[Once WHILE, run_machine_1_def] >>
  qmatch_abbrev_tac `FST (WHILE gd (r m) init) 2 = a ** b` >>
  `∀rs0. ((rs0 4 = 0) ∧ (rs0 3 = 0) ∧ (rs0 5 = 0)) ⇒
     (FST (WHILE gd (r m) (rs0, SOME 1)) 2 = (rs0 1 ** rs0 0) * rs0 2)`
     suffices_by rw[Abbr`init`, APPLY_UPDATE_THM, findi_def] >> rw[] >> 
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


(* 0: input *)
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
    >- (rw[Once WHILE, run_machine_1_def, factorial_def] >>
          `rs 3 = 0` by simp[] >> fs[] >> rw[APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >> 
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, APPLY_UPDATE_THM] >>
          rw[] >> rw[])
    >> rw[SimpLHS, Ntimes WHILE 2, run_machine_1_def, factorial_def] >>
      rw[APPLY_UPDATE_THM] >>
      `rs 3 = SUC v` by simp[] >> fs[] >> 
      fs[factorial_def, APPLY_UPDATE_THM] >> 
      qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
      `rs1 = rs2` suffices_by simp[] >>
      simp[Abbr `rs1`, Abbr`rs2`] >>
      simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
QED


Theorem fac_correct:
  ∀a. RUN factorial [a] = FACT a 
Proof
  rw[RUN_def, run_machine_def, init_machine_def, findi_def] >>
  rw[Once WHILE, run_machine_1_def] >>
  qmatch_abbrev_tac `FST (WHILE gd (r m) (init, SOME 1)) 1 = _` >>
  `∀rs0. ((rs0 4 = 0) ∧ (rs0 3 = 0) ∧ (rs0 1 = FACT (rs0 2))) ⇒
     (FST (WHILE gd (r m) (rs0 , SOME 1)) 1 = FACT (rs0 0 + rs0 2))`
     suffices_by rw[Abbr`init`, APPLY_UPDATE_THM, FACT] >>
  rw[] >>
  Induct_on `rs0 0` >> rw[Abbr`r`, Abbr`m`, Abbr`gd`]
    >- (rw[APPLY_UPDATE_THM, factorial_def, Ntimes whileTheory.WHILE 2, run_machine_1_def] >>
        `rs0 0 = 0` by simp[] >> fs[] >> rw[numeralTheory.numeral_fact]
        >>rw[Once WHILE, run_machine_1_def] >> rw[APPLY_UPDATE_THM])
    >> rw[Once WHILE, run_machine_1_def]
    >> rw[Once WHILE, run_machine_1_def]
    >> rw[APPLY_UPDATE_THM, fac_loop1]
    >> rw[APPLY_UPDATE_THM, fac_loop2]
    >> `rs0 0 = SUC v` by simp[] >> fs[]
    >> qmatch_abbrev_tac `FST (WHILE _ _ (ss, SOME 1)) 1 = _`
    >> first_x_assum (qspec_then `ss` mp_tac)
    >> simp[Abbr`ss`, APPLY_UPDATE_THM]
    >> simp[GSYM ADD1, FACT]
    >> rw[APPLY_UPDATE_THM]
    >> rw[ADD1]
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
      q0 := 0;
      In := GENLIST I ns;
      Out := n;
    |>
End

 (* 
   -------------------------------------- 
   ------------ Composition  ------------
   -------------------------------------- 
   *)



val Cn_def = Define `
  Cn m ms = 
    let isz = LENGTH (HD ms).In;
        mms = MAPi (λi mm. mrInst (i+2) mm) (m::ms);
        m'  = HD mms;
        ms' = TL mms;
        ics = FLAT (MAP (λmm. MAPi (λi r. dup (npair 0 i) r (npair 1 0)) mm.In) ms');
        ocs = MAPi (λi mm. dup mm.Out (EL i m'.In) (npair 1 0)) ms';
        mix = ics++ms'++ocs++[m'];
        mix' = MAPi msInst mix;
    in 
      link_all mix' with In := MAP (npair 0) (GENLIST I isz)
`;


(* 
   ---------------------------------- 
   ------ Primitive Recursion  ------
   ----------------------------------
*)


Definition loopguard:
  loopguard guard step = <|
    Q:= {npair 0 2} ∪ step.Q;
    tf := (λs. if s=(npair 0 2) then (Dec guard (SOME step.q0) NONE)
                else end_link (step.tf s) (npair 0 2));
    q0 := (npair 0 2);
    In := [guard] ++ step.In;
    Out := step.Out;
  |>
End



Definition count:
  count = <|
    Q:= {(npair 0 0)};
    tf := (λs. Inc (npair 0 0) NONE);
    q0 := (npair 0 0);
    In := [(npair 0 0)];
    Out := (npair 0 0);
  |>
End

(*
(0,0) counter
(0,1) acc
(0,2) guard

Pr guard [i1...in]
base [i1...in]
step counter acc [i1...in]
*)

Definition Pr_def:
  Pr base step = 
      let base' = mrInst 2 base;
          step' = mrInst 3 step;
          ptb   = MAPi (λi r. dup (npair 0 (i+3)) r (npair 1 0)) base'.In; 
          btp   = dup base'.Out (npair 0 1) (npair 1 0) ;
          pts0  = dup (npair 0 0) (EL 0 step'.In) (npair 1 0);
          pts1  = dup (npair 0 1) (EL 1 step'.In) (npair 1 0);
          pts   = MAPi (λi r. dup (npair 0 (i+3)) r (npair 1 0)) (DROP 2 step'.In);
          stp   = dup step'.Out (npair 0 1) (npair 1 0);
          mix1   = ptb ++ [base'] ++ [btp];
          mix2   = pts0::pts1::pts ++ [step'] ++ [count] ++ [stp];
          mix1'  = MAPi (λi m. msInst (i+1) m) mix1;
          mix1'' = MAP (msInst 2) mix1';
          mix2'  = MAPi (λi m. msInst (i+1) m) mix2;
          mix2'' = MAP (msInst 3) mix2';
          m2     = link_all mix2'';
          m2'  = loopguard (npair 0 2) m2;
          mix  = mix1''++[m2'];
    in 
      link_all mix with In := MAP (λr. npair 0 (r+2)) (GENLIST I $ LENGTH base.In + 1)
End


Definition add1_def:
  add1 = <|
    Q:={0};
    tf:=(λs. Inc 0 NONE);
    q0:=0;
    In:=[0];
    Out:=0;
  |>
End



(* 
   ---------------------------------- 
   ----  Minimisation Function   ----
   ----------------------------------
*)

(*
Definition Mu_def:
   Mu f =
      let 
        f' = mrInst 1 f;
        count' = count ++ f' ;
        mtf = dup Mu.In f'.In (npair 0 1);
        ftg = dup f'.Out guard.In (npair 0 1);
        guard' = plink (msInst 0 guard) (msInst 1 count); 
        mix = mtf ++ f' ++ ftg;
        mix' = MAPi (λi m. msInst (i+2) m) mix;
      in 
        link with In := [(npair 0 0)]
End
*)

(* 
   ---------------------------------------------
   ----  Proving RM -> Recursive Functions  ----
   ---------------------------------------------
   - 0 
   - SUC
   - Projection
   - Composition
   - Primitive Recursion
   - Minimisation
*)

(* Helper functions *)
Definition correct_def:
  correct m f a ⇔ ∀l. LENGTH l = a ⇒ RUN m l = f l
End

Definition run_step_def:
  run_step m rsq 0 = rsq ∧
  run_step m rsq (SUC n) = run_step m (run_machine_1 m rsq) n 
End

Theorem run_one_step:
  ∀m rsq n. run_machine_1 m (run_step m rsq n) = run_step m rsq (SUC n)
Proof 
  Induct_on `n` >> simp[run_step_def]
QED

Theorem combo_steps:
 ∀m rs q1 n1 n2.  run_step m (run_step m (rs, SOME q1) n1) n2
  = run_step m (rs, SOME q1) (n1+n2)
Proof 
  Induct_on `n2` 
  >- simp[run_step_def]
  >> rw[run_step_def, run_machine_def]
  >> `n1 + SUC n2 = SUC n1 + n2` by fs[]
  >> simp[]
  >> `run_step m (run_step m (rs,SOME q1) (SUC n1)) n2 =
       run_step m (rs,SOME q1) (SUC n1 + n2)` suffices_by rw[run_one_step]
  >> metis_tac[]
QED

Definition rmcorr_def:
  rmcorr m q P qf Q = 
    ∀rs. P rs ⇒ ∃n rs'. (run_step m (rs, SOME q) n = (rs', qf)) ∧ Q rs' 
End

Theorem rmcorr_trans:
  rmcorr m q1 P (SOME q2) Q ∧ rmcorr m q2 Q q3 R ⇒ rmcorr m q1 P q3 R
Proof 
  rw[rmcorr_def] >> 
  last_x_assum (qspec_then `rs` assume_tac) >> rfs[] >>
  last_x_assum (qspec_then `rs'` assume_tac) >> rfs[] >>
  qexists_tac`n+n'` >>
  qexists_tac`rs''` >>
  `run_step m (rs,SOME q1) (n + n') =  run_step m (run_step m (rs,SOME q1) n) n' ` 
    by simp[combo_steps] >>
  `run_step m (run_step m (rs,SOME q1) n) n' = run_step m (rs', SOME q2) n' ` 
    by simp[] >>
  rw[]
QED

(* 0 *)
Theorem const0rm[simp] = EVAL``const 0``;

Theorem const0_correct:
  correct (const 0) zerof 1
Proof 
  rw[correct_def] >>
  rw[RUN_def, run_machine_def, init_machine_def, findi_def] >>
  simp[] >>
  rw[Ntimes WHILE 2, run_machine_1_def] >>
  rw[APPLY_UPDATE_THM] 
QED

(* SUC *)
Theorem add1_correct:
  correct add1 succ 1
Proof
  rw[correct_def, add1_def] >>
  rw[RUN_def, run_machine_def, init_machine_def, findi_def] >>
  Cases_on `l` >> fs[] >>
  rw[Ntimes WHILE 2, run_machine_1_def] >>
  rw[APPLY_UPDATE_THM] 
QED

(* Projection *)
Theorem findi_snoc:
  findi i (SNOC k l) = 
            if MEM i l then findi i l 
            else if i = k then LENGTH l
            else LENGTH l + 1
Proof 
  Induct_on `l` >> simp[findi_def]
  >> rw[] 
  >> fs[]
QED

Theorem findi_genlist[simp]:
  findi i (GENLIST I j) = 
              if i < j then i 
                else j
Proof
  Induct_on `j` >> simp[findi_def, GENLIST, findi_snoc, MEM_GENLIST]
QED


Theorem pi_correct:
  correct (Pi i j) (proj i) j
Proof 
  rw[Pi_def, correct_def] >>
  rw[RUN_def, run_machine_def, init_machine_def, findi_def] >>
  rw[AllCaseEqs()] >>
  rw[Once WHILE, run_machine_1_def] 
  >> rw[Ntimes WHILE 2, run_machine_1_def, APPLY_UPDATE_THM]
  >> simp[proj_def]
QED

(* Cn *)
Definition id_def:
  id a = a
End

Theorem identity_correct:
  correct1 id identity 
Proof
  rw[correct1_def, id_def, identity_def] >>
  rw[RUN_def, run_machine_def, init_machine_def, findi_def] >>
  rw[Once WHILE, run_machine_1_def] >> 
  rw[Once WHILE, run_machine_1_def] 
  >> rw[Once WHILE, run_machine_1_def] >> rw[APPLY_UPDATE_THM] 
QED


(*
val Cn_def = Define `
  Cn m ms = 
    let isz = LENGTH (HD ms).In;
        mms = MAPi (λi mm. mrInst (i+2) mm) (m::ms);
        m'  = HD mms;
        ms' = TL mms;
        ics = FLAT (MAP (λmm. MAPi (λi r. dup (npair 0 i) r (npair 1 0)) mm.In) ms');
        ocs = MAPi (λi mm. dup mm.Out (EL i m'.In) (npair 1 0)) ms';
        mix = ics++ms'++ocs++[m'];
        mix' = MAPi msInst mix;
    in 
      link_all mix' with In := MAP (npair 0) (GENLIST I isz)
`;
*)

(*
Definition triple_def:
  triple P q m Q = 
    ∀rs. P rs ⇒ ∃n rs'. (run_step m (rs, SOME q) n = (rs', NONE)) ∧ Q rs rs' 
End
*)

(* 
TODO 18 Sep

[DONE]1. prove rmcorr_trans (hint: 1. prove lemma about run_step 2. combine assumption 0 and 2)
run_Step a .. ( run_step b ..)= run_step (a+b) ...

3. dup (induct on r1) 

5. WHILE assumes things finishes , define a predicate that means terminates (takes a machine, registers states, q0 and returns true if terminate else false)
*)

(*
Theorem dup_correct:
  triple (λrs0. rs0 z = 0) 0 (dup x y z) (λrs0 rs. rs = rs0 (| y |-> rs0 x |))
Proof
  rw[dup_def, triple_def] >>
  qabbrev_tac `X = rs0 x` >>
  qabbrev_tac `Y = rs0 y` >>
  qabbrev_tac `Z = rs0 z` >>
  qexists_tac `Y+5*X+3`   >>


  rw[Once WHILE, run_machine_1_def] >>
  Induct_on `r1` >> rw[] 
  >> rw[Ntimes WHILE 3, run_machine_1_def] 
  >> rw[APPLY_UPDATE_THM] 
  >> rw[ADD1]
  >> 
QED
*)


Theorem link_correct:
  ∀m1 m2 i. RUN (link m1 m2) i = run_machine m2 (rsf m1 i, SOME m2.q0)
Proof
  
QED


Theorem mrInst1_correct:
  ∀mnum. correct1 f m ⇒ correct1 f (mrInst mnum m)
Proof
  rw[mrInst_def, correct1_def] >>
  
QED


Theorem msInst1_correct:
  ∀mnum. correct1 f m ⇒ correct1 f (msInst mnum m)
Proof
 rw[msInst_def, correct1_def] >>
  
QED

Theorem mrInst2_correct:
∀mnum. correct2 f m ⇒ correct2 f (mrInst mnum m)
Proof

QED


Theorem msInst2_correct:
  ∀mnum. correct2 f m ⇒ correct2 f (msInst mnum m)
Proof

QED


Theorem Cn1_correct:
  correct1 f1 m1 ∧ correct1 f2 m2 ⇒ ∀n. RUN (Cn m1 [m2]) [n] = (f1 o f2) n  
Proof
  rw[correct1_def, init_machine_def, run_machine_def, RUN_def, rsf_def] >>
  rw[Cn_def] >>

QED

val _ = export_theory ()