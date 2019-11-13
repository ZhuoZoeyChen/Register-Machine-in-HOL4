open HolKernel Parse boolLib bossLib;
open arithmeticTheory;
open combinTheory;
open whileTheory;
open indexedListsTheory;
open numeralTheory;
open primrecfnsTheory;
open listTheory;
open mp_then;
open boolTheory;
open numpairTheory;
open pred_setTheory;

val _ = new_theory "registerMachine";


Type reg = “:num”;
Type state = “:num”;

Datatype:
  action = Inc num (state option) | Dec num (state option) (state option) 
End

(* regOf :: action -> reg num *)
Definition regOf_def[simp]:
  regOf (Inc r _) = r ∧ regOf (Dec r _ _) = r
End

(* inst_Val :: action -> value -> updated value *)
Definition inst_Val_def[simp]:
  inst_Val (Inc _ _) v = v + 1 /\
  inst_Val (Dec _ _ _) v = if v = 0 then 0 else v - 1
End

(* inst_Dest :: action -> value -> next state *)
Definition inst_Dest_def[simp]:
  inst_Dest (Inc _ s) v = s ∧
  inst_Dest (Dec _ s1 s2) v = if v = 0 then s2 else s1
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

Theorem run_machine_1_alt:
  (run_machine_1 m (rs, NONE) = (rs, NONE)) ∧
   (run_machine_1 m (rs, SOME s) = if s ∉ m.Q then (rs, NONE)
     else let i = m.tf s;
              r = regOf i
          in (rs(|r |-> inst_Val i (rs r)|), inst_Dest i (rs r)))
Proof 
  rw[run_machine_1_def] >> Cases_on`m.tf s` >> rw[] >> fs[] >>
  rw[APPLY_UPDATE_THM, FUN_EQ_THM] >> rw[] >> rw[]
QED

val run_machine_def = Define `
  (run_machine m = WHILE (λ(rs, so). so ≠ NONE) (run_machine_1 m)) 
`;

val rsf_def = Define ` 
  rsf m i = FST (run_machine m (init_machine m i))
`;

val RUN_def = Define `
  RUN m i = FST (run_machine m (init_machine m i)) m.Out
`;

Definition conv_def:
  (conv (SOME s) = s+1) ∧
  (conv NONE = 0)
End

Definition strip_state_def:
  strip_state action = case action of 
     | Inc _ so => [conv so]
     | Dec _ so1 so2 => conv so1::[conv so2]
End

Definition opt_to_set_def[simp]:
  opt_to_set (SOME q) = {q}   ∧
  opt_to_set NONE = {}
End

Definition action_states_def[simp]:
  action_states (Inc r qopt) = opt_to_set qopt ∧
  action_states (Dec r qopt1 qopt2) = opt_to_set qopt1 ∪ opt_to_set qopt2
End

(* Definition of wellformedness of a register machine :
      Has finite states initial state(q0) is in that machine's set of all states(Q),
      and a valid state only transits to a valid state or NONE.
*)
val wfrm_def = Define `
  wfrm m ⇔ 
    FINITE m.Q ∧
    m.q0 ∈ m.Q ∧
    (∀s. s ∈ m.Q ⇒ action_states (m.tf s) ⊆ m.Q) 
`;

val rm_component_equality = theorem "rm_component_equality"
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

Definition upd_def[simp]:
  (upd NONE d = SOME d) 
    ∧
  (upd (SOME d0) d = SOME d0)
End

Definition end_link_def[simp]:
  (end_link (Inc q d0) d = Inc q (upd d0 d))
    ∧
  (end_link (Dec q d1 d2) d = Dec q (upd d1 d) (upd d2 d))
End


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
   -----------------------------------------
   -----    Verification Techniques    -----
   -----------------------------------------
*)



fun generate_machine_rwts thm = 
  let val (mname,tm)= dest_eq (concl thm)
      val qthm = SIMP_CONV (srw_ss()) [thm] (mk_comb(“rm_Q”, mname))
      val states_t = rhs (concl qthm)
      val states = pred_setSyntax.strip_set states_t
      fun mktf k = SIMP_CONV (srw_ss()) [thm] (list_mk_comb(“rm_tf”, [mname,k]))
      val tf_thms = map mktf states
      val inthm = SIMP_CONV (srw_ss()) [thm] (mk_comb(“rm_In”, mname))
      val outthm = SIMP_CONV (srw_ss()) [thm] (mk_comb(“rm_Out”, mname))
      val q0thm = SIMP_CONV (srw_ss()) [thm] (mk_comb(“rm_q0”, mname))
  in LIST_CONJ (inthm :: outthm :: q0thm :: qthm :: tf_thms)
  end
  

(* Helper functions *)
Definition correct_def:
  correct m f a ⇔ ∀l. LENGTH l = a ⇒ RUN m l = f l
End

(*
Definition correct_def:
  correct m f a = rmcorr m m.q0 () NONE 
End
*)

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
  rmcorr M q P qf Q = 
    ∀rs. P rs ⇒ ∃n rs'. (run_step M (rs, SOME q) n = (rs', qf)) ∧ Q rs' 
End

Definition rm_ends_def:
  rm_ends m rs q = ∃n rs'. run_step m (rs, SOME q) n = (rs', NONE) 
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



Theorem rmcorr_inc:
  m.tf q0 = Inc r (SOME d)
∧
  q0 ∈ m.Q
∧
  rmcorr m d (λrs. P (rs (| r |-> rs r - 1 |)) ∧ 0 < rs r) q Q
==> 
  rmcorr m q0 P q Q
Proof 
  rw[rmcorr_def] >>
  qabbrev_tac `rs' = rs⦇r ↦ rs r + 1⦈` >> 
  `rs'⦇r ↦ rs' r - 1⦈ = rs` by rw[APPLY_UPDATE_THM, Abbr`rs'`, FUN_EQ_THM] >>
  `P rs'⦇r ↦ rs' r - 1⦈` by fs[] >>
  `0 < rs' r ` by rw[APPLY_UPDATE_THM, Abbr`rs'`] >>
  first_x_assum drule_all >>
  strip_tac >> 
  map_every qexists_tac [`SUC n`, `rs''`] >>
  rw[run_step_def, run_machine_1_def]
QED 


Theorem rmcorr_stay:
(∀rs. P rs ⇒ Q rs) ⇒ rmcorr m q P (SOME q) Q
Proof 
  rw[rmcorr_def] >>
  map_every qexists_tac [`0`, `rs`] >>
  first_x_assum drule >>
  strip_tac >>
  rw[run_step_def]
QED

Theorem rmcorr_dec:
  m.tf q0 = Dec r (SOME t) (SOME e)
∧ 
  q0 ∈ m.Q
∧
  rmcorr m t (λrs. P (rs (|r |-> rs r + 1|))) q Q
∧
  rmcorr m e (λrs. P rs ∧ rs r = 0) q Q
==>
  rmcorr m q0 P q Q
Proof 
  rw[rmcorr_def] >> 
  Cases_on `0 < rs r` 
  >- (qabbrev_tac`rs' = rs (| r |-> rs r - 1|)` >> 
      `P rs' ⦇r ↦ rs' r + 1⦈ ` 
          by simp[Abbr`rs'`, APPLY_UPDATE_THM, UPDATE_EQ, APPLY_UPDATE_ID]
       >> last_x_assum drule >> strip_tac >> map_every qexists_tac [`SUC n`, `rs''`]
       >> rw[run_step_def, run_machine_1_def])
  >> `rs r = 0` by simp[] 
  >> first_x_assum drule_all
  >> strip_tac >> map_every qexists_tac [`SUC n`, `rs'`]
  >> rw[run_step_def, run_machine_1_def]
QED


Theorem rmcorr_weakening:
  (∀s. P s ⇒ P' s) ∧ (∀s. Q' s ⇒ Q s) ∧ (rmcorr m q0 P' q Q') 
==> rmcorr m q0 P q Q 
Proof 
  rw[rmcorr_def] >>
  `P' rs` by fs[] >>
  `∃n rs'. run_step m (rs,SOME q0) n = (rs',q) ∧ Q' rs'` by fs[] >>
  `Q rs'` by fs[] >>
  qexists_tac `n` >> 
  qexists_tac `rs'` >>
  rw[]
QED


Theorem loop_correct_0:
∀ m q INV gd body exit.
  (∀N. rmcorr m body (λrs. INV (rs(| gd |-> rs gd + 1|)) ∧ rs gd = N) (SOME q) (λrs'. INV rs' ∧ rs' gd <= N))
∧ (m.tf(q) = Dec gd (SOME body) exit) ∧ q ∈ m.Q

==> rmcorr m q INV exit (λrs. INV rs ∧ rs gd = 0)
Proof   
  rw[rmcorr_def] >>
  completeInduct_on `rs gd` >>
  rw[] >>
  fs[PULL_FORALL] >>
  Cases_on`0<rs gd` 
  >- (qabbrev_tac `rsx = rs⦇gd ↦ rs gd - 1⦈` >> 
     `run_machine_1 m (rs, SOME q) = (rsx, SOME body)` by simp[run_machine_1_def] >>
      first_x_assum (qspec_then `rsx` mp_tac) >>
      impl_tac 
      >- rw[Abbr `rsx`, APPLY_UPDATE_THM, APPLY_UPDATE_ID, UPDATE_EQ] 
      >> strip_tac >>
      `rs' gd < rs gd` by fs[Abbr`rsx`, APPLY_UPDATE_THM] >>
      first_x_assum drule_all >> rw[] >>
      map_every qexists_tac [`SUC (n + n')`, `rs''`] >>
      simp[run_step_def, GSYM combo_steps]
    )
  >> map_every qexists_tac [`SUC 0`, `rs`]
  >> rw[run_step_def]
  >> rw[run_machine_1_def]
QED


Theorem loop_correct:
∀ m q INV P Q gd body exit.
  (∀N. rmcorr m body (λrs. INV (rs(| gd |-> rs gd + 1|)) ∧ rs gd = N) (SOME q) (λrs'. INV rs' ∧ rs' gd <= N))
∧ (∀rs. P rs ⇒ INV rs) 
∧ (∀rs. INV rs ∧ rs gd = 0 ⇒ Q rs)
∧ (m.tf(q) = Dec gd (SOME body) exit)
∧ q ∈ m.Q

==> rmcorr m q P exit Q
Proof   
  rw[] >>
  `rmcorr m q INV exit (λrs. INV rs ∧ rs gd = 0)` by rw[loop_correct_0] >>
  fs[rmcorr_def] >>
  rw[rmcorr_def] >>
  `INV rs` by fs[] >>
  `∃n rs'. run_step m (rs,SOME q) n = (rs',exit) ∧ INV rs' ∧ rs' gd = 0` by fs[] >>
  qexists_tac`n` >>
  qexists_tac`rs'` >>
  `Q rs'` by fs[] >>
  rw[]
QED



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


(* Substract 2 from 1 (stops at 0)*)
Definition simp_sub_def:
  simp_sub = <|
    Q := {1;2};
    tf := (λs. case s of 
            | 1 => Dec 2 (SOME 2) NONE 
            | 2 => Dec 1 (SOME 1) (SOME 1)
          );
    q0 := 1;
    In := [1;2];
    Out := 1;
  |>
End


Theorem simp_add_facts[simp] = generate_machine_rwts simp_add_def

Theorem simp_add_correct_rmcorr:
∀RS. 
  rmcorr simp_add 1 (λrs. rs = RS) NONE (λrs. ∀k. k ∉ {1;2} ⇒ rs k = RS k ∧ rs 2 = 0 ∧ rs 1 = RS 1 + RS 2)
Proof 
  rw[] >>
  irule loop_correct >> simp[] >>
  qexists_tac `λrs.  ∀k. k ∉ {1;2} ⇒ rs k = RS k ∧ rs 2 + rs 1 = RS 1 + RS 2` >>
  rw[] 
  >- (first_x_assum drule_all >> rw[])
  >> rw[APPLY_UPDATE_THM]
  >> irule rmcorr_inc >> simp[]
  >> rw[APPLY_UPDATE_THM]
  >> irule rmcorr_stay >> simp[]
  >> rw[]
  >> first_x_assum drule_all
  >> rw[]
QED 

Theorem simp_add_correct:
  correct2 (+) simp_add
Proof
  rw[simp_add_def, correct2_def, init_machine_def, run_machine_def, RUN_def] >>
  qmatch_abbrev_tac `FST (WHILE gd (r m) init) 1 = a + b` >>
  `∀rs0. FST (WHILE gd (r m) (rs0, SOME 1)) 1 = rs0 1 + rs0 2`
    suffices_by rw[Abbr`init`, findi_def] >>
  gen_tac >> 
  rw[Abbr`r`, Abbr`m`, Abbr`gd`] >> 
  Induct_on `rs0 2` >>
  rw[Ntimes WHILE 2, run_machine_1_def, APPLY_UPDATE_THM] 
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

Theorem addition_facts[simp] = generate_machine_rwts addition_def

Theorem addition_correct_rmcorr:
∀RS. RS 3 = 0 ⇒ 
  rmcorr addition 1 (λrs. rs = RS) NONE (λrs. rs 1 = RS 1 + RS 2 ∧ ∀k. k ≠ 1 ⇒ rs k = RS k)
Proof 
  rw[] >>
  irule rmcorr_trans >> simp[] >> 
  map_every qexists_tac [`λrs. ∀k. k ∉ {1;2;3} ⇒ rs k = RS k ∧ rs 1 = RS 1 + RS 2 ∧ rs 3 = RS 2 ∧ rs 2 = 0`,`4`] >> 
  rw[]
  >- (irule loop_correct >> simp[] >> 
      qexists_tac `λrs. ∀k. k ∉ {1;2;3} ⇒ rs k = RS k ∧ rs 1 + rs 2 = RS 1 + RS 2 ∧ rs 3 + rs 2 = RS 2` >>
      rw[] 
      >- (first_x_assum drule_all >> rw[])
      >- (first_x_assum drule_all >> rw[])
      >> irule rmcorr_inc >> simp[] 
      >> rw[APPLY_UPDATE_THM]
      >> irule rmcorr_inc >> simp[]
      >> rw[APPLY_UPDATE_THM]
      >> irule rmcorr_stay >> simp[]
      >> rw[APPLY_UPDATE_THM]
      >> first_x_assum drule_all >> rw[]
    )
  >> irule loop_correct >> simp[]
  >> qexists_tac `λrs. rs 1 = RS 1 + RS 2 ∧ rs 3 + rs 2 = RS 2 ∧ ∀k. k ∉ {1;2;3} ⇒ rs k = RS k` 
  >> rw[APPLY_UPDATE_THM]
  >- (fs[] >> Cases_on `k = 2`
      >- rw[]
      >> Cases_on `k = 3`
      >> rw[])
  >> irule rmcorr_inc >> simp[]
  >> irule rmcorr_stay >> simp[]
  >> rw[APPLY_UPDATE_THM]
QED


Theorem addition_correct:
  correct2 (+) addition 
Proof
  rw[addition_def, correct2_def, init_machine_def, run_machine_def, RUN_def] >>
  qmatch_abbrev_tac `FST (WHILE gd (r m) init) 1 = a + b` >>
  `∀rs0. FST (WHILE gd (r m) (rs0, SOME 1)) 1 = rs0 1 + rs0 2`
    suffices_by rw[Abbr`init`, findi_def] >>
  gen_tac >>
  Induct_on `rs0 2` 
    >- (`∀rs0. FST (WHILE gd (r m) (rs0, SOME 4)) 1 = rs0 1` 
          suffices_by (rw[] >> rw[Once WHILE, Abbr`r`, Abbr`m`, run_machine_1_def]) 
        >> gen_tac
        >> Induct_on `rs0 3`
        >> rw[Abbr`gd`, Abbr`r`, Abbr`m`]
        >> rw[Ntimes WHILE 2, run_machine_1_def, APPLY_UPDATE_THM])
    >> rw[Abbr`r`, Abbr`m`, Abbr`gd`] 
    >> rw[Ntimes WHILE 3, run_machine_1_def, APPLY_UPDATE_THM] 
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


Theorem multi_facts[simp] = generate_machine_rwts multiplication_def


Theorem multiplication_correct_rmcorr:
∀RS. (RS 2 = 0 ∧ RS 3 = 0) ⇒ 
  rmcorr multiplication 1 (λrs. rs = RS) NONE (λrs. rs 2 = RS 0 * RS 1 ∧ rs 0 = 0 ∧ ∀k. k ∉ {0;2} ⇒ rs k = RS k)
Proof 
  rw[] >> 
  irule loop_correct >> simp[] >>
  qexists_tac `λrs. rs 0 * rs 1 + rs 2 = RS 0 * RS 1 ∧ ∀k. k ∉ {0;2} ⇒ rs k = RS k` >>
  rw[]
  >- fs[]
  >> irule rmcorr_trans >> simp[APPLY_UPDATE_THM]
  >> map_every qexists_tac [`λrs. rs 0 = N ∧ rs 0 * rs 3 + rs 2 = RS 0 * RS 1 ∧ rs 1 = 0 ∧ rs 3 = RS 1 ∧ ∀k. k ∉ {0;1;2;3} ⇒ rs k = RS k`,`5`]
  >> rw[]
  >- (irule loop_correct >> simp[] >> 
      qexists_tac `λrs. rs 0 = N ∧ rs 1 + rs 3 = RS 1 ∧ rs 0 * RS 1 + rs 2 + rs 1 = RS 0 * RS 1 ∧ ∀k. k ∉ {0;1;2;3} ⇒ rs k = RS k `
      >> rw[] >> fs[]
      >> irule rmcorr_inc >> simp[] 
      >> irule rmcorr_inc >> simp[] 
      >> irule rmcorr_stay >> simp[]
      >> rw[APPLY_UPDATE_THM]
      >> fs[])
  >> irule rmcorr_trans >> simp[]
  >> map_every qexists_tac [`λrs. rs 0 = N ∧ rs 0 * RS 1 + rs 2 = RS 0 * RS 1 ∧ ∀k. k ∉ {0;2} ⇒ rs k = RS k`, `1`] 
  >> rw[]
  >- (irule loop_correct >> simp[]
      >> qexists_tac `λrs. rs 0 = N ∧ rs 1 + rs 3 = RS 1 ∧ rs 0 * RS 1 + rs 2 = RS 0 * RS 1 ∧ ∀k. k ∉ {0;1;2;3} ⇒ rs k = RS k`
      >> rw[]
      >- fs[]
      >- (Cases_on `k = 1` 
          >> fs[]
          >> Cases_on `k = 3`
          >> fs[])
      >> irule rmcorr_inc >> simp[]
      >> irule rmcorr_stay >> simp[]
      >> rw[APPLY_UPDATE_THM]
      )
  >> irule rmcorr_stay >> simp[]
  >> rw[APPLY_UPDATE_THM] 
  >> fs[]
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
    >- (rw[Once WHILE, run_machine_1_def, multiplication_def] >>
          `rs 1 = 0` by simp[] >> fs[] >> rw[APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >> 
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, APPLY_UPDATE_THM] >>
          rw[] >> rw[])
    >> qmatch_abbrev_tac`_ = goal` >>
      rw[Ntimes WHILE 3, run_machine_1_def, multiplication_def] >>
      rw[APPLY_UPDATE_THM] >>
      `rs 1 = SUC v` by simp[] >> fs[] >> 
      fs[multiplication_def, APPLY_UPDATE_THM] >> 
      rw[Abbr`goal`] >> qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
      `rs1 = rs2` suffices_by simp[] >>
      simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, APPLY_UPDATE_THM]
QED

Theorem mult_loop2:
  WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 multiplication) (rs, SOME 5) 
  = WHILE (λ(rs,so). so ≠ NONE) (run_machine_1 multiplication) 
    (rs (| 1 |-> rs 1 + rs 3; 
           3 |-> 0 |) 
     , SOME 1) 
Proof
  Induct_on `rs 3` >> rw[] 
    >- (rw[Once WHILE, run_machine_1_def, multiplication_def] >>
          `rs 3 = 0` by simp[] >> fs[] >> rw[APPLY_UPDATE_THM] >>
          qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
          `rs1 = rs2` suffices_by simp[] >> 
          simp[Abbr `rs1`, Abbr`rs2`, FUN_EQ_THM, APPLY_UPDATE_THM] >>
          rw[] >> rw[])
    >> rw[SimpLHS, Ntimes WHILE 2, run_machine_1_def, multiplication_def] >>
      rw[APPLY_UPDATE_THM] >>
      `rs 3 = SUC v` by simp[] >> fs[] >> 
      fs[multiplication_def, APPLY_UPDATE_THM] >> 
      qmatch_abbrev_tac`WHILE _ _ (rs1, _) = WHILE _ _ (rs2, _)` >>
      `rs1 = rs2` suffices_by simp[] >>
      simp[Abbr `rs1`, Abbr`rs2`] >>
      simp[FUN_EQ_THM, APPLY_UPDATE_THM]
QED

        

Theorem multi_correct:
  correct2 $* multiplication
Proof  
  rw[correct2_def, init_machine_def, run_machine_def, RUN_def] >>
  qmatch_abbrev_tac `FST (WHILE gd (r m) init) 2 = a * b` >>
  `∀rs0. (rs0 3 = 0) ⇒ (FST (WHILE gd (r m) (rs0, SOME 1)) 2 = rs0 0 * rs0 1 + rs0 2)` 
    suffices_by rw[Abbr`init`, findi_def] >> rw[] >>
  Induct_on `rs0 0` >> rw[]
    >- (rw[multiplication_def, Ntimes WHILE 2, Abbr`gd`, Abbr`r`, Abbr`m`, run_machine_1_def] >>
        `rs0 0 = 0` by simp[] >> fs[])
    >> rw[Once WHILE, run_machine_1_def, Abbr`gd`, Abbr`r`, Abbr`m`, mult_loop1]
    >> rw[mult_loop2]
    >> rw[APPLY_UPDATE_THM] >> `rs0 0 = SUC v` by simp[] >> fs[]
    >> fs[arithmeticTheory.ADD1]
QED


(* swapping r1 and r2 for multiplication part can make the machine faster *)
(* r1 ** r0 *)
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

Theorem exp_facts[simp] = generate_machine_rwts exponential_def


Theorem exponential_correct_rmcorr:
∀RS. (RS 2 = 0 ∧ RS 3 = 0 ∧ RS 4 = 0 ∧ RS 5 = 0) ⇒ 
  rmcorr exponential 14 (λrs. rs = RS) NONE 
      (λrs. rs 2 = RS 1 ** RS 0 ∧ rs 0 = 0 ∧ ∀k. k ∉ {0;2} ⇒ rs k = RS k)
Proof 
  rw[] >>
  irule rmcorr_inc >> simp[] >>
  irule loop_correct >> simp[] >>
  qexists_tac `λrs. rs 2 * (rs 1 ** rs 0) = RS 1 ** RS 0 ∧ ∀k. k ∉ {0;2} ⇒ rs k = RS k` >>
  rw[APPLY_UPDATE_THM]
  >- (`rs 2 = 1` by fs[UPDATE_APPLY] >> rw[APPLY_UPDATE_THM])
  >- rw[APPLY_UPDATE_THM]
  >- fs[]
  >> irule rmcorr_trans >> simp[]
  >> map_every qexists_tac
   [`λrs. rs 0 = N ∧ rs 1 = 0 ∧ rs 5 = RS 1 ∧ rs 2 * (rs 5 ** (rs 0 + 1)) = RS 1 ** RS 0 ∧ 
        rs 3 = rs 2 * rs 5 ∧ ∀k. k ∉ {0;1;2;3;5} ⇒ rs k = RS k`,`9`]
  >> rw[]
  >- (irule loop_correct >> simp[] 
      >> qexists_tac `λrs. rs 1 + rs 5 = RS 1 ∧ rs 0 = N ∧ rs 2 * (RS 1 ** (rs 0 + 1)) = RS 1 ** RS 0 
         ∧ rs 4 = 0 ∧ rs 3 + rs 1 * rs 2 = RS 1 * rs 2 ∧ ∀k. k ∉ {0;1;2;3;5} ⇒ rs k = RS k` 
      >> rw[APPLY_UPDATE_THM] >> fs[]
      >> irule rmcorr_inc >> simp[]
      >> rw[APPLY_UPDATE_THM]
      >> irule rmcorr_trans >> simp[]
      >> map_every qexists_tac [`λrs. rs 1 = N' ∧ rs 0 = N ∧ 
         rs 1 + rs 5 = RS 1 ∧ rs 4 * (RS 1 ** (rs 0 + 1)) = RS 1 ** RS 0 
         ∧ rs 2 = 0 ∧ rs 3 + rs 1 * rs 4 = RS 1 * rs 4 ∧ ∀k. k ∉ {0;1;2;3;4;5} ⇒ rs k = RS k`,`7`]
      >> rw[APPLY_UPDATE_THM] >> fs[]
      >- (irule loop_correct >> simp[]
          >> qexists_tac `λrs. rs 1 = N' ∧ rs 0 = N ∧ 
         rs 1 + rs 5 = RS 1 ∧ (rs 2 + rs 4) * (RS 1 ** (rs 0 + 1)) = RS 1 ** RS 0 
         ∧ (rs 2 + rs 3) + rs 1 * (rs 2 + rs 4) = RS 1 * (rs 2 + rs 4) ∧ ∀k. k ∉ {0;1;2;3;4;5} ⇒ rs k = RS k`
          >> rw[APPLY_UPDATE_THM] >> fs[]
          >> irule rmcorr_inc >> simp[]
          >> irule rmcorr_inc >> simp[]
          >> rw[APPLY_UPDATE_THM]
          >> irule rmcorr_stay >> simp[]
          >> rw[APPLY_UPDATE_THM] >> fs[])
      >> irule loop_correct >> simp[]
      >> qexists_tac `λrs. rs 1 = N' ∧ rs 0 = N ∧ 
         rs 1 + rs 5 = RS 1 ∧ (rs 2 + rs 4) * (RS 1 ** (rs 0 + 1)) = RS 1 ** RS 0 
         ∧ rs 3 + rs 1 * (rs 2 + rs 4) = RS 1 * (rs 2 + rs 4) ∧ ∀k. k ∉ {0;1;2;3;4;5} ⇒ rs k = RS k`
      >> rw[APPLY_UPDATE_THM] >> fs[]
      >- (Cases_on `k=4` >> fs[])
      >> irule rmcorr_inc >> simp[]
      >> irule rmcorr_stay >> simp[]
      >> rw[APPLY_UPDATE_THM] >> fs[]
      )
  >> irule rmcorr_trans >> simp[]
  >> map_every qexists_tac [`λrs. rs 0 = N ∧ rs 2 * (RS 1 ** (rs 0 + 1)) = RS 1 ** RS 0 ∧ 
        rs 3 = rs 2 * RS 1 ∧ ∀k. k ∉ {0;2;3} ⇒ rs k = RS k`,`11`]
  >> rw[]
  >- (irule loop_correct >> simp[]
      >> qexists_tac `λrs. rs 0 = N ∧ (rs 5 + rs 1) = RS 1 ∧ rs 2 * ((rs 5 + rs 1) ** (rs 0 + 1)) = RS 1 ** RS 0 ∧ 
        rs 3 = rs 2 * (rs 5 + rs 1) ∧ ∀k. k ∉ {0;1;2;3;5} ⇒ rs k = RS k`
      >> rw[APPLY_UPDATE_THM] >> fs[]
      >- metis_tac[]
      >- metis_tac[] 
      >- (Cases_on `k=1` >> fs[] >> Cases_on `k=5` >> fs[])
      >> irule rmcorr_inc >> simp[]
      >> irule rmcorr_stay >> simp[]
      >> rw[APPLY_UPDATE_THM] >> fs[]
      >> metis_tac[])
  >> irule rmcorr_trans >> simp[]
  >> map_every qexists_tac [`λrs. rs 0 = N ∧ rs 3 * (RS 1 ** rs 0) = RS 1 ** RS 0 ∧ 
        ∀k. k ∉ {0;3} ⇒ rs k = RS k`,`12`]
  >> rw[]
  >- (irule loop_correct >> simp[] 
      >> qexists_tac `λrs. rs 0 = N ∧ rs 3 * (RS 1 ** rs 0) = RS 1 ** RS 0 ∧ 
        ∀k. k ∉ {0;2;3} ⇒ rs k = RS k`
      >> rw[APPLY_UPDATE_THM] >> fs[]
      >- (`rs 0 + 1 = SUC (rs 0)` by fs[] 
          >> `rs 2 * (RS 1 ** (rs 0 + 1) )= rs 2 * (RS 1 ** (SUC (rs 0)))` by metis_tac[] 
          >> `rs 2 * RS 1 ** SUC (rs 0) = rs 2 * RS 1 * RS 1 ** rs 0` by fs[EXP] 
          >> `RS 1 * rs 2 * RS 1 ** rs 0 = rs 2 * RS 1 * RS 1 ** rs 0` by rw[MULT_COMM] 
          >> metis_tac[])
      >- (Cases_on `k=2` >> fs[])
      >> irule rmcorr_stay >> simp[]
      )
  >> irule loop_correct >> simp[]
  >> qexists_tac `λrs. rs 0 = N ∧ (rs 3 + rs 2) * (RS 1 ** rs 0) = RS 1 ** RS 0 ∧ 
        ∀k. k ∉ {0;2;3} ⇒ rs k = RS k`
  >> rw[APPLY_UPDATE_THM] >> fs[]
  >- (Cases_on`k = 3` >> fs[])
  >> irule rmcorr_inc >> simp[]
  >> irule rmcorr_stay >> simp[]
  >> rw[APPLY_UPDATE_THM]
  >> fs[]
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


(* Cn f g = f o g *)


Definition Cn_def:
  Cn f g = 
      let f' = mrInst 1 f;
          g' = mrInst 2 g;
          d1 = dup g'.Out (HD f'.In) (npair 0 1);
          mix = [g'; d1; f'];
          mix' = MAPi msInst mix;
      in 
        link_all mix' with In := g'.In
End

(* Old Cn Definition *)
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
          pts0  = dup (npair 0 0) (HD step'.In) (npair 1 0);
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


Theorem dup_facts[simp]:
  (dup r1 r2 r3).tf 0 = Dec r2 (SOME 0) (SOME 1) ∧
  (dup r1 r2 r3).tf 1 = Dec r1 (SOME 2) (SOME 4) ∧
  (dup r1 r2 r3).tf 2 = Inc r2 (SOME 3) ∧
  (dup r1 r2 r3).tf 3 = Inc r3 (SOME 1) ∧
  (dup r1 r2 r3).tf 4 = Dec r3 (SOME 5) NONE ∧
  (dup r1 r2 r3).tf 5 = Inc r1 (SOME 4) ∧
  (dup r1 r2 r3).Q = {0;1;2;3;4;5} ∧
  (dup r1 r2 r3).q0 = 0 ∧
  (dup r1 r2 r3).In = [r1] ∧
  (dup r1 r2 r3).Out = r2 
Proof
  rw[dup_def]
QED


Theorem dup_correct:
  ∀r1 r2 r3 RS. 
  r1 ≠ r2 ∧ r1 ≠ r3 ∧ r2 ≠ r3 ∧ RS r3 = 0
  ∧ P = (λrs. rs = RS) ∧ Q = (λrs'. rs' = RS (| r2 |-> RS r1 |) ) 
==>
  rmcorr (dup r1 r2 r3) 0 P NONE Q
Proof 
  rw[] >>
  irule rmcorr_trans >>
(* loop1 : clear r2 *)
  map_every qexists_tac [`λrs'. rs'= RS (| r2 |-> 0 |)`, `1`] >> rw[] 
  >- (irule loop_correct >> simp[] >> qexists_tac`(λrs. ∀k. k ≠ r2 ⇒ rs k = RS k)` 
      >> rw[] 
      >- (rw[APPLY_UPDATE_THM, FUN_EQ_THM] >> rw[] >> rw[]) 
      >> rw[rmcorr_def] >> map_every qexists_tac [`0`, `rs`] 
      >> rw[] 
      >- rw[run_step_def]
      >> first_x_assum drule
      >> rw[APPLY_UPDATE_THM]
      )
  >> irule rmcorr_trans >>
(* loop2: transfer r1 into r2 and r3 *)
  map_every qexists_tac [`λrs'. rs'= RS (| r1 |-> 0 ; r2 |-> RS r1 ; r3 |-> RS r1|)`, `4`] >> rw[]
  >- (irule loop_correct >> simp[] 
      >> qexists_tac`(λrs. rs r1 + rs r2 = RS r1 ∧ rs r2 = rs r3 ∧ ∀k. k ∉ {r1; r2; r3} ⇒ rs k = RS k)` 
      >> rw[]
      >> rw[APPLY_UPDATE_THM]
      >- (`rs r2 = RS r1` by simp[] >> rw[APPLY_UPDATE_THM, FUN_EQ_THM]
          >> rw[] >> rw[])
      >> rw[rmcorr_def]
      >> map_every qexists_tac [`SUC (SUC 0)`,`rs (| r2 |-> rs r2 + 1 ; r3 |-> rs r3 + 1 |)`]
      >> rw[run_step_def, run_machine_1_def, FUN_EQ_THM, APPLY_UPDATE_THM]
      )
(* loop3: transfer r3 back into r1 *)
  >> irule loop_correct >> simp[] >> 
  qexists_tac`(λrs. rs r1 + rs r3 = RS r1 ∧ rs r2 = RS r1 ∧ ∀k. k ∉ {r1; r2; r3} ⇒ rs k = RS k)` >> 
  rw[APPLY_UPDATE_THM] >>
  fs[] >>
  rw[FUN_EQ_THM, APPLY_UPDATE_THM] 
  >- (Cases_on `x = r1` 
      >- fs[]
      >> Cases_on `x = r2`
      >- fs[]
      >> Cases_on `x = r3`
      >- fs[] 
      >> rw[APPLY_UPDATE_ID, FUN_EQ_THM])
  >> rw[rmcorr_def] 
  >> map_every qexists_tac [`SUC 0`,`rs (| r1 |-> rs r1 + 1|)`]
  >> rw[run_step_def, run_machine_1_def, APPLY_UPDATE_THM, FUN_EQ_THM]
QED



Theorem dup_correct_2:
  ∀r1 r2 r3 RS. 
  r1 ≠ r2 ∧ r1 ≠ r3 ∧ r2 ≠ r3 ∧ P = (λrs. rs r3 = 0 ∧ rs r1 = N) ∧ Q = (λrs. rs r3 = 0 ∧ rs r1 = N ∧ rs r2 = N) 
==>
  rmcorr (dup r1 r2 r3) 0 P NONE Q
Proof 
  rw[] >>
  irule rmcorr_trans >>
(* loop1 : clear r2 *)
  map_every qexists_tac [`λrs. rs r2 = 0 ∧ rs r3 = 0 ∧ rs r1 = N`, `1`] >> rw[] 
  >- (irule loop_correct >> simp[] >> qexists_tac`(λrs. rs r3 = 0 ∧ rs r1 = N)` 
      >> rw[APPLY_UPDATE_THM]
      >> irule rmcorr_stay >> rw[]
      )
  >> irule rmcorr_trans >>
(* loop2: transfer r1 into r2 and r3 *)
  map_every qexists_tac [`λrs. rs r1 = 0 ∧ rs r2 = N ∧ rs r3 = N`, `4`] >> rw[]
  >- (irule loop_correct >> simp[] 
      >> qexists_tac`(λrs. rs r1 + rs r2 = N ∧ rs r2 = rs r3)` 
      >> rw[]
      >> rw[APPLY_UPDATE_THM]
      >> irule rmcorr_inc >> rw[]
      >> irule rmcorr_inc >> rw[]
      >> rw[APPLY_UPDATE_THM]
      >> irule rmcorr_stay >> rw[]
      )
(* loop3: transfer r3 back into r1 *)
  >> irule loop_correct >> simp[] >> 
  qexists_tac`λrs. rs r1 + rs r3 = N ∧ rs r2 = N` >> 
  rw[APPLY_UPDATE_THM] >>
  fs[] >>
  irule rmcorr_inc >> rw[] >>
  rw[APPLY_UPDATE_THM] >>
  irule rmcorr_stay >> rw[]
QED

Theorem link_Q[simp]:
  (link m1 m2).Q = m1.Q ∪ m2.Q
Proof 
  rw[link_def]
QED 

Theorem link_tf:
  (link m1 m2).tf s = if s ∈ m1.Q then end_link (m1.tf s) m2.q0 else m2.tf s
Proof 
  rw[link_def, linktf_def]
QED 

Theorem run_machine_1_NONE[simp]:
  run_machine_1 m (rs, NONE) = (rs, NONE)
Proof 
  rw[run_machine_1_def]
QED 

Theorem run_step_NONE[simp]:
  run_step m (rs, NONE) n = (rs, NONE)
Proof 
  Induct_on `n` >> 
  rw[run_step_def] 
QED

Theorem regOf_end_link[simp]:
  regOf (end_link ins s) = regOf ins
Proof 
  Cases_on`ins` >> simp[end_link_def]
QED


Theorem  inst_Val_end_link[simp]:
  inst_Val (end_link ins s) v = inst_Val ins v
Proof 
  Cases_on`ins` >> simp[end_link_def]
QED

Theorem inst_Dest_end_link[simp]:
  inst_Dest (end_link ins d) v = 
    case inst_Dest ins v of 
        SOME d' => SOME d'
      | NONE => SOME d
Proof 
  Cases_on`ins` >> rw[end_link_def] >> rename [`upd opt d`] >> 
  Cases_on`opt` >> simp[upd_def]
QED 

Theorem inst_Dest_wf:
  wfrm m ∧ q ∈ m.Q ∧ inst_Dest (m.tf q) v = SOME q' ⇒ q' ∈ m.Q
Proof 
  Cases_on`m.tf q` >> rw[wfrm_def] >> first_x_assum drule 
  >> simp[action_states_def, opt_to_set_def]
QED



Theorem link_run_step_m1ToSOME:
  ∀q m m' rs rs'. 
  wfrm m ∧ wfrm m' ∧ DISJOINT m.Q m'.Q ∧ q ∈ m.Q ⇒
  (run_step m (rs, SOME q) n = (rs', SOME p) ⇒ run_step (link m m') (rs, SOME q) n = (rs', SOME p))
Proof 
  Induct_on `n` 
  (* 0 step *)
  >> rw[run_step_def] 
  (* k, suc k *)
  (* SOME to SOME *)
  >> fs[run_machine_1_alt] >> rw[link_tf] >> rfs[] >> 
  Cases_on `inst_Dest (m.tf q) (rs (regOf (m.tf q)))` >> fs[]
  >> first_x_assum irule >> simp[] 
  >> metis_tac[inst_Dest_wf]
QED


Theorem link_run_step_m1_ToNONE:
 ∀q m m' rs rs'. 
  wfrm m ∧ wfrm m' ∧ DISJOINT m.Q m'.Q ∧ q ∈ m.Q ⇒
  (run_step m (rs, SOME q) n = (rs', NONE) ⇒ ∃n'. n' ≤ n ∧ run_step (link m m') (rs, SOME q) n' = (rs', SOME m'.q0))
Proof 
  Induct_on `n` 
  (* 0 step *)
  >> rw[run_step_def] 
  (* SOME to NONE*)
  >> fs[run_machine_1_alt] >> rw[link_tf] >> rfs[]
  >> Cases_on `inst_Dest (m.tf q) (rs (regOf (m.tf q)))` >> fs[] 
  (* To NONE *)
  >- (qexists_tac`SUC 0` >> rw[run_step_def] >> rw[run_machine_1_alt] >>
      rw[APPLY_UPDATE_THM, FUN_EQ_THM] >> rw[link_tf])
  (* To SOME *)
  >> `∃n'. n' ≤ n ∧ run_step (m ⇨ m') (rs,SOME q) (SUC n') = (rs',SOME m'.q0)`
         suffices_by (rw[] >> qexists_tac`SUC n'` >> rw[])
  >> rw[run_step_def] 
  >> rw[run_machine_1_alt, link_tf]
  >> rename [`SOME q`, `q' ∈ m.Q`]
  >> qabbrev_tac `rs0 = rs⦇regOf (m.tf q') ↦ inst_Val (m.tf q') (rs (regOf (m.tf q')))⦈`
  >> first_x_assum irule >> simp[] 
  >> metis_tac[inst_Dest_wf]
QED 



Theorem link_run_step_m2:
  ∀q m m' rs rs'. 
  wfrm m ∧ wfrm m' ∧ DISJOINT m.Q m'.Q ∧ q ∈ m'.Q ⇒
  (run_step m' (rs, SOME q) n = (rs', opt) ⇒ run_step (link m m') (rs, SOME q) n = (rs', opt))
Proof 
  Induct_on `n` 
  (* 0 step *)
  >> rw[run_step_def] 
  (* k, suc k *)
  >> fs[run_machine_1_alt] >> rw[link_tf] >> fs[] 
  (* q in m.Q and q in m'.Q *)
  >- (fs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[])
  (* q not in m.Q and q in m'.Q *)
  >> rfs[]
  >> qabbrev_tac `rs0 = rs⦇regOf (m'.tf q) ↦ inst_Val (m'.tf q) (rs (regOf (m'.tf q)))⦈`
  >> Cases_on `inst_Dest (m'.tf q) (rs (regOf (m'.tf q)))` >> fs[]   (* q0 = NONE *)
  (* q0 = SOME _ *)
  >> first_x_assum irule >> simp[]
  >> metis_tac[inst_Dest_wf]
QED


Theorem link_m1end:
  q0 ∈ m.Q ∧ wfrm m' ∧ wfrm m ∧ DISJOINT m.Q m'.Q ∧ rmcorr m q0 P NONE Q ⇒ rmcorr (link m m') q0 P (SOME m'.q0) Q
Proof 
  rw[rmcorr_def] >> metis_tac[link_run_step_m1_ToNONE]
QED 

Theorem link_m2end:
  q0 ∈ m'.Q ∧ wfrm m' ∧ wfrm m ∧ DISJOINT m.Q m'.Q ∧ rmcorr m' q0 P opt Q ⇒ rmcorr (link m m') q0 P opt Q
Proof 
  rw[rmcorr_def] >> metis_tac[link_run_step_m2]
QED 




Theorem link_correct:
  wfrm m1 ∧ wfrm m2 ∧ DISJOINT m1.Q m2.Q ∧ rmcorr m1 m1.q0 P NONE Q ∧ rmcorr m2 m2.q0 Q opt R ∧ q = m1.q0
⇒ rmcorr (link m1 m2) q P opt R
Proof
  rw[] >>
  irule rmcorr_trans >>
  map_every qexists_tac [`Q`,`m2.q0`] >>
  rw[] 
  >- metis_tac[link_m1end, wfrm_def]
  >> metis_tac[link_m2end, wfrm_def]
QED




Theorem mrInst_prop[simp]:
 (s ∈ M.Q ⇒ (mrInst n M).tf s = (rInst n (M.tf s))) ∧
   (mrInst n M).Q = M.Q
Proof 
  rw[mrInst_def]
QED

Definition rs_mrInst_B4_def:
  rs_mrInst_B4 rsm rs mnum = (∀q. (rsm (mnum *, q) = rs q))
End 

Definition rs_mrInst_Aft_def:
  rs_mrInst_Aft rsm' rsm rs' mnum = 
  ((∀q. rsm' (mnum*, q)= rs' q) ∧ (∀r. nfst r ≠ mnum ⇒ (rsm' r = rsm r)))
End 


Theorem inst_Dest_rInst[simp]:
  inst_Dest (rInst mnum opt) v = inst_Dest opt v
Proof 
  Cases_on `opt` 
  >> metis_tac[inst_Dest_def, rInst_def]
QED 

Theorem regOf_rInst[simp]:
  regOf (rInst mnum opt) = npair mnum (regOf opt)
Proof 
  Cases_on `opt` >> 
  rw[regOf_def, rInst_def]
QED 

Theorem inst_Val_rInst[simp]:
  inst_Val (rInst mnum opt) v = inst_Val opt v
Proof 
  Cases_on `opt` >> metis_tac[inst_Val_def, rInst_def]
QED 

Theorem mrInst_run_step:
  ∀q n rs rs' M mnum rsm rsm'. 
  wfrm M ∧ q ∈ M.Q ∧ rs_mrInst_B4 rsm rs mnum ∧ rs_mrInst_Aft rsm' rsm rs' mnum ⇒
  (run_step M (rs, SOME q) n = (rs', opt) ⇒ 
  run_step (mrInst mnum M) (rsm, SOME q) n = (rsm', opt))
Proof 
  Induct_on`n` >>
  (* 0 Case *)
  rw[run_step_def] >>
  (* Inductive Case *)
  fs[run_machine_1_alt, rs_mrInst_B4_def, rs_mrInst_Aft_def] 
  >- (rw[FUN_EQ_THM] >> metis_tac[numpairTheory.npair_cases, numpairTheory.nfst_npair]) 
  >> rfs[]
  >> Cases_on `inst_Dest (M.tf q) (rs (regOf (M.tf q)))` 
  (* NONE *)
  >- (fs[] >> rw[FUN_EQ_THM, APPLY_UPDATE_THM] >> rw[] 
        >- rw[APPLY_UPDATE_THM] (*>> *)
        >> Cases_on `nfst x ≠ mnum` 
        >- simp[]
        >> rw[] 
        >> metis_tac[APPLY_UPDATE_THM, npair])
  (* SOME *)
  >> first_x_assum irule 
  >> rw[]
  >- (rw[APPLY_UPDATE_THM] >> metis_tac[nfst_npair])
  >- (map_every qexists_tac [`rs⦇regOf (M.tf q) ↦ inst_Val (M.tf q) (rs (regOf (M.tf q)))⦈`, `rs'`] >>
      rw[APPLY_UPDATE_THM])
  >> metis_tac[inst_Dest_wf]
QED

Definition liftP_def:
  liftP n P = (λrs. P (λr. rs (npair n r)))
End 

(* rmcorr M q P opt Q ==> rmcorr (mrInst n M) q (λrs. (P (λr. rs (nsnd r))) ∧ (λr. nfst r = mnum)) opt (λrs. Q (λr. rs (nsnd r)))*)
Theorem mrInst_correct:
 (wfrm M ∧ q ∈ M.Q ∧ P' = liftP n P ∧ Q' = liftP n Q) ⇒
  (rmcorr M q P opt Q ⇒ rmcorr (mrInst n M) q P' opt Q')
Proof
  rw[liftP_def, rmcorr_def] >>
  rename [`P (λr. rsm (mnum ⊗ r))`] >>
  `∃n rs'. run_step M ((λr. rsm (mnum ⊗ r)),SOME q) n = (rs',opt) ∧ Q rs'` by rfs[] >>
  `rs_mrInst_B4 rsm (λr. rsm (mnum ⊗ r)) mnum` by rw[rs_mrInst_B4_def] >>
  rename [`run_step M ((λr. rsm (mnum ⊗ r)),SOME q) n = (rs',opt)`] >>
  qexists_tac `n` >> 
  drule mrInst_run_step >>
  rw[] >>
  qexists_tac `(λr. if nfst r = mnum then rs' (nsnd r) else rsm r)` >>
  `rs_mrInst_Aft (λr. if nfst r = mnum then rs' (nsnd r) else rsm r) rsm rs' mnum` 
    by rw[rs_mrInst_Aft_def] >>
  rw[] 
  >- metis_tac[]
  >> `rs' = (λr. rs' r)` by metis_tac[FUN_EQ_THM]
  >> metis_tac[]
QED

Definition liftP_V_def:
  liftP_V n P X = (λrs. P (λr. rs (n ⊗ r)) ∧ X rs)
End

(* rmcorr M q P opt Q ==> rmcorr (mrInst n M) q (λrs. (P (λr. rs (nsnd r))) ∧ (λr. nfst r = mnum)) opt (λrs. Q (λr. rs (nsnd r)))*)
Theorem mrInst_correct_V:
 ∀RS. (wfrm M ∧ q ∈ M.Q ∧ P' = liftP_V n P (λrs. rs = RS) 
       ∧ Q' = liftP_V n Q (λrs. ∀k. nfst k ≠ n ⇒ rs k = RS k))
  ⇒
  (rmcorr M q P opt Q ⇒ rmcorr (mrInst n M) q P' opt Q')
Proof
  rw[liftP_V_def, rmcorr_def] >>
  rename [`P (λr. rsm (mnum ⊗ r))`] >>
  `∃n rs'. run_step M ((λr. rsm (mnum ⊗ r)),SOME q) n = (rs',opt) ∧ Q rs'` by rfs[] >>
  `rs_mrInst_B4 rsm (λr. rsm (mnum ⊗ r)) mnum` by rw[rs_mrInst_B4_def] >>
  rename [`run_step M ((λr. rsm (mnum ⊗ r)),SOME q) n = (rs',opt)`] >>
  qexists_tac `n` >> 
  drule mrInst_run_step >>
  rw[] >>
  qexists_tac `(λr. if nfst r = mnum then rs' (nsnd r) else rsm r)` >>
  `rs_mrInst_Aft (λr. if nfst r = mnum then rs' (nsnd r) else rsm r) rsm rs' mnum` 
    by rw[rs_mrInst_Aft_def] >>
  rw[] 
  >- metis_tac[]
  >> `rs' = (λr. rs' r)` by metis_tac[FUN_EQ_THM]
  >> metis_tac[]
QED

Theorem mrInst_correct_kN:
  nfst k ≠ n ∧
  (wfrm M ∧ q ∈ M.Q ∧ P' = liftP_V n P (λrs. rs k = N) ∧ Q' = liftP_V n Q (λrs. rs k = N))
  ⇒
  (rmcorr M q P opt Q ⇒ rmcorr (mrInst n M) q P' opt Q')
Proof
  rw[liftP_V_def, rmcorr_def] >>
  rename [`P (λr. rsm (mnum ⊗ r))`] >>
  `∃n rs'. run_step M ((λr. rsm (mnum ⊗ r)),SOME q) n = (rs',opt) ∧ Q rs'` by rfs[] >>
  `rs_mrInst_B4 rsm (λr. rsm (mnum ⊗ r)) mnum` by rw[rs_mrInst_B4_def] >>
  rename [`run_step M ((λr. rsm (mnum ⊗ r)),SOME q) n = (rs',opt)`] >>
  qexists_tac `n` >> 
  drule mrInst_run_step >>
  rw[] >>
  qexists_tac `(λr. if nfst r = mnum then rs' (nsnd r) else rsm r)` >>
  `rs_mrInst_Aft (λr. if nfst r = mnum then rs' (nsnd r) else rsm r) rsm rs' mnum` 
    by rw[rs_mrInst_Aft_def] >>
  rw[] 
  >- metis_tac[]
  >> `rs' = (λr. rs' r)` by metis_tac[FUN_EQ_THM]
  >> metis_tac[]
QED

Definition npair_opt_def:
  npair_opt mnum NONE = NONE ∧
  npair_opt mnum (SOME q) = SOME (npair mnum q)
End 

Theorem regOf_msInst[simp]:
  regOf ((msInst mnum M).tf (mnum ⊗ q)) = regOf (M.tf q)
Proof
  rw[msInst_def] >>
  Cases_on `M.tf q` >>
  metis_tac[regOf_def, sInst_def]
QED 

Theorem inst_Val_msInst[simp]:
  inst_Val ((msInst mnum M).tf (mnum ⊗ q)) v = inst_Val (M.tf q) v
Proof 
  rw[msInst_def] >>
  Cases_on `M.tf q` >>
  metis_tac[inst_Val_def, sInst_def]
QED 

Theorem inst_Dest_msInst[simp]:
  inst_Dest ((msInst mnum M).tf (mnum ⊗ q)) v = npair_opt mnum (inst_Dest (M.tf q) v)
Proof 
  rw[msInst_def] >> 
  Cases_on `M.tf q` >> rw[inst_Dest_def, sInst_def, npair_opt_def] >> fs[]
  >> rename [`npair_opt mnum opt`]
  >> Cases_on `opt` >>  fs[] >>  metis_tac[npair_opt_def]
QED

Theorem msInst_run_step:
  ∀q n rs rs' M mnum. 
  wfrm M ∧ q ∈ M.Q  ⇒
  (run_step M (rs, SOME q) n = (rs', opt) ⇒ 
  run_step (msInst mnum M) (rs, SOME (npair mnum q)) n = (rs', npair_opt mnum opt))
Proof 
  Induct_on `n` >> rw[npair_opt_def, run_step_def, run_machine_1_alt]
  (* 0 Case *)
  >- metis_tac[npair_opt_def]
  (* Inductive Case *)
  >- fs[msInst_def]  (* (mnum, q) not in new machine's Q (False) *)
  >- fs[msInst_def] 
  >> Cases_on `inst_Dest (M.tf q) (rs (regOf (M.tf q)))`
  (* From NONE *)
  >- (fs[run_step_def] >> rw[msInst_def, npair_opt_def])
  (* From SOME *)
  >> rw[npair_opt_def] 
  >> first_x_assum irule 
  >> rw[]
  >> metis_tac[inst_Dest_wf]
QED 


Theorem msInst_correct: 
∀mnum M q P opt Q.
  (wfrm M ∧ q ∈ M.Q) ⇒ 
  (rmcorr M q P opt Q ⇒ rmcorr (msInst mnum M) (npair mnum q) P (npair_opt mnum opt) Q) 
Proof 
  metis_tac[rmcorr_def, msInst_run_step]
QED 

Theorem msInst_correct_2: 
  wfrm M ∧ q ∈ M.Q ∧ 
  rmcorr M q P opt Q ∧
    q' = npair mnum q ∧
    opt' = npair_opt mnum opt
    ⇒ rmcorr (msInst mnum M) q' P opt' Q
Proof 
  metis_tac[msInst_correct]
QED 


Definition lst_def:
  lst = <|
        Q := {1;2;3;4};
        tf := (λs. case s of 
                | 1 => Dec 1 (SOME 2) NONE
                | 2 => Dec 2 (SOME 1) (SOME 3)
                | 3 => Inc 3 (SOME 4)
                | 4 => Dec 1 (SOME 4) (SOME 1));
        q0 := 1;
        In := [1;2];
        Out := 3;
        |>
End


Theorem lst_thms[simp]:
  lst.Q = {1;2;3;4} ∧
  lst.tf 1 = Dec 1 (SOME 2) NONE ∧
  lst.tf 2 = Dec 2 (SOME 1) (SOME 3) ∧
  lst.tf 3 = Inc 3 (SOME 4) ∧
  lst.tf 4 = Dec 1 (SOME 4) (SOME 1)
Proof 
  rw[lst_def]
QED 

Theorem lst_correct:
  rmcorr lst 1 (λrs. rs = RS ∧ rs 3 = 0) NONE (λrs. rs 3 = if RS 2 < RS 1 then 1 else 0)
Proof 
  irule loop_correct >>
  simp[] >>
  qexists_tac `λrs. (rs 3 = 0 ⇒ (RS 2 < RS 1 ⇔ rs 2 < rs 1)) 
               ∧ (rs 3 = 1 ⇒ (RS 2 < RS 1) ∧ rs 1 = 0 ∧ rs 2 = 0) ∧ rs 3 < 2 ` >>
  simp[] >>
  rpt strip_tac >>
  rw[APPLY_UPDATE_THM] >>
  irule rmcorr_dec >> 
  simp[] >>
  rw[] 
  >- (irule rmcorr_inc >> simp[] >> 
      irule loop_correct >> simp[APPLY_UPDATE_THM] >>
      map_every qexists_tac [`λrs. rs 3 = 1 ∧ (RS 2 < RS 1) ∧ rs 2 = 0`] >> 
      simp[] >>
      rw[APPLY_UPDATE_THM] >> 
      rw[rmcorr_stay])
  >> rw[APPLY_UPDATE_THM] 
  >> `∀rs0. (λrs.((rs 3 = 0 ⇒ (RS 2 < RS 1 ⇔ rs 2 < rs 1)) ∧ rs 3 ≠ 1 ∧ rs 3 < 2) ∧
          rs 1 = N) rs0
   ==>  
    (λrs'.((rs' 3 = 0 ⇒ (RS 2 < RS 1 ⇔ rs' 2 < rs' 1)) ∧
           (rs' 3 = 1 ⇒ RS 2 < RS 1 ∧ rs' 1 = 0 ∧ rs' 2 = 0) ∧ rs' 3 < 2) ∧
          rs' 1 ≤ N) rs0` by rw[APPLY_UPDATE_THM]
  >> rw[rmcorr_stay] 
QED


Definition Tri_def:
  Tri = <|
          Q :={1;2;3;4;5;6;7};
          tf :=(λs. 
                  case s of 
                  | 1 => Dec 1 (SOME 2) NONE
                  | 2 => Inc 2 (SOME 3) 
                  | 3 => Dec 1 (SOME 4) (SOME 6)
                  | 4 => Inc 2 (SOME 5)
                  | 5 => Inc 3 (SOME 3)
                  | 6 => Dec 3 (SOME 7) (SOME 1)
                  | 7 => Inc 1 (SOME 6)
                );
          q0 := 1;
          In := [1];
          Out := 2;
|>
End

val tri = EVAL ``RUN Tri [10]``;


Theorem Tri_facts[simp] = generate_machine_rwts Tri_def

Theorem Tri_correct:
 rmcorr Tri 1 (λrs. rs = RS ∧ ∀k. k ∈ {2;3} ⇒ rs k = 0) NONE (λrs. rs 2 = tri (RS 1))
Proof 
  irule loop_correct >> simp[] >>
  qexists_tac `(λrs. rs 2 + tri (rs 1) = tri (RS 1) ∧ rs 3 = 0)` >>
  rw[] 
  >- fs[]
  >> irule rmcorr_inc >> simp[]
  >> rw[APPLY_UPDATE_THM]
  >> irule rmcorr_trans 
  >> map_every qexists_tac [`(λrs. rs 1 = 0 ∧ rs 2 + tri (rs 3) = tri (RS 1) ∧ rs 3 = N)`, `6`]
  >> rw[APPLY_UPDATE_THM]
  >- (irule loop_correct >> simp[] 
      >> qexists_tac `(λrs. rs 1 + rs 2 + tri (rs 1 + rs 3) = tri (RS 1) ∧ rs 1 + rs 3 = N)` >> rw[APPLY_UPDATE_THM]
      >- fs[GSYM ADD1]
      >- fs[]
      >> irule rmcorr_inc >> simp[APPLY_UPDATE_THM]
      >> irule rmcorr_inc >> simp[APPLY_UPDATE_THM]
      >> irule rmcorr_stay >> rw[]
      >> fs[]
      )
  >> irule loop_correct >> simp[] 
  >> qexists_tac `λrs. rs 2 + tri (rs 1 + rs 3) = tri (RS 1) ∧ rs 1 + rs 3 = N`
  >> rw[APPLY_UPDATE_THM]
  >- fs[]
  >- fs[]
  >> irule rmcorr_inc >> simp[]
  >> irule rmcorr_stay >> simp[APPLY_UPDATE_THM]
  >> rw[]
  >> fs[]
QED 



Definition invTri_def:
  invTri = <|
      Q := {1;2;3;4;5;6;7;8};
      tf := (λs. case s of 
                     1 => Dec 1 (SOME 2) (SOME 7)
                  |  2 => Dec 2 (SOME 3) (SOME 4)
                  |  3 => Inc 3 (SOME 1)
                  |  4 => Dec 3 (SOME 5) (SOME 6)
                  |  5 => Inc 2 (SOME 4)
                  |  6 => Inc 2 (SOME 1)
                  |  7 => Dec 3 (SOME 8) NONE
                  |  8 => Inc 2 (SOME 7) 
                   );
      q0 := 1;
      In := [1];
      Out := 2;
    |>
End


Theorem invTri_facts[simp] = generate_machine_rwts invTri_def

Theorem invTri_correct:
  rmcorr invTri 1 (λrs. rs = RS ∧ ∀k. k ∈ {2;3} ⇒ rs k = 0) NONE (λrs. rs 2 = invtri (RS 1))
Proof 
  irule rmcorr_trans >> simp[] >>
  map_every qexists_tac [`λrs. (rs 3 + rs 2) = invtri (RS 1)`,`7`] >>
  rw[]
  (* LOOP *)
  >- (irule loop_correct >> simp[] >> 
      qexists_tac `λrs. SND (invtri0 (rs 1 + rs 3) (rs 2 + rs 3)) = invtri (RS 1)` >>
      rw[]
      >- rw[invtri_def]
      >- fs[Once invtri0_def]
      >> rw[APPLY_UPDATE_THM]
      (*     -> 4 (-> 5) -> 6
         2                    -> 1
                   -> 3              *)
      >> irule rmcorr_dec >> simp[]
      >> rw[APPLY_UPDATE_THM]
        (* 2    -> 4 (-> 5) -> 6 ->   1*)
      >- (irule rmcorr_trans >> simp[] >>
          map_every qexists_tac [`λrs. rs 3 = 0 ∧ rs 1 = N ∧
                 SND (invtri0 (rs 1 + rs 2 + 1) (rs 2)) = invtri (RS 1)` ,`6`] >>
          rw[]
            (* 4 -> 6 *)
          >- (irule loop_correct >> simp[] >>
               qexists_tac `λrs. rs 1 = N ∧ 
                  SND (invtri0 (rs 1 + rs 2 + rs 3 + 1) (rs 2 + rs 3)) = invtri (RS 1)` >> rw[]
               >- fs[Once invtri0_def]
               >- fs[Once invtri0_def]
               >> irule rmcorr_inc >> simp[]
               >> irule rmcorr_stay >> simp[] 
               >> rw[APPLY_UPDATE_THM]
               >> fs[])
            (* 6 -> 1 *)
          >> irule rmcorr_inc >> simp[]
          >> rw[APPLY_UPDATE_THM]
          >> irule rmcorr_stay >> simp[] 
          >> rw[]
          >> fs[]
          >> `invtri0 (rs 1 + rs 2) (rs 2 − 1) = invtri0 (rs 1) (rs 2)` by simp[Once invtri0_def]
          >> metis_tac[]
          )
        (* 2 -> 3 -> 1*)
      >> irule rmcorr_inc >> simp[]
      >> rw[APPLY_UPDATE_THM]
      >> irule rmcorr_stay >> simp[] 
      >> rw[]
      >> fs[]
      )
  (* RETURN r2+r3 *)
  >> irule loop_correct >> simp[]
  >> qexists_tac `λrs. rs 3 + rs 2 = tri⁻¹ (RS 1)`
  >> rw[APPLY_UPDATE_THM]
  >> irule rmcorr_inc >> simp[]
  >> irule rmcorr_stay >> simp[] 
  >> rw[APPLY_UPDATE_THM]
QED 


(* Pair f g n = npair (f n) (g n) 

npair 0 0 = 0 (input register) 
npair 0 2 = 5 (input register) 
npair 0 1 = 2 (scratch register) 
*)
Definition Pair_def:
  Pair = 
        let 
            add1 = mrInst 1 simp_add;
            tri' = mrInst 2 Tri;
            add2 = mrInst 3 simp_add;

            dup00_1 = dup 0 (HD add1.In) 2;
            dup01_1 = dup 5 (EL 1 add1.In) 2;
            dup01_3 = dup 5 (HD add2.In) 2;
            
            dup1_2 = dup add1.Out (HD tri'.In) 2;
            
            dup2_3 = dup tri'.Out (EL 1 add2.In) 2;

            mix = [dup00_1; dup01_1; dup01_3; add1; dup1_2; tri'; dup2_3; add2];
            mix' = MAPi msInst mix;
        in 
          link_all mix' with In := [0;5]
End



(* FST n = nfst n 
    FST.In = 0; 
    FST.Out = 16 (sub.Out) 

npair 0 0 = 0 (input register) 
npair 0 1 = 2 (scratch register) 
npair 4 1 = 16 (output register )
*)
Definition FST_def:
  FST = 
        let 
            tri' = mrInst 1 Tri;
            invtri' = mrInst 2 invTri;
            add = mrInst 3 simp_add;
            sub = mrInst 4 simp_sub;

            dup0_2 = dup 0 (HD invtri'.In) 2;
            dup0_4 = dup 0 (EL 1 sub.In) 2;
            
            dup2_3 = dup invtri'.Out (HD add.In) 2;
            dup2_1 = dup invtri'.Out (HD tri'.In) 2;
            
            dup1_3 = dup tri'.Out (EL 1 add.In) 2;

            dup3_4 = dup add.Out (HD sub.In) 2;

            mix = [dup0_2; dup0_4; invtri'; dup2_3; dup2_1; tri'; dup1_3; add; dup3_4; sub];
            mix' = MAPi msInst mix;
        in 
          link_all mix' with In := [0]
End


(* SND n = nsnd n *)
Definition SND_def:
  SND = 
        let 
            invtri' = mrInst 1 invTri;
            tri' = mrInst 2 Tri;
            sub = mrInst 3 simp_sub;

            dup0_1 = dup 0 (HD invtri'.In) 2;
            dup0_3 = dup 0 (HD sub.In) 2;
            
            dup1_2 = dup invtri'.Out (HD tri'.In) 2;
            
            dup2_3 = dup tri'.Out (EL 1 sub.In) 2;

            mix = [dup0_1; dup0_3; invtri'; dup1_2; tri'; dup2_3; sub];
            mix' = MAPi msInst mix;
        in 
          link_all mix' with In := [0]
End


Theorem rInst_states[simp]:
  action_states (rInst mnum act) = action_states act
Proof 
  Cases_on `act` >>
  rw[rInst_def, action_states_def]
QED 

Theorem mrInst_wfrm[simp]:
∀mnum f.  wfrm (mrInst mnum f) ⇔  wfrm f
Proof 
  rw[wfrm_def, mrInst_def]
QED

Theorem opt_to_set_OPTION_MAP[simp]:
   opt_to_set (OPTION_MAP f stop) = {f x| x ∈ opt_to_set stop}
Proof 
  Cases_on `stop` >> 
  rw[EXTENSION, optionTheory.OPTION_MAP_DEF, opt_to_set_def] 
QED 

Theorem sInst_states[simp]:
  action_states (sInst mnum act) = {npair mnum x | x ∈ action_states act}
Proof 
  Cases_on `act` >> 
  rw[sInst_def, action_states_def, EXTENSION] >>
  metis_tac[]
QED 

Theorem msInst_wfrm[simp]:
∀mnum f.  wfrm (msInst mnum f) ⇔  wfrm f
Proof 
  rw[wfrm_def, msInst_def, PULL_EXISTS] >>
  rw[pred_setTheory.SUBSET_DEF] >>
  rw[PULL_EXISTS] 
QED

Theorem mrInst_Q[simp]:
  (mrInst mnum f).Q = f.Q ∧ (mrInst mnum f).q0 = f.q0
Proof 
  rw[mrInst_def]
QED 

Theorem msInst_Q[simp]:
  (msInst mnum f).Q = {npair mnum x | x ∈ f.Q} ∧ (msInst mnum f).q0 = npair mnum f.q0
Proof 
  rw[msInst_def, EXTENSION]
QED

Theorem msInst_In[simp]:
  (msInst mnum f).In = f.In 
Proof 
  rw[msInst_def]
QED 

Theorem mrInst_In[simp]:
  (mrInst mnum f).In = MAP (λr. npair mnum r) f.In
Proof 
  rw[mrInst_def]
QED

Theorem msInst_mrInst_In[simp]:
 (msInst mnum' (mrInst mnum f)).In = MAP (λr. npair mnum r) f.In
Proof 
  rw[]
QED


Theorem msInst_Out[simp]:
  (msInst mnum f).Out = f.Out
Proof 
  rw[msInst_def]
QED 

Theorem mrInst_Out[simp]:
  (mrInst mnum f).Out = npair mnum f.Out
Proof 
  rw[mrInst_def]
QED

Theorem msInst_with_In[simp]:
  msInst mnum m with In := x = msInst mnum (m with In := x)
Proof 
  rw[msInst_def]
QED 


Theorem link_facts[simp]:
  (link m1 m2).q0 = m1.q0 ∧
  (link m1 m2).Out = m2.Out
Proof 
  rw[link_def]
QED 


Theorem dup_wfrm[simp]:
 ∀r1 r2 r3. wfrm (dup r1 r2 r3)
Proof 
  rw[dup_def, wfrm_def, action_states_def, opt_to_set_def] >>
  rw[dup_def, wfrm_def, action_states_def, opt_to_set_def]
QED



(*
Theorem link_associative:
∀a b c.  wfrm a ∧ wfrm b ∧ wfrm c ∧ 
         DISJOINT a.Q b.Q ∧ DISJOINT a.Q c.Q ∧ DISJOINT b.Q c.Q
      ⇒ (a ⇨ b) ⇨ c = a ⇨ (b ⇨ c)
Proof
  rw[link_def]
  >- rw[UNION_ASSOC]
  >> fs[wfrm_def]
  >> fs[DISJOINT_DEF]
  >> `c.q0 ∉ (a.Q ∪ b.Q)`
        by (rw[]
            >- (SPOSE_NOT_THEN ASSUME_TAC >> `c.q0 ∈ a.Q ∩ c.Q` by rw[INTER_DEF] 
                >> metis_tac[NOT_IN_EMPTY])
            >> SPOSE_NOT_THEN ASSUME_TAC >> `c.q0 ∈ b.Q ∩ c.Q` by rw[INTER_DEF] 
                >> metis_tac[NOT_IN_EMPTY])
  >> `b.q0 ∉ a.Q` by (SPOSE_NOT_THEN ASSUME_TAC >>
                       `b.q0 ∈ a.Q ∩ b.Q` by rw[INTER_DEF] >> metis_tac[NOT_IN_EMPTY])
  >> rw[linktf_def]
QED
*)
(*

Theorem link_first:
  rmcorr (
Proof 
QED 
*)
Theorem link_with_In[simp]:
∀a b lst. link a b with In := lst = link (a with In := lst) b 
Proof  
  rw[link_def] 
QED 

Theorem link_In[simp]:
∀a b. (link a b).In = a.In
Proof 
  rw[link_def]
QED

Theorem link_wfrm[simp]:
  wfrm m1 ∧ wfrm m2 ⇒ wfrm (link m1 m2) 
Proof 
  rw[wfrm_def, link_def, linktf_def] >> simp[]
  >- (Cases_on`m1.tf s` >> rw[end_link_def] 
        >- (Cases_on`o'` >> rw[] >> last_x_assum drule >> rw[])
        >- (Cases_on`o'` >> rw[] >> last_x_assum drule >> rw[]) 
        >> Cases_on`o0` >> rw[] >> last_x_assum drule >> rw[])
  >> Cases_on`s ∈ m1.Q` >> rw[]
  >- (Cases_on`m1.tf s` >> rw[end_link_def] 
        >- (Cases_on`o'` >> rw[] >> last_x_assum drule >> rw[])
        >- (Cases_on`o'` >> rw[] >> last_x_assum drule >> rw[]) 
        >> Cases_on`o0` >> rw[] >> last_x_assum drule >> rw[])
  >> metis_tac[SUBSET_DEF, IN_UNION]
QED 

Theorem wfrm_In[simp]:
∀x m.  wfrm (m with In := x) = wfrm m 
Proof 
  rw[wfrm_def]
QED 

Theorem with_In[simp]:
∀m.  (m with In := m.In) = m 
Proof 
 simp[rm_component_equality]
QED 


Theorem Cn_correct: 
  wfrm g ∧ wfrm f ∧ LENGTH g.In = 1 ∧ LENGTH f.In = 1 
∧
  rmcorr g g.q0 (λrs. rs (HD g.In) = M) NONE (λrs. rs g.Out = N)
∧ 
  rmcorr f f.q0 (λrs. rs (HD f.In) = N) NONE (λrs. rs f.Out = Op)

⇒ rmcorr (Cn f g) (Cn f g).q0 (λrs. rs (HD (Cn f g).In)= M ∧ rs (npair 0 1) = 0) NONE (λrs. rs (Cn f g).Out = Op) 
Proof 
  rw[Cn_def, link_all_def] >>
  irule link_correct >> simp[] >> rw[]
  >- (rw[DISJOINT_DEF, EXTENSION] >> metis_tac[npair_11, DECIDE``2 ≠ 0``])
  >- (rw[DISJOINT_DEF, EXTENSION] >> metis_tac[npair_11, DECIDE``2 ≠ 1``])
  >> qexists_tac `λrs. rs (HD (msInst 2 (mrInst 1 f)).In) = N`
  >> reverse (rw[])
  >- (irule msInst_correct_2 >> rw[] >> qexists_tac`NONE` >> rw[]
      >- rw[npair_opt_def]
      >- metis_tac[wfrm_def]
      >> irule mrInst_correct >> rw[] 
      >- metis_tac[wfrm_def]
      >> map_every qexists_tac [`(λrs. rs (HD f.In) = N)`,`(λrs. rs f.Out = Op)`]
      >> rw[liftP_def]
      >> (Cases_on`f.In` >> fs[]))
  >> irule link_correct >> simp[] >> rw[]
  >- (rw[DISJOINT_DEF, EXTENSION] >> metis_tac[npair_11, DECIDE``1 ≠ 0``])
  >> qexists_tac `λrs. rs (npair 0 1) = 0 ∧ rs (msInst 0 (mrInst 2 g) with In := MAP (λr. 2 ⊗ r) g.In).Out = N`
  >> reverse (rw[])
  >- (irule msInst_correct_2 >> rw[] >> qexists_tac`NONE` >> rw[]
      >- rw[npair_opt_def]
      >> irule rmcorr_weakening >> simp[]
      >> map_every qexists_tac [`(λrs. rs (0 ⊗ 1) = 0 ∧ rs (2 ⊗ g.Out) = N)`,`(λrs.
                 rs (0 ⊗ 1) = 0 ∧ rs (2 ⊗ g.Out) = N ∧
                 rs (HD (MAP (λr. 1 ⊗ r) f.In)) = N)`]
      >> rw[]
      >> irule dup_correct_2
      >> rw[]
      >- (Cases_on`f.In` >> fs[])
      >- (Cases_on`f.In` >> fs[])
      >> qexists_tac`N`
      >> rw[])
  >> irule msInst_correct_2 >> rw[]
  >> qexists_tac `NONE` >> rw[]
  >- rw[npair_opt_def]
  >- metis_tac[wfrm_def]
  >> `(mrInst 2 g).In = MAP (λr. 2 ⊗ r) g.In` by rw[]
  >> `mrInst 2 g with In := MAP (λr. 2 ⊗ r) g.In = mrInst 2 g with In := (mrInst 2 g).In` 
        by metis_tac[]
  >> rw[]
  >> Cases_on `g.In` >> fs[]
  >> irule mrInst_correct_kN >> rw[]
  >- fs[wfrm_def]
  >> map_every qexists_tac [`0`, `(λrs. rs h = M)`,`(λrs. rs g.Out = N)`, `0 ⊗ 1`]
  >> rw[liftP_V_def]
  >> metis_tac[]
QED 



(* TODO 
5. prove npair snd fst 
6. report
7. Rewrite exp and fac proof etc with the loop theorem 

 *)
 (*

2. correct function in terms of rmcorr
3. (unary function) correct m1 f /\ correct m2 g ==>  correct (Cn m1 m2) (f o g)*)



val _ = export_theory ()