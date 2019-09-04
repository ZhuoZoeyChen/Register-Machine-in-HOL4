open HolKernel Parse boolLib bossLib;
open arithmeticTheory;
open combinTheory;
open whileTheory;
open indexedListsTheory;
open numeralTheory;
open registerMachineTheory;

Theorem _ = new_theory "testing";

Theorem _ = computeLib.set_skip computeLib.the_compset ``COND`` (SOME 1);

fun teval n t = 
  let 
    Theorem i = ref n
    fun stop t = if !i <= 0 then true else (i := !i - 1; false)
  in
    with_flag (computeLib.stoppers, SOME stop) (computeLib.WEAK_CBV_CONV computeLib.the_compset) t
  end;


(* strip_state *)
Theorem st = EVAL ``strip_state (Inc 5 (SOME 4))``
Theorem st2 = EVAL ``strip_state (Inc 5 NONE)``
Theorem st3 = EVAL ``strip_state (Dec 199 (SOME 4) NONE)``
Theorem stf = EVAL ``FOLDL (λe s. e ∧ ((s-1 ∈ {1}) ∨ (s = 0))) T st2``

(* Well-definedness *)
Theorem wfep = EVAL ``wfrm empty``
Theorem wfad = EVAL ``wfrm addition``

(* Constant Machine *)
Theorem test_const = EVAL ``RUN (const 0) [10]``;
Theorem test_const2 = EVAL ``RUN (const 1) [10]``;
Theorem test_const3 = EVAL ``RUN (const 10) [10]``;

(* Identity Machine *)
Theorem test_iden = EVAL ``RUN identity [5; 6]``;

(* Empty Machine *)
Theorem empty_lemma = EVAL `` run_machine empty (init_machine empty [3])``

(* Transfer Machine *)
Theorem transfer_lemma = EVAL `` run_machine transfer (init_machine transfer [10])``

(* Double Machine *)
Theorem test_double = EVAL ``RUN double [15]``

(* Duplicate Machine *)
Theorem test_dup = EVAL ``RUN (dup 14 15 0) [27]``;


(* mrInst *)
(*
Theorem test_mrInst_add = EVAL``RUN (mrInst 3 addition) [15; 26]``;

Theorem test_mrInst_constr = EVAL ``mrInst 3 addition``;

Theorem test_mrInst_add2 = EVAL 
  ``run_machine (mrInst 3 addition) (init_machine (mrInst 3 addition) [15; 26])``;
*)

(* msInst *)
(*
Theorem test_msInst_RUN = EVAL``RUN (msInst 3 addition) [15; 26]``;

Theorem test_msInst_add = teTheorem 1000 ``(msInst 2 addition)``;
*)

(* Components of Cn *)


(*
Theorem test_lka = EVAL``link_all [(mrInst 1 (msInst 1 identity)); (mrInst 2 (msInst 2 identity))]``;

Theorem test_link_out = EVAL ``RUN (link_all [identity;identity2]) [5]``;


Theorem test_id2 = EVAL ``RUN identity2 [15]``;

Theorem test_link = EVAL `` RUN (msInst 0 identity ⇨ msInst 2 (dup0 0 10 1 ) ⇨ msInst 1 identity2) [15] ``;

Theorem test_link_ddd = teTheorem 10000 ``(MAPi msInst [double; double])``;

Theorem test_link_run = EVAL ``
    let ma = (let m = MAPi (λi m. (mrInst (i+1) m)) [double;double];
                                 dup = dup0 (HD m).Out (HD (LAST m).In) 0;
                                 mix = MAPi msInst [HD m ; dup ; LAST m]
               in 
                 link_all mix)
    in 
      run_machine ma (init_machine ma [2])
``;

Theorem test_link_RUN = EVAL ``RUN (let m = MAPi (λi m. (mrInst (i+1) m)) [double;double];
                                 dup = dup0 (HD m).Out (HD (LAST m).In) 0;
                                 mix = MAPi msInst [HD m ; dup ; LAST m]
               in 
                 link_all mix) [5]``;

Theorem test_1 = computeLib.RESTR_EVAL_CONV [``$o``] `` let m = MAPi (λi m. (mrInst (i+1) m)) [double;double];
                                 dup = dup0 (HD m).Out (HD (LAST m).In) 0;
                                 mix = MAPi msInst [HD m ; dup ; LAST m]
               in 
                 link_all mix``;
*)

(* Simp_add *)
Theorem s_adR = EVAL ``RUN simp_add [15; 23]``;
Theorem s_adr = EVAL ``run_machine simp_add (init_machine simp_add [15;27])``;

(* Addition *)
Theorem addition = EVAL ``addition``;
Theorem addition_0 = EVAL ``init_machine addition [15; 23]``;
Theorem addition_lemma = EVAL `` run_machine addition (init_machine addition [15; 23])``;
Theorem R_addition = EVAL ``RUN addition [15; 23]``;

(* Mult *)
Theorem multiplication_lemma = EVAL `` run_machine multiplication (init_machine multiplication [3; 4])``
Theorem multiplication_RUN = EVAL ``RUN multiplication [2; 15]``;

(* Exponential *)
Theorem exp_t1 = EVAL``RUN exponential [3;3]``

(* Factorial *)
Theorem fac_t1 = EVAL ``RUN factorial [0]``;
Theorem fac_t1 = EVAL ``RUN factorial [1]``;
Theorem fac_t1 = EVAL ``RUN factorial [3]``;
Theorem fac_t1 = EVAL ``RUN factorial [5]``;

(* Cn *)
Theorem test_Cn_iden = EVAL ``RUN (Cn identity [identity]) [5]``;
Theorem test_Cn_add = EVAL ``RUN (Cn addition [addition; addition]) [2;2]``;

(* loopguard *)
Theorem lpg = EVAL``loopguard (npair 0 2) ``;


(*Pr tests*)
Theorem add1' = EVAL``RUN (add1 with In:=[3;0;1]) [1;100;5]``;
Theorem machine =EVAL ``Pr identity (add1 with In:=[3;0;1])``;
Theorem machine =EVAL ``RUN ((Pr identity (add1 with In:=[3;0;1])) with In:=[10000000;5;9]) [1;2;3]``;
Theorem cnm = EVAL ``RUN (Cn (Pr identity (add1 with In:=[3;0;1])) [Pi 1 3; Pi 2 3]) [1;2;3]``;
(*Theorem pr_add1_E = EVAL``RUN (Pr () (Pr identity add1)) [10;3]``;
Theorem pr_mult = EVAL ``RUN (Pr (const 0) (Pr identity add1))``;
Theorem pr0 = EVAL ``RUN (Pr (const 1) (multiplication with In:=[1;0;10])) [3;1]``;
Theorem pr1 = EVAL ``RUN (Pr (const 1) (multiplication with In:=[3;0;1])) [3;2]``;*)

Theorem _ = export_theory()