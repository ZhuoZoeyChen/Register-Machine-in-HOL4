open HolKernel Parse boolLib bossLib;
open arithmeticTheory;
open combinTheory;
open whileTheory;
open indexedListsTheory;
open numeralTheory;
open registerMachineTheory;

val _ = new_theory "testing";

val _ = computeLib.set_skip computeLib.the_compset ``COND`` (SOME 1);

fun teval n t = 
  let 
    val i = ref n
    fun stop t = if !i <= 0 then true else (i := !i - 1; false)
  in
    with_flag (computeLib.stoppers, SOME stop) (computeLib.WEAK_CBV_CONV computeLib.the_compset) t
  end;


(* strip_state *)
val st = EVAL ``strip_state (Inc 5 (SOME 4))``
val st2 = EVAL ``strip_state (Inc 5 NONE)``
val st3 = EVAL ``strip_state (Dec 199 (SOME 4) NONE)``
val stf = EVAL ``FOLDL (λe s. e ∧ ((s-1 ∈ {1}) ∨ (s = 0))) T st2``

(* Well-definedness *)
val wfep = EVAL ``wfrm empty``
val wfad = EVAL ``wfrm addition``

(* Constant Machine *)
val test_const = EVAL ``RUN (const 0) [10]``;
val test_const2 = EVAL ``RUN (const 1) [10]``;
val test_const3 = EVAL ``RUN (const 10) [10]``;

(* Identity Machine *)
val test_iden = EVAL ``RUN identity [5; 6]``;

(* Empty Machine *)
val empty_lemma = EVAL `` run_machine empty (init_machine empty [3])``

(* Transfer Machine *)
val transfer_lemma = EVAL `` run_machine transfer (init_machine transfer [10])``

(* Double Machine *)
val test_double = EVAL ``RUN double [15]``

(* Duplicate Machine *)
val test_dup = EVAL ``RUN (dup 14 15 0) [27]``;


(* mrInst *)
(*
val test_mrInst_add = EVAL``RUN (mrInst 3 addition) [15; 26]``;

val test_mrInst_constr = EVAL ``mrInst 3 addition``;

val test_mrInst_add2 = EVAL 
  ``run_machine (mrInst 3 addition) (init_machine (mrInst 3 addition) [15; 26])``;
*)

(* msInst *)
(*
val test_msInst_RUN = EVAL``RUN (msInst 3 addition) [15; 26]``;

val test_msInst_add = teval 1000 ``(msInst 2 addition)``;
*)

(* Components of Cn *)


(*
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
*)

(* Simp_add *)
val s_adR = EVAL ``RUN simp_add [15; 23]``;
val s_adr = EVAL ``run_machine simp_add (init_machine simp_add [15;27])``;

(* Addition *)
val addition = EVAL ``addition``;
val addition_0 = EVAL ``init_machine addition [15; 23]``;
val addition_lemma = EVAL `` run_machine addition (init_machine addition [15; 23])``;
val R_addition = EVAL ``RUN addition [15; 23]``;

(* Mult *)
val multiplication_lemma = EVAL `` run_machine multiplication (init_machine multiplication [3; 4])``
val multiplication_RUN = EVAL ``RUN multiplication [2; 15]``;

(* Exponential *)
val exp_t1 = EVAL``RUN exponential [3;3]``

(* Factorial *)
val fac_t1 = EVAL ``RUN factorial [0]``;
val fac_t1 = EVAL ``RUN factorial [1]``;
val fac_t1 = EVAL ``RUN factorial [3]``;
val fac_t1 = EVAL ``RUN factorial [5]``;

(* Cn *)
val test_Cn_iden = EVAL ``RUN (Cn identity [identity]) [5]``;
val test_Cn_add = EVAL ``RUN (Cn addition [addition; addition]) [2;2]``;

(* loopguard *)
val lpg = EVAL``loopguard (npair 0 2) ``;


(*Pr tests*)
Theorem add1' = EVAL``RUN add1 [1;100;5]``;
val machine =EVAL ``Pr identity add1``;
val machine =EVAL ``RUN ((Pr identity add1) with In:=[10000000;5;9]) [1;2;3]``;
val cnm = EVAL ``RUN (Cn (Pr identity add1) [Pi 1 3; Pi 2 3]) [1;2;3]``;
(*val pr_add1_E = EVAL``RUN (Pr () (Pr identity add1)) [10;3]``;
val pr_mult = EVAL ``RUN (Pr (const 0) (Pr identity add1))``;
val pr0 = EVAL ``RUN (Pr (const 1) (multiplication with In:=[1;0;10])) [3;1]``;
val pr1 = EVAL ``RUN (Pr (const 1) (multiplication with In:=[3;0;1])) [3;2]``;*)

val _ = export_theory()