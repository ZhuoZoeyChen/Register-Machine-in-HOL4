open HolKernel Parse boolLib bossLib;

val _ = new_theory "subseq";
val subseq_def = Define ‘
		(subseq [] _ = T) ∧
		(subseq (x::xs) [] = F) ∧
		(subseq (x::xs) (y::ys) = 
			if x=y then subseq xs ys 
			else 		subseq (x::xs) ys)
		’; 

val th = EVAL“subseq [1;3] [1;2;3]”
val false_th = EVAL“subseq [2;3] [3;2;1]”

Theorem subseq_refl:
	∀xs. subseq xs xs
Proof
	Induct_on `xs`
		>- (simp [subseq_def]) 
		>- (simp [subseq_def])
QED


Theorem subseq_nil2[simp]:
	∀xs. subseq xs [] = (xs=[])
Proof 
	Cases_on `xs` 
		>- (simp [subseq_def])
		>- (simp [subseq_def])
QED


Theorem subseq_cons:
	(∀h t. subseq (h::t) l ⇒ subseq t l) ∧ (∀h t. subseq t l ⇒ subseq t (h::l)) 
Proof 
	Induct_on `l` >> simp [subseq_def] >> rw [] 
		>- metis_tac []
		>- (Cases_on `t` >> fs [subseq_def] >> rw [] >> metis_tac [])
QED


Theorem subseq_len:
	∀xs ys. subseq xs ys ⇒ LENGTH xs ≤ LENGTH ys
Proof
	Induct_on `ys` 
		>- simp [subseq_def] 
		>-(Cases_on `xs` >> simp [subseq_def] >> rw [] >> first_x_assum drule >> simp [] )
		(*OR 
		>-(Cases_on `xs` >> simp [subseq_def] >> rw [] >> first_x_assum irule 
		>> drule (CONJUNCT1 subseq_cons) 
		>> metis_tac [subseq_cons])*)
QED

(*
- simp is good with equation and numbers 
- metis_tac handles implication and quantifiers well, and must finish the goal
- irule and drule can work well for implications
	- irule is backwords (changes the goal)
	- drule is forwards (adds to the assumptions)
*)

Theorem subseq_eqlen:
	∀xs ys. subseq xs ys ∧ (LENGTH xs = LENGTH ys) ⇒ (xs = ys)
Proof
	Induct_on `ys` >> simp [subseq_def] >> Cases_on `xs` >> simp [subseq_def]
	>> rw [] >> Cases_on `LENGTH t = LENGTH ys` >> simp [] >> strip_tac >> drule subseq_len 
	>> simp []
QED


Theorem subseq_antisym:
	∀xs ys. subseq xs ys ∧ subseq ys xs ⇒ (xs=ys)
Proof
	rw [] >> `LENGTH xs ≤ LENGTH ys` by metis_tac [subseq_len] 
	>> `LENGTH ys ≤ LENGTH xs` by metis_tac [subseq_len] 
	>> simp [subseq_eqlen]
	(* >> irule subseq_eqlen >> simp [] *)
	(* >> drule_all subseq_eqlen >> simp [] *)

QED


Theorem subseq_trans:
	∀xs ys zs. subseq xs ys ∧ subseq ys zs ⇒ subseq xs zs
Proof 
	Induct_on `zs` >> simp []
	>> Cases_on `ys` >> simp [subseq_def] >> rw []
		>- (Cases_on `xs` >> simp [subseq_def] >> rw [] >> fs [subseq_def] >> metis_tac [])
		>- metis_tac [subseq_cons]
QED

val _ = export_theory ()
