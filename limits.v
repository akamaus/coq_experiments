Require Import ZArith.

Open Scope Z_scope.

Definition tst1 := 2 <= 4.

Print Z.le.

Search Z.le.

Print Z.
Print Z.compare.
Compute (2 ?= 4).

Theorem tst1_true: tst1.
Proof. intros. unfold tst1. apply Z.le_trans with (m:=3). apply Z.le_succ_diag_r. apply Z.le_succ_diag_r. Qed.

Require Import QArith.

Open Scope Q_scope.
Compute (3 # 4) + (2 # 3) <= 100 # 4.

Set Printing All.
Check (1 <= 2 <= 3) %Z.
Unset Printing All.

Search Q.

Theorem xxx: true <> false.
Proof. unfold not. intro. discriminate.
Qed.

Print xxx.
Print eq_ind.
Print True_ind.
Print Qmult_0_l.

Check eq_ind false.

(* Set Printing All. *)
Print Qeq.

Require Import ZArith.
Require Import QArith.
Open Scope Q_scope.

Theorem q_less: forall x y z, (0 <= x <= y)%Z -> x # z <= y # z.
Proof. intros. destruct H as [Hl Hr]. rewrite (Zle_Qle x y) in Hr.
       rewrite <- (Qmult_le_l (inject_Z x) (inject_Z y) (/ inject_Z (Zpos z))) in Hr. simpl in Hr.
       - rewrite Qmult_comm in Hr. rewrite Qmult_comm with (x := / inject_Z (Z.pos z)) in Hr.
         unfold inject_Z in Hr. unfold Qinv in Hr. destruct (Qnum (Z.pos z # 1)) eqn:ZV.
         + simpl in ZV. discriminate.
         + simpl in Hr. simpl in ZV. injection ZV. intro ZP. unfold Qmult in Hr. simpl in Hr.
           rewrite <- ZP in Hr. rewrite Z.mul_1_r in Hr. rewrite Z.mul_1_r in Hr. exact Hr.
         + simpl in ZV. discriminate.
       - unfold Qinv. simpl. apply Z.lt_0_1.
Qed.

Check Z.

Inductive Seq (T:Set) := mkSeq (seq_elt:nat->T).
Definition elt {T:Set} (seq: Seq T) n := match seq with
                                         | mkSeq _ f => f n
                                         end.

Check elt.
Check mkSeq.
Check Seq.

Check 1.
Check mkSeq Q (fun n => 1).
Check Seq Q.
Check cons 1 nil.

Inductive converging_qseq: Seq Q -> Prop :=
 ex_limit (s:Seq Q) (a:Q) (H: forall eps:Q, eps>0 -> exists (n0:nat), forall (n:nat), (n0 <= n)%nat -> a - eps < elt s n /\
                                                                       a + eps > elt s n)
 : converging_qseq s.

Definition const_qseq := fun a => mkSeq Q (fun n => a).

(* Open Scope Z_scope. *)
(* Lemma zlt_pos: forall a,b,p ->  *)

(* Set Printing All. *)

Lemma lt_lower: forall a p, p > 0 -> a - p < a.
Admitted.
Lemma le_lower: forall a p, p >= 0 -> a - p <= a.
Proof.
  intros. unfold Qminus. rewrite <- Qplus_0_r with (x:=a) at 2. apply (Qplus_le_compat a a (-p) (0%Q)).
  - apply Qle_refl.
  - (* apply Qopp_le_compat. *)
    Admitted.


Theorem const_converging: forall a, converging_qseq (const_qseq a).
Proof. intros. apply (ex_limit (const_qseq a) a).
       intros eps Heps. exists 0%nat. intros.
       split.
       - simpl. apply lt_lower. exact Heps.
       - simpl. rewrite <- Qplus_0_l at 1.  rewrite (Qplus_comm a eps). rewrite Qplus_lt_l. exact Heps.
Qed.