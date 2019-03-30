Require Import ZArith.
Require Import QArith.
Open Scope Q_scope.

Inductive Seq (T:Set) := mkSeq (seq_elt:nat->T).
Definition elt {T:Set} (seq: Seq T) n := match seq with
                                         | mkSeq _ f => f n
                                         end.

Inductive converging_qseq: Seq Q -> Prop :=
 ex_limit (s:Seq Q) (a:Q) (H: forall eps:Q, eps>0 -> exists (n0:nat), forall (n:nat), (n0 <= n)%nat -> a - eps < elt s n /\
                                                                       a + eps > elt s n)
 : converging_qseq s.

Definition qseq_const := fun a => mkSeq Q (fun n => a).
Definition qseq_plus sx sy := mkSeq Q (fun n => elt sx n + elt sy n).


Open Scope Q_scope.
Lemma lt_lower: forall a p, p > 0 -> a - p < a.
Proof. intros. unfold Qminus. rewrite <- Qplus_0_r with (x:=a) at 2.
       rewrite Qplus_comm. rewrite (Qplus_comm a 0). apply (Qplus_lt_le_compat (-p) 0 a a ).
       - unfold Qlt. simpl. rewrite Z.mul_comm. rewrite (Z.mul_1_l (-Qnum p)).
         unfold Qlt in H. simpl in H. rewrite Z.mul_comm in H. rewrite (Z.mul_1_l (Qnum p)) in H.
         apply Z.opp_lt_mono. rewrite Z.opp_involutive. rewrite Z.opp_0. exact H.
       - apply Z.le_refl.
Qed.

Theorem converging_const: forall a, converging_qseq (qseq_const a).
Proof. intros. apply (ex_limit (qseq_const a) a).
       intros eps Heps. exists 0%nat. intros.
       split.
       - simpl. apply lt_lower. exact Heps.
       - simpl. rewrite <- Qplus_0_l at 1.  rewrite (Qplus_comm a eps). rewrite Qplus_lt_l. exact Heps.
Qed.


Lemma split_halfs: forall a, a == a * (1#2) + a * (1#2).
Proof. intros. ring_simplify. easy.
Qed.

Lemma dswap: forall a b c d, a+b+c+d == (a+c) +(b+d).
  intros. ring_simplify. easy.
Qed.

Theorem converging_sum: forall s1 s2, converging_qseq s1 -> converging_qseq s2 -> converging_qseq (qseq_plus s1 s2).
Proof. intros s1 s2 H1 H2. destruct H1 as [s1 a Ha]. destruct H2 as [s2 b Hb].
       apply (ex_limit (qseq_plus s1 s2) (a+b)). intros.

       assert (0 < 1#2) as Heps2. { unfold Qlt. simpl. apply Z.lt_0_1. }
       assert (HH := Qmult_lt_compat_r 0 eps (1#2) Heps2 H).  rewrite Qmult_0_l in HH.
       assert (Ha := Ha (eps * (1#2) ) HH).
       assert (Hb := Hb (eps * (1#2) ) HH).
       destruct Ha as [na Ha]. destruct Hb as [nb Hb].
       set (mab := max na nb).
       exists mab. intros n Hmax.

       split.
       (* lower bound *)
       - rewrite (split_halfs eps) at 1. unfold Qminus. rewrite Qopp_plus. rewrite Qplus_assoc.
         rewrite dswap. simpl.
         apply Qplus_lt_le_compat.
         + apply Ha.  apply Nat.le_trans with (m:= mab). apply Nat.le_max_l. exact Hmax.
         + unfold Qminus in Hb. apply Qlt_le_weak. apply Hb.
           apply Nat.le_trans with (m:= mab). apply Nat.le_max_r. exact Hmax.
       (* upper bound *)
       - rewrite (split_halfs eps). rewrite Qplus_assoc, dswap.
         apply Qplus_lt_le_compat.
         + apply Ha. apply Nat.le_trans with (m:= mab). apply Nat.le_max_l. exact Hmax.
         + apply Qlt_le_weak. apply Hb. apply Nat.le_trans with (m:= mab). apply Nat.le_max_r. exact Hmax.
Qed.

