Section Group.

  Variable (D:Set) (op: D->D->D) (inv: D->D) (ne:D).

  Notation "x + y" := (op x y).
  Notation "0" := ne.

  Axiom ne_left :  forall x:D, 0 + x = x.
  Axiom ne_right : forall x:D, x + 0 = x.

  Axiom op_assoc : forall x y z:D, x + (y + z) = (x + y) + z.

  Axiom inverse_works: forall x:D, inv x + x = 0 /\ x + inv x = 0.

  Theorem ne_unique:
    forall ne', (forall x, x + ne' = x /\ ne' + x = x) -> ne' = 0.
  Proof. intros ne' H.
         assert (ne' + 0 = ne') as H1. { apply ne_right. }
         assert (ne' + 0 = 0) as H2. { destruct (H ne) as [HN1 HN2]. apply HN2. }
         rewrite <- H1. rewrite H2. reflexivity.
  Qed.

  Theorem inverse_unique:
    forall x, (forall ix, x+ix = 0 /\ ix+x = 0 -> ix = inv x).
  Proof. intros. destruct H as [HL HR].
         assert (ix = ix + 0) as H1. { symmetry. apply ne_right. }
         destruct (inverse_works x) as [HI1 HI2].
         rewrite <- HI2 in H1. rewrite op_assoc in H1. rewrite HR in H1.
         rewrite ne_left in H1. apply H1.
  Qed.
End Group.

Require Export ZArith.
Open Scope Z_scope.

Locate "_ + _".

Check inverse_unique Z Z.add (fun x => -x) 0.