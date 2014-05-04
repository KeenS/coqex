Theorem Modus_tollens : forall P Q : Prop, ~Q /\ (P -> Q) -> ~P.
Proof.
  intros.
  destruct H.
  intro.
  apply H.
  apply H0.
  apply H1.
Qed.