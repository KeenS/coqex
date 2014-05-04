Theorem DeBolran1 : forall P Q : Prop, ~P \/ ~Q -> ~(P /\ Q).
Proof.
  intros.
  destruct H.
  intro.
  destruct H0.
  apply H, H0.
  intro.
  destruct H.
  destruct H0.
  apply H0.
Qed.

Theorem DeBolran2 : forall P Q : Prop, ~P /\ ~Q -> ~(P \/ Q).
Proof.
  intros.
  destruct H.
  intro.
  destruct H1.
  apply H, H1.
  apply H0, H1.
Qed.

Theorem DeBolran3 : forall P Q : Prop, ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  intros.
  split.
  intro.
  destruct H.
  left.
  apply H0.
  intro.
  destruct H.
  right.
  apply H0.
Qed.