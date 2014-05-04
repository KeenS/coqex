Theorem DeMorgan3 : forall P Q : Prop, ~(P \/ Q) -> ~P /\ ~Q.
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
Theorem NotNot_LEM : forall P : Prop, ~~(P \/ ~P).
Proof.
  intros.
  intro Q.
  apply DeMorgan3 in Q.
  destruct Q.
  apply H0.
  apply H.
Qed.
