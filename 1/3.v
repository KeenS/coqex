Theorem Disjunctive_syllogism : forall P Q : Prop, (P \/ Q) -> ~P -> Q.
Proof.
  intros.
  destruct H.
  destruct H0.
  apply H.
  apply H.
Qed
.