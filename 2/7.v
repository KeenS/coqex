Goal forall P Q : nat -> Prop, P 0 -> (forall x , P x -> Q x) -> Q 0.
Proof.
  intros.
  apply H0.
  apply H.
Qed.

Goal forall P : nat -> Prop, P 2 -> (exists y, P (1 + y)).
Proof.
  intros.
  exists 1.
  apply H.
Qed.

Goal forall P : nat -> Prop, (forall n m, P n -> P m) -> (exists p, P p) -> forall q, P q.
Proof.
  intros.
  destruct H0.
  apply (H x q).
  apply H0.
Qed.