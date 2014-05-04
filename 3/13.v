Inductive pos : Set :=
| S1 : pos
| S : pos -> pos.

Fixpoint plus(n m:pos) : pos :=
  match n with
    | S1 => S m
    | S l => S (plus l  m)
  end.

Infix "+" := plus.

Lemma succ_equal : forall n m : pos, (n = m) -> (S n = S m).
Proof.
  intros.
  induction n.
  rewrite <- H.
  auto.
  rewrite H.
  auto.
Qed.

Theorem plus_assoc : forall n m p, n + (m + p) = (n + m) + p.
Proof.
  intros.
  induction n.
  simpl.
  auto.
  simpl.
  apply succ_equal.
  auto.
Qed.