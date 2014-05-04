Require Import Arith.

Fixpoint sum_odd(n:nat) : nat :=
  match n with
    | 0 => 0
    | S m => 1 + m + m + sum_odd m
  end.

Goal forall n, sum_odd n = n * n.
Proof.
  intros.
  induction n.
  simpl.
  ring.
  simpl.
  rewrite <- (eq_S (n + n + sum_odd n) (n + n * S n)).
  ring.
  rewrite IHn.
  ring.
Qed.
             