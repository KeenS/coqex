Require Import Arith.

Goal forall n m p q : nat, (n + m) + (p + q) = (n + p) + (m + q).
Proof.
  intros.
  rewrite (plus_assoc (n + m) p q).
  rewrite (plus_assoc (n + p) m q).
  rewrite <- (plus_assoc n m p).
  rewrite <- (plus_assoc n p m).
  rewrite (plus_comm m p).
  reflexivity.
Qed.

Goal forall n m : nat, (n + m) * (n + m) = n * n + m * m + 2 * n * m.
Proof.
  intros.
  rewrite (mult_plus_distr_r n m (n + m)).
  rewrite (mult_plus_distr_l n n m).
  rewrite (mult_plus_distr_l m n m).
  rewrite (plus_assoc (n * n + n * m) (m * n) (m * m)).
  rewrite <- (mult_1_r (n * m)).
  rewrite (mult_comm m n).
  rewrite <- (plus_assoc (n * n) (n * m * 1) (n * m)).
  rewrite (mult_n_Sm (n * m) 1).
  rewrite (mult_comm (n * m) 2).
  rewrite (mult_assoc 2 n m).
  rewrite <- (plus_assoc (n * n) (2 * n * m) (m * m)).
  rewrite (plus_comm (2 * n * m) (m * m)).
  rewrite (plus_assoc (n * n) (m * m) (2 * n * m)).
  reflexivity.
Qed.