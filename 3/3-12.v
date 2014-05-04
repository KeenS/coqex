Require Import Lists.List.

Fixpoint sum (xs: list nat) : nat :=
  match xs with
    | nil => 0
    | x :: xs => x + sum xs
  end.

Theorem Pigeon_Hole_Principle :
  forall (xs : list nat), length xs < sum xs -> (exists x, 1 < x /\ In x xs).
Proof.
  intros.
  induction (xs).
  inversion H.
  