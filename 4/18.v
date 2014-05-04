Require Import Arith.

Definition Nat : Type :=
  forall A : Type, (A -> A) -> (A -> A).

Definition NatPlus(n m : Nat) : Nat
  := (fun (A : Type) (s : A -> A) (z : A) =>
         n A s (m A s z)).

Definition nat2Nat : nat -> Nat := nat_iter.

Definition Nat2nat(n : Nat) : nat := n _ S 0.

Lemma NatPlus_plus :
  forall n m, Nat2nat (NatPlus (nat2Nat n) (nat2Nat m)) = n + m.
Proof.
  intros.
  induction n.
  simpl.
  induction m.
  compute.
  ring.
  rewrite <- IHm at 2.
  compute.
  reflexivity.
  rewrite (plus_Sn_m n m).
  rewrite <- IHn.
  compute.
  reflexivity.
Qed.