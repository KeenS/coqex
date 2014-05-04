Parameter G : Set.
Parameter mult : G -> G -> G.
Notation "x * y" := (mult x y).
Parameter one : G.
Notation "1" := one.
Parameter inv : G -> G.
Notation "/ x" := (inv x).

Axiom mult_assoc : forall x y z, x * (y * z) = (x * y) * z.
Axiom one_unit_l : forall x, 1 * x = x.
Axiom inv_l : forall x, /x * x = 1.

Lemma inv_r : forall x, x * / x = 1.
Proof.
  intros.
  rewrite <- (one_unit_l  x).
  rewrite <- (inv_l (/ x)).
  rewrite <- (mult_assoc (/ / x) (/ x) x).
  rewrite inv_l.
  rewrite <- (mult_assoc (/ / x) 1 (/ (/ / x * 1))).
  rewrite one_unit_l.
  rewrite inv_l.
  rewrite <- (inv_l x).
  rewrite (mult_assoc (/ / x) (/ x) x).
  rewrite inv_l.
  rewrite one_unit_l.
  rewrite inv_l.
  rewrite inv_l.
  reflexivity.
Qed.

Lemma one_unit_r : forall x, x * / x = 1.
Proof.
  intros.
  rewrite inv_r.
  reflexivity.
Qed.