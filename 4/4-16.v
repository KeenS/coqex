Definition tautology : forall P : Prop, P -> P
:= (fun (P : Prop) (H : P)=> H).

Definition Modus_tollens : forall P Q : Prop, ~Q /\ (P -> Q) -> ~P :=
  (fun (P Q : Prop) (H : ~Q /\ (P -> Q)) =>
     match H with
       | conj H0 H1 => (fun (H2 : P) => H0 (H1 H2))
     end).

Definition Diojunctive_syllogism : forall P Q : Prop, (P \/ Q) -> ~P -> Q
  :=(fun (P Q : Prop) (H0 : P \/ Q) (H1 : ~P) =>
       match H0 with
         | or_introl H2 => match H1 H2 return Q with end
         | or_intror H2 => H2
       end
    )
.

Definition tautology_on_Set : forall A : Set, A -> A
  := (fun (A : Set) (B : A) => B)
.

Definition Modus_tollens_on_Set : forall A B : Set, (B -> Empty_set) * (A -> B) -> (A -> Empty_set)
  := (fun (A B : Set) (H : (B -> Empty_set) * (A -> B)) (H0 : A) =>
        let (a, b) := H in
        a (b H0)
     )
.

Definition Diojunctive_syllogism_on_Set : forall A B : Set, (A + B) -> (A -> Empty_set) -> B
  := (fun (A B : Set) (C : A + B) (H : A -> Empty_set) =>
        match C with
          | inr b => b
          | inl a => match H a return B with
                     end
        end
     )
.
