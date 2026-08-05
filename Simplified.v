Axiom Classic : forall p, p \/ ~ p.
Parameter Subject : Type.
Parameter Positive : forall P : Subject -> Prop, Prop.

Definition G (x : Subject) : Prop :=
    forall (Phi : Subject -> Prop), ((Positive Phi) -> (Phi x)).

Axiom Axiom1 : forall (Phi Psi : Subject -> Prop), ((Positive Phi /\ (
  forall x, (Phi x -> Psi x)
)) -> Positive Psi).

Axiom Axiom2 : forall Phi : Subject -> Prop, 
  Positive (fun x => ~ Phi x) <-> ~ Positive Phi.
  
Axiom Axiom3 : Positive G.


Lemma GodPropPos : forall x : Subject, forall Phi : Subject -> Prop,
  G x -> (Phi x) -> Positive Phi.
Proof.
  intros x Phi hG hPhi.
  destruct (Classic (Positive Phi)).
  - assumption.
  - apply Axiom2 in H.
    pose (Psi t := ~ Phi t).
    specialize (hG Psi H).
    exfalso.
    apply hG.
    assumption.
Qed.


Theorem GodEx : exists x, G x.
Proof.
  destruct (Classic (exists x, G x)).
  - assumption.
  - exfalso.
    assert (forall x : Subject, ~G x).
    + intro x.
      intro h_G.
      apply H.
      exists x.
      assumption.
    + assert (Positive (fun x => ~ G x)).
      -- apply (Axiom1 G).
         split.
         ++ exact Axiom3.
         ++ intro x. intro h_G.
            apply H0.
      -- apply Axiom2 in H1.
         apply H1.
         exact Axiom3.
Qed.


Theorem GodExUn : exists! x, G x.
Proof.
  destruct (GodEx).
  exists x.
  unfold unique.
  split.
  assumption.
  intros y hy.
  pose (phi t := x = t).
  specialize (hy phi).
  apply hy.
  apply (GodPropPos x).
  + assumption.
  + unfold phi.
    reflexivity.
Qed.
  