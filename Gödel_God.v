(*Classical Logic*)
Axiom Classic : forall p, p \/ ~p.

(*Modal Logic*)
Parameter World : Type.
Definition MProp := World -> Prop.
Definition valid (P : MProp) : Prop := forall w : World, P w.
Definition m_not (P : MProp) : MProp := fun w => ~ (P w).
Definition m_impl (P Q : MProp) : MProp := fun w => P w -> Q w.
Definition m_eqiv (P Q : MProp) : MProp := fun w => (P w <-> Q w).
Definition m_and (P Q : MProp) : MProp := fun w => P w /\ Q w.
Definition m_or (P Q : MProp) : MProp := fun w => P w \/ Q w.
Definition m_all (T : Type) (P : T -> MProp) : MProp := fun w => (forall x : T, P x w).
Definition m_exi (T : Type) (P : T -> MProp) : MProp := fun w => (exists x : T, P x w).
Definition m_exi_uni (T : Type) (P : T -> MProp) : MProp := fun w => (exists! x : T, P x w).
Parameter Nessesary : MProp -> MProp.
Definition Possible (P : MProp) : MProp := m_not (Nessesary (m_not P)).
Axiom Necessitation : forall P : MProp, valid P -> valid (Nessesary P).
Axiom Axiom_K : forall P Q : MProp, valid (m_impl (Nessesary (m_impl P Q)) (m_impl (Nessesary P) (Nessesary Q))).
Axiom Axiom_T : forall P : MProp, valid (m_impl (Nessesary P) P).
Axiom Axiom_5 : forall P : MProp, valid (m_impl (Possible P) (Nessesary (Possible P))).

Lemma Lemma1 : valid (
  m_all _ (fun (P : MProp) =>
    m_all _ (fun(Q : MProp) =>
      m_impl (Nessesary (m_impl P Q)) (m_impl (Possible P) (Possible Q))
    )
  )
).
Proof.
  intros world P Q h_ness h_posP h_nnessP.
  apply h_posP.
  enough (Nessesary (m_impl (m_not Q) (m_not P)) world).
  -- apply Axiom_K in H.
     apply H.
     assumption.
  -- enough (Nessesary (m_impl (m_impl P Q) (m_impl (m_not Q) (m_not P))) world).
     ++ apply Axiom_K in H.
     apply H.
     assumption.
     ++ enough (valid (Nessesary
  (m_impl (m_impl P Q)
     (m_impl (m_not Q) (m_not P))))).
      --- apply H.
      --- apply Necessitation.
          intros w h_pq h_nq h_p.
          apply h_nq.
          apply h_pq.
          assumption.
Qed.

Lemma Lemma2 : valid (
  m_all _ (fun (P : MProp) =>
    m_eqiv (m_not (Possible P)) (Nessesary (m_not P))
  )
).
Proof.
  intros world P.
  split.
  - intro h_np.
    destruct (Classic (Nessesary (m_not P) world)).
    + assumption.
    + exfalso. apply h_np. assumption.
  - intro h_ness.
    intro h_poss.
    apply h_poss.
    assumption.
Qed.

Lemma Lemma3 : valid (
  m_all _ (fun (P : MProp) =>
    m_eqiv (m_not (Nessesary P)) (Possible (m_not P))
  )
).
Proof.
  intros world P.
  split.
  - intro h_not_ness.
    intro h_pos.
    apply h_not_ness.
    pose (h := Axiom_K (m_not (m_not P)) P).
    apply h.
    + enough (valid (Nessesary (m_impl (m_not (m_not P)) P))).
      ++ apply H.
      ++ apply Necessitation.
         intro w.
         intro h_nnp.
         destruct (Classic (P w)).
         -- assumption.
         -- exfalso. apply h_nnp. assumption.
    + assumption.
  - intros h_pos h_ness.
    apply h_pos.
    pose (h := Axiom_K P (m_not (m_not P))).
    apply h.
    + enough (valid (Nessesary (m_impl P (m_not (m_not P))))).
      ++ apply H.
      ++ apply Necessitation.
         intro w.
         intro h_P.
         intro h_nP.
         apply h_nP.
         assumption.
    + assumption.
Qed.

Lemma Lemma4 : valid (
  m_all _ (fun (P : MProp) =>
     m_impl (Possible (Nessesary P)) (Nessesary P)
  )
).
Proof.
  intros world P.
  pose (h := Axiom_5 (m_not P) world).
  intro h_pos_ness.
  pose (h2 := Lemma2 world (m_not P)).
  enough (Nessesary (m_not (m_not P)) world).
  + pose (h3 := Axiom_K (m_not (m_not P)) P world).
    apply h3.
    ++ enough (valid (Nessesary (m_impl (m_not (m_not P)) P))).
       -- apply H0.
       -- apply Necessitation.
          intro w.
          intro h_nnp.
          destruct (Classic (P w)).
          +++ assumption.
          +++ exfalso. apply h_nnp. assumption.
    ++ assumption.
  + apply h2. clear h2.
    intro h_pos.
    apply h in h_pos.
    clear h.
    apply h_pos_ness. clear h_pos_ness.
    pose (h_ax := Axiom_K (Possible (m_not P)) (m_not (Nessesary P)) world).
    apply h_ax.
    ++ enough (valid (Nessesary
  (m_impl (Possible (m_not P))
     (m_not (Nessesary P))))).
      +++ apply H.
      +++ apply Necessitation.
          intro w.
          intro h_np.
          apply Lemma3.
          assumption.
    ++ assumption.
Qed.




(*Gödel Axioms and Definitions*)
Parameter Subject : Type.
Parameter Positive : forall P : Subject -> MProp, MProp.
Definition G (x : Subject) : MProp :=
    m_all _ (fun (Phi : Subject -> MProp) => m_impl (Positive Phi) (Phi x)).
Definition esse (phi : Subject -> MProp) (x : Subject) : MProp :=
  m_and (phi x) (
    m_all _ (fun (psi : Subject -> MProp) => 
      (m_impl (psi x) (
          Nessesary (
            m_all _ (fun (y : Subject) =>
                (m_impl (phi y) (psi y)) 
              )
          )
        )
      )
    )
  ).
Definition E (x : Subject) : MProp := 
  m_all _ (fun (phi : Subject -> MProp) => m_impl (esse phi x) 
    (Nessesary (m_exi _ (fun(y : Subject) => phi y)
    ))
  ).
Axiom Axiom1 : valid (
  m_all _ (fun(phi : Subject -> MProp) =>
    m_all _ (fun (psi : Subject -> MProp) =>
      m_impl (
         m_and (Positive phi) (
            Nessesary (
              m_all _ (fun (x : Subject) => (
                m_impl (phi x) (psi x)
              ))
            )
         )
      
      ) (Positive psi)
    )
  )
).
Axiom Axiom2 :
valid (
m_all _ (fun (phi : Subject -> MProp) =>
    m_eqiv 
      (Positive (fun x => m_not (phi x))) 
      (m_not (Positive phi)
    )
  )
).
Axiom Axiom3 : valid (Positive G).
Axiom Axiom4 : valid (
  m_all _ (fun (phi : Subject -> MProp) => 
    m_impl (Positive phi) (Nessesary (Positive phi))
    
  )
).
Axiom Axiom5 : valid (Positive E).

(*Gödel lemmas and theorems*)
Theorem Theorem1 : valid (
  m_all _ (fun (phi : Subject -> MProp) => 
    m_impl(Positive phi) (Possible (
      m_exi _ (fun (y : Subject) => 
        phi y  
      )
    ))
    
  )
).
Proof.
intros world phi h_pos h_ness.
pose (psi := fun w => m_not (phi w)).
pose (h := Axiom1 world phi psi).
enough (Positive psi world).
- pose (h2 := Axiom2 world phi).
  apply h2 in H.
  apply H. assumption.
- apply h.
  split.
  + assumption.
  + pose (P := (m_not
       (m_exi Subject (fun y : Subject => phi y)))).
    pose (Q := (m_all Subject
     (fun x : Subject => m_impl (phi x) (psi x)))).
    pose (h2 := Axiom_K P Q world).
    apply h2.
    -- enough (valid (Nessesary (m_impl P Q))).
       ++ apply H.
       ++ apply Necessitation.
          intros w h_P.
          intros u hu.
          exfalso.
          apply h_P.
          exists u.
          assumption.
    -- assumption.
Qed.

Theorem Theorem2 : valid (Possible (m_exi _ G)).
Proof.
  intro world.
  apply Theorem1.
  apply Axiom3.
Qed.

Theorem Theorem3 : valid (
  m_all _ (fun (x : Subject) =>
    m_impl (G x) (esse G x)
  )
).
Proof.
  intros world x h_G.
  split.
  - assumption.
  - intros psi h_psi.
    assert (Positive psi world).
    -- destruct (Classic (Positive psi world)).
      ++ assumption.
      ++ pose (h2 := Axiom2 world psi).
          apply h2 in H.
          specialize (h_G (fun x : Subject => m_not (psi x)) H).
          exfalso. apply h_G. assumption.
    -- apply Axiom4 in H.
       revert H.
       apply Axiom_K.
       enough (
          valid (Nessesary
            (m_impl (Positive psi)
               (m_all Subject
                  (fun y : Subject => m_impl (G y) (psi y)))))
       ).
       ++ apply H.
       ++ apply Necessitation.
          intros w h_pos y h_g.
          specialize (h_g psi h_pos). 
          assumption.
Qed.

Lemma Lemma5 : valid (Possible (Nessesary (m_exi _ G))).
Proof.
  intro world.
  pose (h := Lemma1 world (m_exi _ G) (Nessesary (m_exi _ G))).
  apply h.
  - clear h.
    revert world.
    apply Necessitation.
    intros world h_exi.
    destruct h_exi as [x h_x].
    pose (h2_x := Theorem3 world x h_x).
    pose (h3_x := h_x).
    specialize ((h3_x E) (Axiom5 world)).
    specialize ((h3_x G) h2_x).
    assumption.
  - apply Theorem2.
Qed.

(*In all acessible worlds, there is Godlike entity : □ ∃ x G(x)*)
Lemma GodNesEx : valid (Nessesary (m_exi _ G)).
Proof.
  intro world.
  apply Lemma4.
  apply Lemma5.
Qed.

(*There exists entity, 
which is Godlike in all accessible worlds*)
Theorem GodNesExWorld : valid (m_exi _ (fun x => Nessesary (G x))).
Proof.
  intro world.
  pose (h := Axiom_T).
  pose (g := GodNesEx world).
  apply h in g.
  destruct g as [x h_x].
  exists x.
  pose (P t (_ : World) := (x = t)).
  assert (Positive P world).
  - destruct (Classic (Positive P world)) as [H | H].
    + assumption.
    + apply Axiom2 in H.
      pose (Q t (_ : World) := (x <> t)).
      specialize (h_x Q H).
      exfalso. apply h_x. reflexivity.
  - apply Axiom4 in H.
    clear h.
    clear h_x.
    revert H.
    apply Axiom_K.
    apply Necessitation.
    intros w h_p.
    pose (h := GodNesEx w).
    apply Axiom_T in h.
    destruct h as [y h_y].
    enough (x = y).
    + rewrite H. assumption.
    + specialize (h_y P h_p).
      unfold P in h_y.
      assumption.
Qed.

(*There exists unique entity, 
which is Godlike in all accessible worlds*)
Theorem GodNesExUnWorld : valid (m_exi_uni _ (fun x => Nessesary (G x))).
Proof.
  intro world.
  destruct (GodNesExWorld world) as [x h_x].
  exists x.
  split.
  - assumption.
  - intros y h_y.
    apply Axiom_T in h_x.
    apply Axiom_T in h_y.
    pose (P t (_ : World) := (x = t)).
    assert (Positive P world).
    + destruct (Classic (Positive P world)) as [ H | H]. 
      ++ assumption.
      ++ exfalso.
         apply Axiom2 in H.
         pose (Q t (_ : World) := (x <> t)).
         specialize (h_x Q H).
         apply h_x. reflexivity.
    + specialize (h_y P H).
      unfold P in h_y.
      assumption.
Qed.



         
      
  