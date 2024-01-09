Require Import Base.
Require Import Coq.Sets.Ensembles.

Inductive prove_Hi (Г :Ensemble Formula) :Formula -> Prop :=
|Hi0 : forall a, a ∈ Г -> prove_Hi Г a
|Hi1 : forall a, prove_Hi Г ((a ∨ a) → a) 
|Hi2 : forall a b, prove_Hi Г (a → (a ∨ b))
|Hi3 : forall a b, prove_Hi Г ((a ∨ b) → (b ∨ a))
|Hi4 : forall a b r, prove_Hi Г ((b → r) → ((a ∨ b) → (a ∨ r)))
|MP : forall a b, prove_Hi Г (a → b) -> prove_Hi Г a -> prove_Hi Г b.
Notation "Г ├Hi a" := (prove_Hi Г a) (at level 80).
Notation " ├Hi a" := (prove_Hi Φ a)(at level 80).

Lemma HiUnion_l: forall Г a, Г ├Hi a -> forall A, Г ∪ A ├Hi a.
Proof.
  intros. induction H. 
  - pose proof (Union_introl _ Г A a).
    pose proof (Hi0 (Г ∪ A) a). apply H1, H0, H.
  - pose proof (Hi1 (Г ∪ A) a). apply H.
  - pose proof (Hi2 (Г ∪ A) a). apply H.
  - pose proof (Hi3 (Г ∪ A) a). apply H.
  - pose proof (Hi4 (Г ∪ A) a). apply H.
  - pose proof (MP (Г ∪ A) a). apply H1. 
    apply IHprove_Hi1. apply IHprove_Hi2.
Qed.
Lemma HiUnion_r: forall Г a, Г ├Hi a -> forall A, A ∪ Г ├Hi a.
Proof.
  intros. induction H. 
  - pose proof (Union_intror _ A Г a).
    pose proof (Hi0 (A ∪ Г) a). apply H1, H0, H.
  - pose proof (Hi1 (A ∪ Г) a). apply H.
  - pose proof (Hi2 (A ∪ Г) a). apply H.
  - pose proof (Hi3 (A ∪ Г) a). apply H.
  - pose proof (Hi4 (A ∪ Г) a). apply H.
  - pose proof (MP (A ∪ Г) a). apply H1. 
    apply IHprove_Hi1. apply IHprove_Hi2.
Qed.

(*----------------------Theorem----------------------*)
(*PC 三段论原则*)
Theorem PT1: forall Γ a b r, Γ ├Hi (b → r) → (a → b) → (a → r).
Proof.
  intros. pose proof (Hi4 Γ ﹁a b r). apply H.
Qed.

(*同一原则*)
Theorem PT2: forall Γ a, Γ ├Hi a → a.
Proof.
  intros. pose proof (PT1 Γ a (a ∨ a) a). pose proof (Hi1 Γ a). 
  pose proof (Hi2 Γ a a). pose proof (MP Γ _ _ H H0).
  pose proof (MP Γ _ _ H2 H1). apply H3.
Qed.

(* 3 4 排中律*)
Theorem PT3: forall Γ a, Γ ├Hi ﹁a ∨ a.
Proof.
  intros. apply PT2.
Qed.

Theorem PT4: forall Γ a, Γ ├Hi a ∨ ﹁a.
Proof.
  intros. pose proof (Hi3 Γ ﹁a a). 
  pose proof (PT3 Γ). specialize H0 with a. 
  pose proof (MP Γ _ _ H H0). apply H1.
Qed.

(*双重否定原则*)
Theorem PT5: forall Γ a, Γ ├Hi a → ﹁﹁a.
Proof.
  intros. pose proof (PT4 Γ ﹁a). apply H.
Qed.

(*5的逆*)
Theorem PT6:forall Γ a, Γ ├Hi ﹁﹁a → a.
Proof.
  intros. pose proof(PT5 Γ ﹁a). pose proof(Hi4 Γ a ﹁a ﹁﹁﹁a).
  pose proof(MP Γ _ _ H0 H). pose proof (PT4 Γ a). 
  pose proof(MP Γ _ _ H1 H2). pose proof (Hi3 Γ a ﹁﹁﹁a).
  pose proof(MP Γ _ _ H4 H3). apply H5.
Qed.

(*假言易位原则*)
Theorem PT7: forall Γ a b, Γ ├Hi (a → b) → (﹁b → ﹁a).
Proof.
  intros. pose proof(PT5 Γ b). pose proof(Hi4 Γ ﹁a b ﹁﹁b).
  pose proof(MP Γ _ _ H0 H). pose proof(Hi3 Γ ﹁a ﹁﹁b).
  pose proof(PT1 Γ (﹁a ∨ b)  (﹁a ∨ ﹁﹁b) (﹁﹁b ∨ ﹁a)).
  pose proof (MP Γ _ _ H3 H2). pose proof(MP Γ _ _ H4 H1). apply H5.
Qed.

(*8 9 合取否定的德 摩根律*)
Theorem PT8: forall Γ a b, Γ ├Hi ﹁(a ∧ b) → ﹁a ∨ ﹁b.
Proof.
  intros. apply PT6 with (a :=(﹁a ∨ ﹁b)).
 (* pose proof(PT6 (﹁a ∨ ﹁b)). apply H.*)
Qed.

Theorem PT9: forall Γ a b, Γ├Hi ﹁a ∨ ﹁b → ﹁(a ∧ b).
Proof.
  intros. apply PT5 with (a :=(﹁a ∨ ﹁b)).
Qed.

(*析取的左附加原则*)
Theorem PT10: forall Γ a b, Γ ├Hi a → b ∨ a.
Proof.
  intros. pose proof(Hi2 Γ a b). pose proof(Hi3 Γ a b).
  pose proof(PT1 Γ a (a ∨ b) (b ∨ a)).
  pose proof(MP Γ _ _ H1 H0). pose proof(MP Γ _ _ H2 H). apply H3.
Qed.

(*德 摩根律 (析取的否定式 的 德摩根定律)*)
Theorem PT11: forall Γ a b, Γ ├Hi ﹁ (a ∨ b) → ﹁a ∧ ﹁b.
Proof.
  intros. pose proof (PT6 Γ b) as H1. pose proof (Hi4 Γ (﹁﹁a) (﹁﹁b) b) as H2.
  pose proof (MP Γ _ _ H2 H1) as H3. pose proof (PT6 Γ a) as H4.
  pose proof (Hi4 Γ b (﹁﹁a) a) as H5. pose proof (MP Γ _ _ H5 H4) as H6.
  pose proof (Hi3 Γ (﹁﹁a) b) as H7. 
  pose proof (PT1 Γ (﹁﹁a ∨ b) (b ∨ ﹁﹁a) (b ∨ a)) as H8.
  pose proof (MP Γ _ _  H8 H6) as H9. pose proof (MP Γ _ _ H9 H7) as H10.
  pose proof (Hi3 Γ b a) as H11. 
  pose proof (PT1 Γ (﹁﹁a ∨ b) (b ∨ a) (a ∨ b)) as H12.
  pose proof (MP Γ _ _ H12 H11) as H13. pose proof (MP Γ _ _ H13 H10) as H14.
  pose proof (PT1 Γ (﹁﹁a ∨ ﹁﹁b) (﹁﹁a ∨ b) (a ∨ b)) as H15.
  pose proof (MP Γ _ _ H15 H14) as H16. pose proof (MP Γ _ _ H16 H3) as H17. 
  pose proof (PT7 Γ (﹁﹁a ∨ ﹁﹁b) (a ∨ b)) as H18.
  pose proof (MP Γ _ _ H18 H17). apply H.
Qed.

Theorem PT12: forall Γ a b, Γ ├Hi ﹁a ∧ ﹁b → ﹁ (a ∨ b).
Proof.
  intros. pose proof (PT5 Γ b) as H1. pose proof (Hi4 Γ (﹁﹁a) b (﹁﹁b)) as H2.
  pose proof (MP Γ _ _ H2 H1) as H3. pose proof (PT5 Γ a) as H4.
  pose proof (Hi4 Γ b a (﹁﹁a)) as H5. pose proof (MP Γ _ _ H5 H4) as H6.
  pose proof (PT1 Γ (a ∨ b) (b ∨ a) (b ∨ ﹁﹁a)) as H7.
  pose proof (MP Γ _ _ H7 H6) as H8. pose proof (Hi3 Γ a b) as H9.
  pose proof (MP Γ _ _ H8 H9) as H10.
  pose proof (Hi3 Γ b (﹁﹁a)) as H11. 
  pose proof (PT1 Γ (a ∨ b) (b ∨ ﹁﹁a) (﹁﹁a ∨ b)) as H12.
  pose proof (MP Γ _ _ H12 H11) as H13. pose proof (MP Γ _ _ H13 H10) as H14.
  pose proof (PT1 Γ (a ∨ b) (﹁﹁a ∨ b) (﹁﹁a ∨ ﹁﹁b)) as H15.
  pose proof (MP Γ _ _ H15 H3) as H16. pose proof (MP Γ _ _ H16 H14) as H17.
  pose proof (PT7 Γ (a ∨ b) (﹁﹁a ∨ ﹁﹁b)) as H18. 
  pose proof (MP Γ _ _ H18 H17). apply H.
Qed.

(*合取∧的交换律*)
Theorem PT13: forall Γ a b, Γ ├Hi a ∧ b → b ∧ a.
Proof.
  intros. pose proof (Hi3 Γ ﹁b ﹁a) as H1. 
  pose proof (PT7 Γ (﹁b ∨ ﹁a) (﹁a ∨ ﹁b)) as H2.
  pose proof (MP Γ  _ _ H2 H1). apply H.
Qed.

(*合取的分析式*)
Theorem PT14: forall Γ a b, Γ ├Hi a ∧ b → a.
Proof.
  intros. pose proof (PT9 Γ a b) as H1.
  pose proof (Hi2 Γ ﹁a ﹁b) as H2. 
  pose proof (PT1 Γ ﹁a (﹁a ∨ ﹁b) ﹁(a ∧ b)) as H3.
  pose proof (MP Γ _ _ H3 H1) as H4. pose proof (MP Γ _ _ H4 H2) as H5.
  pose proof (PT7 Γ (﹁a) (﹁(a ∧ b))) as H6.
  pose proof (MP Γ _ _ H6 H5) as H7. pose proof (PT5 Γ (a ∧ b)) as H8.
  pose proof (PT1 Γ (a ∧ b) (﹁﹁(a ∧ b)) (﹁﹁a)) as H9.
  pose proof (MP Γ _ _ H9 H7) as H10. pose proof (MP Γ _ _ H10 H8) as H11.
  pose proof (PT6 Γ a) as H12. pose proof (PT1 Γ (a ∧ b) ﹁﹁a a) as H13.
  pose proof (MP Γ _ _ H13 H12) as H14. 
  pose proof (MP Γ _ _ H14 H11) as H15. apply H15.
Qed.
 
Theorem PT15: forall Γ a b, Γ ├Hi a ∧ b → b.
Proof.
  intros. pose proof (PT14 Γ b a) as H1. pose proof (PT13 Γ a b) as H2.
  pose proof (PT1 Γ (a ∧ b) (b ∧ a) b) as H3.
  pose proof (MP Γ _ _ H3 H1) as H4. pose proof (MP Γ _ _ H4 H2). apply H.
Qed.

(*析取 ∨ 的结合律*)
Theorem PT16: forall Γ a b r, Γ ├Hi a ∨ (b ∨ r) → b ∨ (a ∨ r).
Proof.
  intros. pose proof (PT10 Γ r a) as H1. pose proof (Hi4 Γ b r (a ∨ r)) as H2.
  pose proof (MP Γ _ _ H2 H1) as H3. pose proof (Hi4 Γ a (b ∨ r) (b ∨ a ∨ r)) as H4.
  pose proof (MP Γ  _ _ H4 H3) as H5. pose proof (Hi3 Γ a (b ∨ a ∨ r)) as H6.
  pose proof (PT1 Γ (a ∨ b ∨ r) (a ∨ b ∨ a ∨ r) ((b ∨ a ∨ r) ∨ a)) as H7.
  pose proof (MP Γ _ _ H7 H6) as H8. pose proof (MP Γ _ _ H8 H5) as H9.
  pose proof (PT10 Γ (a ∨ r) b) as H10. pose proof (Hi2 Γ a r) as H11.
  pose proof (PT1 Γ a (a ∨ r) (b ∨ a ∨ r)) as H12. 
  pose proof (MP Γ _ _ H12 H10) as H13. pose proof (MP Γ _ _ H13 H11) as H14.
  pose proof (Hi4 Γ (b ∨ a ∨ r) a (b ∨ a ∨ r)) as H15. 
  pose proof (MP Γ _ _ H15 H14) as H16. pose proof (Hi1 Γ (b ∨ a ∨ r)) as H17.
  pose proof (PT1 Γ ((b ∨ a ∨ r) ∨ a) ((b ∨ a ∨ r) ∨ b ∨ a ∨ r) (b ∨ a ∨ r)) as H18.
  pose proof (MP Γ _ _  H18 H17) as H19. pose proof (MP Γ _ _ H19 H16) as H20.
  pose proof (PT1 Γ (a ∨ b ∨ r) ((b ∨ a ∨ r) ∨ a) (b ∨ a ∨ r)) as H21.
  pose proof (MP Γ _ _ H21 H20) as H22. pose proof (MP Γ _ _ H22 H9). apply H.
Qed.

Theorem PT17: forall Γ a b r, Γ ├Hi a ∨ (b ∨ r) → (a ∨ b) ∨ r.
Proof.
  intros. pose proof (PT16 Γ a r b) as H1. pose proof (Hi3 Γ b r) as H2.
  pose proof (Hi4 Γ a (b ∨ r) (r ∨ b)) as H3. pose proof (MP Γ _ _ H3 H2) as H4.
  pose proof (PT1 Γ (a ∨ b ∨ r) (a ∨ r ∨ b) (r ∨ a ∨ b)) as H5.
  pose proof (MP Γ _ _ H5 H1) as H6. pose proof (MP Γ _ _ H6 H4) as H7.
  pose proof (Hi3 Γ r (a ∨ b)) as H8.
  pose proof (PT1 Γ (a ∨ b ∨ r) (r ∨ a ∨ b) ((a ∨ b) ∨ r)) as H9.
  pose proof (MP Γ _ _ H9 H8) as H10. pose proof (MP Γ _ _ H10 H7). apply H.
Qed.

Theorem PT18: forall Γ a b r, Γ ├Hi (a ∨ b) ∨ r → a ∨ (b ∨ r).
Proof.
  intros. pose proof (PT17 Γ r b a) as H1. pose proof (Hi3 Γ a b) as H2.
  pose proof (Hi4 Γ r (a ∨ b) (b ∨ a)) as H3. pose proof (MP Γ _ _ H3 H2) as H4.
  pose proof (PT1 Γ (r ∨ a ∨ b) (r ∨ b ∨ a) ((r ∨ b) ∨ a)) as H5. 
  pose proof (MP Γ _ _ H5 H1) as H6. pose proof (MP Γ _ _ H6 H4) as H7.
  pose proof (Hi3 Γ r b) as H8. pose proof (Hi4 Γ a (r ∨ b) (b ∨ r)) as H9.
  pose proof (MP Γ _ _ H9 H8) as H10. pose proof (Hi3 Γ (r ∨ b) a) as H11.
  pose proof (PT1 Γ ((r ∨ b) ∨ a) (a ∨ r ∨ b) (a ∨ b ∨ r)) as H12.  
  pose proof (MP Γ _ _ H12 H10) as H13. pose proof (MP Γ _ _ H13 H11) as H14.
  pose proof (Hi3 Γ a (b ∨ r)) as H15. 
  pose proof (PT1 Γ ((r ∨ b) ∨ a) (a ∨ b ∨ r) ((b ∨ r) ∨ a)) as H16.
  pose proof (MP Γ _ _ H16 H15) as H17. pose proof (MP Γ _ _ H17 H14) as H18.
  pose proof (PT1 Γ (r ∨ a ∨ b) ((r ∨ b) ∨ a) ((b ∨ r) ∨ a)) as H19. 
  pose proof (MP Γ _ _ H19 H18) as H20. pose proof (MP Γ _ _ H20 H7) as H21.
  pose proof (Hi3 Γ (a ∨ b) r) as H22. pose proof (Hi3 Γ (b ∨ r) a) as H23.
  pose proof (PT1 Γ ((a ∨ b) ∨ r) (r ∨ a ∨ b) ((b ∨ r) ∨ a)) as H24.
  pose proof (MP Γ _ _ H24 H21) as H25. pose proof (MP Γ _ _ H25 H22) as H26. 
  pose proof (PT1 Γ ((a ∨ b) ∨ r) ((b ∨ r) ∨ a) (a ∨ b ∨ r)) as H27.
  pose proof (MP Γ _ _ H27 H23) as H28. pose proof (MP Γ _ _ H28 H26). apply H.
Qed.

(*合取∧的结合律*)
Theorem PT19: forall Γ a b r, Γ ├Hi a ∧ (b ∧ r) → (a ∧ b) ∧ r.
Proof.
  intros. pose proof (PT18 Γ ﹁a ﹁b ﹁r) as H1. 
  pose proof (PT7 Γ ((a → ﹁ b) ∨ ﹁ r) (a → b → ﹁ r)) as H2.
  pose proof (MP Γ _ _ H2 H1) as H3. pose proof (PT12 Γ ﹁a (﹁b ∨ ﹁r)) as H4.
  pose proof (PT1 Γ (﹁ ﹁ a ∧ ﹁(﹁b ∨ ﹁r)) (﹁ (﹁a ∨ (﹁b ∨ ﹁ r))) (﹁ ((﹁a ∨ ﹁b) ∨ ﹁ r))) as H5.
  pose proof (MP Γ _ _ H5 H3) as H6. pose proof (MP Γ _ _ H6 H4) as H7.
  pose proof (PT11 Γ (﹁a ∨ ﹁b) ﹁ r) as H8.
  pose proof (PT1 Γ (﹁ ﹁ a ∧ ﹁(﹁b ∨ ﹁r)) (﹁ ((﹁a ∨ ﹁b) ∨ ﹁ r)) (﹁ (﹁a ∨ ﹁b) ∧ ﹁﹁ r)) as H9.
  pose proof (MP Γ _ _ H9 H8) as H10. pose proof (MP Γ _ _ H10 H7) as H11.
  pose proof (PT7 Γ (﹁ (﹁﹁﹁a ∨ ﹁(b ∧ r))) (﹁ (﹁(a ∧ b) ∨ ﹁﹁﹁r))) as H12.
  pose proof (MP Γ _ _ H12 H11) as H13. pose proof (PT5 Γ (﹁(a ∧ b) ∨ ﹁﹁﹁r)) as H14.
  pose proof (PT1 Γ (﹁(a ∧ b) ∨ ﹁﹁﹁r) (﹁﹁(﹁(a ∧ b) ∨ ﹁﹁﹁r)) (﹁﹁(﹁﹁﹁a ∨ ﹁(b ∧ r)))) as H15.
  pose proof (MP Γ _ _ H15 H13) as H16. pose proof (MP Γ _ _ H16 H14) as H17.
  pose proof (PT6 Γ (﹁﹁﹁a ∨ ﹁(b ∧ r))) as H18.
  pose proof (PT1 Γ (﹁(a ∧ b) ∨ ﹁﹁﹁r) (﹁﹁(﹁﹁﹁a ∨ ﹁(b ∧ r))) (﹁﹁﹁a ∨ ﹁(b ∧ r))) as H19.
  pose proof (MP Γ _ _ H19 H18) as H20. pose proof (MP Γ _ _ H20 H17) as H21.
  pose proof (PT5 Γ ﹁r) as H22. pose proof (Hi4 Γ (﹁(a ∧ b)) ﹁r ﹁﹁﹁r) as H23.
  pose proof (MP Γ _ _ H23 H22) as H24.
  pose proof (PT1 Γ (﹁(a ∧ b) ∨ ﹁r) (﹁(a ∧ b) ∨ ﹁﹁﹁r) (﹁﹁﹁a ∨ ﹁(b ∧ r))) as H25.
  pose proof (MP Γ _ _ H25 H21) as H26. pose proof (MP Γ _ _ H26 H24) as H27.
  pose proof (PT6 Γ ﹁a) as H28. pose proof (Hi4 Γ (﹁(b ∧ r)) ﹁﹁﹁a ﹁a) as H29.
  pose proof (MP Γ _ _ H29 H28) as H30. pose proof (Hi3 Γ ﹁﹁﹁a (﹁(b ∧ r))) as H31.
  pose proof (PT1 Γ (﹁﹁﹁a ∨ ﹁(b ∧ r)) (﹁(b ∧ r) ∨ ﹁﹁﹁a) (﹁(b ∧ r) ∨ ﹁a)) as H32.
  pose proof (MP Γ _ _ H32 H30) as H33. pose proof (MP Γ _ _ H33 H31) as H34.
  pose proof (Hi3 Γ ﹁(b ∧ r) ﹁a) as H35.
  pose proof (PT1 Γ (﹁﹁﹁a ∨ ﹁(b ∧ r)) (﹁(b ∧ r) ∨ ﹁a) (﹁a ∨ ﹁(b ∧ r))) as H36.
  pose proof (MP Γ _ _ H36 H35) as H37. pose proof (MP Γ _ _ H37 H34) as H38.
  pose proof (PT1 Γ (﹁(a ∧ b) ∨ ﹁r) (﹁﹁﹁a ∨ ﹁(b ∧ r)) (﹁a ∨ ﹁(b ∧ r))) as H39.
  pose proof (MP Γ _ _ H39 H38) as H40. pose proof (MP Γ _ _ H40 H27) as H41.
  pose proof (PT7 Γ (﹁(a ∧ b) ∨ ﹁r) (﹁a ∨ ﹁(b ∧ r))) as H42.
  pose proof (MP Γ _ _ H42 H41). apply H.
Qed. 

Theorem PT20: forall Γ a b r, Γ ├Hi (a ∧ b) ∧ r → a ∧ (b ∧ r).
Proof.
  intros. pose proof (PT17 Γ ﹁a ﹁b ﹁r) as H1.
  pose proof (PT7 Γ (﹁a ∨ (﹁b ∨ ﹁r)) ((﹁a ∨ ﹁b) ∨ ﹁r)) as H2.
  pose proof (MP Γ _ _ H2 H1) as H3. pose proof (PT12 Γ (﹁a ∨ ﹁b) ﹁r) as H4.
  pose proof (PT1 Γ (﹁(﹁a ∨ ﹁b) ∧ ﹁﹁r) (﹁((﹁a ∨ ﹁b) ∨ ﹁r)) (﹁(﹁a ∨ (﹁b ∨ ﹁r)))) as H5.
  pose proof (MP Γ _ _ H5 H3) as H6. pose proof (MP Γ _ _ H6 H4) as H7.
  pose proof (PT11 Γ ﹁a (﹁b ∨ ﹁r)) as H8.
  pose proof (PT1 Γ (﹁(﹁a ∨ ﹁b) ∧ ﹁﹁r) (﹁(﹁a ∨ (﹁b ∨ ﹁r))) (﹁﹁a ∧ ﹁(﹁b ∨ ﹁r))) as H9.
  pose proof (MP Γ _ _ H9 H8) as H10. pose proof (MP Γ _ _ H10 H7) as H11.
  pose proof (PT7 Γ (﹁(﹁(a ∧ b) ∨ ﹁﹁﹁r)) (﹁(﹁﹁﹁a ∨ ﹁(b ∧ r)))) as H12. 
  pose proof (MP Γ _ _ H12 H11) as H13. pose proof (PT5 Γ (﹁﹁﹁a ∨ ﹁(b ∧ r))) as H14.
  pose proof (PT1 Γ (﹁﹁﹁a ∨ ﹁(b ∧ r)) (﹁﹁(﹁﹁﹁a ∨ ﹁(b ∧ r))) (﹁﹁(﹁(a ∧ b) ∨ ﹁﹁﹁r))) as H15.
  pose proof (MP Γ _ _ H15 H13) as H16. pose proof (MP Γ _ _ H16 H14) as H17.
  pose proof (PT6 Γ (﹁(a ∧ b) ∨ ﹁﹁﹁r)) as H18.
  pose proof (PT1 Γ (﹁﹁﹁a ∨ ﹁(b ∧ r)) (﹁﹁(﹁(a ∧ b) ∨ ﹁﹁﹁r)) (﹁(a ∧ b) ∨ ﹁﹁﹁r)) as H19.
  pose proof (MP Γ _ _ H19 H18) as H20. pose proof (MP Γ _ _ H20 H17) as H21.
  pose proof (PT6 Γ ﹁r) as H22. pose proof (Hi4 Γ ﹁(a ∧ b) ﹁﹁﹁r ﹁r) as H23.
  pose proof (MP Γ _ _ H23 H22) as H24.
  pose proof (PT1 Γ (﹁﹁﹁a ∨ ﹁(b ∧ r)) (﹁(a ∧ b) ∨ ﹁﹁﹁r) (﹁(a ∧ b) ∨ ﹁r)) as H25.
  pose proof (MP Γ _ _ H25 H24) as H26. pose proof (MP Γ _ _ H26 H21) as H27.
  pose proof (PT5 Γ ﹁a) as H28. pose proof (Hi4 Γ ﹁(b ∧ r) ﹁a ﹁﹁﹁a) as H29.
  pose proof (MP Γ _ _ H29 H28) as H30. pose proof (Hi3 Γ ﹁a ﹁(b ∧ r)) as H31.
  pose proof (PT1 Γ (﹁a ∨ ﹁(b ∧ r)) (﹁(b ∧ r) ∨ ﹁a) (﹁(b ∧ r) ∨ ﹁﹁﹁a)) as H32.
  pose proof (MP Γ _ _ H32 H30) as H33. pose proof (MP Γ _ _ H33 H31) as H34.
  pose proof (Hi3 Γ ﹁(b ∧ r) ﹁﹁﹁a) as H35.
  pose proof (PT1 Γ (﹁a ∨ ﹁(b ∧ r)) (﹁(b ∧ r) ∨ ﹁﹁﹁a) (﹁﹁﹁a ∨ ﹁(b ∧ r))) as H36.
  pose proof (MP Γ _ _ H36 H35) as H37. pose proof (MP Γ _ _ H37 H34) as H38.
  pose proof (PT1 Γ (﹁a ∨ ﹁(b ∧ r)) (﹁﹁﹁a ∨ ﹁(b ∧ r)) (﹁(a ∧ b) ∨ ﹁r)) as H39.
  pose proof (MP Γ _ _ H39 H27) as H40. pose proof (MP Γ _ _ H40 H38) as H41.
  pose proof (PT7 Γ (﹁a ∨ ﹁(b ∧ r)) (﹁(a ∧ b) ∨ ﹁r)) as H42. 
  pose proof (MP Γ _ _ H42 H41). apply H.
Qed.

(*合取构成原则--等值构成规则*)
Theorem PT21: forall Γ a b, Γ ├Hi a → (b → a ∧ b).
Proof.
  intros. pose proof (PT4 Γ (﹁a ∨ ﹁b)) as H1.
  pose proof (PT18 Γ ﹁a ﹁b (a ∧ b)) as H2.
  pose proof (MP Γ _ _ H2 H1). apply H.
Qed.

(*条件互易原则*)
Theorem PT22: forall Γ a b r, Γ ├Hi (a → (b → r)) → (b → (a → r)).
Proof.
  intros. pose proof (PT16 Γ ﹁a ﹁b r). apply H.
Qed.

(*条件合取原则*)
Theorem PT23: forall Γ a b r, Γ ├Hi (a → (b → r)) → ((a ∧ b)→ r).
Proof.
  intros. pose proof (PT17 Γ ﹁a ﹁b r) as H1.
  pose proof (PT5 Γ (﹁a ∨ ﹁b)) as H2. pose proof (Hi4 Γ r (﹁a ∨ ﹁b) ﹁﹁(﹁a ∨ ﹁b)) as H3.
  pose proof (MP Γ _ _ H3 H2) as H4. pose proof (Hi3 Γ (﹁a ∨ ﹁b) r) as H5.
  pose proof (PT1 Γ ((﹁a ∨ ﹁b) ∨ r) (r ∨ (﹁a ∨ ﹁b)) (r ∨ ﹁﹁(﹁a ∨ ﹁b))) as H6.
  pose proof (MP Γ _ _ H6 H4) as H7. pose proof (MP Γ _ _ H7 H5) as H8.
  pose proof (Hi3 Γ r (﹁﹁(﹁a ∨ ﹁b))) as H9.
  pose proof (PT1 Γ ((﹁a ∨ ﹁b) ∨ r) (r ∨ ﹁﹁(﹁a ∨ ﹁b)) (﹁﹁(﹁a ∨ ﹁b) ∨ r)) as H10.
  pose proof (MP Γ _ _ H10 H9) as H11. pose proof (MP Γ _ _ H11 H8) as H12.
  pose proof (PT1 Γ (﹁a ∨ (﹁b ∨ r)) ((﹁a ∨ ﹁b) ∨ r) (﹁﹁(﹁a ∨ ﹁b) ∨ r)) as H13.
  pose proof (MP Γ _ _ H13 H12) as H14. pose proof (MP Γ _ _ H14 H1). apply H.
Qed.

(*23逆 条件合取逆原则*)
Theorem PT24: forall Γ a b r, Γ ├Hi ((a ∧ b)→ r) → (a → (b → r)).
Proof.
  intros. pose proof (PT18 Γ ﹁a ﹁b r) as H1.
  pose proof (PT6 Γ (﹁a ∨ ﹁b)) as H2. pose proof (Hi4 Γ r ﹁﹁(﹁a ∨ ﹁b) (﹁a ∨ ﹁b)) as H3.
  pose proof (MP Γ _ _ H3 H2) as H4. pose proof (Hi3 Γ ﹁﹁(﹁a ∨ ﹁b) r) as H5.
  pose proof (PT1 Γ (﹁﹁(﹁a ∨ ﹁b) ∨ r) (r ∨ ﹁﹁(﹁a ∨ ﹁b)) (r ∨ (﹁a ∨ ﹁b))) as H6.
  pose proof (MP Γ _ _ H6 H4) as H7. pose proof (MP Γ _ _ H7 H5) as H8.
  pose proof (Hi3 Γ r (﹁a ∨ ﹁b)) as H9.
  pose proof (PT1 Γ (﹁﹁(﹁a ∨ ﹁b) ∨ r) (r ∨ (﹁a ∨ ﹁b)) ((﹁a ∨ ﹁b) ∨ r)) as H10.
  pose proof (MP Γ _ _ H10 H9) as H11. pose proof (MP Γ _ _ H11 H8) as H12.
  pose proof (PT1 Γ  (﹁﹁(﹁a ∨ ﹁b) ∨ r) ((﹁a ∨ ﹁b) ∨ r) (﹁a ∨ (﹁b ∨ r))) as H13.
  pose proof (MP Γ _ _ H13 H1) as H14. pose proof (MP Γ _ _ H14 H12). apply H.
Qed.

(*条件融合原则*)
Theorem PT25: forall Γ a b, Γ ├Hi (a →(a → b)) → (a → b).
Proof.
  intros. pose proof (Hi1 Γ ﹁a) as H1. pose proof (Hi4 Γ b (﹁a ∨ ﹁a) ﹁a) as H2.
  pose proof (MP Γ _ _ H2 H1) as H3. pose proof (Hi3 Γ b ﹁a) as H4.
  pose proof (PT1 Γ (b ∨ ﹁a ∨ ﹁a) (b ∨ ﹁a) (﹁a ∨ b)) as H5.
  pose proof (MP Γ _ _ H5 H4) as H6. pose proof (MP Γ _ _ H6 H3) as H7.
  pose proof (Hi3 Γ (﹁a ∨ ﹁a) b) as H8.
  pose proof (PT1 Γ ((﹁a ∨ ﹁a) ∨ b) (b ∨ (﹁a ∨ ﹁a)) (﹁a ∨ b)) as H9.
  pose proof (MP Γ _ _ H9 H7) as H10. pose proof (MP Γ _ _ H10 H8) as H11.
  pose proof (PT17 Γ ﹁a ﹁a b) as H12.
  pose proof (PT1 Γ (﹁a ∨ (﹁a ∨ b)) ((﹁a ∨ ﹁a) ∨ b) (﹁a ∨ b)) as H13.
  pose proof (MP Γ _ _ H13 H11) as H14. pose proof (MP Γ _ _ H14 H12). apply H.
Qed.

(*25逆 条件融合逆原则*)
Theorem PT26: forall Γ a b, Γ ├Hi (a → b) → (a →(a → b)).
Proof.
  intros. pose proof (Hi2 Γ ﹁a ﹁a) as H1. pose proof (Hi4 Γ b ﹁a (﹁a ∨ ﹁a)) as H2.
  pose proof (MP Γ _ _ H2 H1) as H3. pose proof (Hi3 Γ ﹁a b) as H4.
  pose proof (PT1 Γ (﹁a ∨ b) (b ∨ ﹁a) (b ∨ ﹁a ∨ ﹁a)) as H5.
  pose proof (MP Γ _ _ H5 H3) as H6. pose proof (MP Γ _ _ H6 H4) as H7.
  pose proof (Hi3 Γ b (﹁a ∨ ﹁a)) as H8.
  pose proof (PT1 Γ (﹁a ∨ b) (b ∨ (﹁a ∨ ﹁a)) ((﹁a ∨ ﹁a) ∨ b)) as H9.
  pose proof (MP Γ _ _ H9 H8) as H10. pose proof (MP Γ _ _ H10 H7) as H11.
  pose proof (PT18 Γ ﹁a ﹁a b) as H12.
  pose proof (PT1 Γ (﹁a ∨ b) ((﹁a ∨ ﹁a) ∨ b) (﹁a ∨ (﹁a ∨ b))) as H13.
  pose proof (MP Γ _ _ H13 H12) as H14. pose proof (MP Γ _ _ H14 H11). apply H.
Qed.

(*27-30 分配律*)
Theorem PT27: forall Γ a b r, Γ ├Hi (a ∨ (b ∧ r)) → ((a ∨ b) ∧ (a ∨ r)).
Proof.
  intros. pose proof (PT14 Γ b r) as H1. pose proof (Hi4 Γ a (b ∧ r) b) as H2.
  pose proof (MP Γ _ _ H2 H1) as H3. pose proof (PT15 Γ b r) as H4.
  pose proof (Hi4 Γ a (b ∧ r) r) as H5. pose proof (MP Γ _ _ H5 H4) as H6.
  pose proof (PT21 Γ (a ∨ b) (a ∨ r)) as H7. 
  pose proof (PT1 Γ (a ∨ (b ∧ r)) (a ∨ b) ((a ∨ r) → (a ∨ b) ∧ (a ∨ r))) as H8.
  pose proof (MP Γ _ _ H8 H7) as H9. pose proof (MP Γ _ _ H9 H3) as H10.
  pose proof (PT22 Γ (a ∨ (b ∧ r)) (a ∨ r) ((a ∨ b) ∧ (a ∨ r))) as H11.
  pose proof (MP Γ _ _ H11 H10) as H12.
  pose proof (PT1 Γ (a ∨ (b ∧ r)) (a ∨ r) (a ∨ (b ∧ r) → (a ∨ b) ∧ (a ∨ r))) as H13.
  pose proof (MP Γ _ _ H13 H12) as H14. pose proof (MP Γ _ _ H14 H6) as H15.
  pose proof (PT25 Γ (a ∨ (b ∧ r)) ((a ∨ b) ∧ (a ∨ r))) as H16.
  pose proof (MP Γ _ _  H16 H15). apply H.
Qed.

Theorem PT28: forall Γ a b r, Γ ├Hi ((a ∨ b) ∧ (a ∨ r)) → (a ∨ (b ∧ r)).
Proof.
  intros. pose proof (PT21 Γ b r) as H1. pose proof (Hi4 Γ a r (b ∧ r)) as H2.
  pose proof (PT1 Γ b (r → b ∧ r) ( a ∨ r → a ∨ (b ∧ r))) as H3. pose proof (MP Γ _ _ H3 H2) as H4.
  pose proof (MP Γ _ _ H4 H1) as H5. pose proof (PT22 Γ b (a ∨ r) (a ∨ (b ∧ r))) as H6.
  pose proof (MP Γ _ _ H6 H5) as H7. pose proof (Hi4 Γ a b (a ∨ (b ∧ r))) as H8.
  pose proof (PT1 Γ (a ∨ r) (b → a ∨ (b ∧ r)) (a ∨ b → a ∨ (a ∨ (b ∧ r)))) as H9.
  pose proof (MP Γ _ _ H9 H8) as H10. pose proof (MP Γ _ _ H10 H7) as H11.
  pose proof (PT23 Γ (a ∨ r) (a ∨ b) (a ∨ (a ∨ (b ∧ r)))) as H12. pose proof (MP Γ _ _ H12 H11) as H13.
  pose proof (PT13 Γ (a ∨ b) (a ∨ r)) as H14.
  pose proof (PT1 Γ ((a ∨ b) ∧ (a ∨ r)) ((a ∨ r) ∧ (a ∨ b)) (a ∨ (a ∨ (b ∧ r)))) as H15.
  pose proof (MP Γ _ _ H15 H13) as H16. pose proof (MP Γ _ _ H16 H14) as H17.
  pose proof (PT17 Γ a a (b ∧ r)) as H18.
  pose proof (PT1 Γ ((a ∨ b) ∧ (a ∨ r)) (a ∨ (a ∨ (b ∧ r))) ((a ∨ a) ∨ (b ∧ r))) as H19.
  pose proof (MP Γ _ _ H19 H18) as H20. pose proof (MP Γ _ _ H20 H17) as H21.
  pose proof (Hi1 Γ a) as H22. pose proof (Hi4 Γ (b ∧ r) (a ∨ a) a) as H23.
  pose proof (MP Γ _ _ H23 H22) as H24. pose proof (Hi3 Γ (a ∨ a) (b ∧ r)) as H25.
  pose proof (PT1 Γ ((a ∨ a) ∨ (b ∧ r)) ((b ∧ r) ∨ (a ∨ a)) ((b ∧ r) ∨ a)) as H26.
  pose proof (MP Γ _ _ H26 H24) as H27. pose proof (MP Γ _ _ H27 H25) as H28.
  pose proof (Hi3 Γ (b ∧ r) a) as H29.
  pose proof (PT1 Γ ((a ∨ a) ∨ (b ∧ r)) ((b ∧ r) ∨ a) (a ∨ (b ∧ r))) as H30.
  pose proof (MP Γ _ _ H30 H29) as H31. pose proof (MP Γ _ _ H31 H28) as H32.
  pose proof (PT1 Γ ((a ∨ b) ∧ (a ∨ r)) ((a ∨ a) ∨ (b ∧ r)) (a ∨ (b ∧ r))) as H33.
  pose proof (MP Γ _ _ H33 H32) as H34. pose proof (MP Γ _ _ H34 H21). apply H.
Qed.

Theorem PT29: forall Γ a b r, Γ ├Hi (a ∧ (b ∨ r)) → ((a ∧ b) ∨ (a ∧ r)).
Proof.
  intros. pose proof (PT28 Γ ﹁a ﹁b ﹁r) as H1.
  pose proof (PT7 Γ ((﹁a ∨ ﹁b) ∧ (﹁a ∨ ﹁r)) (﹁a ∨ (﹁ b ∧ ﹁ r))) as H2.
  pose proof (MP Γ _ _ H2 H1) as H3. pose proof (PT12 Γ ﹁a (﹁ b ∧ ﹁ r)) as H4.
  pose proof (PT1 Γ (﹁﹁a ∧ ﹁(﹁b ∧ ﹁r))(﹁(﹁a ∨ (﹁ b ∧ ﹁ r))) (﹁((﹁a ∨ ﹁b) ∧ (﹁a ∨ ﹁r)))) as H5.
  pose proof (MP Γ _ _ H5 H3) as H6. pose proof (MP Γ _ _ H6 H4) as H7.
  pose proof (PT8 Γ (﹁a ∨ ﹁b) (﹁a ∨ ﹁r)) as H8.
  pose proof (PT1 Γ (﹁﹁a ∧ ﹁(﹁b ∧ ﹁r)) (﹁((﹁a ∨ ﹁b) ∧ (﹁a ∨ ﹁r))) (﹁(﹁a ∨ ﹁b) ∨ ﹁(﹁a ∨ ﹁r))) as H9.
  pose proof (MP Γ _ _ H9 H8) as H10. pose proof (MP Γ _ _ H10 H7) as H11.
  pose proof (PT5 Γ r) as H12. pose proof (Hi4 Γ b r ﹁﹁r) as H13. 
  pose proof (MP Γ _ _ H13 H12) as H14. pose proof (PT5 Γ b) as H15.
  pose proof (Hi4 Γ ﹁﹁r b ﹁﹁b) as H16. pose proof (MP Γ _ _ H16 H15) as H17.
  pose proof (Hi3 Γ b ﹁﹁r) as H18.
  pose proof (PT1 Γ (b ∨ ﹁﹁r) (﹁﹁r ∨ b) (﹁﹁r ∨ ﹁﹁b)) as H19.
  pose proof (MP Γ _ _ H19 H17) as H20. pose proof (MP Γ _ _ H20 H18) as H21.
  pose proof (Hi3 Γ ﹁﹁r ﹁﹁b) as H22.
  pose proof (PT1 Γ (b ∨ ﹁﹁r) (﹁﹁r ∨ ﹁﹁b) (﹁﹁b ∨ ﹁﹁r)) as H23.
  pose proof (MP Γ _ _ H23 H22) as H24. pose proof (MP Γ _ _ H24 H21) as H25.
  pose proof (PT1 Γ (b ∨ r) (b ∨ ﹁﹁r) (﹁﹁b ∨ ﹁﹁r)) as H26.
  pose proof (MP Γ _ _ H26 H25) as H27. pose proof (MP Γ _ _ H27 H14) as H28.
  pose proof (PT9 Γ ﹁b ﹁r) as H29.
  pose proof (PT1 Γ (b ∨ r) (﹁﹁b ∨ ﹁﹁r) (﹁(﹁b ∧ ﹁r))) as H30.
  pose proof (MP Γ _ _ H30 H29) as H31. pose proof (MP Γ _ _ H31 H28) as H32.
  pose proof (PT7 Γ (b ∨ r) (﹁(﹁b ∧ ﹁r))) as H33. pose proof (MP Γ _ _ H33 H32) as H34.
  pose proof (Hi4 Γ ﹁﹁﹁a (﹁﹁(﹁b ∧ ﹁r)) (﹁(b ∨ r))) as H35. pose proof (MP Γ _ _ H35 H34) as H36.
  pose proof (PT6 Γ ﹁a) as H37. pose proof (Hi4 Γ (﹁(b ∨ r)) ﹁﹁﹁a ﹁a) as H38.
  pose proof (MP Γ _ _ H38 H37) as H39. pose proof (Hi3 Γ ﹁﹁﹁a (﹁(b ∨ r))) as H40.
  pose proof (PT1 Γ (﹁﹁﹁a ∨ (﹁(b ∨ r))) ((﹁(b ∨ r)) ∨ ﹁﹁﹁a) ((﹁(b ∨ r)) ∨ ﹁a)) as H41.
  pose proof (MP Γ _ _ H41 H39) as H42. pose proof (MP Γ _ _ H42 H40) as H43.
  pose proof (Hi3 Γ ﹁(b ∨ r) ﹁a) as H44.
  pose proof (PT1 Γ (﹁﹁﹁a ∨ (﹁(b ∨ r))) ((﹁(b ∨ r)) ∨ ﹁a) (﹁a ∨ (﹁(b ∨ r)))) as H45.
  pose proof (MP Γ _ _ H45 H44) as H46. pose proof (MP Γ _ _ H46 H43) as H47.
  pose proof (PT1 Γ (﹁﹁﹁a ∨ (﹁﹁(﹁b ∧ ﹁r))) (﹁﹁﹁a ∨ (﹁(b ∨ r))) (﹁a ∨ (﹁(b ∨ r)))) as H48.
  pose proof (MP Γ _ _ H48 H47) as H49. pose proof (MP Γ _ _ H49 H36) as H50.
  pose proof (PT7 Γ (﹁﹁﹁a ∨ (﹁﹁(﹁b ∧ ﹁r))) (﹁a ∨ (﹁(b ∨ r)))) as H51.
  pose proof (MP Γ _ _ H51 H50) as H52.
  pose proof (PT1 Γ (﹁(﹁a ∨ (﹁(b ∨ r)))) (﹁(﹁﹁﹁a ∨ (﹁﹁(﹁b ∧ ﹁r)))) (﹁(﹁a ∨ ﹁b) ∨ ﹁(﹁a ∨ ﹁r))) as H53.
  pose proof (MP Γ _ _ H53 H11) as H54. pose proof (MP Γ _ _ H54 H52). apply H.
Qed.

Theorem PT30: forall Γ a b r, Γ ├Hi ((a ∧ b) ∨ (a ∧ r)) → (a ∧ (b ∨ r)).
Proof.
  intros. pose proof (PT27 Γ ﹁a ﹁b ﹁r) as H1.
  pose proof (PT7 Γ (﹁a ∨ (﹁b ∧ ﹁r)) ((﹁a ∨ ﹁b) ∧ (﹁a ∨ ﹁r))) as H2. pose proof (MP Γ _ _ H2 H1) as H3.
  pose proof (PT9 Γ (﹁a ∨ ﹁b) (﹁a ∨ ﹁r)) as H4.
  pose proof (PT1 Γ (﹁(﹁a ∨ ﹁b) ∨ ﹁(﹁a ∨ ﹁r)) (﹁((﹁a ∨ ﹁b) ∧ (﹁a ∨ ﹁r))) (﹁(﹁a ∨ (﹁b ∧ ﹁r)))) as H5.
  pose proof (MP Γ _ _ H5 H3) as H6. pose proof (MP Γ _ _ H6 H4) as H7.
  pose proof (PT11 Γ ﹁a (﹁b ∧ ﹁r)) as H8.
  pose proof (PT1 Γ (﹁(﹁a ∨ ﹁b) ∨ ﹁(﹁a ∨ ﹁r)) (﹁(﹁a ∨ (﹁b ∧ ﹁r))) (﹁﹁a ∧ ﹁(﹁b ∧ ﹁r))) as H9.
  pose proof (MP Γ _ _ H9 H8) as H10. pose proof (MP Γ _ _ H10 H7) as H11.
  pose proof (PT6 Γ r) as H12. pose proof (Hi4 Γ b ﹁﹁r r) as H13. 
  pose proof (MP Γ _ _ H13 H12) as H14. pose proof (PT6 Γ b) as H15.
  pose proof (Hi4 Γ ﹁﹁r ﹁﹁b b) as H16. pose proof (MP Γ _ _ H16 H15) as H17.
  pose proof (Hi3 Γ ﹁﹁r b) as H18. pose proof (PT1 Γ (﹁﹁r ∨ ﹁﹁b) (﹁﹁r ∨ b) (b ∨ ﹁﹁r)) as H19.
  pose proof (MP Γ _ _ H19 H18) as H20. pose proof (MP Γ _ _ H20 H17) as H21.
  pose proof (Hi3 Γ ﹁﹁b ﹁﹁r) as H22. pose proof (PT1 Γ (﹁﹁b ∨ ﹁﹁r) (﹁﹁r ∨ ﹁﹁b) (b ∨ ﹁﹁r)) as H23.
  pose proof (MP Γ _ _ H23 H21) as H24. pose proof (MP Γ _ _ H24 H22) as H25.
  pose proof (PT1 Γ (﹁﹁b ∨ ﹁﹁r) (b ∨ ﹁﹁r) (b ∨ r)) as H26.
  pose proof (MP Γ _ _ H26 H14) as H27. pose proof (MP Γ _ _ H27 H25) as H28.
  pose proof (PT8 Γ ﹁b ﹁r) as H29. pose proof (PT1 Γ (﹁(﹁b ∧ ﹁r)) (﹁﹁b ∨ ﹁﹁r) (b ∨ r)) as H30.
  pose proof (MP Γ _ _ H30 H28) as H31. pose proof (MP Γ _ _ H31 H29) as H32.
  pose proof (PT7 Γ (﹁(﹁b ∧ ﹁r)) (b ∨ r)) as H33. pose proof (MP Γ _ _ H33 H32) as H34.
  pose proof (Hi4 Γ ﹁﹁﹁a (﹁(b ∨ r)) (﹁﹁(﹁b ∧ ﹁r))) as H35. pose proof (MP Γ _ _ H35 H34) as H36.
  pose proof (PT5 Γ ﹁a) as H37. pose proof (Hi4 Γ (﹁(b ∨ r)) ﹁a ﹁﹁﹁a) as H38.
  pose proof (MP Γ _ _ H38 H37) as H39. pose proof (Hi3 Γ ﹁a (﹁(b ∨ r))) as H40.
  pose proof (PT1 Γ (﹁a ∨ (﹁(b ∨ r))) ((﹁(b ∨ r)) ∨ ﹁a) ((﹁(b ∨ r)) ∨ ﹁﹁﹁a)) as H41.
  pose proof (MP Γ _ _ H41 H39) as H42. pose proof (MP Γ _ _ H42 H40) as H43.
  pose proof (Hi3 Γ (﹁(b ∨ r)) ﹁﹁﹁a) as H44.
  pose proof (PT1 Γ (﹁a ∨ (﹁(b ∨ r))) (﹁(b ∨ r) ∨ ﹁﹁﹁a) (﹁﹁﹁a ∨ ﹁(b ∨ r))) as H45.
  pose proof (MP Γ _ _ H45 H44) as H46. pose proof (MP Γ _ _ H46 H43) as H47.
  pose proof (PT1 Γ (﹁a ∨ (﹁(b ∨ r))) (﹁﹁﹁a ∨ ﹁(b ∨ r)) (﹁﹁﹁a ∨ ﹁﹁(﹁b ∧ ﹁r))) as H48.
  pose proof (MP Γ _ _ H48 H36) as H49. pose proof (MP Γ _ _ H49 H47) as H50.
  pose proof (PT7 Γ (﹁a ∨ (﹁(b ∨ r))) (﹁﹁﹁a ∨ ﹁﹁(﹁b ∧ ﹁r))) as H51.
  pose proof (MP Γ _ _ H51 H50) as H52.
  pose proof (PT1 Γ (﹁(﹁a ∨ ﹁b) ∨ ﹁(﹁a ∨ ﹁r)) (﹁(﹁﹁﹁a ∨ ﹁﹁(﹁b ∧ ﹁r))) (﹁(﹁a ∨ (﹁(b ∨ r))))) as H53.
  pose proof (MP Γ _ _ H53 H52) as H54. pose proof (MP Γ _ _ H54 H11). apply H.
Qed.

(*蕴含合取构成原则*)
Theorem PT31: forall Γ a b r, Γ ├Hi ((a → b) ∧ (a → r)) → (a → (b ∧ r)).
Proof.
  intros. pose proof (PT28 Γ ﹁a b r). apply H.
Qed.

Theorem PT32: forall Γ a, Γ ├Hi a ↔ ﹁﹁a.
Proof.
  intros. pose proof (PT5 Γ a) as H1. pose proof (PT6 Γ a) as H2.
  pose proof (PT21 Γ (a → ﹁﹁a) (﹁﹁a → a))as H3.
  pose proof (MP Γ _ _ H3 H1) as H4. pose proof (MP Γ _ _ H4 H2). apply H.
Qed.

Theorem PT33: forall Γ a b, Γ ├Hi ﹁(a ∨ b) ↔ ﹁a ∧ ﹁b.
Proof.
  intros. pose proof (PT11 Γ a b) as H1. pose proof (PT12 Γ a b) as H2.
  pose proof (PT21 Γ (﹁(a ∨ b) → ﹁a ∧ ﹁b) (﹁a ∧ ﹁b → ﹁(a ∨ b))) as H3.
  pose proof (MP Γ _ _ H3 H1) as H4. pose proof (MP Γ _ _ H4 H2). apply H.
Qed.

Theorem PT34: forall Γ a b, Γ ├Hi ﹁(a ∧ b) ↔ ﹁a ∨ ﹁b.
Proof.
  intros. pose proof (PT8 Γ a b) as H1. pose proof (PT9 Γ a b) as H2.
  pose proof (PT21 Γ (﹁(a ∧ b) → (﹁a ∨ ﹁b)) ((﹁a ∨ ﹁b) → ﹁(a ∧ b))) as H3.
  pose proof (MP Γ _ _ H3 H1) as H4. pose proof (MP Γ _ _ H4 H2). apply H.
Qed.

Theorem PT35: forall Γ a, Γ ├Hi a ↔ a.
Proof.
  intros. pose proof (PT2 Γ a) as H1. pose proof (PT2 Γ a) as H2.
  pose proof (PT21 Γ (a → a) (a → a)) as H3.
  pose proof (MP Γ _ _ H3 H1) as H4. pose proof (MP Γ _ _ H4 H2). apply H.
Qed.

Theorem PT36: forall Γ a b, Γ ├Hi (a → b) ↔ (﹁a ∨ b).
Proof.
  intros. pose proof (PT35 Γ (a → b)). apply H.
Qed.

Theorem PT37: forall Γ a b, Γ ├Hi (a ↔ b) ↔ ((﹁a ∨ b) ∧ (﹁b ∨ a)).
Proof.
  intros. pose proof (PT35 Γ (a ↔ b)). apply H.
Qed.

Theorem PT38: forall Γ a b, Γ ├Hi (a ↔ b) → (﹁a ↔ ﹁b).
Proof.
  intros. pose proof (PT14 Γ (a → b) (b → a)) as H1. pose proof (PT7 Γ a b) as H2.
  pose proof (PT1 Γ (a ↔ b) (a → b) (﹁b → ﹁a)) as H3.
  pose proof (MP Γ _ _ H3 H2) as H4. pose proof (MP Γ _ _ H4 H1) as H5.
  pose proof (PT15 Γ (a → b) (b → a)) as H6. pose proof (PT7 Γ b a) as H7.
  pose proof (PT1 Γ (a ↔ b) (b → a) (﹁a → ﹁b)) as H8.
  pose proof (MP Γ _ _ H8 H7) as H9. pose proof (MP Γ _ _ H9 H6) as H10.
  pose proof (PT21 Γ ((a ↔ b) → (﹁a → ﹁b)) ((a ↔ b) → (﹁b → ﹁a))) as H11.
  pose proof (MP Γ _ _ H11 H10) as H12. pose proof (MP Γ _ _ H12 H5) as H13.
  pose proof (PT31 Γ (a ↔ b) (﹁a → ﹁b) (﹁b → ﹁a)) as H14.
  pose proof (MP Γ _ _ H14 H13). apply H.
Qed.

Theorem PT39: forall Γ a b, Γ ├Hi a ↔ a ∧ (b ∨ ﹁b).
Proof.
  intros. pose proof (PT14 Γ a (b ∨ ﹁b)) as H1. 
  pose proof (PT21 Γ a (b ∨ ﹁b)) as H2.
  pose proof (PT22 Γ a (b ∨ ﹁b) (a ∧ (b ∨ ﹁b))) as H3. 
  pose proof (MP Γ _ _ H3 H2) as H4. pose proof (PT4 Γ b) as H5. 
  pose proof (MP Γ _ _ H4 H5) as H6.
  pose proof (PT21 Γ (a → a ∧ (b ∨ ﹁b)) (a ∧ (b ∨ ﹁b) → a)) as H7.
  pose proof (MP Γ _ _ H7 H6) as H8. pose proof (MP Γ _ _ H8 H1). apply H.
Qed.

Theorem PT40: forall Γ a b, Γ ├Hi a ↔ a ∨ (b ∧ ﹁b).
Proof.
  intros. pose proof (PT39 Γ ﹁a ﹁b) as H1.
  pose proof (PT14 Γ (﹁a → (﹁a ∧ (﹁b ∨ ﹁﹁b))) ((﹁a ∧ (﹁b ∨ ﹁﹁b)) → ﹁a)) as H2.
  pose proof (MP Γ _ _ H2 H1) as H3. pose proof (PT7 Γ ﹁a (﹁a ∧ (﹁b ∨ ﹁﹁b))) as H4.
  pose proof (MP Γ _ _ H4 H3) as H5. pose proof (PT6 Γ a) as H6.
  pose proof (PT1 Γ (﹁(﹁a ∧ (﹁b ∨ ﹁﹁b))) ﹁﹁a a) as H7.
  pose proof (MP Γ _ _ H7 H6) as H8. pose proof (MP Γ _ _ H8 H5) as H9.
  pose proof (PT9 Γ ﹁a (﹁b ∨ ﹁﹁b)) as H10. pose proof (PT5 Γ a) as H11.
  pose proof (Hi4 Γ (b ∧ ﹁b) a ﹁﹁a) as H12. pose proof (MP Γ _ _ H12 H11) as H13.
  pose proof (Hi3 Γ a (b ∧ ﹁b)) as H14.
  pose proof (PT1 Γ (a ∨ (b ∧ ﹁ b)) ((b ∧ ﹁ b) ∨ a) ((b ∧ ﹁ b) ∨ ﹁﹁a)) as H15.
  pose proof (MP Γ _ _ H15 H13) as H16. pose proof (MP Γ _ _ H16 H14) as H17.
  pose proof (Hi3 Γ (b ∧ ﹁ b) ﹁﹁a) as H18.
  pose proof (PT1 Γ (a ∨ (b ∧ ﹁ b)) ((b ∧ ﹁ b) ∨ ﹁﹁a) (﹁﹁a ∨ (b ∧ ﹁ b))) as H19.
  pose proof (MP Γ _ _ H19 H18) as H20. pose proof (MP Γ _ _ H20 H17) as H21.
  pose proof (PT1 Γ (a ∨ (b ∧ ﹁ b)) (﹁﹁a ∨ (b ∧ ﹁ b)) (﹁(﹁a ∧ (﹁b ∨ ﹁﹁b)))) as H22.
  pose proof (MP Γ _ _ H22 H10) as H23. pose proof (MP Γ _ _ H23 H21) as H24.
  pose proof (PT1 Γ (a ∨ (b ∧ ﹁ b)) (﹁(﹁a ∧ (﹁b ∨ ﹁﹁b))) a) as H25.
  pose proof (MP Γ _ _ H25 H9) as H26. pose proof (MP Γ _ _ H26 H24) as H27.
  pose proof (PT15 Γ (﹁a → (﹁a ∧ (﹁b ∨ ﹁﹁b))) ((﹁a ∧ (﹁b ∨ ﹁﹁b)) → ﹁a)) as H28.
  pose proof (MP Γ _ _ H28 H1) as H29. pose proof (PT7 Γ (﹁a ∧ (﹁b ∨ ﹁﹁b)) ﹁a) as H30.
  pose proof (MP Γ _ _ H30 H29) as H31. pose proof (PT5 Γ a) as H32.
  pose proof (PT1 Γ a ﹁﹁a (﹁(﹁a ∧ (﹁b ∨ ﹁﹁b)))) as H33.
  pose proof (MP Γ _ _ H33 H31) as H34. pose proof (MP Γ _ _ H34 H32) as H35.
  pose proof (Hi4 Γ (b ∧ ﹁ b) ﹁﹁a a) as H36. pose proof (MP Γ _ _ H36 H6) as H37.
  pose proof (Hi3 Γ ﹁﹁a (b ∧ ﹁ b)) as H38.
  pose proof (PT1 Γ (﹁﹁a ∨ (b ∧ ﹁b)) ((b ∧ ﹁b) ∨ ﹁﹁a) ((b ∧ ﹁b) ∨ a)) as H39.
  pose proof (MP Γ _ _ H39 H37) as H40. pose proof (MP Γ _ _ H40 H38) as H41.
  pose proof (Hi3 Γ (b ∧ ﹁ b) a) as H42.
  pose proof (PT1 Γ (﹁﹁a ∨ (b ∧ ﹁b)) ((b ∧ ﹁b) ∨ a) (a ∨ (b ∧ ﹁b))) as H43.
  pose proof (MP Γ _ _ H43 H42) as H44. pose proof (MP Γ _ _ H44 H41) as H45.
  pose proof (PT8 Γ ﹁a (﹁b ∨ ﹁﹁b)) as H46.
  pose proof (PT1 Γ (﹁(﹁a ∧ (﹁b ∨ ﹁﹁b))) (﹁﹁a ∨ (b ∧ ﹁b)) (a ∨ (b ∧ ﹁b))) as H47.
  pose proof (MP Γ _ _ H47 H45) as H48. pose proof (MP Γ _ _ H48 H46) as H49.
  pose proof (PT1 Γ a (﹁(﹁a ∧ (﹁b ∨ ﹁﹁b))) (a ∨ (b ∧ ﹁b))) as H50.
  pose proof (MP Γ _ _ H50 H49) as H51. pose proof (MP Γ _ _ H51 H35) as H52.
  pose proof (PT21 Γ (a → a ∨ (b ∧ ﹁b)) (a ∨ (b ∧ ﹁b) → a)) as H53.
  pose proof (MP Γ _ _ H53 H52) as H54. pose proof (MP Γ _ _ H54 H27). apply H.
Qed.

Theorem PT41: forall Γ a b, Γ ├Hi a → (b → a).
Proof.
  intros. pose proof (Hi3 Γ a ﹁b). pose proof (PT1 Γ a (a ∨ ﹁b) (b → a)).
  pose proof (Hi2 Γ a ﹁b). pose proof (MP Γ _ _ H0 H). 
  pose proof (MP Γ _ _ H2 H1). apply H3.
Qed.

Theorem PT42: forall Γ a b r, Γ ├Hi a ↔ a ∧ (b ∨ ﹁b ∨ r).
Proof.
  intros. pose proof (Hi2 Γ (b ∨ ﹁b) r) as H1. pose proof (PT18 Γ b ﹁b r) as H2.
  pose proof (PT1 Γ (b ∨ ﹁b) ((b ∨ ﹁b) ∨ r) (b ∨ (﹁b ∨ r))) as H3.
  pose proof (MP Γ _ _ H3 H2) as H4. pose proof (MP Γ _ _ H4 H1) as H5.
  pose proof (PT41 Γ (b ∨ ﹁b) (b ∨ (﹁b ∨ r))) as H6. pose proof (PT4 Γ b) as H7.
  pose proof (MP Γ _ _ H6 H7) as H8. pose proof (PT39 Γ a b) as H9.
  pose proof (PT14 Γ (a → a ∧ (b ∨ ﹁b)) (a ∧ (b ∨ ﹁b) → a)) as H10.
  pose proof (MP Γ _ _ H10 H9) as H11. pose proof (PT7 Γ (b ∨ ﹁b) (b ∨ (﹁b ∨ r))) as H12.
  pose proof (MP Γ _ _ H12 H5) as H13. pose proof (Hi4 Γ ﹁a ﹁(b ∨ (﹁b ∨ r)) ﹁(b ∨ ﹁b)) as H14.
  pose proof (MP Γ _ _ H14 H13) as H15. pose proof (PT7 Γ (﹁a ∨ ﹁(b ∨ (﹁b ∨ r))) (﹁a ∨ ﹁(b ∨ ﹁b))) as H16.
  pose proof (MP Γ _ _ H16 H15) as H17. pose proof (PT1 Γ a (a ∧ (b ∨ ﹁b)) (a ∧ (b ∨ (﹁b ∨ r)))) as H18.
  pose proof (MP Γ _ _ H18 H17) as H19. pose proof (MP Γ _ _ H19 H11) as H20.
  pose proof (PT14 Γ a (b ∨ ﹁b)) as H21. pose proof (PT7 Γ (b ∨ (﹁b ∨ r)) (b ∨ ﹁b)) as H22.
  pose proof (MP Γ _ _ H22 H8) as H23. pose proof (Hi4 Γ ﹁a ﹁(b ∨ ﹁ b) ﹁(b ∨ (﹁b ∨ r))) as H24.
  pose proof (MP Γ _ _ H24 H23) as H25. pose proof (PT7 Γ (﹁a ∨ ﹁(b ∨ ﹁ b)) (﹁a ∨ ﹁(b ∨ (﹁b ∨ r)))) as H26.
  pose proof (MP Γ _ _ H26 H25) as H27. pose proof (PT1 Γ (a ∧ (b ∨ (﹁b ∨ r))) (a ∧ (b ∨ ﹁b)) a) as H28.
  pose proof (MP Γ _ _ H28 H21) as H29. pose proof (MP Γ _ _ H29 H27) as H30.
  pose proof (PT21 Γ (a → a ∧ (b ∨ (﹁b ∨ r))) (a ∧ (b ∨ (﹁b ∨ r)) → a)) as H31.
  pose proof (MP Γ _ _ H31 H20) as H32. pose proof (MP Γ _ _ H32 H30). apply H.
Qed.

Theorem PT43: forall Γ a b r, Γ ├Hi a ↔ a ∨ (b ∧ ﹁b ∧ r).
Proof.
  intros. pose proof (PT42 Γ ﹁a ﹁b ﹁r) as H1.
  pose proof (PT14 Γ (﹁a → ﹁a ∧ (﹁b ∨ ﹁﹁b ∨ ﹁r)) (﹁a ∧ (﹁b ∨ ﹁﹁b ∨ ﹁r) → ﹁a)) as H2.
  pose proof (MP Γ _ _ H2 H1) as H3. pose proof (PT7 Γ ﹁a ﹁a ∧ (﹁b ∨ ﹁﹁b ∨ ﹁r)) as H4.
  pose proof (MP Γ _ _ H4 H3) as H5. pose proof (PT6 Γ a) as H6.
  pose proof (PT1 Γ ﹁(﹁a ∧ (﹁b ∨ ﹁﹁b ∨ ﹁r)) ﹁﹁a a) as H7. pose proof (MP Γ _ _ H7 H6) as H8.
  pose proof (MP Γ _ _ H8 H5) as H9. pose proof (PT5 Γ (﹁﹁b ∨ ﹁r)) as H10.
  pose proof (Hi4 Γ ﹁b (﹁﹁b ∨ ﹁r) ﹁﹁(﹁﹁b ∨ ﹁r)) as H11. pose proof (MP Γ _ _ H11 H10) as H12.
  pose proof (PT7 Γ (﹁b ∨ (﹁﹁b ∨ ﹁r)) (﹁b ∨ ﹁﹁(﹁﹁b ∨ ﹁r))) as H13. pose proof (MP Γ _ _ H13 H12) as H14.
  pose proof (Hi4 Γ ﹁﹁a (b ∧ ﹁b ∧ r) ﹁(﹁b ∨ (﹁﹁b ∨ ﹁r))) as H15. pose proof (MP Γ _ _ H15 H14) as H16.
  pose proof (PT5 Γ a) as H17. pose proof (Hi4 Γ (b ∧ ﹁b ∧ r) a ﹁﹁a) as H18.
  pose proof (MP Γ _ _ H18 H17) as H19. pose proof (Hi3 Γ a (b ∧ ﹁b ∧ r)) as H20.
  pose proof (PT1 Γ (a ∨ (b ∧ ﹁b ∧ r)) ((b ∧ ﹁b ∧ r) ∨ a) ((b ∧ ﹁b ∧ r) ∨ ﹁﹁a)) as H21.
  pose proof (MP Γ _ _ H21 H19) as H22. pose proof (MP Γ _ _ H22 H20) as H23.
  pose proof (Hi3 Γ (b ∧ ﹁b ∧ r) ﹁﹁a) as H24.
  pose proof (PT1 Γ (a ∨ (b ∧ ﹁b ∧ r)) ((b ∧ ﹁b ∧ r) ∨ ﹁﹁a) (﹁﹁a ∨ (b ∧ ﹁b ∧ r))) as H25.
  pose proof (MP Γ _ _ H25 H24) as H26. pose proof (MP Γ _ _ H26 H23) as H27.
  pose proof (PT1 Γ (a ∨ (b ∧ ﹁b ∧ r)) (﹁﹁a ∨ (b ∧ ﹁b ∧ r)) (﹁﹁a ∨ ﹁(﹁b ∨ ﹁﹁b ∨ ﹁r))) as H28.
  pose proof (MP Γ _ _ H28 H16) as H29. pose proof (MP Γ _ _ H29 H27) as H30.
  pose proof (PT9 Γ ﹁a (﹁b ∨ ﹁﹁b ∨ ﹁r)) as H31.
  pose proof (PT1 Γ (a ∨ (b ∧ ﹁b ∧ r)) (﹁﹁a ∨ ﹁(﹁b ∨ ﹁﹁b ∨ ﹁r)) ﹁(﹁a ∧ (﹁b ∨ ﹁﹁b ∨ ﹁r))) as H32.
  pose proof (MP Γ _ _ H32 H31) as H33. pose proof (MP Γ _ _ H33 H30) as H34.
  pose proof (PT1 Γ (a ∨ (b ∧ ﹁b ∧ r)) ﹁(﹁a ∧ (﹁b ∨ ﹁﹁b ∨ ﹁r)) a) as H35.
  pose proof (MP Γ _ _ H35 H9) as H36. pose proof (MP Γ _ _ H36 H34) as H37.
  pose proof (PT15 Γ (﹁a → ﹁a ∧ (﹁b ∨ ﹁﹁b ∨ ﹁r)) (﹁a ∧ (﹁b ∨ ﹁﹁b ∨ ﹁r) → ﹁a)) as H38.
  pose proof (MP Γ _ _ H38 H1) as H39. pose proof (PT7 Γ (﹁a ∧ (﹁b ∨ ﹁﹁b ∨ ﹁r)) ﹁a) as H40.
  pose proof (MP Γ _ _ H40 H39) as H41. pose proof (PT5 Γ a) as H42.
  pose proof (PT1 Γ a ﹁﹁a ﹁(﹁a ∧ (﹁b ∨ ﹁﹁b ∨ ﹁r))) as H43. pose proof (MP Γ _ _ H43 H41) as H44.
  pose proof (MP Γ _ _ H44 H42) as H45. pose proof (PT6 Γ (﹁﹁b ∨ ﹁r)) as H46.
  pose proof (Hi4 Γ ﹁b ﹁﹁(﹁﹁b ∨ ﹁r) (﹁﹁b ∨ ﹁r)) as H47. pose proof (MP Γ _ _ H47 H46) as H48.
  pose proof (PT7 Γ (﹁b ∨ ﹁﹁(﹁﹁b ∨ ﹁r)) (﹁b ∨ (﹁﹁b ∨ ﹁r))) as H49. pose proof (MP Γ _ _ H49 H48) as H50.
  pose proof (Hi4 Γ ﹁﹁a ﹁(﹁b ∨ (﹁﹁b ∨ ﹁r)) ﹁(﹁b ∨ ﹁﹁(﹁﹁b ∨ ﹁r))) as H51.
  pose proof (MP Γ _ _ H51 H50) as H52. pose proof (PT6 Γ a) as H53.
  pose proof (Hi4 Γ (b ∧ ﹁b ∧ r) ﹁﹁a a) as H54. pose proof (MP Γ _ _ H54 H53) as H55.
  pose proof (Hi3 Γ ﹁﹁a (b ∧ ﹁b ∧ r)) as H56.
  pose proof (PT1 Γ (﹁﹁a ∨ (b ∧ ﹁b ∧ r)) ((b ∧ ﹁b ∧ r) ∨ ﹁﹁a) ((b ∧ ﹁b ∧ r) ∨ a)) as H57.
  pose proof (MP Γ _ _ H57 H55) as H58. pose proof (MP Γ _ _ H58 H56) as H59.
  pose proof (Hi3 Γ (b ∧ ﹁b ∧ r) a) as H60.
  pose proof (PT1 Γ (﹁﹁a ∨ (b ∧ ﹁b ∧ r)) ((b ∧ ﹁b ∧ r) ∨ a) (a ∨ (b ∧ ﹁b ∧ r))) as H61.
  pose proof (MP Γ _ _ H61 H60) as H62. pose proof (MP Γ _ _ H62 H59) as H63.
  pose proof (PT1 Γ (﹁﹁a ∨ ﹁(﹁b ∨ (﹁﹁b ∨ ﹁r))) (﹁﹁a ∨ (b ∧ ﹁b ∧ r)) (a ∨ (b ∧ ﹁b ∧ r))) as H64.
  pose proof (MP Γ _ _ H64 H63) as H65. pose proof (MP Γ _ _ H65 H52) as H66.
  pose proof (PT8 Γ ﹁a (﹁b ∨ (﹁﹁b ∨ ﹁r))) as H67.
  pose proof (PT1 Γ ﹁(﹁a ∧ (﹁b ∨ (﹁﹁b ∨ ﹁r))) (﹁﹁a ∨ ﹁(﹁b ∨ (﹁﹁b ∨ ﹁r))) (a ∨ (b ∧ ﹁b ∧ r))) as H68.
  pose proof (MP Γ _ _ H68 H66) as H69. pose proof (MP Γ _ _ H69 H67) as H70.
  pose proof (PT1 Γ a ﹁(﹁a ∧ (﹁b ∨ (﹁﹁b ∨ ﹁r))) (a ∨ (b ∧ ﹁b ∧ r))) as H71.
  pose proof (MP Γ _ _ H71 H70) as H72. pose proof (MP Γ _ _ H72 H45) as H73.
  pose proof (PT21 Γ (a → (a ∨ (b ∧ ﹁b ∧ r))) ((a ∨ (b ∧ ﹁b ∧ r)) → a)) as H74.
  pose proof (MP Γ _ _ H74 H73) as H75. pose proof (MP Γ _ _ H75 H37). apply H.
Qed.

Theorem PT44: forall Γ a b, Γ ├Hi (a ↔ b) ↔ (a ∧ b) ∨ (﹁a ∧ ﹁b).
Proof.
  intros. pose proof (PT40 Γ (a ∧ b) a) as H1.
  pose proof (PT14 Γ ((a ∧ b) → (a ∧ b) ∨ (a ∧ ﹁a)) ((a ∧ b) ∨ (a ∧ ﹁a) → (a ∧ b))) as H2.
  pose proof (MP Γ _ _ H2 H1) as H3. pose proof (Hi3 Γ (a ∧ b) (a ∧ ﹁a)) as H4.
  pose proof (PT1 Γ (a ∧ b) ((a ∧ b) ∨ (a ∧ ﹁a)) ((a ∧ ﹁a) ∨ (a ∧ b))) as H5.
  pose proof (MP Γ _ _ H5 H4) as H6. pose proof (MP Γ _ _ H6 H3) as H7.
  pose proof (PT30 Γ a ﹁a b) as H8. pose proof (PT1 Γ (a ∧ b) ((a ∧ ﹁a) ∨ (a ∧ b)) (a ∧ (﹁a ∨ b))) as H9.
  pose proof (MP Γ _ _ H9 H8) as H10. pose proof (MP Γ _ _ H10 H7) as H11.
  pose proof (PT13 Γ a (﹁a ∨ b)) as H12. pose proof (PT1 Γ (a ∧ b) (a ∧ (﹁a ∨ b)) ((﹁a ∨ b) ∧ a)) as H13.
  pose proof (MP Γ _ _ H13 H12) as H14. pose proof (MP Γ _ _ H14 H11) as H15.
  pose proof (PT40 Γ (﹁a ∧ ﹁b) b) as H16. pose proof (PT13 Γ b ﹁b) as H17.
  pose proof (Hi4 Γ (﹁a ∧ ﹁b) (b ∧ ﹁b) (﹁b ∧ b)) as H18. pose proof (MP Γ _ _ H18 H17) as H19.
  pose proof (PT1 Γ (﹁a ∧ ﹁b) ((﹁a ∧ ﹁b) ∨ (b ∧ ﹁b)) ((﹁a ∧ ﹁b) ∨ (﹁b ∧ b))) as H20.
  pose proof (MP Γ _ _ H20 H19) as H21.
  pose proof (PT14 Γ ((﹁a ∧ ﹁b) → ((﹁a ∧ ﹁b) ∨ (b ∧ ﹁b))) (((﹁a ∧ ﹁b) ∨ (b ∧ ﹁b)) → (﹁a ∧ ﹁b))) as H22.
  pose proof (MP Γ _ _ H22 H16) as H23. pose proof (MP Γ _ _ H21 H23) as H24.
  pose proof (PT13 Γ ﹁a ﹁b) as H25. pose proof (Hi4 Γ (﹁b ∧ b) (﹁a ∧ ﹁b) (﹁b ∧ ﹁a)) as H26.
  pose proof (MP Γ _ _ H26 H25) as H27. pose proof (Hi3 Γ (﹁a ∧ ﹁b) (﹁b ∧ b)) as H28.
  pose proof (PT1 Γ ((﹁a ∧ ﹁b) ∨ (﹁b ∧ b)) ((﹁b ∧ b) ∨ (﹁a ∧ ﹁b)) ((﹁b ∧ b) ∨ (﹁b ∧ ﹁a))) as H29.
  pose proof (MP Γ _ _ H29 H27) as H30. pose proof (MP Γ _ _ H30 H28) as H31.
  pose proof (Hi3 Γ (﹁b ∧ b) (﹁b ∧ ﹁a)) as H32.
  pose proof (PT1 Γ ((﹁a ∧ ﹁b) ∨ (﹁b ∧ b)) ((﹁b ∧ b) ∨ (﹁b ∧ ﹁a)) ((﹁b ∧ ﹁a) ∨ (﹁b ∧ b))) as H33.
  pose proof (MP Γ _ _ H33 H32) as H34. pose proof (MP Γ _ _ H34 H31) as H35.
  pose proof (PT1 Γ (﹁a ∧ ﹁b) ((﹁a ∧ ﹁b) ∨ (﹁b ∧ b)) ((﹁b ∧ ﹁a) ∨ (﹁b ∧ b))) as H36.
  pose proof (MP Γ _ _ H36 H35) as H37. pose proof (MP Γ _ _ H37 H24) as H38.
  pose proof (PT30 Γ ﹁b ﹁a b) as H39. pose proof (PT13 Γ ﹁b (﹁a ∨ b)) as H40.
  pose proof (PT1 Γ ((﹁b ∧ ﹁a) ∨ (﹁b ∧ b)) (﹁b ∧ (﹁a ∨ b)) ((﹁a ∨ b) ∧ ﹁b)) as H41.
  pose proof (MP Γ _ _ H41 H40) as H42. pose proof (MP Γ _ _ H42 H39) as H43.
  pose proof (PT1 Γ (﹁a ∧ ﹁b) ((﹁b ∧ ﹁a) ∨ (﹁b ∧ b)) ((﹁a ∨ b) ∧ ﹁b)) as H44.
  pose proof (MP Γ _ _ H44 H43) as H45. pose proof (MP Γ _ _ H45 H38) as H46.
  pose proof (Hi4 Γ (a ∧ b) (﹁a ∧ ﹁b) ((﹁a ∨ b) ∧ ﹁b)) as H47. pose proof (MP Γ _ _ H47 H46) as H48.
  pose proof (Hi3 Γ (a ∧ b) ((﹁a ∨ b) ∧ ﹁b)) as H49.
  pose proof (PT1 Γ ((a ∧ b) ∨ (﹁a ∧ ﹁b)) ((a ∧ b) ∨ ((﹁a ∨ b) ∧ ﹁b)) (((﹁a ∨ b) ∧ ﹁b) ∨ (a ∧ b))) as H50.
  pose proof (MP Γ _ _ H50 H49) as H51. pose proof (MP Γ _ _ H51 H48) as H52.
  pose proof (Hi4 Γ ((﹁a ∨ b) ∧ ﹁b) (a ∧ b) ((﹁a ∨ b) ∧ a)) as H53. pose proof (MP Γ _ _ H53 H15) as H54.
  pose proof (PT1 Γ ((a ∧ b) ∨ (﹁a ∧ ﹁b)) (((﹁a ∨ b) ∧ ﹁b) ∨ (a ∧ b)) (((﹁a ∨ b) ∧ ﹁b) ∨ ((﹁a ∨ b) ∧ a))) as H55.
  pose proof (MP Γ _ _ H55 H54) as H56. pose proof (MP Γ _ _ H56 H52) as H57.
  pose proof (PT30 Γ (﹁a ∨ b) ﹁b a) as H58.
  pose proof (PT1 Γ ((a ∧ b) ∨ (﹁a ∧ ﹁b)) (((﹁a ∨ b) ∧ ﹁b) ∨ ((﹁a ∨ b) ∧ a)) ((﹁a ∨ b) ∧ (﹁b ∨ a))) as H59.
  pose proof (MP Γ _ _ H59 H58) as H60. pose proof (MP Γ _ _ H60 H57) as H61.
  pose proof (PT13 Γ (﹁a ∨ b) ﹁b) as H62. pose proof (PT29 Γ ﹁b ﹁a b) as H63.
  pose proof (PT13 Γ ﹁b b) as H64. pose proof (Hi4 Γ (﹁b ∧ ﹁a) (﹁b ∧ b) (b ∧ ﹁b)) as H65.
  pose proof (MP Γ _ _ H65 H64) as H66.
  pose proof (PT1 Γ (﹁b ∧ (﹁a ∨ b)) ((﹁b ∧ ﹁a) ∨ (﹁b ∧ b)) ((﹁b ∧ ﹁a) ∨ (b ∧ ﹁b))) as H67.
  pose proof (MP Γ _ _ H67 H66) as H68. pose proof (MP Γ _ _ H68 H63) as H69.
  pose proof (PT13 Γ ﹁b ﹁a) as H70. pose proof (Hi4 Γ (b ∧ ﹁b) (﹁b ∧ ﹁a) (﹁a ∧ ﹁b)) as H71.
  pose proof (MP Γ _ _ H71 H70) as H72. pose proof (Hi3 Γ (﹁b ∧ ﹁a) (b ∧ ﹁b)) as H73.
  pose proof (PT1 Γ ((﹁b ∧ ﹁a) ∨ (b ∧ ﹁b)) ((b ∧ ﹁b) ∨ (﹁b ∧ ﹁a)) ((b ∧ ﹁b) ∨ (﹁a ∧ ﹁b))) as H74.
  pose proof (MP Γ _ _ H74 H72) as H75. pose proof (MP Γ _ _ H75 H73) as H76.
  pose proof (Hi3 Γ (b ∧ ﹁b) (﹁a ∧ ﹁b)) as H77.
  pose proof (PT1 Γ ((﹁b ∧ ﹁a) ∨ (b ∧ ﹁b)) ((b ∧ ﹁b) ∨ (﹁a ∧ ﹁b)) ((﹁a ∧ ﹁b) ∨ (b ∧ ﹁b))) as H78.
  pose proof (MP Γ _ _ H78 H77) as H79. pose proof (MP Γ _ _ H79 H76) as H80.
  pose proof (PT1 Γ (﹁b ∧ (﹁a ∨ b)) ((﹁b ∧ ﹁a) ∨ (b ∧ ﹁b)) ((﹁a ∧ ﹁b) ∨ (b ∧ ﹁b))) as H81.
  pose proof (MP Γ _ _ H81 H80) as H82. pose proof (MP Γ _ _ H82 H69) as H83.
  pose proof (PT1 Γ ((﹁a ∨ b) ∧ ﹁b) (﹁b ∧ (﹁a ∨ b)) ((﹁a ∧ ﹁b) ∨ (b ∧ ﹁b))) as H84.
  pose proof (MP Γ _ _ H84 H83) as H85. pose proof (MP Γ _ _ H85 H62) as H86.
  pose proof (PT40 Γ (﹁a ∧ ﹁b) b) as H87.
  pose proof (PT15 Γ ((﹁a ∧ ﹁b) → ((﹁a ∧ ﹁b) ∨ (b ∧ ﹁b))) (((﹁a ∧ ﹁b) ∨ (b ∧ ﹁b)) → (﹁a ∧ ﹁b))) as H88.
  pose proof (MP Γ _ _ H88 H87) as H89. pose proof (PT1 Γ ((﹁a ∨ b) ∧ ﹁b) ((﹁a ∧ ﹁b) ∨ (b ∧ ﹁b)) (﹁a ∧ ﹁b)) as H90.
  pose proof (MP Γ _ _ H90 H89) as H91. pose proof (MP Γ _ _ H91 H86) as H92.
  pose proof (PT13 Γ (﹁a ∨ b) a) as H93. pose proof (PT29 Γ a ﹁a b) as H94.
  pose proof (PT1 Γ ((﹁a ∨ b) ∧ a) (a ∧ (﹁a ∨ b)) ((a ∧ ﹁a) ∨ (a ∧ b))) as H95.
  pose proof (MP Γ _ _ H95 H94) as H96.  pose proof (MP Γ _ _ H96 H93) as H97.
  pose proof (Hi3 Γ (a ∧ ﹁a) (a ∧ b)) as H98.
  pose proof (PT1 Γ ((﹁a ∨ b) ∧ a) ((a ∧ ﹁a) ∨ (a ∧ b)) ((a ∧ b) ∨ (a ∧ ﹁a))) as H99.
  pose proof (MP Γ _ _ H99 H98) as H100. pose proof (MP Γ _ _ H100 H97) as H101.
  pose proof (PT40 Γ (a ∧ b) a) as H102.
  pose proof (PT15 Γ ((a ∧ b) → ((a ∧ b) ∨ (a ∧ ﹁a))) (((a ∧ b) ∨ (a ∧ ﹁a)) → (a ∧ b))) as H103.
  pose proof (MP Γ _ _ H103 H102) as H104. pose proof (PT1 Γ ((﹁a ∨ b) ∧ a) ((a ∧ b) ∨ (a ∧ ﹁a)) (a ∧ b)) as H105.
  pose proof (MP Γ _ _ H105 H104) as H106. pose proof (MP Γ _ _ H106 H101) as H107.
  pose proof (Hi4 Γ ((﹁a ∨ b) ∧ ﹁b) ((﹁a ∨ b) ∧ a) (a ∧ b)) as H108. pose proof (MP Γ _ _ H108 H107) as H109.
  pose proof (Hi4 Γ (a ∧ b) ((﹁a ∨ b) ∧ ﹁b) (﹁a ∧ ﹁b)) as H110. pose proof (MP Γ _ _ H110 H92) as H111.
  pose proof (Hi3 Γ ((﹁a ∨ b) ∧ ﹁b) (a ∧ b)) as H112.
  pose proof (PT1 Γ (((﹁a ∨ b) ∧ ﹁b) ∨ (a ∧ b)) ((a ∧ b) ∨ ((﹁a ∨ b) ∧ ﹁b)) ((a ∧ b) ∨ (﹁a ∧ ﹁b))) as H113.
  pose proof (MP Γ _ _ H113 H111) as H114. pose proof (MP Γ _ _ H114 H112) as H115.
  pose proof (PT1 Γ (((﹁a ∨ b) ∧ ﹁b) ∨ ((﹁a ∨ b) ∧ a)) (((﹁a ∨ b) ∧ ﹁b) ∨ (a ∧ b)) ((a ∧ b) ∨ (﹁a ∧ ﹁b))) as H116.
  pose proof (MP Γ _ _ H116 H115) as H117. pose proof (MP Γ _ _ H117 H109) as H118.
  pose proof (PT29 Γ (﹁a ∨ b) ﹁b a) as H119.
  pose proof (PT1 Γ ((﹁a ∨ b) ∧ (﹁b ∨ a)) (((﹁a ∨ b) ∧ ﹁b) ∨ ((﹁a ∨ b) ∧ a)) ((a ∧ b) ∨ (﹁a ∧ ﹁b))) as H120.
  pose proof (MP Γ _ _ H120 H118) as H121. pose proof (MP Γ _ _ H121 H119) as H122.
  pose proof (PT21 Γ (((﹁a ∨ b) ∧ (﹁b ∨ a)) → ((a ∧ b) ∨ (﹁a ∧ ﹁b))) (((a ∧ b) ∨ (﹁a ∧ ﹁b)) → ((﹁a ∨ b) ∧ (﹁b ∨ a)))) as H123.
  pose proof (MP Γ _ _ H123 H122) as H124. pose proof (MP Γ _ _ H124 H61). apply H.
Qed.

Theorem PT45: forall Γ a b r, Γ ├Hi ((a → r) ∧ (b → r)) → (a ∨ b) → r.
Proof.
  intros. pose proof (PT11 Γ r ﹁a) as H1. pose proof (PT13 Γ ﹁r ﹁﹁a) as H2.
  pose proof (PT12 Γ ﹁a r) as H3.
  pose proof (PT1 Γ (﹁r ∧ ﹁﹁a) (﹁﹁a ∧ ﹁r) (﹁(﹁a ∨ r))) as H4.
  pose proof (MP Γ _ _ H4 H3) as H5. pose proof (MP Γ _ _ H5 H2) as H6.
  pose proof (PT1 Γ (﹁(r ∨ ﹁a)) (﹁r ∧ ﹁﹁a) (﹁(﹁a ∨ r))) as H7.
  pose proof (MP Γ _ _ H7 H6) as H8. pose proof (MP Γ _ _ H8 H1) as H9.
  pose proof (PT11 Γ r ﹁b) as H10. pose proof (PT13 Γ ﹁r ﹁﹁b) as H11.
  pose proof (PT12 Γ ﹁b r) as H12.
  pose proof (PT1 Γ (﹁r ∧ ﹁﹁b) (﹁﹁b ∧ ﹁r) (﹁(﹁b ∨ r))) as H13.
  pose proof (MP Γ _ _ H13 H12) as H14. pose proof (MP Γ _ _ H14 H11) as H15.
  pose proof (PT1 Γ (﹁(r ∨ ﹁b)) (﹁r ∧ ﹁﹁b) (﹁(﹁b ∨ r))) as H16.
  pose proof (MP Γ _ _ H16 H15) as H17. pose proof (MP Γ _ _ H17 H10) as H18.
  pose proof (Hi4 Γ (﹁(r ∨ ﹁a)) (﹁(r ∨ ﹁b)) (﹁(﹁b ∨ r))) as H19.
  pose proof (MP Γ _ _ H19 H18) as H20.
  pose proof (Hi4 Γ (﹁(﹁b ∨ r)) (﹁(r ∨ ﹁a)) (﹁(﹁a ∨ r))) as H21.
  pose proof (MP Γ _ _ H21 H9) as H22.
  pose proof (Hi3 Γ (﹁(r ∨ ﹁a)) (﹁(﹁b ∨ r))) as H23.
  pose proof (PT1 Γ (﹁(r ∨ ﹁a) ∨ ﹁(﹁b ∨ r)) (﹁(﹁b ∨ r) ∨ ﹁(r ∨ ﹁a)) (﹁(﹁b ∨ r) ∨ ﹁(﹁a ∨ r))) as H24.
  pose proof (MP Γ _ _ H24 H22) as H25. pose proof (MP Γ _ _ H25 H23) as H26.
  pose proof (Hi3 Γ (﹁(﹁b ∨ r)) (﹁(﹁a ∨ r))) as H27.
  pose proof (PT1 Γ (﹁(r ∨ ﹁a) ∨ ﹁(﹁b ∨ r)) (﹁(﹁b ∨ r) ∨ ﹁(﹁a ∨ r)) (﹁(﹁a ∨ r) ∨ ﹁(﹁b ∨ r))) as H28.
  pose proof (MP Γ _ _ H28 H27) as H29. pose proof (MP Γ _ _ H29 H26) as H30.
  pose proof (PT1 Γ (﹁(r ∨ ﹁a) ∨ ﹁(r ∨ ﹁b)) (﹁(r ∨ ﹁a) ∨ ﹁(﹁b ∨ r)) (﹁(﹁a ∨ r) ∨ ﹁(﹁b ∨ r))) as H31.
  pose proof (MP Γ _ _ H31 H30) as H32. pose proof (MP Γ _ _ H32 H20) as H33.
  pose proof (PT7 Γ (﹁(r ∨ ﹁a) ∨ ﹁(r ∨ ﹁b)) (﹁(﹁a ∨ r) ∨ ﹁(﹁b ∨ r))) as H34. pose proof (MP Γ _ _ H34 H33) as H35.
  pose proof (PT28 Γ r ﹁a ﹁b) as H36. pose proof (PT12 Γ a b) as H37.
  pose proof (Hi4 Γ r (﹁a ∧ ﹁b) ﹁(a ∨ b)) as H38. pose proof (MP Γ _ _ H38 H37) as H39.
  pose proof (Hi3 Γ r ﹁(a ∨ b)) as H40.
  pose proof (PT1 Γ (r ∨ (﹁a ∧ ﹁b)) (r ∨ ﹁(a ∨ b)) (﹁(a ∨ b) ∨ r)) as H41.
  pose proof (MP Γ _ _ H41 H40) as H42. pose proof (MP Γ _ _ H42 H39) as H43.
  pose proof (PT1 Γ ((r ∨ ﹁a) ∧ (r ∨ ﹁b)) (r ∨ (﹁a ∧ ﹁b)) (﹁(a ∨ b) ∨ r)) as H44.
  pose proof (MP Γ _ _ H44 H43) as H45. pose proof (MP Γ _ _ H45 H36) as H46.
  pose proof (PT1 Γ ((﹁a ∨ r) ∧ (﹁b ∨ r)) ((r ∨ ﹁a) ∧ (r ∨ ﹁b)) (﹁(a ∨ b) ∨ r)) as H47.
  pose proof (MP Γ _ _ H47 H46) as H48. pose proof (MP Γ _ _ H48 H35). apply H.
Qed.




























