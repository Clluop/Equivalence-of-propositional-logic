Require Import Base.
Require Import Coq.Sets.Ensembles.
Require Import Hisys.
Require Import NDsys.

Theorem ND_to_Hi: forall Γ a, Γ ├Hi a -> Γ ├ND a.
Proof.
  intros. induction H.
  - apply ND0. apply H.
  - apply NTHi1.
  - apply NTHi2.
  - apply NTHi3.
  - apply NTHi4.
  - apply (ND2 Γ a b).
    + apply IHprove_Hi2.
    + apply IHprove_Hi1.
Qed.

Theorem deductive_ND: forall Γ a b, Γ ∪ [a] ├ND b -> Γ ├ND a → b.
Proof.
  intros. apply ND1 in H. apply H.
Qed.

Theorem ni_deductive_ND: forall Γ a b, Γ ├ND a → b -> Γ ∪ [a] ├ND b.
Proof.
  intros. assert(Γ ∪ [a] ├ND a → b).
  { apply NDUnion_l. apply H. }
  assert(Γ ∪ [a] ├ND a).
  { apply NDUnion_r. apply ND0. reflexivity. }
  pose proof (ND2 (Γ ∪ [a]) _ _ H1 H0). apply H2. 
Qed.

Theorem PT_con_dis: forall Γ a b r, Γ ├Hi (a → (b → r)) → ((a → b) → (a → r)).
Proof.
  intros. pose proof (Hi3 Γ a ﹁a) as H1. pose proof (PT7 Γ (a ∨ ﹁a) (﹁a ∨ a)) as H2.
  pose proof (MP Γ _ _ H2 H1) as H3.
  pose proof (Hi4 Γ (﹁(﹁a ∨ ﹁b)) (﹁(﹁a ∨ a)) (﹁(a ∨ ﹁a))) as H4.
  pose proof (MP Γ _ _ H4 H3) as H5.
  pose proof (PT7 Γ (﹁(﹁a ∨ ﹁b) ∨ ﹁(﹁a ∨ a)) (﹁(﹁a ∨ ﹁b) ∨ ﹁(a ∨ ﹁a))) as H6.
  pose proof (MP Γ _ _ H6 H5) as H7. pose proof (PT39 Γ (﹁a ∨ ﹁b) a) as H8.
  pose proof (PT14 Γ ((﹁a ∨ ﹁b) → ((﹁a ∨ ﹁b) ∧ (a ∨ ﹁a))) (((﹁a ∨ ﹁b) ∧ (a ∨ ﹁a)) → (﹁a ∨ ﹁b))) as H9.
  pose proof (MP Γ _ _ H9 H8) as H10.
  pose proof (PT1 Γ (﹁a ∨ ﹁b) ((﹁a ∨ ﹁b) ∧ (a ∨ ﹁a)) ((﹁a ∨ ﹁b) ∧ (﹁a ∨ a))) as H11.
  pose proof (MP Γ _ _ H11 H7) as H12. pose proof (MP Γ _ _ H12 H10) as H13.
  pose proof (PT13 Γ (﹁a ∨ ﹁b) (﹁a ∨ a)) as H14.
  pose proof (PT1 Γ (﹁a ∨ ﹁b) ((﹁a ∨ ﹁b) ∧ (﹁a ∨ a)) ((﹁a ∨ a) ∧ (﹁a ∨ ﹁b))) as H15.
  pose proof (MP Γ _ _ H15 H14) as H16. pose proof (MP Γ _ _ H16 H13) as H17.
  pose proof (PT28 Γ ﹁a a ﹁b) as H18. pose proof (Hi3 Γ ﹁a (a ∧ ﹁b)) as H19.
  pose proof (PT1 Γ ((﹁a ∨ a) ∧ (﹁a ∨ ﹁b)) (﹁a ∨ (a ∧ ﹁b)) ((a ∧ ﹁b) ∨ ﹁a)) as H20.
  pose proof (MP Γ _ _ H20 H19) as H21. pose proof (MP Γ _ _ H21 H18) as H22.
  pose proof (PT1 Γ (﹁a ∨ ﹁b) ((﹁a ∨ a) ∧ (﹁a ∨ ﹁b)) ((a ∧ ﹁b) ∨ ﹁a)) as H23.
  pose proof (MP Γ _ _ H23 H22) as H24. pose proof (MP Γ _ _ H24 H17) as H25. 
  pose proof (Hi4 Γ r (﹁a ∨ ﹁b) ((a ∧ ﹁b) ∨ ﹁a)) as H26. pose proof (MP Γ _ _ H26 H25) as H27.
  pose proof (Hi3 Γ (﹁a ∨ ﹁b) r) as H28.
  pose proof (PT1 Γ ((﹁a ∨ ﹁b) ∨ r) (r ∨ (﹁a ∨ ﹁b)) (r ∨ ((a ∧ ﹁b) ∨ ﹁a))) as H29.
  pose proof (MP Γ _ _ H29 H27) as H30. pose proof (MP Γ _ _ H30 H28) as H31.
  pose proof (Hi3 Γ r ((a ∧ ﹁b) ∨ ﹁a)) as H32.
  pose proof (PT1 Γ ((﹁a ∨ ﹁b) ∨ r) (r ∨ ((a ∧ ﹁b) ∨ ﹁a)) (((a ∧ ﹁b) ∨ ﹁a) ∨ r)) as H33.
  pose proof (MP Γ _ _ H33 H32) as H34. pose proof (MP Γ _ _ H34 H31) as H35.
  pose proof (PT17 Γ ﹁a ﹁b r) as H36.
  pose proof (PT1 Γ (﹁a ∨ (﹁b ∨ r)) ((﹁a ∨ ﹁b) ∨ r) (((a ∧ ﹁b) ∨ ﹁a) ∨ r)) as H37.
  pose proof (MP Γ _ _ H37 H35) as H38. pose proof (MP Γ _ _ H38 H36) as H39.
  pose proof (PT18 Γ (a ∧ ﹁b) ﹁a r) as H40.
  pose proof (PT1 Γ (﹁a ∨ (﹁b ∨ r)) (((a ∧ ﹁b) ∨ ﹁a) ∨ r) ((a ∧ ﹁b) ∨ (﹁a ∨ r))) as H41.
  pose proof (MP Γ _ _ H41 H40) as H42. pose proof (MP Γ _ _ H42 H39) as H43.
  pose proof (PT5 Γ b) as H44. pose proof (Hi4 Γ ﹁a b ﹁﹁b) as H45.
  pose proof (MP Γ _ _ H45 H44) as H46. pose proof (PT7 Γ (﹁a ∨ b) (﹁a ∨ ﹁﹁b)) as H47.
  pose proof (MP Γ _ _ H47 H46) as H48. pose proof (Hi4 Γ (﹁a ∨ r) (﹁(﹁a ∨ ﹁﹁b)) (﹁(﹁a ∨ b))) as H49.
  pose proof (MP Γ _ _ H49 H48) as H50. pose proof (Hi3 Γ (﹁(﹁a ∨ ﹁﹁b)) (﹁a ∨ r)) as H51.
  pose proof (PT1 Γ (﹁(﹁a ∨ ﹁﹁b) ∨ (﹁a ∨ r)) ((﹁a ∨ r) ∨ ﹁(﹁a ∨ ﹁﹁b)) ((﹁a ∨ r) ∨ ﹁(﹁a ∨ b))) as H52.
  pose proof (MP Γ _ _ H52 H50) as H53. pose proof (MP Γ _ _ H53 H51) as H54.
  pose proof (Hi3 Γ (﹁a ∨ r) ﹁(﹁a ∨ b)) as H55.
  pose proof (PT1 Γ (﹁(﹁a ∨ ﹁﹁b) ∨ (﹁a ∨ r)) ((﹁a ∨ r) ∨ ﹁(﹁a ∨ b)) (﹁(﹁a ∨ b) ∨ (﹁a ∨ r))) as H56.
  pose proof (MP Γ _ _ H56 H55) as H57. pose proof (MP Γ _ _ H57 H54) as H58.
  pose proof (PT1 Γ (﹁a ∨ (﹁b ∨ r)) (﹁(﹁a ∨ ﹁﹁b) ∨ (﹁a ∨ r)) (﹁(﹁a ∨ b) ∨ (﹁a ∨ r))) as H59.
  pose proof (MP Γ _ _ H59 H58) as H60. pose proof (MP Γ _ _ H60 H43). apply H.
Qed. 

Theorem deductive_Hi: forall Γ a b, Γ ∪ [a] ├Hi b -> Γ ├Hi a → b.
Proof.
  intros. induction H.
    + destruct H.
      * pose proof (Hi0 Γ x). pose proof (Hi2 Γ x ﹁a). 
        pose proof (Hi3 Γ x ﹁a). apply H0 in H. 
        pose proof (MP Γ _ _ H1 H). pose proof (MP Γ _ _ H2 H3). apply H4.
      * apply Single in H. rewrite H. pose proof (Hi1 Γ a).
        pose proof (Hi2 Γ a a). pose proof (Hi4 Γ ﹁a (a ∨ a) a).
        pose proof (MP Γ _ _ H2 H0). pose proof (MP Γ _ _ H3 H1). apply H4.
    + pose proof (Hi1 Γ a0). pose proof (PT41 Γ (a0 ∨ a0 → a0) a).
      pose proof (MP Γ _ _ H0 H). apply H1.
    + pose proof (Hi2 Γ a0 b). pose proof (PT41 Γ (a0 → a0 ∨ b) a).
      pose proof (MP Γ _ _ H0 H). apply H1.
    + pose proof (Hi3 Γ a0 b). pose proof (PT41 Γ (a0 ∨ b → b ∨ a0) a).
      pose proof (MP Γ _ _ H0 H). apply H1.
    + pose proof (Hi4 Γ a0 b r). pose proof (PT41 Γ (b → r) → a0 ∨ b → a0 ∨ r a).
      pose proof (MP Γ _ _ H0 H). apply H1.
    + pose proof (PT_con_dis Γ a a0 b). pose proof (MP Γ _ _ H1 IHprove_Hi1).
      pose proof (MP Γ _ _ H2 IHprove_Hi2). apply H3.
Qed.


Theorem ni_deductive_Hi: forall Γ a b, Γ ├Hi a → b ->  Γ ∪ [a] ├Hi b.
Proof.
  intros. assert(H':Γ ∪ [a] ├Hi a).
  { apply Hi0. apply Union_intror. reflexivity. }
  assert(H'':Γ ∪ [a] ├Hi a → b).
  { apply HiUnion_l. apply H. }
  pose proof (MP (Γ ∪ [a]) _ _ H'' H'). apply H0.
Qed.

Theorem PT_dilemma: forall Γ a b r, Γ ├Hi (a → r) → (b → r) → (a ∨ b) → r.
Proof.
  intros. pose proof (PT45 Γ a b r) as H1.
  pose proof (PT24 Γ (a → r) (b → r) ((a ∨ b) → r)) as H2.
  pose proof (MP Γ _ _ H2 H1). apply H.
Qed.

Theorem PT_contradiction: forall Г a b, Г ├Hi (﹁a → b) → (﹁a → ﹁b) → a.
Proof.
  intros. pose proof (PT5 Г ﹁a) as H1. pose proof (Hi4 Г a ﹁a ﹁﹁﹁a) as H2.
  pose proof (MP Г _ _ H2 H1) as H3. pose proof (PT7 Г (a ∨ ﹁a) (a ∨ ﹁﹁﹁a)) as H4.
  pose proof (MP Г _ _ H4 H3) as H5.
  pose proof (Hi4 Г (﹁(a ∨ ﹁﹁b)) (﹁(a ∨ ﹁﹁﹁a)) (﹁(a ∨ ﹁a))) as H6. 
  pose proof (MP Г _ _ H6 H5) as H7.
  pose proof (PT7 Г (﹁(a ∨ ﹁﹁b) ∨ ﹁(a ∨ ﹁﹁﹁a)) (﹁(a ∨ ﹁﹁b) ∨ ﹁(a ∨ ﹁a))) as H8.
  pose proof (MP Г _ _ H8 H7) as H9. pose proof (PT13 Г (a ∨ ﹁﹁b) (a ∨ ﹁﹁﹁a)) as H10.
  pose proof (PT28 Г a ﹁﹁﹁a ﹁﹁b) as H11. pose proof (PT12 Г ﹁﹁a ﹁b) as H12.
  pose proof (Hi4 Г a (﹁﹁﹁a ∧ ﹁﹁b) ﹁(﹁﹁a ∨ ﹁b)) as H13. pose proof (MP Г _ _ H13 H12) as H14.
  pose proof (PT1 Г ((a ∨ ﹁﹁﹁a) ∧ (a ∨ ﹁﹁b)) (a ∨ (﹁﹁﹁a ∧ ﹁﹁b)) (a ∨ ﹁(﹁﹁a ∨ ﹁b))) as H15.
  pose proof (MP Г _ _ H15 H14) as H16. pose proof (MP Г _ _ H16 H11) as H17.
  pose proof (Hi3 Г a ﹁(﹁﹁a ∨ ﹁b)) as H18.
  pose proof (PT1 Г ((a ∨ ﹁﹁﹁a) ∧ (a ∨ ﹁﹁b)) (a ∨ ﹁(﹁﹁a ∨ ﹁b)) (﹁(﹁﹁a ∨ ﹁b) ∨ a)) as H19.
  pose proof (MP Г _ _ H19 H18) as H20. pose proof (MP Г _ _ H20 H17) as H21.
  pose proof (PT1 Г ((a ∨ ﹁﹁b) ∧ (a ∨ ﹁﹁﹁a)) ((a ∨ ﹁﹁﹁a) ∧ (a ∨ ﹁﹁b)) (﹁(﹁﹁a ∨ ﹁b) ∨ a)) as H22.
  pose proof (MP Г _ _ H22 H21) as H23. pose proof (MP Г _ _ H23 H10) as H24.
  pose proof (PT1 Г ((a ∨ ﹁﹁b) ∧ (a ∨ ﹁a)) ((a ∨ ﹁﹁b) ∧ (a ∨ ﹁﹁﹁a)) (﹁(﹁﹁a ∨ ﹁b) ∨ a)) as H25.
  pose proof (MP Г _ _ H25 H24) as H26. pose proof (MP Г _ _ H26 H9) as H27.
  pose proof (PT39 Г (a ∨ ﹁﹁b) a) as H28.
  pose proof (PT14 Г ((a ∨ ﹁﹁b) → ((a ∨ ﹁﹁b) ∧ (a ∨ ﹁a))) (((a ∨ ﹁﹁b) ∧ (a ∨ ﹁a)) → (a ∨ ﹁﹁b))) as H29.
  pose proof (MP Г _ _ H29 H28) as H30. pose proof (PT5 Г b) as H31.
  pose proof (Hi4 Г a b ﹁﹁b) as H32. pose proof (MP Г _ _ H32 H31) as H33.
  pose proof (PT6 Г a) as H34. pose proof (Hi4 Г b ﹁﹁a a) as H35.
  pose proof (MP Г _ _ H35 H34) as H36. pose proof (Hi3 Г ﹁﹁a b) as H37.
  pose proof (PT1 Г (﹁﹁a ∨ b) (b ∨ ﹁﹁a) (b ∨ a)) as H38.
  pose proof (MP Г _ _ H38 H36) as H39. pose proof (MP Г _ _ H39 H37) as H40.
  pose proof (Hi3 Г b a) as H41. pose proof (PT1 Г (﹁﹁a ∨ b) (b ∨ a) (a ∨ b)) as H42.
  pose proof (MP Г _ _ H42 H41) as H43. pose proof (MP Г _ _ H43 H40) as H44.
  pose proof (PT1 Г (﹁﹁a ∨ b) (a ∨ b) (a ∨ ﹁﹁b)) as H45.
  pose proof (MP Г _ _ H45 H33) as H46. pose proof (MP Г _ _ H46 H44) as H47.
  pose proof (PT1 Г (﹁﹁a ∨ b) (a ∨ ﹁﹁b) ((a ∨ ﹁﹁b) ∧ (a ∨ ﹁a))) as H48.
  pose proof (MP Г _ _ H48 H30) as H49. pose proof (MP Г _ _ H49 H47) as H50.
  pose proof (PT1 Г (﹁﹁a ∨ b) ((a ∨ ﹁﹁b) ∧ (a ∨ ﹁a)) (﹁(﹁﹁a ∨ ﹁b) ∨ a)) as H51.
  pose proof (MP Г _ _ H51 H27) as H52. pose proof (MP Г _ _ H52 H50). apply H.
Qed.

Theorem Hi_to_ND: forall Γ a, Γ ├ND a -> Γ ├Hi a.
Proof.
  intros. induction H.
  - apply Hi0. apply H.
  - apply deductive_Hi. apply IHprove_ND.
  - pose proof (MP Г _ _ IHprove_ND2 IHprove_ND1). apply H1.
  - pose proof (Hi2 Г a b). pose proof (MP Г _ _ H0 IHprove_ND). apply H1.
  - pose proof (PT10 Г a b). pose proof (MP Г _ _ H0 IHprove_ND). apply H1.
  - pose proof (PT_dilemma Г a b r) as H2. 
    pose proof (MP Г _ _ H2 IHprove_ND2) as H3.
    pose proof (MP Г _ _ H3 IHprove_ND3) as H4.
    pose proof (MP Г _ _ H4 IHprove_ND1). apply H5.
  - pose proof (PT21 Г a b) as H1. 
    pose proof (MP Г _ _ H1 IHprove_ND1) as H2.
    pose proof (MP Г _ _ H2 IHprove_ND2) as H3. apply H3.
  - pose proof (PT14 Г a b). 
    pose proof (MP Г _ _ H0 IHprove_ND) as H1. apply H1.
  - pose proof (PT15 Г a b). 
    pose proof (MP Г _ _ H0 IHprove_ND) as H1. apply H1.
  - pose proof (PT21 Г (a → b) (b → a)) as H1.
    pose proof (MP Г _ _ H1 IHprove_ND1) as H2.
    pose proof (MP Г _ _ H2 IHprove_ND2) as H3. apply H3.
  - pose proof (PT14 Г (a → b) (b → a)) as H1.
    pose proof (MP Г _ _ H1 IHprove_ND1) as H2.
    pose proof (MP Г _ _ H2 IHprove_ND2) as H3. apply H3.
  - pose proof (PT15 Г (a → b) (b → a)) as H1.
    pose proof (MP Г _ _ H1 IHprove_ND1) as H2.
    pose proof (MP Г _ _ H2 IHprove_ND2) as H3. apply H3.
  - pose proof (PT14 Г (a → b) (b → a)) as H1.
    pose proof (MP Г _ _ H1 IHprove_ND) as H2. apply H2.
  - pose proof (PT15 Г (a → b) (b → a)) as H1.
    pose proof (MP Г _ _ H1 IHprove_ND) as H2. apply H2.
  - apply deductive_Hi in IHprove_ND1. apply deductive_Hi in IHprove_ND2.
    pose proof (PT_contradiction Г a b) as H1.
    pose proof (MP Г _ _ H1 IHprove_ND1) as H2.
    pose proof (MP Г _ _ H2 IHprove_ND2) as H3. apply H3.
Qed.

Theorem Equivalent: forall Γ a, Γ ├ND a <-> Γ ├Hi a.
Proof.
  intros. split.
  - apply Hi_to_ND.
  - apply ND_to_Hi.
Qed.

Example Equ_Example: forall Γ a, 
  (exists b, Γ ∪ [﹁a] ├Hi b /\ Γ ∪ [﹁a] ├Hi ﹁b) <-> Γ ├Hi a.
Proof.
  intros. split.
  - intros. destruct H as [b [H1 H2]].
    apply Equivalent. apply Equivalent in H1,H2. apply ND9 with b.
    + apply H1.
    + apply H2.
  - intros. exists a. split.
    + apply HiUnion_l. apply H.
    + apply Hi0. apply Union_intror. reflexivity.
Qed.

Lemma Lemma1: forall Γ a b, Γ ├Hi ﹁b → (b → a).
Proof.
  assert (H0: forall Γ a b, Γ ├Hi a → (b → a)).
  { intros. pose proof (Hi2 Γ a ﹁b) as H1. pose proof (Hi3 Γ a ﹁b) as H2.
  pose proof (PT1 Γ a (a ∨ ﹁b) (﹁b ∨ a)) as H3.
  pose proof (MP Γ _ _ H3 H2) as H4.  pose proof (MP Γ _ _ H4 H1). apply H. }
  assert (H1: forall Γ a b, Γ ├Hi (﹁a → ﹁b) → (b → a)).
  { intros. pose proof (PT6 Γ a) as H1. 
  pose proof (Hi4 Γ ﹁b ﹁﹁a a) as H2. pose proof (MP Γ _ _ H2 H1) as H3.
  pose proof (Hi3 Γ ﹁﹁a ﹁b) as H4.
  pose proof (PT1 Γ (﹁﹁a ∨ ﹁b) (﹁b ∨ ﹁﹁a) (﹁b ∨ a)) as H5.
  pose proof (MP Γ _ _ H5 H3) as H6. 
  pose proof (MP Γ _ _ H6 H4). apply H. }
  intros. pose proof H1 Γ a b. pose proof H0 Γ ((﹁ a → ﹁ b) → b → a) ﹁b.
  pose proof MP _ _ _ H2 H.
  pose proof PT_con_dis Γ ﹁b (﹁ a → ﹁ b) (b → a).
  pose proof MP _ _ _ H4 H3. pose proof H0 Γ ﹁b ﹁a.
  pose proof MP _ _ _ H5 H6. apply H7.
Qed.

Lemma Lemma2: forall Γ a, Γ ├Hi (﹁a → a) → a.
Proof.
  assert (H0: forall Γ a b, Γ ├Hi (﹁a → ﹁b) → (b → a)).
  { intros. pose proof (PT6 Γ a) as H1. 
  pose proof (Hi4 Γ ﹁b ﹁﹁a a) as H2. pose proof (MP Γ _ _ H2 H1) as H3.
  pose proof (Hi3 Γ ﹁﹁a ﹁b) as H4.
  pose proof (PT1 Γ (﹁﹁a ∨ ﹁b) (﹁b ∨ ﹁﹁a) (﹁b ∨ a)) as H5.
  pose proof (MP Γ _ _ H5 H3) as H6. 
  pose proof (MP Γ _ _ H6 H4). apply H. }
  intros. pose proof Lemma1 Γ ﹁(﹁a → a) a.
  pose proof PT_con_dis Γ ﹁a a ﹁(﹁a → a).
  pose proof MP _ _ _ H1 H. apply ni_deductive_Hi in H2.
  pose proof H0 (Γ ∪ [﹁ a → a]) a (﹁a → a).
  pose proof MP _ _ _ H3 H2.
  assert (Γ ∪ [﹁ a → a] ├Hi (﹁ a → a)).
  { apply Hi0. apply Union_intror. reflexivity. }
  pose proof MP _ _ _ H4 H5. apply deductive_Hi in H6. apply H6.
Qed.

Example Equ_Example': forall Γ a, 
  (exists b, Γ ∪ [﹁a] ├Hi b /\ Γ ∪ [﹁a] ├Hi ﹁b) <-> Γ ├Hi a.
Proof.
  intros. split.
  - intros. destruct H as [b [H1 H2]].
    pose proof Lemma1 (Γ ∪ [﹁ a]) a b.
    pose proof MP _ _ _ H H2. pose proof MP _ _ _ H0 H1.
    apply deductive_Hi in H3. pose proof Lemma2 Γ a.
    pose proof MP _ _ _ H4 H3. apply H5.
  - intros. exists a. split.
    + apply HiUnion_l. apply H.
    + apply Hi0. apply Union_intror. reflexivity.
Qed.
