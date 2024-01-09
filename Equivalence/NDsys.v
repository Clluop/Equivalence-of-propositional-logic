Require Import Base.  
Require Import Coq.Sets.Ensembles.

Inductive prove_ND (Г : Ensemble Formula) :Formula -> Prop :=
|ND0 :  forall a, a ∈ Г -> prove_ND Г a  
|ND1 :  forall a b,  prove_ND (Г ∪ [a]) b -> prove_ND Г (a → b)
|ND2 :  forall a b, prove_ND Г a -> prove_ND Г (a → b) -> prove_ND Г b
|ND31 : forall a b, prove_ND Г a -> prove_ND Г (a ∨ b)
|ND32 : forall a b, prove_ND Г a -> prove_ND Г (b ∨ a)
|ND4 :  forall a b r, prove_ND Г (a ∨ b) -> prove_ND Г (a → r)
                    -> prove_ND Г (b → r) -> prove_ND Г r
|ND5 :  forall a b, prove_ND Г a -> prove_ND Г b -> prove_ND Г (a ∧ b)
|ND61 : forall a b, prove_ND Г (a ∧ b) -> prove_ND Г a
|ND62 : forall a b, prove_ND Г (a ∧ b) -> prove_ND Г b
|ND7 :  forall a b, prove_ND Г (a → b) -> prove_ND Г (b → a) 
                  -> prove_ND Г (a ↔ b)
|ND81 : forall a b, prove_ND Г (a ↔ b) -> prove_ND Г a -> prove_ND Г b
|ND82 : forall a b, prove_ND Г (a ↔ b) -> prove_ND Г b -> prove_ND Г a
|ND83 : forall a b, prove_ND Г (a ↔ b) -> prove_ND Г (a → b)
|ND84 : forall a b, prove_ND Г (a ↔ b) -> prove_ND Г (b → a)
|ND9 :  forall a b, prove_ND (Г ∪ [﹁ a]) b-> prove_ND (Г ∪ [﹁ a]) ﹁ b 
                   -> prove_ND Г a.

Notation "Г ├ND a" := (prove_ND Г a) (at level 80).
Notation " ├ND a" := (prove_ND Φ a)(at level 80).
(*
Lemma Uequal1: forall {U} (A ND : Ensemble U), A ∪ ND = ND ∪ A.
Lemma Uequal2: forall {U} (A ND C : Ensemble U), (A ∪ ND) ∪ C = A ∪ (ND ∪ C).
Lemma Uequal3: forall {U} (A ND C : Ensemble U), (A ∪ ND) ∪ C = (A ∪ C) ∪ ND.

*)
Lemma NDUnion_ass1: forall A ND a, A ∪ ND ├ND a <-> ND ∪ A ├ND a.
Proof. intros. rewrite Uequal1. split; intros; apply H. Qed.

Lemma NDUnion_l: forall Г a, Г ├ND a -> forall A, Г ∪ A ├ND a.
Proof.
  intros. induction H.
  - pose proof (Union_introl _ Г A a). pose proof (ND0 (Г ∪ A) a). 
    apply H1,H0,H.
  - apply ND1. rewrite Uequal3. apply IHprove_ND.
  - pose proof (ND2 (Г ∪ A) a b). apply H1.
    apply IHprove_ND1. apply IHprove_ND2.
  - apply (ND31 (Г ∪ A) a b). apply IHprove_ND.
  - apply (ND32 (Г ∪ A) a b). apply IHprove_ND.
  - apply (ND4 (Г ∪ A) a b r). 
    apply IHprove_ND1. apply IHprove_ND2. apply IHprove_ND3.
  - apply (ND5 (Г ∪ A) a b). apply IHprove_ND1. apply IHprove_ND2.
  - apply (ND61 (Г ∪ A) a b). apply IHprove_ND.
  - apply (ND62 (Г ∪ A) a b). apply IHprove_ND.
  - apply (ND7 (Г ∪ A) a b). apply IHprove_ND1. apply IHprove_ND2.
  - apply (ND81 (Г ∪ A) a b). apply IHprove_ND1. apply IHprove_ND2.
  - apply (ND82 (Г ∪ A) a b). apply IHprove_ND1. apply IHprove_ND2.
  - apply (ND83 (Г ∪ A) a b). apply IHprove_ND.
  - apply (ND84 (Г ∪ A) a b). apply IHprove_ND.
  - rewrite Uequal3 in IHprove_ND1. rewrite Uequal2 in IHprove_ND2. 
    rewrite Uequal1 with (A0:= [﹁ a]) in IHprove_ND2.
    rewrite <- Uequal2 in IHprove_ND2.
    apply ND9 with b. apply IHprove_ND1. apply IHprove_ND2.
Qed.

Fact NDUnion_r: forall Г a, Г ├ND a -> forall A, A ∪ Г ├ND a.
Proof.
  intros. induction H.
  - pose proof (Union_intror _ A Г a). pose proof (ND0 (A ∪ Г) a). 
    apply H1,H0,H.
  - apply ND1. rewrite Uequal2. apply IHprove_ND.
  - pose proof (ND2 (A ∪ Г) a b). apply H1. 
    apply IHprove_ND1. apply IHprove_ND2.
  - apply (ND31 (A ∪ Г) a b). apply IHprove_ND.
  - apply (ND32 (A ∪ Г) a b). apply IHprove_ND.
  - apply (ND4 (A ∪ Г) a b r). 
    apply IHprove_ND1. apply IHprove_ND2. apply IHprove_ND3.
  - apply (ND5 (A ∪ Г) a b). apply IHprove_ND1. apply IHprove_ND2.
  - apply (ND61 (A ∪ Г) a b). apply IHprove_ND.
  - apply (ND62 (A ∪ Г) a b). apply IHprove_ND.
  - apply (ND7 (A ∪ Г) a b). apply IHprove_ND1. apply IHprove_ND2.
  - apply (ND81 (A ∪ Г) a b). apply IHprove_ND1. apply IHprove_ND2.
  - apply (ND82 (A ∪ Г) a b). apply IHprove_ND1. apply IHprove_ND2.
  - apply (ND83 (A ∪ Г) a b). apply IHprove_ND.
  - apply (ND84 (A ∪ Г) a b). apply IHprove_ND.
  - rewrite <- Uequal2 in IHprove_ND1, IHprove_ND2. 
    apply ND9 with b. apply IHprove_ND1. apply IHprove_ND2.
Qed.

(*----------------------- Theorem -------------------------*)
(*Hi Axiom I*)
Theorem NTHi1: forall Γ a, Γ ├ND a ∨ a → a.
Proof.
  intros. assert(H1: ([a ∨ a] ∪ [a]) a).
  { apply (Union_intror _ [a ∨ a] [a] a). reflexivity. }
  apply ND0 in H1. apply ND1 in H1. 
  assert (H2: [a ∨ a] a ∨ a). { reflexivity. }
  apply ND0 in H2. pose proof (ND4 [a ∨ a] _ _ _ H2 H1 H1). 
  apply ND1. apply NDUnion_r. apply H.
Qed.

(*Hi Axiom II*)
Theorem NTHi2: forall Γ a b, Γ ├ND a → a ∨ b.
Proof.
  intros. assert(H1: [a] a). { reflexivity. } apply ND0 in H1. 
  pose proof (ND31 [a] a b H1). apply ND1. apply NDUnion_r. apply H.
Qed.

(*Hi Axiom III*)
Theorem NTHi3: forall Γ a b, Γ ├ND a ∨ b → b ∨ a.
Proof.
  intros. assert(H1:([a ∨ b] ∪ [a]) a). 
  { apply (Union_intror _ _ _ a). reflexivity. }
  apply ND0 in H1. apply (ND32 _ _ b) in H1. apply ND1 in H1. 
  assert(H2:([a ∨ b] ∪ [b]) b). 
  { apply (Union_intror _ _ _ b). reflexivity. }
  apply ND0 in H2. apply (ND31 _ b a) in H2. apply ND1 in H2.
  assert (H3: [a ∨ b] (a ∨ b)). { reflexivity. } apply ND0 in H3.
  pose proof (ND4 _ _ _ _ H3 H1 H2). apply ND1. apply NDUnion_r. apply H.
Qed.
 
(*Hi Axiom IV*)
Theorem NTHi4: forall Γ a b r, Γ ├ND (b → r) → (a ∨ b → a ∨ r).
Proof.
  intros. assert(H1:([b → r] ∪ [a ∨ b] ∪ [a]) a). 
  { apply (Union_intror _). reflexivity. } apply ND0 in H1. 
  apply (ND31 _ _ r) in H1. apply ND1 in H1.
  assert(H2:([b → r] ∪ [a ∨ b] ∪ [b]) b). 
  { apply (Union_intror _). reflexivity. } apply ND0 in H2.
  assert(H3:([b → r] ∪ [a ∨ b] ∪ [b]) (b → r)). 
  { apply (Union_introl _). apply (Union_introl _). reflexivity. }
   apply ND0 in H3. pose proof (ND2 _ _ _ H2 H3) as H4.
   apply (ND32 _ r a) in H4. apply ND1 in H4.
  assert(H5:([b → r] ∪ [a ∨ b]) (a ∨ b)). 
  { apply (Union_intror _). reflexivity. } apply ND0 in H5.
  pose proof (ND4 _ _ _ _ H5 H1 H4) as H6. apply ND1 in H6.
  apply ND1. apply NDUnion_r. apply H6.
Qed.

