Require Import Coq.Sets.Ensembles.

Notation "a ∈ A" := (In _ A a) (at level 10).
Notation "A ∪ B" := (Union _ A B) (at level 40, left associativity).
Notation "[ a ]" := (Singleton _ a) (at level 0, right associativity).
Notation "A ⊆ B" := (Included _ A B) (at level 70).

Inductive Formula : Type :=
| X : nat -> Formula
| Not (a:Formula) : Formula
| disjunction (a b:Formula) : Formula
.

Notation "﹁ a" := (Not a)(at level 5,right associativity).
Notation "a ∨ b" := (disjunction a b)(at level 6,right associativity).
Notation "a ∧ b" := (﹁(﹁a ∨ ﹁b))(at level 7,right associativity).
Notation "a → b" := (﹁a ∨ b)(at level 8,right associativity).
Notation "a ↔ b" := ((a → b)∧(b → a))(at level 9,right associativity).
Definition Φ:= (Empty_set Formula).

Corollary Single : forall {U} (a x:U), a ∈ [ x ] -> a = x.
Proof.
  intros. unfold In in H. destruct H. reflexivity.
Qed.

Corollary UnionI : forall {U} (a: U) B C, a ∈ (B ∪ C) <-> a ∈ B \/ a ∈ C.
Proof.
  intros. split.
  - intros. destruct H.
    + left. apply H.
    + right. apply H.
  - intros. destruct H.
    + apply (Union_introl _ B C). apply H.
    + apply (Union_intror _ B C). apply H.
Qed.

Lemma Uequal1: forall {U} (A B : Ensemble U), A ∪ B = B ∪ A.
Proof.
  intros. apply (Extensionality_Ensembles _ (A ∪ B) (B ∪ A)). 
  unfold Same_set. split.
  * unfold Included. intros. destruct H.
    ** apply (Union_intror _ B A). apply H.
    ** apply (Union_introl _ B A). apply H.
  * unfold Included. intros. destruct H.
    ** apply (Union_intror _ A B). apply H.
    ** apply (Union_introl _ A B). apply H.
Qed.

Lemma Uequal2: forall {U} (A B C : Ensemble U), (A ∪ B) ∪ C = A ∪ (B ∪ C).
Proof.
  intros. apply (Extensionality_Ensembles _ ((A ∪ B) ∪ C) (A ∪ (B ∪ C))).
  unfold Same_set. split.
  * unfold Included. intros. destruct H.
    ** destruct H.
     *** apply (Union_introl _ A (B ∪ C)). apply H.
     *** apply (Union_intror _ A (B ∪ C)). apply (Union_introl _ B C). apply H.
    ** apply (Union_intror _ A (B ∪ C)). apply (Union_intror _ B C). apply H.
  * unfold Included. intros. destruct H.
    ** apply (Union_introl _ (A ∪ B) C). apply (Union_introl _ A B). apply H.
    ** destruct H.
     *** apply (Union_introl _ (A ∪ B) C). apply (Union_intror _ A B). apply H.
     *** apply (Union_intror _ (A ∪ B) C). apply H.
Qed.

Lemma Uequal3: forall {U} (A B C : Ensemble U), (A ∪ B) ∪ C = (A ∪ C) ∪ B.
Proof.
  intros. assert (H':  B ∪ C = C ∪ B). { rewrite Uequal1. reflexivity. }
  rewrite Uequal2. rewrite H'. rewrite Uequal2. reflexivity.
Qed.