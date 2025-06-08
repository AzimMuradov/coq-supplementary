(** Based on Benjamin Pierce's "Software Foundations" *)

From Stdlib Require Import List Lia.
Import ListNotations.
From Stdlib Require Export Arith Arith.EqNat.
Require Export Id.

From hahn Require Import HahnBase.


Section S.

  Variable A : Set.
  
  Definition state := list (id * A). 

  Reserved Notation "st / x => y" (at level 0).

  Inductive st_binds : state -> id -> A -> Prop := 
    st_binds_hd : forall st id x, ((id, x) :: st) / id => x
  | st_binds_tl : forall st id x id' x', id <> id' -> st / id => x -> ((id', x')::st) / id => x
  where "st / x => y" := (st_binds st x y).

  Definition update (st : state) (id : id) (a : A) : state := (id, a) :: st.

  Notation "st [ x '<-' y ]" := (update st x y) (at level 0).
  
  (* Functional version of binding-in-a-state relation *)
  Fixpoint st_eval (st : state) (x : id) : option A :=
    match st with
    | (x', a) :: st' =>
        if id_eq_dec x' x then Some a else st_eval st' x
    | [] => None
    end.
 
  (* State a prove a lemma which claims that st_eval and
     st_binds are actually define the same relation.
  *)

  Lemma state_deterministic' (st : state) (x : id) (n m : option A)
    (SN : st_eval st x = n)
    (SM : st_eval st x = m) :
    n = m.
  Proof using Type.
    subst n. subst m. reflexivity.
  Qed.
  
  Lemma state_deterministic (st : state) (x : id) (n m : A)   
    (SN : st / x => n)
    (SM : st / x => m) :
    n = m. 
  Proof.
    induction SN; inversion SM; subst; try (contradiction || auto).
  Qed.
  
  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof. unfold update. constructor. Qed.

  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof.
    split; intros H.
    apply st_binds_tl; auto.
    inv H.
  Qed.

  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof.
    split; intro H.
    - inversion H; subst.
      + apply st_binds_hd.
      + inversion H6; subst.
        * exfalso. apply H5. reflexivity.
        * apply st_binds_tl; assumption.
    - inversion H; subst.
      + apply st_binds_hd.
      + apply st_binds_tl.
        * assumption.
        * apply st_binds_tl; assumption.
  Qed.
  
  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof.
    destruct (id_eq_dec x1 x2) as [H_eq | H_neq].
    - subst.
      assert (H_eq_values: n1 = m).
      apply (state_deterministic st x2 n1 m); assumption.
      subst.
      apply st_binds_hd.
    - apply st_binds_tl.
      + intro H_contra. apply H_neq. auto.
      + auto.
  Qed.
  
  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    inversion SM; subst.
    - apply st_binds_tl.
      + auto.
      + apply st_binds_hd.
    - inversion H5.
      + apply st_binds_hd.
      + apply st_binds_tl.
        * auto.
        * apply st_binds_tl; auto.
  Qed.

  Lemma state_extensional_equivalence (st st' : state) (H: forall x z, st / x => z <-> st' / x => z) : st = st'.
  Proof. Abort.

  Lemma state_extensional_equivalence_is_false : (exists a: A, True) -> exists (st st' : state), (forall x z, st / x => z <-> st' / x => z) /\ st <> st'.
  Proof.
    intro.
    destruct H as [a _].
    exists [(Id 0, a); (Id 0, a)], [(Id 0, a)].

    split.
    - intros x z.
      split; intro H.
      + inversion H; subst.
        * apply st_binds_hd.
        * inversion H6; subst.
          -- exfalso. apply H5. reflexivity.
          -- inversion H8.
      + inversion H; subst.
        * apply st_binds_hd.
        * inversion H6.
    - intro H_eq.
      discriminate H_eq.
  Qed.

  Definition state_equivalence (st st' : state) := forall x a, st / x => a <-> st' / x => a.

  Notation "st1 ~~ st2" := (state_equivalence st1 st2) (at level 0).

  Lemma st_equiv_refl (st: state) : st ~~ st.
  Proof. 
    intros x a.
    reflexivity.
  Qed.

  Lemma st_equiv_symm (st st': state) (H: st ~~ st') : st' ~~ st.
  Proof.
    intros x a.
    symmetry.
    auto.
  Qed.

  Lemma st_equiv_trans (st st' st'': state) (H1: st ~~ st') (H2: st' ~~ st'') : st ~~ st''.
  Proof.
    intros x a.
    transitivity (st' / x => a); auto.
  Qed.

  Lemma equal_states_equive (st st' : state) (HE: st = st') : st ~~ st'.
  Proof.
    intros x a.
    subst.
    split; intros H; auto.
  Qed.
  
End S.
