From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Lia.

From Stdlib Require Import BinInt ZArith_dec Zorder ZArith.
Require Export Id.
Require Export State.
Require Export Expr.

From hahn Require Import HahnBase.

(* AST for statements *)
Inductive stmt : Type :=
| SKIP  : stmt
| Assn  : id -> expr -> stmt
| READ  : id -> stmt
| WRITE : expr -> stmt
| Seq   : stmt -> stmt -> stmt
| If    : expr -> stmt -> stmt -> stmt
| While : expr -> stmt -> stmt.

(* Supplementary notation *)
Notation "x  '::=' e"                         := (Assn  x e    ) (at level 37, no associativity).
Notation "s1 ';;'  s2"                        := (Seq   s1 s2  ) (at level 35, right associativity).
Notation "'COND' e 'THEN' s1 'ELSE' s2 'END'" := (If    e s1 s2) (at level 36, no associativity).
Notation "'WHILE' e 'DO' s 'END'"             := (While e s    ) (at level 36, no associativity).

(* Configuration *)
Definition conf := (state Z * list Z * list Z)%type.

(* Big-step evaluation relation *)
Reserved Notation "c1 '==' s '==>' c2" (at level 0).

Notation "st [ x '<-' y ]" := (update Z st x y) (at level 0).

Inductive bs_int : stmt -> conf -> conf -> Prop := 
| bs_Skip        : forall (c : conf), c == SKIP ==> c 
| bs_Assign      : forall (s : state Z) (i o : list Z) (x : id) (e : expr) (z : Z)
                          (VAL : [| e |] s => z),
                          (s, i, o) == x ::= e ==> (s [x <- z], i, o)
| bs_Read        : forall (s : state Z) (i o : list Z) (x : id) (z : Z),
                          (s, z::i, o) == READ x ==> (s [x <- z], i, o)
| bs_Write       : forall (s : state Z) (i o : list Z) (e : expr) (z : Z)
                          (VAL : [| e |] s => z),
                          (s, i, o) == WRITE e ==> (s, i, z::o)
| bs_Seq         : forall (c c' c'' : conf) (s1 s2 : stmt)
                          (STEP1 : c == s1 ==> c') (STEP2 : c' == s2 ==> c''),
                          c ==  s1 ;; s2 ==> c''
| bs_If_True     : forall (s : state Z) (i o : list Z) (c' : conf) (e : expr) (s1 s2 : stmt)
                          (CVAL : [| e |] s => Z.one)
                          (STEP : (s, i, o) == s1 ==> c'),
                          (s, i, o) == COND e THEN s1 ELSE s2 END ==> c'
| bs_If_False    : forall (s : state Z) (i o : list Z) (c' : conf) (e : expr) (s1 s2 : stmt)
                          (CVAL : [| e |] s => Z.zero)
                          (STEP : (s, i, o) == s2 ==> c'),
                          (s, i, o) == COND e THEN s1 ELSE s2 END ==> c'
| bs_While_True  : forall (st : state Z) (i o : list Z) (c' c'' : conf) (e : expr) (s : stmt)
                          (CVAL  : [| e |] st => Z.one)
                          (STEP  : (st, i, o) == s ==> c')
                          (WSTEP : c' == WHILE e DO s END ==> c''),
                          (st, i, o) == WHILE e DO s END ==> c''
| bs_While_False : forall (st : state Z) (i o : list Z) (e : expr) (s : stmt)
                          (CVAL : [| e |] st => Z.zero),
                          (st, i, o) == WHILE e DO s END ==> (st, i, o)
where "c1 == s ==> c2" := (bs_int s c1 c2).

#[export] Hint Constructors bs_int : core.

(* "Surface" semantics *)
Definition eval (s : stmt) (i o : list Z) : Prop :=
  exists st, ([], i, []) == s ==> (st, [], o).

Notation "<| s |> i => o" := (eval s i o) (at level 0).

(* "Surface" equivalence *)
Definition eval_equivalent (s1 s2 : stmt) : Prop :=
  forall (i o : list Z),  <| s1 |> i => o <-> <| s2 |> i => o.

Notation "s1 ~e~ s2" := (eval_equivalent s1 s2) (at level 0).
 
(* Contextual equivalence *)
Inductive Context : Type :=
| Hole 
| SeqL   : Context -> stmt -> Context
| SeqR   : stmt -> Context -> Context
| IfThen : expr -> Context -> stmt -> Context
| IfElse : expr -> stmt -> Context -> Context
| WhileC : expr -> Context -> Context.

(* Plugging a statement into a context *)
Fixpoint plug (C : Context) (s : stmt) : stmt := 
  match C with
  | Hole => s
  | SeqL     C  s1 => Seq (plug C s) s1
  | SeqR     s1 C  => Seq s1 (plug C s) 
  | IfThen e C  s1 => If e (plug C s) s1
  | IfElse e s1 C  => If e s1 (plug C s)
  | WhileC   e  C  => While e (plug C s)
  end.  

Notation "C '<~' e" := (plug C e) (at level 43, no associativity).

(* Contextual equivalence *)
Definition contextual_equivalent (s1 s2 : stmt) :=
  forall (C : Context), (C <~ s1) ~e~ (C <~ s2).

Notation "s1 '~c~' s2" := (contextual_equivalent s1 s2) (at level 42, no associativity).

Lemma contextual_equiv_stronger (s1 s2 : stmt) (H: s1 ~c~ s2) : s1 ~e~ s2.
Proof.
  specialize (H Hole).
  exact H.
Qed.

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof. 
  exists (Id 0 ::= Nat 0), (Id 1 ::= Nat 1).
  split.
  - intros i o.
    split; intro H.
    + destruct H as [st H].
      inversion H; subst.
      inversion VAL; subst.
      exists (update Z nil (Id 1) Z.one).
      apply bs_Assign.
      apply bs_Nat.
    + destruct H as [st H].
      inversion H; subst.
      inversion VAL; subst.
      exists (update Z nil (Id 0) Z.zero).
      apply bs_Assign.
      apply bs_Nat.
  - intro H.
    specialize (H (SeqL Hole (WRITE (Var (Id 0))))).
    specialize (H nil (Z.zero :: nil)).
    destruct H as [H _].
    assert (Hcontradiction: <| ((Id 0 ::= Nat 0) ;; (WRITE (Var (Id 0)))) |> nil => (Z.zero :: nil)).
    {
      exists (update Z nil (Id 0) Z.zero).
      apply bs_Seq with (update Z nil (Id 0) Z.zero, nil, nil).
      - eauto.
      - apply bs_Write.
        apply bs_Var.
        apply st_binds_hd.
    }
    apply H in Hcontradiction.
    unfold eval in Hcontradiction.
    destruct Hcontradiction as [st Hcontradiction].
    exfalso.
    inversion Hcontradiction; subst.
    inversion STEP1; subst.
    inversion VAL; subst.
    inversion STEP2; subst.
    inversion VAL0; subst.
    inversion VAR; subst.
    inversion H6.
Qed.

(* Big step equivalence *)
Definition bs_equivalent (s1 s2 : stmt) :=
  forall (c c' : conf), c == s1 ==> c' <-> c == s2 ==> c'.

Notation "s1 '~~~' s2" := (bs_equivalent s1 s2) (at level 0).

Ltac seq_inversion :=
  match goal with
    H: _ == _ ;; _ ==> _ |- _ => inversion_clear H
  end.

Ltac seq_apply :=
  match goal with
  | H: _   == ?s1 ==> ?c' |- _ == (?s1 ;; _) ==> _ => 
    apply bs_Seq with c'; solve [seq_apply | assumption]
  | H: ?c' == ?s2 ==>  _  |- _ == (_ ;; ?s2) ==> _ => 
    apply bs_Seq with c'; solve [seq_apply | assumption]
  end.

Module SmokeTest.

  (* Associativity of sequential composition *)
  Lemma seq_assoc (s1 s2 s3 : stmt) :
    ((s1 ;; s2) ;; s3) ~~~ (s1 ;; (s2 ;; s3)).
  Proof. 
    split; intro H; inversion_clear H.
    - inversion_clear STEP1. eauto.
    - inversion_clear STEP2. eauto.
  Qed.
  
  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof. 
    split; intro H; inversion_clear H;
    eauto; inversion STEP; eauto.
  Qed.
      
  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof.
    remember (WHILE e DO s END) as while_stmt.
    remember ((st, i, o)).
    induction EXE; try discriminate;
    injection Heqwhile_stmt; intros.
    - eauto.
    - injection Heqp; intros; subst.
      eauto.
  Qed.
  
  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof. 
    split; intro H; exfalso.
    - remember (WHILE (Nat 1) DO SKIP END) as loop_stmt.
      induction H; try discriminate Heqloop_stmt.
      + eauto.
      + injection Heqloop_stmt; intros; subst.
        inversion CVAL.
    - inversion H; inversion CVAL.
  Qed.
  
  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof. 
    split; intro H.
    - remember (WHILE e DO s1 END) as W.
      induction H; try discriminate HeqW;
      injection HeqW as eq_e eq_s; subst.
      + eapply bs_While_True; eauto.
        apply EQ; eauto.
      + apply bs_While_False; auto.
    - remember (WHILE e DO s2 END) as W.
      induction H; try discriminate HeqW;
      injection HeqW as eq_e eq_s; subst.
      + eapply bs_While_True; eauto.
        apply EQ; eauto.
      + apply bs_While_False; auto.
  Qed.
  
  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof.
    intro H.
    remember (WHILE (Nat 1) DO s END) as W.
    induction H; try discriminate HeqW;
    injection HeqW as H_e H_s; subst.
    + auto.
    + inversion CVAL.
  Qed.
  
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof.
  unfold bs_equivalent.
  intros c c'.
  split; intro H; inversion_clear H;
  apply bs_Seq with c'0;
  try (assumption || apply EQ; assumption).
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof.
  unfold bs_equivalent.
  intros c c'.
  split; intro H; inversion_clear H;
  apply bs_Seq with c'0;
  try (assumption || apply EQ; assumption).
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof.
  unfold bs_equivalent.
  intros c c'.
  split; intro H; inversion_clear H;
  try (
    eauto ||
    apply bs_If_False; eauto; apply EQ; eauto
  ).
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof.
  unfold bs_equivalent.
  intros c c'.
  split; intro H; inversion_clear H;
  try (
    eauto ||
    apply bs_If_True; eauto; apply EQ; eauto
  ).
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof.
  apply SmokeTest.while_eq. auto.
Qed.

Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof.
  split. apply eq_congruence_seq_r. auto.
  split. apply eq_congruence_seq_l. auto.
  split. apply eq_congruence_cond_else. auto.
  split. apply eq_congruence_cond_then. auto.
  apply eq_congruence_while. auto.
Qed.

(* Big-step semantics is deterministic *)
Ltac by_eval_deterministic :=
  match goal with
    H1: [|?e|]?s => ?z1, H2: [|?e|]?s => ?z2 |- _ => 
     apply (eval_deterministic e s z1 z2) in H1; [subst z2; reflexivity | assumption]
  end.

Ltac eval_zero_not_one :=
  match goal with
    H : [|?e|] ?st => (Z.one), H' : [|?e|] ?st => (Z.zero) |- _ =>
    assert (Z.zero = Z.one) as JJ; [ | inversion JJ];
    eapply eval_deterministic; eauto
  end.

Lemma bs_int_deterministic (c c1 c2 : conf) (s : stmt)
      (EXEC1 : c == s ==> c1) (EXEC2 : c == s ==> c2) :
  c1 = c2.
Proof.
  generalize dependent c2.
  induction EXEC1; intros c2 EXEC2; inversion EXEC2; eauto;
  try (
    by_eval_deterministic || eval_zero_not_one ||
    assert (c' = c'0) by (eapply IHEXEC1_1; eauto); subst; eauto
  ).
Qed.

Definition equivalent_states (s1 s2 : state Z) :=
  forall id, Expr.equivalent_states s1 s2 id.

Lemma bs_equiv_states_helper_1 
  (st st' : state Z)
  (x : id)
  (z : Z)
  (H: equivalent_states st st') :  equivalent_states ((st)[x <- z]) ((st')[x <- z]) .
Proof. 
  intro. specialize (id_eq_dec id x) as H'.
  destruct H'; split; intros; inversion H0;
  try (
    apply st_binds_hd ||
    subst; contradiction ||
    apply st_binds_tl; assumption ||
    apply H; assumption
  ).
Qed.

Lemma bs_equiv_states_helper_2
  (s1 s2 : state Z)
  (HE : equivalent_states s1 s2)
  (e : expr) (z : Z)
  (H : [|e|] s1 => z) : [|e|] s2 => z.
Proof.
  induction H; intros.
  apply bs_Nat.
  apply bs_Var.
  apply HE. apply VAR.
  all: try by econstructor; try (apply (IHeval1 HE) || apply (IHeval2 HE)).
Qed.

Lemma bs_equiv_states
  (s            : stmt)
  (i o i' o'    : list Z)
  (st1 st2 st1' : state Z)
  (HE1          : equivalent_states st1 st1')  
  (H            : (st1, i, o) == s ==> (st2, i', o')) :
  exists st2',  equivalent_states st2 st2' /\ (st1', i, o) == s ==> (st2', i', o').
Proof.
  remember (st1, i, o). remember (st2, i', o'). generalize i o i' o' st1 st2 st1' HE1 Heqp Heqp0. 
  clear Heqp0 Heqp HE1 st1' st2 st1 o' i' o i. 
  induction H; intros.
  subst. inversion Heqp0. subst. exists st1'. split; eauto.
  all: inversion Heqp; inversion Heqp0; subst.
  - exists (st1' [x <- z]). split. apply bs_equiv_states_helper_1. apply HE1. apply bs_Assign.
    eapply bs_equiv_states_helper_2; eauto.
  - exists (st1' [x <- z]). split. 
    apply bs_equiv_states_helper_1. apply HE1. apply bs_Read.
  - exists st1'. split. eauto.
    apply bs_Write. eapply bs_equiv_states_helper_2; eauto.
  - destruct c'. destruct p. 
    assert ((s, l0, l) = (s, l0, l)). auto. 
    destruct (IHbs_int1 i o l0 l st1 s st1' HE1 H1 H3). destruct H4. 
    destruct (IHbs_int2 l0 l i' o' s st2 x H4 H3 H2). destruct H6. 
    exists x0. split. apply H6. eapply bs_Seq; eauto.
  - destruct (IHbs_int i0 o0 i' o' st1 st2 st1' HE1 Heqp H0). destruct H1. 
    exists x. split. apply H1. 
    apply bs_If_True. eapply bs_equiv_states_helper_2; eauto. eauto.
  - destruct (IHbs_int i0 o0 i' o' st1 st2 st1' HE1 Heqp H0). destruct H1.
    exists x. split. apply H1. apply bs_If_False. eapply bs_equiv_states_helper_2; eauto. eauto.
  - destruct c'. destruct p. 
    assert ((s0, l0, l) = (s0, l0, l)). auto. 
    destruct (IHbs_int1 i0 o0 l0 l st1 s0 st1' HE1 Heqp H2). destruct H3. 
    destruct (IHbs_int2 l0 l i' o' s0 st2 x H3 H2 H1). destruct H5. 
    exists x0. split. apply H5. eapply bs_While_True. 
    eapply bs_equiv_states_helper_2; eauto. eauto. eauto.
  - exists st1'. split. apply HE1. apply bs_While_False. eapply bs_equiv_states_helper_2; eauto.
Qed.
  
(* Contextual equivalence is equivalent to the semantic one *)
(* TODO: no longer needed *)
Ltac by_eq_congruence e s s1 s2 H :=
  remember (eq_congruence e s s1 s2 H) as Congruence;
  match goal with H: Congruence = _ |- _ => clear H end;
  repeat (match goal with H: _ /\ _ |- _ => inversion_clear H end); assumption.
      
(* Small-step semantics *)
Module SmallStep.
  
  Reserved Notation "c1 '--' s '-->' c2" (at level 0).

  Inductive ss_int_step : stmt -> conf -> option stmt * conf -> Prop :=
  | ss_Skip        : forall (c : conf), c -- SKIP --> (None, c) 
  | ss_Assign      : forall (s : state Z) (i o : list Z) (x : id) (e : expr) (z : Z) 
                            (SVAL : [| e |] s => z),
      (s, i, o) -- x ::= e --> (None, (s [x <- z], i, o))
  | ss_Read        : forall (s : state Z) (i o : list Z) (x : id) (z : Z),
      (s, z::i, o) -- READ x --> (None, (s [x <- z], i, o))
  | ss_Write       : forall (s : state Z) (i o : list Z) (e : expr) (z : Z)
                            (SVAL : [| e |] s => z),
      (s, i, o) -- WRITE e --> (None, (s, i, z::o))
  | ss_Seq_Compl   : forall (c c' : conf) (s1 s2 : stmt)
                            (SSTEP : c -- s1 --> (None, c')),
      c -- s1 ;; s2 --> (Some s2, c')
  | ss_Seq_InCompl : forall (c c' : conf) (s1 s2 s1' : stmt)
                            (SSTEP : c -- s1 --> (Some s1', c')),
      c -- s1 ;; s2 --> (Some (s1' ;; s2), c')
  | ss_If_True     : forall (s : state Z) (i o : list Z) (s1 s2 : stmt) (e : expr)
                            (SCVAL : [| e |] s => Z.one),
      (s, i, o) -- COND e THEN s1 ELSE s2 END --> (Some s1, (s, i, o))
  | ss_If_False    : forall (s : state Z) (i o : list Z) (s1 s2 : stmt) (e : expr)
                            (SCVAL : [| e |] s => Z.zero),
      (s, i, o) -- COND e THEN s1 ELSE s2 END --> (Some s2, (s, i, o))
  | ss_While       : forall (c : conf) (s : stmt) (e : expr),
      c -- WHILE e DO s END --> (Some (COND e THEN s ;; WHILE e DO s END ELSE SKIP END), c)
  where "c1 -- s --> c2" := (ss_int_step s c1 c2).

  Reserved Notation "c1 '--' s '-->>' c2" (at level 0).

  Inductive ss_int : stmt -> conf -> conf -> Prop :=
    ss_int_Base : forall (s : stmt) (c c' : conf),
                    c -- s --> (None, c') -> c -- s -->> c'
  | ss_int_Step : forall (s s' : stmt) (c c' c'' : conf),
                    c -- s --> (Some s', c') -> c' -- s' -->> c'' -> c -- s -->> c'' 
  where "c1 -- s -->> c2" := (ss_int s c1 c2).

  Lemma ss_int_step_deterministic (s : stmt)
        (c : conf) (c' c'' : option stmt * conf) 
        (EXEC1 : c -- s --> c')
        (EXEC2 : c -- s --> c'') :
    c' = c''.
  Proof.
    generalize dependent c''.
    induction EXEC1; intros c'' EXEC2; inversion EXEC2; subst; eauto;
    try (assert (z = z0) by (eapply eval_deterministic; eauto); subst; eauto);
    try (assert (Z.zero = Z.one) by (eapply eval_deterministic; eauto); discriminate);
    try (assert ((None, c') = (Some s1', c'0)) by (eapply IHEXEC1; eauto); discriminate);
    try (assert ((Some s1', c') = (None, c'0)) by (eapply IHEXEC1; eauto); discriminate);
    try (assert ((None, c') = (None, c'0)) by (eapply IHEXEC1; eauto); injection H; intros; subst; eauto);
    try (assert ((Some s1', c') = (Some s1'0, c'0)) by (eapply IHEXEC1; eauto); injection H; intros; subst; eauto).
  Qed.
  
  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof.
    generalize dependent c''.
    induction STEP1; intros c_final STEP2.
    - destruct STEP2 as [s1 c1 c1' H1 | s1 s1' c1 c1' c1'' H1 H2].
      + assert (HEQ : (None, c') = (None, c1')) by (eapply ss_int_step_deterministic; eauto).
        injection HEQ; intros; subst. reflexivity.
      + assert (HEQ : (None, c') = (Some s1', c1')) by (eapply ss_int_step_deterministic; eauto).
        discriminate HEQ.
    - destruct STEP2 as [s2 c2 c2' H2 | s2 s2' c2 c2' c2'' H2 H3].
      + assert (HEQ : (Some s', c') = (None, c2')) by (eapply ss_int_step_deterministic; eauto).
        discriminate HEQ.
      + assert (HEQ : (Some s', c') = (Some s2', c2')) by (eapply ss_int_step_deterministic; eauto).
        injection HEQ; intros; subst.
        eapply IHSTEP1. eauto.
  Qed.
  
  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof. inversion STEP; eauto. Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'. 
  Proof.
    induction STEP1 as [s c_start c_final HSTEP | s s_cont c_start c_mid c_final HSTEP HCONT IH].
    - apply ss_int_Step with (s' := s2) (c' := c_final).
      + apply ss_Seq_Compl. eauto.
      + eauto.
    - apply ss_int_Step with (s' := s_cont ;; s2) (c' := c_mid).
      + apply ss_Seq_InCompl. eauto.
      + eauto.
  Qed.
  
  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof.
    generalize dependent c''.
    generalize dependent s'.
    generalize dependent c'.
    induction s; intros; inversion STEP; subst.
     - apply bs_Seq with c'.
      + apply ss_bs_base. exact SSTEP.
      + exact EXEC.
    - inversion EXEC; subst.
      apply bs_Seq with c'0.
      + apply IHs1 with (c' := c') (s' := s1'); auto.
      + exact STEP2.
    - apply bs_If_True; auto.
    - apply bs_If_False; auto.
    - inversion EXEC; subst.
      + inversion STEP0; subst.
        eapply bs_While_True; eauto.
      + inversion STEP0; subst.
        apply bs_While_False; auto.
  Qed.
  
  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof.
    split; intro H; induction H.
    + apply ss_int_Base. apply ss_Skip.
    + apply ss_int_Base. apply ss_Assign. exact VAL.
    + apply ss_int_Base. apply ss_Read.
    + apply ss_int_Base. apply ss_Write. exact VAL.
    + apply ss_ss_composition with c'; auto.
    + apply ss_int_Step with (s' := s1) (c' := (s, i, o)).
      * apply ss_If_True. exact CVAL.
      * exact IHbs_int.
    + apply ss_int_Step with (s' := s2) (c' := (s, i, o)).
      * apply ss_If_False. exact CVAL.
      * exact IHbs_int.
    + apply ss_int_Step with (s' := COND e THEN s ;; WHILE e DO s END ELSE SKIP END) (c' := (st, i, o)).
      * apply ss_While.
      * apply ss_int_Step with (s' := s ;; WHILE e DO s END) (c' := (st, i, o)).
        apply ss_If_True. exact CVAL.
        apply ss_ss_composition with c'; auto.
    + apply ss_int_Step with (s' := COND e THEN s ;; WHILE e DO s END ELSE SKIP END) (c' := (st, i, o)).
      * apply ss_While.
      * apply ss_int_Step with (s' := SKIP) (c' := (st, i, o)).
        apply ss_If_False. exact CVAL.
        apply ss_int_Base. apply ss_Skip.
    + apply ss_bs_base. exact H.
    + apply ss_bs_step with (c' := c') (s' := s'); auto.
  Qed.
  
End SmallStep.

Module Renaming.

  Definition renaming := Renaming.renaming.

  Definition rename_conf (r : renaming) (c : conf) : conf :=
    match c with
    | (st, i, o) => (Renaming.rename_state r st, i, o)
    end.
  
  Fixpoint rename (r : renaming) (s : stmt) : stmt :=
    match s with
    | SKIP                       => SKIP
    | x ::= e                    => (Renaming.rename_id r x) ::= Renaming.rename_expr r e
    | READ x                     => READ (Renaming.rename_id r x)
    | WRITE e                    => WRITE (Renaming.rename_expr r e)
    | s1 ;; s2                   => (rename r s1) ;; (rename r s2)
    | COND e THEN s1 ELSE s2 END => COND (Renaming.rename_expr r e) THEN (rename r s1) ELSE (rename r s2) END
    | WHILE e DO s END           => WHILE (Renaming.rename_expr r e) DO (rename r s) END             
    end.   

  Lemma re_rename
    (r r' : Renaming.renaming)
    (Hinv : Renaming.renamings_inv r r')
    (s    : stmt) : rename r (rename r' s) = s.
  Proof.
    induction s; simpl.
    - reflexivity.
    - rewrite (Renaming.re_rename_expr r r' Hinv e).
      rewrite (Hinv i).
      reflexivity.
    - rewrite (Hinv i).
      reflexivity.
    - rewrite (Renaming.re_rename_expr r r' Hinv e).
      reflexivity.
    - rewrite IHs1, IHs2.
      reflexivity.
    - rewrite (Renaming.re_rename_expr r r' Hinv e).
      rewrite IHs1, IHs2.
      reflexivity.
    - rewrite (Renaming.re_rename_expr r r' Hinv e).
      rewrite IHs.
      reflexivity.
  Qed.
  
  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof.
    unfold update.
    simpl.
    destruct r as [f Hf].
    simpl.
    reflexivity.
  Qed.
  
  #[export] Hint Resolve Renaming.eval_renaming_invariance : core.

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof.
    destruct r.
    induction Hbs; subst; simpl.
    - eauto.
    - constructor.
      apply Renaming.eval_renaming_invariance.
      eauto.
    - eauto.
    - constructor.
      apply Renaming.eval_renaming_invariance.
      eauto.
    - eauto.
    - eapply bs_If_True.
      + apply Renaming.eval_renaming_invariance. eauto.
      + eauto.
    - eapply bs_If_False.
      + apply Renaming.eval_renaming_invariance. eauto.
      + eauto.
    - eapply bs_While_True.
      + apply Renaming.eval_renaming_invariance. eauto.
      + eauto.
      + eauto.
    - eapply bs_While_False.
      apply Renaming.eval_renaming_invariance. eauto.
  Qed.
  
  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof.
    destruct (Renaming.renaming_inv r) as [r' Hinv].
    assert (H : (rename_conf r' (rename_conf r c)) == (rename r' (rename r s)) ==> (rename_conf r' (rename_conf r c'))).
    apply renaming_invariant_bs. auto.
    destruct c as [[st i] o], c' as [[st' i'] o'].
    simpl in H.
    rewrite (Renaming.re_rename_state r' r Hinv st) in H.
    rewrite (Renaming.re_rename_state r' r Hinv st') in H.
    rewrite (re_rename r' r Hinv s) in H.
    auto.
  Qed.
    
  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof.
    intros i o.
    split; intro H; destruct H as [st H].
    - exists (Renaming.rename_state r st).
      apply renaming_invariant_bs with (c := ([], i, [])) (c' := (st, [], o)).
      exact H.
    - destruct (Renaming.renaming_inv2 r) as [r' Hinv].
      exists (Renaming.rename_state r' st).
      apply renaming_invariant_bs_inv with (r := r).
      simpl.
      rewrite (Renaming.re_rename_state r r' Hinv st).
      exact H.
  Qed.
  
End Renaming.

(* CPS semantics *)
Inductive cont : Type := 
| KEmpty : cont
| KStmt  : stmt -> cont.
 
Definition Kapp (l r : cont) : cont :=
  match (l, r) with
  | (KStmt ls, KStmt rs) => KStmt (ls ;; rs)
  | (KEmpty  , _       ) => r
  | (_       , _       ) => l
  end.

Notation "'!' s" := (KStmt s) (at level 0).
Notation "s1 @ s2" := (Kapp s1 s2) (at level 0).

Reserved Notation "k '|-' c1 '--' s '-->' c2" (at level 0).

Inductive cps_int : cont -> cont -> conf -> conf -> Prop :=
| cps_Empty       : forall (c : conf), KEmpty |- c -- KEmpty --> c
| cps_Skip        : forall (c c' : conf) (k : cont)
                           (CSTEP : KEmpty |- c -- k --> c'),
    k |- c -- !SKIP --> c'
| cps_Assign      : forall (s : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (x : id) (e : expr) (n : Z)
                           (CVAL : [| e |] s => n)
                           (CSTEP : KEmpty |- (s [x <- n], i, o) -- k --> c'),
    k |- (s, i, o) -- !(x ::= e) --> c'
| cps_Read        : forall (s : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (x : id) (z : Z)
                           (CSTEP : KEmpty |- (s [x <- z], i, o) -- k --> c'),
    k |- (s, z::i, o) -- !(READ x) --> c'
| cps_Write       : forall (s : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (e : expr) (z : Z)
                           (CVAL : [| e |] s => z)
                           (CSTEP : KEmpty |- (s, i, z::o) -- k --> c'),
    k |- (s, i, o) -- !(WRITE e) --> c'
| cps_Seq         : forall (c c' : conf) (k : cont) (s1 s2 : stmt)
                           (CSTEP : !s2 @ k |- c -- !s1 --> c'),
    k |- c -- !(s1 ;; s2) --> c'
| cps_If_True     : forall (s : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (e : expr) (s1 s2 : stmt)
                           (CVAL : [| e |] s => Z.one)
                           (CSTEP : k |- (s, i, o) -- !s1 --> c'),
    k |- (s, i, o) -- !(COND e THEN s1 ELSE s2 END) --> c'
| cps_If_False    : forall (s : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (e : expr) (s1 s2 : stmt)
                           (CVAL : [| e |] s => Z.zero)
                           (CSTEP : k |- (s, i, o) -- !s2 --> c'),
    k |- (s, i, o) -- !(COND e THEN s1 ELSE s2 END) --> c'
| cps_While_True  : forall (st : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (e : expr) (s : stmt)
                           (CVAL : [| e |] st => Z.one)
                           (CSTEP : !(WHILE e DO s END) @ k |- (st, i, o) -- !s --> c'),
    k |- (st, i, o) -- !(WHILE e DO s END) --> c'
| cps_While_False : forall (st : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (e : expr) (s : stmt)
                           (CVAL : [| e |] st => Z.zero)
                           (CSTEP : KEmpty |- (st, i, o) -- k --> c'),
    k |- (st, i, o) -- !(WHILE e DO s END) --> c'
where "k |- c1 -- s --> c2" := (cps_int k s c1 c2).

Ltac cps_bs_gen_helper k H HH :=
  destruct k eqn:K; subst; inversion H; subst;
  [inversion EXEC; subst | eapply bs_Seq; eauto];
  apply HH; auto.
    
Lemma cps_bs_gen (S : stmt) (c c' : conf) (S1 k : cont)
      (EXEC : k |- c -- S1 --> c') (DEF : !S = S1 @ k):
  c == S ==> c'.
Proof. admit. Admitted.

Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof. admit. Admitted.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') : 
  c == s ==> c'.
Proof. admit. Admitted.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof. admit. Admitted.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof. admit. Admitted.

Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof. admit. Admitted.

(* Lemma cps_stmt_assoc s1 s2 s3 s (c c' : conf) : *)
(*   (! (s1 ;; s2 ;; s3)) |- c -- ! (s) --> (c') <-> *)
(*   (! ((s1 ;; s2) ;; s3)) |- c -- ! (s) --> (c'). *)
