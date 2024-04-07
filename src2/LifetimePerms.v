(* begin hide *)

From Coq Require Import
     Classes.Morphisms
     Relations.Relation_Operators
     Logic.JMeq
     Lists.List
     Arith.PeanoNat
     Logic.FunctionalExtensionality
     Lia.

From Heapster2 Require Import
     Utils
     Permissions
     Lifetime
     SepStep
     Typing.

From ITree Require Import
     ITree
     Eq.Eqit.

From Paco Require Import
     paco.

Import ListNotations.
(* end hide *)

Section LifetimePerms.
  Context {S : Type}.
  Context `{Hlens: Lens S Lifetimes}.

  (*
  (* Some lifetime permissions only work with other permissions that do not affect lifetimes *)
  Record nonLifetime p : Prop :=
    {
      nonLT_inv : forall x lts, inv p x -> inv p (lput x lts);
      nonLT_guar : forall x y lts, inv p x -> guar p x y -> guar p (lput x lts) (lput y lts);
      nonLT_guar_eq : forall x y, inv p x -> guar p x y -> lget x = lget y;
    }.

  (*
  Definition nonLifetime p : Prop :=
    (* rely does not tolerate lifetimes going wrong *)
    (* (forall x y, rely p x y -> Lifetimes_lte (lget (fst (proj1_sig x))) (lget (fst (proj1_sig y)))) /\ *)
      (* guar doesn't allow for lifetime changes *)
    (forall x y, inv p x -> guar p x y -> lget x = lget y).
   *)

  (*
  Lemma nonLifetime_restrict c c' Hspred p :
    nonLifetime c' p ->
    nonLifetime c (restrict _ (interp_LifetimeClauses c) (interp_LifetimeClauses c') Hspred p).
  Proof.
    repeat intro.
    cbn in *. red in H, H0. destruct x, y, x, x0.
    specialize (H _ _ H0). cbn in *. auto.
  Qed.
   *)

  Definition nonLifetime_pred (pred : S -> Prop) : Prop :=
    forall x lts, pred x -> pred (lput x lts).

  Lemma nonLifetime_invperm pred : nonLifetime_pred pred -> nonLifetime (invperm pred).
  Proof.
    split; repeat intro.
    - apply H. assumption.
    - inversion H1; reflexivity.
    - inversion H1; reflexivity.
  Qed.


  Lemma nonLifetime_sep_conj p q : nonLifetime p -> nonLifetime q ->
                                   nonLifetime (p ** q).
  Proof.
    constructor; intros.
    - destruct H1 as [? [? ?]].
      split; [ | split ]; try assumption; eapply nonLT_inv; eassumption.
    - induction H2.
      + destruct H1 as [? [? ?]].
        destruct H2; apply t_step; [ left | right ]; eapply nonLT_guar; eassumption.
      + etransitivity; [ apply IHclos_trans1; assumption | ].
        apply IHclos_trans2.
        eapply inv_guar; eassumption.
    - induction H2.
      + destruct H1 as [? [? ?]].
        destruct H2;
          [ eapply (nonLT_guar_eq _ H) | eapply (nonLT_guar_eq _ H0) ]; eassumption.
      + etransitivity; [ apply IHclos_trans1; assumption | ].
        apply IHclos_trans2. eapply inv_guar; eassumption.
  Qed.

  (* FIXME: this no longer holds as-is because the smaller permission could have
     a bigger invariant

  Lemma nonLifetime_lte p q : p <= q -> nonLifetime q -> nonLifetime p.
  Proof.
    repeat intro. apply H0.
    - eapply inv_inc; try eassumption.
apply H. auto.
  Qed.
   *)

  Lemma nonLifetime_bottom : nonLifetime bottom_perm.
  Proof.
  Admitted.
   *)


  (* Permission to allocate lifetimes with index >= n; also requires any other
  permissions (via its rely) to respect the lifetime evolution order *)
  Program Definition lalloc_perm (n : nat) : perm :=
    {|
      pre x := length (lget x) = n;

      rely x y :=
        Lifetimes_lte (lget x) (lget y) /\
          length (lget x) = length (lget y) /\
          (forall n', n' >= n -> lifetime (lget x) n' = lifetime (lget y) n');

      guar x y :=
        (exists (ls : Lifetimes), y = lput x ls) /\
          (forall l, l < n -> lifetime (lget x) l = lifetime (lget y) l) /\
          Lifetimes_lte (lget x) (lget y);

      inv x := True;
    |}.
  Next Obligation.
    constructor; repeat intro.
    - split; [ | split ]; reflexivity.
    - destruct H as [? [? ?]]; destruct H0 as [? [? ?]].
      split; [ etransitivity; eassumption | ].
      split; [ etransitivity; eassumption | ]; intros.
      etransitivity; [ apply H2 | apply H4 ]; assumption.
  Qed.
  Next Obligation.
    constructor; repeat intro.
    - split; [ exists (lget x); symmetry; apply lPutGet | ].
      split; reflexivity.
    - destruct H as [[lts_x ?] [? ?]]. destruct H0 as [[lts_y ?] [? ?]]. subst.
      repeat rewrite lPutPut in * |- *. repeat rewrite lGetPut in * |- *.
      rewrite lGetPut in H4. rewrite lGetPut in H3.
      split; [ eexists; reflexivity | ].
      split; [ | etransitivity; eassumption ].
      intros; etransitivity; [ apply H1 | apply H3 ]; assumption.
  Qed.


  (* Ownership of lifetime l, assuming it is currently active, that all
  lifetimes in ls are children of l, and that pre must be satisfied whenever l
  is finished. *)
  Program Definition lowned_perm l (ls : nat -> Prop) (pred : S -> Prop) :=
    {|
      (* [l] must be current *)
      pre x := lifetime (lget x) l = Some current;

      (* Nobody else can change l or violate the all_lte invariant *)
      rely x y :=
        lifetime (lget x) l = lifetime (lget y) l /\
          (all_lte l ls (lget x) -> all_lte l ls (lget y));

      (* I can end l if pred is satisfied and all children are finished *)
      guar x y :=
        x = y \/
          y = (lput x (replace_list_index (lget x) l finished)) /\
            pred y /\ (forall l', ls l' -> lifetime (lget x) l' = Some finished);

      (* l has at least been allocated, and if l is finished then so are all its
      children *)
      inv x :=
        statusOf_lte (Some current) (lifetime (lget x) l) /\
          all_lte l ls (lget x);
    |}.
  Next Obligation.
    constructor; intros.
    - intro; split; [ reflexivity | intro; assumption ].
    - intros x y z [? ?] [? ?].
      split; [ etransitivity; eassumption | auto ].
  Qed.
  Next Obligation.
    constructor; repeat intro.
    - left; reflexivity.
    - destruct H; [ subst; assumption | ].
      destruct H0; [ subst; right; assumption | ].
      destruct H as [? [? ?]]. destruct H0 as [? [? ?]].
      right; subst. repeat rewrite lGetPut. repeat rewrite lPutPut.
      rewrite replace_list_index_idem.
      split; [ reflexivity | ].
      rewrite lPutPut in H3. rewrite lGetPut in H3.
      rewrite replace_list_index_idem in H3.
      split; [ assumption | ].
      rewrite lGetPut in H4. assumption.
  Qed.
  Next Obligation.
    destruct H as [? | [? [? ?]]]; subst; [ split; assumption | ].
    rewrite lGetPut.
    split; [ | apply all_lte_finish; try assumption;
               apply lte_current_lt_length; assumption ].
    unfold lifetime. rewrite nth_error_replace_list_index_eq. trivial.
  Qed.


  Lemma separate_lowned_lalloc_perm l ls pred n :
    l < n -> lowned_perm l ls pred ⊥ lalloc_perm n.
  Proof.
    constructor; intros.
    - destruct H2 as [[lts_y ?] [? ?]]; subst.
      split; [ apply H3; assumption | ].
      repeat intro. rewrite lGetPut.
      rewrite lGetPut in H3. rewrite lGetPut in H4.
      rewrite <- (H3 l); [ | assumption ].
      etransitivity; [ apply H2; eassumption | apply H4 ].
    - destruct H2; subst; [ reflexivity | ].
      destruct H2 as [? [? ?]]. subst. destruct H0. split; [ | split ].
      + rewrite lGetPut.
        apply Lifetimes_lte_update;
          [ apply lte_current_lt_length; assumption | apply finished_greatest ].
      + rewrite lGetPut. apply replace_list_index_length.
        apply lte_current_lt_length. assumption.
      + intros. rewrite lGetPut. unfold lifetime.
        apply nth_error_replace_list_index_neq;
          [ apply lte_current_lt_length; assumption | ].
        intro. subst. apply (Lt.lt_not_le l n); assumption.
  Qed.


  Lemma lowned_lowned_separate_h l1 ls1 pred1 l2 ls2 pred2 x y :
    l1 <> l2 -> inv (lowned_perm l1 ls1 pred1) x ->
    inv (lowned_perm l2 ls2 pred2) x ->
    guar (lowned_perm l1 ls1 pred1) x y -> rely (lowned_perm l2 ls2 pred2) x y.
  Proof.
    intros. destruct H0. destruct H1.
    destruct H2 as [? | [? [? ?]]]; subst; [ reflexivity | ].
    simpl. rewrite lGetPut.
    assert (l1 < length (lget x));
      [ apply lte_current_lt_length; assumption | ].
    unfold all_lte, lifetime.
    rewrite <- nth_error_replace_list_index_neq;
      [ | assumption | apply Nat.neq_sym; assumption ].
    split; [ reflexivity | ]. intros.
    destruct (Nat.eq_dec l' l1).
    + subst. rewrite nth_error_replace_list_index_eq.
      apply finished_greatest.
    + rewrite <- nth_error_replace_list_index_neq; try assumption.
      apply H7. assumption.
  Qed.


  (*
  Lemma owned_owned_separate l1 ls1 pred1 l2 ls2 pred2 :
    (exists x,
        all_finished ls1 (lget x) /\
          pred1 (lput x (replace_list_index (lget x) l1 finished))) ->
    l1 <> l2 <-> owned l1 ls1 pred1 ⊥ owned l2 ls2 pred2.
  Proof.
    split; [ constructor | ]; intros.
    - eapply owned_owned_separate_h; try apply Nat.neq_sym; eassumption.
    - eapply owned_owned_separate_h; eassumption.
    - destruct H as [? [? ?]].
      assert (rely (owned l2 ls2 pred2)
                x (lput x (replace_list_index (lget x) l1 finished)));


      assert (guar (owned l1 ls1 pred1)
                x (lput x (replace_list_index (lget x) l1 finished)));
        [ right; split; [ reflexivity | split ]; assumption | ].
   *)

  Lemma lowned_lowned_separate l1 ls1 pred1 l2 ls2 pred2 :
    l1 <> l2 -> lowned_perm l1 ls1 pred1 ⊥ lowned_perm l2 ls2 pred2.
  Proof.
    constructor; intros.
    - eapply lowned_lowned_separate_h; try apply Nat.neq_sym; eassumption.
    - eapply lowned_lowned_separate_h; eassumption.
  Qed.


  Lemma lowned_subsume l1 ls1 pred1 l2 ls2 pred2 :
    l1 <> l2 ->
    sep_step (lowned_perm l1 ls1 pred1 ** lowned_perm l2 ls2 pred2)
      (lowned_perm l1 (eq l2 \1/ ls1) pred1 ** lowned_perm l2 ls2 pred2).
  Proof.
    intro neq; apply sep_step_rg; intros.
    - destruct H as [? [? ?]].
      split; [ | split; [ | apply lowned_lowned_separate ]; assumption ].
      destruct H. split; [ assumption | ].
      repeat intro. apply H2. right; assumption.
    - induction H0; [ destruct H0 | ].
      + destruct H0 as [? | [? [? ?]]]; [ subst; reflexivity | ].
        apply t_step; left. right; split; [ | split ]; try assumption.
        intros; apply H2. right; assumption.
      + apply t_step; right; assumption.
      + etransitivity; [ apply IHclos_trans1; assumption | ].
        apply IHclos_trans2. eapply inv_guar; [ | eassumption ].
        apply H0_.
    - destruct H as [[? ?] [? ?]]. destruct H0. split; [ | assumption ].
      destruct H0. destruct H4.
      split; [ assumption | ]. repeat intro. destruct H8.
      + subst. rewrite <- H0. rewrite <- H4. apply H7; left; reflexivity.
      + apply H5; [ | assumption ]. repeat intro; apply H7; right; assumption.
  Qed.


  (* Note: does not have permission to start or end the lifetime [l] *)
  Program Definition when_perm (l : nat) (p : perm) : perm :=
    {|
      pre x := pre p x \/ lifetime (lget x) l = Some finished;

      rely x y :=
        statusOf_lte (lifetime (lget x) l) (lifetime (lget y) l) /\
        (* if the lifetime isn't ending or already ended, the rely of p must hold *)
        (rely p x y \/
           lifetime (lget y) l = Some finished /\ inv p y);

      guar x y :=
        x = y \/
          lifetime (lget x) l = Some current /\
          lifetime (lget y) l = Some current /\
          guar p x y;

      inv x := inv p x /\ statusOf_lte (Some current) (lifetime (lget x) l)
    |}.
  Next Obligation.
    constructor; repeat intro.
    - split; [ | left ]; reflexivity.
    - destruct H; destruct H0.
      split; [ etransitivity; eassumption | ].
      destruct H2; [ | right; assumption ].
      destruct H1.
      + left; etransitivity; eassumption.
      + destruct H1. right. split.
        * apply finished_lte_eq. rewrite <- H1. apply H0.
        * eapply inv_rely; eassumption.
  Qed.
  Next Obligation.
    constructor; repeat intro.
    - left; reflexivity.
    - destruct H; [ subst; assumption | ].
      destruct H0; [ subst; right; assumption | ].
      destruct H as [? [? ?]].
      destruct H0 as [? [? ?]].
      right; split; [ | split ]; try assumption.
      etransitivity; eassumption.
  Qed.
  Next Obligation.
    destruct H0.
    - destruct H1; [ | destruct H1; right; assumption ].
      left; eapply pre_respects; eassumption.
    - right; apply finished_lte_eq; rewrite <- H0; apply H.
  Qed.
  Next Obligation.
    split; [ destruct H2 | ].
    - eapply inv_rely; eassumption.
    - destruct H2; assumption.
    - change (statusOf_lte (Some current) (lifetime (lget y) l)).
      etransitivity; [ apply H1 | apply H ].
  Qed.
  Next Obligation.
    destruct H; [ subst; split; try assumption; apply H0 | ].
    destruct H as [? [? ?]].
    split.
    - eapply inv_guar; eassumption.
    - change (statusOf_lte (Some current) (lifetime (lget y) l)).
      rewrite <- H2; reflexivity.
  Qed.

  (* not true since the when cannot tolerate lifetime changes in its rely *)
  (*
    Lemma when_original n p Hp :
      when n p Hp <= p.
    Proof.
      intros. constructor; cbn; intros.
      - destruct x, x. cbn in *. auto.
      - destruct x, y, x, x0. cbn in *. split; auto. destruct Hp.
        specialize (H0 _ _ H). apply H0.
      - destruct x, y, x, x0. cbn in *. destruct H; auto.
        + rewrite H. reflexivity.
        + decompose [and] H; auto 7.
    Qed.
   *)

  Lemma when_monotone n p1 p2 : p1 <= p2 -> when_perm n p1 <= when_perm n p2.
  Proof.
    constructor; intros.
    - destruct H1; [ | right; assumption ].
      left. eapply pre_inc; eauto. apply H0.
    - destruct H1 as [? [? | [? ?]]].
      + split; [ assumption | ]. destruct H0.
        left; apply H; assumption.
      + split; [ assumption | ]. right; split; try assumption.
        apply H; assumption.
    - destruct H1 as [? | [? [? ?]]]; [ left; assumption | ].
      right; split; [ | split ]; try assumption.
      destruct H0. apply H; assumption.
    - destruct H0. split; [ | assumption ].
      apply H; assumption.
  Qed.


  Program Definition after_perm l p : perm :=
    {|
      (** [l] must be current *)
      pre x := lifetime (lget x) l = Some finished -> pre p x;

      rely x y :=
        statusOf_lte (lifetime (lget x) l) (lifetime (lget y) l) /\
          (inv p x -> inv p y) /\
          ((lifetime (lget x) l = Some finished -> pre p x) ->
           lifetime (lget y) l = Some finished -> pre p y) /\
          (lifetime (lget x) l = Some finished -> rely p x y);

      (** If [l] is finished afterwards, the guar of [p] holds *)
      guar x y :=
        x = y \/
          lifetime (lget x) l = Some finished /\
            lifetime (lget y) l = Some finished /\
            guar p x y;

      inv x := inv p x /\ statusOf_lte (Some current) (lifetime (lget x) l)
    |}.
  Next Obligation.
    constructor; intros.
    - split; [ reflexivity | ]. split; [ intro; assumption | ].
      split; [ intros; auto | ]. intro; reflexivity.
    - intros x y z [? [? [? ?]]] [? [? [? ?]]].
      split; [ etransitivity; eassumption | ].
      split; [ auto | ].
      split; [ auto | ].
      intro; etransitivity; auto.
      apply H6. apply finished_lte_eq. rewrite <- H7. assumption.
  Qed.
  Next Obligation.
    constructor; intros.
    - left; reflexivity.
    - intros x y z Hxy Hyz.
      destruct Hxy; [ subst; assumption | ].
      destruct Hyz as [? | [? [? ?]]]; [ subst; right; assumption | ].
      destruct H as [? [? ?]]. right.
      split; [ assumption | ]. split; [ assumption | ]. etransitivity; eassumption.
  Qed.
  Next Obligation.
    split; [ auto | ].
    change (statusOf_lte (Some current) (lifetime (lget y) l)).
    etransitivity; eassumption.
  Qed.
  Next Obligation.
    destruct H; [ subst; split; assumption | ]. destruct H as [? [? ?]].
    split; [ eapply inv_guar; eassumption | ].
    change (statusOf_lte (Some current) (lifetime (lget y) l)).
    rewrite H2; simpl; trivial.
  Qed.

  Lemma separate_when_after l p : when_perm l p ⊥ after_perm l p.
  Proof.
    constructor; intros.
    - destruct H1 as [ ? | [? [? ?]]]; [ subst; reflexivity | ].
      split; [ rewrite H1; rewrite H2; reflexivity | ].
      right; split; [ assumption | ].
      destruct H0. eapply inv_guar; eassumption.
    - destruct H1 as [ ? | [? [? ?]]]; [ subst; reflexivity | ].
      split; [ rewrite H1; rewrite H2; reflexivity | ].
      split; [ intro; eapply inv_guar; eassumption | ].
      rewrite H1; rewrite H2.
      split; intros; discriminate.
  Qed.

  Lemma separate_when_lowned l ls pred p :
    p ⊥ lowned_perm l ls pred ->
    when_perm l p ⊥ lowned_perm l ls (pred /1\ pre p).
  Proof.
    constructor; intros.
    - destruct H2 as [ ? | [? [[? ?] ?]]]; [ subst; reflexivity | ]. subst. simpl.
      rewrite lGetPut. unfold lifetime; rewrite nth_error_replace_list_index_eq.
      split; [ apply finished_greatest | ].
      destruct H1. left; apply (sep_l _ _ H); try assumption.
      right; split; [ reflexivity | ]; split; assumption.
    - destruct H2 as [ ? | [? [? ?]]]; [ subst; reflexivity | ]. destruct H0.
      assert (rely (lowned_perm l ls pred) x y) as [? ?];
        [ apply (sep_r _ _ H); assumption | ].
      split; assumption.
  Qed.

  Lemma separate_after_lowned l ls pred p :
    p ⊥ lowned_perm l ls pred ->
    after_perm l p ⊥ lowned_perm l ls (pred /1\ pre p).
  Proof.
    constructor; intros.
    - destruct H1. destruct H2 as [ ? | [? [[? ?] ?]]]; [ subst; reflexivity | ].
      assert (rely p x y).
      + apply (sep_l _ _ H); try assumption.
        right; split; [ | split ]; assumption.
      + subst. simpl.
        rewrite lGetPut. unfold lifetime; rewrite nth_error_replace_list_index_eq.
        split; [ apply finished_greatest | ].
        split; [ intro; eapply inv_rely; eassumption | ].
        split; intros; assumption.
    - destruct H2 as [ ? | [? [? ?]]]; [ subst; reflexivity | ]. destruct H0.
      assert (rely (lowned_perm l ls pred) x y) as [? ?];
        [ apply (sep_r _ _ H); assumption | ].
      split; assumption.
  Qed.

  Lemma separate_when_after_lowned l ls pred p :
    p ⊥ lowned_perm l ls pred ->
    when_perm l p ** after_perm l p ⊥ lowned_perm l ls (pred /1\ pre p).
  Proof.
    symmetry; apply sep_conj_perm_separate; symmetry;
      [ apply separate_when_lowned | apply separate_after_lowned ]; assumption.
  Qed.

  Lemma perm_split_lt p l ls pred :
    (when_perm l p ** after_perm l p) ** (lowned_perm l ls (pred /1\ pre p))
    <= p ** lowned_perm l ls pred.
  Proof.
    constructor; intros.
    - simpl in H0; destruct H0.
      split; [ split | ]; [ left | intro | ]; assumption.
    - destruct H0 as [? [? ?]].
      simpl. split; [ split | ]; split; try assumption.
      + rewrite H1. reflexivity.
      + left; assumption.
      + rewrite H1; reflexivity.
      + split; [ intro; eapply inv_rely; eassumption | ].
        split; [ | intro; assumption ].
        rewrite H1. intros. eapply pre_respects; try eassumption. auto.
    - simpl in H0. rewrite clos_trans_clos_trans_or in H0. clear H.
      induction H0; [ destruct H; [ destruct H | ] | ].
      + destruct H as [? | [? [? ?]]]; [ subst; reflexivity | ].
        apply t_step; left; assumption.
      + destruct H as [? | [? [? ?]]]; [ subst; reflexivity | ].
        apply t_step; left; assumption.
      + destruct H as [? | [? [[? ?] ?]]]; [ subst; reflexivity | ].
        apply t_step; right; right.
        split; [ assumption | ]. split; assumption.
      + etransitivity; eassumption.
    - destruct H as [? [[? ?] ?]].
      split; split.
      + split; assumption.
      + split; [ split; assumption | ]. apply separate_when_after.
      + split; assumption.
      + apply separate_when_after_lowned; assumption.
  Qed.


  (* Needed to prove the following associativity lemma *)
  Lemma sep_after_lowned_sep_after l ls pred p q :
    after_perm l p ⊥ after_perm l q ** lowned_perm l ls pred ->
    after_perm l p ⊥ after_perm l q.
  Admitted.

  (* I think this will be useful for the lowned rules *)
  Lemma after_after_lowned_assoc l ls pred p q :
    after_perm l p ⊥ after_perm l q ** lowned_perm l ls pred ->
    (lowned_perm l ls pred ** (after_perm l p ** after_perm l q))
    <= ((lowned_perm l ls pred ** after_perm l p) ** after_perm l q).
  Proof.
    intro. apply sep_conj_perm_assoc'. eapply sep_after_lowned_sep_after.
    eassumption.
  Qed.


  (* l1 is current whenever l2 is current, i.e., Some current <= l1 <= l2. This
  means that l1 is an ancestor of l2, i.e., a larger lifetime containing l2. *)
  Definition lcurrent l1 l2 :=
    invperm (fun x =>
               statusOf_lte (Some current) (lifetime (lget x) l1) /\
                 statusOf_lte (lifetime (lget x) l1) (lifetime (lget x) l2)).

  Lemma lcurrent_trans l1 l2 l3 :
    lcurrent l1 l3 <= lcurrent l1 l2 ** lcurrent l2 l3.
  Proof.
    constructor; intros.
    - apply I.
    - destruct H as [[? ?] [[? ?] ?]]. destruct H0 as [? ?].
  Admitted.


  (* Lifetime l is finished *)
  Definition lfinished l :=
    invperm (fun x => lifetime (lget x) l = Some finished).

  (* If l is finished then we can recover a permission from an after_perm *)
  Lemma lfinished_after l p : p <= lfinished l ** after_perm l p.
  Proof.
  Admitted.


  (***
   *** Lifetime ownership permission set
   ***)

  (* The set of lowned_perm l ls pred permissions for some pred *)
  Definition lowned_set l ls :=
    mkPerms (fun r => exists pred, r = lowned_perm l ls pred).

  (* The set of lowned permissions along with assertions of their preds *)
  Definition lowned_pre_set l ls :=
    mkPerms (fun r => exists pred, r = preperm pred ** lowned_perm l ls pred).

  (* The set of permissions after_perm l p for all p in P *)
  Definition after_set l P :=
    mkPerms (fun r => exists p, in_Perms P p /\ r = after_perm l p).

  (* The lifetime ownership permission set, which says:
     1. We currently own lifetime l with sub-lifetimes in ls; and
     2. If we give back any permission in P, we can end l and get back Q *)
  Definition lowned l ls P Q :=
    join_Perms2
      (lowned_set l ls)
      (impl_Perms P (lowned_pre_set l ls * after_set l Q)).


FIXME: old stuff below

    Program Definition lcurrent l1 l2
            (H : forall (x : {x : Si * Ss | interp_LifetimeClauses c x}),
                let '(si, _) := x in subsumes l1 l2 (lget si) (lget si)) :
      @perm {x : Si * Ss | interp_LifetimeClauses c x} :=
      {|
        pre x := True;
        rely x y := True;
        guar x y := x = y;
      |}.
    Next Obligation.
      constructor; repeat intro; auto.
    Qed.

    Lemma lcurrent_sep n1 n2 H :
      lcurrent n1 n2 H ⊥ lcurrent n1 n2 H.
    Proof.
      constructor; intros ? ? []; reflexivity.
    Qed.

    Lemma lcurrent_transitive n1 n2 n3 H12 H23 H13 :
      lcurrent n1 n3 H13 <= lcurrent n1 n2 H12 ** lcurrent n2 n3 H23.
    Proof.
      constructor; intros; cbn in *; intuition.
    Qed.

    Lemma lcurrent_when n1 n2 p H Hp :
      lcurrent n1 n2 H ** when n2 p Hp <= lcurrent n1 n2 H ** when n1 p Hp.
    Proof.
      constructor; intros.
      - destruct x, x. cbn in *. destruct H0 as (_ & ? & ?). split; [| split]; auto.
        + intro. apply H0. destruct H2.
          * clear H1. specialize (H (exist _ _ i)).
            eapply subsumes_2_none_inv; eauto.
          * clear H1. specialize (H (exist _ _ i)).
            right. eapply subsumes_2_current_inv; eauto.
        + constructor; intros; cbn in *; subst; auto.
          destruct y, x. cbn. split; reflexivity.
      - destruct x, y, x, x0. cbn in *.
        split; auto. destruct H0 as [_ ?].
        destruct H0 as (? & ?). split; auto.
        intros [].
        + apply H1; auto.
          specialize (H (exist _ _ i0)).
          eapply subsumes_2_none_inv; eauto.
        + apply H1; auto. right.
          specialize (H (exist _ _ i0)).
          eapply subsumes_2_current_inv; eauto.
    - cbn in *. induction H0. 2: econstructor 2; eauto.
      destruct H0; subst; try solve [constructor; auto].
      destruct x, y, x, x0. cbn in *.
      destruct H0; subst; try solve [constructor; auto].
      destruct H0 as (? & ? & ? & ?).
      constructor 1. right. right.
      split; [| split; [| split]]; auto.
      + specialize (H (exist _ _ i)).
        eapply subsumes_2_current_inv; eauto.
      + specialize (H (exist _ _ i0)).
        eapply subsumes_2_current_inv; eauto.
    Qed.
  End asdf.


  Definition when_Perms l P : Perms2 :=
    meet_Perms2 (fun R => exists c p Hp, p ∈2 P /\ R = singleton_Perms2 _ (when c l p Hp)).

  Lemma when_perm_Perms c l p Hp P :
    p ∈2 P ->
    when c l p Hp ∈2 when_Perms l P.
  Proof.
    intros H.
    eexists. split.
    - exists c. exists p. eexists. split. 2: reflexivity. apply H.
    - exists (fun _ H => H). red. rewrite restrict_same. reflexivity.
  Qed.

  (* when l (read_Perms ptr) * lowned l (when l (read_Perms ptr) -o write_Perms ptr) ⊢
     endLifetime l :
     write_Perms p *)

  (* p ∈ read_Perms ptr * lowned l (read_Perms ptr -o write_Perms ptr) *)
  (* -> p >= r * l *)
  (* pre p s is true, so pre of both are true *)

  (* r ∈ read_Perms ptr *)
  (* -> r ≈ read_perm ptr v, for some v *)

  (* l ∈ lowned l .... *)
  (* ∃ w, w ∈ write_Perms ptr /\ l >= owned l w /\
     (forall s, lifetime s = current -> pre r s -> pre l s -> pre w s) *)
  (* -> w ≈ write_perm ptr v, for some v *)

  (* currently "lending" P, and will "return" Q when l ends (and P is provided to lowned). *)
  Definition lowned_Perms l ls Hsub P Q : Perms2 :=
    meet_Perms2 (fun R => (* forall c (p : @perm {x : Si * Ss | interp_LifetimeClauses c x}), p ∈2 P -> *)
                            exists c r q Hq,
                              R = singleton_Perms2 _ (r ** owned c l ls (Hsub c) q Hq) /\
                                q ∈2 Q /\ (* q also has the spred c *)
                                (* r ∈2 (impl_Perms2 P Q) /\ *)
                                (forall p, p ∈2 P -> exists q, q ∈2 Q /\
                                                      (forall s, pre p s -> pre r s -> pre q s))).
  (* remove r? *)

  (* x = owned l (write_perm ptr v) ** pred_perm (ptr |-> v) *)
  (* x ∈ lowned l (read_Perms ptr -o write_Perms ptr) *)
  (* forall r ∈ read_Perms ptr (r ≈ read_perm ptr v', for some v')
     exists w ∈ write_Perms ptr. (pick w = write_perm ptr v)
   x >= owned l w *)


  (* p  \in   lowned l (P1 * P2) Q    /\   p'  \in P1
     then    pred_perm (pre p') ** p   \in  lowned l P2 Q
   *)
  Program Definition lowned_Perms' l ls Hsub (P Q : @Perms2 (Si * Ss)) : Perms2 :=
    {|
      in_Perms2 := fun spred x =>
                     exists c Hspred r1 r2 Hnlr2,
                       r2 ∈2 Q /\
                         hlte_perm2 (Si * Ss) spred (interp_LifetimeClauses c) Hspred
                           (r1 ** owned c l ls (Hsub c) r2 Hnlr2) x /\
                         forall (p : @perm {x : Si * Ss | interp_LifetimeClauses c x}),
                           p ∈2 P ->
                           exists (q : @perm {x : Si * Ss | interp_LifetimeClauses c x}),
                             q ∈2 Q /\
                               sep_step _ (interp_LifetimeClauses c) (interp_LifetimeClauses c) (fun _ H => H) r2 q /\
                               (forall c1 c2 (Hc : interp_LifetimeClauses c (c1, c2)),
                                   pre p ((lput c1 (replace_list_index (lget c1) l current)), c2) ->
                                   pre r1 ((lput c1 (replace_list_index (lget c1) l current)), c2) ->
                                   pre q ((lput c1 (replace_list_index (lget c1) l finished)), c2));
    |}.
  Next Obligation.
    cbn.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
    rename H into c, H1 into Hspred'.
    exists c. eexists. Unshelve.
    2: { intros. apply Hspred'. apply Hspred. apply H. }
    exists H2, H3, H4. split; auto. split; auto.
    - eapply hlte_perm2_transitive; eauto.
    - intros. (* eapply H7. apply H7. *)
  Admitted.

  Program Definition lowned_Perms'' l ls Hsub (P Q : @Perms2 (Si * Ss)) : Perms2 :=
    {|
      in_Perms2 := fun spred x =>
                     exists c Hspred,
                     forall (p : @perm {x : Si * Ss | interp_LifetimeClauses c x}),
                       p ∈2 P ->
                       exists (q : @perm {x : Si * Ss | interp_LifetimeClauses c x}) Hq,
                         q ∈2 Q /\
                           hlte_perm2
                             (Si * Ss) spred (interp_LifetimeClauses c) Hspred
                             (owned c l ls (Hsub c) q Hq)
                             x /\
                           (forall s, pre p _ -> pre x s -> pre q _);
    |}.
  Next Obligation.
    esplit. apply Hspred. apply H.
  Defined.
  Next Obligation.
    esplit. apply Hspred. apply H.
  Defined.
  Next Obligation.
    rename H into c. rename H1 into Hspred'.
    exists c. eexists. Unshelve. 2: { auto. } intros p Hp.
    specialize (H2 p). destruct H2 as (q & Hq' & Hq & Hhlte & Hpre); auto.
    exists q, Hq'. split; auto. split; auto.
    - eapply hlte_perm2_transitive; eauto.
    - intros [[]]. specialize (Hpre (exist _ _ (Hspred _ s1))). cbn in *.
      intros. apply Hpre; auto.
      red in H0. apply H0 in H1. cbn in H1. apply H1.
  Qed.

  Lemma lowned_perm_Perms c l ls Hsub p Hp P :
    p ∈2 P ->
    owned c l ls (Hsub c) p Hp ∈2 lowned_Perms l ls Hsub P P.
  Proof.
  (*   intros. cbn. do 4 eexists. split; eauto. split. *)
  (*   - red. rewrite restrict_same. reflexivity. *)
  (*   - intros. *)
  (*   Unshelve. intros. auto. *)
  (* Qed. *)
    (* cbn. intros. exists p0. eexists. eexists. *)
    (* split. auto. split. *)
    (* 2: { intros. auto. } *)


    intros. cbn. eexists. split.
    - do 4 eexists. split; [| split]. reflexivity.
      apply H.
      clear p H Hp. intros p Hp. exists p. split; auto.
    - exists (fun _ H => H). red. rewrite restrict_same.
      rewrite sep_conj_perm_commut. rewrite sep_conj_perm_bottom. reflexivity.
  Qed.

  Definition lte_Perms' (P Q : Perms2) : Prop :=
    forall (c : LifetimeClauses) (p : @perm {x | interp_LifetimeClauses c x}), p ∈2 Q -> p ∈2 P.
  Definition entails P Q := lte_Perms' Q P.

  (* Lemma foo l P : *)
  (*   entails P (when_Perms l P). *)
  (* Proof. *)
  (*   repeat intro. cbn. eexists. split. *)
  (*   - do 2 eexists. split; [| reflexivity]. eapply H. Set Printing All. admit. *)
  (*   - Unset Printing All. cbn. eexists. *)

  Lemma restrict_owned c c' Hspred l ls Hsub p Hp:
    restrict (Si * Ss) (interp_LifetimeClauses c) (interp_LifetimeClauses c') Hspred
             (owned c' l ls Hsub p Hp) <=
      owned c l ls (fun x Hc => Hsub x (Hspred _ Hc)) (restrict _ _ _ Hspred p) (nonLifetime_restrict _ _ Hspred p Hp).
  Proof.
    constructor.
    - intros [[]] ?. cbn in *. auto.
    - intros [[]] [[]] ?. cbn in *. auto.
    - intros [[]] [[]] ?. cbn in *. intuition.
      left. inversion H0. subst. clear H0.
      rewrite (ProofIrrelevance.proof_irrelevance _ i i0). reflexivity.
  Qed.

  Lemma restrict_owned' c c' Hspred l ls Hsub p Hp:
    owned c l ls (fun x Hc => Hsub x (Hspred _ Hc)) (restrict _ _ _ Hspred p) (nonLifetime_restrict _ _ Hspred p Hp) <=
      restrict (Si * Ss) (interp_LifetimeClauses c) (interp_LifetimeClauses c') Hspred
               (owned c' l ls Hsub p Hp).
  Proof.
    constructor.
    - intros [[]] ?. cbn in *. auto.
    - intros [[]] [[]] ?. cbn in *. auto.
    - intros [[]] [[]] ?. cbn in *. intuition.
      left. inversion H0. subst. clear H0.
      rewrite (ProofIrrelevance.proof_irrelevance _ i i0). reflexivity.
  Qed.

  Lemma obvious l ls Hsub P Q :
    entails (lowned_Perms'' l ls Hsub bottom_Perms2 Q)
            (lowned_Perms'' l ls Hsub P Q).
  Proof.
    intros c p' H. cbn in H.
    destruct H as (c' & Hspred & ?).
    exists c', Hspred. intros.
    specialize (H p I). apply H.
  Qed.

  Lemma typing_end l ls Hsub P Q :
    @typing Si Ss LifetimeClauses interp_LifetimeClauses _ _
      (P *2 (lowned_Perms' l ls Hsub P Q))
      (fun _ _ => Q)
      (endLifetime l)
      (Ret tt).
  Proof.
    intros c p' c1 c2 Hc (p & lowned' & Hp & Hl & Hlte) Hpre.
    cbn in Hl.
    destruct Hl as (c' & Hspred & Hl).
    (* specialize (Hl (restrict _ _ _ Hspred p) Hp). destruct Hl as (Hspred & q & Hq' & Hq & Hhlte & Hpre'). *)
    destruct Hl as (r1 & r2 & Hnlr2 & Hr2 & Hhltge & Hf).
    unfold endLifetime. unfold id.
    rewritebisim @bind_trigger.
    pstep. econstructor; eauto; try reflexivity. cbn. reflexivity.

    pose proof Hpre as Hpre''.
    apply Hlte in Hpre. destruct Hpre as (_ & ? & _). apply Hhlte in H.
    cbn in H. destruct H as (_ & ? & _). unfold lifetime in H. setoid_rewrite H.

    rewritebisim @bind_trigger.
    (* specialize (Hf (restrict _ _ _ Hspred p)). *)


    econstructor; unfold id. eauto.
    cbn in *. apply Hlte. constructor 1. right.
    apply Hhlte. cbn. right.
    {
      rewrite lGetPut.
      split; [| split].
      - admit.
      - unfold lifetime. apply nth_error_replace_list_index_eq.
      - red in Hq'. (* TODO update defn of nonLifetime *) admit.
    }

    2: {
      assert (asdf: interp_LifetimeClauses c (lput c1 (replace_list_index (lget c1) l finished), c2)) by admit.

      econstructor. 2: apply Hq.
      Unshelve. 2: auto.
      3: apply asdf.
      specialize (Hpre' (exist (fun x : Si * Ss => interp_LifetimeClauses c x)
                               (lput c1 (replace_list_index (lget c1) l finished), c2) asdf)).
      cbn in *.
      erewrite (ProofIrrelevance.proof_irrelevance _ asdf).
      apply Hpre'. admit. admit. (* how is this even true here *)
      admit.
    }

    (* ok plausible, since q should be inside the rely and guar of p' *)
    admit.
  Abort.
*)

  Lemma join_commut' c l ls Hsub p Hp powned asdf asdf' asdf'':
    join_perm' (fun pp => exists q Hq, owned c l ls Hsub q Hq <= powned /\
                                  pp = owned c l ls Hsub (p ** q) (nonLifetime_sep_conj _ _ _ Hp Hq)) asdf <=
      owned c l ls Hsub (p ** (join_perm' (fun q => exists Hq, owned c l ls Hsub q Hq <= powned) asdf')) asdf''
  .
  Proof.
    constructor.
    - intros [[]] ? ? ?. cbn in *. destruct H0 as (? & ? & ? & ?). subst. cbn. auto.
    - intros [[]] [[]] ? ? ?. cbn in *. destruct H0 as (? & ? & ? & ?). subst. cbn.
      destruct H as (? & ? & ?). split; auto. split; auto.
      intros. destruct H2; auto. split; auto.
      apply H4. eauto.
    - intros ? ? ?. cbn in H. induction H. 2: etransitivity; eauto.
      destruct H as (? & ? & ?). destruct H as (q & Hq & Hlte & ?). subst.
      destruct x, y, x, x0. cbn in *.
      destruct H0; auto.
      right. destruct H as (? & ? & ?). split; auto. split; auto.
      (* constructor. right. constructor. eexists. split. exists q, Hq. split; auto. *)
      cbn.
      clear H0.
      remember (exist _ _ i). remember (exist _ _ i0).
      revert s s0 s1 s2 i i0 H Heqs3 Heqs4. clear asdf asdf' asdf''.
      induction H1; intros; subst.
      + constructor 1. destruct H; auto.
        right. constructor 1. eexists. split; eauto.
      + destruct y, x.
        specialize (IHclos_trans2 s3 s4). specialize (IHclos_trans1 s s0 s3 s4).
        assert (Lifetimes_lte (lget s3) (lget s1)).
        {
          clear IHclos_trans1 IHclos_trans2 H H1_ s s0 i Hlte powned.
          remember (exist _ _ i1). remember (exist _ _ i0).
          revert s1 s2 s3 s4 i0 i1 Heqs Heqs0.
          rename H1_0 into H.
          induction H; intros; subst.
          - destruct H.
            + apply Hp in H. cbn in *. rewrite H. reflexivity.
            + apply Hq in H. cbn in *. rewrite H. reflexivity.
          - subst. destruct y, x. specialize (IHclos_trans1 s s0 s3 s4).
            etransitivity. eapply IHclos_trans1; eauto.
            eapply IHclos_trans2; eauto.
        }
        assert (Lifetimes_lte (lget s) (lget s3)).
        {
          clear IHclos_trans1 IHclos_trans2 H H0 H1_0 s1 s2 i0 Hlte powned.
          remember (exist _ _ i1). remember (exist _ _ i).
          revert s s0 s3 s4 i i1 Heqs1 Heqs2.
          rename H1_ into H.
          induction H; intros; subst.
          - destruct H.
            + apply Hp in H. cbn in *. rewrite H. reflexivity.
            + apply Hq in H. cbn in *. rewrite H. reflexivity.
          - subst. destruct y, x. specialize (IHclos_trans1 s s0 s1 s2).
            etransitivity. eapply IHclos_trans1; eauto.
            eapply IHclos_trans2; eauto.
        }
        econstructor 2; eauto.
  Qed.


  (*
    Lemma join_commut c l ls Hsub p Hp powned asdf asdf' asdf'':
    join_perm' (fun pp => exists q Hq, owned c l ls Hsub q Hq <= powned /\
                                  pp = owned c l ls Hsub (p ** q) (nonLifetime_sep_conj _ _ _ Hp Hq)) asdf <=
      owned c l ls Hsub (p ** (join_perm' (fun pp => exists q Hq, owned c l ls Hsub q Hq <= powned /\
                        pp = owned c l ls Hsub q Hq) asdf')) asdf''
  .
  Proof.
    constructor.
    - intros [[]] ? ? ?. cbn in *. destruct H0 as (? & ? & ? & ?). subst. cbn. auto.
    - intros [[]] [[]] ? ? ?. cbn in *. destruct H0 as (? & ? & ? & ?). subst. cbn.
      destruct H as (? & ? & ?). split; auto. split; auto.
      intros.
      destruct H2; auto. split; auto.
      specialize (H4 (owned c l ls Hsub x x0)).
      cbn in H4. apply H4; auto. do 2 eexists. split; eauto.
    - intros ? ? ?. cbn in H. induction H. 2: etransitivity; eauto.
      destruct H as (? & ? & ?). destruct H as (q & Hq & Hlte & ?). subst.
      destruct x, y, x, x0. cbn in *.
      destruct H0; auto.
      right. destruct H as (? & ? & ?). split; auto. split; auto.
      (* constructor. right. constructor. eexists. split. exists q, Hq. split; auto. *)
      cbn.
      remember (exist _ _ i). remember (exist _ _ i0).
      revert s s0 s1 s2 i i0 H H0 Heqs3 Heqs4. clear asdf asdf' asdf''.
      induction H1; intros; subst.
      + constructor 1. destruct H; auto.
        right. constructor 1. eexists. split. exists q, Hq. split; auto. cbn.
        right. auto.
      + destruct y, x.
        specialize (IHclos_trans2 s3 s4). specialize (IHclos_trans1 s s0 s3 s4).
        assert (Lifetimes_lte (lget s3) (lget s1)) by admit.
        assert (Lifetimes_lte (lget s) (lget s3)) by admit.
        econstructor 2.
        2: eapply IHclos_trans2; eauto.
        clear IHclos_trans2 H1_0 s1 s2 i0 H H0 H1.

        eapply IHclos_trans1; eauto. admit. (* TODO: I think we need to do more case analysis here *)
  Admitted.
   *)

  Lemma foo l ls Hsub P Q R :
    entails (P *2 (lowned_Perms' l ls Hsub R Q))
            (when_Perms l P *2 (lowned_Perms' l ls Hsub (P *2 R) (P *2 Q))).
  Proof.
    intros c p' H. cbn in H.
    destruct H as (p & powned & Hp & ? & Hlte); subst.
    (* do 2 eexists. *)
    eexists.
    (* assert (Hpr : forall r, nonLifetime c r) by admit. *)
    eexists (join_perm' (fun p' => exists q Hq, owned c l ls (Hsub c) q Hq <= powned /\
                                       p' = owned c l ls (Hsub c) (p ** q) _) _).
    split; [| split].
    3: {
      etransitivity. 2: apply Hlte. etransitivity.
      apply sep_conj_perm_monotone; [reflexivity |].
      apply join_commut'.
      etransitivity. apply convert. apply sep_conj_perm_monotone; [reflexivity |].
      destruct H as (? & ? & ?).
      specialize (H c). unfold hlte_perm2 in H. setoid_rewrite restrict_same in H.
      (* edestruct H as (? & ? & ? & ? & ? & ?). admit. *)
      constructor.
      - intros [[]]. cbn. admit.
      - intros [[]] [[]]. cbn. intros. intuition. admit. admit.
        destruct H2. apply H2 in H0. cbn in H0. apply H0; auto.
      - intros [[]] [[]]. cbn. intros. destruct H0. rewrite H0. reflexivity.
        intuition.
        assert (lifetime (lget s) l = Some finished).
        {
          remember (exist _ _ i). remember (exist _ _ i0).
          revert s s0 i s1 s2 i0 Heqs3 Heqs4 H1 H0.
          induction H3; intros; subst.
          - destruct H0 as (? & (? & ?) & ?). apply x0 in H3. cbn in *. rewrite H3. auto.
          - destruct y, x.
            eapply (IHclos_trans1 _ _ _ _ _ _ eq_refl eq_refl); eauto.
            admit.
            eapply (IHclos_trans2 _ _ _ _ _ _ eq_refl eq_refl); eauto.
            admit.
        }
        remember (exist _ _ i). remember (exist _ _ i0).
        revert s s0 i s1 s2 i0 Heqs3 Heqs4 H1 H0 H2.
        induction H3; intros; subst.
        + destruct H0. destruct H0. destruct H0. apply H0. right. intuition.
        + destruct y, x.
          etransitivity.
          eapply (IHclos_trans1 _ _ _ _ _ _ eq_refl eq_refl); eauto. admit. admit.
          eapply (IHclos_trans2 _ _ _ _ _ _ eq_refl eq_refl); eauto. admit. admit.
    }
    apply when_perm_Perms; auto.
    intros ? ? ?.
    eexists.

    (* Set Printing All. *)
    (* do 2 eexists. split; [| split]. *)
    2: { cbn. do 3 eexists. split.
         - do 2 eexists. split. reflexivity. split.
           + exists p, (restrict _ _ _ Hspred q). split; auto.
             split. 2: reflexivity.
             eapply Perms2_upwards_closed. apply Hq.
             red. reflexivity.
           + intros. cbn.
             destruct H as (? & ? & ? & ? & ?).
             (* destruct (H0 x0). *)
             admit.
         - eexists. red. rewrite restrict_same. reflexivity.
    }
    - apply when_perm_Perms. apply Hp.
    - rewrite <- sep_conj_perm_assoc. rewrite sep_conj_perm_commut.
      etransitivity. red in Hhlte. eapply convert.


             split; [| split].
             2: {
               destruct s, x1. cbn. eapply H0.
               eapply Perms2_upwards_closed. apply H2.
               red. reflexivity.
               cbn. apply H3. admit.
             }
             admit. admit.
             * destruct H as (? & ? & ? & ? & ?).

    3: {
      etransitivity. 2: apply Hlte.
      etransitivity. eapply convert. apply sep_conj_perm_monotone. reflexivity.
      red in Hhlte. etransitivity. 2: apply Hhlte.
      etransitivity. 2: apply restrict_owned'. reflexivity.
    }
    - apply when_perm_Perms; auto.
    - eexists. split.
      + do 3 eexists. split. reflexivity. split.
        (* * (* Set Printing All. do 2 eexists. split; [| split]. apply Hp. apply Hq. reflexivity. *) *)
        2: { intros. destruct H as (? & ? & ? & ? & ?). eapply H0. apply H2. apply H3. auto. }
        admit.
      + cbn. exists Hspred. red. rewrite restrict_owned. rewrite <- (restrict_same _ _ p).

  Qed.

  (* we need to know R includes a nonlifetime perm *)
  Lemma foo l ls Hsub P Q R :
    entails (R *2 lowned_Perms l ls Hsub P Q)
            (when_Perms l R).
  Proof.
    repeat intro. cbn in *.
    destruct H as (r & pl & Hr & (? & (c' & q & Hq' & ? & Hq & ?) & asdf) & Hlte).
    subst. destruct asdf as (Hspred & Hhlte). eexists. split.
    - do 3 eexists. split; [| reflexivity]. eapply Hr.
    - cbn. exists (fun H x => x). red. rewrite restrict_same.
      etransitivity. eapply when_original.
      etransitivity; eauto. apply lte_l_sep_conj_perm.
      Unshelve.
  Qed.


  Lemma foo l ls Hsub P Q R :
    R *2 lowned_Perms l ls Hsub P Q ⊨2
         when_Perms l R.
  Proof.
    repeat intro. destruct H as (r & Hp' & Hr & (? & (q & Hq' & ? & Hq & ?) & asdf) & Hlte).
    subst. destruct asdf as (Hspred & Hhlte). eexists. split.
      - do 2 eexists. split. 2: reflexivity.
        Set Printing All.
    Qed.

      (* lowned_Perms l ls Hsub (P *2 when_Perms l R) (Q *2 R). *)
    Proof.
      repeat intro. cbn in H.
      destruct H as (r & p' & Hr & (? & ((q & Hqnonlifetime & ? & Hq & Hpre) & Hp')) & Hlte).
      subst. destruct Hp' as (Hspred & Hhlte). cbn. Set Printing All.
      eexists. split.
      - do 2 eexists. Set Printing All. split. reflexivity. split.
        + Set Printing All.
          eapply Perms2_upwards_closed. Unshelve. 6: { intros ? asdf. apply asdf. }
                                                Set Printing All.
                                                apply sep_conj_Perms2_perm.
          2: apply Hr.
          eapply Perms2_upwards_closed; eauto. red. Unshelve.
          red. Unshelve. 4: apply Hspred.
        2: { intros pr (p'' & q'' & Hp'' & Hq'' & Hpr).
             intros. eapply Hpre; eauto. apply Hpr. auto. }

        + do 2 eexists. split; [| split]. 3: reflexivity. admit. admit.
        + intros p''' (p'' & ? & (? & (? & (? & ? & ? & ?) & ?) & ?)). subst.
          cbn in H2. destruct H2 as (? & ?). red in H1. rewrite restrict_same in H1.
          clear x0. intros [] ? ?. admit.
      - exists Hspred. red. red in Hp'.
          split.
          * eapply Hpre; auto.
            apply H. apply Hp'. apply Hp. apply H1.
            apply H3. apply H4.
          * split; auto. apply Hp. auto.
            apply Hp in H1. destruct H1 as (? & ? & ?).
            symmetry. eapply separate_antimonotone. apply H6.
            apply Hp'.
            apply Hp' in H5. destruct H5 as (? & ? & ?).
      - eapply Perms2_upwards_closed. 2: { red. rewrite restrict_same. eapply Hlte. }
                                    cbn.




      destruct H as (r & p' & Hr & (P' & (r' & q & Hq' & ? & Hq & Hpre) & Hp') & Hp).
      subst. destruct Hp' as (Hspred & Hp'). cbn in *.
      eexists. split.
      - do 3 eexists. split. reflexivity. split.
        + do 2 eexists. split; [| split]. 3: reflexivity. admit. admit.
        + intros p''' (p'' & ? & (? & (? & (? & ? & ? & ?) & ?) & ?)). subst.
          cbn in H2. destruct H2 as (? & ?). red in H1. rewrite restrict_same in H1.
          clear x0. intros [] ? ?. admit.
      - exists Hspred. red. red in Hp'.
          split.
          * eapply Hpre; auto.
            apply H. apply Hp'. apply Hp. apply H1.
            apply H3. apply H4.
          * split; auto. apply Hp. auto.
            apply Hp in H1. destruct H1 as (? & ? & ?).
            symmetry. eapply separate_antimonotone. apply H6.
            apply Hp'.
            apply Hp' in H5. destruct H5 as (? & ? & ?).
            cbn in H8.
    Qed.
*)

  End asdf.


  Lemma foo l ls Hsub P Q R :
    entails (R *2 lowned_Perms l ls Hsub P Q)
            (when_Perms l R).
  Proof.
    repeat intro. destruct H as (r & Hp' & Hr & (? & (q & Hq' & ? & Hq & ?) & asdf) & Hlte).
    subst. destruct asdf as (Hspred & Hhlte). eexists. split.
    - do 2 eexists. split; [| reflexivity]. eapply Hr.
      Set Printing All.
  Qed.
End LifetimePerms.
