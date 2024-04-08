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

Global Instance PreOrder_trivial {A} : @PreOrder A (fun _ _ => True).
Proof.
  constructor; repeat intro; trivial.
Qed.

Global Instance PreOrder_and {A} (R1 R2 : A -> A -> Prop) `{PreOrder A R1} `{PreOrder A R2} :
  PreOrder (fun x y => R1 x y /\ R2 x y).
Proof.
  constructor; repeat intro.
  - split; reflexivity.
  - destruct H1; destruct H2; split; etransitivity; eassumption.
Qed.

Global Instance PreOrder_impl {A} (R : A -> Prop) : PreOrder (fun x y => R x -> R y).
Proof.
  constructor; repeat intro; auto.
Qed.

Global Instance PreOrder_map_PreOrder {A B} f R `{PreOrder B R} :
  @PreOrder A (fun x y => R (f x) (f y)).
Proof.
  constructor; repeat intro; [ reflexivity | etransitivity; eassumption ].
Qed.


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
    repeat apply PreOrder_and; try (apply PreOrder_map_PreOrder; typeclasses eauto).
    constructor; repeat intro; [ reflexivity | ].
    etransitivity; [ apply H | apply H0 ]; assumption.
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
  Program Definition lcurrent l1 l2 :=
    {|
      pre x := True;
      rely x y :=
        statusOf_lte (lifetime (lget x) l1) (lifetime (lget y) l1) /\
          statusOf_lte (lifetime (lget x) l2) (lifetime (lget y) l2) /\
          (statusOf_lte (lifetime (lget x) l1) (lifetime (lget x) l2) ->
           statusOf_lte (lifetime (lget y) l1) (lifetime (lget y) l2));
      guar x y := x = y;
      inv x :=
        statusOf_lte (Some current) (lifetime (lget x) l1) /\
          statusOf_lte (lifetime (lget x) l1) (lifetime (lget x) l2)
    |}.
  Next Obligation.
    split.
    - change (statusOf_lte (Some current) (lifetime (lget y) l1)).
      etransitivity; eassumption.
    - auto.
  Qed.

  (* lcurrent can be duplicated *)
  Lemma lcurrent_dup l1 l2 :
    eq_perm (lcurrent l1 l2) (lcurrent l1 l2 ** lcurrent l1 l2).
  Proof.
    apply dup_self_sep. apply self_sep_trivial_guar; intros; reflexivity.
  Qed.

  (* Transitivity of lcurrent *)
  Lemma lcurrent_trans l1 l2 l3 :
    lcurrent l1 l3 <= lcurrent l1 l2 ** lcurrent l2 l3.
  Proof.
    constructor; intros.
    - apply I.
    - destruct H as [[? ?] [[? ?] ?]].
      destruct H0 as [[? [? ?]] [? [? ?]]].
      split; [ assumption | ]. split; [ assumption | ]. intro.
      etransitivity; eauto.
    - simpl in H0. apply t_step; left; assumption.
    - destruct H as [[? ?] [[? ?] ?]].
      split; [ assumption | ]. etransitivity; eassumption.
  Qed.


  (* Separateness of p from lcurrent l1 l2 is necessary to ensure that any guar
  step of when_perm l2 p does not end l1 *)
  Lemma lcurrent_when l1 l2 p :
    p ⊥ lcurrent l1 l2 ->
    when_perm l2 p <= when_perm l1 p ** lcurrent l1 l2.
  Proof.
    intro p_sep; constructor; intros.
    - destruct H as [[? ?] [[? ?] ?]].
      destruct H0 as [[? | ?] ?]; [ left; assumption | ].
      right. apply finished_lte_eq. rewrite <- H0. assumption.
    - destruct H as [[? ?] [[? ?] ?]]. destruct H0 as [[? ?] [? [? ?]]].
      split; [ assumption | ].
      destruct H5 as [? | [? ?]]; [ left; assumption | ].
      right; split; [ | assumption ].
      apply finished_lte_eq. rewrite <- H5.
      apply H8. assumption.
    - destruct H as [[? ?] [[? ?] ?]].
      destruct H0 as [? | [? [? ?]]]; [ subst; reflexivity | ].
      apply t_step; left; right. split; [ | split ]; try assumption.
      + apply statusOf_lte_eq; try assumption.
        rewrite <- H0. assumption.
      + assert (inv (lcurrent l1 l2) y) as [? ?].
        * eapply inv_rely; [ | split; eassumption ].
          apply (sep_r _ _ p_sep); try assumption. split; assumption.
        * apply statusOf_lte_eq; try assumption.
          rewrite <- H5. assumption.
    - destruct H as [[? ?] [[? ?] ?]].
      split; [ assumption | ]. etransitivity; eassumption.
  Qed.


  (* Lifetime l is finished *)
  Definition lfinished l :=
    invperm (fun x => lifetime (lget x) l = Some finished).

  Lemma lfinished_dup l : eq_perm (lfinished l) (lfinished l ** lfinished l).
  Proof.
    apply dup_self_sep. apply self_sep_trivial_guar; intros; reflexivity.
  Qed.

  (* If l is finished then we can recover a permission from an after_perm,
  assuming that permission is separate from lfinished *)
  Lemma lfinished_after l p :
    p ⊥ lfinished l ->
    eq_perm (lfinished l ** p) (lfinished l ** after_perm l p).
  Proof.
    intro p_sep; constructor; constructor; intros.
    - destruct H as [? [? ?]]. destruct H0.
      split; [ apply I | ]. apply H3. assumption.
    - destruct H as [? [? ?]]. destruct H0 as [? [? [? [? ?]]]].
      split; [ assumption | ]. apply H6; assumption.
    - destruct H as [? [[? ?] ?]].
      unfold lfinished in H0. rewrite sep_conj_invperm_guar_eq in H0.
      apply t_step; right; right.
      split; [ assumption | ]. split; [ | assumption ].
      eapply (inv_rely (lfinished l)); [ | eassumption ].
      apply (sep_r _ _ p_sep); assumption.
    - destruct H as [? [[? ?] ?]].
      split; [ | split ]; try assumption. symmetry; assumption.
    - destruct H as [? [? ?]]. destruct H0. split; [ apply I | ].
      intro; assumption.
    - destruct H as [? [? ?]]. destruct H0.
      split; [ assumption | ]. simpl in H. simpl in H0.
      split; [ | split; [ | split ] ].
      + rewrite H. rewrite (H0 H). reflexivity.
      + intro; eapply inv_rely; eassumption.
      + intros. eapply pre_respects; eauto.
      + intros; assumption.
    - unfold lfinished in H0; rewrite sep_conj_invperm_guar_eq in H0.
      unfold lfinished; rewrite sep_conj_invperm_guar_eq.
      destruct H0 as [? | [? [? ?]]]; [ subst; reflexivity | assumption ].
    - destruct H as [? [? ?]]. split; [ assumption | ].
      split; [ split; [ assumption | ] | ].
      + simpl in H. rewrite H. apply finished_greatest.
      + symmetry; apply separate_invperm; intros.
        destruct H3 as [? | [? [? ?]]]; [ subst | ]; assumption.
  Qed.


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

End LifetimePerms.
