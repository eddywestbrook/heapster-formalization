(* begin hide *)

From Coq Require Import
     Classes.Morphisms
     Relations.Relation_Operators
     Lists.List
     Arith.PeanoNat.

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
        Lifetimes_lte x y /\
          (forall n', n' >= n -> lifetime x n' = lifetime y n');

      guar x y :=
        (exists (ls : Lifetimes), y = lput x ls) /\
          (forall l, l < n -> lifetime x l = lifetime y l) /\
          Lifetimes_lte x y;

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
      repeat rewrite lPutPut in * |- *.
      split; [ eexists; reflexivity | ].
      split; [ intros; etransitivity; [ apply H1 | apply H3 ]; assumption | ].
      intro. etransitivity; [ apply H2 | apply H4 ].
  Qed.
  Next Obligation.
    destruct (proj1 (lt_length_least_None _ _ (length (lget x))) (reflexivity _)).
    apply lt_length_least_None. split.
    - symmetry in H1.
      etransitivity; [ apply H1; unfold ge; reflexivity | assumption ].
    - intros.
      assert (i < length (lget y));
        [ eapply Lt.lt_le_trans; [ | apply Lifetimes_lte_length_lte ]; eassumption | ].
      pose proof (proj2 (nth_error_Some _ _) H4).
      simpl. simpl in H4.
      destruct (nth_error (lget y) i); [ eexists; reflexivity | ].
      elimtype False; apply H5; reflexivity.
  Qed.


  (* Ownership of lifetime l, assuming it is currently active and that all
  lifetimes in ls are children of l *)
  Program Definition lowned_perm l (ls : nat -> Prop) :=
    {|
      (* [l] must be current *)
      pre x := lifetime x l = Some current;

      (* Nobody else can change l or violate the all_lte invariant *)
      rely x y :=
        lifetime x l = lifetime y l /\
          (all_lte l ls x -> all_lte l ls y);

      (* I can end l if all children are finished *)
      guar x y :=
        x = y \/
          y = end_lifetime x l /\
            (forall l', ls l' -> lifetime x l' = Some finished);

      (* l has at least been allocated, and if l is finished then so are all its
      children *)
      inv x :=
        statusOf_lte (Some current) (lifetime x l) /\
          all_lte l ls x;
    |}.
  Next Obligation.
    constructor; repeat intro.
    - left; reflexivity.
    - destruct H; [ subst; assumption | ].
      destruct H0; [ subst; right; assumption | ].
      destruct H. destruct H0.
      right; subst.
      split; [ apply iPutPut_eq | ]. assumption.
  Qed.
  Next Obligation.
    destruct H as [? | [? ?]]; subst; [ split; assumption | ].
    rewrite end_lifetime_eq. split; [ apply I | ].
    apply all_lte_finish. repeat intro.
    apply H2; assumption.
  Qed.


  (* lowned l is separate from lalloc n when n > l *)
  Lemma separate_lowned_lalloc_perm l ls n :
    l < n -> lowned_perm l ls ⊥ lalloc_perm n.
  Proof.
    constructor; intros.
    - destruct H2 as [[lts_y ?] [? ?]]; subst.
      split; [ apply H3; assumption | ].
      repeat intro.
      rewrite <- (H3 l); [ | assumption ].
      etransitivity; [ apply H2; eassumption | apply H4 ].
    - destruct H2 as [? | [? ?]]; subst; [ reflexivity | ]. destruct H0.
      split.
      + apply Lifetimes_lte_update; [ assumption | apply finished_greatest ].
      + intros. symmetry; apply end_lifetime_neq; [ | assumption ].
        intro; subst. apply (Lt.lt_not_le l n); assumption.
  Qed.


  Lemma lowned_lowned_separate_h l1 ls1 l2 ls2 x y :
    l1 <> l2 -> inv (lowned_perm l1 ls1) x ->
    inv (lowned_perm l2 ls2) x ->
    guar (lowned_perm l1 ls1) x y -> rely (lowned_perm l2 ls2) x y.
  Proof.
    intros. destruct H0. destruct H1.
    destruct H2 as [? | [? ?]]; subst; [ reflexivity | ].
    split.
    - rewrite end_lifetime_neq; [ reflexivity
                                | intro; subst; apply H; reflexivity
                                | eassumption ].
    - repeat intro.
      destruct (Nat.eq_dec l' l1).
      + subst. rewrite end_lifetime_eq. apply finished_greatest.
      + destruct (current_lte_Some _ H1).
        assert (statusOf_lte (Some current) (iget l' x));
          [ etransitivity; [ | apply H4 ]; assumption | ].
        destruct (current_lte_Some _ H8).
        erewrite (end_lifetime_neq x l1 l2);
          [ | intro; subst; apply H; reflexivity | assumption ].
        erewrite (end_lifetime_neq x l1 l'); [ apply H4 | | ]; eassumption.
  Qed.

  Lemma lowned_lowned_separate l1 ls1 l2 ls2 :
    l1 <> l2 -> lowned_perm l1 ls1 ⊥ lowned_perm l2 ls2.
  Proof.
    constructor; intros.
    - eapply lowned_lowned_separate_h; try apply Nat.neq_sym; eassumption.
    - eapply lowned_lowned_separate_h; eassumption.
  Qed.


  Lemma lowned_subsume l1 ls1 l2 ls2 :
    l1 <> l2 ->
    sep_step (lowned_perm l1 ls1 ** lowned_perm l2 ls2)
      (lowned_perm l1 (eq l2 \1/ ls1) ** lowned_perm l2 ls2).
  Proof.
    intro neq; apply sep_step_rg; intros.
    - destruct H as [? [? ?]].
      split; [ | split; [ | apply lowned_lowned_separate ]; assumption ].
      destruct H. split; [ assumption | ].
      repeat intro. apply H2. right; assumption.
    - induction H0; [ destruct H0 | ].
      + destruct H0 as [? | [? ?]]; [ subst; reflexivity | ].
        apply t_step; left. right; split; [ assumption | ].
        intros; apply H1. right; assumption.
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
      pre x := pre p x \/ lifetime x l = Some finished;

      rely x y :=
        statusOf_lte (lifetime x l) (lifetime y l) /\
        (* if the lifetime isn't ending or already ended, the rely of p must hold *)
        (rely p x y \/ lifetime y l = Some finished /\ inv p y);

      guar x y :=
        x = y \/
          lifetime x l = Some current /\
          lifetime y l = Some current /\
          guar p x y;

      inv x := inv p x /\ statusOf_lte (Some current) (lifetime x l)
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
    - change (statusOf_lte (Some current) (lifetime y l)).
      etransitivity; [ apply H1 | apply H ].
  Qed.
  Next Obligation.
    destruct H; [ subst; split; try assumption; apply H0 | ].
    destruct H as [? [? ?]].
    split.
    - eapply inv_guar; eassumption.
    - change (statusOf_lte (Some current) (lifetime y l)).
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

  (* when_perm is monotone wrt the permission argument *)
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

  (* Proper instance for the monotonicity of when *)
  Global Instance Proper_when n : Proper (lte_perm ==> lte_perm) (when_perm n).
  Proof.
    repeat intro; apply when_monotone; assumption.
  Qed.


  Program Definition after_perm l p : perm :=
    {|
      (** after_perm has no precondition; this is so an lowned_perm can end a
      lifetime in any state without having to re-establish the precondition of
      after_perm *)
      pre x := True;

      rely x y :=
        statusOf_lte (lifetime x l) (lifetime y l) /\
          (inv p x -> inv p y) /\
          (lifetime x l = Some finished -> rely p x y);

      (** If [l] is finished afterwards, the guar of [p] holds *)
      guar x y :=
        x = y \/
          lifetime x l = Some finished /\
            lifetime y l = Some finished /\
            guar p x y;

      inv x := inv p x /\ statusOf_lte (Some current) (lifetime x l)
    |}.
  Next Obligation.
    constructor; intros.
    - split; [ reflexivity | ]. split; [ intro; assumption | ].
      intro; reflexivity.
    - intros x y z [? [? ?]] [? [? ?]].
      split; [ etransitivity; eassumption | ].
      split; [ auto | ].
      intro; etransitivity; auto.
      apply H4. apply finished_lte_eq. rewrite <- H5. assumption.
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
    change (statusOf_lte (Some current) (lifetime y l)).
    etransitivity; eassumption.
  Qed.
  Next Obligation.
    destruct H; [ subst; split; assumption | ]. destruct H as [? [? ?]].
    split; [ eapply inv_guar; eassumption | ].
    change (statusOf_lte (Some current) (lifetime y l)).
    rewrite H2; simpl; trivial.
  Qed.


  (* after_perm is monotone wrt the permission argument *)
  Lemma after_monotone n p1 p2 : p1 <= p2 -> after_perm n p1 <= after_perm n p2.
  Proof.
    constructor; intros.
    - apply I.
    - destruct H0. destruct H1 as [? [? ?]].
      split; [ assumption | ].
      split; [ intro; apply H; auto | ].
      intro; apply H; auto.
    - destruct H0. destruct H1 as [? | [? [? ?]]]; [ subst; reflexivity | ].
      right; split; [ | split ]; try assumption.
      apply H; assumption.
    - destruct H0. split; [ apply H | ]; assumption.
  Qed.

  Global Instance Proper_after n : Proper (lte_perm ==> lte_perm) (after_perm n).
  Proof.
    repeat intro; apply after_monotone; assumption.
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
      intros. rewrite H4 in H1. discriminate.
  Qed.

  Lemma separate_when_lowned l ls p :
    p ⊥ lowned_perm l ls -> when_perm l p ⊥ lowned_perm l ls.
  Proof.
    constructor; intros.
    - destruct H2 as [ ? | [? ?]]; [ subst; reflexivity | ]. subst. simpl.
      rewrite end_lifetime_eq.
      split; [ apply finished_greatest | ].
      destruct H1. left; apply (sep_l _ _ H); try assumption.
      right; split; [ reflexivity | assumption ].
    - destruct H2 as [ ? | [? [? ?]]]; [ subst; reflexivity | ]. destruct H0.
      assert (rely (lowned_perm l ls) x y) as [? ?];
        [ apply (sep_r _ _ H); assumption | ].
      split; assumption.
  Qed.

  Lemma separate_after_lowned l ls p :
    p ⊥ lowned_perm l ls -> after_perm l p ⊥ lowned_perm l ls.
  Proof.
    constructor; intros.
    - destruct H1. destruct H2 as [ ? | [? ?]]; [ subst; reflexivity | ].
      assert (rely p x y).
      + apply (sep_l _ _ H); try assumption.
        right; split; assumption.
      + subst. simpl. rewrite end_lifetime_eq.
        split; [ apply finished_greatest | ].
        split; [ intro; eapply inv_rely; eassumption | ].
        intros; assumption.
    - destruct H2 as [ ? | [? [? ?]]]; [ subst; reflexivity | ]. destruct H0.
      assert (rely (lowned_perm l ls) x y) as [? ?];
        [ apply (sep_r _ _ H); assumption | ].
      split; assumption.
  Qed.

  Lemma separate_when_after_lowned l ls p :
    p ⊥ lowned_perm l ls ->
    when_perm l p ** after_perm l p ⊥ lowned_perm l ls.
  Proof.
    symmetry; apply sep_conj_perm_separate; symmetry;
      [ apply separate_when_lowned | apply separate_after_lowned ]; assumption.
  Qed.

  Lemma perm_split_lt p l ls :
    (when_perm l p ** after_perm l p) ** (lowned_perm l ls)
    <= p ** lowned_perm l ls.
  Proof.
    constructor; intros.
    - destruct H0.
      split; [ split | ]; [ left | apply I | ]; assumption.
    - destruct H0 as [? [? ?]].
      split; [ split | ]; split; try assumption.
      + rewrite H1. reflexivity.
      + left; assumption.
      + rewrite H1; reflexivity.
      + split; [ intro; eapply inv_rely; eassumption | ].
        intro; assumption.
    - simpl in H0. rewrite clos_trans_clos_trans_or in H0. clear H.
      induction H0; [ destruct H; [ destruct H | ] | ].
      + destruct H as [? | [? [? ?]]]; [ subst; reflexivity | ].
        apply t_step; left; assumption.
      + destruct H as [? | [? [? ?]]]; [ subst; reflexivity | ].
        apply t_step; left; assumption.
      + destruct H as [? | [? ?]]; [ subst; reflexivity | ].
        apply t_step; right; right. split; assumption.
      + etransitivity; eassumption.
    - destruct H as [? [[? ?] ?]].
      split; split.
      + split; assumption.
      + split; [ split; assumption | ]. apply separate_when_after.
      + split; assumption.
      + apply separate_when_after_lowned; assumption.
  Qed.


  (* FIXME: no longer needed?
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
  *)


  (* l1 is current whenever l2 is current, i.e., Some current <= l1 <= l2. This
  means that l1 is an ancestor of l2, i.e., a larger lifetime containing l2. *)
  Program Definition lcurrent_perm l1 l2 :=
    {|
      pre x := True;
      rely x y :=
        statusOf_lte (lifetime x l1) (lifetime y l1) /\
          statusOf_lte (lifetime x l2) (lifetime y l2) /\
          (statusOf_lte (lifetime x l1) (lifetime x l2) ->
           statusOf_lte (lifetime y l1) (lifetime y l2));
      guar x y := x = y;
      inv x :=
        statusOf_lte (Some current) (lifetime x l1) /\
          statusOf_lte (lifetime x l1) (lifetime x l2)
    |}.
  Next Obligation.
    split.
    - change (statusOf_lte (Some current) (lifetime y l1)).
      etransitivity; eassumption.
    - auto.
  Qed.

  (* lcurrent can be duplicated *)
  Lemma lcurrent_dup l1 l2 :
    eq_perm (lcurrent_perm l1 l2) (lcurrent_perm l1 l2 ** lcurrent_perm l1 l2).
  Proof.
    apply dup_self_sep. apply self_sep_trivial_guar; intros; reflexivity.
  Qed.

  (* Transitivity of lcurrent *)
  Lemma lcurrent_trans l1 l2 l3 :
    lcurrent_perm l1 l3 <= lcurrent_perm l1 l2 ** lcurrent_perm l2 l3.
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
    p ⊥ lcurrent_perm l1 l2 ->
    when_perm l2 p <= when_perm l1 p ** lcurrent_perm l1 l2.
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
      + assert (inv (lcurrent_perm l1 l2) y) as [? ?].
        * eapply inv_rely; [ | split; eassumption ].
          apply (sep_r _ _ p_sep); try assumption. split; assumption.
        * apply statusOf_lte_eq; try assumption.
          rewrite <- H5. assumption.
    - destruct H as [[? ?] [[? ?] ?]].
      split; [ assumption | ]. etransitivity; eassumption.
  Qed.


  (* Lifetime l is finished *)
  Definition lfinished_perm l :=
    invperm (fun x => lifetime x l = Some finished).

  (* lfinished can be duplicated *)
  Lemma lfinished_perm_dup l :
    eq_perm (lfinished_perm l) (lfinished_perm l ** lfinished_perm l).
  Proof. apply invperm_dup. Qed.

  (* Anything separate from lowned is separate from lfinished *)
  Lemma sep_lowned_sep_lfinished l p :
    p ⊥ lowned_perm l (fun _ => False) -> p ⊥ lfinished_perm l.
  Proof.
    constructor; intros.
    - inversion H2. reflexivity.
    - assert (rely (lowned_perm l (fun _ => False)) x y) as [? ?].
      + apply (sep_r _ _ H); try assumption.
        split; [ | repeat intro; elimtype False; assumption ].
        simpl in H1. rewrite H1. apply finished_greatest.
      + intro. rewrite <- H3. assumption.
  Qed.

  (* rewind_perm l p says when l was current we had permission p, so its
  invariant and precondition held *)
  Program Definition rewind_perm l p : perm :=
    {|
      pre x := pre p (replace_lifetime x l current);
      rely x y :=
        (inv p (replace_lifetime x l current) -> inv p (replace_lifetime y l current)) /\
          (pre p (replace_lifetime x l current) -> pre p (replace_lifetime y l current));
      guar x y := x = y;
      inv x := inv p (replace_lifetime x l current);
    |}.

  (* Rewinding a when_perm is the same as rewinding the perm it contains *)
  Lemma rewind_when_perm l p :
    eq_perm (rewind_perm l (when_perm l p)) (rewind_perm l p).
  Proof.
    constructor; constructor; intros.
    - left; apply H0.
    - destruct H0. split; intros.
      + destruct H2. split; [ apply H0; apply H | ].
        rewrite replace_lifetime_eq. reflexivity.
      + left. apply H1. destruct H2; [ assumption | ].
        rewrite replace_lifetime_eq in H2. discriminate.
    - inversion H0. reflexivity.
    - split; [ apply H | ]. rewrite replace_lifetime_eq. reflexivity.
    - destruct H0; [ assumption | ].
      rewrite replace_lifetime_eq in H0. discriminate.
    - destruct H. destruct H0. split; intros.
      + refine (proj1 (H0 _)). split; [ assumption | ].
        rewrite replace_lifetime_eq; reflexivity.
      + assert (pre (when_perm l p) (replace_lifetime x l current));
          [ left; assumption | ].
        destruct (H2 H4); [ assumption | ].
        rewrite replace_lifetime_eq in H5. discriminate.
    - inversion H0. reflexivity.
    - destruct H. assumption.
  Qed.


  (* If p is separate from lowned then pre p implies pre_set_cur l p *)
  Lemma lowned_sep_pre_set_cur l p st :
    p ⊥ lowned_perm l (fun _ => False) ->
    lifetime st l = Some finished ->
    inv (rewind_perm l p) st -> pre (rewind_perm l p) st -> pre p st.
  Proof.
    intros. simpl in H1, H2. eapply pre_respects; [ | eassumption ].
    apply (sep_l _ _ H); try assumption.
    - simpl. rewrite replace_lifetime_eq.
      split; [ apply I | ]. repeat intro; elimtype False; assumption.
    - right. split; [ | intros; elimtype False; assumption ].
      unfold end_lifetime.
      erewrite replace_lifetime_twice; [ | rewrite H0; intro; discriminate ].
      rewrite eq_replace_lifetime; [ | assumption ]. reflexivity.
  Qed.

  (* If l is finished then we can recover a permission from an after_perm and a
  rewind_perm, assuming that permission is separate from lowned *)
  Lemma lfinished_after_perm l p :
    p ⊥ lowned_perm l (fun _ => False) ->
    lfinished_perm l ** p <=
      lfinished_perm l ** (rewind_perm l p ** after_perm l p).
  Proof.
    intro p_sep; constructor; intros.
    - destruct H as [? [[? [? ?]] ?]]. destruct H0 as [? [? ?]].
      split; [ apply I | ]. eapply lowned_sep_pre_set_cur; eassumption.
    - destruct H as [? [[? [? ?]] ?]]. destruct H0 as [? [? [? [? ?]]]].
      split; [ assumption | ]. apply H8; assumption.
    - destruct H as [? [[? [[? ?] ?]] ?]].
      unfold lfinished_perm in H0. rewrite sep_conj_invperm_guar_eq in H0.
      apply t_step; right. apply t_step; right; right.
      split; [ assumption | ]. split; [ | assumption ].
      assert (rely (lowned_perm l (fun _ => False)) x y) as [? ?].
      + apply (sep_r _ _ p_sep); try assumption.
        split; [ assumption | ]. repeat intro; elimtype False; assumption.
      + simpl in H. rewrite <- H6; assumption.
    - destruct H as [? [[? [[? ?] ?]] ?]].
      split; [ | split ]; try assumption.
      symmetry; apply sep_lowned_sep_lfinished. assumption.
  Qed.

(* End LifetimePerms. *)


(***
 *** Lifetime typing rules
 ***)

(*
Section LifetimeRules.
  (*
  Context {Si Ss : Type}.
  Context `{Hlens: Lens Si Lifetimes}.
   *)
  Context {S : Type}.
  Context `{Hlens: Lens S Lifetimes}.
*)

  (* The set of permissions when_perm l p for all p in P *)
  Definition when l P : Perms := mapPerms (when_perm l) P.

  (* The set of permissions after_perm l p for all p in P *)
  Definition after l P : Perms := mapPerms (after_perm l) P.

  (* The set of permissions rewind_perm l p for all p in P *)
  Definition rewind l P := mapPerms (rewind_perm l) P.

  (* The permission set allowing allocation of lifetimes *)
  Definition lalloc : Perms :=
    mkPerms (fun r => exists n, r = lalloc_perm n).

  (* The permission set stating that l is finished *)
  Definition lfinished l : Perms :=
    singleton_Perms (lfinished_perm l).

  (* The lfinished permission set can be duplicated *)
  (* FIXME: generalize this to all singleton_Perms sets of invperms *)
  Lemma lfinished_dup l : eq_Perms (lfinished l) (lfinished l * lfinished l).
  Proof.
    split; [ apply lte_l_sep_conj_Perms | ].
    repeat intro. simpl in H. simpl.
    exists (lfinished_perm l); exists (lfinished_perm l).
    split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ etransitivity; [ apply lfinished_perm_dup | eassumption ] | ].
    apply self_sep_trivial_guar; intros; reflexivity.
  Qed.

  (* The singleton Perms set containing lowned_perm l ls *)
  Definition lowned_Perms l ls : Perms := singleton_Perms (lowned_perm l ls).

  (* lowned is the conjunction of an lowned perm plus any permission p such that
  if the precondition of P held before l was ended then p implies Q after l
  finishes *)
  Definition lowned l ls P Q :=
    lowned_Perms l ls * impl_Perms (lfinished l * rewind l P) Q.

  Lemma sep_lowned_any_ls l ls p :
    p ⊥ lowned_perm l (fun _ => False) -> p ⊥ lowned_perm l ls.
  Admitted.


  Lemma Perms_split_lt p l ls :
    p ⊥ lowned_perm l (fun _ => False) ->
    singleton_Perms p * lowned_Perms l ls
      ⊨ (when l (singleton_Perms p) * after l (singleton_Perms p)) * lowned_Perms l ls.
  Proof.
    intros. unfold lowned_Perms, when, after.
    rewrite sep_conj_singleton; [ | apply sep_lowned_any_ls; assumption ].
    rewrite map_singleton_Perms; [ | typeclasses eauto ].
    rewrite map_singleton_Perms; [ | typeclasses eauto ].
    rewrite sep_conj_singleton; [ | apply separate_when_after ].
    rewrite sep_conj_singleton; [ | apply separate_when_after_lowned;
                                    apply sep_lowned_any_ls; assumption ].
    apply lte_singleton_Perms.
    apply perm_split_lt.
  Qed.

  Lemma rewind_conj l P Q :
    eq_Perms (rewind l (P * Q)) (rewind l P * rewind l Q).
  Admitted.

  Lemma lfinished_distrib l P Q :
    eq_Perms (lfinished l * (P * Q)) ((lfinished l * P) * (lfinished l * Q)).
  Admitted.

  Lemma impl_Perms_apply (P Q : @Perms S) : P * impl_Perms P Q ⊨ Q.
  Admitted.

  Lemma lfinished_after l p :
    p ⊥ lowned_perm l (fun _ => False) ->
    lfinished l * (rewind l (when l (singleton_Perms p)) * after l (singleton_Perms p))
    ⊨ singleton_Perms p.
  Admitted.


  (* The rule for splitting the lifetime of a singleton permission *)
  Lemma lowned_split_lt l ls p Q R :
    p ⊥ lowned_perm l (fun _ => False) ->
    singleton_Perms p * lowned l ls Q R
      ⊨ when l (singleton_Perms p)
        * lowned l ls (when l (singleton_Perms p) * Q) (singleton_Perms p * R).
  Proof.
    intros. unfold lowned.
    rewrite sep_conj_Perms_assoc.
    etransitivity;
      [ apply sep_conj_Perms_monotone;
        [ apply Perms_split_lt; assumption | reflexivity ] | ].
    rewrite <- sep_conj_Perms_assoc.
    rewrite <- sep_conj_Perms_assoc.
    apply sep_conj_Perms_monotone; [ reflexivity | ].
    rewrite (sep_conj_Perms_assoc (after l (singleton_Perms p))).
    rewrite (sep_conj_Perms_commut (after l (singleton_Perms p))).
    rewrite <- (sep_conj_Perms_assoc _ (after l (singleton_Perms p))).
    apply sep_conj_Perms_monotone; [ reflexivity | ].
    refine (proj1 (adjunction _ _ _) _).
    rewrite rewind_conj.
    rewrite (sep_conj_Perms_commut (rewind l _) (rewind l Q)).
    rewrite lfinished_distrib.
    rewrite <- (sep_conj_Perms_assoc (after l (singleton_Perms p))).
    rewrite (sep_conj_Perms_assoc (impl_Perms _ _)).
    rewrite (sep_conj_Perms_commut _ (lfinished l * rewind l (when l _))).
    rewrite (sep_conj_Perms_assoc (after l _)).
    rewrite (sep_conj_Perms_commut (impl_Perms _ _)).
    apply sep_conj_Perms_monotone; [ | apply impl_Perms_apply ].
    rewrite (sep_conj_Perms_commut (after _ _)).
    rewrite <- (sep_conj_Perms_assoc).
    apply lfinished_after; assumption.
  Qed.


(* End LifetimeRules. *)
End LifetimePerms.
