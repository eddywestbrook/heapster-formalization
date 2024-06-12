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
     Typing
     LensPerms.

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

  (* Help Coq infer the IxPartialLens for lifetimes in this section *)
  Local Instance IxPartialLens_Lifetimes : IxPartialLens nat S status.
  Proof. unfold Lifetimes in Hlens. typeclasses eauto. Defined.

  (* Permission to allocate lifetimes with index >= n *)
  Definition lalloc_perm (n : nat) : @perm S :=
    ixplens_multi_write_perm (fun i => gt i n).

  (* Permission to mutate the state of a lifetime *)
  Definition lmutate_perm (l : nat) : perm := ixplens_write_perm_any l.

  (* Permission p was held before l was ended, and now we hold q *)
  Definition rewind_lt_perm l p q :=
    rewind_perm (fun x => end_lifetime x l) p q.

  (* Permission p was held before l was created, and now we hold q *)
  Definition rewind_lt_alloc_perm l p q :=
    rewind_perm (fun x => replace_lifetime x l current) p q.


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

  (* lmutate_perm l sep_steps to lowned_perm l with no child lifetimes *)
  Lemma lmutate_sep_step_lowned l :
    sep_step (lmutate_perm l) (lowned_perm l (fun _ => False)).
  Proof.
    apply sep_step_rg; intros.
    - apply I.
    - destruct H. destruct H0 as [? | [? ?]]; subst; [ reflexivity | ].
      right; split.
      + intro. unfold lifetime, Lifetimes in H. unfold IxPartialLens_Lifetimes in H0.
        rewrite H0 in H. apply H.
      + exists finished. reflexivity.
    - split; [ | intro; apply all_lte_empty ].
      destruct H. apply H0. intro.
      unfold lifetime, Lifetimes in H. unfold IxPartialLens_Lifetimes in H2.
      rewrite H2 in H. apply H.
  Qed.


  (* Setting a lifetime to current using an lmutate_perm l can get you an
  lowned_perm l with no child lifetimes *)
  Lemma lmutate_entails_lowned l :
    rewind_lt_alloc_perm l (lmutate_perm l) (lmutate_perm l)
      ⊢ lowned_perm l (fun _ => False).
  Proof.
    apply sep_step_entails_perm;
      [ etransitivity; [ apply set_pre_sep_step | apply lmutate_sep_step_lowned ] | ].
    intros. destruct H as [_ [y [_ [[z [? [_ [elem [? _]]]]] ?]]]]; subst.
    assert (lifetime x l = Some current) as H;
      [ | simpl; rewrite H; split; [ split | ]; try trivial;
          apply all_lte_empty ].
    symmetry. etransitivity; [ symmetry; apply iGetPut_eq | apply H1 ].
    unfold replace_lifetime. rewrite iGetPut_eq.
    eapply Some_not_None. reflexivity.
  Qed.


  (* lowned l is separate from lalloc n when n > l *)
  (* FIXME: get this working again after having changed lalloc_perm
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
   *)

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

  (* Helper lemma for the lifetime subsumption rule *)
  Lemma lowned_perm_subsume_step l1 ls1 l2 ls2 :
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

  (* If we own two unequal lifetimes then we can subsume one inside the other *)
  Lemma lowned_perm_subsume l1 ls1 l2 ls2 :
    l1 <> l2 ->
    lowned_perm l1 ls1 ** lowned_perm l2 ls2 ⊢
      lowned_perm l1 (eq l2 \1/ ls1) ** lowned_perm l2 ls2.
  Proof.
    intro; apply sep_step_entails_perm;
      [ apply lowned_perm_subsume_step; assumption | ].
    intros. destruct H0 as [[[? ?] [[? ?] ?]] [? ?]]. simpl in H5. simpl in H6.
    split; [ split; [ split | split; [ split | ] ] | split ].
    - rewrite H5; reflexivity.
    - repeat intro. destruct H7.
      + subst. rewrite H5. rewrite H6. reflexivity.
      + apply H1; assumption.
    - rewrite H6; reflexivity.
    - repeat intro. apply H3. assumption.
    - apply lowned_lowned_separate; assumption.
    - assumption.
    - assumption.
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
        split; [ | apply all_lte_empty ].
        simpl in H1. rewrite H1. apply finished_greatest.
      + intro. rewrite <- H3. assumption.
  Qed.

  (* Ending a lifetime gives you an lfinished *)
  Lemma rewind_lowned_entails_lfinished l :
    rewind_lt_perm l (lowned_perm l (fun _ => False)) (lowned_perm l (fun _ => False))
      ⊢ lfinished_perm l.
  Proof.
    apply sep_step_entails_perm.
    - etransitivity; [ apply set_pre_sep_step | ].
      apply sep_step_rg; intros.
      + simpl in H. simpl. rewrite H.
        split; [ trivial | apply all_lte_empty ].
      + inversion H0; reflexivity.
      + destruct H0. simpl. rewrite H0. intro; assumption.
    - intros. split; [ | apply I ].
      simpl. destruct H as [[? ?] [y [[? ?] [[z [? [[? ?] ?]]] [? ?]]]]]; subst.
      rewrite <- H7. rewrite end_lifetime_eq. reflexivity.
  Qed.


  (* An after_perm for p can be turned back into p if its lifetime is finished
  and we held a when_perm for p before the lifetime was ended *)
  Lemma lfinished_after_recover_perm l p :
    p ⊥ lowned_perm l (fun _ => False) ->
    lfinished_perm l **
    rewind_lt_perm l (lowned_perm l (fun _ => False) ** when_perm l p) (after_perm l p)
    ⊢ lfinished_perm l ** p.
  Proof.
    intro; apply sep_step_entails_perm; [ apply sep_step_rg | ]; intros.
    - destruct H0 as [? [? ?]].
      split; [ assumption | ]. simpl. simpl in H0. rewrite H0.
      split; [ split; [ assumption | trivial ] | ].
      symmetry; apply separate_rewind.
      apply separate_invperm; intros.
      destruct H4 as [? | [? [? ?]]]; [ subst | ]; assumption.
    - destruct H0 as [? [? ?]]. unfold lfinished_perm in H1.
      rewrite sep_conj_invperm_guar_eq in H1.
      apply t_step. right. right. split; [ assumption | ].
      split; [ | assumption ]. change (inv (lfinished_perm l) y).
      eapply inv_rely; [ | eassumption ].
      eapply sep_l; eassumption.
    - destruct H0 as [? [? ?]]. destruct H1 as [? [? [? ?]]]. simpl in H1.
      split; [ assumption | ]. apply H6. assumption.
    - destruct H0 as [[? [[? ?] ?]] [? ?]].
      split; [ split; [ | split ] | split ]; try assumption.
      + symmetry; apply sep_lowned_sep_lfinished; assumption.
      + destruct H5 as [y [[? ?] [[z [? [[? ?] ?]]] [? [? ?]]]]]; subst.
        simpl in H10.
        destruct H10 as [? [? | ?]];
          [ | rewrite H7 in H10; discriminate ].
        apply (pre_respects p z); [ | assumption ].
        rewrite end_lifetime_eq in H13.
        etransitivity; [ | apply H13; reflexivity ].
        destruct H9 as [[? ?] ?].
        apply (sep_l _ _ H); try assumption.
        right. split; [ reflexivity | ]. intros; elimtype False; assumption.
  Qed.

  (* If we held both a when p and an after p before l was ended then we can
     recover p *)
  Lemma lfinished_when_after_recover_perm l p :
    p ⊥ lowned_perm l (fun _ => False) ->
    lfinished_perm l **
    rewind_lt_perm l (lowned_perm l (fun _ => False)
                        ** (when_perm l p ** after_perm l p))
                     (when_perm l p ** after_perm l p)
    ⊢ lfinished_perm l ** p.
  Proof.
    intro. etransitivity; [ | apply lfinished_after_recover_perm; assumption ].
    apply monotone_entails_sep_conj_perm; [ | reflexivity | ].
    - symmetry; apply sep_lowned_sep_lfinished. apply separate_rewind.
      symmetry; apply separate_sep_conj_perm; symmetry;
        [ apply separate_when_lowned | apply separate_after_lowned ]; assumption.
    - apply bigger_perm_entails; [ apply Proper_lte_rewind_perm | ].
      + apply sep_conj_perm_monotone_sep;
          [ | reflexivity | apply lte_l_sep_conj_perm ].
        symmetry; apply separate_when_lowned; assumption.
      + apply lte_r_sep_conj_perm.
      + simpl; intros x [? ?].
        destruct (lifetime x l); [ | inversion H1 ].
        repeat (split; [ split; [ assumption | trivial ] | ]).
        apply separate_when_after.
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

  (* Helper for lowned_subsume, below *)
  Lemma lowned_Perms_subsume l1 ls1 l2 ls2 :
    l1 <> l2 ->
    lowned_Perms l1 ls1 * lowned_Perms l2 ls2 ⊨
      lowned_Perms l1 (eq l2 \1/ ls1) * lowned_Perms l2 ls2.
  Proof.
    intro H. unfold lowned_Perms.
    repeat rewrite sep_conj_singleton; try (apply lowned_lowned_separate; assumption).
    apply entails_singleton_Perms.
    apply lowned_perm_subsume. assumption.
  Qed.


  (* A permission P that we also held before we ended lifetime l *)
  Definition rewind_lt l P :=
    rewind_conj (fun x => end_lifetime x l) (lowned_Perms l (fun _ => False)) P.

  (* rewind_lt is Proper wrt permission set equality *)
  Global Instance Proper_eq_rewind_lt l :
    Proper (eq_Perms ==> eq_Perms) (rewind_lt l).
  Proof.
    apply Proper_eq_rewind_conj; reflexivity.
  Qed.

  (* rewind_lt is Proper wrt entailment *)
  Global Instance Proper_ent_rewind_lt :
    Proper (eq ==> entails_Perms ==> entails_Perms) rewind_lt.
  Proof.
    intros l1 l2 eql P1 P2 entP. subst.
    apply mono_ent_rewind_conj; [ | assumption ].
    intros. simpl in H. eapply guar_inc; try eassumption.
    right. split; [ reflexivity | intros; elimtype False; assumption ].
  Qed.

  (* rewind_lt is Proper wrt entailment *)
  Global Instance Proper_ent_rewind_lt_flip :
    Proper (eq ==> entails_Perms --> Basics.flip entails_Perms) rewind_lt.
  Proof.
    intros l1 l2 eql P1 P2 entP; apply Proper_ent_rewind_lt; try symmetry; eassumption.
  Qed.

  (* The rewind_lt function can be dropped *)
  Lemma rewind_lt_gte_P l P : rewind_lt l P ⊨ P.
  Proof.
    apply bigger_Perms_entails. apply rewind_conj_gte_Q.
    intros. simpl in H. apply H; [ assumption | ].
    right. split; [ reflexivity | intros; elimtype False; assumption ].
  Qed.

  (* The rewind_lt of a conjunction entails the conjunction of rewind_lts *)
  Lemma rewind_lt_of_conj l P Q :
    rewind_lt l (P * Q) ⊨ rewind_lt l P * rewind_lt l Q.
  Proof.
    apply bigger_Perms_entails. apply rewind_conj_of_conj.
  Qed.

  (* The set of all permissions such that, if you held them and some permissions
     P a before ending lifetime l, you could recover Q a afterwards *)
  Definition rewind_lt_impl l A (P Q : A -> Perms) :=
    meet_Perms (fun R => forall a, lfinished l * rewind_lt l (P a * R) ⊨ Q a).

  (* rewind_lt_impl is Proper wrt permission set equality *)
  Global Instance Proper_eq_rewind_lt_impl l A :
    Proper (pointwise_relation _ eq_Perms ==>
              pointwise_relation _ eq_Perms ==> eq_Perms) (rewind_lt_impl l A).
  Proof.
    intros P1 P2 eqP Q1 Q2 eqQ; split; apply meet_Perms_max; intros;
      apply lte_meet_Perms; eexists; (split; [ | reflexivity ]); intros.
    - rewrite eqP. rewrite eqQ. apply H.
    - rewrite <- eqP. rewrite <- eqQ. apply H.
  Qed.

  (* P entails a rewind_lt_impl if it satisfies the rewind_lt_impl condition *)
  Lemma rewind_lt_impl_lambda l A P Q R :
    (forall a, lfinished l * rewind_lt l (Q a * P) ⊨ R a) ->
    P ⊨ rewind_lt_impl l A Q R.
  Proof.
    repeat intro.
    exists p. split; [ | reflexivity ]. exists P. split; assumption.
  Qed.

  (* A rewind_lt_impl can be "partially applied" *)
  Lemma rewind_lt_impl_part_apply l A (a:A) B P Q (R : A*B -> Perms) :
    P a * rewind_lt_impl l (A*B) (P *1 Q) R ⊨ rewind_lt_impl l B Q (fun b => R (a,b)).
  Proof.
    rewrite sep_conj_Perms_commut.
    unfold rewind_lt_impl.
    rewrite sep_conj_Perms_meet_commute.
    apply meet_Perms_max_ent; intros P0 [P' [? ?]]; subst.
    apply ent_meet_Perms.
    eexists; split; [ intros | reflexivity ].
    rewrite (sep_conj_Perms_commut P').
    rewrite (sep_conj_Perms_assoc (Q a0)).
    rewrite (sep_conj_Perms_commut (Q a0)).
    apply (H0 (a,a0)).
  Qed.


  (* lowned is the conjunction of an lowned permission plus a permission R such
  that ending the lifetime while holding P plus R yields Q *)
  Definition lowned l ls {A} P Q := lowned_Perms l ls * rewind_lt_impl l A P Q.

  (* If we own two unequal lifetimes then we can subsume one inside the other *)
  Lemma lowned_subsume l1 ls1 A P1 Q1 l2 ls2 B P2 Q2 :
    l1 <> l2 ->
    @lowned l1 ls1 A P1 Q1 * @lowned l2 ls2 B P2 Q2 ⊨
      lowned l1 (eq l2 \1/ ls1) P1 Q1 * lowned l2 ls2 P2 Q2.
  Proof.
    intro. unfold lowned.
    rewrite (sep_conj_Perms_distrib (lowned_Perms l1 ls1)).
    rewrite (sep_conj_Perms_distrib (lowned_Perms l1 (eq l2 \1/ ls1))).
    apply monotone_entails_sep_conj; [ | reflexivity ].
    apply lowned_Perms_subsume; assumption.
  Qed.

  (* A singleton permission set that is separate from lowned can be split into
  when and after *)
  Lemma Perms_split_lt p l ls :
    p ⊥ lowned_perm l ls ->
    singleton_Perms p * lowned_Perms l ls
      ⊨ (when l (singleton_Perms p) * after l (singleton_Perms p)) * lowned_Perms l ls.
  Proof.
    intros. unfold lowned_Perms, when, after.
    rewrite sep_conj_singleton; [ | assumption ].
    rewrite map_singleton_Perms; [ | typeclasses eauto ].
    rewrite map_singleton_Perms; [ | typeclasses eauto ].
    rewrite sep_conj_singleton; [ | apply separate_when_after ].
    rewrite sep_conj_singleton; [ | apply separate_when_after_lowned; assumption ].
    apply bigger_Perms_entails.
    apply lte_singleton_Perms.
    apply perm_split_lt.
  Qed.

  (* lfinished is always separate from when *)
  Lemma lfinished_when_sep l p : lfinished_perm l ⊥ when_perm l p.
  Proof.
    symmetry; apply separate_invperm; intros.
    destruct H0 as [? | [? [? ?]]]; [ subst; assumption | ].
    rewrite H0 in H. inversion H.
  Qed.

  (* lfinished is always separate from after *)
  Lemma lfinished_after_sep l p : lfinished_perm l ⊥ after_perm l p.
  Proof.
    symmetry; apply separate_invperm; intros.
    destruct H0 as [? | [? [? ?]]]; subst; assumption.
  Qed.


  (* An after_perm for p can be turned back into p if its lifetime is finished
  and we held a when_perm for p before the lifetime was ended *)
  Lemma lfinished_after_recover_singleton l p :
    p ⊥ lowned_perm l (fun _ => False) ->
    lfinished l * (rewind_lt l (when l (singleton_Perms p)
                                * after l (singleton_Perms p)))
    ⊨ singleton_Perms p.
  Proof.
    intros; unfold lfinished, rewind_lt, when, after, lowned_Perms.
    rewrite (map_singleton_Perms (after_perm l)); [ | typeclasses eauto ].
    rewrite (map_singleton_Perms (when_perm l)); [ | typeclasses eauto ].
    rewrite sep_conj_singleton; [ | apply separate_when_after; assumption ].
    rewrite rewind_conj_singleton.
    2: { apply sep_conj_perm_separate; symmetry;
         [ apply separate_when_lowned | apply separate_after_lowned ]; assumption. }
    rewrite sep_conj_singleton.
    2: { symmetry; apply separate_rewind; symmetry; apply sep_conj_perm_separate;
         [ apply lfinished_when_sep | apply lfinished_after_sep ]. }
    transitivity (lfinished l * singleton_Perms p);
      [ | apply entails_r_sep_conj ].
    unfold lfinished.
    rewrite sep_conj_singleton;
      [ | symmetry; apply sep_lowned_sep_lfinished; assumption ].
    apply entails_singleton_Perms.
    apply lfinished_when_after_recover_perm; assumption.
  Qed.


  (* The rule for splitting the lifetime of a singleton permission *)
  Lemma lowned_split l ls p A Q R :
    p ⊥ lowned_perm l ls -> p ⊥ lowned_perm l (fun _ => False) ->
    singleton_Perms p * lowned l ls Q R
      ⊨ when l (singleton_Perms p)
        * lowned l ls (fun a:A => when l (singleton_Perms p) * Q a) (fun a => singleton_Perms p * R a).
  Proof.
    intros. unfold lowned.
    rewrite sep_conj_Perms_assoc.
    etransitivity;
      [ apply monotone_entails_sep_conj;
        [ apply Perms_split_lt; assumption | reflexivity ] | ].
    rewrite <- sep_conj_Perms_assoc.
    rewrite <- sep_conj_Perms_assoc.
    apply monotone_entails_sep_conj; [ reflexivity | ].
    rewrite (sep_conj_Perms_assoc (after l (singleton_Perms p))).
    rewrite (sep_conj_Perms_commut (after l (singleton_Perms p))).
    rewrite <- (sep_conj_Perms_assoc _ (after l (singleton_Perms p))).
    apply monotone_entails_sep_conj; [ reflexivity | ].
    unfold rewind_lt_impl.
    rewrite (sep_conj_Perms_commut (after l _)); rewrite sep_conj_Perms_meet_commute.
    apply meet_Perms_max_ent. intros P' [P [? ?]]; subst.
    apply ent_meet_Perms.
    exists (P * after l (singleton_Perms p)).
    split; [ intros | reflexivity ].
    rewrite (sep_conj_Perms_commut P (after l _)).
    rewrite sep_conj_Perms_distrib.
    (* FIXME: set up the right Proper instances to make this use rewriting *)
    etransitivity;
      [ eapply monotone_entails_sep_conj; [ reflexivity | ];
        apply bigger_Perms_entails; apply rewind_conj_of_conj | ].
    rewrite lfinished_dup.
    rewrite (sep_conj_Perms_distrib (lfinished l)).
    apply monotone_entails_sep_conj.
    - apply lfinished_after_recover_singleton; assumption.
    - apply H2.
  Qed.


  (* The rule to return part of the LHS permission of an lowned *)
  Lemma lowned_part_return l ls A (a:A) B P Q (R : A*B -> Perms) :
    P a * lowned l ls (fun ab => P (fst ab) * Q (snd ab)) R ⊨ lowned l ls Q (fun b => R (a,b)).
  Proof.
    unfold lowned.
    rewrite sep_conj_Perms_assoc.
    rewrite (sep_conj_Perms_commut (P a)).
    rewrite <- sep_conj_Perms_assoc.
    apply monotone_entails_sep_conj; [ reflexivity | ].
    apply rewind_lt_impl_part_apply.
  Qed.


  (* Apply an entailment to the LHS of an lowned permission set *)
  Lemma lowned_ent_lhs l ls A B (f : A -> B) P
    (Q1 : B -> Perms) (Q2 : A -> Perms) (R : B -> Perms)
    : (forall a, P * Q2 a ⊨ Q1 (f a)) ->
      P * lowned l ls Q1 R ⊨ lowned l ls Q2 (fun a => R (f a)).
  Proof.
    intro. unfold lowned.
    rewrite (sep_conj_Perms_commut P).
    rewrite <- sep_conj_Perms_assoc.
    apply monotone_entails_sep_conj; [ reflexivity | ].
    unfold rewind_lt_impl. rewrite sep_conj_Perms_meet_commute.
    apply meet_Perms_max_ent; intros. destruct_ex_conjs H0; subst.
    apply ent_meet_Perms. exists (x * P); split; [ intros | reflexivity ].
    rewrite (sep_conj_Perms_commut x).
    rewrite (sep_conj_Perms_assoc (Q2 a)).
    rewrite (sep_conj_Perms_commut (Q2 a)).
    rewrite H. apply H2.
  Qed.

  (* Apply an entailment to the RHS of an lowned permission set *)
  Lemma lowned_ent_rhs l ls A P (Q R1 R2 : A -> Perms) :
    (forall a, P * R1 a ⊨ R2 a) -> P * lowned l ls Q R1 ⊨ lowned l ls Q R2.
  Proof.
    intro. unfold lowned.
    rewrite (sep_conj_Perms_commut P).
    rewrite <- sep_conj_Perms_assoc.
    apply monotone_entails_sep_conj; [ reflexivity | ].
    unfold rewind_lt_impl. rewrite sep_conj_Perms_meet_commute.
    apply meet_Perms_max_ent; intros. destruct_ex_conjs H0; subst.
    apply ent_meet_Perms. exists (x * P); split; [ intros | reflexivity ].
    rewrite (sep_conj_Perms_assoc (Q a)).
    rewrite rewind_lt_of_conj.
    rewrite sep_conj_Perms_assoc.
    rewrite (H2 _). rewrite rewind_lt_gte_P.
    rewrite sep_conj_Perms_commut. apply H.
  Qed.

(* End LifetimeRules. *)
End LifetimePerms.
