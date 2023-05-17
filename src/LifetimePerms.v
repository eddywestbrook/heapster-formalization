(* begin hide *)
From Coq Require Import
     Arith.PeanoNat
     Logic.FunctionalExtensionality
     Logic.Decidable
     Lists.List
     Lia
     Classes.RelationClasses
     Classes.Morphisms
     FSets.FMaps.

From ITree Require Import
     ITree
     Eq.Eqit
     Events.Exception.

From Heapster Require Import
     Utils
     Permissions
     PermissionsSpred2
     Lifetime
     Typing
     SepStep
     MemoryPerms.

From Paco Require Import
     paco.

Import ListNotations.
Import ITreeNotations.
Local Open Scope itree_scope.
Open Scope list_scope.
(* end hide *)

Section LifetimePerms.

  Context {Si Ss : Type}.
  Context `{Hlens: Lens Si Lifetimes}.

  Definition nonLifetime (p : @perm (Si * Ss)) : Prop :=
    (* cannot change lifetimes *)
    (forall x y, guar p x y -> lget (fst x) = lget (fst y)).
      (*  /\ *)
      (* (* must continue to tolerate states no matter the lifetime *) *)
      (* (forall si ss si' ss' l1 l2, rely p (si, ss) (si', ss') -> *)
      (*                         rely p ((lput si l1), ss) ((lput si' l2), ss')). *)

  (* /\ *)
  (*     (forall si si' ss ss' l s, guar p (si, ss) (si', ss') -> *)
  (*                           guar p ((lput si (replace_list_index (lget si) l s)), ss) *)
  (*                                ((lput si' (replace_list_index (lget si') l s)), ss')). *)

  (*
  Program Definition nonLifetimeify (p : @perm (Si * Ss)) : perm :=
    {|
      pre := pre p;
      rely '(si, ss) '(si', ss') := exists l, rely p ((lput si l), ss) ((lput si' l), ss');
      guar x y := guar p x y /\ lget (fst x) = lget (fst y);
    |}.
  Next Obligation.
    constructor; repeat intro.
    - destruct x. exists nil. reflexivity.
    - destruct x, y, z. destruct H, H0.
      eexists. etransitivity; eauto.
  Qed.

  Lemma nonLifetimeify_works :
    nonLifetime (nonLifetimeify p).

    Lemma nonLifetimeify_lte :
      nonLifetimify p <= p.
   *)

  Lemma clos_trans_nonLifetime p q (Hp : nonLifetime p) (Hq : nonLifetime q) x y :
    Relation_Operators.clos_trans (Si * Ss) (guar p \2/ guar q) x y ->
    lget (fst x) = lget (fst y).
  Proof.
    repeat intro. induction H.
    - destruct H; [apply Hp | apply Hq]; auto.
    - etransitivity; eauto.
  Qed.

  Lemma nonLifetime_sep_conj p q (Hp : nonLifetime p) (Hq : nonLifetime q) :
    nonLifetime (p ** q).
  Proof.
    repeat intro.
    apply (clos_trans_nonLifetime p q); auto.
  Qed.

  Lemma nonLifetime_bottom : nonLifetime bottom_perm.
  Proof.
    repeat intro; cbn in *; subst; auto.
  Qed.

  Lemma nonLifetime_lte p q :
    nonLifetime p -> q <= p -> nonLifetime q.
  Proof.
    repeat intro. apply H0 in H1. apply H; auto.
  Qed.

  Lemma nonLifetime_sep_step p q :
    nonLifetime p -> sep_step p q -> nonLifetime q.
  Proof.
    repeat intro. eapply sep_step_guar in H1; eauto.
  Qed.

  (* Definition lifetime_invariant x y := *)
  (*   (forall n n', subsumes n' n (lget x) (lget x) -> *)
  (*            subsumes n' n (lget y) (lget y)) /\ *)
  (*     (forall n, lifetime_lte (lifetime (lget x) n) (lifetime (lget y) n)). *)

  (* Instance lifetime_invariant_preorder : PreOrder lifetime_invariant. *)
  (* Proof. *)
  (*   split; [split; intuition |]. *)
  (*   - intros ? ? ? [] []. split; auto; etransitivity; eauto. *)
  (* Qed. *)

  (* Definition monotonic_at (p : @perm C) (n : nat) x y : Prop := *)
  (*   guar p x y -> lifetime_lte (lifetime (lget x) n) (lifetime (lget y) n). *)

  (* Instance monotonic_at_reflexive p n : Reflexive (monotonic_at p n). *)
  (* Proof. *)
  (*   repeat intro. reflexivity. *)
  (* Qed. *)

  (* Lemma bottom_monotonic_at n : forall x y, monotonic_at bottom_perm n x y. *)
  (* Proof. *)
  (*   repeat intro. simpl in H. subst. reflexivity. *)
  (* Qed. *)

  (* Definition monotonic (P : Perms) (n : nat) : Prop := *)
  (*   forall p, p ∈ P -> exists p', p' <= p /\ p' ∈ P /\ forall x y, monotonic_at p' n x y. *)

  (* Lemma monotonic_bottom n : monotonic bottom_Perms n. *)
  (* Proof. *)
  (*   repeat intro. exists bottom_perm. split; [| split]. *)
  (*   apply bottom_perm_is_bottom. auto. apply bottom_monotonic_at. *)
  (* Qed. *)

  (* Program Definition restrict_monotonic_at (p : perm) (n : nat) : @perm C := *)
  (*   {| *)
  (*     pre := pre p; *)
  (*     rely := rely p; *)
  (*     guar := fun x y => guar p x y /\ monotonic_at p n x y; *)
  (*   |}. *)
  (* Next Obligation. *)
  (*   constructor; repeat intro. *)
  (*   - split; intuition. *)
  (*   - destruct H, H0. split; [etransitivity; eauto |]. intro. etransitivity; eauto. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   respects. *)
  (* Qed. *)

  (* Lemma restrict_monotonic_at_monotone p p' n : *)
  (*   p <= p' -> restrict_monotonic_at p n <= restrict_monotonic_at p' n. *)
  (* Proof. *)
  (*   intros []. constructor; intros; simpl; auto. destruct H. *)
  (*   split; auto. intro. auto. *)
  (* Qed. *)

  (* Lemma restrict_monotonic_at_lte p n : restrict_monotonic_at p n <= p. *)
  (* Proof. *)
  (*   constructor; intros; simpl in *; intuition. *)
  (* Qed. *)

  (* Definition invariant_at (p : perm) (n : nat) : Prop := *)
  (*   forall l1 l2 x y, guar p x y <-> guar p (replace_lifetime x n l1) (replace_lifetime y n l2). *)

  (* Lemma invariant_l p n (Hinv : invariant_at p n) : *)
  (*   forall l1 l2 x y, lifetime y n = Some l2 -> *)
  (*                guar p x y <-> guar p (replace_lifetime x n l1) y. *)
  (* Proof. *)
  (*   intros. *)
  (*   erewrite <- (replace_list_index_eq _ y n l2) at 2; auto. *)
  (* Qed. *)

  (* Lemma invariant_r p n (Hinv : invariant_at p n) : *)
  (*   forall l1 l2 x y, lifetime x n = Some l1 -> *)
  (*                guar p x y <-> guar p x (replace_lifetime y n l2). *)
  (* Proof. *)
  (*   intros. *)
  (*   rewrite <- (replace_list_index_eq _ x n l1) at 2; auto. *)
  (* Qed. *)

  (* Note: does not have permission to start or end the lifetime [n] *)
  Program Definition when
          (l : nat)
          (p : perm)
          (Hp : nonLifetime p) : perm :=
    {|
      pre x :=
      let '(si, _) := x in
      (statusOf l (lget si) = None \/ statusOf l (lget si) = Some current) ->
      pre p x;

      rely x y :=
      let '(si, _) := x in
      let '(si', _) := y in
        Lifetimes_lte (lget si) (lget si') /\
          (* if the lifetime isn't starting or already started, the rely of p must hold *)
          ((statusOf l (lget si') = None \/ statusOf l (lget si') = Some current) ->
           rely p x y);

      guar x y :=
        let '(si, _) := x in
        let '(si', _) := y in
        x = y \/
          Lifetimes_lte (lget si) (lget si') /\
            statusOf l (lget si) = Some current /\
            statusOf l (lget si') = Some current /\
            guar p x y;
    |}.
  Next Obligation.
    constructor; repeat intro.
    - destruct x. split; intuition.
    - destruct x, y, z.
      destruct H as (? & ?), H0 as (? & ?). split; [etransitivity; eauto |].
      intros [].
      + etransitivity; eauto. apply H1. left. specialize (H0 l). rewrite H3 in H0.
        destruct (statusOf l (lget s1)); auto; inversion H0.
      + etransitivity; eauto. apply H1. specialize (H0 l). rewrite H3 in H0.
        destruct (statusOf l (lget s1)); [destruct s5 |]; auto; inversion H0.
  Qed.
  Next Obligation.
    constructor; [intros [] | intros [] [] [] ? ?]; auto.
    decompose [and or] H; decompose [and or] H0; clear H H0.
    - inversion H1; inversion H2; subst; auto.
    - inversion H1. subst. auto.
    - inversion H4. subst. auto.
    - right. intuition. etransitivity; eauto.
  Qed.
  Next Obligation.
    destruct x, y.
    destruct H. intros. respects. apply H0.
    specialize (H l).
    destruct H2.
    - rewrite H2 in H.
      destruct (statusOf l (lget s)); auto; inversion H.
    - rewrite H2 in H.
      destruct (statusOf l (lget s)); [destruct s3 |]; auto; inversion H.
  Qed.

  Lemma when_monotone n p1 p2 Hp1 Hp2 : p1 <= p2 -> when n p1 Hp1 <= when n p2 Hp2.
  Proof.
    intros. destruct H. constructor; simpl; intros.
    - destruct x. auto.
    - destruct x, y. destruct H; auto.
    - destruct x, y. intuition.
  Qed.

  (* Instance Proper_lte_perm_when : *)
  (*   Proper (eq ==> lte_perm ==> eq ==> lte_perm) when. *)
  (* Proof. *)
  (*   repeat intro; subst. apply when_monotone; auto. *)
  (* Qed. *)

  (* Instance Proper_eq_perm_when : *)
  (*   Proper (eq ==> eq_perm ==> eq_perm) when. *)
  (* Proof. *)
  (*   repeat intro; subst. split; apply when_monotone; auto. *)
  (* Qed. *)

  (* Gives us permission to end the lifetime [n], which gives us back [p] *)
  Program Definition owned
          (l : nat)
          (p : perm)
          (Hp : nonLifetime p) : @perm (Si * Ss) :=
    {|
      (* TODO: probably need soemthing with subsumes *)
      pre x := let '(si, _) := x in
               statusOf l (lget si) = Some current;

      rely x y :=
      let '(si, _) := x in
      let '(si', _) := y in
      Lifetimes_lte (lget si) (lget si') /\
        statusOf l (lget si) = statusOf l (lget si') /\
        (statusOf l (lget si) = Some finished -> rely p x y);

      guar x y :=
      let '(si, ss) := x in
      let '(si', ss') := y in
      x = y \/
        (* Lifetimes_lte (lget si) (lget si') /\ *)
        (forall l', l <> l' -> statusOf l' (lget si) = statusOf l' (lget si')) /\
          length (lget si) = length (lget si') /\
          statusOf l (lget si') = Some finished /\
          guar p
               ((lput si (replace_list_index (lget si) l finished)), ss)
               ((lput si' (replace_list_index (lget si') l finished)), ss');
    |}.
  Next Obligation.
    constructor; repeat intro; auto.
    - destruct x. split; intuition.
    - destruct x, y, z.
      destruct H as (? & ? & ?), H0 as (? & ? & ?).
      split; [| split]; intros.
      + etransitivity; eauto.
      + etransitivity; eauto.
      + etransitivity; eauto. apply H4; auto. rewrite <- H1. auto.
  Qed.
  Next Obligation.
    constructor; repeat intro; auto.
    - destruct x. auto.
    - destruct x, y, z.
      decompose [and or] H; decompose [and or] H0; clear H H0.
      + inversion H1. inversion H2. subst; auto.
      + inversion H1. subst; auto.
      + inversion H4. subst; auto.
      + right. split; [| split; [| split]]; auto; etransitivity; eauto.
        transitivity (statusOf l' (lget s1)); eauto.
  Qed.
  Next Obligation.
    destruct x, y.
    destruct H as (? & ? & ?). rewrite <- H1. auto.
  Qed.

  Lemma owned_sep_step l p1 p2 Hp1 Hp2 :
    sep_step p1 p2 -> sep_step (owned l p1 Hp1) (owned l p2 Hp2).
  Proof.
    intros. rewrite sep_step_iff in *. destruct H.
    split; intros [] [] ?; cbn in *.
    - decompose [and or] H1; auto.
    - decompose [and or] H1; auto 6.
  Qed.

  Lemma owned_monotone l p1 p2 Hp1 Hp2 :
    p1 <= p2 -> owned l p1 Hp1 <= owned l p2 Hp2.
  Proof.
    intros. destruct H.
    constructor; cbn; intros.
    - destruct x. decompose [and or] H; auto.
    - destruct x, y. decompose [and or] H; auto.
    - destruct x, y. decompose [and or] H; auto 6.
  Qed.

  (* Instance Proper_lte_perm_owned l ls Hls : *)
  (*   Proper (lte_perm ==> lte_perm) (owned l ls Hls). *)
  (* Proof. *)
  (*   repeat intro; subst. apply owned_monotone; auto. *)
  (* Qed. *)

  (* Instance Proper_eq_perm_owned l ls H : *)
  (*   Proper (eq_perm ==> eq_perm) (owned l ls H). *)
  (* Proof. *)
  (*   repeat intro; subst. split; apply owned_monotone; auto. *)
  (* Qed. *)

  Program Definition lifetime_perm (n : nat) : (@perm (Si * Ss)) :=
    {|
      pre '(x, _) := length (lget x) = n;

      rely '(x, _) '(y, _) :=
      length (lget x) = length (lget y) /\
        Lifetimes_lte (lget x) (lget y) /\
        (forall n', n' >= n -> statusOf n' (lget x) = statusOf n' (lget y));

      guar '(x, _) '(y, _) :=
      (* (exists (ls : Lifetimes), y = lput (lget x) ls) /\ *)
      (forall l, l < n ->
            statusOf l (lget x) = statusOf l (lget y));
    |}.
  Next Obligation.
    constructor; repeat intro.
    - destruct x. split; [| split]; reflexivity.
    - destruct x, y, z. destruct H as (? & ? & ?), H0 as (? & ? & ?).
      split; [| split]; etransitivity; eauto.
      transitivity (statusOf n' (lget s1)); auto.
  Qed.
  Next Obligation.
    constructor; repeat intro.
    - destruct x. reflexivity.
    - destruct x, y, z. intros. transitivity (statusOf l (lget s1)); eauto.
  Qed.
  Next Obligation.
    destruct x, y. destruct H. rewrite <- H. auto.
  Qed.

  Program Definition lfinished
          (l : nat)
          (p : perm)
          (Hp : nonLifetime p) : perm :=
    {|
      pre x :=
      let '(si, _) := x in
      statusOf l (lget si) = Some finished /\
        pre p x;

      rely x y :=
      let '(si, _) := x in
      let '(si', _) := y in
      Lifetimes_lte (lget si) (lget si') /\ (* TODO: what if it is ending at the moment *)
        (statusOf l (lget si) = Some finished ->
         rely p x y);

      guar x y :=
        let '(si, _) := x in
        let '(si', _) := y in
        x = y \/
          lget si = lget si' /\
            statusOf l (lget si) = Some finished /\
            statusOf l (lget si') = Some finished /\
            guar p x y;
    |}.
  Next Obligation.
    constructor; repeat intro.
    - destruct x. split; intuition.
    - destruct x, y, z.
      destruct H as (? & ?), H0 as (? & ?). split; [etransitivity; eauto |].
      intros. etransitivity; eauto. apply H2. specialize (H l). rewrite H3 in H.
        destruct (statusOf l (lget s1)); [destruct s5 |]; auto; inversion H.
  Qed.
  Next Obligation.
    constructor; [intros [] | intros [] [] [] ? ?]; auto.
    decompose [and or] H; decompose [and or] H0; clear H H0.
    - inversion H1; inversion H2; subst; auto.
    - inversion H1. subst. auto.
    - inversion H4. subst. auto.
    - right. intuition. etransitivity; eauto.
  Qed.
  Next Obligation.
    destruct x, y. intuition.
    specialize (H1 l). rewrite H in H1.
    destruct (statusOf l (lget s1)); [destruct s3 |]; auto; inversion H1.
  Qed.

  Lemma when_finished_sep l p q Hp Hq : when l p Hp ⊥ lfinished l q Hq.
  Proof.
    constructor; intros; cbn in H; auto.
    - destruct x, y. decompose [and or] H; [inversion H0; subst; reflexivity |]; clear H.
      cbn. split. rewrite H1. reflexivity.
      intro. rewrite H2 in H. destruct H; inversion H.
    - destruct x, y. decompose [and or] H; [inversion H0; subst; reflexivity |]; clear H.
      cbn. split; auto.
      intros. rewrite H in H0. inversion H0.
  Qed.

  Lemma lte_lifetimes_guar_owned l s s' :
    (forall l' : nat, l <> l' -> statusOf l' (lget s) = statusOf l' (lget s')) ->
    statusOf l (lget s') = Some finished ->
    Lifetimes_lte (lget s) (lget s').
  Proof.
    intros Hneq Heq l'.
    destruct (Nat.eq_decidable l l').
    - subst. rewrite Heq. destruct (statusOf l' (lget s)); cbn; auto.
      destruct s0; cbn; auto.
    - erewrite Hneq; auto. reflexivity.
  Qed.


  (* not actually a special case of the above *)
  Lemma when_owned_sep l p q Hp Hq : when l p Hp ⊥ owned l q Hq.
  Proof.
    constructor; intros; cbn in H; auto.
    - destruct x, y. decompose [and or] H; [inversion H0; subst; reflexivity |]; clear H.
      cbn. split; auto. eapply lte_lifetimes_guar_owned; eauto.
      intros. rewrite H2 in H. destruct H; inversion H.
    - destruct x, y. decompose [and or] H; [inversion H0; subst; reflexivity |]; clear H.
      simpl. split; [| split]; auto.
      + rewrite H0, H2. auto.
      + intros. rewrite H in H0. discriminate H0.
  Qed.

  Lemma owned_lifetime_sep n n' p Hp :
    p ⊥ lifetime_perm n' ->
    n < n' ->
    owned n p Hp ⊥ lifetime_perm n'. (* add p ⊥ lifetime_perm *)
  Proof.
    intros Hsep Hlt.
    constructor; intros; cbn in *; auto.
    - destruct x, y. split; [| split]; auto.
      cbn. admit.
      intros. eapply Hsep. cbn. auto.
    - destruct x, y. decompose [and or] H; clear H.
      inversion H0. subst. split; [| split]; reflexivity.
      split; [| split]; auto.
      + eapply lte_lifetimes_guar_owned; eauto.
      + intros. apply H1. lia.
  Admitted.

  (* oh. this was not necessary all along *)
  Lemma lifetimes_sep_gen p q l Hp Hq :
    p ⊥ owned l q Hq ->
    when l p Hp ⊥ owned l (p ** q) (nonLifetime_sep_conj _ _ Hp Hq).
  Proof.
    intros.
    eapply when_owned_sep.
    (* split; intros. *)
    (* - destruct x, y. cbn in H0. *)
    (*   decompose [and or] H0; [inversion H1; subst; intuition |]. clear H0. *)
    (*   cbn. split; auto. intros []. *)
    (*   + rewrite H0 in H1. inversion H1. *)
    (*   + rewrite H0 in H1. inversion H1. *)
    (* - cbn in H0. destruct x, y. *)
    (*   decompose [and or] H0; [inversion H1; subst; intuition |]; clear H0. *)
    (*   cbn. split; [| split]; auto. *)
    (*   + intros. rewrite H1, H3. auto. *)
    (*   + intros. rewrite H1 in H0. discriminate H0. *)
  Abort.



  Lemma convert p q l Hp Hq :
    when l p Hp ** owned l (p ** q) (nonLifetime_sep_conj _ _ Hp Hq) <=
      p ** owned l q Hq.
  Proof.
    split; intros.
    - destruct x. cbn in *.
      decompose [and or] H; auto. split; auto. split; auto.
      eapply when_owned_sep; eauto.
    - destruct x, y. cbn in *.
      destruct H as (? & ? & ? & ?). split; [| split; [| split]]; auto.
    - destruct x, y. cbn in H.
      induction H. 2: econstructor 2; eauto.
      clear s s0 s1 s2.
      destruct x, y.
      decompose [and or] H; cbn; subst; try solve [constructor; auto]; clear H.
      rename H0 into Hneq, H1 into Hlen, H2 into Hfin, H4 into Hguar.
      apply Operators_Properties.clos_trans_t1n_iff.
      apply Operators_Properties.clos_trans_t1n_iff in Hguar.

      constructor 2 with (y := (lput s (replace_list_index (lget s) l finished), s0)).
      {
        do 2 right.
        setoid_rewrite lGetPut. rewrite lPutPut.
        split; [| split; [| split]].
        - intros. eapply nth_error_replace_list_index_neq; auto.
          rewrite Hlen.
          apply nth_error_Some. intro. unfold statusOf, Lifetimes in Hfin.
          rewrite Hfin in H0. inversion H0.
        - rewrite Hlen. apply replace_list_index_length. symmetry; auto.
          rewrite <- nth_error_Some. intro. unfold statusOf, Lifetimes in Hfin.
          rewrite Hfin in H. inversion H.
        - apply nth_error_replace_list_index_eq.
        - rewrite replace_list_index_twice. reflexivity.
      }
      rewrite <- (lPutGet s1).
      setoid_rewrite <- (replace_list_index_eq _ (lget s1)).
      2: apply Hfin.

      remember (lput _ _, s0). remember (lput _ _, s2).
      revert s s0 s1 s2 Hneq Hlen Hfin Heqp0 Heqp1. induction Hguar; intros; subst.
      + constructor 1. destruct H; auto.
        do 2 right.
        setoid_rewrite lGetPut. repeat rewrite lPutPut.
        repeat rewrite replace_list_index_twice.
        split; [| split; [| split]]; auto.
        * intros. unfold statusOf, Lifetimes in *.
          assert (l < length (lget s1)).
          { rewrite <- nth_error_Some. intro. rewrite Hfin in H1. inversion H1. }
          rewrite <- nth_error_replace_list_index_neq; auto.
          rewrite <- nth_error_replace_list_index_neq; auto. rewrite Hlen; auto.
        * erewrite <- replace_list_index_length; eauto.
          erewrite <- replace_list_index_length; eauto.
          rewrite Hlen. apply nth_error_Some. intro.
          unfold statusOf, Lifetimes in Hfin. rewrite Hfin in H0. inversion H0.
          apply replace_list_index_length_bound.
        * apply nth_error_replace_list_index_eq.
      + destruct y.
        assert (statusOf l (lget s3) = Some finished).
        {
          destruct H.
          - apply Hp in H. cbn in H.
            rewrite lGetPut in H. rewrite <- H. apply nth_error_replace_list_index_eq.
          - apply Hq in H. cbn in H.
            rewrite lGetPut in H. rewrite <- H. apply nth_error_replace_list_index_eq.
        }
        assert (s3 = lput s3 (replace_list_index (lget s3) l finished)).
        {
          setoid_rewrite <- (lPutGet s3).
          setoid_rewrite <- (replace_list_index_eq _ (lget s3)); eauto.
          rewrite lPutPut, lGetPut. rewrite replace_list_index_twice.
          reflexivity.
        }
        (* rewrite H1 in *. *)
        econstructor 2.
        2: {
          eapply (IHHguar s3 s4 s1 s2); eauto; clear IHHguar.
          - rewrite replace_list_index_eq in Hguar; auto.
            rewrite lPutGet in Hguar.
            apply Operators_Properties.clos_trans_t1n_iff in Hguar.
            pose proof (clos_trans_nonLifetime _ _ Hp Hq _ _ Hguar).
            cbn in H2. rewrite H2. reflexivity.
          - rewrite replace_list_index_eq in Hguar; auto.
            rewrite lPutGet in Hguar.
            apply Operators_Properties.clos_trans_t1n_iff in Hguar.
            pose proof (clos_trans_nonLifetime _ _ Hp Hq _ _ Hguar).
           cbn in H2. setoid_rewrite H2. reflexivity.
          - rewrite H1 at 1; reflexivity.
        }
        clear IHHguar.
        destruct H; auto.
        right. right.
        repeat rewrite lPutPut.
        setoid_rewrite lGetPut.
        repeat rewrite replace_list_index_twice.
        split; [| split; [| split]]; auto.
        * apply Hq in H. cbn in H. repeat rewrite lGetPut in H. rewrite H. reflexivity.
        * erewrite <- replace_list_index_length; auto.
          -- symmetry. transitivity (length (lget s1)); auto.
             rewrite replace_list_index_eq in Hguar; auto.
             rewrite lPutGet in Hguar.
             apply Operators_Properties.clos_trans_t1n_iff in Hguar.
             pose proof (clos_trans_nonLifetime _ _ Hp Hq _ _ Hguar).
             cbn in H2. setoid_rewrite H2. reflexivity.
          -- rewrite <- nth_error_Some. intro.
             unfold statusOf, Lifetimes in H0. rewrite H0 in H2. inversion H2.
        * rewrite <- H1. auto.
  Qed.

  (* special case of convert *)
  Lemma convert_bottom p n Hp :
    when n p Hp ** owned n p Hp <= p ** owned n bottom_perm nonLifetime_bottom.
  Proof.
  (*   rewrite <- (sep_conj_perm_bottom p) at 2. eapply convert; auto. *)
  (* Qed. *)
  Abort.

(* Lemma lcurrent_pre_trans' x n1 n2 n3 : *)
(*     lcurrent_pre x n1 n3 -> *)
(*     lcurrent_pre x n1 n2 /\ lcurrent_pre x n2 n3. *)
(* Proof. *)
(*   unfold lcurrent_pre. split. *)
(*   - split. *)
(*     + intro. apply H. *)
  (* Admitted. *)

  (** The naive defn is transitive, at least *)
(*    Program Definition lcurrent n1 n2 : @perm C :=
    {|
      pre x := subsumes n1 n2 (lget x) (lget x);
      rely x y := x = y \/
                    subsumes n1 n2 (lget x) (lget x) /\
                    subsumes n1 n2 (lget y) (lget y);
      guar x y := x = y;
    |}.
  Next Obligation.
    constructor; repeat intro; try solve [intuition].
    destruct H, H0; subst; auto.
    right. destruct H, H0. split; eapply subsumes_preorder; eauto; reflexivity.
  Qed.
  Next Obligation.
    constructor; repeat intro; subst; intuition.
  Qed.
  Next Obligation.
    destruct H; subst; auto. destruct H; intuition.
  Qed.

  Lemma lcurrent_transitive n1 n2 n3 :
    lcurrent n1 n3 <= lcurrent n1 n2 ** lcurrent n2 n3.
  Proof.
    constructor; intros; cbn; intuition.
    - destruct H as (? & ? & ?). simpl in *. eapply subsumes_preorder; eauto.
    - destruct H. simpl in *. destruct H, H0; subst; auto. right.
      destruct H, H0. split; auto; eapply subsumes_preorder; eauto.
  Qed.
*)
  Definition lifetime_Perms :=
    meet_Perms (fun Q => exists n : nat, Q = singleton_Perms (lifetime_perm n)).

  Definition when_Perms l P : Perms :=
    meet_Perms (fun R => exists p Hp, p ∈ P /\ R = singleton_Perms (when l p Hp)).

  Definition lfinished_Perms l P : Perms :=
    meet_Perms (fun R => exists p Hp, p ∈ P /\ R = singleton_Perms (lfinished l p Hp)).

  Definition lowned_Perms l P Q : Perms :=
    meet_Perms (fun R => exists r q Hq, R = singleton_Perms (r ** owned l q Hq) /\
                               q ∈ Q /\
                               (forall p, p ∈ P -> forall s, pre r s -> pre p s -> pre q s)).

  Program Definition lowned_Perms' l P Q :=
    {|
      in_Perms x :=
      exists r1 r2 Hr2,
        r1 ** owned l r2 Hr2 <= x /\
          (forall p, p ∈ P ->
                p ⊥ r1 ** owned l r2 Hr2 ->
                exists q, q ∈ Q /\
                       sep_step r2 q /\ (* means that q is also nonLifetime since r2 is *)
                       (* r1 ⊥ p /\ (* this can't be true for all p... *) *)
                       (forall c1 c2, pre p ((lput c1 (replace_list_index (lget c1) l current)), c2) ->
                                 pre r1 ((lput c1 (replace_list_index (lget c1) l current)), c2) ->
                                 pre q ((lput c1 (replace_list_index (lget c1) l finished)), c2)));
    |}.
  Next Obligation.
    destruct H as (r1 & r2 & Hr2 & Hlte & H).
    exists r1, r2, Hr2. split; auto. etransitivity; eauto.
    (* intros. apply H; auto. eapply separate_antimonotone; eauto. *)
  Qed.

  Lemma when_perm_Perms l p Hp P :
    p ∈ P ->
    when l p Hp ∈ when_Perms l P.
  Proof.
    intros H.
    eexists. split.
    - exists p, Hp. split; eauto.
    - cbn. reflexivity.
  Qed.

  Lemma lfinished_perm_Perms l p Hp P :
    p ∈ P ->
    lfinished l p Hp ∈ lfinished_Perms l P.
  Proof.
    intros H.
    eexists. split.
    - exists p, Hp. split; eauto.
    - cbn. reflexivity.
  Qed.

  (* Lemma lowned_perm_Perms l p Hp P : *)
  (*   p ∈ P -> *)
  (*   owned l p Hp ∈ lowned_Perms' l bottom_Perms P. *)
  (* Proof. *)
  (*   intros H. *)
  (*   exists bottom_perm, p, Hp. split. *)
  (*   - rewrite sep_conj_perm_commut. rewrite sep_conj_perm_bottom. reflexivity. *)
  (*   - intros ? ?. exists p. split; [| split]; auto. reflexivity. *)
  (*     intros. cbn in *. *)
  (* Qed. *)


  (*
    (* TODO: need to add pre_perm *)
  Lemma lowned_perm_Perms l ls Hsub p Hp P :
    p ∈ P ->
    owned l ls Hsub p Hp ∈ lowned_Perms' l ls Hsub P P.
  Proof.
    cbn. intros. cbn. exists p0. split; [| split]; auto. reflexivity.
    - do 3 eexists. split; [| split]. reflexivity.
      apply H.
      intros. apply H1.
    - exists (fun _ H => H). red. rewrite restrict_same.
      rewrite sep_conj_perm_commut. rewrite sep_conj_perm_bottom. reflexivity.
  Qed.
   *)

  (* returns the new lifetime *)
  Definition beginLifetime : itree (sceE Si) nat :=
    s <- trigger (Modify id);;
    trigger (Modify (fun s => lput s ((lget s) ++ [current])));;
    Ret (length (lget s)).

  Definition endLifetime (l : nat) : itree (sceE Si) unit :=
    s <- trigger (Modify id);;
    match nth_error (lget s) l with
    | Some current =>
        trigger (Modify (fun s =>
                           (lput s (replace_list_index
                                      (lget s)
                                      l
                                      finished))));;
        Ret tt
    | _ => throw tt
    end.

  (* Lemma sep_step_lowned p q l Hq : *)
  (*   p ⊥ owned l q Hq -> *)
  (*   p ⊥ q. *)
  (* Proof. *)
  (*   intros. constructor. *)
  (*   - destruct H. intros. apply H. cbn. destruct x, y. right. *)
  (* Qed. *)


  Lemma sep_step_owned_finished l p Hp :
    SepStep.sep_step
      (owned l p Hp)
      (lfinished l p Hp).
  Proof.
    repeat intro. constructor.
    - intros [] [] ?. cbn in *. apply H in H0. cbn in H0. intuition.
    - intros [] [] ?. cbn in *. destruct H0. rewrite H0. reflexivity.
      destruct H0 as (? & ? & ? & ?). apply H. cbn. right. intuition.
      + rewrite H0. reflexivity.
      + setoid_rewrite H0. reflexivity.
      + do 2 (rewrite replace_list_index_eq; auto).
        do 2 rewrite lPutGet; auto.
  Qed.

  Lemma sep_step_beginLifetime n :
    sep_step (lifetime_perm n)
             (owned n bottom_perm nonLifetime_bottom ** lifetime_perm (n + 1)).
  Proof.
    apply sep_step_rg.
    - intros [si ss] [si' ss'] ?. induction H; try solve [etransitivity; eauto].
      destruct H.
      + destruct x, y. cbn in *. intros. destruct H. inversion H. subst. reflexivity.
        apply H. lia.
      + destruct x, y. cbn in *. intros.
        apply H. lia.
      (* induction H; try solve [etransitivity; eauto]. destruct H. *)
      (* + destruct x, y. split; apply H; lia. *)
      (* + destruct x, y. simpl in *. subst; auto. *)
    - intros [si ss] [si' ss'] (Hlen & Hlte & Hlater). cbn in *.
      split; split; auto. split; auto. intros. apply Hlater. lia.
  Qed.

  Lemma typing_begin :
    typing lifetime_Perms
           (fun l _ => lowned_Perms' l top_Perms top_Perms * lifetime_Perms)
           beginLifetime
           (Ret tt).
  Proof.
    intros p' c1 c2 (? & (l & ?) & Hlte) Hpre; subst.
    unfold beginLifetime. unfold id.
    rewritebisim @bind_trigger.
    pstep. econstructor; eauto; try reflexivity.

    rewritebisim @bind_trigger.
    econstructor; auto.
    { apply Hlte in Hpre. cbn in Hpre. subst. apply Hlte. cbn.
      intros. rewrite lGetPut. symmetry. apply nth_error_app1; auto. }
    etransitivity. apply sep_step_lte'. apply Hlte. apply sep_step_beginLifetime.

    apply Hlte in Hpre. cbn in Hpre.
    econstructor.
    - cbn. do 2 rewrite lGetPut.
      split; [| split]; auto.
      + unfold statusOf. apply nth_error_app_last; auto.
      + rewrite app_length. rewrite Hpre. reflexivity.
      + apply owned_lifetime_sep. symmetry. apply separate_bottom. lia.
    - apply sep_conj_Perms_perm.
      + cbn. exists bottom_perm, bottom_perm, nonLifetime_bottom.
        split; intros; try contradiction.
        rewrite sep_conj_perm_commut. rewrite sep_conj_perm_bottom.
        rewrite Hpre. reflexivity.
      + eexists. split. eexists. reflexivity.
        cbn. reflexivity.
  Qed.

  Lemma typing_end l P Q :
    typing (P * (lowned_Perms' l P Q))
           (fun _ _ => lfinished_Perms l Q)
           (endLifetime l)
           (Ret tt).
  Proof.
    intros p' c1 c2 (p & lowned' & Hp & H & Hlte) Hpre. cbn in H.
    destruct H as (r1 & r2 & Hr2 & Hlte' & Hf).
    unfold endLifetime. unfold id.
    rewritebisim @bind_trigger.
    pstep. econstructor; eauto; try reflexivity.

    pose proof Hpre as Hpre''.
    apply Hlte in Hpre. destruct Hpre as (_ & Hpre & _).
    apply Hlte' in Hpre. destruct Hpre as (_ & H & _).
    cbn in H. setoid_rewrite H.
    rewritebisim @bind_trigger.
    specialize (Hf _ Hp). destruct Hf as (q & Hq & Hsep_step & Hpre).
    { apply Hlte in Hpre''. destruct Hpre'' as (? & ? & ?).
      eapply separate_antimonotone; eauto. }
    econstructor; unfold id. eauto.
    cbn in *. apply Hlte. constructor 1. right.
    apply Hlte'. constructor 1. right. right.
    {
      repeat rewrite lGetPut.
      split; [| split; [| split]].
      - intros. apply nth_error_replace_list_index_neq; auto.
        apply nth_error_Some. intro.
        unfold statusOf, Lifetimes in H. rewrite H1 in H. inversion H.
      - apply replace_list_index_length; auto. apply nth_error_Some. intro.
        unfold statusOf, Lifetimes in H. rewrite H0 in H. inversion H.
      - unfold statusOf. apply nth_error_replace_list_index_eq.
      - rewrite lPutPut, replace_list_index_twice. reflexivity.
    }
    2: {
      econstructor. 2: apply lfinished_perm_Perms; eauto.
      Unshelve. 2: eapply nonLifetime_sep_step; eauto.
      cbn. rewrite lGetPut.
      split. apply nth_error_replace_list_index_eq.
      apply Hpre; auto.
      - apply Hlte in Hpre''. cbn in H. rewrite replace_list_index_eq; auto.
        rewrite lPutGet. apply Hpre''.
      - apply Hlte in Hpre''. destruct Hpre'' as (_ & Hpre'' & _).
        apply Hlte' in Hpre''.
        rewrite replace_list_index_eq; auto.
        rewrite lPutGet. apply Hpre''.
    }
    eapply SepStep.sep_step_lte; eauto.
    eapply SepStep.sep_step_lte. apply lte_r_sep_conj_perm.
    eapply SepStep.sep_step_lte; eauto.
    eapply SepStep.sep_step_lte. apply lte_r_sep_conj_perm.
    etransitivity. 2: apply sep_step_owned_finished.
    apply owned_sep_step; auto.
  Qed.

  Lemma partial l P Q R :
    P * lowned_Perms' l (P * Q) R ⊨ lowned_Perms' l Q R.
  Proof.
    intros p0 (p & powned & Hp & (r1 & r2 & Hr2 & Hlte' & Hf) & Hlte).
    (* assert (Hp' : nonLifetime p) by admit. *)
    exists (p ** r1), r2, Hr2.
    split.
    {
      etransitivity; eauto. rewrite sep_conj_perm_assoc.
      apply sep_conj_perm_monotone; auto; reflexivity.
    }
    intros q Hq Hsep.
    specialize (Hf (p ** q)).
    destruct Hf as (r & Hr & Hsep_step & Hpre).
    - apply sep_conj_Perms_perm; auto.
    - (* need the precondition here *)
      admit.
  Abort.

  Lemma partial {config specConfig} l P Q R F ti ts :
    typing (lowned_Perms' l Q R)
           F ti ts ->
    @typing Si Ss config specConfig (P * (lowned_Perms' l (P * Q) R))
           F ti ts.
  Proof.
    intros Ht p' c1 c2 (p & powned & Hp & (r1 & r2 & Hr2 & Hlte' & Hf) & Hlte) Hpre.
    red in Ht. apply Ht; auto.
    exists (p ** r1), r2, Hr2. split; auto.
    - etransitivity; eauto. rewrite sep_conj_perm_assoc.
      apply sep_conj_perm_monotone; auto. reflexivity.
    - intros q Hq Hsep. specialize (Hf (p ** q)).
      destruct Hf as (r & Hr & Hsep_step & Hpre').
      + apply sep_conj_Perms_perm; auto.
      + symmetry. apply separate_sep_conj_perm; auto.
        * apply Hlte in Hpre. destruct Hpre as (_ & _ & Hpre).
          eapply separate_antimonotone in Hpre; eauto. symmetry. auto.
        * rewrite sep_conj_perm_assoc in Hsep.
          symmetry. eapply separate_antimonotone in Hsep; eauto.
          apply lte_r_sep_conj_perm.
        * rewrite sep_conj_perm_assoc in Hsep.
          eapply separate_antimonotone in Hsep; eauto.
          apply lte_l_sep_conj_perm.
      + exists r. split; [| split]; auto.
        intros. apply Hpre'; auto.
        2: apply H0.
        split; [| split]; auto. apply H0.
        rewrite sep_conj_perm_assoc in Hsep.
        symmetry.
        eapply separate_antimonotone in Hsep; eauto.
        apply lte_l_sep_conj_perm.
  Qed.

  (* not true, makes sense?
     lowned_Perms is not a "true" implication. *)
  Lemma add l P Q R :
    lowned_Perms' l Q R ⊨ lowned_Perms' l (P * Q) (P * R).
  Proof.
    intros p0 (r1 & r2 & Hr2 & Hlte' & Hf).
    (* assert (Hp' : nonLifetime p) by admit. *)
    unfold in_Perms. unfold lowned_Perms'. simpl.
    cbn.
    exists r1, r2, Hr2.
    split; auto.
    intros p1 (p & q & Hp & Hq & Hlte).
    specialize (Hf _ Hq).
    destruct Hf as (r & Hr & Hsep_step & Hpre).
  Abort.

  Lemma when_owned l p q Hp Hq :
    when l p Hp ⊥ owned l q Hq ->
    p ⊥ q.
  Proof.
    intros. split; intros [] [] ?.
    - destruct H as (? & _). specialize (sep_l (s, s0) (s1, s2)). cbn in sep_l.
      apply sep_l; auto. admit. admit.
    - destruct H as (_ & ?). specialize (sep_r (s, s0) (s1, s2)). cbn in sep_r.
      apply sep_r; auto. admit. admit.
  Abort.

  (* P initially = write_Perms p
     inside the owned P = read_Perms p

keep the permission on the value separate?
   *)
  Lemma foo l P Q R (Hinhab : exists q, q ∈ Q /\ nonLifetime q) :
    P * lowned_Perms' l Q R ⊨
    when_Perms l P * lowned_Perms' l (when_Perms l P * Q) (P * R).
  Proof.
    intros p0 (p & powned & Hp & (r1 & r2 & Hr2 & Hlte' & Hf) & Hlte).
    assert (Hp' : nonLifetime p) by admit.
    exists (when l p Hp').
    exists (r1 ** owned l (p ** r2) (nonLifetime_sep_conj _ _ Hp' Hr2)).
    split; [| split]; auto.
    - apply when_perm_Perms; auto.
    - do 3 eexists.
      split. reflexivity.
      intros p1 (pw & q & (? & (pr & Hpr' & Hpr & ?) & Hlte''') & Hq' & Hlte'') Hsep; subst.
      cbn in Hlte'''.
      specialize (Hf _ Hq'). destruct Hf as (r & Hr & Hsep_step & Hpre).
      {
        symmetry in Hsep.
        eapply separate_antimonotone in Hsep; eauto.
        eapply separate_antimonotone in Hsep; eauto.
        2: apply lte_r_sep_conj_perm.
        symmetry in Hsep.
        eapply separate_antimonotone in Hsep; eauto.
        apply sep_conj_perm_monotone. reflexivity.
        apply owned_monotone. apply lte_r_sep_conj_perm.
      }
      exists (pr ** r). split; [| split].
      + apply sep_conj_Perms_perm; auto. (* we don't have p ⊥ r, best we can do is that p ⊥ owned r2, and r2 ~> r *)
        (* lfinished_Perms could help? *)
      + (* apply sep_step_sep_conj_r; auto. *) admit. (* p ~ pr should be ok if they're both pointer permissions, but them being separate from r/r2 is a problem *)
      + intros. split; [| split]; auto.
        * apply Hlte'' in H. destruct H as (? & ? & ?).
          apply Hlte''' in H. cbn in H.
          rewrite lGetPut in H. setoid_rewrite nth_error_replace_list_index_eq in H.
          admit. (* should be ok if pr is a ptr permission *)
        * apply Hpre; auto. apply Hlte''; auto.
        * admit. (* we sort of have owned l r2 ⊥ when l r, but thta's true for any permissions inside the when and owned *)
    - etransitivity; eauto.
      etransitivity. 2: apply sep_conj_perm_monotone; [reflexivity |].
      2: apply Hlte'.
      do 2 rewrite <- sep_conj_perm_assoc.
      do 2 rewrite (sep_conj_perm_commut _ r1).
      do 2 rewrite sep_conj_perm_assoc.
      apply sep_conj_perm_monotone; [reflexivity |].
      apply convert.
  Qed.

  (* Require Import Heapster.Typing. *)

  (* Definition startLifetime : itree (sceE C) nat := *)
  (*   ret 0. *)
End LifetimePerms.
