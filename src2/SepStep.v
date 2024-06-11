(* begin hide *)
From Heapster2 Require Import
  Utils
  Permissions.

From Coq Require Import
     Classes.Morphisms
     Classes.RelationClasses.
(* end hide *)


Section step.
  Context {config : Type}.

  (** * Preserves separability *)
  Definition inv_strengthen (p q : @perm config) : Prop :=
    forall x, inv q x -> inv p x.
  Record sep_step (p q : perm) : Prop :=
    { sep_step_inv : inv_strengthen p q;
      sep_step_sep : forall r, p ⊥ r -> q ⊥ r }.

  (* Definition sep_step (p q : @perm config) := *)
  (*   forall r, p ⊥ r -> q ⊥ r. *)

  Global Instance Proper_eq_perm_sep_step_impl :
    Proper (eq_perm ==> eq_perm ==> Basics.flip Basics.impl) sep_step.
  Proof.
    repeat intro. destruct H1.
    split; auto. repeat intro.
    erewrite (eq_perm_inv x). 2: eauto.
    apply sep_step_inv0; auto.
    erewrite (eq_perm_inv y0). 2: eauto. auto.

    intros. rewrite H0. apply sep_step_sep0. rewrite <- H. auto.
  Qed.

  Global Instance Proper_eq_perm_sep_step_iff :
    Proper (eq_perm ==> eq_perm ==> Basics.flip iff) sep_step.
  Proof.
    constructor; apply Proper_eq_perm_sep_step_impl;
      try assumption; symmetry; assumption.
  Qed.

  Global Instance sep_step_refl : Reflexive sep_step.
  Proof.
    split; repeat intro; auto.
  Qed.

  Global Instance sep_step_trans : Transitive sep_step.
  Proof.
    split; repeat intro; auto.
    apply H, H0; auto.
    apply H0, H. auto.
  Qed.

  (* Lemma sep_step_lte : forall p p' q, p <= p' -> sep_step p q -> sep_step p' q. *)
  (* Proof. *)
  (*   repeat intro. split. repeat intro. apply H0 in H1. destruct H. apply inv_inc. *)
  (*   apply H0. symmetry. symmetry in H1. eapply separate_antimonotone; eauto. *)
  (* Qed. *)

  (* Lemma sep_step_lte' : forall p q, q <= p -> sep_step p q. *)
  (* Proof. *)
  (*   split; repeat intro. *)
  (*   - destruct H. symmetry. eapply separate_antimonotone; eauto. symmetry; auto. *)
  (* Qed. *)

  Program Definition sym_guar_perm (p : @perm config) : perm :=
    {|
      pre x := False;
      rely := guar p;
      guar := rely p;
      inv x := inv p x;
    |}.
  Next Obligation.
    eapply inv_guar; eauto.
  Qed.
  Next Obligation.
    eapply inv_rely; eauto.
  Qed.


  Lemma separate_self_sym : forall p, p ⊥ sym_guar_perm p.
  Proof.
    intros. split; intros; auto.
  Qed.

  Lemma sep_step_rely : forall p q x y, sep_step p q ->
                                   inv q x ->
                                   rely p x y ->
                                   rely q x y.
  Proof.
    intros. destruct H. specialize (sep_step_sep0 (sym_guar_perm p) (separate_self_sym _)).
    apply sep_step_sep0; cbn; auto.
  Qed.

  Lemma sep_step_guar : forall p q x y, sep_step p q ->
                                   (* inv p x -> *)
                                   inv q x ->
                                   guar q x y ->
                                   guar p x y.
  Proof.
    intros. destruct H as (? & H).
    specialize (H (sym_guar_perm p) (separate_self_sym p)).
    apply H; cbn; auto.
  Qed.

  Lemma sep_step_rg : forall p q,
      (forall x, inv q x -> inv p x) ->
      (forall x y, inv q x -> guar q x y -> guar p x y) ->
      (forall x y, inv q x -> rely p x y -> rely q x y) ->
      sep_step p q.
  Proof.
    repeat intro. split; intros.
    - red. apply H; auto.
    - split; intros.
      + apply H1; auto. apply H2; auto.
      + apply H2; auto.
  Qed.

  Lemma sep_step_sep_conj_l : forall p1 p2 q, p1 ⊥ q -> sep_step p1 p2 -> sep_step (p1 ** q) (p2 ** q).
  Proof.
    intros p1 p2 q ? ?. split; auto.
    - repeat intro. cbn. split; [| split]; auto. apply H0; auto. apply H1. apply H1.
    - apply sep_step_rg.
      + intros. destruct H1 as (? & ? & ?). split; [| split]; auto. apply H0; auto.
      + intros. destruct H1 as (? & ? & ?).
        induction H2; auto.
        * destruct H2.
          constructor. left. eapply sep_step_guar; eauto.
          constructor. right. auto.
        * etransitivity; eauto.
          apply (clos_trans_preserves (fun x => inv p2 x /\ inv q x)) in H2_.
          -- destruct H2_.
             apply IHclos_trans2; auto.
          -- intros. destruct H2. destruct H5; auto.
             split.
             eapply inv_guar; eauto.
             apply H4 in H5; auto. eapply inv_rely; eauto.
             split.
             apply H4 in H5; auto. eapply inv_rely; eauto.
             eapply inv_guar; eauto.
          -- split; auto.
      + intros. destruct H1 as (? & ? & ?). destruct H2.
        split; auto. eapply sep_step_rely; eauto.
  Qed.

  Lemma sep_step_sep_conj_r p1 p2 q : p1 ⊥ q -> sep_step p1 p2 -> sep_step (q ** p1) (q ** p2).
  Proof.
    intros. rewrite (sep_conj_perm_commut _ p1). rewrite (sep_conj_perm_commut _ p2).
    apply sep_step_sep_conj_l; assumption.
  Qed.


  Lemma sep_step_lte p1 p2 q1 : p1 <= q1 -> sep_step p1 p2 ->
                                sep_step q1 (invperm (inv q1) ** p2).
  Proof.
    intros; apply sep_step_rg; intros.
    - destruct H1 as [? [? ?]]; assumption.
    - simpl in H2. rewrite clos_trans_eq_or in H2; [ | typeclasses eauto ].
      rewrite clos_trans_trans in H2; [ | typeclasses eauto ].
      destruct H1 as [? [? ?]]. apply H; auto. eapply sep_step_guar; eauto.
    - split; [ intro; eapply inv_rely; eauto | ].
      destruct H1 as [? [? ?]]. eapply sep_step_rely; eauto.
  Qed.

  (* Setting a precondition on p sep_steps to p *)
  Lemma set_pre_sep_step pred p : sep_step (set_pre_perm pred p) p.
  Proof.
    apply sep_step_rg; intros; assumption.
  Qed.

  (* Adding a precondition on p sep_steps to p *)
  Lemma add_pre_sep_step pred p : sep_step (add_pre_perm pred p) p.
  Proof.
    apply sep_step_rg; intros; assumption.
  Qed.

  (* Permission entailment is sep_step plus the requirement that the
  precondition plus invariant of the LHS implies that of the RHS *)
  Record entails_perm (p q : perm) : Prop :=
    { entails_inv : inv_strengthen p q;
      entails_sep : forall r, p ⊥ r -> q ⊥ r;
      entails_pred : forall x, inv p x /\ pre p x -> inv q x /\ pre q x }.

  Notation "p ⊢ q" := (entails_perm p q) (at level 60).

  (* Entailment respects permission eauality *)
  Global Instance Proper_eq_entails_perm_impl :
    Proper (eq_perm ==> eq_perm ==> Basics.impl) entails_perm.
  Proof.
    intros p1 p2 Rp q1 q2 Rq H. constructor; repeat intro.
    - apply Rp. apply (entails_inv _ _ H). apply Rq. assumption.
    - rewrite <- Rq. apply (entails_sep _ _ H). rewrite Rp. assumption.
    - assert (inv p1 x /\ pre p1 x);
        [ destruct H0; split; apply Rp; assumption | ].
      pose proof (entails_pred _ _ H x H1) as [? ?].
      split; apply Rq; assumption.
  Qed.

  Global Instance Proper_eq_entails_perm_flip_impl :
    Proper (eq_perm ==> eq_perm ==> Basics.flip Basics.impl) entails_perm.
  Proof.
    repeat intro.
    refine (Proper_eq_entails_perm_impl y x _ y0 x0 _ H1); symmetry; assumption.
  Qed.

  (* Entailment implies sep_step *)
  Lemma entails_perm_sep_step p q : entails_perm p q -> sep_step p q.
  Proof. intro H; destruct H; constructor; assumption. Qed.

  (* sep_step plus preserving the invariant plus precondition gives entailment *)
  Lemma sep_step_entails_perm p q :
    sep_step p q -> (forall x, inv p x /\ pre p x -> inv q x /\ pre q x) ->
    entails_perm p q.
  Proof.
    intros; destruct H; constructor; assumption.
  Qed.

  (* entailment is a preorder *)
  Global Instance PreOrder_entails_perm : PreOrder entails_perm.
  Proof.
    constructor; repeat intro.
    - apply sep_step_entails_perm; [ reflexivity | ].
      intros; assumption.
    - apply sep_step_entails_perm;
        [ transitivity y; apply entails_perm_sep_step; assumption | ].
      intros. eapply entails_pred; [ eassumption | ].
      eapply entails_pred; eassumption.
  Qed.

  (* A bigger permission entails a smaller one augmented with the invariant of
     the bigger one *)
  Lemma bigger_perm_entails_inv p q :
    p >= q -> entails_perm p (invperm (inv p) ** q).
  Proof.
    intro. apply sep_step_entails_perm.
    - eapply sep_step_lte; [ eassumption | reflexivity ].
    - intros x [? ?]. split; [ | split; [ apply I | apply H; assumption ] ].
      split; [ assumption | ]. split; [ apply H; assumption | ].
      apply separate_bigger_invperm; assumption.
  Qed.

  (* A bigger permission entails a smaller one that has the same invariant *)
  Lemma bigger_perm_entails p q :
    p >= q -> (forall x, inv q x -> inv p x) -> entails_perm p q.
  Proof.
    intros. pose proof (bigger_perm_entails_inv p q H).
    rewrite (eq_invperm (inv q) (inv p)) in H1;
      [ | split; [ apply H0 | apply H ] ].
    rewrite sep_conj_perm_commut in H1.
    rewrite sep_conj_self_invperm in H1.
    assumption.
  Qed.

  (* Conjunction is monotonic wrt entailment on separate permissions *)
  Lemma monotone_entails_sep_conj_perm p p' q q' :
    p ⊥ q -> p ⊢ p' -> q ⊢ q' -> p ** q ⊢ p' ** q'.
  Proof.
    repeat intro. apply sep_step_entails_perm.
    - etransitivity; [ apply sep_step_sep_conj_l | apply sep_step_sep_conj_r ];
        try assumption; try (apply entails_perm_sep_step; assumption).
      symmetry; eapply entails_sep; eassumption.
    - intros x [[? [? ?]] [? ?]].
      destruct (entails_pred p p' H0 x (conj H2 H5)).
      destruct (entails_pred q q' H1 x (conj H3 H6)).
      simpl. split_conjs; try assumption.
      eapply entails_perm_sep_step; try eassumption.
      symmetry; eapply entails_perm_sep_step; try eassumption.
      symmetry; assumption.
  Qed.

  (* NOTE: rewind_perm is NOT Proper wrt entailment, because the precondition of
     rewind_perm p q does not include pre q, and so we can't use entails_pred
     with q |- q' to prove inv q. Fixing this would require rewind_perm to be
     defined using add_pre instead of set_pre, which we don't want to do because
     using set_pre here is specifically the point of rewind_perm.
  (* rewind_perm is Proper wrt entailment *)
  Global Instance Proper_ent_rewind_perm f :
    Proper (entails_perm ==> entails_perm ==> entails_perm) (rewind_perm f).
  Proof.
    repeat intro. apply sep_step_entails_perm; [ apply sep_step_rg | ]; intros.
    - apply (entails_inv _ _ H0). assumption.
    - apply (sep_step_guar x0 y0); [ apply entails_perm_sep_step | | ]; assumption.
    - apply (sep_step_rely x0 y0); [ apply entails_perm_sep_step | | ]; assumption.
    - simpl in H1.  destruct_ex_conjs H1; subst. simpl.
  Admitted.
   *)

  (* FIXME: docs *)
  Lemma mono_ent_rewind_conj_perm f p q r :
    (forall x, inv (p**q) x -> pre (p**q) x -> rely q x (f x)) ->
    q ⊢ r -> rewind_perm f (p ** q) q ⊢ rewind_perm f (p ** r) r.
  Proof.
    intros. apply sep_step_entails_perm; [ apply sep_step_rg | ]; intros.
    - apply (entails_inv _ _ H0). assumption.
    - apply (sep_step_guar q r); [ apply entails_perm_sep_step | | ]; assumption.
    - apply (sep_step_rely q r); [ apply entails_perm_sep_step | | ]; assumption.
    - destruct H1.
      assert (pre q x).
      1: { eapply pre_inc; try eassumption.
           apply rewind_conj_rely_gte; apply H. }
      assert (inv r x /\ pre r x) as [? ?];
        [ eapply entails_pred; [ | split ]; eassumption | ].
      split; [ assumption | ].
      simpl in H2; destruct_ex_conjs H2; subst.
      assert (inv r x1 /\ pre r x1) as [? ?];
        [ eapply entails_pred; [ eassumption | split; assumption ] | ].
      assert (rely q x1 (f x1)); [ apply H; repeat (split; try assumption) | ].
      assert (rely r x1 (f x1));
        [ eapply sep_step_rely; try apply entails_perm_sep_step; eassumption | ].
      assert (inv r (f x1) /\ pre r (f x1)) as [? ?];
        [ split; [ eapply inv_rely | eapply pre_respects ]; eassumption | ].
      assert (rely r (f x1) x);
        [ eapply sep_step_rely; try apply entails_perm_sep_step; eassumption | ].
      exists (f x1). split; [ assumption | ]. split; [ | assumption ].
      eexists; split; [ reflexivity | ].
      split; [ | split; assumption ].
      split; [ assumption | ]. split; [ assumption | ].
      symmetry; eapply entails_sep; [ | symmetry ]; eassumption.
  Qed.


  (* rewind_same_perm f is monotone wrt p |- q if f is in the rely of q *)
  (* FIXME: there should be a simpler proof using rewind_self_gte *)
  Lemma mono_ent_rewind_same_perm f p q :
    (forall x, inv p x -> pre p x -> rely p x (f x)) ->
    p ⊢ q -> rewind_same_perm f p ⊢ rewind_same_perm f q.
  Proof.
    intros. unfold rewind_same_perm.
    transitivity (rewind_perm f (bottom_perm ** p) p);
      [ rewrite sep_conj_perm_commut; rewrite sep_conj_perm_bottom; reflexivity | ].
    transitivity (rewind_perm f (bottom_perm ** q) q);
      [ | rewrite sep_conj_perm_commut; rewrite sep_conj_perm_bottom; reflexivity ].
    apply mono_ent_rewind_conj_perm; [ | assumption ].
    intros. destruct H1 as [? [? ?]]. destruct H2.
    apply H; assumption.
  Qed.


  (* A stronger version of the above (FIXME: better docs) *)
  (* FIXME: might not need this any more...? *)
  Lemma mono_ent_conj_rewind_same_perm f p q r :
    (forall x, rely p x (f x)) -> p ⊥ r ->
    p ⊢ q -> rewind_same_perm f (p ** r) ⊢ rewind_same_perm f (q ** r).
  Proof.
    intros.
    assert (p ** r ⊢ q ** r);
      [ apply monotone_entails_sep_conj_perm; try assumption; reflexivity | ].
    apply sep_step_entails_perm; [ apply sep_step_rg | ]; intros.
    - apply (entails_inv _ _ H2). assumption.
    - apply (sep_step_guar (p ** r) (q ** r)); [ apply entails_perm_sep_step | | ]; assumption.
    - apply (sep_step_rely (p ** r) (q ** r)); [ apply entails_perm_sep_step | | ]; assumption.
    - simpl in H3. destruct_ex_conjs H3; subst.
      assert (q ⊥ r); [ eapply entails_sep; eassumption | ].
      assert (inv q x1 /\ pre q x1) as [? ?];
        [ eapply entails_pred; [ eassumption | split; assumption ] | ].
      assert (pre p (f x1)); [ eapply pre_respects; try apply H; eassumption | ].
      pose (H x1).
      assert (pre p x); [ eapply pre_respects; [ etransitivity | ]; eassumption | ].
      assert (inv q (f x1) /\ pre q (f x1)) as [? ?];
        [ eapply entails_pred; [ | split ]; eassumption | ].
      assert (inv q x /\ pre q x) as [? ?];
        [ eapply entails_pred; [ | split ]; eassumption | ].
      assert (rely q (f x1) x);
        [ eapply sep_step_rely; try apply entails_perm_sep_step; try eassumption | ].
      split.
      + split; [ | split ]; assumption.
      + exists (f x1). split; [ split; [ | split ]; assumption | ].
        split; [ | split; assumption ].
        eexists. split; [ reflexivity | ].
        split; [ split; [ | split ] | split ]; assumption.
  Qed.


  (** Permission set entailment *)

  Definition entails_Perms P Q :=
    forall p, p ∈ P -> exists q, q ∈ Q /\ entails_perm p q.

  Notation "P ⊨ Q" := (entails_Perms P Q) (at level 60).

  Global Instance entails_Perms_preorder : PreOrder entails_Perms.
  Proof.
    constructor; repeat intro.
    - exists p; split; [ assumption | reflexivity ].
    - destruct (H p H1) as [q [? ?]].
      destruct (H0 q H2) as [r [? ?]].
      exists r; split; [ assumption | ].
      etransitivity; eassumption.
  Qed.

  Global Instance Proper_lte_Perms_entails_Perms :
    Proper (lte_Perms --> lte_Perms ==> Basics.flip Basics.impl) entails_Perms.
  Proof.
    repeat intro.
    apply H in H2. destruct (H1 p H2) as [q [? ?]]. apply H0 in H3.
    exists q; split; assumption.
  Qed.

  Global Instance Proper_eq_Perms_entails_Perms :
    Proper (eq_Perms ==> eq_Perms ==> Basics.flip Basics.impl) entails_Perms.
  Proof.
    repeat intro. destruct H; destruct H0.
    apply (Proper_lte_Perms_entails_Perms _ _ H3 _ _ H0 H1). assumption.
  Qed.

  (* A bigger permission set entails a smaller one *)
  Lemma bigger_Perms_entails P Q : P ⊒ Q -> P ⊨ Q.
  Proof.
    repeat intro. exists p; split; [ apply H; assumption | reflexivity ].
  Qed.

  (* Entailment on permissions yields entailment on their singleton sets *)
  Lemma entails_singleton_Perms p q :
    p ⊢ q -> singleton_Perms p ⊨ singleton_Perms q.
  Proof.
    repeat intro. exists (invperm (inv p0) ** q). simpl in H0.
    split; [ apply lte_r_sep_conj_perm | ].
    etransitivity; [ apply bigger_perm_entails_inv; eassumption | ].
    apply monotone_entails_sep_conj_perm; [ | reflexivity | assumption ].
    apply separate_bigger_invperm; assumption.
  Qed.

  (* A permission set conjunction entails its left-hand side *)
  Lemma entails_l_sep_conj P Q : P * Q ⊨ P.
  Proof.
    intros p H. exists p; split; [ | reflexivity ].
    apply (lte_l_sep_conj_Perms _ Q p). assumption.
  Qed.

  (* A permission set conjunction entails its right-hand side *)
  Lemma entails_r_sep_conj P Q : P * Q ⊨ Q.
  Proof.
    intros p H. exists p; split; [ | reflexivity ].
    apply (lte_r_sep_conj_Perms P Q p). assumption.
  Qed.

  (* Permission set conjunction is monotonic wrt entailment *)
  Lemma monotone_entails_sep_conj P P' Q Q' :
    P ⊨ P' -> Q ⊨ Q' -> P * Q ⊨ P' * Q'.
  Proof.
    intros entP entQ pq H. destruct H as [p [q [? [? [? ?]]]]].
    destruct (entP p H) as [p' [? ?]].
    destruct (entQ q H0) as [q' [? ?]].
    exists (invperm (inv pq) ** (p' ** q')); split.
    - exists p'; exists q'.
      split_conjs; try assumption; try apply lte_r_sep_conj_perm.
      eapply entails_sep; try eassumption.
      symmetry; eapply entails_sep; try eassumption.
      symmetry; assumption.
    - etransitivity; [ apply bigger_perm_entails_inv; apply H1 | ].
      apply monotone_entails_sep_conj_perm;
       [ apply separate_bigger_invperm; assumption | reflexivity | ].
      apply monotone_entails_sep_conj_perm; assumption.
  Qed.

  (* Monotonicity of sep_conj_Perms wrt entailment as a Proper instance *)
  Global Instance Proper_ent_sep_conj_Perms :
    Proper (entails_Perms ==> entails_Perms ==> entails_Perms) sep_conj_Perms.
  Proof.
    intros P1 P2 entP Q1 Q2 entQ.
    apply monotone_entails_sep_conj; assumption.
  Qed.


  (* Meet is a lower bound wrt entailment for all its elements *)
  Lemma ent_meet_Perms : forall (Ps : Perms -> Prop) P,
      (exists Q, Ps Q /\ P ⊨ Q) ->
      P ⊨ meet_Perms Ps.
  Proof.
    repeat intro. destruct H as [Q [? ?]].
    destruct (H1 p H0) as [q [? ?]].
    exists q; split; [ | assumption ].
    exists Q. split; assumption.
  Qed.

  (* A meet is the greatest lower bound wrt entailment for all its elements *)
  Lemma meet_Perms_max_ent : forall (Ps : Perms -> Prop) Q,
      (forall P, Ps P -> P ⊨ Q) ->
      meet_Perms Ps ⊨ Q.
  Proof.
    repeat intro. destruct H0 as [P [? ?]].
    apply (H P H0 p H1).
  Qed.

  (* A join is an upper bound wrt entailment for all its elements *)
  Lemma ent_join_Perms : forall (Ps : Perms -> Prop) P,
      (exists Q, Ps Q /\ Q ⊨ P) ->
      join_Perms Ps ⊨ P.
  Proof.
    repeat intro. destruct H as [Q [? ?]].
    destruct (H1 p (H0 Q H)) as [q [? ?]].
    exists q; split; assumption.
  Qed.

  (* FIXME: the Q ⊨ P proof for each P in Ps could yield a *different*
  permission in P for each P, so this requires a join on perm *)
  (*
  Lemma join_Perms_min_ent : forall (Ps : Perms -> Prop) Q,
      (forall P, Ps P -> Q ⊨ P) ->
      Q ⊨ join_Perms Ps.
  Proof.
    repeat intro.
   *)

  Lemma ent_join_Perms2 P Q R : (Q ⊨ P \/ R ⊨ P) -> join_Perms2 Q R ⊨ P.
  Proof.
    intro. apply ent_join_Perms.
    destruct H; eexists; (split; [ | eassumption ]);
      solve [ left; reflexivity | right; reflexivity ].
  Qed.

  (* FIXME: requires a binary join on perm *)
  (*
  Lemma join_Perms2_min_ent P Q R : R ⊨ P -> R ⊨ Q -> R ⊨ join_Perms2 P Q.
  Proof.
    intros.
   *)

  (* A prop_Perms on the left entails a permission if its proposition implies
  the entailment *)
  Lemma prop_Perms_ent (P:Prop) Q R : (P -> Q ⊨ R) -> prop_Perms P * Q ⊨ R.
  Proof.
    repeat intro.
    assert (pf : P); [ destruct H0 as [q' [q [pf ?]]]; assumption | ].
    rewrite (proj2 (prop_Perms_bottom P) pf) in H0.
    rewrite sep_conj_Perms_bottom_identity in H0.
    destruct (H pf p H0) as [r [? ?]].
    exists r; split; assumption.
  Qed.

  (* A mkPerms entails P if the singleton of one of its elements does *)
  Lemma mkPerms_ent (Ps : perm -> Prop) Q :
    (forall p, Ps p -> singleton_Perms p ⊨ Q) -> mkPerms Ps ⊨ Q.
  Proof.
    intro H. rewrite mkPerms_meet.
    apply meet_Perms_max_ent; intros. destruct_ex_conjs H0; subst.
    apply H; assumption.
  Qed.

  (* Adding a precondition yields a bigger permission set wrt entailment *)
  Lemma add_pre_ent_P (pred : config -> Prop) P : add_pre pred P ⊨ P.
  Proof.
    apply bigger_Perms_entails; apply add_pre_gte_P.
  Qed.

  Lemma add_poss_pre_ent (pred : config -> Prop) P Q :
    (forall p x, p ∈ add_pre pred P -> pre p x -> inv p x -> pred x ->
                 singleton_Perms p ⊨ Q) ->
    add_poss_pre pred P ⊨ Q.
  Proof.
    unfold add_poss_pre. intro H. rewrite mkPerms_meet.
    apply meet_Perms_max_ent; intros. destruct_ex_conjs H0; subst.
    eapply H; eassumption.
  Qed.

  Lemma add_poss_pre_meet_ent (pred : config -> Prop) (Ps : Perms -> Prop) Q :
    (forall P x, Ps P -> Perms_field P x -> pred x -> add_pre pred P ⊨ Q) ->
    add_poss_pre pred (meet_Perms Ps) ⊨ Q.
  Proof.
    unfold add_poss_pre. intro H. rewrite mkPerms_meet.
    apply meet_Perms_max_ent; intros. simpl in H0. destruct_ex_conjs H0; subst.
    etransitivity; [ | apply (H x2 x3); try assumption ].
    - apply bigger_Perms_entails. repeat intro. simpl in H0.
      eexists; split; [ eexists; split; [ eassumption | reflexivity ] | ].
      etransitivity; eassumption.
    - exists x. repeat split; try assumption.
      eapply Perms_upwards_closed; [ eassumption | ].
      etransitivity; [ | eassumption ].
      constructor; try (intros; assumption).
      intros. destruct H5; assumption.
  Qed.

  (* FIXME: rewind is only Proper wrt entailment on permissions that contain f
     in their rely, so we can use mono_ent_rewind_same_perm

  Lemma Proper_ent_rewind f :
    Proper (entails_Perms ==> entails_Perms) (rewind f).
  Proof.
    intros P Q ent. unfold rewind; repeat rewrite mapPerms_as_meet.
    apply meet_Perms_max_ent; intros. destruct_ex_conjs H; subst.
    destruct (ent x H) as [q [? ?]].
    apply ent_meet_Perms. eexists.
    split; [ eexists; split; [ eassumption | reflexivity ] | ].
    apply entails_singleton_Perms.

    repeat intro. simpl in H0. destruct_ex_conjs H0; subst.

    destruct (H p)
   *)

  (* rewind_conj f P is monotone wrt entailment when f is in the guar of P *)
  Lemma mono_ent_rewind_conj f P Q R :
    (forall p x, p ∈ P -> inv p x -> pre p x -> guar p x (f x)) ->
    Q ⊨ R -> rewind_conj f P Q ⊨ rewind_conj f P R.
  Proof.
    repeat intro. simpl in H1; destruct_ex_conjs H1; subst.
    destruct (H0 x1 H1) as [r [? ?]].
    exists (invperm (inv p) ** rewind_perm f (x0 ** r) r). split.
    - eapply Perms_upwards_closed; [ | apply lte_r_sep_conj_perm ].
      eexists; split; [ | reflexivity ].
      eexists; eexists. repeat (split; [ eassumption | ]).
      split; [ | reflexivity ].
      symmetry; eapply entails_sep; try symmetry; eassumption.
    - etransitivity; [ apply bigger_perm_entails_inv; eassumption | ].
      apply monotone_entails_sep_conj_perm.
      + apply separate_bigger_invperm; assumption.
      + reflexivity.
      + apply mono_ent_rewind_conj_perm; [ | assumption ].
        intros x [? [? ?]] [? ?]. eapply sep_r; try eassumption.
        apply H; assumption.
  Qed.


End step.

Notation "P ⊨ Q" := (entails_Perms P Q) (at level 60).
Notation "p ⊢ q" := (entails_perm p q) (at level 60).
