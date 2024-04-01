(* begin hide *)
From Heapster2 Require Import
     Permissions.
     (* PermissionsSpred2. *)

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

End step.
