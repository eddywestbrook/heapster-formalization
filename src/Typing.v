(* begin hide *)
From Coq Require Import
     Structures.Equalities
     Classes.Morphisms
     Classes.RelationClasses
     Relations.Relation_Operators
     Relations.Operators_Properties
     ProofIrrelevance.

From Heapster Require Import
     Utils
     Permissions
     SepStep.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From Paco Require Import
     paco.

From ITree Require Import
     ITree
     Eq.Eqit
     Eq.EqAxiom
     Events.State
     Events.Exception
     Events.Nondeterminism.

Import ITreeNotations.
Local Open Scope itree_scope.
(* end hide *)

(** * Bisimulation axiom *)
(** We make use of the [bisimulation_is_eq] axiom from the ITrees library.
    This axiom is used to avoid setoid rewriting up to strong bisimulation,
    [eq_itree eq]. This is used for convenience, we could also prove Proper
    instances for our definitions. *)
Ltac rewritebisim lem := pose proof lem as bisim;
                         eapply EqAxiom.bisimulation_is_eq in bisim;
                         rewrite bisim;
                         clear bisim.

Ltac rewritebisim_in lem H := pose proof lem as bisim;
                              eapply EqAxiom.bisimulation_is_eq in bisim;
                              rewrite bisim in H;
                              clear bisim.

Lemma throw_vis {E R} `{exceptE unit -< E} (k : void -> itree E R) :
  vis (Throw tt) k = throw tt.
Proof.
  apply EqAxiom.bisimulation_is_eq. pstep. unfold throw.
  constructor. intros. inversion v.
Qed.

Lemma throw_bind {E R1 R2} `{exceptE unit -< E} (k : R1 -> itree E R2) :
  x <- throw tt;; k x = throw tt.
Proof.
  unfold throw. rewritebisim @bind_vis. apply throw_vis.
Qed.


(** * Stuttering bisimulation *)
Section bisim.
  Context {config specConfig : Type}.

  Inductive sbuter_gen {R1 R2 : Type} (sbuter : perm -> (R1 -> R2 -> Perms) -> itree (sceE config) R1 -> config -> itree (sceE specConfig) R2 -> specConfig -> Prop)
            (p : perm) (Q : R1 -> R2 -> Perms) :
    itree (sceE config) R1 -> config -> itree (sceE specConfig) R2 -> specConfig -> Prop :=
  | sbuter_gen_ret r1 c1 r2 c2 :
    pre p (c1, c2) ->
    inv p (c1, c2) ->
    p ∈ Q r1 r2 ->
    sbuter_gen sbuter p Q (Ret r1) c1 (Ret r2) c2
  | sbuter_gen_err t1 c1 c2 :
    sbuter_gen sbuter p Q t1 c1 (throw tt) c2
  | sbuter_gen_sep_step t1 c1 t2 c2 p' :
    pre p (c1, c2) ->
    inv p (c1, c2) ->
    sep_step p p' ->
    sbuter_gen sbuter p' Q t1 c1 t2 c2 ->
    sbuter_gen sbuter p Q t1 c1 t2 c2

  | sbuter_gen_tau_L t1 c1 t2 c2 :
    pre p (c1, c2) ->
    inv p (c1, c2) ->
    sbuter_gen sbuter p Q t1 c1 t2 c2 ->
    sbuter_gen sbuter p Q (Tau t1) c1 t2 c2
  | sbuter_gen_tau_R t1 c1 t2 c2 :
    pre p (c1, c2) ->
    inv p (c1, c2) ->
    sbuter_gen sbuter p Q t1 c1 t2 c2 ->
    sbuter_gen sbuter p Q t1 c1 (Tau t2) c2
  | sbuter_gen_tau t1 c1 t2 c2 :
    pre p (c1, c2) ->
    inv p (c1, c2) ->
    sbuter p Q t1 c1 t2 c2 ->
    sbuter_gen sbuter p Q (Tau t1) c1 (Tau t2) c2

  (* NOTE: even though sbuter_gen_sep_step already allows sep_step to change the
  input permission, we include sep_step on the modify steps in case the
  precondition of the input permission holds before but not after the modify *)
  | sbuter_gen_modify_L f k c1 t2 c2 p' :
    pre p (c1, c2) ->
    inv p (c1, c2) ->
    guar p (c1, c2) (f c1, c2) ->
    sep_step p p' ->
    sbuter_gen sbuter p' Q (k c1) (f c1) t2 c2 ->
    sbuter_gen sbuter p Q (vis (Modify f) k) c1 t2 c2
  | sbuter_gen_modify_R t1 c1 f k c2 p' :
    pre p (c1, c2) ->
    inv p (c1, c2) ->
    guar p (c1, c2) (c1, f c2) ->
    sep_step p p' ->
    sbuter_gen sbuter p' Q t1 c1 (k c2) (f c2) ->
    sbuter_gen sbuter p Q t1 c1 (vis (Modify f) k) c2
  | sbuter_gen_modify f1 k1 c1 f2 k2 c2 p' :
    pre p (c1, c2) ->
    inv p (c1, c2) ->
    guar p (c1, c2) (f1 c1, f2 c2) ->
    sep_step p p' ->
    sbuter p' Q (k1 c1) (f1 c1) (k2 c2) (f2 c2) ->
    sbuter_gen sbuter p Q (vis (Modify f1) k1) c1 (vis (Modify f2) k2) c2

  | sbuter_gen_choice_L k c1 t2 c2 :
    pre p (c1, c2) ->
    inv p (c1, c2) ->
    (forall b, sbuter_gen sbuter p Q (k b) c1 t2 c2) ->
    sbuter_gen sbuter p Q (vis Or k) c1 t2 c2
  | sbuter_gen_choice_R t1 c1 k c2 :
    pre p (c1, c2) ->
    inv p (c1, c2) ->
    (forall b, sbuter_gen sbuter p Q t1 c1 (k b) c2) ->
    sbuter_gen sbuter p Q t1 c1 (vis Or k) c2
  | sbuter_gen_choice k1 c1 k2 c2 :
    pre p (c1, c2) ->
    inv p (c1, c2) ->
    (forall b1, exists b2, sbuter p Q (k1 b1) c1 (k2 b2) c2) ->
    (forall b2, exists b1, sbuter p Q (k1 b1) c1 (k2 b2) c2) ->
    sbuter_gen sbuter p Q (vis Or k1) c1 (vis Or k2) c2
  .

  Lemma sbuter_gen_mon {R1 R2} : monotone6 (@sbuter_gen R1 R2).
  Proof.
    repeat intro. induction IN; subst; try solve [econstructor; eauto]; auto.
    econstructor 12; eauto; intros.
    - destruct (H1 b1). eexists; eauto.
    - destruct (H2 b2). eexists; eauto.
  Qed.
  #[local] Hint Resolve sbuter_gen_mon : paco.

  (* Stuttering Bisimulation Up To Error on the Right *)
  Definition sbuter {R1 R2} := paco6 (@sbuter_gen R1 R2) bot6.

  (* Bisimulation wrt input permission p implies that either the precondition
  and invariant of p hold OR the RHS computation is an error *)
  Lemma sbuter_gen_pre_inv {R1 R2} r p (Q : R1 -> R2 -> Perms) t s c1 c2 :
    sbuter_gen r p Q t c1 s c2 ->
    s = throw tt \/ (pre p (c1, c2) /\ inv p (c1, c2)).
  Proof.
    inversion 1; auto.
  Qed.

  (* Invert an sbuter with a Tau on the left to remove the Tau *)
  Lemma sbuter_tau_inv_l {R1 R2} p Q t c1 s c2 :
    @sbuter R1 R2 p Q (Tau t) c1 s c2 -> sbuter p Q t c1 s c2.
  Proof.
    intro. pstep. punfold H.
    remember (Tau t) as tau_t.
    induction H; try solve [econstructor; eauto | inversion Heqtau_t ].
    - inversion Heqtau_t; subst. assumption.
    - pclearbot. inversion Heqtau_t; subst. punfold H1.
      apply sbuter_gen_tau_R; assumption.
  Qed.

  (* Invert an sbuter with a Tau on the right to remove the Tau *)
  Lemma sbuter_tau_inv_r {R1 R2} p Q t c1 s c2 :
    @sbuter R1 R2 p Q t c1 (Tau s) c2 -> sbuter p Q t c1 s c2.
  Proof.
    intro. pstep. punfold H.
    remember (Tau s) as tau_s.
    induction H; try solve [econstructor; eauto | inversion Heqtau_s ].
    - inversion Heqtau_s; subst. assumption.
    - pclearbot. inversion Heqtau_s; subst. punfold H1.
      apply sbuter_gen_tau_L; assumption.
  Qed.

  (* The input permission of sbuter can be strenghtened using sep_step, as long
  as the precondition is preserved *)
  Lemma sbuter_sep_step_left {R1 R2} p p' (Q : R1 -> R2 -> Perms) t s c1 c2 :
    sep_step p p' -> pre p (c1,c2) ->
    sbuter p' Q t c1 s c2 -> sbuter p Q t c1 s c2.
  Proof.
    intros. punfold H1. pstep.
    destruct (sbuter_gen_pre_inv _ _ _ _ _ _ _ H1) as [? | [? ?]];
      [ subst; constructor | ].
    eapply sbuter_gen_sep_step; eauto.
    eapply sep_step_inv; eassumption.
  Qed.

  (* The input permission of sbuter can be strenghtened using entailment, as long
  as the precondition is preserved *)
  Lemma sbuter_entails_left {R1 R2} p p' (Q : R1 -> R2 -> Perms) t s c1 c2 :
    p ⊢ p' -> pre p (c1,c2) -> sbuter p' Q t c1 s c2 -> sbuter p Q t c1 s c2.
  Proof.
    intros. eapply sbuter_sep_step_left; try apply entails_perm_sep_step; eassumption.
  Qed.

  (* The output permission set of sbuter can be weakened to a larger set *)
  Lemma sbuter_lte {R1 R2} p Q Q' (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) c1 c2 :
    sbuter p Q t c1 s c2 -> (forall r1 r2, Q r1 r2 ⊒ Q' r1 r2) -> sbuter p Q' t c1 s c2.
  Proof.
    revert p Q Q' t s c1 c2. pcofix CIH. intros p Q Q' t s c1 c2 Htyping Hlte.
    punfold Htyping. pstep.
    induction Htyping; pclearbot; try solve [econstructor; eauto].
    - constructor; eauto. apply Hlte. auto.
    - econstructor 12; eauto; intros.
      + destruct (H1 b1). eexists. right. eapply CIH; eauto. pclearbot. apply H3.
      + destruct (H2 b2). eexists. right. eapply CIH; eauto. pclearbot. apply H3.
  Qed.

  (* sbuter respects itree equality *)
  Lemma sbuter_eqit {R1 R2} p Q (t1 t2 : itree (sceE config) R1)
    (s1 s2 : itree (sceE specConfig) R2) c1 c2 :
    eq_itree eq t1 t2 -> eq_itree eq s1 s2 ->
    sbuter p Q t1 c1 s1 c2 -> sbuter p Q t2 c1 s2 c2.
  Proof.
    revert p Q t1 t2 s1 s2 c1 c2. pcofix CIH.
    intros p Q t1 t2 s1 s2 c1 c2 Heq_t Heq_s Htyping. revert t2 s2 Heq_t Heq_s.
    punfold Htyping. induction Htyping; intros.
    - symmetry in Heq_t; symmetry in Heq_s.
      apply eqitree_inv_Ret_r in Heq_t; apply eqitree_inv_Ret_r in Heq_s.
      rewrite (itree_eta_ t2); rewrite (itree_eta_ s2).
      rewrite Heq_t; rewrite Heq_s.
      pstep. eapply sbuter_gen_ret; eassumption.
    - symmetry in Heq_s. apply eqitree_inv_Vis_r in Heq_s.
      destruct Heq_s as [k' [? ?]]. rewrite (itree_eta_ s2). rewrite H.
      rewrite throw_vis. pstep. constructor.
    - pstep. eapply sbuter_gen_sep_step; try eassumption.
      specialize (IHHtyping _ _ Heq_t Heq_s). pstep_reverse.
    - symmetry in Heq_t. apply eqitree_inv_Tau_r in Heq_t.
      destruct Heq_t as [t3 [? ?]]. symmetry in H2.
      rewrite (itree_eta_ t0). rewrite H1.
      pstep. apply sbuter_gen_tau_L; try assumption. pstep_reverse.
    - symmetry in Heq_s; apply eqitree_inv_Tau_r in Heq_s.
      destruct Heq_s as [t3 [? ?]]. symmetry in H2.
      rewrite (itree_eta_ s2). rewrite H1.
      pstep. apply sbuter_gen_tau_R; try assumption. pstep_reverse.
    - pclearbot.
      symmetry in Heq_t; apply eqitree_inv_Tau_r in Heq_t.
      destruct Heq_t as [t3 [? ?]]. symmetry in H3.
      symmetry in Heq_s; apply eqitree_inv_Tau_r in Heq_s.
      destruct Heq_s as [s3 [? ?]]. symmetry in H5.
      rewrite (itree_eta_ t0); rewrite H2.
      rewrite (itree_eta_ s2); rewrite H4.
      pstep. apply sbuter_gen_tau; try assumption. right.
      eapply CIH; eassumption.
    - symmetry in Heq_t. apply eqitree_inv_Vis_r in Heq_t.
      destruct Heq_t as [k' [? ?]]. symmetry in H4.
      rewrite (itree_eta_ t0). rewrite H3.
      pstep. eapply sbuter_gen_modify_L; try eassumption. pstep_reverse.
    - symmetry in Heq_s. apply eqitree_inv_Vis_r in Heq_s.
      destruct Heq_s as [k' [? ?]]. symmetry in H4.
      rewrite (itree_eta_ s2). rewrite H3.
      pstep. eapply sbuter_gen_modify_R; try eassumption. pstep_reverse.
    - pclearbot.
      symmetry in Heq_t. apply eqitree_inv_Vis_r in Heq_t.
      destruct Heq_t as [k1' [? ?]]. symmetry in H5.
      symmetry in Heq_s. apply eqitree_inv_Vis_r in Heq_s.
      destruct Heq_s as [k2' [? ?]]. symmetry in H7.
      rewrite (itree_eta_ t2). rewrite H4.
      rewrite (itree_eta_ s2). rewrite H6.
      pstep. eapply sbuter_gen_modify; try eassumption.
      right. eapply CIH; eauto.
    - symmetry in Heq_t. apply eqitree_inv_Vis_r in Heq_t.
      destruct Heq_t as [k' [? ?]]. symmetry in H4.
      rewrite (itree_eta_ t0). rewrite H3.
      pstep. eapply sbuter_gen_choice_L; try eassumption. intros.
      pstep_reverse.
    - symmetry in Heq_s. apply eqitree_inv_Vis_r in Heq_s.
      destruct Heq_s as [k' [? ?]]. symmetry in H4.
      rewrite (itree_eta_ s2). rewrite H3.
      pstep. eapply sbuter_gen_choice_R; try eassumption. intros. pstep_reverse.
    - pclearbot.
      symmetry in Heq_t. apply eqitree_inv_Vis_r in Heq_t.
      destruct Heq_t as [k1' [? ?]]. symmetry in H4.
      symmetry in Heq_s. apply eqitree_inv_Vis_r in Heq_s.
      destruct Heq_s as [k2' [? ?]]. symmetry in H6.
      rewrite (itree_eta_ t2). rewrite H3.
      rewrite (itree_eta_ s2). rewrite H5.
      pstep. eapply sbuter_gen_choice; try eassumption; intros.
      + destruct (H1 b1) as [b2' ?]. pclearbot. eexists. right.
        eapply CIH; eauto.
      + destruct (H2 b2) as [b1' ?]. pclearbot. eexists. right.
        eapply CIH; eauto.
  Qed.

  (* sbuter respects eutt equality in the implementation itree *)
  (* FIXME: this should hold, but is complicated to prove
  Lemma sbuter_eutt_impl {R1 R2} p Q (t1 t2 : itree (sceE config) R1)
    (s : itree (sceE specConfig) R2) c1 c2 :
    eutt eq t1 t2 -> sbuter p Q t1 c1 s c2 -> sbuter p Q t2 c1 s c2.
  Proof.
   *)

  (* The output permission set of sbuter can be weakened by entailment *)
  Lemma sbuter_entails_right {R1 R2} p Q Q' (t : itree (sceE config) R1)
    (s : itree (sceE specConfig) R2) c1 c2 :
    sbuter p Q t c1 s c2 -> (forall r1 r2, Q r1 r2 ⊨ Q' r1 r2) -> sbuter p Q' t c1 s c2.
  Proof.
    revert p Q Q' t s c1 c2. pcofix CIH. intros p Q Q' t s c1 c2 Htyping Hent.
    punfold Htyping. pstep.
    induction Htyping; pclearbot; try solve [econstructor; eauto].
    - destruct (Hent r1 r2 p H1) as [q [? ?]].
      apply (sbuter_gen_sep_step _ _ _ _ _ _ _ q);
        [ assumption | assumption | apply entails_perm_sep_step; assumption | ].
      destruct (entails_pred p q H3 (c1,c2)); [ split; assumption | ].
      constructor; auto.
    - econstructor 12; eauto; intros.
      + destruct (H1 b1). eexists. right. eapply CIH; eauto. pclearbot. apply H3.
      + destruct (H2 b2). eexists. right. eapply CIH; eauto. pclearbot. apply H3.
  Qed.


  (** * Typing *)
  Definition typing {R1 R2} P Q (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) :=
    forall p c1 c2, p ∈ P -> pre p (c1, c2) -> inv p (c1, c2) -> sbuter p Q t c1 s c2.

  Lemma typing_lte {R1 R2} P P' (Q Q' : R1 -> R2 -> Perms) t s :
    typing P Q t s -> P' ⊒ P -> (forall r1 r2, Q r1 r2 ⊒ Q' r1 r2) ->
    typing P' Q' t s.
  Proof.
    repeat intro.
    eapply sbuter_lte; eauto.
  Qed.

  Lemma typing_entails {R1 R2} P P' (Q Q' : R1 -> R2 -> Perms) t s :
    typing P Q t s -> P' ⊨ P -> (forall r1 r2, Q r1 r2 ⊨ Q' r1 r2) ->
    typing P' Q' t s.
  Proof.
    repeat intro. destruct (H0 p H2) as [q [? ?]].
    eapply sbuter_entails_left; eauto.
    eapply sbuter_entails_right; eauto.
    destruct (entails_pred _ _ H6 (c1,c2)); [ split; assumption | ].
    apply H; assumption.
  Qed.


  Lemma typing_ret {R1 R2} P Q (r1 : R1) (r2 : R2) :
    P ⊨ (Q r1 r2) -> typing P Q (Ret r1) (Ret r2).
  Proof.
    repeat intro. destruct (H p H0) as [q [? ?]]. pstep.
    apply (sbuter_gen_sep_step _ _ _ _ _ _ _ q); try assumption;
      try (apply entails_perm_sep_step; assumption).
    destruct (entails_pred p q H4 (c1,c2)); [ split; assumption | ].
    apply sbuter_gen_ret; assumption.
  Qed.

  Lemma rewrite_spin {E R} : (ITree.spin : itree E R) = Tau (ITree.spin).
  Proof.
    intros. apply EqAxiom.bisimulation_is_eq.
    ginit. gcofix CIH. gstep. unfold ITree.spin. constructor.
    apply Reflexive_eqit_gen_eq.
  Qed.


  Lemma typing_spin {R1 R2} P Q :
    typing P Q (ITree.spin : itree (sceE config) R1) (ITree.spin : itree (sceE specConfig) R2).
  Proof.
    repeat intro. pcofix CIH. pstep.
    rewrite (@rewrite_spin _ R1). rewrite (@rewrite_spin _ R2).
    econstructor 6; eauto.
  Qed.

  Lemma typing_top {R1 R2} Q (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) :
    typing top_Perms Q t s.
  Proof.
    repeat intro. inversion H.
  Qed.

  Lemma sbuter_bottom {R1 R2} p Q (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) c1 c2:
    sbuter p Q t c1 s c2 -> sbuter p (fun _ _ => bottom_Perms) t c1 s c2.
  Proof.
    revert p Q t s c1 c2. pcofix CIH. intros. pstep. punfold H0.
    induction H0; pclearbot; try solve [econstructor; simpl; eauto].
    econstructor 12; eauto; intros.
    - destruct (H1 b1). eexists. right. eapply CIH; pclearbot; apply H3.
    - destruct (H2 b2). eexists. right. eapply CIH; pclearbot; apply H3.
  Qed.

  Lemma typing_bottom {R1 R2} P Q (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) :
    typing P Q t s -> typing P (fun _ _ => bottom_Perms) t s.
  Proof.
    repeat intro. eapply sbuter_bottom; eauto.
  Qed.


  (* Reading the state on the left is bisimilar to the trivial computation on
  the right relative to any input permission set P with output permission set
  adding a precondition to P that the state equals the returned value *)
  Lemma typing_read_L P :
    typing P (fun x _ => add_poss_pre (fun c12 => fst c12 = x) P) read (Ret tt).
  Proof.
    repeat intro. pstep.
    apply (sbuter_gen_modify_L _ _ _ _ _ _ _ _ (add_pre_perm (fun c12 => fst c12 = c1) p));
      [ eassumption | eassumption | reflexivity
      | apply sep_step_rg; intros; assumption | ].
    apply sbuter_gen_ret.
    - split; [ assumption | ]. exists (c1,c2). split; [ assumption | ].
      split; reflexivity.
    - assumption.
    - eexists. split; [ | reflexivity ]. split.
      + eexists. split; [ | reflexivity ].
        exists p; split; [ assumption | reflexivity ].
      + exists (c1, c2). split; split; try assumption; try reflexivity.
        exists (c1, c2). split; [ assumption | split; reflexivity ].
  Qed.

  (* Apply a function to the first element of a pair *)
  Definition map_pair_L {A B} (f : A -> A) (p : A * B) : A * B :=
    (f (fst p), snd p).

  (* Updating the state on the left is bisimilar to the trivial computation on
  the right relative to any input permission set P containing the update in all
  of its guarantees with output permission set rewind f P P *)
  Lemma typing_update_L f P :
    (forall p c12, p ∈ P -> inv p c12 -> pre p c12 -> guar p c12 (map_pair_L f c12)) ->
    typing P (fun _ _ => rewind (map_pair_L f) P) (update f) (Ret tt).
  Proof.
    repeat intro; pstep. unfold update, trigger. rewritebisim @bind_vis.
    apply (sbuter_gen_modify_L _ _ _ _ _ _ _ _ (rewind_perm (map_pair_L f) p p));
      [ eassumption | eassumption | apply H; assumption
      | apply sep_step_rg; intros; assumption | ].
    rewritebisim @bind_ret_l.
    apply sbuter_gen_ret.
    - exists (f c1,c2).
      split; [ eapply inv_guar; [ apply (H p (c1,c2)) | ]; assumption | ].
      split; [ | reflexivity ].
      exists (c1,c2). split; [ reflexivity | ].
      split; assumption.
    - eapply inv_guar; [ apply (H p (c1,c2)) | ]; assumption.
    - eexists; split; [ | reflexivity ].
      exists p. split; [ assumption | reflexivity ].
  Qed.

  Lemma sbuter_bind {R1 R2 S1 S2} (p : perm) (Q : R1 -> S1 -> Perms) (R : R2 -> S2 -> Perms)
        (t1 : itree (sceE config) R1) (t2 : R1 -> itree (sceE config) R2)
        (s1 : itree (sceE specConfig) S1) (s2 : S1 -> itree (sceE specConfig) S2)
        c1 c2 r :
    pre p (c1, c2) ->
    inv p (c1, c2) ->
    sbuter p Q t1 c1 s1 c2 ->
    (forall r1 r2 p c1 c2, p ∈ (Q r1 r2) ->
                      pre p (c1, c2) ->
                      inv p (c1, c2) ->
                      paco6 sbuter_gen r p R (t2 r1) c1 (s2 r2) c2) ->
    paco6 sbuter_gen r p R (x <- t1 ;; t2 x) c1 (x <- s1 ;; s2 x) c2.
  Proof.
    revert p Q R t1 t2 s1 s2 c1 c2. pcofix CIH.
    intros p Q R t1 t2 s1 s2 c1 c2 Hpre Hinv Htyping1 Htyping2.
    punfold Htyping1. induction Htyping1.
    - do 2 rewritebisim @bind_ret_l. specialize (Htyping2 _ _ _ c1 c2 H1 H H0).
      eapply paco6_mon; eauto.
    - Locate throw_bind.
rewrite throw_bind. pstep. constructor.
    - apply sbuter_gen_pre_inv in Htyping1.
      destruct Htyping1 as [? | [? ?]];
        [ subst; rewrite throw_bind; pstep; constructor | ].
      specialize (IHHtyping1 H2 H3 Htyping2). punfold IHHtyping1.
      pstep. unshelve eapply sbuter_gen_sep_step; assumption.
    - rewritebisim @bind_tau.
      specialize (IHHtyping1 Hpre Hinv Htyping2). punfold IHHtyping1.
      pstep. constructor; auto.
    - rewritebisim @bind_tau.
      specialize (IHHtyping1 Hpre Hinv Htyping2). punfold IHHtyping1.
      pstep. constructor; auto.
    - do 2 rewritebisim @bind_tau. pclearbot.
      pstep. constructor 6; auto. right. eapply CIH; eauto.
    - rewritebisim @bind_vis. apply sbuter_gen_pre_inv in Htyping1.
      destruct Htyping1 as [? | [? ?]]; subst.
      + rewrite throw_bind. pstep. constructor.
      + specialize (IHHtyping1 H3 H4 Htyping2). punfold IHHtyping1. pstep.
        eapply sbuter_gen_modify_L; eauto.
    - rewritebisim @bind_vis. apply sbuter_gen_pre_inv in Htyping1.
      destruct Htyping1 as [? | [? ?]]; subst.
      + pstep. eapply sbuter_gen_modify_R; eauto. rewrite H3.
        rewrite throw_bind. constructor.
      + specialize (IHHtyping1 H3 H4 Htyping2). punfold IHHtyping1. pstep.
        eapply sbuter_gen_modify_R; eauto.
    - do 2 rewritebisim @bind_vis. pclearbot.
      pose proof H3. punfold H3.
      pstep. econstructor 9; eauto.
      destruct (sbuter_gen_pre_inv _ _ _ _ _ _ _ H3) as [? | [? ?]]; eauto.
      rewrite H5. rewrite throw_bind. left. pstep. constructor.
    - rewritebisim @bind_vis. pstep.
      eapply sbuter_gen_choice_L; eauto. intros.
      destruct (sbuter_gen_pre_inv _ _ _ _ _ _ _ (H1 b)) as [? | [? ?]].
      + rewrite H3. rewrite throw_bind. constructor.
      + specialize (H2 b H3 H4 Htyping2). punfold H2.
    - rewritebisim @bind_vis. pstep.
      eapply sbuter_gen_choice_R; eauto. intros.
      destruct (sbuter_gen_pre_inv _ _ _ _ _ _ _ (H1 b)) as [? | [? ?]].
      + rewrite H3. rewrite throw_bind. constructor.
      + specialize (H2 b H3 H4 Htyping2). punfold H2.
    - do 2 rewritebisim @bind_vis. pclearbot. pstep.
      econstructor 12; eauto; intros.
      + specialize (H1 b1). destruct H1. pclearbot.
        punfold H1. destruct (sbuter_gen_pre_inv _ _ _ _ _ _ _ H1) as [? | [? ?]].
        * exists x. left. pstep. rewrite H3. rewrite throw_bind. econstructor; eauto.
        * eexists. right. eapply CIH; eauto. pstep; eauto.
      + specialize (H2 b2). destruct H2. pclearbot.
        punfold H2. destruct (sbuter_gen_pre_inv _ _ _ _ _ _ _ H2) as [? | [? ?]].
        * exists x. left. pstep. rewrite H3. rewrite throw_bind. econstructor; eauto.
        * eexists. right. eapply CIH; eauto. pstep; eauto.
  Qed.

  Lemma typing_bind {R1 R2 S1 S2} (P : Perms) (Q : R1 -> S1 -> Perms) (R : R2 -> S2 -> Perms)
        (t1 : itree (sceE config) R1) (t2 : R1 -> itree (sceE config) R2)
        (s1 : itree (sceE specConfig) S1) (s2 : S1 -> itree (sceE specConfig) S2) :
    typing P Q t1 s1 ->
    (forall r1 r2, typing (Q r1 r2) R (t2 r1) (s2 r2)) ->
    typing P R (x <- t1 ;; t2 x) (x <- s1 ;; s2 x).
  Proof.
    repeat intro.
    eapply sbuter_bind; eauto.
  Qed.


  Lemma sbuter_frame {R1 R2} p r Q R (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) c1 c2:
    pre r (c1, c2) ->
    inv r (c1, c2) ->
    r ∈ R -> p ⊥ r ->
    sbuter p Q t c1 s c2 ->
    sbuter (p ** r) (fun r1 r2 => Q r1 r2 * R) t c1 s c2.
  Proof.
    revert p r Q R t s c1 c2. pcofix CIH. rename r into r0.
    intros p r Q R t s c1 c2 Hpre Hinv Hr Hsep Hsbuter. pstep. punfold Hsbuter.
    revert r Hr Hsep Hpre Hinv.
    induction Hsbuter; intros; pclearbot; try solve [econstructor; eauto].
    - constructor.
      + split; assumption.
      + split; [ | split ]; assumption.
      + do 2 eexists. split; [| split; [| split]]; eauto.
      reflexivity.
    - eapply sbuter_gen_sep_step.
      + split; assumption.
      + split; [ | split ]; assumption.
      + apply sep_step_sep_conj_l; eassumption.
      + apply IHHsbuter; try assumption.
        eapply sep_step_sep; eassumption.
    - apply sbuter_gen_pre_inv in Hsbuter.
      destruct Hsbuter as [? | [? ?]]; [subst; constructor |].
      constructor.
      + split; assumption.
      + split; [ | split ]; assumption.
      + apply IHHsbuter; assumption.
    - apply sbuter_gen_pre_inv in Hsbuter.
      constructor.
      + split; assumption.
      + split; [ | split ]; assumption.
      + destruct Hsbuter; [ subst; constructor | destruct H1 ].
        apply IHHsbuter; assumption.
    - apply sbuter_gen_tau.
      + split; assumption.
      + split; [ | split ]; assumption.
      + right. apply CIH; assumption.
    - apply sbuter_gen_pre_inv in Hsbuter.
      destruct Hsbuter as [? | [? ?]]; [subst; constructor |].
      eapply sbuter_gen_modify_L.
      + split; assumption.
      + split; [ | split ]; assumption.
      + apply t_step; left; assumption.
      + apply sep_step_sep_conj_l; eassumption.
      + apply IHHsbuter; try assumption.
        * eapply sep_step_sep; eassumption.
        * eapply pre_respects; try eassumption.
          eapply sep_r; eassumption.
        * eapply inv_rely; try eassumption.
          eapply sep_r; eassumption.
    - apply sbuter_gen_pre_inv in Hsbuter. eapply sbuter_gen_modify_R.
      + split; assumption.
      + split; [ | split ]; assumption.
      + apply t_step; left; assumption.
      + apply sep_step_sep_conj_l; eassumption.
      + destruct Hsbuter; [ rewrite H3; constructor | destruct H3 ].
        apply IHHsbuter; try assumption.
        * eapply sep_step_sep; eassumption.
        * eapply pre_respects; try eassumption.
          eapply sep_r; eassumption.
        * eapply inv_rely; try eassumption.
          eapply sep_r; eassumption.
    - econstructor 9.
      + split; assumption.
      + split; [ | split ]; assumption.
      + apply t_step; left; assumption.
      + apply sep_step_sep_conj_l; eassumption.
      + right. apply CIH.
        5: apply H3.
        4: {
          apply H2. apply Hsep.
        }
        * respects. apply Hsep; auto.
        * apply Hsep in H1; auto. eapply inv_rely; eauto.
        * auto.
    - eapply sbuter_gen_choice_L.
      + split; assumption.
      + split; [ | split ]; assumption.
      + intros. eapply H2; auto.
    - eapply sbuter_gen_choice_R.
      + split; assumption.
      + split; [ | split ]; assumption.
      + intros. eapply H2; auto.
    - eapply sbuter_gen_choice.
      + split; assumption.
      + split; [ | split ]; assumption.
      + intros. specialize (H1 b1). destruct H1 as (b2 & H1). pclearbot. exists b2.
        pose proof H1 as Hsbuter.
        punfold Hsbuter.
      + intros. specialize (H2 b2). destruct H2 as (b1 & H2). pclearbot. exists b1.
        pose proof H2 as Hsbuter.
        punfold Hsbuter.
  Qed.


  (* The input permission of sbuter can be strengthened to a stronger one. This
  falls out as a consequence of the frame rule *)
  Lemma sbuter_lte_left {R1 R2} p p' Q (t : itree (sceE config) R1)
    (s : itree (sceE specConfig) R2) c1 c2 :
    pre p' (c1, c2) -> inv p' (c1, c2) ->
    sbuter p Q t c1 s c2 -> p <= p' -> sbuter p' Q t c1 s c2.
  Proof.
    intros.
    pose proof (sep_step_lte p p p' H2 (reflexivity _)) as H3.
    rewrite sep_conj_perm_commut in H3.
    eapply sbuter_sep_step_left; [ apply H3 | eassumption | ].
    eapply sbuter_lte;
      [ eapply (sbuter_frame _ _ _
                  (singleton_Perms (invperm (inv p')))) | ]; try eassumption.
    - apply I.
    - simpl; reflexivity.
    - symmetry; apply separate_bigger_invperm; assumption.
    - intros; apply lte_l_sep_conj_Perms.
  Qed.

  (* The frame rule for the typing judgment *)
  Lemma typing_frame {R1 R2} P Q R (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2):
    typing P Q t s ->
    typing (P * R) (fun r1 r2 => Q r1 r2 * R) t s.
  Proof.
    intros Ht p' c1 c2 (p & r & Hp & Hr & Hlte & Hsep) Hpre Hinv.
    eapply sbuter_lte_left; try eassumption.
    apply sbuter_frame; try assumption.
    - eapply pre_inc; try eassumption.
      etransitivity; [ apply lte_r_sep_conj_perm | eassumption ].
    - eapply inv_inc; try eassumption.
      etransitivity; [ apply lte_r_sep_conj_perm | eassumption ].
    - apply Ht; try assumption.
      + eapply pre_inc; try eassumption.
        etransitivity; [ apply lte_l_sep_conj_perm | eassumption ].
      + eapply inv_inc; try eassumption.
        etransitivity; [ apply lte_l_sep_conj_perm | eassumption ].
  Qed.

  (* Typing is Proper wrt permission set equality *)
  Global Instance Proper_eqit_Perms_typing {R1 R2} :
    Proper (eq_Perms ==>
           (pointwise_relation _ (pointwise_relation _ eq_Perms)) ==>
           eq_itree eq ==> eq_itree eq ==> flip impl) (@typing R1 R2).
  Proof.
    repeat intro.
    eapply sbuter_lte; [ | intros; apply H0 ].
    eapply sbuter_eqit; try (symmetry; eassumption).
    eapply H3; try eassumption. rewrite <- H. assumption.
  Qed.

End bisim.
