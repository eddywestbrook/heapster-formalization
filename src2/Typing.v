(* begin hide *)
From Coq Require Import
     Structures.Equalities
     Classes.Morphisms
     Classes.RelationClasses
     Relations.Relation_Operators
     Relations.Operators_Properties
     ProofIrrelevance.

From Heapster2 Require Import
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

  | sbuter_gen_choice_L k c1 t2 c2 p' :
    pre p (c1, c2) ->
    inv p (c1, c2) ->
    sep_step p p' ->
    (forall b, sbuter_gen sbuter p' Q (k b) c1 t2 c2) ->
    sbuter_gen sbuter p Q (vis Or k) c1 t2 c2
  | sbuter_gen_choice_R t1 c1 k c2 p' :
    pre p (c1, c2) ->
    inv p (c1, c2) ->
    sep_step p p' ->
    (forall b, sbuter_gen sbuter p' Q t1 c1 (k b) c2) ->
    sbuter_gen sbuter p Q t1 c1 (vis Or k) c2
  | sbuter_gen_choice k1 c1 k2 c2 p' :
    pre p (c1, c2) ->
    inv p (c1, c2) ->
    sep_step p p' ->
    (forall b1, exists b2, sbuter p' Q (k1 b1) c1 (k2 b2) c2) ->
    (forall b2, exists b1, sbuter p' Q (k1 b1) c1 (k2 b2) c2) ->
    sbuter_gen sbuter p Q (vis Or k1) c1 (vis Or k2) c2
  .

  Lemma sbuter_gen_mon {R1 R2} : monotone6 (@sbuter_gen R1 R2).
  Proof.
    repeat intro. induction IN; subst; try solve [econstructor; eauto]; auto.
    econstructor 11; eauto; intros.
    - destruct (H2 b1). eexists; eauto.
    - destruct (H3 b2). eexists; eauto.
  Qed.
  #[local] Hint Resolve sbuter_gen_mon : paco.

  Definition sbuter {R1 R2} := paco6 (@sbuter_gen R1 R2) bot6.

  Lemma sbuter_gen_pre_inv {R1 R2} r p (Q : R1 -> R2 -> Perms) t s c1 c2 :
    sbuter_gen r p Q t c1 s c2 ->
    s = throw tt \/ (pre p (c1, c2) /\ inv p (c1, c2)).
  Proof.
    inversion 1; auto.
  Qed.

  Lemma sbuter_lte {R1 R2} p Q Q' (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) c1 c2 :
    sbuter p Q t c1 s c2 -> (forall r1 r2, Q r1 r2 ⊨ Q' r1 r2) -> sbuter p Q' t c1 s c2.
  Proof.
    revert p Q Q' t s c1 c2. pcofix CIH. intros p Q Q' t s c1 c2 Htyping Hlte.
    punfold Htyping. pstep.
    induction Htyping; pclearbot; try solve [econstructor; eauto].
    - constructor; eauto. apply Hlte. auto.
    - econstructor 11; eauto; intros.
      + destruct (H2 b1). eexists. right. eapply CIH; eauto. pclearbot. apply H4.
      + destruct (H3 b2). eexists. right. eapply CIH; eauto. pclearbot. apply H4.
  Qed.

  Lemma sbuter_lte_left {R1 R2} p p' Q (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) c1 c2 :
    pre p' (c1, c2) -> inv p' (c1, c2) ->
    sbuter p Q t c1 s c2 -> p <= p' -> sbuter p' Q t c1 s c2.
  Proof.
    revert p p' Q t s c1 c2. pcofix CIH. intros p p' Q t s c1 c2 Hpre Hinv Htyping Hlte.
    punfold Htyping. pstep.
    revert p' Hpre Hinv Hlte; induction Htyping; intros;
      pclearbot; try solve [econstructor; eauto].
    - constructor; try assumption. eapply Perms_upwards_closed; eassumption.
    - econstructor; try assumption.
      + eapply guar_inc; eassumption.
      + eapply sep_step_lte; eassumption.
      + apply sbuter_gen_pre_inv in Htyping.
        destruct Htyping; [ subst; econstructor | destruct H3 ].
        apply IHHtyping.
        * split; [ constructor | assumption ].
        * split; [ | split ].
          -- eapply (inv_guar p'0); [ | eassumption ].
             eapply guar_inc; eassumption.
          -- assumption.
          -- symmetry; eapply sep_step_sep; [ eassumption | ].
             symmetry; eapply separate_bigger_invperm. assumption.
        * apply lte_r_sep_conj_perm.
    - econstructor; try assumption.
      + eapply guar_inc; eassumption.
      + eapply sep_step_lte; eassumption.
      + apply sbuter_gen_pre_inv in Htyping.
        destruct Htyping; [ rewrite H3; econstructor | destruct H3 ].
        apply IHHtyping.
        * split; [ constructor | assumption ].
        * split; [ | split ].
          -- eapply (inv_guar p'0); [ | eassumption ].
             eapply guar_inc; eassumption.
          -- assumption.
          -- symmetry; eapply sep_step_sep; [ eassumption | ].
             symmetry; eapply separate_bigger_invperm. assumption.
        * apply lte_r_sep_conj_perm.
  Admitted.

  (*
  Lemma bisim_spred_lte {R1 R2} (spred spred' : config * specConfig -> Prop) p Q
        (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2)
        c1 c2 (Hspred': forall x, spred' x -> spred x) :
    bisim spred' (restrict _ _ _ Hspred' p) Q t c1 s c2 ->
    spred' (c1, c2) ->
    bisim spred
          p
          Q
          (* (fun spred'' Hspred'' r1 r2 => Restrict _ _ _ Hspred'' (Restrict _ _ _ Hspred' (Q r1 r2))) *)
                                                 (* Q spred'' (fun x Hx => (Hspred' x (Hspred'' x Hx)))) *)
          t c1 s c2.
  Proof.
    (* Set Printing All. *)
    revert spred p Q t s c1 c2 spred' Hspred'. pcofix CIH.
    intros spred p Q t s c1 c2 spred' Hspred' Hbisim Hc1c2.
    punfold Hbisim. pstep.
    remember (restrict _ _ _ _ p).
    revert spred p Hspred' Heqp0.
    revert Hc1c2 CIH.
    induction Hbisim; intros; subst.
    - econstructor 1. Unshelve. 3: auto.
      + cbn. erewrite (proof_irrelevance _ (Hspred' (c1, c2) _)). apply H.
      + eapply Perms_upwards_closed1; eauto. unfold hlte_perm1. reflexivity.
    - constructor 2.
    - econstructor 3. apply H.
      eapply IHHbisim; eauto.
      (* erewrite (proof_irrelevance _ (Hspred' (c1, c2) _)). apply H. *)
    - econstructor 4. apply H.
      eapply IHHbisim; eauto.
    - econstructor 5.
      + cbn. apply H.
      + pclearbot. right. eapply CIH; eauto.
    - econstructor 6.
      + clear IHHbisim CIH. apply H.
      + clear IHHbisim CIH. apply H0.
      + clear IHHbisim. cbn. repeat intro. admit.
      + eapply IHHbisim. apply Hf. auto. admit.
    - econstructor 7.
      + clear IHHbisim CIH. apply H.
      + clear IHHbisim CIH. apply H0.
      + clear IHHbisim. cbn. repeat intro. admit.
      + eapply IHHbisim; auto. admit.
    - econstructor 8; eauto.
      + clear CIH. apply H.
      + clear CIH. apply H0.
      + cbn. repeat intro. admit.
      + pclearbot. right. eapply CIH; eauto. admit.
    - econstructor 9; eauto.
    (*   cbn. erewrite (proof_irrelevance _ (Hspred' (c1, c2) _)). apply H. *)
    (* - econstructor 10; eauto. *)
    (*   cbn. erewrite (proof_irrelevance _ (Hspred' (c1, c2) _)). apply H. *)
    (* - econstructor 11; eauto. *)
    (*   + cbn. erewrite (proof_irrelevance _ (Hspred' (c1, c2) _)). apply H. *)
    (*   + intros b. destruct (H0 b). pclearbot. eauto. *)
    (*   + intros b. destruct (H1 b). pclearbot. eauto. *)

    (*     Unshelve. all: auto. *)
  Admitted.
   *)
  (* section variable: the spred lang and the interp function *)
  (** * Typing *)
  Definition typing {R1 R2} P Q (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) :=
    forall p c1 c2, p ∈ P -> pre p (c1, c2) -> inv p (c1, c2) -> sbuter p Q t c1 s c2.

  Lemma typing_lte {R1 R2} P P' Q Q' (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) :
    typing P Q t s ->
    P' ⊨ P ->
    (forall r1 r2, Q r1 r2 ⊨ Q' r1 r2) ->
    typing P' Q' t s.
  Proof.
    repeat intro.
    eapply sbuter_lte; eauto.
  Qed.

  Lemma typing_ret {R1 R2} P Q (r1 : R1) (r2 : R2) :
    P ⊨ (Q r1 r2) -> typing P Q (Ret r1) (Ret r2).
  Proof.
    repeat intro. pstep. econstructor; eauto.
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
    econstructor 5; eauto.
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
    econstructor 11; eauto; intros.
    - destruct (H2 b1). eexists. right. eapply CIH; pclearbot; apply H4.
    - destruct (H3 b2). eexists. right. eapply CIH; pclearbot; apply H4.
  Qed.

  Lemma typing_bottom {R1 R2} P Q (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) :
    typing P Q t s -> typing P (fun _ _ => bottom_Perms) t s.
  Proof.
    repeat intro. eapply sbuter_bottom; eauto.
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
    - rewrite throw_bind. pstep. constructor.
    - rewritebisim @bind_tau.
      specialize (IHHtyping1 Hpre Hinv Htyping2). punfold IHHtyping1.
      pstep. constructor; auto.
    - rewritebisim @bind_tau.
      specialize (IHHtyping1 Hpre Hinv Htyping2). punfold IHHtyping1.
      pstep. constructor; auto.
    - do 2 rewritebisim @bind_tau. pclearbot.
      pstep. constructor 5; auto. right. eapply CIH; eauto.
    - rewritebisim @bind_vis. apply sbuter_gen_pre_inv in Htyping1.
      destruct Htyping1 as [? | [? ?]]; subst.
      + rewrite throw_bind. pstep. constructor.
      + specialize (IHHtyping1 H3 H4 Htyping2). punfold IHHtyping1. pstep. econstructor; eauto.
    - rewritebisim @bind_vis. apply sbuter_gen_pre_inv in Htyping1.
      destruct Htyping1 as [? | [? ?]]; subst.
      + pstep. econstructor; eauto. rewrite H3. rewrite throw_bind. constructor.
      + specialize (IHHtyping1 H3 H4 Htyping2). punfold IHHtyping1. pstep. econstructor; eauto.
    - do 2 rewritebisim @bind_vis. pclearbot.
      pose proof H3. punfold H3.
      pstep. econstructor 8; eauto.
      destruct (sbuter_gen_pre_inv _ _ _ _ _ _ _ H3) as [? | [? ?]]; eauto.
      rewrite H5. rewrite throw_bind. left. pstep. constructor.
    - rewritebisim @bind_vis. pstep. econstructor; eauto. intros.
      destruct (sbuter_gen_pre_inv _ _ _ _ _ _ _ (H2 b)) as [? | [? ?]].
      + rewrite H4. rewrite throw_bind. constructor.
      + specialize (H3 b H4 H5 Htyping2). punfold H3.
    - rewritebisim @bind_vis. pstep. econstructor; eauto. intros.
      destruct (sbuter_gen_pre_inv _ _ _ _ _ _ _ (H2 b)) as [? | [? ?]].
      + rewrite H4. rewrite throw_bind. constructor.
      + specialize (H3 b H4 H5 Htyping2). punfold H3.
    - do 2 rewritebisim @bind_vis. pclearbot. pstep. econstructor 11; eauto; intros.
      + specialize (H2 b1). destruct H2. pclearbot.
        punfold H2. destruct (sbuter_gen_pre_inv _ _ _ _ _ _ _ H2) as [? | [? ?]].
        * exists x. left. pstep. rewrite H4. rewrite throw_bind. econstructor; eauto.
        * eexists. right. eapply CIH; eauto. pstep; eauto.
      + specialize (H3 b2). destruct H3. pclearbot.
        punfold H3. destruct (sbuter_gen_pre_inv _ _ _ _ _ _ _ H3) as [? | [? ?]].
        * exists x. left. pstep. rewrite H4. rewrite throw_bind. econstructor; eauto.
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
    - apply sbuter_gen_pre_inv in Hsbuter.
      econstructor.
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
    - econstructor 8.
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
    - econstructor 9.
      + split; assumption.
      + split; [ | split ]; assumption.
      + apply sep_step_sep_conj_l; eassumption.
      + intros. eapply H3; auto. apply H1; auto.
    - econstructor 10.
      + split; assumption.
      + split; [ | split ]; assumption.
      + apply sep_step_sep_conj_l; eassumption.
      + intros. eapply H3; auto. apply H1; auto.
    - econstructor 11; eauto.
      split; assumption.
      split; [ | split]; assumption.
      2: { intros. specialize (H2 b1). destruct H2 as (b2 & H2). pclearbot. exists b2.
           pose proof H2 as Hsbuter.
           punfold Hsbuter. apply sbuter_gen_pre_inv in Hsbuter.
           destruct Hsbuter; [rewrite H4; left; pstep; constructor |].
           right. eapply CIH. 5: apply H2. all: eauto. apply H1; auto.
      }
      2: { intros. specialize (H3 b2). destruct H3 as (b1 & H3). pclearbot. exists b1.
           pose proof H3 as Hsbuter.
           punfold Hsbuter. apply sbuter_gen_pre_inv in Hsbuter.
           destruct Hsbuter; [rewrite H4; left; pstep; constructor |].
           right. eapply CIH. 5: apply H3. all: eauto. apply H1; auto.
      }
      apply sep_step_sep_conj_l; auto.
  Qed.

  (*
  Lemma sbuter_frame {R1 R2} p r p' Q R (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) c1 c2:
    pre p' (c1, c2) ->
    inv p' (c1, c2) ->
    r ∈ R -> p ⊥ r ->
    p ** r <= p' ->
    sbuter p Q t c1 s c2 ->
    sbuter p' (fun r1 r2 => Q r1 r2 * R) t c1 s c2.
  Proof.
    revert p r p' Q R t s c1 c2. pcofix CIH. rename r into r0.
    intros p r p' Q R t s c1 c2 Hpre Hinv Hr Hsep Hlte Hsbuter. pstep. punfold Hsbuter.
    revert p' Hlte Hpre Hinv. generalize dependent r.
    induction Hsbuter; intros; pclearbot; try solve [econstructor; eauto].
    - constructor; auto. eapply Perms_upwards_closed; eauto.
      do 2 eexists. split; [| split; [| split]]; eauto.
      reflexivity.
    - apply sbuter_gen_pre_inv in Hsbuter.
      destruct Hsbuter as [? | [? ?]]; [subst; constructor |].
      constructor 6 with (p':= p' ** r ** invperm (inv  p'0)); eauto.
      + apply Hlte; auto. constructor. left. auto.
      + rewrite (sep_conj_perm_commut (p' ** r)).
        apply (sep_step_lte _ _ _ Hlte).
        apply sep_step_sep_conj_l; assumption.
      + eapply IHHsbuter; eauto.
        * eapply sep_step_sep; eassumption.
        * apply lte_l_sep_conj_perm.
        *
        {
          split.
          split; auto.
          apply Hlte in Hpre. destruct Hpre as (? & ?). respects.
          eapply inv_inc in Hinv; eauto. destruct Hinv as (? & ? & ?). apply H9; auto.

          auto.

          cbn. auto.
        }
        {
          split; [| split]; auto.
          - split; [| split]; auto. apply Hlte. apply Hinv.
        * apply H1. apply Hlte in Hpre. apply Hpre.
    - econstructor; eauto.
      + apply Hlte. constructor. left. auto.
      + eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; eauto.
        apply Hlte in Hpre. apply Hpre.
      + apply sbuter_gen_pre in Hsbuter. destruct Hsbuter; [rewrite H2; constructor |].
        eapply IHHsbuter; eauto. reflexivity.
        split; [| split]; auto.
        * apply Hlte in Hpre. destruct Hpre as (? & ? & ?). respects.
          apply H5. auto.
        * apply H1. apply Hlte in Hpre. apply Hpre.
    - econstructor 8; eauto.
      3: { pose proof H2 as Hsbuter.
           punfold Hsbuter. apply sbuter_gen_pre in Hsbuter.
           destruct Hsbuter; [rewrite H3; left; pstep; constructor |].
           right. eapply CIH. 4: apply H2. 2: eauto. 2: reflexivity.
           apply Hlte in Hpre. destruct Hpre as (? & ? & ?).
           split; [| split]; auto.
           respects. apply H6. auto.
      }
      + apply Hlte. constructor. left. auto.
      + eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; auto.
        apply Hlte in Hpre. apply Hpre.
    - econstructor; eauto.
      + eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; eauto.
        apply Hlte in Hpre. apply Hpre.
      + intros. specialize (H1 b).
        apply sbuter_gen_pre in H1. destruct H1; [subst; constructor |].
        eapply H2; eauto. reflexivity.
        apply Hlte in Hpre. destruct Hpre as (? & ? & ?).
        split; [| split]; auto.
    - econstructor; eauto.
      + eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; eauto.
        apply Hlte in Hpre. apply Hpre.
      + intros. specialize (H1 b).
        apply sbuter_gen_pre in H1. destruct H1; [rewrite H1; constructor |].
        eapply H2; eauto. reflexivity.
        apply Hlte in Hpre. destruct Hpre as (? & ? & ?).
        split; [| split]; auto.
    - econstructor 11; eauto.
      2: { intros. specialize (H1 b1). destruct H1 as (b2 & H1). pclearbot. exists b2.
           pose proof H1 as Hsbuter.
           punfold Hsbuter. apply sbuter_gen_pre in Hsbuter.
           destruct Hsbuter; [rewrite H3; left; pstep; constructor |].
           right. eapply CIH. 4: apply H1. 2: eauto. 2: reflexivity.
           apply Hlte in Hpre. destruct Hpre as (? & ? & ?).
           split; [| split]; auto.
      }
      2: { intros. specialize (H2 b2). destruct H2 as (b1 & H2). pclearbot. exists b1.
           pose proof H2 as Hsbuter.
           punfold Hsbuter. apply sbuter_gen_pre in Hsbuter.
           destruct Hsbuter; [rewrite H3; left; pstep; constructor |].
           right. eapply CIH. 4: apply H2. 2: eauto. 2: reflexivity.
           apply Hlte in Hpre. destruct Hpre as (? & ? & ?).
           split; [| split]; auto.
      }
      eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; auto.
      apply Hlte in Hpre. apply Hpre.
  Qed.
   *)

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

  (*
  Lemma sbuter_frame' {R1 R2} p r Q R (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) c1 c2:
    pre (p ** r) (c1, c2) ->
    inv (p ** r) (c1, c2) ->
    r ∈ R ->
    sbuter p Q t c1 s c2 ->
    sbuter (p ** r) (fun r1 r2 => Q r1 r2 * R) t c1 s c2.
  Proof.
    revert p r Q R t s c1 c2. pcofix CIH. rename r into r0.
    intros p r Q R t s c1 c2 Hpre Hinv Hr Hsbuter. pstep. punfold Hsbuter.
    revert Hr Hpre Hinv. generalize dependent r.
    induction Hsbuter; intros; pclearbot; try solve [econstructor; eauto].
    - constructor; auto.
      apply sep_conj_Perms_perm; auto. apply Hinv.
    - apply sbuter_gen_pre_inv in Hsbuter. destruct Hsbuter; [subst; constructor |].
      destruct H3.
      econstructor; eauto.
      3: {
        destruct Hinv as (Hinvp & Hinvr & Hsep).
        eapply IHHsbuter; eauto.
        * split; auto.
          eapply pre_respects. apply Hsep; eauto. apply Hpre.
        * split; [| split]; auto.
          2: { apply H2. apply Hsep. }
          eapply inv_rely; eauto. apply Hsep; eauto.
      }
      + constructor. left. auto.
      + apply sep_step_frame; auto. apply Hinv.
    -
  Admitted.


  Lemma sbuter_frame {R1 R2} p r p' Q R (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) c1 c2:
    pre p' (c1, c2) ->
    inv p' (c1, c2) ->
    r ∈ R ->
    p ⊥ r ->
    sep_step p' (p ** r) ->
    sbuter p Q t c1 s c2 ->
    sbuter p' (fun r1 r2 => Q r1 r2 * R) t c1 s c2.
  Proof.
    intros. eapply sbuter_lte'; eauto.
    apply sbuter_frame'; eauto. admit.
  Qed.
   *)


  (*
  (** * [no_errors] *)
  Variant no_errors_gen {R C : Type} no_errors (c : C) : itree (sceE C) R -> Prop :=
  | no_errors_ret : forall r, no_errors_gen no_errors c (Ret r)
  | no_errors_tau : forall t, no_errors c t -> no_errors_gen no_errors c (Tau t)
  | no_errors_modify : forall f k,
      no_errors (f c) (k c) ->
      no_errors_gen no_errors c (vis (Modify f) k)
  | no_errors_choice : forall k,
      (forall b, no_errors c (k b)) ->
      no_errors_gen no_errors c (vis Or k)
  .
  Lemma no_errors_gen_mon {R C} : monotone2 (@no_errors_gen R C).
  Proof.
    repeat intro. inversion IN; subst; try solve [constructor; auto].
  Qed.
  #[local] Hint Resolve no_errors_gen_mon : paco.

  Definition no_errors {R C : Type} :=
    paco2 (@no_errors_gen R C) bot2.

  Lemma sbuter_no_errors {R1 R2} Q (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) p c1 c2 :
    sbuter p Q t c1 s c2 ->
    no_errors c2 s ->
    no_errors c1 t.
  Proof.
    revert Q t s p c1 c2. pcofix CIH. intros Q t s p c1 c2 Htyping Hs. pstep.
    punfold Htyping.
    induction Htyping;
      try solve [constructor; eauto];
      pinversion Hs;
      try (match goal with
           | [H : existT _ _ _ = existT _ _ _ |- _] => apply inj_pair2 in H
           end); subst; eauto;
        try solve [constructor; eauto].
    - subst. apply (H2 true). apply H4.
    - constructor. intros. right. destruct (H1 b). eapply CIH.
      + destruct H3; eauto. inversion b0.
      + inversion Hs. apply inj_pair2 in H5; subst.
        specialize (H6 x). pclearbot. eauto.
  Qed.
*)

  Global Instance Proper_eq_Perms_typing {R1 R2} :
    Proper (eq_Perms ==>
           (pointwise_relation _ (pointwise_relation _ eq_Perms)) ==> eq ==> eq ==> flip impl) (@typing R1 R2).
  Proof.
    repeat intro. subst.
    eapply sbuter_lte.
    - eapply H3; try eassumption. rewrite <- H; assumption.
    - intros; apply H0.
  Qed.
End bisim.
