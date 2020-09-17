From Heapster Require Import
     Permissions
     Config.

From Coq Require Import
     Structures.Equalities
     Ensembles
     Classes.Morphisms
     Classes.RelationClasses
     Relations.Relation_Operators
     Relations.Operators_Properties
     Program.Equality.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITree Require Import
     ITree
     ITreeFacts
     Basics.MonadState
     Basics.MonadProp
     Events.State
     Events.Nondeterminism
     Eq.Eq
     Eq.UpToTaus
     Eq.EqAxiom.

From Paco Require Import
     paco.

Import ITreeNotations.
(* Import CatNotations. *)
(* Import MonadNotation. *)
Open Scope monad_scope.

Lemma bind_ret_r' {E R} (t : itree E R) :
  x <- t;; Ret x = t.
Proof.
  apply bisimulation_is_eq. apply bind_ret_r.
Qed.

Lemma bind_ret_l' {E R1 R2} (r : R1) (k : R1 -> itree E R2) :
  x <- Ret r;; k x = k r.
Proof.
  apply bisimulation_is_eq. apply bind_ret_l.
Qed.

Lemma bind_tau' {E R1 R2} (t : itree E R1) (k : R1 -> itree E R2) :
  x <- Tau t;; k x = Tau (x <- t;; k x).
Proof.
  apply bisimulation_is_eq. apply bind_tau.
Qed.

Lemma bind_vis' {E R1 R2 R3} (e : E R1) (k1 : R1 -> itree E R2) (k2 : R2 -> itree E R3) :
  x <- Vis e k1;; k2 x = Vis e (fun x => x' <- k1 x;; k2 x').
Proof.
  apply bisimulation_is_eq. apply bind_vis.
Qed.

Lemma bind_bind' {E R1 R2 R3} (t : itree E R1) (k1 : R1 -> itree E R2) (k2 : R2 -> itree E R3) :
  x <- (x <- t;; k1 x);; k2 x = x1 <- t;; x2 <- k1 x1;; k2 x2.
Proof.
  apply bisimulation_is_eq. apply bind_bind.
Qed.

Lemma bind_trigger' {E E' R} `{E' -< E} X (e : E' X) k :
  x <- trigger e ;; k x = (vis e (fun x => k x) : itree E R).
Proof.
  apply bisimulation_is_eq. apply bind_trigger.
Qed.

Lemma unfold_bind' {E R S} (t : itree E R) (k : R -> itree E S) :
  x <- t;; k x = ITree._bind k (fun t0 : itree E R => x <- t0;; k x) (observe t).
Proof.
  apply bisimulation_is_eq. apply unfold_bind.
Qed.

Definition sep_step p q : Prop :=
  forall r, p ⊥ r -> q ⊥ r.

Definition sep_step_Perms P Q : Prop :=
  forall p, p ∈ P -> exists q, q ∈ Q /\ sep_step p q.

Instance sep_step_refl : Reflexive sep_step.
Proof.
  repeat intro; auto.
Qed.

Instance sep_step_trans : Transitive sep_step.
Proof.
  repeat intro. auto.
Qed.

Lemma sep_step_lte : forall p p' q, p <= p' -> sep_step p q -> sep_step p' q.
Proof.
  repeat intro. apply H0. symmetry. symmetry in H1. eapply separate_antimonotone; eauto.
Qed.

Lemma sep_step_lte' : forall p q, q <= p -> sep_step p q.
Proof.
  repeat intro. symmetry. eapply separate_antimonotone; eauto. symmetry; auto.
Qed.

Lemma sep_step_view : forall p q x y, sep_step p q -> view p x y -> view q x y.
Proof.
  intros. specialize (H (sym_upd_perm p) (separate_self_sym _)).
  apply H; auto.
Qed.

Lemma sep_step_upd : forall p q x y, sep_step p q ->
                                     upd q x y ->
                                     upd p x y.
Proof.
  intros. specialize (H (sym_upd_perm p) (separate_self_sym _)).
  apply H; auto.
Qed.

Lemma sep_step_sep_conj_l : forall p1 p2 q, p1 ⊥ q -> sep_step p1 p2 -> sep_step (p1 * q) (p2 * q).
Proof.
  intros p1 p2 q ? ?.
  repeat intro; auto. symmetry in H1. symmetry. apply separate_sep_conj_perm; symmetry; auto.
  - apply H0. symmetry. eapply separate_sep_conj_perm_l; eauto.
  - symmetry. eapply separate_sep_conj_perm_r; eauto.
Qed.
Lemma sep_step_sep_conj_r : forall p1 p2 q, p1 ⊥ q -> sep_step p1 p2 -> sep_step (q * p1) (q * p2).
Proof.
  intros p1 p2 q ? ?.
  repeat intro; auto. symmetry in H1. symmetry. apply separate_sep_conj_perm; symmetry; auto.
  - symmetry. eapply separate_sep_conj_perm_l; eauto.
  - apply H0. symmetry. eapply separate_sep_conj_perm_r; eauto.
  - symmetry. auto.
Qed.

Section ts.
  Variant MemoryE : Type -> Type :=
  | Load : forall (p : SByte), MemoryE SByte
  | Store : forall (p v : SByte) , MemoryE unit
  .

  (* Definition E := (stateE config +' nondetE). *)
  Definition E := (MemoryE +' nondetE).

  Context {R : Type}.
  (* Definition R := SByte. *)

  Definition par_match {R1 R2}
             (par : itree E R1 -> itree E R2 -> itree E (R1 * R2))
             (t1 : itree E R1)
             (t2 : itree E R2)
    : itree E (R1 * R2) :=
    vis Or (fun b : bool =>
              if b then
                match (observe t1) with
                | RetF r1 => fmap (fun r2 => (r1, r2)) t2
                | TauF t => Tau (par t t2)
                | VisF o k => vis o (fun x => par (k x) t2)
                end
              else
                match (observe t2) with
                | RetF r2 => fmap (fun r1 => (r1, r2)) t1
                | TauF t => Tau (par t1 t)
                | VisF o k => vis o (fun x => par t1 (k x))
                end).

  CoFixpoint par {R1 R2} (t1 : itree E R1) (t2 : itree E R2) := par_match par t1 t2.

  Lemma rewrite_par : forall {R1 R2} (t1 : itree E R1) (t2 : itree E R2),
      par t1 t2 = par_match par t1 t2.
  Proof.
    intros. apply bisimulation_is_eq. revert t1 t2.
    ginit. gcofix CIH. intros. gstep. unfold par. constructor. red. intros.
    apply Reflexive_eqit_gen_eq. (* not sure why reflexivity doesn't work here *)
  Qed.

  Lemma rewrite_spin : (ITree.spin : itree E R) = Tau (ITree.spin).
  Proof.
    intros. apply bisimulation_is_eq.
    ginit. gcofix CIH. gstep. unfold ITree.spin. constructor.
    apply Reflexive_eqit_gen_eq.
  Qed.

  Variant step : itree E R -> config -> itree E R -> config -> Prop :=
  | step_tau : forall t c, step (Tau t) c t c
  | step_nondet_true : forall k c, step (vis Or k) c (k true) c
  | step_nondet_false : forall k c, step (vis Or k) c (k false) c
  | step_load : forall k c p v, read c p = Some v ->
                                step (vis (Load (Ptr p)) k) c (k v) c
  | step_store : forall k c c' p v, write c p v = Some c' ->
                                    step (vis (Store (Ptr p) v) k) c (k tt) c'
  | step_load_fail : forall k c p, read c p = None ->
                                   step (vis (Load (Ptr p)) k) c (k (Byte 0)) (error_config c)
  | step_store_fail : forall k c p v, write c p v = None ->
                                      step (vis (Store (Ptr p) v) k) c (k tt) (error_config c)
  (* | step_get : forall k c, step (vis (Get _) k) c (k c) c *)
  (* | step_put : forall k c c', step (vis (Put _ c') k) c (k tt) c' *)
  .

  Inductive multistep : itree E R -> config -> itree E R -> config -> Prop :=
  | multistep_refl : forall t c, multistep t c t c
  | multistep_step : forall t c t' c' t'' c'',
      multistep t c t' c' -> step t' c' t'' c'' -> multistep t c t'' c''
  .

  Lemma step_bind : forall (t1 t2 : itree E R) (c1 c2 : config) (k : R -> itree E R),
      step t1 c1 t2 c2 ->
      step (t1 >>= k) c1 (t2 >>= k) c2.
  Proof.
    intros. inversion H; subst; try solve [rewrite bind_vis'; constructor; auto].
    - rewrite bind_tau'. constructor.
    - rewrite bind_vis'.
      (* constructor doesn't work here for some reason *)
      apply (step_load (fun v => x <- k0 v;; k x) _ _ _ H0).
  Qed.

  Lemma step_ret_bind : forall (t1 t2 : itree E R) (c1 c2 : config) (r : R),
      step t1 c1 t2 c2 ->
      step (Ret r;; t1) c1 t2 c2.
  Proof.
    intros. pose proof (bind_ret_l r (fun _ => t1)) as bind_ret.
    apply bisimulation_is_eq in bind_ret. rewrite bind_ret. assumption.
  Qed.

  (* to handle the nondeterminism, par needs double the amount of steps *)
  (* Lemma par_step_left : forall (t1 t2 t' : itree E R) (c c' : config), *)
  (*     step t1 c t2 c' -> *)
  (*     exists t'', step (par t1 t') c t'' c /\ step t'' c (par t2 t') c'. *)
  (* Proof. *)
  (*   inversion 1; subst; *)
  (*     try solve [rewrite rewrite_par; unfold par_match; simpl; repeat eexists; constructor; auto]. *)
  (*   (* as above, load case needs its constructor manually applied... *) *)
  (*   rewrite rewrite_par; unfold par_match; simpl; repeat eexists. constructor. *)
  (*   apply (step_load (fun x => par (k x) t') _ _ _ H0). *)
  (* Qed. *)
  (* Lemma par_step_right : forall (t1 t2 t' : itree E R) (c c' : config), *)
  (*     step t1 c t2 c' -> *)
  (*     exists t'', step (par t' t1) c t'' c /\ step t'' c (par t' t2) c'. *)
  (* Proof. *)
  (*   inversion 1; subst; *)
  (*     try solve [rewrite rewrite_par; unfold par_match; simpl; repeat eexists; constructor; auto]. *)
  (*   rewrite rewrite_par; unfold par_match; simpl; repeat eexists. constructor 3. *)
  (*   apply (step_load (fun x => par t' (k x)) _ _ _ H0). *)
  (* Qed. *)

  Variant typing_perm_gen typing (p : perm) (q : R -> perm) : itree E R -> Prop :=
  | cond : forall t, (exists c t' c', step t c t' c') /\ (* we can step *)
                     (forall c, dom p c -> (* and everything we can step to... *)
                                forall t' c',
                                  step t c t' c' ->
                                  (
                                    (* we step to configs that satisfy the perm *)
                                    (upd p c c') /\
                                    (* we step to machines that are well-typed by some other perm that maintains separation *)
                                    (exists p', typing p' q t' /\ sep_step p p' /\ dom p' c'))) ->
                     typing_perm_gen typing p q t
  | ret : forall r, q r <= p -> typing_perm_gen typing p q (Ret r).

  Definition typing_perm := paco3 typing_perm_gen bot3.

  Lemma typing_perm_gen_mon : monotone3 typing_perm_gen.
  Proof.
    repeat intro.
    inversion IN; subst.
    - econstructor. destruct H. split; auto.
      intros. edestruct H0; eauto. split; eauto.
      destruct H4 as [? [? [? ?]]]. eexists. split; [| split]; eauto.
    - constructor 2; auto.
  Qed.
  Hint Resolve typing_perm_gen_mon : paco.

  Definition no_error (c : config) :=
    e c = false.

  (* use instead of no_upd_error? *)
  Program Definition no_error_perm : perm :=
    {|
    dom := no_error;
    view := fun c c' => no_error c -> no_error c';
    upd := eq;
    |}.
  Next Obligation.
    constructor; auto.
  Qed.

  Lemma typing_perm_multistep : forall p q t,
      typing_perm p q t ->
      forall c, dom p c ->
                forall t' c', multistep t c t' c' ->
                              exists p', dom p' c' /\ sep_step p p' /\ typing_perm p' q t'.
  Proof.
    intros. induction H1.
    - eexists; split; [| split]; eauto; reflexivity.
    - destruct IHmultistep as (? & ? & ? & ?); eauto. pinversion H5; subst.
      + edestruct H6 as (? & ? & ? & ? & ? & ?); eauto. pclearbot.
        exists x0; split; [| split]; eauto. etransitivity; eauto.
      + inversion H2.
  Qed.

  Lemma typing_perm_soundness_step : forall p q t,
      typing_perm p q t ->
      forall c, dom (p * no_error_perm) c ->
                forall t' c', step t c t' c' -> no_error c'.
  Proof.
    intros. destruct H0 as (? & ? & ?).
    pinversion H; subst.
    - destruct H4. specialize (H5 _ H0 _ _ H1). decompose [ex and] H5; clear H4.
      eapply H3; eauto.
    - inversion H1.
  Qed.

  Lemma typing_perm_soundness : forall p q t,
      typing_perm p q t ->
      forall c, dom (p * no_error_perm) c ->
                forall t' c', multistep t c t' c' -> no_error c'.
  Proof.
    intros. destruct H0 as (? & ? & ?).
    generalize dependent p. induction H1; intros; auto.
    destruct (typing_perm_multistep _ _ _ H0 _ H3 _ _ H1) as (? & ? & ? & ?).
    specialize (IHmultistep H2 _ H0 H3 H4).
    apply H6 in H4.
    eapply typing_perm_soundness_step; eauto. split; [| split]; auto.
  Qed.

  Lemma typing_perm_lte : forall p q p' t, typing_perm p q t -> p <= p' -> typing_perm p' q t.
  Proof.
    intros. pcofix CIH. pstep.
    pinversion H; subst.
    - constructor 1. destruct H1 as ((? & ? & ? & ?) & ?).
      split; eauto. intros.
      edestruct H2; eauto. split; eauto.
      destruct H6 as [p'' [? [? ?]]].
      exists p''. split; [| split]; auto.
      + pclearbot. left. eapply paco3_mon_bot; eauto.
      + eapply sep_step_lte; eauto.
    - constructor 2. etransitivity; eauto.
  Qed.

  Inductive Returns (r : R) : itree E R -> Prop :=
  | ReturnsRet: Returns r (Ret r)
  | ReturnsTau: forall t, Returns r t -> Returns r (Tau t)
  | ReturnsVis: forall {X} (e : E X) (x : X) k, Returns r (k x) -> Returns r (Vis e k)
  .

  (* Inductive Returns {E} {A: Type} (a: A) : itree E A -> Prop := *)
  (* | ReturnsRet: forall t, t ≈ Ret a -> Returns a t *)
  (* | ReturnsTau: forall t u, t ≈ Tau u -> Returns a u -> Returns a t *)
  (* | ReturnsVis: forall {X} (e: E X) (x: X) t k, t ≈ Vis e k -> Returns a (k x) -> Returns a t *)
  (* . *)

  Lemma typing_perm_lte' : forall p q q' t,
      typing_perm p q t ->
      (forall r, q' r <= q r) ->
      typing_perm p q' t.
  Proof.
    pcofix CIH. intros. pstep. pinversion H0; subst.
    - constructor. destruct H as ((? & ? & ? & ?) & ?).
      split; eauto. intros.
      edestruct H2; eauto. split; eauto.
      destruct H6 as [p'' [? [? ?]]].
      exists p''. split; [| split]; auto.
      pclearbot. right. eapply CIH; eauto.
    - constructor 2. etransitivity; eauto.
  Qed.

  (* Lemma typing_perm_ret : forall p q r, typing_perm p q (Ret r). *)
  (* Proof. *)
  (*   pstep. constructor 2. intros. inversion H0. *)
  (* Qed. *)

  Lemma typing_perm_spin : forall p q, typing_perm p q ITree.spin.
  Proof.
    pcofix CIH. pstep. constructor 1. split.
    - exists start_config. eexists. exists start_config. rewrite rewrite_spin. constructor.
    - intros. rewrite rewrite_spin in H0.
      inversion H0; subst; split; try reflexivity.
      exists p. split; eauto; intuition.
  Qed.

  (* Lemma typing_perm_load' ptr val : *)
  (*   typing_perm (read_perm_p ptr val) (trigger (Load (Ptr ptr))). *)
  (* Proof. *)
  (*   pcofix CIH. pstep. constructor. intros. inversion H0; auto_inj_pair2; subst. *)
  (*   split; intuition. *)
  (*   eexists. split; [| split]; eauto; intuition. *)
  (*   left. eapply paco2_mon_bot; eauto. apply typing_perm_ret. *)
  (* Qed. *)

  (* Lemma typing_perm_store ptr val : *)
  (*   typing_perm (write_p ptr) (trigger (Store (Ptr ptr) val)). *)
  (* Proof. *)
  (*   pcofix CIH. pstep. constructor. intros. inversion H0; auto_inj_pair2; subst. *)
  (*   split; simpl; auto. *)
  (*   - intros. admit. *)
  (*   - exists (write_p ptr). split; [| split]. *)
  (*     + left. eapply paco2_mon_bot; eauto. apply typing_perm_ret. *)
  (*     + reflexivity. *)
  (*     + admit. *)
  (* Abort. *)

  Lemma typing_perm_bind : forall p q r t k,
      typing_perm p q t ->
      (forall r', typing_perm (q r') r (k r')) ->
      typing_perm p r (x <- t;; k x).
  Proof.
    pcofix CIH. intros. pinversion H0; subst.
    - destruct H as ((? & ? & ? & ?) & ?). pstep. constructor. split; auto.
      do 3 eexists; apply step_bind; eauto.
      intros. inversion H4; subst.
      + pose proof @eqitree_inv_bind_tau.
        edestruct H5 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H6; reflexivity | |];
          apply bisimulation_is_eq in H7; apply bisimulation_is_eq in H8; subst;
            [| inversion H].
        destruct (H2 _ H3 _ _ (step_tau _ _)) as (? & p' & ? & ? & ?). pclearbot.
        split; auto.
        exists p'. split; [| split]; auto. right. eapply CIH; eauto.
      + pose proof @eqitree_inv_bind_vis.
        edestruct H5 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H6; reflexivity | |];
          apply bisimulation_is_eq in H7; subst; [| inversion H].
        rewrite bind_vis' in H6. inversion H6; auto_inj_pair2; subst.
        destruct (H2 _ H3 _ _ (step_nondet_true _ _)) as (? & p' & ? & ? & ?). pclearbot.
        split; auto.
        exists p'. split; [| split]; auto. right. eapply CIH; eauto.
      + pose proof @eqitree_inv_bind_vis.
        edestruct H5 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H6; reflexivity | |];
          apply bisimulation_is_eq in H7; subst; [| inversion H].
        rewrite bind_vis' in H6. inversion H6; auto_inj_pair2; subst.
        destruct (H2 _ H3 _ _ (step_nondet_false _ _)) as (? & p' & ? & ? & ?). pclearbot.
        split; auto.
        exists p'. split; [| split]; auto. right. eapply CIH; eauto.
      + pose proof @eqitree_inv_bind_vis.
        edestruct H7 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H5; reflexivity | |];
          apply bisimulation_is_eq in H8; subst; [| inversion H].
        rewrite bind_vis' in H5. inversion H5; auto_inj_pair2; subst.
        destruct (H2 _ H3 _ _ (step_load _ _ _ _ H6)) as (? & p' & ? & ? & ?). pclearbot.
        split; auto.
        exists p'. split; [| split]; auto. right. eapply CIH; eauto.
      + pose proof @eqitree_inv_bind_vis.
        edestruct H7 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H5; reflexivity | |];
          apply bisimulation_is_eq in H8; subst; [| inversion H].
        rewrite bind_vis' in H5. inversion H5; auto_inj_pair2; subst.
        destruct (H2 _ H3 _ _ (step_store _ _ _ _ _ H6)) as (? & p' & ? & ? & ?). pclearbot.
        split; auto.
        exists p'. split; [| split]; auto. right. eapply CIH; eauto.
      + pose proof @eqitree_inv_bind_vis.
        edestruct H7 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H5; reflexivity | |];
          apply bisimulation_is_eq in H8; subst; [| inversion H].
        rewrite bind_vis' in H5. inversion H5; auto_inj_pair2; subst.
        destruct (H2 _ H3 _ _ (step_load_fail _ _ _ H6)) as (? & p' & ? & ? & ?). pclearbot.
        split; auto.
        exists p'. split; [| split]; auto. right. eapply CIH; eauto.
      + pose proof @eqitree_inv_bind_vis.
        edestruct H7 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H5; reflexivity | |];
          apply bisimulation_is_eq in H8; subst; [| inversion H].
        rewrite bind_vis' in H5. inversion H5; auto_inj_pair2; subst.
        destruct (H2 _ H3 _ _ (step_store_fail _ _ _ _ H6)) as (? & p' & ? & ? & ?). pclearbot.
        split; auto.
        exists p'. split; [| split]; auto. right. eapply CIH; eauto.
    - rewrite bind_ret_l'. eapply paco3_mon_bot; eauto. eapply typing_perm_lte; eauto.
  Qed.

  (* too weak *)
  Lemma typing_perm_frame_todo : forall p q r t,
      typing_perm p q t ->
      typing_perm (p * r) (fun r' => q r' * r) t.
  Proof.
    pcofix CIH. intros. pinversion H0; subst.
    - destruct H as ((? & ? & ? & ?) & ?). pstep. constructor. split; [do 3 eexists; eauto |].
      intros. edestruct H1; eauto; [apply H2 |]. clear H1.
      split; [constructor; auto |]. destruct H5 as (p' & ? & ? & ?).
      pclearbot. exists (p' * r0). split; [| split]; auto.
      + apply sep_step_sep_conj_l; auto. apply H2.
      + split; [| split]; auto.
        * destruct H2 as (? & ? & ?). apply H8 in H4. eapply dom_respects; eauto.
        * apply H5. apply H2.
    - pstep. constructor 2. intros. apply sep_conj_perm_monotone; intuition.
  Qed.

End ts.

Hint Resolve typing_perm_gen_mon : paco.

Lemma return_par {R1 R2} (t1 : itree E R1) (t2 : itree E R2) r1 r2 :
  Returns (r1, r2) (par t1 t2) ->
  Returns r1 t1.
Proof.
  intros.
  remember (par _ _) in H.
  generalize dependent t1.
  generalize dependent t2.
  induction H; intros.
  - admit.
  - admit.
  - rewrite rewrite_par in Heqi. unfold par_match in Heqi.
Qed.


Ltac rewritebisim lem := pose proof lem as bisim;
                         eapply bisimulation_is_eq in bisim;
                         rewrite bisim;
                         clear bisim.

Ltac rewritebisim_in lem H := pose proof lem as bisim;
                              eapply bisimulation_is_eq in bisim;
                              rewrite bisim in H;
                              clear bisim.

Lemma step_fmap {R1 R2} : forall (t t' : itree E R1) c c' (f : R1 -> R2),
    step t c t' c' ->
    step (fmap f t) c (fmap f t') c'.
Proof.
  intros. inversion H; subst; simpl; unfold ITree.map;
            try solve [rewrite bind_vis'; constructor; auto].
  - rewrite bind_tau'. constructor; auto.
  - rewrite bind_vis'.
    (* again have to specify k manually? *)
    apply (step_load (fun x => x' <- k x;; Ret (f x'))); auto.
Qed.

Lemma bind_fst {R1 R2} (t : itree E R1) (r2 : R2) :
  x1 <- t;; x <- Ret (x1, r2);; Ret (fst x) ≅ t.
Proof.
  revert t r2. pcofix CIH. intros.
  rewrite unfold_bind'. pstep.
  rewrite (itree_eta_ t0). destruct (observe t0); simpl.
  - rewrite unfold_bind'. constructor; auto.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma bind_snd {R1 R2} (t : itree E R2) (r1 : R1) :
  x2 <- t;; x <- Ret (r1, x2);; Ret (snd x) ≅ t.
Proof.
  revert t r1. pcofix CIH. intros.
  rewrite unfold_bind'. pstep.
  rewrite (itree_eta_ t0). destruct (observe t0); simpl.
  - rewrite unfold_bind'. constructor; auto.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma step_fmap_fst {R1 R2} : forall (t : itree E R2) (t' : itree E (R1 * R2)) c c' (r1 : R1),
    step (fmap (fun r2 : R2 => (r1, r2)) t) c t' c' ->
    step t c (fmap snd t') c'.
Proof.
  simpl. intros. unfold ITree.map in *. inversion H; subst.
  - edestruct @eqitree_inv_bind_tau as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H1; reflexivity | |].
    + apply bisimulation_is_eq in H0. apply bisimulation_is_eq in H2.
      rewrite H0. rewrite <- H2. rewritebisim @bind_bind. rewritebisim @bind_snd. constructor.
    + apply bisimulation_is_eq in H0. rewrite H0 in H1.
      rewritebisim_in @bind_ret_l H1. inversion H1.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H1; reflexivity | |].
    + specialize (H2 true). apply bisimulation_is_eq in H0. apply bisimulation_is_eq in H2.
      rewrite H0. rewrite <- H2. rewritebisim @bind_bind. rewritebisim @bind_snd. constructor.
    + apply bisimulation_is_eq in H0. rewrite H0 in H1.
      rewritebisim_in @bind_ret_l H1. inversion H1.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H1; reflexivity | |].
    + specialize (H2 false). apply bisimulation_is_eq in H0. apply bisimulation_is_eq in H2.
      rewrite H0. rewrite <- H2. rewritebisim @bind_bind. rewritebisim @bind_snd. constructor.
    + apply bisimulation_is_eq in H0. rewrite H0 in H1.
      rewritebisim_in @bind_ret_l H1. inversion H1.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H0; reflexivity | |].
    + specialize (H3 v). apply bisimulation_is_eq in H2. apply bisimulation_is_eq in H3.
      rewrite H2. rewrite <- H3.
      rewritebisim @bind_bind. rewritebisim @bind_snd. constructor; auto.
    + apply bisimulation_is_eq in H2. rewrite H2 in H0.
      rewritebisim_in @bind_ret_l H0. inversion H0.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H0; reflexivity | |].
    + specialize (H3 tt). apply bisimulation_is_eq in H2. apply bisimulation_is_eq in H3.
      rewrite H2. rewrite <- H3.
      rewritebisim @bind_bind. rewritebisim @bind_snd. constructor; auto.
    + apply bisimulation_is_eq in H2. rewrite H2 in H0.
      rewritebisim_in @bind_ret_l H0. inversion H0.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H0; reflexivity | |].
    + specialize (H3 (Byte 0)). apply bisimulation_is_eq in H2. apply bisimulation_is_eq in H3.
      rewrite H2. rewrite <- H3.
      rewritebisim @bind_bind. rewritebisim @bind_snd. constructor; auto.
    + apply bisimulation_is_eq in H2. rewrite H2 in H0.
      rewritebisim_in @bind_ret_l H0. inversion H0.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H0; reflexivity | |].
    + specialize (H3 tt). apply bisimulation_is_eq in H2. apply bisimulation_is_eq in H3.
      rewrite H2. rewrite <- H3.
      rewritebisim @bind_bind. rewritebisim @bind_snd. constructor 7; auto.
    + apply bisimulation_is_eq in H2. rewrite H2 in H0.
      rewritebisim_in @bind_ret_l H0. inversion H0.
Qed.

Lemma step_fmap_snd {R1 R2} : forall (t : itree E R1) (t' : itree E (R1 * R2)) c c' (r2 : R2),
    step (fmap (fun r1 : R1 => (r1, r2)) t) c t' c' ->
    step t c (fmap fst t') c'.
Proof.
  simpl. intros. unfold ITree.map in *. inversion H; subst.
  - edestruct @eqitree_inv_bind_tau as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H1; reflexivity | |].
    + apply bisimulation_is_eq in H0. apply bisimulation_is_eq in H2.
      rewrite H0. rewrite <- H2. rewritebisim @bind_bind. rewritebisim @bind_fst. constructor.
    + apply bisimulation_is_eq in H0. rewrite H0 in H1.
      rewritebisim_in @bind_ret_l H1. inversion H1.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H1; reflexivity | |].
    + specialize (H2 true). apply bisimulation_is_eq in H0. apply bisimulation_is_eq in H2.
      rewrite H0. rewrite <- H2. rewritebisim @bind_bind. rewritebisim @bind_fst. constructor.
    + apply bisimulation_is_eq in H0. rewrite H0 in H1.
      rewritebisim_in @bind_ret_l H1. inversion H1.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H1; reflexivity | |].
    + specialize (H2 false). apply bisimulation_is_eq in H0. apply bisimulation_is_eq in H2.
      rewrite H0. rewrite <- H2. rewritebisim @bind_bind. rewritebisim @bind_fst. constructor.
    + apply bisimulation_is_eq in H0. rewrite H0 in H1.
      rewritebisim_in @bind_ret_l H1. inversion H1.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H0; reflexivity | |].
    + specialize (H3 v). apply bisimulation_is_eq in H2. apply bisimulation_is_eq in H3.
      rewrite H2. rewrite <- H3.
      rewritebisim @bind_bind. rewritebisim @bind_fst. constructor; auto.
    + apply bisimulation_is_eq in H2. rewrite H2 in H0.
      rewritebisim_in @bind_ret_l H0. inversion H0.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H0; reflexivity | |].
    + specialize (H3 tt). apply bisimulation_is_eq in H2. apply bisimulation_is_eq in H3.
      rewrite H2. rewrite <- H3.
      rewritebisim @bind_bind. rewritebisim @bind_fst. constructor; auto.
    + apply bisimulation_is_eq in H2. rewrite H2 in H0.
      rewritebisim_in @bind_ret_l H0. inversion H0.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H0; reflexivity | |].
    + specialize (H3 (Byte 0)). apply bisimulation_is_eq in H2. apply bisimulation_is_eq in H3.
      rewrite H2. rewrite <- H3.
      rewritebisim @bind_bind. rewritebisim @bind_fst. constructor; auto.
    + apply bisimulation_is_eq in H2. rewrite H2 in H0.
      rewritebisim_in @bind_ret_l H0. inversion H0.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H0; reflexivity | |].
    + specialize (H3 tt). apply bisimulation_is_eq in H2. apply bisimulation_is_eq in H3.
      rewrite H2. rewrite <- H3.
      rewritebisim @bind_bind. rewritebisim @bind_fst. constructor 7; auto.
    + apply bisimulation_is_eq in H2. rewrite H2 in H0.
      rewritebisim_in @bind_ret_l H0. inversion H0.
Qed.

Lemma step_fmap_inv {R1 R2 : Type} (f : R1 -> R2) (t : itree E R1) (t' : itree E R2) c c' :
  step (fmap f t) c t' c' ->
  exists t'', t' = fmap f t''.
Proof.
  intros. simpl in *. unfold ITree.map in *. inversion H; subst.
  - edestruct @eqitree_inv_bind_tau as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H1; reflexivity | |].
    + apply bisimulation_is_eq in H2. eexists. symmetry. apply H2.
    + apply bisimulation_is_eq in H0. rewrite H0 in H1.
      rewritebisim_in @bind_ret_l H1. inversion H1.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H1; reflexivity | |].
    + specialize (H2 true). apply bisimulation_is_eq in H2. eexists. symmetry. apply H2.
    + apply bisimulation_is_eq in H0. rewrite H0 in H1.
      rewritebisim_in @bind_ret_l H1. inversion H1.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H1; reflexivity | |].
    + specialize (H2 false). apply bisimulation_is_eq in H2. eexists. symmetry. apply H2.
    + apply bisimulation_is_eq in H0. rewrite H0 in H1.
      rewritebisim_in @bind_ret_l H1. inversion H1.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H0; reflexivity | |].
    + specialize (H3 v). apply bisimulation_is_eq in H3. eexists. symmetry. apply H3.
    + apply bisimulation_is_eq in H2. rewrite H2 in H0.
      rewritebisim_in @bind_ret_l H0. inversion H0.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H0; reflexivity | |].
    + specialize (H3 tt). apply bisimulation_is_eq in H3. eexists. symmetry. apply H3.
    + apply bisimulation_is_eq in H2. rewrite H2 in H0.
      rewritebisim_in @bind_ret_l H0. inversion H0.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H0; reflexivity | |].
    + specialize (H3 (Byte 0)). apply bisimulation_is_eq in H3. eexists. symmetry. apply H3.
    + apply bisimulation_is_eq in H2. rewrite H2 in H0.
      rewritebisim_in @bind_ret_l H0. inversion H0.
  - edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H0; reflexivity | |].
    + specialize (H3 tt). apply bisimulation_is_eq in H3. eexists. symmetry. apply H3.
    + apply bisimulation_is_eq in H2. rewrite H2 in H0.
      rewritebisim_in @bind_ret_l H0. inversion H0.
Qed.

(* TODO Generalize these lemmas *)
Lemma fmap_fst {R1 R2 : Type} (t' : itree E R1) (t : itree E (R1 * R2)) (r2 : R2) :
  t = fmap (fun x => (x, r2)) t' ->
  t = fmap (fun x => (x, r2)) (fmap fst t).
Proof.
  intros. apply bisimulation_is_eq. generalize dependent H. revert t' t r2.
  pcofix CIH. intros.
  pstep. unfold eqit_. simpl in *. unfold ITree.map in H0.
  destruct (observe t0) eqn:?.
  - symmetry in Heqi. pose proof (simpobs Heqi). apply bisimulation_is_eq in H. rewrite H.
    rewritebisim @map_map.
    rewritebisim @map_ret.
    constructor.
    edestruct @eqitree_inv_bind_ret as (? & ? & ?);
      [rewrite H in H0; rewrite H0; reflexivity |].
    destruct r0 as [r1 r2']. apply bisimulation_is_eq in H2. inversion H2. reflexivity.
  - symmetry in Heqi. pose proof (simpobs Heqi). apply bisimulation_is_eq in H. rewrite H.
    do 2 rewritebisim @map_tau.
    edestruct @eqitree_inv_bind_tau as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H in H0; rewrite H0; reflexivity | |].
    + constructor. right. eapply CIH; eauto. apply bisimulation_is_eq. symmetry. apply H2.
    + apply bisimulation_is_eq in H1. subst. rewrite bind_ret_l' in H. inversion H.
  - symmetry in Heqi. pose proof (simpobs Heqi). apply bisimulation_is_eq in H. rewrite H.
    unfold ITree.map. rewrite bind_vis'. rewrite bind_vis'.
    edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H in H0; rewrite H0; reflexivity | |].
    + constructor. intros. right. subst. eapply CIH.
      specialize (H2 v). apply bisimulation_is_eq in H2. symmetry. apply H2.
    + apply bisimulation_is_eq in H2. inversion H2.
Qed.

Lemma fmap_snd {R1 R2 : Type} (t' : itree E R2) (t : itree E (R1 * R2)) (r1 : R1) :
  t = fmap (fun x => (r1, x)) t' ->
  t = fmap (fun x => (r1, x)) (fmap snd t).
Proof.
  intros. apply bisimulation_is_eq. generalize dependent H. revert t' t r1.
  pcofix CIH. intros.
  pstep. unfold eqit_. simpl in *. unfold ITree.map in H0.
  destruct (observe t0) eqn:?.
  - symmetry in Heqi. pose proof (simpobs Heqi). apply bisimulation_is_eq in H. rewrite H.
    rewritebisim @map_map.
    rewritebisim @map_ret.
    constructor.
    edestruct @eqitree_inv_bind_ret as (? & ? & ?);
      [rewrite H in H0; rewrite H0; reflexivity |].
    destruct r0 as [r1' r2]. apply bisimulation_is_eq in H2. inversion H2. reflexivity.
  - symmetry in Heqi. pose proof (simpobs Heqi). apply bisimulation_is_eq in H. rewrite H.
    do 2 rewritebisim @map_tau.
    edestruct @eqitree_inv_bind_tau as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H in H0; rewrite H0; reflexivity | |].
    + constructor. right. eapply CIH; eauto. apply bisimulation_is_eq. symmetry. apply H2.
    + apply bisimulation_is_eq in H1. subst. rewrite bind_ret_l' in H. inversion H.
  - symmetry in Heqi. pose proof (simpobs Heqi). apply bisimulation_is_eq in H. rewrite H.
    unfold ITree.map. rewrite bind_vis'. rewrite bind_vis'.
    edestruct @eqitree_inv_bind_vis as [(? & ? & ?) | (? & ? & ?)];
      [rewrite H in H0; rewrite H0; reflexivity | |].
    + constructor. intros. right. subst. eapply CIH.
      specialize (H2 v). apply bisimulation_is_eq in H2. symmetry. apply H2.
    + apply bisimulation_is_eq in H2. inversion H2.
Qed.

Lemma typing_perm_frame {R1 R2 : Type} : forall p q o (r1 : R1) (t : itree E R2),
    typing_perm p q t ->
    typing_perm (o r1 * p) (fun '(r1, r2) => o r1 * q r2) (fmap (fun r2 => (r1, r2)) t).
Proof.
  pcofix CIH. intros. pinversion H0; subst.
  - destruct H as ((? & ? & ? & ?) & ?). pstep. constructor.
    split. {
      simpl. do 3 eexists. eapply step_fmap; eauto.
    }
    intros. pose proof (step_fmap_fst _ _ _ _ _ H3).
    edestruct H1; eauto. apply H2.
    split; [constructor; auto |]. destruct H6 as (p' & ? & ? & ?).
    pclearbot. exists (o r1 * p'). split; [| split]; auto.
    + right.
      simpl in H3. unfold ITree.map in H3.
      pose proof @step_fmap_inv. simpl in H9. unfold ITree.map in H9.
      specialize (H9 _ _ _ _ _ _ _ H3). destruct H9.
      erewrite fmap_snd; eauto.
    + apply sep_step_sep_conj_r; auto. symmetry. apply H2.
    + split; [| split]; auto.
      * destruct H2 as (? & ? & ?).
        eapply dom_respects; eauto. apply H10; auto.
      * symmetry. apply H7. symmetry. apply H2.
  - simpl. pstep. unfold ITree.map. rewrite bind_ret_l'.
    constructor 2. apply sep_conj_perm_monotone; intuition.
Qed.

Lemma typing_perm_frame' {R1 R2 : Type} : forall p q o (r2 : R2) (t : itree E R1),
    typing_perm p q t ->
    typing_perm (p * o r2) (fun '(r1, r2) => q r1 * o r2) (fmap (fun r1 => (r1, r2)) t).
Proof.
  pcofix CIH. intros. pinversion H0; subst.
  - destruct H as ((? & ? & ? & ?) & ?). pstep. constructor.
    split. {
      simpl. do 3 eexists. eapply step_fmap; eauto.
    }
    intros. pose proof (step_fmap_snd _ _ _ _ _ H3).
    edestruct H1; eauto. apply H2.
    split; [constructor; auto |]. destruct H6 as (p' & ? & ? & ?).
    pclearbot. exists (p' * o r2). split; [| split]; auto.
    + right.
      simpl in H3. unfold ITree.map in H3.
      pose proof @step_fmap_inv. simpl in H9. unfold ITree.map in H9.
      specialize (H9 _ _ _ _ _ _ _ H3). destruct H9.
      erewrite fmap_fst; eauto.
    + apply sep_step_sep_conj_l; auto. apply H2.
    + split; [| split]; auto.
      * destruct H2 as (? & ? & ?).
        eapply dom_respects; eauto. apply H10; auto.
      * apply H7. apply H2.
  - simpl. pstep. unfold ITree.map. rewrite bind_ret_l'.
    constructor 2. apply sep_conj_perm_monotone; intuition.
Qed.

Lemma parallel_perm : forall {R1 R2} p1 p2 q1 q2 (t1 : itree E R1) (t2 : itree E R2),
    typing_perm p1 q1 t1 ->
    typing_perm p2 q2 t2 ->
    typing_perm (p1 * p2) (fun '(r1, r2) => q1 r1 * q2 r2) (par t1 t2).
Proof.
  intros R1 R2.
  pcofix CIH. intros p1 p2 q1 q2 t1 t2 Ht1 Ht2.
  pstep. econstructor.
  rewrite rewrite_par. unfold par_match. split.
  simpl. exists start_config. eexists. exists start_config. constructor.
  intros c (Hdom1 & Hdom2 & Hsep) t' c' Hstep.
  inversion Hstep; auto_inj_pair2; subst; clear Hstep; split; try reflexivity.
  { pinversion Ht1; subst.
    - destruct H as ((? & ? & ? & ?) & ?).
      inversion H; subst; clear H.
      + (* tau *) clear x1. simpl.
        exists (p1 * p2). split; [| split]; intuition.
        * left. pstep. constructor. split.
          -- exists start_config; eexists; exists start_config; constructor.
          -- intros. inversion H1; subst.
             split; intuition. destruct H as (Hdom1' & Hdom2' & Hsep').
             destruct (H0 _ Hdom1' _ _ (step_tau _ _)) as (? & (p & ? & ? & ?)).
             pclearbot. exists (p * p2). split; [| split]; auto.
             ++ apply sep_step_sep_conj_l; auto.
             ++ split; [| split]; auto.
        * split; [| split]; auto.
      + (* nondet *) clear x1. simpl.
        exists (p1 * p2). split; [| split]; auto; intuition.
        * left. pstep. constructor. split.
          -- exists start_config; eexists; exists start_config; constructor.
          -- intros. destruct H as (Hdom1' & Hdom2' & Hsep').
             inversion H1; auto_inj_pair2; subst.
             {
               split; intuition.
               destruct (H0 _ Hdom1' _ _ (step_nondet_true _ _)) as (? & (p & ? & ? & ?)).
               pclearbot. exists (p * p2). split; [| split]; auto.
               - apply sep_step_sep_conj_l; auto.
               - split; [| split]; auto.
             }
             {
               split; intuition.
               destruct (H0 _ Hdom1' _ _ (step_nondet_false _ _)) as (? & (p & ? & ? & ?)).
               pclearbot. exists (p * p2). split; [| split]; auto.
               - apply sep_step_sep_conj_l; auto.
               - split; [| split]; auto.
             }
        * split; [| split]; auto.
      + (* same as previous case *) clear x1. simpl.
        exists (p1 * p2). split; [| split]; auto; intuition.
        * left. pstep. constructor. split.
          -- exists start_config; eexists; exists start_config; constructor.
          -- intros. destruct H as (Hdom1' & Hdom2' & Hsep').
             inversion H1; auto_inj_pair2; subst.
             {
               split; intuition.
               destruct (H0 _ Hdom1' _ _ (step_nondet_true _ _)) as (? & (p & ? & ? & ?)).
               pclearbot. exists (p * p2). split; [| split]; auto.
               - apply sep_step_sep_conj_l; auto.
               - split; [| split]; auto.
             }
             {
               split; intuition.
               destruct (H0 _ Hdom1' _ _ (step_nondet_false _ _)) as (? & (p & ? & ? & ?)).
               pclearbot. exists (p * p2). split; [| split]; auto.
               - apply sep_step_sep_conj_l; auto.
               - split; [| split]; auto.
             }
        * split; [| split]; auto.
      + (* load *) clear H1 x1. simpl. rename p into l.
        exists (p1 * p2). split; [| split]; auto; intuition.
        * left. pstep. constructor. split.
          -- do 3 eexists. unshelve constructor; auto. apply read_config_mem.
          -- intros. destruct H as (Hdom1' & Hdom2' & Hsep').
             inversion H1; auto_inj_pair2; subst.
             {
               split; intuition.
               destruct (H0 _ Hdom1' _ _ (step_load _ _ _ _ H6)) as (? & (p & ? & ? & ?)).
               pclearbot. exists (p * p2). split; [| split]; auto.
               - apply sep_step_sep_conj_l; auto.
               - split; [| split]; auto.
             }
             {
               destruct (H0 _ Hdom1' _ _ (step_load_fail  _ _ _ H6)) as (? & (p & ? & ? & ?)).
               split. constructor 1. auto.
               pclearbot. exists (p * p2). split; [| split]; auto.
               - apply sep_step_sep_conj_l; auto.
               - split; [| split]; auto.
                 respects. apply Hsep. auto.
             }
        * split; [| split]; auto.
      + (* store *) clear H1 x1 x. simpl. rename p into l.
        exists (p1 * p2). split; [| split]; auto; intuition.
        * left. pstep. constructor. split.
          -- do 3 eexists. constructor. unshelve apply write_config_mem; auto.
          -- intros. destruct H as (Hdom1' & Hdom2' & Hsep').
             inversion H1; auto_inj_pair2; subst.
             {
               destruct (H0 _ Hdom1' _ _ (step_store _ _ _ _ _ H7)) as (? & (p & ? & ? & ?)).
               split. constructor 1; auto.
               pclearbot. exists (p * p2). split; [| split]; auto.
               - apply sep_step_sep_conj_l; auto.
               - split; [| split]; auto.
                 respects. apply Hsep. auto.
             }
             {
               destruct (H0 _ Hdom1' _ _ (step_store_fail _ _ _ _ H7)) as (? & (p & ? & ? & ?)).
               split. constructor 1; auto.
               pclearbot. exists (p * p2). split; [| split]; auto.
               - apply sep_step_sep_conj_l; auto.
               - split; [| split]; auto.
                 respects. apply Hsep. auto.
             }
        * split; [| split]; auto.
      + (* load *) clear H1 x. simpl. rename p into l.
        exists (p1 * p2). split; [| split]; auto; intuition.
        * left. pstep. constructor. split.
          -- do 3 eexists. unshelve constructor. apply (Byte 0). apply read_config_mem.
          -- intros. destruct H as (Hdom1' & Hdom2' & Hsep').
             inversion H1; auto_inj_pair2; subst.
             {
               split; intuition.
               destruct (H0 _ Hdom1' _ _ (step_load _ _ _ _ H6)) as (? & (p & ? & ? & ?)).
               pclearbot. exists (p * p2). split; [| split]; auto.
               - apply sep_step_sep_conj_l; auto.
               - split; [| split]; auto.
             }
             {
               destruct (H0 _ Hdom1' _ _ (step_load_fail  _ _ _ H6)) as (? & (p & ? & ? & ?)).
               split. constructor 1. auto.
               pclearbot. exists (p * p2). split; [| split]; auto.
               - apply sep_step_sep_conj_l; auto.
               - split; [| split]; auto.
                 respects. apply Hsep. auto.
             }
        * split; [| split]; auto.
      + (* store *) clear H1 x. simpl. rename p into l.
        exists (p1 * p2). split; [| split]; auto; intuition.
        * left. pstep. constructor. split.
          -- do 3 eexists. constructor. unshelve apply write_config_mem; auto.
          -- intros. destruct H as (Hdom1' & Hdom2' & Hsep').
             inversion H1; auto_inj_pair2; subst.
             {
               destruct (H0 _ Hdom1' _ _ (step_store _ _ _ _ _ H7)) as (? & (p & ? & ? & ?)).
               split. constructor 1; auto.
               pclearbot. exists (p * p2). split; [| split]; auto.
               - apply sep_step_sep_conj_l; auto.
               - split; [| split]; auto.
                 respects. apply Hsep. auto.
             }
             {
               destruct (H0 _ Hdom1' _ _ (step_store_fail _ _ _ _ H7)) as (? & (p & ? & ? & ?)).
               split. constructor 1; auto.
               pclearbot. exists (p * p2). split; [| split]; auto.
               - apply sep_step_sep_conj_l; auto.
               - split; [| split]; auto.
                 respects. apply Hsep. auto.
             }
        * split; [| split]; auto.
    - simpl. exists (q1 r0 * p2). split; [| split].
      + left.
        eapply paco3_mon_bot; eauto.
        apply typing_perm_frame; auto.
      + apply sep_step_sep_conj_l. auto.
        apply sep_step_lte'; auto.
      + split; [| split]; auto.
        respects; intuition. symmetry. eapply separate_antimonotone; eauto. symmetry. auto.
  }
  { pinversion Ht2; subst.
    - destruct H as ((? & ? & ? & ?) & ?).
      inversion H; subst; clear H.
      + (* tau *) clear x1. simpl.
        exists (p1 * p2). split; [| split]; intuition.
        * left. pstep. constructor. split.
          -- exists start_config; eexists; exists start_config; constructor.
          -- intros. inversion H1; subst.
             split; intuition. destruct H as (Hdom1' & Hdom2' & Hsep'). symmetry in Hsep'.
             destruct (H0 _ Hdom2' _ _ (step_tau _ _)) as (? & (p & ? & ? & ?)).
             pclearbot. exists (p1 * p). split; [| split]; auto.
             ++ apply sep_step_sep_conj_r; auto.
             ++ split; [| split]; auto. symmetry; apply H3; auto.
        * split; [| split]; auto.
      + (* nondet *) clear x1. simpl.
        exists (p1 * p2). split; [| split]; auto; intuition.
        * left. pstep. constructor. split.
          -- exists start_config; eexists; exists start_config; constructor.
          -- intros. destruct H as (Hdom1' & Hdom2' & Hsep'). symmetry in Hsep'.
             inversion H1; auto_inj_pair2; subst.
             {
               split; intuition.
               destruct (H0 _ Hdom2' _ _ (step_nondet_true _ _)) as (? & (p & ? & ? & ?)).
               pclearbot. exists (p1 * p). split; [| split]; auto.
               - apply sep_step_sep_conj_r; auto.
               - split; [| split]; auto. symmetry; apply H3; auto.
             }
             {
               split; intuition.
               destruct (H0 _ Hdom2' _ _ (step_nondet_false _ _)) as (? & (p & ? & ? & ?)).
               pclearbot. exists (p1 * p). split; [| split]; auto.
               - apply sep_step_sep_conj_r; auto.
               - split; [| split]; auto. symmetry; apply H3; auto.
             }
        * split; [| split]; auto.
      + (* same as previous case *) clear x1. simpl.
        exists (p1 * p2). split; [| split]; auto; intuition.
        * left. pstep. constructor. split.
          -- exists start_config; eexists; exists start_config; constructor.
          -- intros. destruct H as (Hdom1' & Hdom2' & Hsep'). symmetry in Hsep'.
             inversion H1; auto_inj_pair2; subst.
             {
               split; intuition.
               destruct (H0 _ Hdom2' _ _ (step_nondet_true _ _)) as (? & (p & ? & ? & ?)).
               pclearbot. exists (p1 * p). split; [| split]; auto.
               - apply sep_step_sep_conj_r; auto.
               - split; [| split]; auto. symmetry; apply H3; auto.
             }
             {
               split; intuition.
               destruct (H0 _ Hdom2' _ _ (step_nondet_false _ _)) as (? & (p & ? & ? & ?)).
               pclearbot. exists (p1 * p). split; [| split]; auto.
               - apply sep_step_sep_conj_r; auto.
               - split; [| split]; auto. symmetry; apply H3; auto.
             }
        * split; [| split]; auto.
      + (* load *) clear H1 x1. simpl. rename p into l.
        exists (p1 * p2). split; [| split]; auto; intuition.
        * left. pstep. constructor. split.
          -- do 3 eexists. unshelve constructor; auto. apply read_config_mem.
          -- intros. destruct H as (Hdom1' & Hdom2' & Hsep'). symmetry in Hsep'.
             inversion H1; auto_inj_pair2; subst.
             {
               split; intuition.
               destruct (H0 _ Hdom2' _ _ (step_load _ _ _ _ H6)) as (? & (p & ? & ? & ?)).
               pclearbot. exists (p1 * p). split; [| split]; auto.
               - apply sep_step_sep_conj_r; auto.
               - split; [| split]; auto. symmetry. apply H3; auto.
             }
             {
               destruct (H0 _ Hdom2' _ _ (step_load_fail  _ _ _ H6)) as (? & (p & ? & ? & ?)).
               split. constructor 1. auto.
               pclearbot. exists (p1 * p). split; [| split]; auto.
               - apply sep_step_sep_conj_r; auto.
               - split; [| split]; auto.
                 respects. apply Hsep. auto.
                 symmetry. apply H3; auto.
             }
        * split; [| split]; auto.
      + (* store *) clear H1 x1 x. simpl. rename p into l.
        exists (p1 * p2). split; [| split]; auto; intuition.
        * left. pstep. constructor. split.
          -- do 3 eexists. constructor. unshelve apply write_config_mem; auto.
          -- intros. destruct H as (Hdom1' & Hdom2' & Hsep'). symmetry in Hsep'.
             inversion H1; auto_inj_pair2; subst.
             {
               destruct (H0 _ Hdom2' _ _ (step_store _ _ _ _ _ H7)) as (? & (p & ? & ? & ?)).
               split. constructor 1; auto.
               pclearbot. exists (p1 * p). split; [| split]; auto.
               - apply sep_step_sep_conj_r; auto.
               - split; [| split]; auto.
                 respects. apply Hsep. auto.
                 symmetry. apply H3; auto.
             }
             {
               destruct (H0 _ Hdom2' _ _ (step_store_fail _ _ _ _ H7)) as (? & (p & ? & ? & ?)).
               split. constructor 1; auto.
               pclearbot. exists (p1 * p). split; [| split]; auto.
               - apply sep_step_sep_conj_r; auto.
               - split; [| split]; auto.
                 respects. apply Hsep. auto.
                 symmetry. apply H3; auto.
             }
        * split; [| split]; auto.
      + (* load *) clear H1 x. simpl. rename p into l.
        exists (p1 * p2). split; [| split]; auto; intuition.
        * left. pstep. constructor. split.
          -- do 3 eexists. unshelve constructor. apply (Byte 0). apply read_config_mem.
          -- intros. destruct H as (Hdom1' & Hdom2' & Hsep'). symmetry in Hsep'.
             inversion H1; auto_inj_pair2; subst.
             {
               split; intuition.
               destruct (H0 _ Hdom2' _ _ (step_load _ _ _ _ H6)) as (? & (p & ? & ? & ?)).
               pclearbot. exists (p1 * p). split; [| split]; auto.
               - apply sep_step_sep_conj_r; auto.
               - split; [| split]; auto. symmetry. apply H3; auto.
             }
             {
               destruct (H0 _ Hdom2' _ _ (step_load_fail  _ _ _ H6)) as (? & (p & ? & ? & ?)).
               split. constructor 1. auto.
               pclearbot. exists (p1 * p). split; [| split]; auto.
               - apply sep_step_sep_conj_r; auto.
               - split; [| split]; auto.
                 respects. apply Hsep. auto.
                 symmetry. apply H3; auto.
             }
        * split; [| split]; auto.
      + (* store *) clear H1 x. simpl. rename p into l.
        exists (p1 * p2). split; [| split]; auto; intuition.
        * left. pstep. constructor. split.
          -- do 3 eexists. constructor. unshelve apply write_config_mem; auto.
          -- intros. destruct H as (Hdom1' & Hdom2' & Hsep'). symmetry in Hsep'.
             inversion H1; auto_inj_pair2; subst.
             {
               destruct (H0 _ Hdom2' _ _ (step_store _ _ _ _ _ H7)) as (? & (p & ? & ? & ?)).
               split. constructor 1; auto.
               pclearbot. exists (p1 * p). split; [| split]; auto.
               - apply sep_step_sep_conj_r; auto.
               - split; [| split]; auto.
                 respects. apply Hsep. auto.
                 symmetry. apply H3; auto.
             }
             {
               destruct (H0 _ Hdom2' _ _ (step_store_fail _ _ _ _ H7)) as (? & (p & ? & ? & ?)).
               split. constructor 1; auto.
               pclearbot. exists (p1 * p). split; [| split]; auto.
               - apply sep_step_sep_conj_r; auto.
               - split; [| split]; auto.
                 respects. apply Hsep. auto.
                 symmetry. apply H3; auto.
             }
        * split; [| split]; auto.
    - simpl. exists (p1 * q2 r0). split; [| split].
      + left.
        eapply paco3_mon_bot; eauto.
        apply typing_perm_frame'. auto.
      + apply sep_step_sep_conj_r. symmetry; auto.
        apply sep_step_lte'; auto.
      + split; [| split]; auto.
        respects; intuition. eapply separate_antimonotone; eauto.
  }
Qed.

Section ts.

  Context {R : Type}.

  Definition typing (P : Perms) (Q : R -> Perms) (t : itree E R) :=
    forall p, p ∈ P -> exists q, (forall r, Returns r t -> q r ∈ Q r) /\ typing_perm p q t.

  Lemma typing_soundness : forall P Q (t : itree E R),
      (* (exists q, q ∈ Q) /\ (* change to something involving top_Perms? *) *)
      typing P Q t -> forall p c, p ∈ (P ** singleton_Perms no_error_perm) ->
                            dom p c ->
                            forall t' c', multistep t c t' c' ->
                                     no_error c'.
  Proof.
    intros. simpl in *.
    destruct H0 as (? & ? & ? & ? & ?).
    destruct (H _ H0) as (? & ? & ?). (* as ((? & ?) & ?). *)
    eapply typing_perm_soundness; eauto.
    split; [| split]; auto.
    - apply H4; auto.
    - apply H3; apply H4; auto.
    - eapply separate_antimonotone; eauto. destruct H4 as [? _ _]. apply (dom_inc0 _ H1).
  Qed.

  Lemma typing_lte : forall P P' Q t, typing P Q t -> P ⊑ P' -> typing P' Q t.
  Proof.
    repeat intro; auto.
  Qed.
  Lemma typing_lte' : forall P Q Q' t,
      typing P Q t -> (forall r, Returns r t -> Q' r ⊑ Q r) -> typing P Q' t.
  Proof.
    repeat intro.
    specialize (H _ H1). destruct H as (? & ? & ?).
    exists x. split; auto. intros. apply H0; auto.
  Qed.

  Lemma typing_ret : forall P Q r, Q r ⊑ P -> typing P Q (Ret r).
  Proof.
    repeat intro. specialize (H _ H0). exists (fun _ => p).
    split; intros; auto. inversion H1; subst; auto.
    pstep. constructor 2. reflexivity.
  Qed.
  Lemma typing_spin : forall P Q, typing P Q ITree.spin.
  Proof.
    repeat intro. exists (fun _ => p). split.
    2: apply typing_perm_spin.
    intros. exfalso. rewrite rewrite_spin in H0. dependent induction H0.
    apply IHReturns; auto. apply rewrite_spin.
  Qed.

  Lemma typing_top : forall P t, typing top_Perms P t.
  Proof.
    repeat intro. inversion H.
  Qed.

  Lemma typing_tau : forall P Q t, typing P Q t -> typing P Q (Tau t).
  Proof.
    repeat intro. specialize (H _ H0). destruct H as (? & ? & ?). pinversion H1; subst.
    - exists x. split; auto. intros. apply H. inversion H3; auto. pstep. constructor.
      split; [exists start_config; eexists; exists start_config; constructor |].
      intros. inversion H4; subst. split; intuition. eexists; split; [| split]; eauto; intuition.
    - exists x. split; auto. intros. apply H. inversion H3; auto. pstep. constructor.
      split; [exists start_config; eexists; exists start_config; constructor |].
      intros. inversion H4; subst. split; intuition. eexists; split; [| split]; eauto; intuition.
  Qed.

  (* Lemma typing_frame : forall P Q R t, typing P Q t -> typing (P ** R) (Q ** R) t. *)
  (* Proof. *)
  (*   repeat intro. rename p into p'. destruct H0 as (p & r & ? & ? & ?). *)
  (*   destruct (H _ H0) as (q & ? & ?). *)
  (*   exists (q * r). split. *)
  (*   - exists q, r. split; [| split]; intuition. *)
  (*   - eapply typing_perm_lte; eauto. apply typing_perm_frame; auto. *)
  (* Qed. *)

  (* (* todo get proper instance working *) *)
  (* Lemma frame' : forall P1 P2 t, typing P2 t -> typing (P1 ** P2) t. *)
  (* Proof. *)
  (*   intros. eapply type_lte; eauto. apply lte_r_sep_conj_Perms. *)
  (* Qed. *)

End ts.

Lemma return_par {R1 R2} (t1 : itree E R1) (t2 : itree E R2) r1 r2 :
  Returns (r1, r2) (par t1 t2) ->
  Returns r1 t1.
Proof.
  intros. (* rewrite rewrite_par in H. unfold par_match in H. *)
  dependent induction H.
  admit.
  admit.
  rewrite rewrite_par in x. unfold par_match in x.
  inversion x; subst; auto_inj_pair2; subst; clear x.
  destruct x0.
  {

  destruct x.
  { destruct (observe t1) eqn:?.
    admit.
    admit.
    (* eapply IHReturns; eauto. *)
    destruct e.
    - inversion H; subst; auto_inj_pair2; subst.
      rewrite itree_eta_. rewrite Heqi. econstructor.
      eapply IHReturns; eauto.

  remember (Vis _ _) in H.
  inversion H. admit. admit.
  rewrite rewrite_par in H0. unfold par_match in H0.
  inversion H0; subst; auto_inj_pair2; subst; clear H0. destruct x.
  - destruct (observe t1) eqn:?.
    + admit.
    + inversion H1; subst. dependent induction H2. admit. admit.

  dependent induction H. admit. admit. rewrite rewrite_par in x. unfold par_match in x.
  inversion x; subst; auto_inj_pair2; subst; clear x.
  destruct x0.
  - destruct (observe t1) eqn:?.
    + admit.
    + inversion H; subst; auto.

  generalize dependent t1.
  generalize dependent t2.
  induction H; intros.
  - inversion Heqi.
  - inversion Heqi.
  - inversion Heqi; subst; auto_inj_pair2; subst. clear Heqi.

    (* dependent induction H; auto_inj_pair2; subst. *)
    destruct x. {
      destruct (observe t1) eqn:?.
      - admit.
      -
  - destruct (observe t1) eqn:?.
    + rewrite (itree_eta_ t1). rewrite Heqi.
      admit.
    + inversion H; subst. eapply IHReturns; eauto.
Qed.
Abort.

Lemma typing_parallel {R1 R2} : forall P1 P2 Q1 Q2 (t1 : itree E R1) (t2 : itree E R2),
    typing P1 Q1 t1 ->
    typing P2 Q2 t2 ->
    typing (P1 ** P2) (fun '(r1, r2) => Q1 r1 ** Q2 r2) (par t1 t2).
Proof.
  intros P1 P2 Q1 Q2 t1 t2 Ht1 Ht2 p [p1 [p2 [? [? ?]]]].
  destruct (Ht1 _ H) as (q1 & ? & ?). specialize (Ht2 _ H0) as (q2 & ? & ?).
  exists (fun '(r1, r2) => q1 r1 * q2 r2). split.
  - intros. destruct r as [r1 r2]. exists (q1 r1), (q2 r2). split; [| split]; intuition.
    apply H2. admit. admit.
  - eapply typing_perm_lte; eauto. eapply parallel_perm; eauto.
Abort.

Definition fun_typing {R1} (P : Perms) (t : itree E R1) (P': R1 -> Perms) : Prop :=
  forall R2 (k : R1 -> itree E R2), (forall (r : R1), typing (P' r) (k r)) -> typing P (bind t k).


Lemma read_perm_read_succeed p ptr c v v' :
  read_perm ptr v <= p ->
  dom p c ->
  read c ptr = Some v' ->
  v = v'.
Proof.
  intros. apply H in H0. simpl in H0. rewrite H0 in H1. inversion H1; auto.
Qed.
Lemma read_perm_read_fail p ptr c v :
  read_perm ptr v <= p ->
  dom p c ->
  read c ptr = None ->
  False.
Proof.
  intros. apply H in H0. simpl in H0. rewrite H0 in H1. inversion H1.
Qed.
Lemma write_perm_write_fail p ptr c v v' :
  write_perm ptr v <= p ->
  dom p c ->
  write c ptr v' = None ->
  False.
Proof.
  intros. apply H in H0. simpl in H0. destruct ptr as [b o].
  unfold read, write in *. simpl in *.
  destruct (m c b); try solve [inversion H1]; try solve [inversion H0]. destruct l.
  destruct (PeanoNat.Nat.ltb o size); destruct (bytes o); simpl in *;
    try solve [inversion H1]; try solve [inversion H0].
Qed.

Lemma fun_typing_consequence {R} P (t : itree E R) P' Q Q' :
  fun_typing P t P' ->
  P ⊑ Q ->
  (forall r, Q' r ⊑ P' r) ->
  fun_typing Q t Q'.
Proof.
  red. intros. eapply type_lte; eauto. apply H. intros. eapply type_lte; eauto.
Qed.

Lemma fun_typing_ret {R} (r : R) P : fun_typing (P r) (Ret r) P.
Proof.
  repeat intro. simpl. rewrite bind_ret_l'. apply H; auto.
Qed.

Lemma fun_typing_ret_invert {R} (r : R) P P' :
  fun_typing P (Ret r) P' -> forall p p', p ∈ P -> p' ∈ P' r ->
                                    sep_step p p'.
Proof.
  repeat intro. unfold fun_typing in H. simpl in H.
  setoid_rewrite bind_ret_l' in H.
Admitted.

Lemma fun_typing_bind {R1 R2} (P1 : Perms) (t1 : itree E R1) (P2 : R1 -> Perms) (k : R1 -> itree E R2) (P3 : R2 -> Perms) :
  fun_typing P1 t1 P2 ->
  (forall r, fun_typing (P2 r) (k r) P3) ->
  fun_typing P1 (bind t1 k) P3.
Proof.
  repeat intro. simpl. rewrite bind_bind'. apply H; auto.
  repeat intro. apply H0; auto.
Qed.

Lemma fun_typing_pre {R} P (t : itree E R) P' :
  fun_typing P t P' ->
  typing P t.
Proof.
  intros. rewrite <- bind_ret_r'. apply H. intros. apply type_ret.
Qed.

Program Definition eq_p {T} (y x : T) :=
  {|
  in_Perms := fun _ => x = y;
  |}.

Lemma fun_typing_load ptr P : fun_typing
                                (read_Perms ptr P)
                                (trigger (Load (Ptr ptr)))
                                (fun x => (read_Perms ptr (fun y => eq_p x y)) ** P x).
Proof.
  repeat intro. pstep. constructor. intros.
  destruct H0 as (? & (v & ?) & ?); subst.
  destruct H3 as (pr & p' & (? & ? & ?)).

  simpl in *. rewrite bind_trigger' in H2.
  inversion H2; auto_inj_pair2; subst; clear H2.
  - eapply read_perm_read_succeed in H10; eauto. subst.
    2: { eapply dom_inc; eauto. etransitivity; eauto. apply lte_l_sep_conj_perm. }
    split; intuition. exists (pr * p'). split; [| split].
    + left. apply H; auto. simpl. do 2 eexists. split; [| split]; eauto. 2: reflexivity.
      simpl. eexists; split; eauto. simpl. do 2 eexists. split; [ | split]; eauto.
      rewrite sep_conj_perm_bottom. reflexivity.
    + apply sep_step_lte'. auto.
    + eapply dom_inc; eauto.
  - exfalso. eapply read_perm_read_fail; [| eauto | eauto].
    etransitivity. apply H0. etransitivity; eauto. apply lte_l_sep_conj_perm.
Qed.

Lemma fun_typing_store ptr val P P' : fun_typing
                                        (write_Perms ptr P ** P' val)
                                        (trigger (Store (Ptr ptr) val))
                                        (fun _ => write_Perms ptr P').
Proof.
  repeat intro. pstep. constructor. intros.
  destruct H0 as (? & p' & (? & (v & ?) & ?) & ? & ?). subst.
  destruct H3 as (pw & ? & ? & ? & ?). simpl in *.
  rewrite bind_trigger' in H2.
  inversion H2; auto_inj_pair2; subst; clear H2.
  - split. {
      apply (upd_inc (write_perm ptr v)).
      - etransitivity; eauto. etransitivity; eauto.
        etransitivity. 2: apply lte_l_sep_conj_perm.
        etransitivity; eauto. apply lte_l_sep_conj_perm.
      - split; [eapply write_success_other_ptr |
                split; [eapply write_success_allocation | eapply write_success_others]]; eauto.
    }
    exists (write_perm ptr val * p'). split; [| split].
    + left. apply H. simpl. eexists. split; eauto.
      simpl. exists (write_perm ptr val), p'. split; [| split]; eauto; intuition.
    + repeat intro. symmetry in H2. eapply separate_antimonotone in H2; eauto.
      eapply separate_antimonotone in H2.
      2: { apply sep_conj_perm_monotone. 2: reflexivity.
           etransitivity. 2: eauto. etransitivity. 2: apply lte_l_sep_conj_perm. eauto. }
      constructor; apply H2.
    + assert (write_perm ptr val ⊥ p'). {
        eapply dom_inc in H1; eauto. destruct H1 as (_ & _ & ?).
        symmetry in H1. eapply separate_antimonotone in H1; eauto.
        eapply separate_antimonotone in H1; eauto. 2: apply lte_l_sep_conj_perm.
        eapply separate_antimonotone in H1; eauto. constructor; apply H1.
      }
      split; [| split]; auto.
      * eapply write_read; eauto.
      * respects. 2: { eapply dom_inc. apply lte_r_sep_conj_perm. eapply dom_inc; eauto. }
        apply H2. simpl.
        split; [eapply write_success_other_ptr |
                split; [eapply write_success_allocation | eapply write_success_others]]; eauto.
  - exfalso. eapply write_perm_write_fail. 2, 3: eauto. etransitivity; eauto.
    etransitivity. apply lte_l_sep_conj_perm. etransitivity; eauto.
    etransitivity; eauto. apply lte_l_sep_conj_perm.
Qed.

Lemma in_Perms_lte p P Q : p ∈ P -> Q ⊑ P -> p ∈ Q.
Proof.
  intros. eapply Perms_upwards_closed; eauto; intuition.
Qed.

Lemma fun_typing_frame {R} P (t : itree E R) P' Q :
  fun_typing P t P' ->
  fun_typing (P ** Q) t (fun x => P' x ** Q).
Proof.
  repeat intro. red in H0. red in H.

  generalize dependent P.
  generalize dependent P'.
  generalize dependent Q.
  generalize dependent p.
  pcofix CIH. intros. simpl in H1. simpl.
  setoid_rewrite unfold_bind' in H1.
  rewrite unfold_bind'.
  simpl in CIH. rewrite unfold_bind' in CIH.

  destruct (observe t) eqn:?; simpl; simpl in H1.
  - assert (exists p', p' ∈ P' r0) by admit. destruct H.
    destruct H2 as (? & ? & ? & ? & ?).
    assert (sep_step x0 x) by admit.
    assert (x * x1 ∈ P' r0 ** Q). apply sep_conj_Perms_perm; auto.

    specialize (H0 _ _ H6). pinversion H0; eauto.

    pstep. constructor. intros. split. admit.
    exists (x * x1). split; [| split].
    + admit. admit.
    + repeat intro. admit.
    + simpl.
      (* split; [admit |]. eexists. split; [| split]. *)
      (* + right. simpl in CIH. apply CIH. *)

      (* eapply paco2_mon_bot; eauto. apply H1; eauto. *)
      (* 2: { destruct H2 as (? & ? & ? & ? & ?). eapply Perms_upwards_closed; eauto. *)
      (*      etransitivity; eauto. apply lte_l_sep_conj_perm. } *)
      (* repeat intro. apply H0. simpl. do 2 eexists. split; [| split]; eauto. *)

      (* eapply Perms_upwards_closed; eauto. *)
      admit.
  - eapply paco2_mon_bot; eauto. apply H1. 2: {
      eapply in_Perms_lte; eauto. apply lte_l_sep_conj_Perms.
    }
    repeat intro. apply H0.

    simpl in CIH. pstep. constructor. intros. inversion H3; subst.
    split; intuition.
Qed.

Lemma typing_perm_load p ptr :
  typing_perm p (trigger (Load (Ptr ptr))).
Proof.
  pcofix CIH. pstep. constructor. intros. inversion H0; auto_inj_pair2; subst.
  - split; intuition.
    eexists. split; [| split]; eauto; intuition.
    left. eapply paco2_mon_bot; eauto. apply typing_perm_ret.
  -
Abort.

Lemma typing_load ptr P :
  typing P (trigger (Load (Ptr ptr))).
Proof.
  repeat intro. (* apply typing_perm_load. *)
Abort.

(* Load an addr from ptr, and store val into it *)
Definition load_store ptr val : itree E _ :=
  vis (Load (Ptr ptr)) (fun ptr' => vis (Store ptr' val) (fun _ => Ret tt)).

Lemma typing_perm_store ptr v1 v2 :
  typing_perm (write_perm ptr v1) (vis (Store (Ptr ptr) v2) (fun _ => Ret tt)).
Proof.
  pstep. constructor. intros. inversion H0; auto_inj_pair2; subst. split.
  - split; [| split]; intros; simpl.
    + eapply write_success_other_ptr; eauto.
    + eapply write_success_allocation; eauto.
    + admit.
  - exists (write_perm ptr v2); split; [| split].
    + left. apply typing_perm_ret.
    + repeat intro. destruct H1. constructor; auto.
    + simpl. eapply write_success_ptr; eauto.
  - simpl in H. admit.
Admitted.

Lemma typing_perm_load_store ptr ptr' v v' :
  typing_perm (read_perm ptr (Ptr ptr') * write_perm ptr' v) (load_store ptr v').
Proof.
  intros. pstep. constructor. intros. inversion H0; auto_inj_pair2; subst. split; intuition.
  eexists. split; [| split]; eauto; intuition.
  left. simpl in H. destruct H. rewrite H in H6. inversion H6; subst.
  eapply typing_perm_lte. apply typing_perm_store. apply lte_r_sep_conj_perm.
Qed.

Lemma typing_load_store ptr val :
  typing (read_Perms ptr (fun val' => match val' with
                                   | Ptr ptr' => write_Perms ptr' (fun _ => bottom_Perms)
                                   | _ => bottom_Perms
                                   end))
         (load_store ptr val).
Proof.
  repeat intro. simpl in H. decompose [ex and] H; clear H.
  subst. simpl in H2. decompose [ex and] H2; clear H2.
  destruct x0 eqn:?.
  - pstep. constructor. intros. unfold load_store in *.
    inversion H2; auto_inj_pair2.
    split; intuition.
    assert (x0 = v).
    { subst.
      destruct H3. specialize (dom_inc0 _ H1). destruct dom_inc0. destruct H.
      specialize (dom_inc0 _ H3). simpl in dom_inc0. rewrite dom_inc0 in H9. inversion H9. auto.
    }
    subst.
    eexists. split; [| split]; eauto. left. pstep. constructor. intros. inversion H5. reflexivity.
  - simpl in *. decompose [ex and] H0; clear H0; subst. simpl in H4.
    decompose [ex and] H4; clear H4.
    eapply typing_perm_lte. apply typing_perm_load_store.
    etransitivity; eauto. apply sep_conj_perm_monotone; eauto.
    etransitivity; eauto. etransitivity; eauto. apply lte_l_sep_conj_perm.
Qed.

(* Store an addr into ptr, and then use it by loading and storing into it. *)
Definition store_load_store ptr ptr' : itree E _ :=
  vis (Store (Ptr ptr) ptr') (fun _ => load_store ptr (Byte 1)).

Lemma typing_perm_store_load_store ptr ptr' v v' :
  typing_perm (write_perm ptr v * write_perm ptr' v') (store_load_store ptr (Ptr ptr')).
Proof.
  pstep. constructor. intros. unfold store_load_store in H0.
  inversion H0; auto_inj_pair2; subst.
  (* destruct H as (? & ? & ?). simpl in H. *)
  split.
  - constructor. left. simpl.
    split; [eapply write_success_other_ptr | eapply write_success_allocation]; eauto.
  - exists (read_perm ptr (Ptr ptr') * write_perm ptr' v'). split; [| split].
    + left. apply typing_perm_load_store.
    + (* TODO: factor out this more general version of sep_step_lte' *)
      repeat intro. destruct H1. constructor; auto. intros.
      apply sep_r0. clear sep_l0 sep_r0. induction H1.
      * destruct H1; constructor; [left | right]; simpl in *; subst; auto. split; reflexivity.
      * econstructor 2; eauto.
    + destruct H as (? & ? & ?).
      split; [| split]; simpl in *; auto.
      * eapply write_success_ptr; eauto.
      * apply write_write_separate_neq_ptr in H2. erewrite <- write_success_other_ptr; eauto.
      * rewrite read_write_separate_neq_ptr. apply write_write_separate_neq_ptr in H2; auto.
Qed.

Lemma typing_store_load_store ptr ptr' :
  typing (write_Perms ptr (fun _ => bottom_Perms) **
                      write_Perms ptr' (fun _ => bottom_Perms))
         (store_load_store ptr (Ptr ptr')).
Proof.
  repeat intro. simpl in H. decompose [ex and] H; clear H. subst.
  simpl in H3, H5. decompose [ex and] H3; clear H3.
  decompose [ex and] H5; clear H5. clear H0 H3.
  eapply typing_perm_lte. apply typing_perm_store_load_store.
  etransitivity; eauto.
  apply sep_conj_perm_monotone; etransitivity; eauto;
    etransitivity; eauto; apply lte_l_sep_conj_perm.
Qed.
