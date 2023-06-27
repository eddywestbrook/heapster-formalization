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
     Eq.Eqit.

From Heapster Require Import
     Utils
     Permissions
     PermType
     Memory
     Lifetime
     MemoryPerms
     LifetimePerms
     Typing
     SepStep.

From Paco Require Import
     paco.

Import ListNotations.
Open Scope list_scope.
(* end hide *)

Section Perms.
  Context {Si Ss : Type}.
  Context `{Hmemory: Lens Si memory}.
  Context `{Hlifetime: Lens Si Lifetimes}.

  Context `{HGetPut1 : (forall x y, @lget _ _ Hmemory (@lput _ _ Hlifetime x y) = @lget _ _ Hmemory x)}.
  Context `{HGetPut2 : (forall x y, @lget _ _ Hlifetime (@lput _ _ Hmemory x y) = @lget _ _ Hlifetime x)}.
  Context `{HPutPut : (forall si x y, @lput _ _ Hmemory (@lput _ _ Hlifetime si x) y =
                                   @lput _ _ Hlifetime (@lput _ _ Hmemory si y) x)}.
  (* Context `{HPutPut2 : (forall si x y, @lput _ _ Hlifetime (@lput _ _ Hmemory si x) y = *)
  (*                                   @lput _ _ Hmemory (@lput _ _ Hlifetime si y) x)}. *)

  Lemma nonLifetime_read_perm p v :
    @nonLifetime _ Ss _ (read_perm p v).
  Proof.
    intros n. split; intros [] [].
    - intros. cbn in *. destruct H as ((? & H) & _). rewrite H. rewrite HGetPut1. reflexivity.
    - intros. cbn in *. subst. split; reflexivity.
  Qed.
  Lemma nonLifetime_write_perm p v :
    @nonLifetime _ Ss _ (write_perm p v).
  Proof.
    intros n. split; intros [] [].
    - intros. cbn in *. destruct H as ((? & H) & _). rewrite H. rewrite HGetPut1. reflexivity.
    - intros. cbn in *. destruct H as ((? & H) & _). rewrite H. do 2 rewrite HGetPut2.
      split; reflexivity.
  Qed.

  Lemma guar_inv_read_perm p v :
    @guar_inv _ Ss _ (read_perm p v).
  Proof.
    repeat intro. cbn in *. subst. reflexivity.
  Qed.
  Lemma guar_inv_write_perm p v :
    @guar_inv _ Ss _ (write_perm p v).
  Proof.
    repeat intro. destruct H as ((? & ?) & ? & ? & ?). subst.
    cbn. rewrite !HGetPut1, HGetPut2.
    split; [| split; [| split]]; auto.
    eexists. rewrite HPutPut. reflexivity.
  Qed.

  Lemma pre_inv_read_perm p v :
    @pre_inv _ Ss _ (read_perm p v).
  Proof.
    repeat intro. cbn. rewrite HGetPut1. auto.
  Qed.
  Lemma pre_inv_write_perm p v :
    @pre_inv _ Ss _ (write_perm p v).
  Proof.
    repeat intro. cbn. rewrite HGetPut1. auto.
  Qed.

  Lemma nonLifetime_ptr {A} p rw o' a (T : VPermType A) (HT : forall xi xs, nonLifetime_Perms (xi :: T ▷ xs)) :
    @nonLifetime_Perms _ Ss _ ((VPtr p) :: ptr(rw, o', T) ▷ a).
  Proof.
    intros q Hq. destruct p as [b o]. destruct Hq as (? & (v & ?) & ?). subst.
    destruct H0 as (p & pt' & Hp & Ht' & Hsep & Hlte).
    edestruct (HT v a _ Ht') as (pt & Ht & Hlte' & Hnlt & Hguart & Hpret).
    destruct rw.
    - assert (Hsep' : (read_perm (b, o + o') v) ⊥ pt).
      {
        eapply separate_antimonotone. 2: apply Hlte'.
        symmetry. eapply separate_antimonotone. 2: apply Hp. symmetry; auto.
      }
      exists ((read_perm (b, o + o') v) ** pt). split; [| split; [| split; [| split]]].
      + eexists. split. eexists. reflexivity.
        cbn. do 2 eexists. split; [| split; [| split]]; eauto; reflexivity.
      + etransitivity; eauto. apply sep_conj_perm_monotone; auto.
      + apply nonLifetime_sep_conj_perm; auto. apply nonLifetime_read_perm.
      + apply guar_inv_sep_conj_perm; auto. apply guar_inv_read_perm.
      + apply pre_inv_sep_conj_perm; auto. apply pre_inv_read_perm.
    - assert (Hsep' : (write_perm (b, o + o') v) ⊥ pt).
      {
        eapply separate_antimonotone. 2: apply Hlte'.
        symmetry. eapply separate_antimonotone. 2: apply Hp. symmetry; auto.
      }
      exists ((write_perm (b, o + o') v) ** pt). split; [| split; [| split; [| split]]].
      + eexists. split. eexists. reflexivity.
        cbn. do 2 eexists. split; [| split; [| split]]; eauto; reflexivity.
      + etransitivity; eauto. apply sep_conj_perm_monotone; auto.
      + apply nonLifetime_sep_conj_perm; auto. apply nonLifetime_write_perm.
      + apply guar_inv_sep_conj_perm; auto. apply guar_inv_write_perm.
      + apply pre_inv_sep_conj_perm; auto. apply pre_inv_write_perm.
  Qed.

  Lemma separate_write_perm p l v v' :
    p ⊥ @write_perm _ Ss _ l v ->
    p ⊥ write_perm l v'.
  Proof.
    intros H. split; apply H; auto.
  Qed.

  Lemma sep_step_write_perm p l v v' :
    sep_step p (@write_perm _ Ss _ l v) ->
    sep_step p (write_perm l v').
  Proof.
    repeat intro. split; apply H; auto.
  Qed.

  Lemma nonLifetime_trueP :
    forall (xi : Value) (xs : unit), @nonLifetime_Perms _ Ss _ (xi :: trueP ▷ xs).
  Proof.
    repeat intro. exists bottom_perm. cbn. intuition.
    apply bottom_perm_is_bottom.
    apply nonLifetime_bottom.
    apply guar_inv_bottom.
    apply pre_inv_bottom.
  Qed.

  Lemma nonLifetime_eqp y :
    forall (xi : Value) (xs : unit), @nonLifetime_Perms _ Ss _ (xi :: eqp y ▷ xs).
  Proof.
    repeat intro. exists bottom_perm. cbn. intuition.
    apply bottom_perm_is_bottom.
    apply nonLifetime_bottom.
    apply guar_inv_bottom.
    apply pre_inv_bottom.
  Qed.

  Lemma split_Perms_trueP b o l (P Q : @Perms (Si * Ss)) :
    (VPtr (b, o)) :: ptr(W, 0, trueP) ▷ tt * lowned_Perms l P Q ⊨
      when_Perms l ((VPtr (b, o)) :: ptr(W, 0, trueP) ▷ tt) *
      lowned_Perms l
        (when_Perms l ((VPtr (b, o)) :: ptr(R, 0, trueP) ▷ tt) * P)
        (((VPtr (b, o)) :: ptr(W, 0, trueP) ▷ tt) * Q).
  Proof.
    intros p0 (p' & powned & Hp' & (r1 & r2 & Hr1 & Hr2 & Hr2' & Hsep' & Hr2'' & Hlte' & Hf) & Hsep & Hlte).
    destruct (nonLifetime_ptr _ _ _ _ trueP nonLifetime_trueP _ Hp') as (p & Hp & Hpp' & Hnlp & Hguarp & Hprep).
    exists (when l p Hnlp).
    assert (Hpr2 : p ⊥ r2).
    {
      eapply owned_sep; auto.
      eapply separate_antimonotone.
      2: {
        etransitivity. apply lte_r_sep_conj_perm. eauto.
      }
      symmetry. eapply separate_antimonotone; eauto. symmetry. auto.
    }
    cbn in Hp.
    eexists (r1 ** owned l (p ** r2) (nonLifetime_sep_conj_perm _ _ Hnlp Hr2 Hpr2)).
    split; [| split; [| split]]; auto.
    - apply when_perm_Perms; auto.
    - exists r1, (p ** r2), Hr1, (nonLifetime_sep_conj_perm _ _ Hnlp Hr2 Hpr2), (guar_inv_sep_conj_perm _ _ Hguarp Hr2').
      split; [| split; [| split]].
      3: reflexivity.
      {
        apply sep_owned; auto. eapply separate_antimonotone. 2: apply Hpp'.
        symmetry. eapply separate_antimonotone. apply Hsep.
        etransitivity; eauto. apply lte_l_sep_conj_perm.
      }
      {
        apply sep_conj_Perms_perm; auto.
      }
      (** Precondition part *)
      intros p1 (pw & q & (? & (pr & Hpr' & Hpr & ?) & Hlte''') & Hq' & Hsep''' & Hlte'') Hsep''; subst.
      cbn in Hlte'''.
      specialize (Hf _ Hq'). destruct Hf as (r & Hr & Hsep_step & Hpre).
      {
        symmetry in Hsep''.
        eapply separate_antimonotone in Hsep''; eauto.
        eapply separate_antimonotone in Hsep''; eauto.
        2: apply lte_r_sep_conj_perm.
        symmetry in Hsep''.
        eapply separate_antimonotone in Hsep''; eauto.
        apply sep_conj_perm_monotone. reflexivity.
        apply owned_monotone. apply lte_r_sep_conj_perm.
      }
      destruct Hp as (? & (v & ?) & Hx). subst. rewrite Nat.add_0_r in Hx.
      rewrite sep_conj_Perms_commut in Hx. rewrite sep_conj_Perms_bottom_identity in Hx.
      cbn in Hx.

      destruct Hpr as (? & (v' & ?) & Hx'). subst. rewrite Nat.add_0_r in Hx'.
      rewrite sep_conj_Perms_commut in Hx'. rewrite sep_conj_Perms_bottom_identity in Hx'.
      cbn in Hx'.
      exists ((write_perm (b, o) v') ** r). split; [| split].
      + apply sep_conj_Perms_perm; auto.
        * cbn. eexists. split. eexists. reflexivity.
          rewrite Nat.add_0_r.
          rewrite sep_conj_Perms_commut. rewrite sep_conj_Perms_bottom_identity.
          cbn. reflexivity.
        * symmetry. eapply separate_write_perm.
          apply Hsep_step.
          eapply separate_antimonotone.
          2: apply Hx.
          symmetry. auto.
      + etransitivity.
        * apply sep_step_sep_conj_r; eauto. symmetry. auto.
        * apply sep_step_sep_conj_l; eauto. symmetry. apply Hsep_step. symmetry. auto.
          eapply sep_step_write_perm.
          apply sep_step_lte'; eauto.
      + intros. split; [| split]; auto.
        * apply Hlte'' in H. destruct H as (? & ? & ?).
          apply Hlte''' in H. cbn in H.
          rewrite lGetPut in H. setoid_rewrite nth_error_replace_list_index_eq in H.
          apply Hx' in H. cbn in *.
          rewrite HGetPut1 in H |- *; auto. right. reflexivity.
        * apply Hpre; auto. apply Hlte''; auto.
        * symmetry. apply Hsep_step.
          eapply separate_write_perm.
          eapply separate_antimonotone. symmetry. apply Hpr2. apply Hx.
    - apply separate_sep_conj_perm.
      + apply sep_when; auto.
        symmetry.
        eapply separate_antimonotone. 2: apply Hpp'.
        symmetry.
        eapply separate_antimonotone. apply Hsep. etransitivity; eauto.
        apply lte_l_sep_conj_perm.
      + apply when_owned_sep.
      + symmetry. apply sep_owned; auto. eapply separate_antimonotone. 2: apply Hpp'.
        symmetry. eapply separate_antimonotone. apply Hsep.
        etransitivity; eauto. apply lte_l_sep_conj_perm.
    - etransitivity; eauto.
      etransitivity. 2: apply sep_conj_perm_monotone; [reflexivity |].
      2: apply Hlte'.
      do 2 rewrite <- sep_conj_perm_assoc.
      do 2 rewrite (sep_conj_perm_commut _ r1).
      do 2 rewrite sep_conj_perm_assoc.
      apply sep_conj_perm_monotone; [reflexivity |].
      etransitivity. apply convert.
      apply sep_conj_perm_monotone; [| reflexivity]; auto.
  Qed.

  Lemma split_Perms_eq b o y l (P Q : @Perms (Si * Ss)) :
    (VPtr (b, o)) :: ptr(W, 0, eqp y) ▷ tt * lowned_Perms l P Q ⊨
      when_Perms l ((VPtr (b, o)) :: ptr(W, 0, eqp y) ▷ tt) *
      lowned_Perms l
        (when_Perms l ((VPtr (b, o)) :: ptr(R, 0, eqp y) ▷ tt) * P)
        (((VPtr (b, o)) :: ptr(W, 0, eqp y) ▷ tt) * Q).
  Proof.
    intros p0 (p' & powned & Hp' & (r1 & r2 & Hr1 & Hr2 & Hr2' & Hsep' & Hr2'' & Hlte' & Hf) & Hsep & Hlte).
    destruct (nonLifetime_ptr _ _ _ _ (eqp y) (nonLifetime_eqp y) _ Hp') as (p & Hp & Hpp' & Hnlp & Hguarp & Hprep).
    exists (when l p Hnlp).
    assert (Hpr2 : p ⊥ r2).
    {
      eapply owned_sep; auto.
      eapply separate_antimonotone.
      2: {
        etransitivity. apply lte_r_sep_conj_perm. eauto.
      }
      symmetry. eapply separate_antimonotone; eauto. symmetry. auto.
    }
    eexists (r1 ** owned l (p ** r2) (nonLifetime_sep_conj_perm _ _ Hnlp Hr2 Hpr2)).
    split; [| split; [| split]]; auto.
    - apply when_perm_Perms; auto.
    - exists r1, (p ** r2), Hr1, (nonLifetime_sep_conj_perm _ _ Hnlp Hr2 Hpr2), (guar_inv_sep_conj_perm _ _ Hguarp Hr2').
      split; [| split; [| split]].
      3: reflexivity.
      {
        apply sep_owned; auto. eapply separate_antimonotone. 2: apply Hpp'.
        symmetry. eapply separate_antimonotone. apply Hsep.
        etransitivity; eauto. apply lte_l_sep_conj_perm.
      }
      {
        apply sep_conj_Perms_perm; auto.
      }
      (** Precondition part *)
      intros p1 (pw & q & (? & (pr & Hpr' & Hpr & ?) & Hlte''') & Hq' & Hsep''' & Hlte'') Hsep''; subst.
      cbn in Hlte'''.
      specialize (Hf _ Hq'). destruct Hf as (r & Hr & Hsep_step & Hpre).
      {
        symmetry in Hsep''.
        eapply separate_antimonotone in Hsep''; eauto.
        eapply separate_antimonotone in Hsep''; eauto.
        2: apply lte_r_sep_conj_perm.
        symmetry in Hsep''.
        eapply separate_antimonotone in Hsep''; eauto.
        apply sep_conj_perm_monotone. reflexivity.
        apply owned_monotone. apply lte_r_sep_conj_perm.
      }
      destruct Hp as (? & (v & ?) & Hx). subst. rewrite Nat.add_0_r in Hx.
      cbn in Hx. destruct Hx as (? & ? & ? & ? & ? & ?). subst.
      destruct Hpr as (? & (v' & ?) & Hx'). subst. rewrite Nat.add_0_r in Hx'.
      cbn in Hx'. destruct Hx' as (? & ? & ? & ? & ? & ?). subst.
      exists ((write_perm (b, o) v') ** r). split; [| split].
      + apply sep_conj_Perms_perm; auto.
        * cbn. eexists. split. eexists. reflexivity.
          rewrite Nat.add_0_r.
          cbn. do 2 eexists. split; [| split; [| split]].
          -- reflexivity.
          -- reflexivity.
          -- apply separate_bottom.
          -- rewrite sep_conj_perm_bottom. reflexivity.
        * symmetry. (* eapply separate_write_perm. *)
          apply Hsep_step.
          eapply separate_antimonotone. 2: apply H.
          eapply separate_antimonotone. 2: apply lte_l_sep_conj_perm.
          eapply separate_antimonotone. 2: eauto.
          symmetry. auto.
      + etransitivity.
        * apply sep_step_sep_conj_r; eauto. symmetry. auto.
        * apply sep_step_sep_conj_l; eauto. symmetry. apply Hsep_step. symmetry. auto.
          apply sep_step_lte'; eauto.
          etransitivity; eauto.
          etransitivity; eauto. apply lte_l_sep_conj_perm.
      + intros. split; [| split]; auto.
        * apply Hlte'' in H3. destruct H3 as (? & ? & ?).
          apply Hlte''' in H3. cbn in H3.
          rewrite lGetPut in H3. setoid_rewrite nth_error_replace_list_index_eq in H3.
          apply H5 in H3. destruct H3 as (? & ? & ?).
          apply H0 in H3. cbn in H3. cbn.
          rewrite HGetPut1 in H3 |- *; auto. right. reflexivity.
        * apply Hpre; auto. apply Hlte''; auto.
        * symmetry. apply Hsep_step.
          eapply separate_antimonotone. 2: apply H.
          eapply separate_antimonotone. 2: apply lte_l_sep_conj_perm.
          eapply separate_antimonotone. 2: eauto.
          symmetry. apply Hpr2.
    - apply separate_sep_conj_perm.
      + apply sep_when; auto.
        symmetry.
        eapply separate_antimonotone. 2: apply Hpp'.
        symmetry.
        eapply separate_antimonotone. apply Hsep. etransitivity; eauto.
        apply lte_l_sep_conj_perm.
      + apply when_owned_sep.
      + symmetry. apply sep_owned; auto. eapply separate_antimonotone. 2: apply Hpp'.
        symmetry. eapply separate_antimonotone. apply Hsep.
        etransitivity; eauto. apply lte_l_sep_conj_perm.
    - etransitivity; eauto.
      etransitivity. 2: apply sep_conj_perm_monotone; [reflexivity |].
      2: apply Hlte'.
      do 2 rewrite <- sep_conj_perm_assoc.
      do 2 rewrite (sep_conj_perm_commut _ r1).
      do 2 rewrite sep_conj_perm_assoc.
      apply sep_conj_perm_monotone; [reflexivity |].
      etransitivity. apply convert.
      apply sep_conj_perm_monotone; [| reflexivity]; auto.
  Qed.

  Definition when_ptr_Perms {A} (l : nat) (rw : RW) (p : Value) (a : A) (T : VPermType A)
    : @Perms (Si * Ss) :=
    match p with
    | VNum _ => top_Perms
    | VPtr p =>
        meet_Perms (fun P => exists (v : Value),
                        P = singleton_Perms
                              (match rw with
                               | R => when l (read_perm p v) (nonLifetime_read_perm _ _)
                               | W => when l (write_perm p v) (nonLifetime_write_perm _ _)
                               end) *
                              (v :: T ▷ a))
    end.

  Definition when_ptr {A} (l : nat) '(rw, o, T) : VPermType A :=
    {|
      ptApp := fun x a => when_ptr_Perms l rw (offset x o) a T;
    |}.

  Definition finished_ptr_Perms {A} (l : nat) (rw : RW) (p : Value) (a : A) (T : VPermType A) : @Perms (Si * Ss) :=
    match p with
    | VNum _ => top_Perms
    | VPtr p =>
        meet_Perms (fun P => exists (v : Value),
                        P = singleton_Perms
                              (match rw with
                               | R => lfinished l (read_perm p v) (nonLifetime_read_perm _ _)
                               | W => lfinished l (write_perm p v) (nonLifetime_write_perm _ _)
                               end) *
                              (v :: T ▷ a))
    end.

  Definition finished_ptr {A} (l : nat) '(rw, o, T) : VPermType A :=
    {|
      ptApp := fun x a => finished_ptr_Perms l rw (offset x o) a T;
    |}.

  Lemma typing_end' {A} l b o (T : VPermType A) xs (HT : forall v a, nonLifetime_Perms (v :: T ▷ a)) :
    typing (specConfig := Ss)
      ((VPtr (b, o)) :: when_ptr l (W, 0, T) ▷ xs *
         (lowned_Perms l (when_Perms l ((VPtr (b, o)) :: ptr(R, 0, trueP) ▷ tt))
            ((VPtr (b, o)) :: ptr(W, 0, trueP) ▷ tt)))
      (fun _ _ => (VPtr (b, o)) :: finished_ptr l (W, 0, T) ▷ xs)
      (endLifetime l)
      (Ret tt).
  Proof.
    intros p' c1 c2 (pwt & lowned' & Hpwt & H & Hsep & Hlte) Hpre.
    destruct Hpwt as (? & (v & ?) & Hpwt); subst.
    destruct Hpwt as (pwhen & pt & Hpwhen & Hpt & Hsep' & Hlte').
    destruct (HT _ _ _ Hpt) as (pt' & Hpt' & Hltept' & Hnlpt' & Hguarpt' & Hprept').
    destruct H as (r1 & r2 & Hr1 & Hr2 & Hr2' & Hsep'' & Hr2'' & Hlte'' & Hf).
    unfold endLifetime. unfold id.
    rewritebisim @bind_trigger.
    pstep. econstructor; eauto; try reflexivity.

    pose proof Hpre as Hpre''.
    apply Hlte in Hpre. destruct Hpre as (_ & Hpre & _).
    apply Hlte'' in Hpre. destruct Hpre as (_ & H & _).
    cbn in H. setoid_rewrite H.
    rewritebisim @bind_trigger.
    specialize (Hf (when l (write_perm (b, o + 0) v) (nonLifetime_write_perm (b, o + 0) v))).
    destruct Hf as (q & Hq & Hsep_step & Hpre).
    {
      apply when_perm_Perms. eexists. split. eexists. reflexivity. cbn.
      do 2 eexists. split; [| split; [| split]]. 2: auto.
      - apply read_lte_write.
      - apply separate_bottom.
      - rewrite sep_conj_perm_bottom. reflexivity.
    }
    {
      apply Hlte in Hpre''. destruct Hpre'' as (? & ? & ?).
      eapply separate_antimonotone; eauto.
      symmetry. eapply separate_antimonotone; eauto.
      eapply separate_antimonotone; eauto. symmetry. eauto.
      etransitivity; eauto. apply lte_l_sep_conj_perm.
    }
    destruct Hq as (? & (v' & ?) & Hq); subst.
    rewrite sep_conj_Perms_commut in Hq. rewrite sep_conj_Perms_bottom_identity in Hq.
    cbn in Hq.
    assert (Hv: Some v = read (lget c1) (b, o + 0)).
    {
      apply Hlte in Hpre''. destruct Hpre'' as (Hpre'' & _).
      apply Hlte' in Hpre''. destruct Hpre'' as (Hpre'' & _).
      apply Hpwhen in Hpre''. cbn in Hpre''. auto.
    }
    assert (v = v'). {
      specialize (Hpre c1 c2).
      apply Hq in Hpre.
      - (* from this we can get that (b, o) points to v using pwhen *)
        cbn in Hpre.
        rewrite HGetPut1 in Hpre. rewrite <- Hv in Hpre. inversion Hpre. auto.
      - rewrite replace_list_index_eq; auto. rewrite lPutGet. cbn.
        intros. apply Hv.
      - apply Hlte''. apply Hlte. rewrite replace_list_index_eq; auto.
        rewrite lPutGet. auto.
    } subst. rename v' into v.
    assert (Hsep''': owned l r2 Hr2 ⊥ pt'). {
      eapply separate_antimonotone; eauto.
      eapply separate_antimonotone. 2: apply lte_r_sep_conj_perm.
      eapply separate_antimonotone; eauto.
      symmetry.
      eapply separate_antimonotone; eauto.
      etransitivity; eauto. apply lte_r_sep_conj_perm.
    }
    econstructor; unfold id; auto.
    {
      cbn in *. apply Hlte. constructor 1. right.
      apply Hlte''. constructor 1. right. right.
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
      econstructor.
      2: {
        cbn. eexists. split. eexists. reflexivity. cbn.
        eexists (lfinished l q _). exists pt'. split; [| split; [| split]].
        - apply lfinished_monotone; eauto.
        - auto.
        - apply lfinished_separate'; auto.
          apply Hsep_step. symmetry. eapply owned_sep; eauto. symmetry. eauto.
        - reflexivity.
      }
      cbn. rewrite lGetPut.
      split; split.
      - symmetry. apply nth_error_replace_list_index_eq.
      - apply Hpre.
        + cbn. rewrite lGetPut. rewrite HGetPut1.
          intros. apply Hv.
        + rewrite replace_list_index_eq; auto.
          rewrite lPutGet.
          apply Hlte''. apply Hlte. auto.
      - apply Hprept'. apply Hltept'. apply Hlte'. apply Hlte; auto.
      - apply lfinished_separate'; auto.
        apply Hsep_step. symmetry. eapply owned_sep; eauto. symmetry. eauto.
    }
    eapply sep_step_lte; eauto.
    rewrite sep_conj_perm_commut.
    eapply sep_step_lte. apply sep_conj_perm_monotone. eauto.
    etransitivity. 2: apply Hlte'. etransitivity. 2: apply lte_r_sep_conj_perm.
    apply Hltept'.
    eapply sep_step_lte.
    rewrite sep_conj_perm_assoc. apply lte_r_sep_conj_perm.
    apply sep_step_sep_conj_l; auto.
    etransitivity. 2: eapply sep_step_owned_finished.
    apply owned_sep_step; auto.

    Unshelve.
    eapply nonLifetime_sep_step. 2: eauto. auto.
  Qed.


  Lemma split_Perms' b o l (P Q : @Perms (Si * Ss)) T (xs : Ss)
    (HT : forall xi xs, nonLifetime_Perms (xi :: T ▷ xs)) :
    (VPtr (b, o)) :: ptr(W, 0, T) ▷ xs * lowned_Perms l P Q ⊨
      (VPtr (b, o)) :: when_ptr l (W, 0, T) ▷ xs *
      lowned_Perms l
        ((VPtr (b, o)) :: when_ptr l (R, 0, trueP) ▷ xs * P)
        ((VPtr (b, o)) :: when_ptr l (W, 0, trueP) ▷ xs * Q).
  Proof.
    intros p0 (p' & powned & Hp' & (r1 & r2 & Hr1 & Hr2 & Hr2' & Hsep' & Hr2'' & Hlte' & Hf) & Hsep & Hlte).
    destruct (nonLifetime_ptr _ _ _ _ T HT _ Hp') as (p'' & Hp'' & Hpp' & Hnlp & Hguarp).
    destruct Hp'' as (? & (v & ?) & Hasdf). subst.
    destruct Hasdf as (p & pt & Hp & Hpt & Hsep'' & Hlte'').
    cbn in Hp.
    exists (when l p'' Hnlp).
    assert (Hpr2 : p ⊥ r2).
    {
      eapply owned_sep; auto.
      eapply separate_antimonotone.
      2: {
        etransitivity. apply lte_r_sep_conj_perm. eauto.
      }
      symmetry. eapply separate_antimonotone; eauto. symmetry. auto.
    }
    eexists (r1 ** owned l (p ** r2) (nonLifetime_sep_conj_perm _ _ Hnlp Hr2 Hpr2)).
    split; [| split; [| split]]; auto.
    - apply when_perm_Perms; auto.
    - exists r1, (p ** r2), Hr1, (nonLifetime_sep_conj_perm _ _ Hnlp Hr2 Hpr2), (guar_inv_sep_conj_perm _ _ Hguarp Hr2').
      split; [| split; [| split]].
      3: reflexivity.
      {
        apply sep_owned; auto. eapply separate_antimonotone. 2: apply Hpp'.
        symmetry. eapply separate_antimonotone. apply Hsep.
        etransitivity; eauto. apply lte_l_sep_conj_perm.
      }
      {
        apply sep_conj_Perms_perm; auto.
      }
      (** Precondition part *)
      intros p1 (pw & q & (? & (pr & Hpr' & Hpr & ?) & Hlte''') & Hq' & Hsep''' & Hlte'') Hsep''; subst.
      cbn in Hlte'''.
      specialize (Hf _ Hq'). destruct Hf as (r & Hr & Hsep_step & Hpre).
      {
        symmetry in Hsep''.
        eapply separate_antimonotone in Hsep''; eauto.
        eapply separate_antimonotone in Hsep''; eauto.
        2: apply lte_r_sep_conj_perm.
        symmetry in Hsep''.
        eapply separate_antimonotone in Hsep''; eauto.
        apply sep_conj_perm_monotone. reflexivity.
        apply owned_monotone. apply lte_r_sep_conj_perm.
      }
      cbn in Hp.
      destruct Hp as (? & (v & ?) & Hx). subst. rewrite Nat.add_0_r in Hx.
      rewrite sep_conj_Perms_commut in Hx. rewrite sep_conj_Perms_bottom_identity in Hx.
      cbn in Hx.

      destruct Hpr as (? & (v' & ?) & Hx'). subst. rewrite Nat.add_0_r in Hx'.
      rewrite sep_conj_Perms_commut in Hx'. rewrite sep_conj_Perms_bottom_identity in Hx'.
      cbn in Hx'.
      exists ((write_perm (b, o) v') ** r). split; [| split].
      + apply sep_conj_Perms_perm; auto.
        * cbn. eexists. split. eexists. reflexivity.
          rewrite Nat.add_0_r.
          rewrite sep_conj_Perms_commut. rewrite sep_conj_Perms_bottom_identity.
          cbn. reflexivity.
        * symmetry. eapply separate_write_perm.
          apply Hsep_step.
          eapply separate_antimonotone.
          2: apply Hx.
          symmetry. auto.
      + etransitivity.
        * apply sep_step_sep_conj_r; eauto. symmetry. auto.
        * apply sep_step_sep_conj_l; eauto. symmetry. apply Hsep_step. symmetry. auto.
          eapply sep_step_write_perm.
          apply sep_step_lte'; eauto.
      + intros. split; [| split]; auto.
        * apply Hlte'' in H. destruct H as (? & ? & ?).
          apply Hlte''' in H. cbn in H.
          rewrite lGetPut in H. setoid_rewrite nth_error_replace_list_index_eq in H.
          apply Hx' in H. cbn in *.
          rewrite HGetPut1 in H |- *; auto. right. reflexivity.
        * apply Hpre; auto. apply Hlte''; auto.
        * symmetry. apply Hsep_step.
          eapply separate_write_perm.
          eapply separate_antimonotone. symmetry. apply Hpr2. apply Hx.
    - apply separate_sep_conj_perm.
      + apply sep_when; auto.
        symmetry.
        eapply separate_antimonotone. 2: apply Hpp'.
        symmetry.
        eapply separate_antimonotone. apply Hsep. etransitivity; eauto.
        apply lte_l_sep_conj_perm.
      + apply when_owned_sep.
      + symmetry. apply sep_owned; auto. eapply separate_antimonotone. 2: apply Hpp'.
        symmetry. eapply separate_antimonotone. apply Hsep.
        etransitivity; eauto. apply lte_l_sep_conj_perm.
    - etransitivity; eauto.
      etransitivity. 2: apply sep_conj_perm_monotone; [reflexivity |].
      2: apply Hlte'.
      do 2 rewrite <- sep_conj_perm_assoc.
      do 2 rewrite (sep_conj_perm_commut _ r1).
      do 2 rewrite sep_conj_perm_assoc.
      apply sep_conj_perm_monotone; [reflexivity |].
      etransitivity. apply convert.
      apply sep_conj_perm_monotone; [| reflexivity]; auto.
  Qed.
End Perms.
