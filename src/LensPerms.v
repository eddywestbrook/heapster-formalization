(* begin hide *)

From Coq Require Import
     Classes.Morphisms
     Relations.Relation_Operators
     Logic.JMeq
     Lists.List
     Arith.PeanoNat
     Logic.FunctionalExtensionality
     Lia.

From Heapster Require Import
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


Section PLensPerms.
  Context {St Ix Elem} `{IxPLens:IxPartialLens Ix St Elem}.


  (***
   *** Read and write permissions
   ***)

  (* The permission to write to an ixplens, assuming it already has a value that
  satisfies a given precondition *)
  Program Definition ixplens_write_perm_pre ix (pre : Elem -> Prop) : @perm St :=
    {|
      pre x := exists elem, iget ix x = Some elem /\ pre elem;
      rely x y := iget ix x <> None -> iget ix x = iget ix y;
      guar x y := x = y \/
                    iget ix x <> None /\ exists elem, y = iput ix x elem;
      inv x := True
    |}.
  Next Obligation.
    constructor; repeat intro.
    - reflexivity.
    - rewrite <- (H H1) in H0. apply H0; assumption.
  Qed.
  Next Obligation.
    constructor; repeat intro.
    - left; reflexivity.
    - destruct H; [ subst; assumption | ].
      destruct H0 as [? | [? [elem2 ?]]]; [ subst; right; eassumption | ].
      destruct H as [? [elem1 ?]]. right; subst.
      split; [ assumption | ].
      exists elem2. apply iPutPut; assumption.
  Qed.
  Next Obligation.
    rewrite <- H; [ | eapply Some_not_None; eassumption ].
    eexists; split; eassumption.
  Qed.

  (* Permission to write to an ixplens that already equals a specific value *)
  Definition ixplens_write_perm_eq ix elem :=
    ixplens_write_perm_pre ix (eq elem).

  (* Permission to write to an ixplens that could be any value *)
  Definition ixplens_write_perm_any ix :=
    ixplens_write_perm_pre ix (fun _ => True).

  (* Write permissions are monotonic in their precondition *)
  Lemma monotone_ixplens_write_perm ix (pre1 pre2 : Elem -> Prop) :
    (forall elem, pre1 elem -> pre2 elem) ->
    ixplens_write_perm_pre ix pre2 <= ixplens_write_perm_pre ix pre1.
  Proof.
    constructor; intros; try assumption.
    destruct H1 as [elem [? ?]]. eexists; split; [ | apply H ]; eassumption.
  Qed.


  (* The permission to read from an ixplens, assuming it already has a value *)
  Program Definition ixplens_read_perm_pre ix (pre : Elem -> Prop) : @perm St :=
    {|
      pre x := exists elem, iget ix x = Some elem /\ pre elem;
      rely x y := iget ix x <> None -> iget ix x = iget ix y;
      guar x y := x = y;
      inv x := True
    |}.
  Next Obligation.
    constructor; repeat intro.
    - reflexivity.
    - rewrite <- (H H1) in H0. apply H0; assumption.
  Qed.
  Next Obligation.
    rewrite <- H; [ | eapply Some_not_None; eassumption ].
    eexists; split; eassumption.
  Qed.

  (* Permission to read from an ixplens that already equals a specific value *)
  Definition ixplens_read_perm_eq ix elem :=
    ixplens_read_perm_pre ix (eq elem).

  (* Permission to read from an ixplens that could be any value *)
  Definition ixplens_read_perm_any ix :=
    ixplens_read_perm_pre ix (fun _ => True).

  (* Read permissions are monotonic in their precondition *)
  Lemma monotone_ixplens_read_perm ix (pre1 pre2 : Elem -> Prop) :
    (forall elem, pre1 elem -> pre2 elem) ->
    ixplens_read_perm_pre ix pre2 <= ixplens_read_perm_pre ix pre1.
  Proof.
    constructor; intros; try assumption.
    destruct H1 as [elem [? ?]]. eexists; split; [ | apply H ]; eassumption.
  Qed.


  (* A write permission is greater than a read permission *)
  Lemma lte_read_write ix pre :
    ixplens_read_perm_pre ix pre <= ixplens_write_perm_pre ix pre.
  Proof.
    constructor; intros.
    - apply H0.
    - apply H0.
    - inversion H0; reflexivity.
    - apply I.
  Qed.

  (* Read permissions are always separate *)
  Lemma ixplens_read_read_sep ix1 pre1 ix2 pre2 :
    ixplens_read_perm_pre ix1 pre1 ⊥ ixplens_read_perm_pre ix2 pre2.
  Proof.
    constructor; intros; inversion H1; reflexivity.
  Qed.

  (* Write permissions with different indices are separate *)
  Lemma ixplens_write_write_sep ix1 pre1 ix2 pre2 :
    ix1 <> ix2 -> ixplens_write_perm_pre ix1 pre1 ⊥ ixplens_write_perm_pre ix2 pre2.
  Proof.
    constructor; intros.
    - destruct H2 as [? | [? [elem ?]]]; subst; [ reflexivity | ].
      intro; symmetry; apply iGetPut_neq; assumption.
    - destruct H2 as [? | [? [elem ?]]]; subst; [ reflexivity | ].
      intro; symmetry; apply iGetPut_neq; try assumption.
      intro; subst; apply H; reflexivity.
  Qed.

  (* Write and read with different indices are separate *)
  Lemma ixplens_write_read_sep ix1 pre1 ix2 pre2 :
    ix1 <> ix2 -> ixplens_write_perm_pre ix1 pre1 ⊥ ixplens_read_perm_pre ix2 pre2.
  Proof.
    constructor; intros.
    - inversion H2; reflexivity.
    - destruct H2 as [? | [? [elem ?]]]; subst; [ reflexivity | ].
      intro; symmetry; apply iGetPut_neq; try assumption.
      intro; subst; apply H; reflexivity.
  Qed.


  (***
   *** Read and write permission sets
   ***)

  (* A value indicating whether an ixplens permission is a read or write *)
  Variant RWModality := Write | Read.

  (* A read or write permission whose contents equal a value *)
  Definition ixplens_perm_eq rw ix elem :=
    match rw with
    | Write => ixplens_write_perm_eq ix elem
    | Read => ixplens_read_perm_eq ix elem
    end.

  (* Dependent write permissions are permissions to write to ix along with
  permission P to the value that is currently stored at ix *)
  Definition ixplens_write_dep ix (P : Elem -> Perms) : Perms :=
    meet_Perms
      (fun R => exists elem,
           R = singleton_Perms (ixplens_write_perm_eq ix elem) * (P elem)).

  (* Dependent read permissions are permissions to read from ix along with
  permission P to the value that is currently stored at ix *)
  Definition ixplens_read_dep ix (P : Elem -> Perms) : Perms :=
    meet_Perms
      (fun R => exists elem,
           R = singleton_Perms (ixplens_read_perm_eq ix elem) * (P elem)).

  (* An ixplens permission that is either write or read *)
  Definition ixplens_dep rw ix P :=
    match rw with
    | Write => ixplens_write_dep ix P
    | Read => ixplens_read_dep ix P
    end.

  (* An alternate definition of ixplens_dep as a meet *)
  Definition ixplens_dep_alt rw ix P :=
    meet_Perms
      (fun R => exists elem,
           R = singleton_Perms (ixplens_perm_eq rw ix elem) * (P elem)).

  (* The two definitions of ixplens_dep are equal *)
  Lemma ixplens_dep_alt_eq rw ix P :
    ixplens_dep rw ix P ≡ ixplens_dep_alt rw ix P.
  Proof.
    destruct rw; reflexivity.
  Qed.

  (* The entailment rule for writing to a dependent write permission, which says
  that if you have write_dep perms to ix then putting elem to ix results in a
  write_dep permission whose contents equal elem *)
  Lemma ixplens_write_ent ix P elem :
    rewind (fun x => iput ix x elem) (ixplens_write_dep ix P)
      ⊨ ixplens_write_dep ix (fun e => prop_Perms (e = elem)).
  Proof.
    apply bigger_Perms_entails. repeat intro.
    simpl in H; destruct_ex_conjs H; subst.
    refine (lte_meet_Perms _ (singleton_Perms _) _ p H1).
    eexists; split; [ exists elem; reflexivity | ].
    rewrite (proj2 (prop_Perms_bottom _)); [ | reflexivity ].
    rewrite sep_conj_Perms_commut; rewrite sep_conj_Perms_bottom_identity.
    apply Proper_singleton_Perms.
    constructor; intros.
    - simpl in H0. destruct_ex_conjs H0; subst.
      exists elem. split; [ | reflexivity ].
      transitivity (iget ix (iput ix x3 elem)); [ | apply iGetPut_eq ].
      symmetry. eapply (rely_inc (ixplens_write_perm_eq ix x2) x0); try assumption.
      + rewrite <- lte_l_sep_conj_Perms in H3. apply H3.
      + rewrite iGetPut_eq. eapply Some_not_None; reflexivity.
    - rewrite <- lte_l_sep_conj_Perms in H3.
      apply (rely_inc (ixplens_write_perm_eq ix x2) x0); assumption.
    - rewrite <- lte_l_sep_conj_Perms in H3.
      apply (guar_inc (ixplens_write_perm_eq ix x2) x0); assumption.
    - rewrite <- lte_l_sep_conj_Perms in H3.
      apply (inv_inc (ixplens_write_perm_eq ix x2) x0); assumption.
  Qed.


  (* The entailment rule for reading a dependent lens permission, which says
  that if you have read_dep or write_dep permissions to ix with permissions P on
  the value contained at ix, then if you read from ix (resulting in a predicate
  pred that ensures the value at ix = elem) then you get back a read_dep or
  write_dep with a value equal to elem, to which you also have permissions P *)
  Lemma ixplens_read_ent rw ix P elem (pred : St -> Prop) :
    (forall x, pred x -> iget ix x = Some elem) ->
    add_poss_pre pred (ixplens_dep rw ix P)
      ⊨ ixplens_dep rw ix (fun e => prop_Perms (e = elem)) * P elem.
  Proof.
    intro. repeat rewrite ixplens_dep_alt_eq.
    apply add_poss_pre_meet_ent. intros. destruct H0; subst.
    etransitivity; [ apply add_pre_ent_P | ].
    unfold ixplens_dep_alt. rewrite sep_conj_Perms_meet_commute.
    eapply ent_meet_Perms.
    eexists; split; [ eexists; split; [ reflexivity | exists elem; reflexivity ] | ].
    assert (x0 = elem).
    1: { apply Perms_field_conj_elim in H1. destruct H1.
         apply Perms_field_singleton_elim in H0. destruct H0.
         unfold Perms_field in H1; simpl in H1.
         destruct rw; simpl in H0; destruct_ex_conjs H0; subst; rewrite (H _ H2) in H0;
         inversion H0; reflexivity. }
    erewrite (proj2 (prop_Perms_bottom _)); [ | reflexivity ]. subst.
    rewrite (sep_conj_Perms_commut _ bottom_Perms).
    rewrite sep_conj_Perms_bottom_identity.
    reflexivity.
  Qed.


  (***
   *** Multi-write permissions = allocation permission
   ***)

  (* The permission to write to any index in a set *)
  Program Definition ixplens_multi_write_perm (ixs : Ix -> Prop) : @perm St :=
    {|
      pre x := True;
      rely x y := forall ix, ixs ix -> iget ix x = iget ix y;
      guar x y :=
        clos_refl_trans _ (fun x' y' =>
                             exists ix elem, ixs ix /\ y' = iput ix x' elem) x y;
      inv x := True
    |}.
  Next Obligation.
    constructor; repeat intro.
    - reflexivity.
    - etransitivity; [ apply H | apply H0 ]; eassumption.
  Qed.

  (* multi_write_perm is monotone wrt set inclusion on ixs *)
  Lemma monotone_ixplens_multi_write_perm (ixs1 ixs2 : Ix -> Prop) :
    (forall ix, ixs1 ix -> ixs2 ix) ->
    ixplens_multi_write_perm ixs1 <= ixplens_multi_write_perm ixs2.
  Proof.
    constructor; repeat intro.
    - apply I.
    - apply H1. apply H. assumption.
    - clear H0. induction H1.
      + destruct H0 as [ix [elem [? ?]]]; subst.
        apply rt_step; exists ix; exists elem.
        split; [ apply H; assumption | reflexivity ].
      + reflexivity.
      + etransitivity; eassumption.
    - apply I.
  Qed.

  (* A multi-write permission is always separate from a write permission to an
  index not in the set of the multi-write *)
  Lemma ixplens_write_multi_write_sep ix pre ixs :
    ~ ixs ix -> self_contained_ixs ixs ->
    ixplens_write_perm_pre ix pre ⊥ ixplens_multi_write_perm ixs.
  Proof.
    intros not_in self_c; constructor; repeat intro.
    - clear H H0.
      assert (iget ix x = iget ix y /\ iget ix y <> None) as [? ?];
        [ | assumption ].
      induction H1.
      + destruct H as [ix' [elem [? ?]]]; subst.
        rewrite iGetPut_neq;
          [ split; [ reflexivity | assumption ] | | assumption ].
        intro; subst. apply (not_in H).
      + split; [ reflexivity | assumption ].
      + destruct (IHclos_refl_trans1 H2).
        destruct (IHclos_refl_trans2 H0).
        split; [ etransitivity | ]; eassumption.
    - destruct H1 as [? | [? [elem ?]]]; subst; [ reflexivity | ].
      symmetry; apply self_c; assumption.
  Qed.

  (* Helper lemma for ixplens_multi_write_split_write *)
  Lemma ixplens_multi_write_split_write_step ixs ix pre :
    self_contained_ixs ixs ->
    sep_step (ixplens_multi_write_perm (eq ix \1/ ixs))
      (ixplens_write_perm_pre ix pre ** ixplens_multi_write_perm ixs).
  Proof.
    intros; apply sep_step_rg; intros.
    - apply I.
    - clear H0. induction H1; [ | etransitivity; eassumption ].
      destruct H0.
      + destruct H0 as [? | [? [elem ?]]]; subst; [ reflexivity | ].
        apply rt_step; exists ix; exists elem.
        split; [ left | ]; reflexivity.
      + induction H0.
        * destruct H0 as [ix' [elem [? ?]]]; subst.
          apply rt_step. exists ix'; exists elem.
          split; [ right; assumption | reflexivity ].
        * reflexivity.
        * etransitivity; eassumption.
    - split.
      + intro. apply H1. left; reflexivity.
      + repeat intro. apply H1. right; assumption.
  Qed.

  (* A multi-write permission can be split into a write and a smaller
  multi-write by setting the value of the write permission, assuming the set of
  the smaller multi-write is self-contained *)
  Lemma ixplens_multi_write_split_write ixs ix elem :
    ~ ixs ix -> self_contained_ixs ixs ->
    rewind_perm (fun x => iput ix x elem)
      (ixplens_multi_write_perm (eq ix \1/ ixs))
      (ixplens_multi_write_perm (eq ix \1/ ixs))
      ⊢ ixplens_write_perm_eq ix elem ** ixplens_multi_write_perm ixs.
  Proof.
    intros; apply sep_step_entails_perm.
    - etransitivity; [ apply set_pre_sep_step
                     | apply ixplens_multi_write_split_write_step; assumption ].
    - intros.
      destruct H1 as [_ [y [_ [[z [? _]] ?]]]]; subst.
      split; [ split; [ | split ] | split ]; try apply I.
      + apply ixplens_write_multi_write_sep; assumption.
      + exists elem. split; [ | reflexivity ].
        rewrite <- (H2 ix); [ apply iGetPut_eq | left; reflexivity ].
  Qed.

  (* Multi-write permissions are separate from each other when their index sets
  are self-contained and disjoint *)
  Lemma ixplens_multi_write_multi_write_sep (ixs1 ixs2 : Ix -> Prop) :
    (forall ix, ixs1 ix -> ~ ixs2 ix) ->
    self_contained_ixs ixs1 -> self_contained_ixs ixs2 ->
    ixplens_multi_write_perm ixs1 ⊥ ixplens_multi_write_perm ixs2.
  Proof.
    intros disj self_c1 self_c2; constructor; repeat intro.
    - clear H H0. induction H1.
      + destruct H as [ix' [elem [? ?]]]. subst.
        symmetry; apply self_c1; [ | intro; eapply disj ]; eassumption.
      + reflexivity.
      + etransitivity; eassumption.
    - clear H H0. induction H1.
      + destruct H as [ix' [elem [? ?]]]. subst.
        symmetry; apply self_c2; [ | apply disj ]; assumption.
      + reflexivity.
      + etransitivity; eassumption.
  Qed.

  (* A multi-write permission can be split into two disjoint self-contained
  multi-write permissions; helper lemma *)
  Lemma ixplens_multi_write_split_sep (ixs1 ixs2 : Ix -> Prop) :
    (forall ix, ixs1 ix -> ~ ixs2 ix) ->
    self_contained_ixs ixs1 -> self_contained_ixs ixs2 ->
    sep_step (ixplens_multi_write_perm (ixs1 \1/ ixs2))
      (ixplens_multi_write_perm ixs1 ** ixplens_multi_write_perm ixs2).
  Proof.
    intros disj self_c1 self_c2; apply sep_step_rg; intros.
    - apply I.
    - clear H. induction H0; [ | etransitivity; eassumption ].
      destruct H; destruct H; try reflexivity.
      + destruct H as [ix [elem [? ?]]]. subst. apply rt_step.
        eexists; eexists; split; [ left; eassumption | reflexivity ].
      + transitivity y; (eapply guar_inc;
                         [ eapply monotone_ixplens_multi_write_perm | apply I
                         | try (apply H); apply H0 ]);
          intros; left; assumption.
      + destruct H as [ix [elem [? ?]]]. subst. apply rt_step.
        eexists; eexists; split; [ right; eassumption | reflexivity ].
      + transitivity y; (eapply guar_inc;
                         [ eapply monotone_ixplens_multi_write_perm | apply I
                         | try (apply H); apply H0 ]);
          intros; right; assumption.
    - split; repeat intro; apply H0; [ left | right ]; assumption.
  Qed.

  (* A multi-write permission can be split into two disjoint self-contained
  multi-write permissions *)
  Lemma ixplens_multi_write_split (ixs1 ixs2 : Ix -> Prop) :
    (forall ix, ixs1 ix -> ~ ixs2 ix) ->
    self_contained_ixs ixs1 -> self_contained_ixs ixs2 ->
    ixplens_multi_write_perm (ixs1 \1/ ixs2)
      ⊢ ixplens_multi_write_perm ixs1 ** ixplens_multi_write_perm ixs2.
  Proof.
    intros; apply sep_step_entails_perm.
    - apply ixplens_multi_write_split_sep; assumption.
    - intros. split; [ | simpl; trivial ].
      split; [ | split ]; try apply I.
      apply ixplens_multi_write_multi_write_sep; assumption.
  Qed.

End PLensPerms.
