
From Coq Require Import
         Lists.List.

From ITree Require Import
     ITree
     ITreeFacts.

From Heapster Require Import
     Utils
     Permissions
     Lifetime
     SepStep
     Typing
     PermType
     LensPerms.

Import ITreeNotations.
Import ListNotations.
Local Open Scope itree_scope.


Section PLensTypes.
  Context {Si Ss Ix Elem : Type} {IxPLens:IxPartialLens Ix Si Elem}.


  (***
   *** The permission type associated with an indexed partial lens
   ***)

  Definition ixplensTp {Bs} rw (T : @PermType Si Ss Elem Bs) : PermType Ix Bs :=
    mkPermType (fun ix bs => ixplens_dep rw ix (fun elem => ptApp T elem bs)).

  (* To extract a spec from an implementation that performs a read using
  permission type ixplensTp rw T, we extract a spec from the rest of the
  implementation using permission type T on the value read *)
  Lemma ixplensRead Bs Ri Rss T (U : PermType Ri Rss) rw ix (bs : tuple Bs) ti ts :
    (forall elem,
        (ix :: ixplensTp rw (eqTp elem) ▷ tt * elem :: T ▷ bs)
          ⊢ ti elem ⤳ ts ::: U) ->
    ix :: ixplensTp rw T ▷ bs ⊢ (elem <- readIx ix;; ti elem) ⤳ ts ::: U.
  Proof.
    intro.
    rewrite <- (bind_ret_l tt (fun x => ts)).
    eapply typing_bind; [ | intros; apply H ].
    unfold readIx. rewrite <- (bind_ret_l tt (fun x => Ret tt)).
    eapply typing_bind; [ apply typing_read_L | ]. intros. simpl.
    rewrite (ixplens_read_ent _ _ _ (iget ix r1));
      [ | intros; destruct x; subst; reflexivity ].
    apply typing_meet. intros.
    destruct H0 as [elem [? ?]]; subst.
    rewrite H0. simpl. apply typing_ret. reflexivity.
  Qed.

  (* To extract a spec from an implementation that performs a write using
  permission type ixplensTp Write T, we extract a spec from the rest of the
  implementation using permission type eqTp elem on the value written *)
  Lemma ixplensWrite Bs Ri Rss T (U : PermType Ri Rss) ix elem (bs : tuple Bs) ti ts :
    ix :: ixplensTp Write (eqTp elem) ▷ tt ⊢ ti ⤳ ts ::: U ->
    ix :: ixplensTp Write T ▷ bs ⊢ (_ <- setIx ix elem;; ti) ⤳ ts ::: U.
  Proof.
    intro.
    rewrite <- (bind_ret_l tt (fun x => ts)).
    eapply typing_bind; [ | intros; apply H ].
    unfold setIx.
    eapply typing_entails; [ apply typing_update_L | reflexivity | ]; intros.
    - simpl in H0. destruct_ex_conjs H0; subst.
      rewrite <- lte_l_sep_conj_Perms in H4. simpl in H4.
      apply H4; [ assumption | ]. right. split; [ reflexivity | ].
      eapply pre_inc in H2; try eassumption. destruct H2 as [elem' [? ?]]; subst.
      split; [ eapply Some_not_None; eassumption | ].
      eexists. destruct c12. simpl. reflexivity.
    - simpl. rewrite <- ixplens_write_ent.
      apply bigger_Perms_entails.
      eapply Proper_lte_rewind.
      + repeat intro. reflexivity.
      + reflexivity.
  Qed.


  (***
   *** The allocation permission type
   ***)

  Context {IxA:@IxAlloc _ _ _ IxPLens}.

  (* The allocation permission type relates the unit implementation value to no
  specification values *)
  Definition ixplensAllocTp : @PermType0 Si Ss unit :=
    mkPermType0 (fun _ => ixplens_alloc).

  (* To extract a spec from an implementation starting with an allocation,
  perform extraction for the rest of the implementation after the allocation
  using an arbitrary index for the allocated index *)
  Lemma ixplensAlloc elem Ri Rss ti ts (U : PermType Ri Rss) :
    (forall ix, (ix :: ixplensTp Write (eqTp elem) ▷ tt * tt :: ixplensAllocTp ▷ tt)
                  ⊢ ti ix ⤳ ts ::: U) ->
    tt :: ixplensAllocTp ▷ tt ⊢ (ix <- allocIx elem;; ti ix) ⤳ ts ::: U.
  Proof.
    intro. unfold allocIx. simpl.
    rewrite <- (bind_ret_l tt (fun _ => ts)).
    eapply typing_bind; [ | intros; apply H ]. simpl.
    rewrite <- (bind_ret_l tt (fun _ => Ret tt)).
    eapply typing_bind; [ apply typing_read_L | ]. intros. simpl.
    rewrite (ixplens_alloc_read_ent _ (ialloc r1));
      [ | intros; subst; reflexivity ].
    rewrite <- (bind_ret_l tt (fun _ => Ret tt)).
    eapply typing_bind; [ apply typing_update_L | ].
    - intros. simpl in H0. apply H0; [ assumption | ].
      apply Relation_Operators.rt_step.
      exists (ialloc r1); exists elem. split; [ reflexivity | ].
      unfold map_pair_L. cbn. f_equal.
    - intros. apply typing_ret.
      etransitivity; [ | eapply ixplens_alloc_write_ent ].
      apply bigger_Perms_entails. eapply Proper_lte_rewind; [ | reflexivity ].
      intro. reflexivity.
  Qed.

End PLensTypes.
