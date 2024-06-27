
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
