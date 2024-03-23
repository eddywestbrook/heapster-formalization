(* begin hide *)
From Coq Require Import
     Classes.Morphisms
     Classes.RelationClasses
     Lists.List
     Relations.Relation_Operators
     Relations.Operators_Properties.
(* end hide *)


(*** Helper lemmas for clos_trans ***)

Global Instance Reflexive_clos_trans {A} R `{Reflexive A R} : Reflexive (clos_trans A R).
Proof.
  intro. left. reflexivity.
Qed.

Global Instance Transitive_clos_trans {A} R : Transitive (clos_trans A R).
Proof.
  repeat intro. eapply t_trans; eassumption.
Qed.

Global Instance PreOrder_clos_trans {A} R `{Reflexive A R} : PreOrder (clos_trans A R).
Proof.
  constructor; typeclasses eauto.
Qed.

Lemma clos_trans_trans {A} R `{Transitive A R} x y :
  clos_trans A R x y <-> R x y.
Proof.
  split; intro.
  - induction H0; eauto.
  - left; assumption.
Qed.

(* Helper lemma: clos_trans preserves anything preserved by a single step *)
Lemma clos_trans_preserves {A} (pred:A -> Prop) (R : A -> A -> Prop) :
  (forall x y, pred x -> R x y -> pred y) ->
  forall x y, pred x -> clos_trans _ R x y -> pred y.
Proof.
  intros. revert H0; induction H1; intros.
  - eapply H; eassumption.
  - apply IHclos_trans2; apply IHclos_trans1; assumption.
Qed.

Lemma clos_trans_incl {A} (R S : A -> A -> Prop)
  (incl : forall x y, R x y -> S x y) x y :
  clos_trans A R x y -> clos_trans A S x y.
Proof.
  intro H; induction H.
  - left; apply incl; assumption.
  - eapply t_trans; eassumption.
Qed.

Lemma clos_trans_or_l {A} R S x y : clos_trans A R x y ->
                                    clos_trans A (fun x' y' => R x' y' \/ S x' y') x y.
Proof.
  apply clos_trans_incl. intros. left; assumption.
Qed.

Lemma clos_trans_or_r {A} R S x y : clos_trans A S x y ->
                                    clos_trans A (fun x' y' => R x' y' \/ S x' y') x y.
Proof.
  apply clos_trans_incl. intros. right; assumption.
Qed.

Lemma clos_trans_or_commut {A} R S x y :
  clos_trans A (fun x' y' => R x' y' \/ S x' y') x y <->
    clos_trans A (fun x' y' => S x' y' \/ R x' y') x y.
Proof.
  split; apply clos_trans_incl; intros; repeat destruct H; auto.
Qed.

Lemma clos_trans_or_assoc {A} R S T x y :
  clos_trans A (fun x' y' => R x' y' \/ (S x' y' \/ T x' y')) x y <->
    clos_trans A (fun x' y' => (R x' y' \/ S x' y') \/ T x' y') x y.
Proof.
  split; apply clos_trans_incl; intros; repeat destruct H; auto.
Qed.

Lemma clos_trans_clos_trans_or {A} R S x y :
  clos_trans A (fun x' y' => clos_trans A R x' y' \/ S x' y') x y <->
    clos_trans A (fun x' y' => R x' y' \/ S x' y') x y.
Proof.
  split; intro H.
  - induction H; [ destruct H | ].
    + apply clos_trans_or_l; assumption.
    + left; right; assumption.
    + etransitivity; eassumption.
  - induction H; [ destruct H | ].
    + left; left; left; assumption.
    + left; right; assumption.
    + etransitivity; eassumption.
Qed.

Lemma clos_trans_eq_or {A} R `{Reflexive A R} x y :
  clos_trans A (fun x' y' => x' = y' \/ R x' y') x y <->
  clos_trans A R x y.
Proof.
  split; apply clos_trans_incl; intros.
  - destruct H0; [ subst; reflexivity | assumption ].
  - right; assumption.
Qed.


Section Permissions.
  (** This entire file is parameterized over some state type. *)
  Context {config : Type}.

  (** * Rely-guarantee permissions *)
  Record perm : Type :=
    {
      inv : config -> Prop;
      (** The rely: the updates this permission allows of others. *)
      rely : config -> config -> Prop;
      rely_PO : PreOrder rely;
      (** The guarantee: the updates that this permission allows. *)
      guar : config -> config -> Prop;
      guar_PO : PreOrder guar;
      (** The precondition on configs. *)
      pre : config -> Prop;
      pre_respects : forall x y, rely x y -> pre x -> pre y;

      inv_rely : forall x y, rely x y -> inv x -> inv y;
      inv_guar : forall x y, guar x y -> inv x -> inv y;
    }.

  (* begin hide *)
  Hint Unfold rely : core.
  Hint Unfold pre : core.
  Hint Unfold guar : core.
  Hint Resolve pre_respects : core.

  Global Instance rely_is_preorder p : PreOrder (rely p) := rely_PO p.
  Global Instance guar_is_preorder p : PreOrder (guar p) := guar_PO p.
  (* end hide *)

  Program Definition restrict (p : perm) (sp : config -> Prop) : perm :=
    {|
      rely := fun x y => x = y \/
                        (sp x /\ sp y /\ rely p x y);
      guar := fun x y => x = y \/
                        (sp x /\ sp y /\ guar p x y);
      pre := fun x => sp x /\ pre p x;
      inv := fun x => sp x /\ inv p x;
    |}.
  Next Obligation.
    constructor.
    - intro . left. reflexivity.
    - intros ? ? ? ? ?. destruct H, H0; subst; auto.
      right. destruct H as (? & ? & ?), H0 as (? & ? & ?). split; [| split]; auto.
      etransitivity; eauto.
  Qed.
  Next Obligation.
    constructor; repeat intro.
    - left; auto.
    - destruct H, H0; subst; intuition.
      right. split; [| split]; auto. etransitivity; eauto.
  Qed.
  Next Obligation.
    destruct H; subst; auto. destruct H as (? & ? & ?).
    split; auto. eapply pre_respects; eauto.
  Qed.
  Next Obligation.
    destruct H; subst; auto. destruct H as (? & ? & ?).
    split; auto. eapply inv_rely; eauto.
  Qed.
  Next Obligation.
    destruct H; subst; auto. destruct H as (? & ? & ?).
    split; auto. eapply inv_guar; eauto.
  Qed.


  (** ** Permission ordering *)
  (* Bigger permission has a smaller invariant precondition, and rely, and a
     bigger guarantee, where the last three comparisons are relativized to the
     smaller invariant *)
  Record lte_perm (p q: perm) : Prop :=
    {
      pre_inc : forall x, inv q x -> pre q x -> pre p x;
      rely_inc : forall x y, inv q x -> rely q x y -> rely p x y;
      guar_inc : forall x y, inv q x -> guar p x y -> guar q x y;
      inv_inc : forall x, inv q x -> inv p x;
    }.


  (*
  (* Bigger permission has smaller pre and rely. Bigger inv and guar *)
  Record lte_perm (p q: perm) : Prop :=
    {
      pre_inc : forall x, inv p x ->
                     pre q x -> pre p x;
      rely_inc : forall x y, inv p x ->
                        inv p y ->
                        rely q x y -> rely p x y;

      guar_inc : forall x y, inv p x ->
                        (* inv q y -> (* TODO: NEW *) *)
                        guar p x y -> guar q x y;
      inv_inc : forall x, inv p x -> inv q x;
    }.

  Record lte_perm' (p q: perm) : Prop :=
    {
      pre_inc' : forall x, inv p x ->
                     pre q x -> pre p x;
      rely_inc' : forall x y, inv p x ->
                        inv p y ->
                        rely q x y -> rely p x y;

      guar_inc' : forall x y, inv p x ->
                        (* inv q y -> (* TODO: NEW *) *)
                        guar p x y -> guar q x y;
      inv_inc' : inv p = inv q;
    }.

  (* permissions must preserve inv *)
  Record lte_perm'' (p q: perm) : Prop :=
    {
      pre_inc'' : pre p = pre q;
      rely_inc'' : rely p = rely q;
      guar_inc'' : guar p = guar q;
      inv_inc'' : forall x, inv p x -> inv q x;
    }.
   *)

  (* Lemma lte_restrict p q (sp1 sp2 : config -> Prop) : *)
  (*   (forall x, sp1 x -> sp2 x) -> *)
  (*   lte_perm (restrict p sp1) q -> *)
  (*   lte_perm (restrict p sp2) q. *)
  (* Proof. *)
  (*   intros. destruct H0. *)
  (*   constructor; intros; cbn in *; auto. *)
  (*   - split; [apply H |]; apply pre_inc0; auto. *)
  (*   - destruct H0. apply H; auto. *)
  (*   - destruct H1 as [| (? & ? & ?)]. subst; reflexivity. destruct H0. apply H; auto. *)
  (*   - destruct H0. right. split; [| split]; auto. *)
  (*     + apply H. *)
  (*   - *)
  (* Qed. *)

  (* Definition lte_perm' (p q : perm) : Prop := *)
  (*   (* (forall x, inv q x -> inv p x) /\ (* inv of q ⊆ inv p, same as spred_inc. unnecessary. implied by the next clause *) *) *)
  (*     lte_perm (restrict p (inv q)) q. (* (p with the smaller inv of q) <= q *) *)

  (* lte_perm' := spred_inc /\ lte_perm (restrict p (spred q)) q. *)

  (* begin hide *)
  Hint Resolve pre_inc : core.
  Hint Resolve rely_inc : core.
  Hint Resolve guar_inc : core.
  (* end hide *)

  Notation "p <= q" := (lte_perm p q).

  Global Instance lte_perm_is_PreOrder : PreOrder lte_perm.
  Proof.
    constructor; [ constructor; auto | constructor; intros ]; eauto.
    - apply H; auto; apply H0; auto; apply H; auto.
    - apply H; auto; apply H0; auto; apply H; auto.
    - apply H0; auto. apply H; auto; apply H0; auto.
    - apply H; apply H0; assumption.
  Qed.

  (*
  Global Instance lte_perm'_is_PreOrder : PreOrder lte_perm'.
  Proof.
    constructor; repeat intro.
    - constructor; intros; cbn in *; eauto.
      + right. split; auto. split; auto. eapply inv_rely; eauto.
      + destruct H1; [subst; reflexivity |].
        destruct H1 as (? & ? & ?). auto.
    (* - constructor; intros; cbn in *. *)
    - destruct H, H0. cbn in *.
      split; cbn; intros.
      + split; auto. apply pre_inc0; auto. apply inv_inc1; auto. apply pre_inc1; auto.
      + rename x0 into c, y0 into c'. destruct (rely_inc0 c c'); auto.
        apply inv_inc1; auto.
        { destruct (rely_inc1 c c'); auto. subst. reflexivity. apply H1. }
        destruct H1 as (? & ? & ?).
        right. split; [| split]; auto. eapply inv_rely; eauto.
      + rename x0 into c, y0 into c'. destruct H1; auto.
        destruct H1 as (? & ? & ?). apply guar_inc1; auto.
        right. split; [| split]; auto. apply guar_inc0; auto.
        apply inv_inc1; auto.
        apply inv_inc1; auto.
        right. split; [| split]; auto.
        apply inv_inc1; auto.
        apply inv_inc1; auto.
      + split; auto. apply inv_inc0. apply inv_inc1; auto.
  Qed.
   *)

  (** Equality of permissions = the symmetric closure of the ordering. *)
  Definition eq_perm p q : Prop := p <= q /\ q <= p.

  Notation "p ≡≡ q" := (eq_perm p q) (at level 50).

  Lemma eq_perm_lte_1 : forall p q, p ≡≡ q -> p <= q.
  Proof. intros p q []. auto. Qed.
  Lemma eq_perm_lte_2 : forall p q, p ≡≡ q -> q <= p.
  Proof. intros p q []. auto. Qed.

  (* begin hide *)
  Hint Unfold eq_perm : core.
  Hint Resolve eq_perm_lte_1 : core.
  Hint Resolve eq_perm_lte_2 : core.
  (* end hide *)

  (*
  Global Instance Proper_eq_perm_rely :
    Proper (eq_perm ==> eq ==> eq ==> Basics.flip Basics.impl) rely.
  Proof.
    repeat intro. subst. (* apply H; auto. *)
  Abort.

  Global Instance Proper_eq_perm_guar :
    Proper (eq_perm ==> eq ==> eq ==> Basics.flip Basics.impl) guar.
  Proof.
    repeat intro. subst. apply H; auto.
    admit.
    cbn.
  Abort.

  Global Instance Proper_eq_perm_pre :
    Proper (eq_perm ==> eq ==> Basics.flip Basics.impl) pre.
  Proof.
    repeat intro. subst. apply H; auto.
  Abort.
   *)

  Global Instance Proper_lte_perm_inv :
    Proper (lte_perm ==> eq ==> Basics.flip Basics.impl) inv.
  Proof.
    repeat intro. subst. apply H; auto.
  Qed.

  (* Unnecessary? *)
  (* Global Instance Proper_eq_perm_inv : *)
  (*   Proper (eq_perm ==> eq ==> Basics.flip Basics.impl) inv. *)
  (* Proof. *)
  (*   repeat intro. subst. destruct H. apply H; auto. *)
  (* Qed. *)

  Global Instance eq_perm_is_Equivalence : Equivalence eq_perm.
  Proof.
    constructor.
    - intro. split; reflexivity.
    - intros x y []. split; auto.
    - intros x y z [] []. split; etransitivity; eauto.
  Qed.

  (* Lemma restrict_same p : *)
  (*   restrict p (inv p) ≡≡ p. *)
  (* Proof. *)
  (*   split; constructor; cbn; intros; auto. *)
  (*   - right. split; [| split]; auto. eapply inv_rely; eauto. *)
  (*     right. split; [| split]; auto. eapply inv_rely; eauto. *)
  (*   - destruct H1; subst; [reflexivity |]. *)
  (*     destruct H1 as (? & ? & ?). *)
  (*     destruct H3; subst; [reflexivity | apply H3]. *)
  (*   - split; auto. apply H0. *)
  (*   - destruct H0; auto. right. destruct H0 as (? & ? & ?). *)
  (*     split; [| split]; auto. *)
  (*   - destruct H1; auto. right. destruct H1 as (? & ? & ?). destruct H, H2. *)
  (*     split; [| split]; auto. *)
  (*   - destruct H. split; auto. *)
  (* Qed. *)

  (* Lemma restrict_same' p : *)
  (*   lte_perm (restrict p (inv p)) p. *)
  (* Proof. *)
  (*   split; intros. *)
  (*   - cbn. split; auto. *)
  (*   - cbn. right. split; [| split]; auto. eapply inv_rely; eauto. *)
  (*   - cbn in H1. destruct H1; subst. reflexivity. *)
  (*     apply H1. *)
  (*   - cbn. split; auto. *)
  (* Qed. *)

  (* Lemma restrict_same'' p : *)
  (*   lte_perm p (restrict p (inv p)). *)
  (* Proof. *)
  (*   split; intros. *)
  (*   - cbn in *. apply H0. *)
  (*   - cbn in H0. destruct H0; subst. reflexivity. *)
  (*     apply H0. *)
  (*   - cbn in *. destruct H. right. split; [| split]; auto. eapply inv_guar; eauto. *)
  (*   - cbn in H. apply H. *)
  (* Qed. *)

  Lemma eq_perm_inv p q :
    p ≡≡ q ->
    forall x, inv p x <-> inv q x.
  Proof.
    split; intros; apply H; auto.
  Qed.

  Lemma eq_perm_pre p q :
    p ≡≡ q ->
    forall x, inv q x ->
         (pre p x <-> pre q x).
  Proof.
    split; intros.
    - apply H; auto. rewrite eq_perm_inv in H0; eauto.
    - apply H; auto.
  Qed.

  (* Global Instance Proper_eq_perm_lte_perm' : *)
  (*   Proper (eq_perm ==> eq_perm ==> Basics.flip Basics.impl) lte_perm'. *)
  (* Proof. *)
  (*   repeat intro. *)
  (*   destruct H, H0. etransitivity; eauto. etransitivity; eauto. *)
  (* Qed. *)

  (*

  Lemma restrict_unneeded1 p q : lte_perm p q -> lte_perm' p q.
  Proof.
    intros. red. constructor; intros; cbn.
    - split; auto. apply H; auto.
    - right. split; [| split]; auto.
      eapply inv_rely; eauto.
      apply H; auto.
    - destruct H2; [subst; reflexivity |]. destruct H2 as (? & ? & ?).
      apply H; auto.
    - split; auto. apply H; auto.
  Qed.

  Lemma restrict_unneeded2 p q : lte_perm' p q -> lte_perm p q.
  Proof.
    intros. red in H. constructor; intros; try solve [apply H; auto].
    - destruct H. cbn in *.
      edestruct rely_inc0; eauto; [subst; reflexivity |].
      apply H.
    - destruct H. cbn in *.
      (* specialize (inv_inc0 _ H0). destruct inv_inc0 as (_ & ?). *)
      apply guar_inc0; auto.
      (* right. *)
      (* split; [| split]; auto. *)
      (* eapply inv_guar; eauto. apply H; auto. cbn. right.split; auto. *)
  Qed.

   *)

  Global Instance Proper_eq_perm_lte_perm :
    Proper (eq_perm ==> eq_perm ==> Basics.flip Basics.impl) lte_perm.
  Proof.
    intros p p' H q q' H0 Hlte.
    etransitivity; eauto.
    etransitivity; eauto.
  Qed.


  (** Other lattice definitions. *)
  Program Definition bottom_perm : perm :=
    {|
      pre := fun x => True;
      rely := fun x y => True;
      guar := fun x y => x = y;
      inv := fun x => True;
    |}.
  Next Obligation.
    constructor; repeat intro; subst; auto.
  Qed.

  Lemma bottom_perm_is_bottom : forall p, bottom_perm <= p.
  Proof.
    constructor; simpl; intros; subst; intuition.
  Qed.

  Program Definition top_perm : perm :=
    {|
      pre := fun x => False;
      rely := fun x y => x = y;
      guar := fun x y => True;
      inv := fun x => False;
    |}.
  Next Obligation.
    constructor; repeat intro; subst; auto.
  Qed.

  Lemma top_perm_is_top : forall p, p <= top_perm.
  Proof.
    constructor; simpl; repeat intro; subst; intuition.
  Qed.

  Ltac respects := eapply pre_respects; eauto.

  (* The permission with only an invariant, that is otherwise bottom *)
  Program Definition invperm phi : perm :=
    {|
      pre := fun x => True;
      rely := fun x y => phi x -> phi y;
      guar := fun x y => x = y;
      inv := phi;
    |}.
  Next Obligation.
    constructor; repeat intro; subst; auto.
  Qed.

  (* A stronger predicate gives a stronger invperm *)
  Lemma lte_invperm (pred1 pred2 : config -> Prop) :
    (forall x, pred1 x -> pred2 x) -> invperm pred2 <= invperm pred1.
  Proof.
    constructor; simpl; intros; auto.
  Qed.


  (*
  Program Definition join_perm' (ps: perm -> Prop) (H: exists p, ps p) : perm :=
    {|
      pre := fun x => forall p, ps p -> pre p x;
      rely := fun x y => forall p, ps p -> rely p x y;
      guar  := clos_trans _ (fun x y => exists p, ps p /\ guar p x y);
      spred := fun x => forall p, ps p -> spred p x;
    |}.
  Next Obligation.
    constructor; repeat intro.
    - reflexivity.
    - etransitivity; eauto.
  Qed.
  Next Obligation.
    constructor.
    - constructor. eexists. split. apply H0. reflexivity.
    - repeat intro. econstructor 2; eauto.
  Qed.
  Next Obligation.
    respects.
  Qed.
  Next Obligation.
    eapply spred_rely; eauto.
  Qed.
  Next Obligation.
    induction H0.
    - destruct H0 as (? & ? & ?).

      eapply spred_guar. apply H4. ; eauto.

  Qed.

  Lemma lte_join_perm' (ps : perm -> Prop) p (H : ps p) :
      p <= join_perm' ps (ex_intro _ p H).
  Proof.
    constructor; cbn; intros; auto.
    constructor 1. eexists. split; eauto.
    exists p. split; auto.
  Qed.

  Lemma join_perm'_min (ps : perm -> Prop) (H : exists p, ps p) r :
      (forall p, ps p -> p <= r) ->
      join_perm' ps H <= r.
  Proof.
    intros Hlte. constructor; cbn; intros; auto.
    - apply Hlte; auto.
    - apply Hlte; auto.
    - induction H0; auto.
      + destruct H0 as (p' & ? & ?). eapply Hlte; eauto.
      + transitivity y; auto.
    - destruct H0. eapply Hlte; apply H0.
  Qed.
*)

  (*
  Program Definition join_perm (p q: perm) : perm :=
    {|
      pre := fun x => pre p x /\ pre q x;
      rely := fun x y => rely p x y /\ rely q x y;
      guar := fun x y =>
                (clos_trans _ (fun x y => (guar p x y \/ guar q x y) /\
                                         (* Needed for inv_guar to hold *)
                                         (inv p x -> inv p y) /\
                                         (inv q x -> inv q y)) x y);
      inv := fun x => inv p x /\ inv q x;
    |}.
  Next Obligation.
    constructor; repeat intro.
    - split; reflexivity.
    - destruct H. destruct H0. split; etransitivity; eauto.
  Qed.
  Next Obligation.
    constructor.
    - left. split; [| split]; auto. left. reflexivity.
    - repeat intro.
      (* destruct H, H0; subst; auto. right. *)
      (* destruct H as (? & ? & ?), H0 as (? & ? & ?). *)
      (* split; [| split]; auto. *)
      (*  destruct H2, H4. *)
      destruct H, H0.
      + econstructor 2; constructor; eauto.
      + econstructor 2. left. apply H. econstructor 2; eauto.
      + econstructor 2; eauto. econstructor 2; eauto. left. apply H0.
      + repeat (econstructor 2; eauto).
  Qed.
  Next Obligation.
    split; respects.
  Qed.
  Next Obligation.
    split; eapply inv_rely; eauto.
  Qed.
  Next Obligation.
    revert H0 H1.
    induction H; intros; auto. split; apply H; auto.
    apply IHclos_trans2; apply IHclos_trans1; auto.
  Qed.

  Lemma lte_l_join_perm : forall p q,
      p <= join_perm p q.
  Proof.
    intros. constructor; cbn; auto.
    - intros ? _ [? _]; auto.
    - intros x y [] []; auto.
    - intros x y [] [] ?.
      constructor; auto.
    - intros x []; auto.
  Qed.

  Lemma lte_r_join_perm : forall p q,
      q <= join_perm p q.
  Proof.
    intros. constructor; cbn; auto.
    - intros ? _ [_ ?]; auto.
    - intros x y [] []; auto.
    - intros x y [] [] ?.
      constructor; auto.
    - intros x []; auto.
  Qed.

  Lemma join_perm_min : forall p q r,
      p <= r ->
      q <= r ->
      join_perm p q <= r.
  Proof.
    intros p q r ? ?. constructor; intros; cbn; auto.
    - split; [apply H | apply H0]; auto.
    - split; [apply H | apply H0]; auto.
    - cbn in H3. revert H1 H2. induction H3; intros.
      (* destruct H3. subst; reflexivity. *)
      (* destruct H3 as (? & ? & ?). *)
      (* revert H1 H2 H3 H4. *)
      (* induction H5; intros; auto. *)
      + destruct H1. destruct H1; [apply H | apply H0]; auto.
      + (* destruct H. apply inv_inc0 in H1. *)
        assert (inv r y).
        {
          clear IHclos_trans1 IHclos_trans2.

  (*         apply H *)
  (*       } *)
  (*       etransitivity; eauto. *)
  (* Qed. *)
  Abort.

  Lemma join_perm_commut' : forall p q,
      join_perm p q <= join_perm q p.
  Proof.
    constructor.
    - intros ? ? []. split; auto.
    - intros x y ? []. repeat split; auto.
    - intros. induction H1.
      + destruct H1 as (? & ? & ?); constructor; auto.
        split; [| split]; auto. destruct H1; auto.
      + etransitivity; eauto. apply IHclos_trans1; auto.
        admit.
        apply IHclos_trans2; auto. admit.
    - intros ? []; split; auto.
  Admitted.

  Lemma join_perm_commut : forall p q,
      join_perm p q ≡≡ join_perm q p.
  Proof.
    split; apply join_perm_commut'.
  Qed.

  (*
  Lemma join_perm_assoc : forall p q r,
      join_perm p (join_perm q r) ≡≡ join_perm (join_perm p q) r.
  Proof.
    split; intros.
    {
      constructor.
      - intros x [[? ?] ?]. split; [| split]; auto.
      - intros x y [[] ?].
        repeat split; auto.
      - intros. induction H; try solve [etransitivity; eauto].
        destruct H.
        + constructor. left. constructor. left. auto.
        + induction H; try solve [etransitivity; eauto].
          destruct H.
          * constructor. left. constructor. right. auto.
          * constructor. right. auto.
      - intros ? [? | [? | ?]].
        + left. left. auto.
        + left. right. auto.
        + right. auto.
    }
    {
      constructor.
      - intros x [? [? ?]]. split; [split |]; auto.
      - intros x y [? []].
        repeat split; auto.
      - intros. induction H; try solve [etransitivity; eauto].
        destruct H.
        + induction H; try solve [etransitivity; eauto].
          destruct H.
          * constructor. left. auto.
          * constructor. right. constructor. left. auto.
        + constructor. right. constructor. right. auto.
      - intros ? [[? | ?] | ?].
        + left. auto.
        + right. left. auto.
        + right. right. auto.
    }
  Qed.

  Lemma join_perm_idem : forall p, join_perm p p ≡≡ p.
  Proof.
    split; intros.
    - constructor; intros.
      + split; auto.
      + repeat split; auto.
      + induction H; try solve [etransitivity; eauto].
        destruct H; auto.
      + destruct H; auto.
    - constructor.
      + intros ? [? _]; auto.
      + intros x y []. auto.
      + constructor. auto.
      + left; auto.
  Qed.

  Definition meet_rely p q := clos_trans _ (fun x y => (rely p x y) \/ (rely q x y)).

  Program Definition meet_perm (p q:perm) : perm :=
    {|
    pre := fun x => pre p x \/ pre q x \/ exists y, (pre p y \/ pre q y) /\ meet_rely p q y x;
    rely := meet_rely p q;
      guar  := fun x y => guar p x y /\ guar q x y;
      spred := fun x => spred p x /\ spred q x;
    |}.
  Next Obligation.
    constructor; repeat intro.
    - constructor. left. reflexivity.
    - econstructor 2; eauto.
  Qed.
  Next Obligation.
    constructor.
    - constructor; reflexivity.
    - intros x y z [] []. split; etransitivity; eauto.
  Qed.
  Next Obligation.
    induction H; auto.
    destruct H0 as [? | [? | [z [? ?]]]].
    - destruct H; try solve [left; respects].
      right; right. exists x. split; auto. constructor 1. auto.
    - destruct H; try solve [right; left; respects].
      right; right. exists x. split; auto. constructor 1. auto.
    - destruct H; right; right; exists z; split; auto;
        econstructor 2; eauto; constructor 1; auto.
  Qed.

  Lemma lte_meet_perm_l : forall p q,
      meet_perm p q <= p.
  Proof.
    intros. constructor; simpl; auto.
    - left; auto.
    - intros x y []; auto.
  Qed.
  Lemma lte_meet_perm_r : forall p q,
      meet_perm p q <= q.
  Proof.
    intros. constructor; simpl; auto.
    - left; auto.
    - intros x y []; auto.
  Qed.
  Lemma meet_perm_max : forall p q r,
      r <= p ->
      r <= q ->
      r <= meet_perm p q.
  Proof.
    intros p q r [] []. constructor; intros; simpl; auto.
    - simpl in H. destruct H as [? | [? | [? [? ?]]]]; auto.
      induction H0.
      + destruct H, H0; respects.
      + apply IHclos_trans1 in H.
        clear IHclos_trans1 IHclos_trans2 H0_.
        induction H0_0; auto.
        destruct H0; respects.
    - induction H.
      + destruct H; auto.
      + etransitivity; eauto.
  Qed.
   *)

(* Lemma meet_perm_commut: forall p q, meet_perm p q ≡ meet_perm q p. *)
(* Proof. *)
(*   split; intros. *)
(*   - constructor; intros. *)
(*     + destruct H as [? [? ?]]. *)
(*     + induction H. *)
(*       * destruct H; constructor; auto. *)
(*       * etransitivity; eauto. *)
(*     + destruct H. constructor; auto. *)
(*   - constructor; intros. *)
(*     + induction H. *)
(*       * destruct H; constructor; auto. *)
(*       * etransitivity; eauto. *)
(*     + destruct H. constructor; auto. *)
(* Qed. *)

(* Lemma meet_perm_assoc : forall p q r, *)
(*     eq_perm (meet_perm p (meet_perm q r)) (meet_perm (meet_perm p q) r). *)
(* Proof. *)
(*   split; intros. *)
(*   - constructor; intros. *)
(*     + induction H; try solve [etransitivity; eauto]. *)
(*       destruct H. *)
(*       * induction H; try solve [etransitivity; eauto]. *)
(*         destruct H. *)
(*         -- constructor. left. auto. *)
(*         -- constructor. right. constructor. left. auto. *)
(*       * constructor. right. constructor. right. auto. *)
(*     + destruct H as [? [? ?]]. *)
(*       constructor; auto. constructor; auto. *)
(*   - constructor; intros. *)
(*     + induction H; try solve [etransitivity; eauto]. *)
(*       destruct H. *)
(*       * constructor. left. constructor. left. auto. *)
(*       * induction H; try solve [etransitivity; eauto]. *)
(*         destruct H. *)
(*         -- constructor. left. constructor. right. auto. *)
(*         -- constructor. right. auto. *)
(*     + destruct H as [[? ?] ?]. *)
(*       constructor; auto. constructor; auto. *)
(* Qed. *)

(* Lemma meet_perm_idem : forall p, eq_perm (meet_perm p p) p. *)
(* Proof. *)
(*   split; intros. *)
(*   - constructor; intros. *)
(*     + constructor. left. auto. *)
(*     + destruct H; auto. *)
(*   - constructor; intros. *)
(*     + induction H; try solve [etransitivity; eauto]. *)
(*       destruct H; auto. *)
(*     + constructor; auto. *)
(* Qed. *)

(* Lemma join_perm_absorb : forall p q, eq_perm (join_perm p (meet_perm p q)) p. *)
(* Proof. *)
(*   split; intros. *)
(*   - constructor; intros. *)
(*     + constructor; auto. constructor; auto. *)
(*     + induction H; try solve [etransitivity; eauto]. *)
(*       destruct H; auto. destruct H; auto. *)
(*   - constructor; intros. *)
(*     + destruct H. auto. *)
(*     + constructor. left. auto. *)
(* Qed. *)

(* Lemma meet_perm_absorb : forall p q, eq_perm (meet_perm p (join_perm p q)) p. *)
(* Proof. *)
(*   split; intros. *)
(*   - constructor; intros. *)
(*     + constructor. left. auto. *)
(*     + destruct H. auto. *)
(*   - constructor; intros. *)
(*     + induction H; try solve [etransitivity; eauto]. *)
(*       destruct H; auto. destruct H; auto. *)
(*     + constructor; auto. constructor; auto. *)
  (* Qed. *)

*)

  (** ** Separate permissions *)
  Record separate (p q : perm) : Prop :=
    {
      sep_l: forall x y, inv q x -> inv p x -> (* inv p y -> *)
                    guar q x y -> rely p x y;
      sep_r: forall x y, inv p x -> inv q x -> guar p x y -> rely q x y;
    }.

  Notation "p ⊥ q" := (separate p q) (at level 50).

  Global Instance separate_symmetric: Symmetric separate.
  Proof.
    intros p q []. constructor; auto.
  Qed.

  Lemma separate_bottom : forall p, p ⊥ bottom_perm.
  Proof.
    constructor; intros; cbn; auto.
    inversion H1. reflexivity.
  Qed.

  (* Definition copyable p := forall x y, guar p x y -> rely p x y. *)

  (* Lemma copyable_separate : forall p, copyable p -> p ⊥ p. *)
  (* Proof. *)
  (*   intros. red in H. split; auto. *)
  (* Qed. *)

  (* If p preserves pred then p _|_ invperm pred *)
  Lemma separate_invperm p (pred : config -> Prop) :
    (forall x y, pred x -> guar p x y -> pred y) ->
    separate p (invperm pred).
  Proof.
    intro. constructor; simpl; intros.
    - subst; reflexivity.
    - eapply H; eassumption.
  Qed.


  (** ** Separating conjunction for permissions *)
  Program Definition sep_conj_perm (p q: perm) : perm :=
    {|
      pre := fun x => pre p x /\ pre q x;
      rely := fun x y => rely p x y /\ rely q x y;
      guar := clos_trans _ (fun x y => (guar p x y) \/ (guar q x y)) (* separateness implies each move is in the others' rely *) ;
      inv := fun x => inv p x /\ inv q x /\ p ⊥ q;
    |}.
  Next Obligation.
    constructor; repeat intro.
    - split; reflexivity.
    - destruct H, H0.
      split; etransitivity; eauto.
  Qed.
  Next Obligation.
    constructor.
    - constructor; intuition.
    - repeat intro. destruct H, H0.
      + destruct H, H0; econstructor 2; constructor; eauto.
      + econstructor 2. left. apply H. econstructor 2; eauto.
      + econstructor 2; eauto. econstructor 2; eauto. left. assumption.
      + repeat (econstructor 2; eauto).
  Qed.
  Next Obligation.
    split; respects.
  Qed.
  Next Obligation.
    split; [ | split ]; try assumption; eapply inv_rely; eassumption.
  Qed.
  Next Obligation.
    assert (inv p y /\ inv q y) as H3;
      [ | destruct H3; split; [ | split ]; assumption ].
    refine (clos_trans_preserves (fun z => inv p z /\ inv q z) _ _ _ _ _ H);
      [ | split; assumption ].
    simpl. intros. destruct H3; destruct H4; split;
      try (eapply inv_guar; eassumption).
    - eapply inv_rely; [ | eassumption ]. eapply (sep_r _ _ H2); assumption.
    - eapply inv_rely; [ | eassumption ]. eapply (sep_l _ _ H2); assumption.
  Qed.

  Notation "p ** q" := (sep_conj_perm p q) (at level 40).


  (*
  Lemma sep_conj_join : forall p q, p ⊥ q -> p ** q ≡≡ join_perm p q.
  Proof.
    split; intros.
    - constructor; auto; intros x []; split; auto.
    - constructor; auto; intros x [? [? ?]]; split; auto.
  Qed.
   *)

  Lemma sep_conj_perm_commut' : forall p q, p ** q <= q ** p.
  Proof.
    constructor.
    - intros x [? [? ?]]; simpl; split; intuition.
      (*
    - intros x y []; repeat split; auto.
    - intros. induction H.
      + destruct H; constructor; auto.
      + etransitivity; eauto.
  Qed. *)
  Admitted.

  Lemma sep_conj_perm_commut : forall p q, p ** q ≡≡ q ** p.
  Proof.
    split; apply sep_conj_perm_commut'.
  Qed.

  Lemma lte_l_sep_conj_perm : forall p q, p <= p ** q.
  Proof.
    intros. constructor; simpl; auto.
    - intros x _ []; auto.
    - intros x y [ inv_p [ inv_q sep ]] [ rel_p rel_q ]. assumption.
    - intros x y [ inv_p [ inv_q sep ]] ?. left; left; assumption.
    - intros x [ ? ? ]; assumption.
  Qed.

  Lemma lte_r_sep_conj_perm : forall p q, q <= p ** q.
  Proof.
    intros. rewrite sep_conj_perm_commut.
    apply lte_l_sep_conj_perm.
  Qed.

  Lemma sep_conj_invperm_conj pred1 pred2 :
    eq_perm (invperm pred1 ** invperm pred2) (invperm (fun x => pred1 x /\ pred2 x)).
  Proof.
    constructor; constructor; simpl; intros.
    - split; constructor.
    - destruct (H0 H). split; intro; assumption.
    - rewrite clos_trans_eq_or in H0; [ | typeclasses eauto ].
      apply clos_trans_trans; [ typeclasses eauto | assumption ].
    - destruct H; split; [ | split ]; try assumption.
      apply separate_invperm; intros. inversion H2. subst; assumption.
    - constructor.
    - destruct H1. destruct H0. split; auto.
    - subst; apply t_step; left; reflexivity.
    - destruct H as [? [? ?]]. split; assumption.
  Qed.


  Lemma sep_conj_self_invperm' p : p ** invperm (inv p) <= p.
  Proof.
    constructor; intros; simpl.
    - split; auto.
    - split; intros; auto. eapply inv_rely; eassumption.
    - simpl in H0. apply clos_trans_trans; [ typeclasses eauto | ].
      eapply clos_trans_incl; [ | eassumption ]. intros.
      destruct H1; [ assumption | subst; reflexivity ].
    - split; [ | split ]; try assumption.
      apply separate_invperm; intros. eapply inv_guar; eauto.
  Qed.

  Lemma sep_conj_self_invperm p : eq_perm (p ** invperm (inv p)) p.
  Proof.
    split; [ apply sep_conj_self_invperm' | apply lte_l_sep_conj_perm ].
  Qed.
  
  (** We can always weaken permissions and retain separateness, as long as we
      add the stronger invariant to the weaker permission *)

  Lemma separate_antimonotone p q r : p ⊥ q -> r <= q ->
                                      p ⊥ (invperm (inv q) ** r).
  Proof.
    intros. constructor; intros.
    - destruct H1 as [ ? [ ? ? ]]. simpl in H3.
      rewrite clos_trans_eq_or in H3; [ | typeclasses eauto ].
      rewrite clos_trans_trans in H3; [ | typeclasses eauto ].
      eapply sep_l; eauto.
    - split.
      + intro. eapply inv_rely; eauto. eapply sep_r; eauto.
      + simpl in H2; destruct H2 as [ ? [ ? ? ]]. apply H0; auto.
        eapply sep_r; eauto.
  Qed.

  Global Instance Proper_eq_perm_separate :
    Proper (eq_perm ==> eq_perm ==> Basics.flip Basics.impl) separate.
  Proof.
    intros p p' p_eq q q' q_eq p_sep_q. destruct p_eq; destruct q_eq.
    split; intros.
    - apply H; [ apply H0 | ]; eauto. eapply sep_l; eauto.
      + apply H2; eassumption.
      + apply H0; eassumption.
      + apply H1; [ | assumption ]. apply H2; assumption.
    - apply H1; [ apply H2 | ]; eauto. eapply sep_r; eauto.
      + apply H0; assumption.
      + apply H2; assumption.
      + apply H; [ | assumption ]. apply H0; assumption.
  Qed.

  Lemma sep_conj_perm_monotone_l p p' q :
      p' <= p -> invperm (inv p) ** p' ** q <= p ** q.
  Proof.
    constructor; simpl; intros.
    - destruct H0 as [? [? ?]]. destruct H1. repeat split; eauto.
    - destruct H0 as [? [? ?]]. destruct H1. repeat split; eauto; intros.
      eapply inv_rely; eauto.
    - destruct H0 as [? [? ?]]. simpl in H1.
      rewrite clos_trans_clos_trans_or in H1.
      rewrite <- clos_trans_or_assoc in H1.
      rewrite clos_trans_eq_or in H1; [ | repeat left; reflexivity ].
      induction H1; [ destruct H1 | ].
      + apply t_step; left; apply H; eauto.
      + apply t_step; right; assumption.
      + etransitivity; eauto.
        assert (inv p y /\ inv q y) as H4;
          [ | destruct H4; apply IHclos_trans2; assumption ].
        refine (clos_trans_preserves (fun z => inv p z /\ inv q z) _ _ _ _ _ H1_);
          [ | split; assumption ].
        intros. destruct H1; destruct H4; split.
        * eapply inv_guar; eauto.
        * eapply inv_rely; eauto. eapply sep_r; eauto.
        * eapply inv_rely; eauto. eapply sep_l; eauto.
        * eapply inv_guar; eauto.
    - destruct H0 as [? [? ?]].
      repeat split; simpl; intros; subst; eauto.
      + apply H; assumption.
      + eapply inv_guar; eauto.
      + reflexivity.
      + simpl in H4; destruct H4 as [? [? ?]].
        eapply inv_rely; eauto. eapply sep_l; eauto.
      + simpl in H4; destruct H4 as [? [? ?]].
        apply H; eauto. eapply sep_l; eauto.
      + rewrite clos_trans_eq_or in H5; [ | typeclasses eauto ].
        rewrite clos_trans_trans in H5; [ | typeclasses eauto ].
        destruct H3 as [? [? ?]].
        eapply sep_r; eauto.
  Qed.

  (* FIXME: the "easy" proof requires associativity of **
  Lemma sep_conj_perm_monotone_r p q q' :
    q' <= q -> p ** invperm (inv q) ** q' <= p ** q.
  Proof.
    intros. rewrite (sep_conj_perm_commut _ q'). rewrite (sep_conj_perm_commut _ q).
    apply sep_conj_perm_monotone_l.

  Lemma sep_conj_perm_monotone : forall p p' q q',
      p' <= p -> q' <= q -> invperm (inv p) ** invperm (inv q) ** p' ** q' <= p ** q.
  Proof.
    constructor; intros; simpl.
    - destruct H1 as [? [? ?]]. destruct H2. repeat split; eauto.
    - destruct H1 as [? [? ?]]. destruct H2. repeat split; eauto; intros.
      + eapply inv_rely; eauto.
      + eapply inv_rely; eauto.
    - destruct H1 as [? [? ?]]. simpl in H2.
      rewrite clos_trans_clos_trans_or in H2.
      rewrite <- clos_trans_or_assoc in H2.
      rewrite clos_trans_clos_trans_or in H2.
      rewrite <- clos_trans_or_assoc in H2.
      rewrite clos_trans_eq_or in H2; [ | repeat left; reflexivity ].
      rewrite clos_trans_eq_or in H2; [ | repeat left; reflexivity ].
      induction H2; [ destruct H2 | ].
      + apply t_step; left; apply H; eauto.
      + apply t_step; right; apply H0; eauto.
      + etransitivity; eauto.
        assert (inv p y /\ inv q y) as H5;
          [ | destruct H5; apply IHclos_trans2; assumption ].
        refine (clos_trans_preserves (fun z => inv p z /\ inv q z) _ _ _ _ _ H2_);
          [ | split; assumption ].
        intros. destruct H2. destruct H5.
        * split.
          -- eapply inv_guar; eauto.
          -- eapply inv_rely; eauto. eapply sep_r; eauto.
        * split.
          -- eapply inv_rely; eauto. eapply sep_l; eauto.
          -- eapply inv_guar; eauto.
    - destruct H1 as [? [? ?]].
      repeat split; simpl; intros; subst; eauto.
      + apply H; assumption.
      + eapply inv_guar; eauto.
      + eapply inv_rely; eauto. simpl in H5. destruct H5 as [? [? ?]].
        eapply sep_r; eauto.
      + assert (x0 = y).
        * clear H4 H5. induction H6; [ destruct H4 | ]; subst; reflexivity.
        * subst. reflexivity.
      + apply H0; assumption.
      + simpl in H5; destruct H5 as [[? [? ?]] [? ?]].
        eapply inv_rely; eauto. eapply sep_l; eauto.
      + simpl in H5; destruct H5 as [[? [? ?]] [? ?]].
        eapply inv_guar; eauto.
      + simpl in H5; destruct H5 as [[? [? ?]] [? ?]].
        apply H; auto. eapply sep_l; eauto.
      + destruct H4 as [[? [? ?]] [? ?]].
        rewrite clos_trans_clos_trans_or in H6.
        rewrite <- clos_trans_or_assoc in H6.
        rewrite clos_trans_eq_or in H6; [ | intro; left; reflexivity ].
        rewrite clos_trans_eq_or in H6; [ | typeclasses eauto ].
        rewrite clos_trans_trans in H6; [ | typeclasses eauto ].
        apply H0; eauto. eapply sep_r; eauto.
  Qed.
  *)

  (* NOTE: should still be provable, using the above plus p ** invperm (inv p) = p *)
  Global Instance Proper_eq_perm_sep_conj_perm :
    Proper (eq_perm ==> eq_perm ==> eq_perm) sep_conj_perm.
  Proof.
  Admitted.


  Lemma sep_conj_perm_bottom' : forall p, p ** bottom_perm <= p.
  Proof.
    constructor; intros.
    - split; [| split]; simpl; intuition.
    - repeat split; auto.
    - simpl in H0. eapply clos_trans_trans; [ typeclasses eauto | ].
      eapply clos_trans_incl; [ | eassumption ]. intros.
      destruct H1; [ assumption | subst; reflexivity ].
    - split; [ assumption | split ].
      * constructor.
      * apply separate_bottom.
  Qed.

  Lemma sep_conj_perm_bottom : forall p, p ** bottom_perm ≡≡ p.
  Proof.
    split; [apply sep_conj_perm_bottom' | apply lte_l_sep_conj_perm].
  Qed.

  Lemma sep_conj_perm_top' : forall p, p ** top_perm <= top_perm.
  Proof.
    constructor; intros; simpl in *; intuition.
  Qed.

  Lemma sep_conj_perm_top : forall p, top_perm ≡≡ p ** top_perm.
  Proof.
    split; [apply lte_r_sep_conj_perm | apply sep_conj_perm_top'].
  Qed.


  Lemma separate_sep_conj_perm_l' p q r : p ⊥ q ** r -> p ⊥ (invperm (inv (q ** r)) ** q).
  Proof.
    intros.
    apply separate_antimonotone; [ assumption | ].
    apply lte_l_sep_conj_perm.
  Qed.

  (* FIXME: this should follow from the above *)
  Lemma separate_sep_conj_perm_l p q r : p ⊥ q ** r -> p ⊥ (invperm (inv r) ** q).
  Proof.
  Admitted.

  Lemma separate_sep_conj_perm_r: forall p q r, p ⊥ q ** r -> p ⊥ (invperm (inv q) ** r).
  Proof.
    intros. apply separate_sep_conj_perm_l.
    rewrite sep_conj_perm_commut in H. assumption.
  Qed.


FIXME: this is where I'm stopping for now


  Lemma separate_sep_conj_perm: forall p q r, p ⊥ q ->
                                         p ⊥ r ->
                                         r ⊥ q ->
                                         p ⊥ q ** r.
  Proof.
    intros. constructor; intros.
    - induction H2.
      + destruct H2; [apply H | apply H0]; auto.
      + etransitivity; eauto.
    - split; [apply H | apply H0]; auto.
  Qed.

  Lemma sep_conj_perm_assoc p q r : eq_perm (p ** (q ** r)) ((p ** q) ** r).
  Proof.
    split; constructor; simpl; intros.
    - destruct H0 as [[? ?] ?]. split; [ | split ]; assumption.
    - destruct H0 as [[? ?] ?]. repeat split; assumption.
    - rewrite clos_trans_clos_trans_or.
      rewrite clos_trans_or_commut in H0.
      rewrite clos_trans_clos_trans_or in H0.
      rewrite clos_trans_or_commut in H0.
      rewrite clos_trans_or_assoc in H0. assumption.
    - 

FIXME
      rewrite <- clos_trans_clos_trans_or in H0.
rewrite <- clos_trans_or_assoc.



  Lemma sep_conj_perm_assoc : forall p q r,
      (p ** q) ** r ≡≡ p ** (q ** r).
  Proof.
    split; intros.
    {
      constructor.
      - intros x [? [[? [? ?]] ?]].
        pose proof (separate_sep_conj_perm_l _ _ _ H3).
        pose proof (separate_sep_conj_perm_r _ _ _ H3).
        split; [split; [| split] | split]; auto.
        symmetry. apply separate_sep_conj_perm; symmetry; auto.
      - intros x y [? [? ?]]. split; [split |]; auto.
      - intros. induction H; try solve [etransitivity; eauto].
        destruct H.
        + induction H; try solve [etransitivity; eauto].
          destruct H.
          * constructor. left. auto.
          * constructor. right. constructor. left. auto.
        + constructor. right. constructor. right. auto.
    }
    {
      constructor.
      - intros x [[? [? ?]] [? ?]]. symmetry in H3.
        pose proof (separate_sep_conj_perm_l _ _ _ H3). symmetry in H4.
        pose proof (separate_sep_conj_perm_r _ _ _ H3). symmetry in H5.
        split; [| split; [split; [| split] |]]; auto.
        apply separate_sep_conj_perm; auto. symmetry; auto.
      - intros x y [[? ?] ?]; simpl; auto.
      - intros. induction H; try solve [etransitivity; eauto].
        destruct H.
        + constructor. left. constructor. left. auto.
        + induction H; try solve [etransitivity; eauto].
          destruct H.
          * constructor. left. constructor. right. auto.
          * constructor. right. auto.
    }
  Qed.

  (** * Permission sets *)
  (** Perms = upwards-closed sets of permissions *)
  Record Perms :=
    {
    in_Perms : perm -> Prop;
    Perms_upwards_closed : forall p1 p2, in_Perms p1 -> p1 <= p2 -> in_Perms p2
    }.
  Notation "p ∈ P" := (in_Perms P p) (at level 60).

  (** ** Permission set ordering *)
  (** Defined as superset. *)
  Definition lte_Perms (P Q : Perms) : Prop :=
    forall p, p ∈ Q -> p ∈ P.
  Notation "P ⊑ Q" := (lte_Perms P Q) (at level 60).

  Global Instance lte_Perms_is_preorder : PreOrder lte_Perms.
  Proof.
    constructor; repeat intro; auto.
  Qed.

  (** Various lattice definitions. *)
  Program Definition top_Perms : Perms :=
    {|
    in_Perms := fun r => False
    |}.

  Lemma top_Perms_is_top : forall P, P ⊑ top_Perms.
  Proof.
    repeat intro. inversion H.
  Qed.

  Program Definition bottom_Perms : Perms :=
    {|
    in_Perms := fun r => True
    |}.

  Lemma bottom_Perms_is_bottom : forall P, bottom_Perms ⊑ P.
  Proof.
    repeat intro. simpl. auto.
  Qed.

  (** The least Perms set containing a given p *)
  Program Definition singleton_Perms p1 : Perms :=
    {|
    in_Perms := fun p2 => p1 <= p2
    |}.
  Next Obligation.
    etransitivity; eassumption.
  Qed.

  Program Definition join_Perms (Ps : Perms -> Prop) : Perms :=
    {|
    in_Perms := fun p => forall P, Ps P -> p ∈ P
    |}.
  Next Obligation.
    eapply Perms_upwards_closed; eauto.
  Qed.
  Lemma lte_join_Perms : forall (Ps : Perms -> Prop) P,
      Ps P ->
      P ⊑ join_Perms Ps.
  Proof.
    repeat intro. apply H0. auto.
  Qed.
  Lemma join_Perms_min : forall (Ps : Perms -> Prop) Q,
      (forall P, Ps P -> P ⊑ Q) ->
      join_Perms Ps ⊑ Q.
  Proof.
    repeat intro.
    eapply H; eauto.
  Qed.

  (** Complete meet of Perms sets = union *)
  Program Definition meet_Perms (Ps : Perms -> Prop) : Perms :=
    {|
    in_Perms := fun p => exists P, Ps P /\ p ∈ P
    |}.
  Next Obligation.
    exists H. split; auto.
    apply (Perms_upwards_closed _ p1); assumption.
  Qed.

  Lemma lte_meet_Perms : forall (Ps : Perms -> Prop) P,
      Ps P ->
      meet_Perms Ps ⊑ P.
  Proof.
    repeat intro. exists P. auto.
  Qed.

  Lemma meet_Perms_max : forall (Ps : Perms -> Prop) Q,
      (forall P, Ps P -> Q ⊑ P) ->
      Q ⊑ meet_Perms Ps.
  Proof.
    repeat intro. destruct H0 as [? [? ?]].
    eapply H; eauto.
  Qed.

  Definition meet_Perms2 P Q : Perms := meet_Perms (fun R => R = P \/ R = Q).

  (** Set equality *)
  Definition eq_Perms (P Q : Perms) : Prop := P ⊑ Q /\ Q ⊑ P.
  Notation "P ≡ Q" := (eq_Perms P Q) (at level 60).

  Global Instance Equivalence_eq_Perms : Equivalence eq_Perms.
  Proof.
    constructor; repeat intro.
    - split; reflexivity.
    - destruct H; split; auto.
    - destruct H, H0. split; etransitivity; eauto.
  Qed.

  Global Instance Proper_eq_Perms_lte_Perms :
    Proper (eq_Perms ==> eq_Perms ==> Basics.flip Basics.impl) lte_Perms.
  Proof.
    do 5 red. intros. etransitivity. apply H. etransitivity. apply H1. apply H0.
  Qed.

  Global Instance Proper_eq_Perms_eq_perm_in_Perms : Proper (eq_Perms ==> eq_perm ==> Basics.flip Basics.impl) in_Perms.
  Proof.
    repeat intro; subst. apply H. eapply Perms_upwards_closed; eauto.
  Qed.

  (** ** Separating conjunction for permission sets *)
  Program Definition sep_conj_Perms (P Q : Perms) : Perms :=
    {|
    in_Perms := fun r => exists p q, p ∈ P /\ q ∈ Q /\ p ** q <= r
    |}.
  Next Obligation.
    exists H, H1. split; [| split]; auto. etransitivity; eauto.
  Qed.
  Notation "P * Q" := (sep_conj_Perms P Q).

  Lemma lte_l_sep_conj_Perms : forall P Q, P ⊑ P * Q.
  Proof.
    intros P Q p' ?. destruct H as [p [q [? [? ?]]]].
    eapply Perms_upwards_closed; eauto.
    etransitivity; eauto. apply lte_l_sep_conj_perm.
  Qed.

  Lemma lte_r_sep_conj_Perms : forall P Q, Q ⊑ P * Q.
  Proof.
    intros P Q q' ?. destruct H as [p [q [? [? ?]]]].
    eapply Perms_upwards_closed; eauto.
    etransitivity; eauto. apply lte_r_sep_conj_perm.
  Qed.

  Lemma sep_conj_Perms_bottom_identity : forall P, bottom_Perms * P ≡ P.
  Proof.
    constructor; repeat intro.
    - exists bottom_perm, p. split; simpl; [auto | split; auto].
      rewrite sep_conj_perm_commut. apply sep_conj_perm_bottom.
    - destruct H as [? [? [_ [? ?]]]].
      eapply (Perms_upwards_closed P); eauto.
      etransitivity; eauto. apply lte_r_sep_conj_perm.
  Qed.

  Lemma sep_conj_Perms_top_absorb : forall P, top_Perms * P ≡ top_Perms.
  Proof.
    constructor; repeat intro.
    - inversion H.
    - destruct H as [? [_ [[] _]]].
  Qed.

  Lemma sep_conj_Perms_monotone : forall P P' Q Q', P' ⊑ P -> Q' ⊑ Q -> P' * Q' ⊑ P * Q.
  Proof.
    repeat intro. destruct H1 as [? [? [? [? ?]]]].
    exists x, x0. auto.
  Qed.

  Lemma sep_conj_Perms_perm: forall P Q p q,
      p ∈ P ->
      q ∈ Q ->
      p ** q ∈ P * Q.
  Proof.
    intros. exists p, q. split; auto. split; auto. reflexivity.
  Qed.

  Lemma sep_conj_Perms_commut : forall P Q, P * Q ≡ Q * P.
  Proof.
    split; repeat intro.
    - destruct H as [q [p' [? [? ?]]]].
      exists p', q. split; [| split]; auto. etransitivity; eauto. apply sep_conj_perm_commut.
    - destruct H as [p' [q [? [? ?]]]].
      exists q, p'. split; [| split]; auto. etransitivity; eauto. apply sep_conj_perm_commut.
  Qed.

  Lemma sep_conj_Perms_assoc : forall P Q R, P * (Q * R) ≡ (P * Q) * R.
  Proof.
    split; repeat intro.
    - rename p into p'. destruct H as [pq [r [? [? ?]]]].
      destruct H as [p [q [? [? ?]]]].
      exists p, (q ** r).
      split; auto. split; auto. apply sep_conj_Perms_perm; auto.
      rewrite <- sep_conj_perm_assoc.
      etransitivity; eauto.
      apply sep_conj_perm_monotone; intuition.
    - rename p into p'. destruct H as [p [qr [? [? ?]]]].
      destruct H0 as [q [r [? [? ?]]]].
      exists (p ** q), r.
      split; auto. apply sep_conj_Perms_perm; auto. split; auto.
      rewrite sep_conj_perm_assoc.
      etransitivity; eauto.
      apply sep_conj_perm_monotone; intuition.
  Qed.

  Lemma sep_conj_Perms_meet_commute : forall (Ps : Perms -> Prop) P,
      (meet_Perms Ps) * P ≡ meet_Perms (fun Q => exists P', Q = P' * P /\ Ps P').
  Proof.
    split; repeat intro.
    - destruct H as [? [[Q [? ?]] ?]].
      subst. destruct H1 as [? [? [? [? ?]]]].
      simpl. exists x, x0. split; [ | split]; auto.
      eexists; split; eauto.
    - destruct H as [? [? [[Q [? ?]] [? ?]]]].
      simpl. eexists. split.
      + exists Q. split; auto.
      + eapply Perms_upwards_closed; eauto.
        simpl. exists x, x0. split; [auto | split; [auto | ]]. reflexivity.
  Qed.

  (** Permission entailment, which we sometimes use instead of ordering. *)
  Definition entails_Perms P Q := Q ⊑ P.
  Notation "P ⊨ Q" := (entails_Perms P Q) (at level 60).

  Global Instance entails_Perms_preorder : PreOrder entails_Perms.
  Proof.
    constructor; repeat intro; auto.
  Qed.

  Global Instance Proper_eq_Perms_entails_Perms :
    Proper (eq_Perms ==> eq_Perms ==> Basics.flip Basics.impl) entails_Perms.
  Proof.
    do 6 red. intros. rewrite H. rewrite H0. auto.
  Qed.

  Global Instance Proper_eq_Perms_sep_conj_Perms :
    Proper (eq_Perms ==> eq_Perms ==> eq_Perms) sep_conj_Perms.
  Proof.
    repeat intro. etransitivity.
    - split; eapply sep_conj_Perms_monotone; try eapply H0; try eapply H.
    - split; eapply sep_conj_Perms_monotone; try eapply H0; try eapply H; reflexivity.
  Qed.

  (** Separating implication, though we won't be using it. *)
  Definition impl_Perms P Q := meet_Perms (fun R => R * P ⊨ Q).

  (** A standard property about separating conjunction and implication. *)
  Lemma adjunction : forall P Q R, P * Q ⊨ R <-> P ⊨ (impl_Perms Q R).
  Proof.
    intros. split; intros.
    - red. red. intros. simpl. exists P. auto.
    - apply (sep_conj_Perms_monotone _ _ Q Q) in H; intuition.
      red. etransitivity; [ | apply H ].
      unfold impl_Perms.
      rewrite sep_conj_Perms_meet_commute.
      apply meet_Perms_max. intros P' [? [? ?]]. subst. auto.
  Qed.

  (* (** * TODO: least fixpoints? *) *)
  (* (** The meet of a TODO *) *)
  (* Program Definition meet_A_Perms {A} (Ps : (A -> Perms) -> Prop) : A -> Perms := *)
  (*   fun a => *)
  (*     {| *)
  (*       in_Perms := fun p => exists P, Ps P /\ p ∈ P a *)
  (*     |}. *)
  (* Next Obligation. *)
  (*   exists H. split; auto. *)
  (*   apply (Perms_upwards_closed _ p1); assumption. *)
  (* Qed. *)

  (* Notation "P -⊑- Q" := (forall a, P a ⊑ Q a) (at level 60). *)
  (* Notation "P -≡- Q" := (P -⊑- Q /\ Q -⊑- P) (at level 60). *)

  (* Lemma lte_meet_A_Perms {A} : forall (Ps : (A -> Perms) -> Prop) P, *)
  (*     Ps P -> *)
  (*     meet_A_Perms Ps -⊑- P. *)
  (* Proof. *)
  (*   repeat intro. exists P. auto. *)
  (* Qed. *)

  (* Lemma meet_A_Perms_max {A} : forall (Ps : (A -> Perms) -> Prop) Q, *)
  (*     (forall P, Ps P -> Q -⊑- P) -> *)
  (*     Q -⊑- meet_A_Perms Ps. *)
  (* Proof. *)
  (*   repeat intro. destruct H0 as [? [? ?]]. *)
  (*   eapply H; eauto. *)
  (* Qed. *)

  (* Definition μ {A : Type} *)
  (*            (F : (A -> Perms) -> A -> Perms) *)
  (*            (Hmon: forall P Q, (P -⊑- Q) -> (F P -⊑- F Q)) : A -> Perms := *)
  (*   meet_A_Perms (fun P => F P -⊑- P). *)

  (* Lemma μ_fixedpoint {A} : forall (F : (A -> Perms) -> A -> Perms) Hmon, *)
  (*     F (μ F Hmon) -≡- (μ F Hmon). *)
  (* Proof. *)
  (*   intros. assert (F (μ F Hmon) -⊑- μ F Hmon). *)
  (*   { *)
  (*     unfold μ. repeat intro. destruct H as (P & ? & ?). *)
  (*     eapply Hmon. 2: { apply H. assumption. } *)
  (*     repeat intro. eexists. split; eauto. *)
  (*   } *)
  (*   split; auto. *)
  (*   unfold μ. repeat intro. simpl. eexists. split. 2: eauto. *)
  (*   apply Hmon. apply H. *)
  (* Qed. *)

  (* Lemma μ_least {A} : forall (F : (A -> Perms) -> A -> Perms) Hmon X, *)
  (*     F X -≡- X -> *)
  (*     μ F Hmon -⊑- X. *)
  (* Proof. *)
  (*   intros. unfold μ. apply lte_meet_A_Perms. apply H. *)
  (* Qed. *)

  (* Lemma μ_induction {A} F (P : A -> Perms) Hmon : *)
  (*   (forall a, F P a ⊑ P a) -> *)
  (*   (forall a, μ F Hmon a ⊑ P a). *)
  (* Proof. *)
  (*   intros Hlte a p Hp. *)
  (*   eexists. split; eauto. *)
  (* Qed. *)
End Permissions.

(* begin hide *)
(* Redefining notations outside the section. *)
Notation "p <= q" := (lte_perm p q).
Notation "p ≡≡ q" := (eq_perm p q) (at level 50).
Notation "p ⊥ q" := (separate p q) (at level 50).
Notation "p ** q" := (sep_conj_perm p q) (at level 40).
Notation "p ∈ P" := (in_Perms P p) (at level 60).
Notation "P ⊑ Q" := (lte_Perms P Q) (at level 60).
Notation "P ≡ Q" := (eq_Perms P Q) (at level 60).
Notation "P * Q" := (sep_conj_Perms P Q).
Notation "P ⊨ Q" := (entails_Perms P Q) (at level 60).
Notation "P -⊑- Q" := (forall a, P a ⊑ Q a) (at level 60).
Notation "P -≡- Q" := (P -⊑- Q /\ Q -⊑- P) (at level 60).

Ltac respects := eapply pre_respects; eauto.

#[ export ] Hint Unfold rely : core.
#[ export ] Hint Unfold pre : core.
#[ export ] Hint Unfold guar : core.
#[ export ] Hint Resolve pre_respects : core.
#[ export ] Hint Resolve pre_inc : core.
#[ export ] Hint Resolve rely_inc : core.
#[ export ] Hint Resolve guar_inc : core.
#[ export ] Hint Unfold eq_perm : core.
#[ export ] Hint Resolve eq_perm_lte_1 : core.
#[ export ] Hint Resolve eq_perm_lte_2 : core.

(* end hide *)
