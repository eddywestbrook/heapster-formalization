(* begin hide *)
From Coq Require Import
  Classes.Morphisms
  Classes.RelationClasses
  Lists.List
  Relations.Relation_Operators
  Relations.Operators_Properties.
(* end hide *)

From Heapster Require Import
     Utils.

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

Lemma clos_trans_incl_pred {A} (pred : A -> Prop) (R S : A -> A -> Prop)
  (pres : forall x y, pred x -> R x y -> pred y)
  (incl : forall x y, pred x -> R x y -> S x y) x y :
  pred x -> clos_trans A R x y -> clos_trans A S x y.
Proof.
  intros; induction H0.
  - left; apply incl; assumption.
  - etransitivity; eauto. apply IHclos_trans2.
    eapply (clos_trans_preserves _ _ pres); eassumption.
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


  (* Equivalence of the guarantees of two permissions *)
  Definition guar_eq (p q : perm) : Prop := forall x y, guar p x y <-> guar q x y.

  Global Instance guar_eq_Equivalence : Equivalence guar_eq.
  Proof.
    constructor; repeat intro.
    - reflexivity.
    - symmetry; apply H.
    - etransitivity; [ apply H | apply H0 ].
  Qed.

  Global Instance guar_Proper_guar_eq_impl : Proper (guar_eq ==> eq ==> eq ==>
                                                       Basics.flip Basics.impl) guar.
  Proof.
    repeat intro; subst; apply H. assumption.
  Qed.

  Global Instance guar_Proper_guar_eq : Proper (guar_eq ==> eq ==> eq ==> iff) guar.
  Proof.
    repeat intro. subst. apply H.
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

  (* The inverse of the permission ordering. It is often more useful to write it
     this direction because it captures a notion of logical entailment, where if
     something requires permission q then you can do it if you have permission
     p that is at least as big as it *)
  Definition gte_perm p q := lte_perm q p.


  (* begin hide *)
  Hint Resolve pre_inc : core.
  Hint Resolve rely_inc : core.
  Hint Resolve guar_inc : core.
  (* end hide *)

  Notation "p <= q" := (lte_perm p q).
  Notation "p >= q" := (gte_perm p q).

  Global Instance lte_perm_is_PreOrder : PreOrder lte_perm.
  Proof.
    constructor; [ constructor; auto | constructor; intros ]; eauto.
    - apply H; auto; apply H0; auto; apply H; auto.
    - apply H; auto; apply H0; auto; apply H; auto.
    - apply H0; auto. apply H; auto; apply H0; auto.
    - apply H; apply H0; assumption.
  Qed.

  Global Instance gte_perm_is_PreOrder : PreOrder gte_perm.
  Proof.
    constructor; unfold gte_perm; repeat intro;
      [ reflexivity | etransitivity; eassumption ].
  Qed.

  (** Equality of permissions = the symmetric closure of the ordering. *)
  Definition eq_perm p q : Prop := p <= q /\ q <= p.

  Notation "p ≡≡ q" := (eq_perm p q) (at level 50).

  Lemma eq_perm_lte_1 : forall p q, p ≡≡ q -> p <= q.
  Proof. intros p q []. auto. Qed.
  Lemma eq_perm_lte_2 : forall p q, p ≡≡ q -> q <= p.
  Proof. intros p q []. auto. Qed.

  Lemma eq_perm_eq_inv p q x : p ≡≡ q -> inv p x <-> inv q x.
  Proof.
    intro H. split; intro H0; apply H; assumption.
  Qed.

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

  Global Instance Proper_eq_perm_inv :
    Proper (eq_perm ==> eq ==> Basics.flip Basics.impl) inv.
  Proof.
    repeat intro; subst. apply H; auto.
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

  (* An invperm is less than or equal to any p with a stronger invariant *)
  Lemma lte_invperm (pred : config -> Prop) p :
    (forall x, inv p x -> pred x) -> invperm pred <= p.
  Proof.
    constructor; simpl; intros; auto.
    - apply H; eapply inv_rely; eassumption.
    - subst. reflexivity.
  Qed.

  (* An equivalent predicate gives an equal invperm *)
  Lemma eq_invperm (pred1 pred2 : config -> Prop) :
    (forall x, pred1 x <-> pred2 x) -> eq_perm (invperm pred2) (invperm pred1).
  Proof.
    constructor; simpl; intros; apply lte_invperm; apply H.
  Qed.

  (* The permission with only a precondition, that is otherwise bottom *)
  Program Definition preperm (pred : config -> Prop) : perm :=
    {|
      pre := pred;
      rely x y := pred x -> pred y;
      guar x y := x = y;
      inv x := True
    |}.


  (* Set the precondition to a permission, closed under that permission's rely *)
  Program Definition set_pre_perm (pred : config -> Prop) p :=
    {|
      pre x := exists y, inv p y /\ pred y /\ rely p y x;
      rely := rely p;
      guar := guar p;
      inv := inv p;
    |}.
  Next Obligation.
    eexists. split; [ eassumption | ]. split; [ eassumption | ].
    etransitivity; eassumption.
  Qed.
  Next Obligation.
    eapply inv_rely; eassumption.
  Qed.
  Next Obligation.
    eapply inv_guar; eassumption.
  Qed.

  (* Setting a precondition is Proper wrt the precondition and the permission *)
  Global Instance Proper_lte_set_pre_perm :
    Proper ((eq ==> Basics.impl) --> lte_perm ==> lte_perm) set_pre_perm.
  Proof.
    intros pred1 pred2 Rpred p q Rpq.
    constructor; intros; try (apply Rpq; assumption).
    destruct H0 as [y [? [? ?]]].
    exists y.
    split; [ apply Rpq; assumption | ].
    split; [ apply (Rpred y y (reflexivity _)); assumption | ].
    apply Rpq; assumption.
  Qed.

  Global Instance Proper_eq_set_pre_perm :
    Proper ((eq ==> iff) ==> eq_perm ==> eq_perm) set_pre_perm.
  Proof.
    intros pred1 pred2 ? p q [? ?].
    split; eapply Proper_lte_set_pre_perm; try assumption;
      repeat intro; subst; apply (H y y (reflexivity _)); assumption.
  Qed.

  (* Add a precondition to a permission, closed under its rely *)
  Program Definition add_pre_perm (pred : config -> Prop) p :=
    {|
      pre x := pre p x /\ exists y, inv p y /\ pred y /\ rely p y x;
      rely := rely p;
      guar := guar p;
      inv := inv p;
    |}.
  Next Obligation.
    split; [ eapply pre_respects; eassumption | ].
    eexists. split; [ eassumption | ]. split; [ eassumption | ].
    etransitivity; eassumption.
  Qed.
  Next Obligation.
    eapply inv_rely; eassumption.
  Qed.
  Next Obligation.
    eapply inv_guar; eassumption.
  Qed.

  (* Adding a precondition is Proper wrt the precondition and the permission *)
  Global Instance Proper_lte_add_pre_perm :
    Proper (pointwise_relation _ Basics.impl --> lte_perm ==> lte_perm) add_pre_perm.
  Proof.
    intros pred1 pred2 Rpred p q Rpq.
    constructor; intros; try (apply Rpq; assumption).
    destruct H0 as [? [y [? [? ?]]]]. split; [ apply Rpq; assumption | ].
    exists y.
    split; [ apply Rpq; assumption | ].
    split; [ apply (Rpred y); assumption | ].
    apply Rpq; assumption.
  Qed.

  Global Instance Proper_eq_add_pre_perm :
    Proper (pointwise_relation _ iff ==> eq_perm ==> eq_perm) add_pre_perm.
  Proof.
    intros pred1 pred2 ? p q [? ?].
    split; eapply Proper_lte_add_pre_perm; try assumption;
      repeat intro; apply H; assumption.
  Qed.

  (* Adding a precondition that is already implied by the precondition of a
     permission is a no-op *)
  Lemma add_pre_perm_eq (pred : config -> Prop) p :
    (forall x, pre p x -> pred x) -> eq_perm (add_pre_perm pred p) p.
  Proof.
    constructor; constructor; intros; try assumption.
    - split; [ assumption | ]. exists x. split; [ assumption | ].
      split; [ apply H; assumption | reflexivity ].
    - destruct H1; assumption.
  Qed.

  (* Adding a precondition yields a bigger permission set *)
  Lemma add_pre_perm_gte_p (pred : config -> Prop) p : add_pre_perm pred p >= p.
  Proof.
    constructor; intros; try assumption.
    destruct H0; assumption.
  Qed.

  (* Permission stating that we currently hold q except for its precondition,
     and that we held p before function f was applied to the state *)
  Definition rewind_perm f p q :=
    set_pre_perm (fun y => exists z, y = f z /\ inv p z /\ pre p z) q.

  (* rewind is Proper wrt the permission ordering *)
  Global Instance Proper_lte_rewind_perm f :
    Proper (lte_perm ==> lte_perm ==> lte_perm) (rewind_perm f).
  Proof.
    intros p1 p2 Rp q1 q2 Rq.
    apply Proper_lte_set_pre_perm; try assumption.
    repeat intro. destruct H0 as [z [? [? ?]]]; subst.
    exists z; split; [ reflexivity | split ]; apply Rp; assumption.
  Qed.

  (* rewing is Proper wrt permission equality *)
  Global Instance Proper_eq_rewind_perm f :
    Proper (eq_perm ==> eq_perm ==> eq_perm) (rewind_perm f).
  Proof.
    intros p1 p2 [? ?] q1 q2 [? ?].
    split; apply Proper_lte_rewind_perm; assumption.
  Qed.

  (* The guarantee of a rewind is the same as that of its RHS permission *)
  Lemma rewind_guar_eq f p q : guar_eq (rewind_perm f p q) q.
  Proof. repeat intro. simpl. reflexivity. Qed.


  (* Remove the guarantee of a permission, replacing it with equality *)
  Program Definition no_guar (p : perm) : perm :=
    {|
      pre := pre p;
      rely := rely p;
      guar := eq;
      inv := inv p
    |}.
  Next Obligation.
    eapply pre_respects; eassumption.
  Qed.
  Next Obligation.
    eapply inv_rely; eassumption.
  Qed.

  Global Instance Proper_no_guar : Proper (lte_perm ==> lte_perm) no_guar.
  Proof.
    constructor; intros; try (apply H; assumption).
    inversion H1; reflexivity.
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
      sep_r: forall x y, inv p x -> inv q x ->
                    guar p x y -> rely q x y;
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

  (* If the guarantee of q is equality then p is separate from q if the
     guarantee of p satisfies the rely of q *)
  Lemma sep_guar_eq_bottom p q :
    guar_eq q bottom_perm ->
    (forall x y, inv q x -> guar p x y -> rely q x y) ->
    separate p q.
  Proof.
    constructor; intros.
    - assert (x = y); [ apply H; assumption | subst; reflexivity ].
    - apply H0; assumption.
  Qed.

  (* If p preserves pred then p _|_ invperm pred *)
  Lemma separate_invperm p (pred : config -> Prop) :
    (forall x y, pred x -> guar p x y -> pred y) ->
    separate p (invperm pred).
  Proof.
    intro. constructor; simpl; intros.
    - subst; reflexivity.
    - eapply H; eassumption.
  Qed.

  (* All invperms are separate from each other *)
  Lemma separate_invperm_invperm pred1 pred2 :
    invperm pred1 ⊥ invperm pred2.
  Proof.
    apply separate_invperm; intros. simpl in H0; subst. assumption.
  Qed.

  (* All invperms are self-separate *)
  Lemma self_sep_invperm pred : invperm pred ⊥ invperm pred.
  Proof. apply separate_invperm_invperm. Qed.

  (* Permissions with a trivial guarantee are always self-separate *)
  Lemma self_sep_trivial_guar p :
    (forall x y, guar p x y <-> x = y) -> p ⊥ p.
  Proof.
    intro H; constructor; intros;
      rewrite (H x y) in H2; inversion H2; reflexivity.
  Qed.

  (* A permission is always separate from a larger one's invperm *)
  Lemma separate_bigger_invperm p q : p <= q -> invperm (inv q) ⊥ p.
  Proof.
    symmetry; apply separate_invperm; intros.
    eapply inv_guar; [ | eassumption ].
    eapply guar_inc; eassumption.
  Qed.

  (* Setting a precondition preserves separateness *)
  Lemma separate_set_pre pred p q : p ⊥ q <-> set_pre_perm pred p ⊥ q.
  Proof.
    split; constructor; intros.
    - apply (sep_l _ _ H); assumption.
    - apply (sep_r _ _ H); assumption.
    - apply (sep_l _ _ H); assumption.
    - apply (sep_r _ _ H); assumption.
  Qed.

  (* Adding a precondition preserves separateness *)
  Lemma separate_add_pre pred p q : p ⊥ q <-> add_pre_perm pred p ⊥ q.
  Proof.
    split; constructor; intros.
    - apply (sep_l _ _ H); assumption.
    - apply (sep_r _ _ H); assumption.
    - apply (sep_l _ _ H); assumption.
    - apply (sep_r _ _ H); assumption.
  Qed.

  (* Adding a rewind permission preserves separateness *)
  Lemma separate_rewind f p q r : q ⊥ r <-> rewind_perm f p q ⊥ r.
  Proof. apply separate_set_pre. Qed.


  (** ** Separating conjunction for permissions *)
  Program Definition sep_conj_perm (p q: perm) : perm :=
    {|
      pre := fun x => pre p x /\ pre q x;
      rely := fun x y => rely p x y /\ rely q x y;
      guar := clos_trans _ (fun x y => (guar p x y) \/ (guar q x y)) (* separateness implies each move is in the others' rely *) ;
      inv := fun x => inv p x /\ inv q x /\ p ⊥ q;
    |}.
  Next Obligation.
    apply PreOrder_clos_trans.
    repeat intro. left; reflexivity.
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

  Global Instance Proper_guar_eq_sep_conj_perm :
    Proper (guar_eq ==> guar_eq ==> guar_eq) sep_conj_perm.
  Proof.
    repeat intro; split; intros; eapply clos_trans_incl; try apply H1;
      intros; destruct H2;
      try (left; apply H; assumption); right; apply H0; assumption.
  Qed.

  Lemma sep_conj_guar_eq_commut' p q x y : guar (p ** q) x y -> guar (q ** p) x y.
  Proof.
    intros. eapply clos_trans_incl; [ | apply H ]; intros.
    destruct H0; [ right | left ]; assumption.
  Qed.

  Lemma sep_conj_guar_eq_commut p q : guar_eq (p ** q) (q ** p).
  Proof.
    - repeat intro. split; intro; apply sep_conj_guar_eq_commut'; assumption.
  Qed.

  Lemma sep_conj_guar_eq_assoc' p q r x y : guar (p ** (q ** r)) x y ->
                                            guar ((p ** q) ** r) x y.
  Proof.
    simpl; intros.
    rewrite clos_trans_clos_trans_or.
    rewrite clos_trans_or_commut in H.
    rewrite clos_trans_clos_trans_or in H.
    rewrite clos_trans_or_commut in H.
    rewrite <- clos_trans_or_assoc. assumption.
  Qed.

  Lemma sep_conj_guar_eq_assoc p q r : guar_eq (p ** (q ** r)) ((p ** q) ** r).
  Proof.
    split; [ apply sep_conj_guar_eq_assoc' | ].
    rewrite (sep_conj_guar_eq_commut (p ** q) r).
    rewrite (sep_conj_guar_eq_commut p (q ** r)).
    rewrite (sep_conj_guar_eq_commut q r).
    rewrite (sep_conj_guar_eq_commut p q).
    apply sep_conj_guar_eq_assoc'.
  Qed.

  Lemma sep_conj_invperm_guar_eq pred p : guar_eq (invperm pred ** p) p.
  Proof.
    repeat intro. simpl. rewrite clos_trans_eq_or; [ | typeclasses eauto ].
    rewrite clos_trans_trans; [ | typeclasses eauto ].
    reflexivity.
  Qed.

  Lemma sep_conj_perm_commut' : forall p q, p ** q <= q ** p.
  Proof.
    constructor.
    - intros x [? [? ?]]; simpl; split; intuition.
    - intros x y [? [? ?]]; simpl; split; intuition.
    (* - intros x y [? [? ?]]; simpl; split; intuition. *)
    (* - intros x y []; repeat split; auto. *)
    - intros; apply sep_conj_guar_eq_commut; assumption.
    - intros x [? [? ?]]; simpl; split; intuition.
  Qed.

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

  (* p ** q is the least upper bound of p and q when they are separate *)
  Lemma sep_conj_perm_lte p q r : p ⊥ q -> p <= r -> q <= r -> p ** q <= r.
  Proof.
    constructor; intros.
    - split; [ apply H0 | apply H1 ]; assumption.
    - split; [ apply H0 | apply H1 ]; assumption.
    - simpl in H3. induction H3.
      + destruct H3; [ apply H0 | apply H1 ]; assumption.
      + assert (guar r x y); [ apply IHclos_trans1; assumption | ].
        etransitivity; [ eassumption | ].
        apply IHclos_trans2. eapply inv_guar; eassumption.
    - split; [ apply H0 | split; [ apply H1 | ] ]; assumption.
  Qed.

  (* If p is separate from both q and r then it is separate from q ** r *)
  Lemma separate_sep_conj_perm p q r : p ⊥ q -> p ⊥ r -> p ⊥ q ** r.
  Proof.
    constructor; intros.
    - induction H3.
      + destruct H1 as [? [? ?]].
        destruct H3; [ apply (sep_l _ _ H) | apply (sep_l _ _ H0) ]; assumption.
      + assert (rely p x y); [ apply IHclos_trans1; assumption | ]. rewrite H3.
        apply IHclos_trans2; [ eapply inv_guar | eapply inv_rely]; eassumption.
    - destruct H2 as [? [? ?]].
      split; [ apply (sep_r _ _ H) | apply (sep_r _ _ H0) ]; assumption.
  Qed.

  (* The conjunction of two invperms is the invperm of their conjunction *)
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
    - rewrite sep_conj_guar_eq_commut in H0.
      rewrite sep_conj_invperm_guar_eq in H0. assumption.
    - split; [ | split ]; try assumption.
      apply separate_invperm; intros. eapply inv_guar; eauto.
  Qed.

  Lemma sep_conj_self_invperm p : eq_perm (p ** invperm (inv p)) p.
  Proof.
    split; [ apply sep_conj_self_invperm' | apply lte_l_sep_conj_perm ].
  Qed.

  (* A permission that is separate from itself can be duplicated *)
  Lemma dup_self_sep p : p ⊥ p -> eq_perm p (p ** p).
  Proof.
    intro self_sep; split; [ apply lte_l_sep_conj_perm; reflexivity | ].
    constructor; intros.
    - split; assumption.
    - split; assumption.
    - clear H. induction H0; [ destruct H | etransitivity ]; eassumption.
    - split; [ | split ]; assumption.
  Qed.

  (* Any invperm can always be duplicated *)
  Lemma invperm_dup pred : eq_perm (invperm pred) (invperm pred ** invperm pred).
  Proof.
    apply dup_self_sep. apply self_sep_trivial_guar; intros; reflexivity.
  Qed.

  (* add_pre_perm distributes over separating conjunction. Note that this only
     goes one way: you cannot in general recombine the conjunction of two
     add_pre_perms into one add_pre_perm *)
  Lemma add_pre_perm_conj pred p q :
    add_pre_perm pred p ** add_pre_perm pred q <= add_pre_perm pred (p ** q).
  Proof.
    constructor; intros.
    - destruct H as [? [? ?]].
      destruct H0 as [[? ?] [y [[? [? ?]] [? [? ?]]]]].
      split; split; try assumption; exists y; (split; [ | split ]; assumption).
    - destruct H0; split; assumption.
    - apply H0.
    - destruct H as [? [? ?]]. split; [ assumption | ].
      split; [ assumption | ].
      apply separate_add_pre. symmetry; apply separate_add_pre. symmetry; assumption.
  Qed.

  (* set_pre_perm distributes over separating conjunction. Note that this only
     goes one way: you cannot in general recombine the conjunction of two
     set_pre_perms into one set_pre_perm *)
  Lemma set_pre_perm_conj pred p q :
    set_pre_perm pred p ** set_pre_perm pred q <= set_pre_perm pred (p ** q).
  Proof.
    constructor; intros.
    - destruct H as [? [? ?]].
      destruct H0 as [y [[? [? ?]] [? [? ?]]]].
      split; exists y; (split; [ | split ]; assumption).
    - destruct H0; split; assumption.
    - apply H0.
    - destruct H as [? [? ?]]. split; [ assumption | ].
      split; [ assumption | ].
      apply separate_set_pre. symmetry; apply separate_set_pre. symmetry; assumption.
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

  Global Instance Proper_eq_perm_separate_impl :
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

  Global Instance Proper_eq_perm_separate_iff :
    Proper (eq_perm ==> eq_perm ==> iff) separate.
  Proof.
    repeat intro; split; apply Proper_eq_perm_separate_impl; try assumption;
      symmetry; assumption.
  Qed.

  (*
  Lemma sep_conj_perm_monotone_l p p' q :
    p' <= p -> p' ** q <= p ** q.
  Proof.
    constructor; cbn; intros.
    - destruct H0 as (? & ? & ?). destruct H1. split; auto. apply H; auto.
    - destruct H0 as (? & ? & ?). destruct H1. split; auto. apply H; auto.
    - destruct H0 as (? & ? & ?). induction H1.
      + constructor. destruct H1; eauto.
        (* apply H; auto. apply H0. *)
      + econstructor 2; eauto.
        eapply (clos_trans_preserves (fun x => inv p x /\ inv q x)) in H1_; auto.
        2: {
          intros. destruct H1. destruct H4.
          - split.
            apply H in H4; auto. eapply inv_guar; eauto.
            apply H in H4; auto. apply H3 in H4; auto. eapply inv_rely; eauto.
          - split.
            apply H3 in H4; auto. eapply inv_rely; eauto.
            eapply inv_guar; eauto.
        }
        destruct H1_. apply IHclos_trans2; auto.
    - destruct H0 as [? [? ?]].
  Abort.
   *)

  Lemma sep_conj_perm_monotone_l p p' q :
    p' <= p -> invperm (inv p) ** p' ** q <= p ** q.
  Proof.
    constructor; intros.
    - destruct H0 as [? [? ?]]. destruct H1. repeat split; eauto.
    - simpl. destruct H0 as [? [? ?]]. destruct H1. repeat split; eauto; intros.
      eapply inv_rely; eauto.
    - destruct H0 as [? [? ?]].
      rewrite sep_conj_invperm_guar_eq in H1.
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

  Lemma sep_conj_perm_monotone_r p q q' :
    q' <= q -> p ** (invperm (inv q) ** q') <= p ** q.
  Proof.
    intros. rewrite (sep_conj_perm_commut _ (invperm (inv q) ** q')).
    rewrite (sep_conj_perm_commut _ q).
    apply sep_conj_perm_monotone_l.
    assumption.
  Qed.

  Lemma sep_conj_perm_monotone p p' q q' :
    p' <= p -> q' <= q -> (invperm (inv p) ** p') ** (invperm (inv q) ** q') <= p ** q.
  Proof.
    etransitivity;
      [ apply sep_conj_perm_monotone_l | apply sep_conj_perm_monotone_r ];
      assumption.
  Qed.

  (* Separating conjunction is stricly monotone if the lesser permissions are
     separate *)
  Lemma sep_conj_perm_monotone_sep p p' q q' :
    p' ⊥ q' -> p' <= p -> q' <= q -> p' ** q' <= p ** q.
  Proof.
    constructor; intros.
    - destruct H2 as [? [? ?]]. destruct H3.
      split; [ apply H0 | apply H1 ]; assumption.
    - destruct H2 as [? [? ?]]. destruct H3.
      split; [ apply H0 | apply H1 ]; assumption.
    - assert (guar (p ** q) x y /\ inv (p ** q) y) as [? ?]; [ | assumption ].
      induction H3; [ destruct H3 | ].
      + destruct H2 as [? [? ?]].
        split; [ apply t_step; left; apply H0; assumption | ].
        split; [ | split; [ | assumption ]].
        * eapply inv_guar; [ | eassumption ]. apply H0; assumption.
        * eapply inv_rely; [ | eassumption ].
          apply (sep_r _ _ H5); try assumption.
          apply H0; assumption.
      + destruct H2 as [? [? ?]].
        split; [ apply t_step; right; apply H1; assumption | ].
        split; [ | split; [ | assumption ]].
        * eapply inv_rely; [ | eassumption ].
          apply (sep_l _ _ H5); try assumption.
          apply H1; assumption.
        * eapply inv_guar; [ | eassumption ]. apply H1; assumption.
      + destruct (IHclos_trans1 H2).
        destruct (IHclos_trans2 H4).
        split; [ | assumption ].
        etransitivity; eassumption.
    - destruct H2 as [? [? ?]].
      split; [ apply H0 | split; [ apply H1 | ]]; assumption.
  Qed.

  Lemma eq_perm_sep_conj_lte_l p p' q : eq_perm p p' -> p ** q <= p' ** q.
  Proof.
    constructor; intros.
    - destruct H0; destruct H1; split; eauto.
    - destruct H0; destruct H1; split; eauto.
    - simpl in H0. rewrite (eq_perm_eq_inv p' p) in H0; [ | symmetry; assumption ].
      rewrite <- H in H0.
      eapply (clos_trans_incl_pred (inv (p ** q)));
        [ | | apply H0 | apply H1 ]; intros.
      + eapply inv_guar; [ | eassumption ].
        destruct H3; apply t_step; [ left | right ]; assumption.
      + destruct H3; [ | right; assumption ].
        left. apply H; [ | assumption ]. apply H. destruct H2; assumption.
    - simpl in H0.
      rewrite (eq_perm_eq_inv p' p) in H0; [ | symmetry; assumption ].
      rewrite <- H in H0. apply H0.
  Qed.

  Global Instance Proper_eq_perm_sep_conj_perm :
    Proper (eq_perm ==> eq_perm ==> eq_perm) sep_conj_perm.
  Proof.
    repeat intro.
    etransitivity;
      [ split; apply eq_perm_sep_conj_lte_l; [ | symmetry ]; eassumption | ].
    rewrite (sep_conj_perm_commut _ x0). rewrite (sep_conj_perm_commut _ y0).
    split; apply eq_perm_sep_conj_lte_l; [ | symmetry ]; eassumption.
  Qed.


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


  Lemma sep_conj_perm_separate p q r : p ⊥ q -> p ⊥ r -> p ⊥ q ** r.
  Proof.
    constructor; intros.
    - induction H3; [ destruct H3 | ].
      + destruct H1 as [? [? ?]]. apply (sep_l _ _ H); assumption.
      + destruct H1 as [? [? ?]]. apply (sep_l _ _ H0); assumption.
      + assert (rely p x y); [ apply IHclos_trans1; assumption | ].
        etransitivity; [ eassumption | ]. apply IHclos_trans2.
        * eapply inv_guar; eassumption.
        * eapply inv_rely; eassumption.
    - destruct H2 as [? [? ?]].
      split; [ apply (sep_r _ _ H) | apply (sep_r _ _ H0) ]; assumption.
  Qed.

  Lemma separate_sep_conj_perm_l p q r : p ⊥ q ** r -> p ⊥ (invperm (inv (q ** r)) ** q).
  Proof.
    intros.
    apply separate_antimonotone; [ assumption | ].
    apply lte_l_sep_conj_perm.
  Qed.

  (*
  Lemma separate_invperm_conj_conj p q :
    p ⊥ q -> eq_perm (invperm (inv (p ** q)) ** p) (invperm (inv q) ** p).
  Proof.
    intro. simpl.
    repeat rewrite <- sep_conj_invperm_conj.
  Admitted.
   *)

  Lemma separate_conj_assoc p q r : p ⊥ q ** r -> q ⊥ r -> p ** q ⊥ r.
  Proof.
    split; [ split | ]; intros.
    - destruct H2 as [? [? ?]].
      eapply (sep_l _ _ H); try eassumption.
      + split; [ | split ]; assumption.
      + apply t_step; right; assumption.
    - destruct H2 as [? [? ?]].
      eapply (sep_l _ _ H0); assumption.
    - induction H3; [ destruct H3 | ].
      + destruct H1 as [? [? ?]].
        refine (proj2 (sep_r _ _ H _ _ _ _ _)); try assumption.
        split; [ | split ]; assumption.
      + destruct H1 as [? [? ?]].
        apply (sep_r _ _ H0); assumption.
      + assert (rely r x y); [ apply IHclos_trans1; assumption | ].
        etransitivity; [ eassumption | ].
        apply IHclos_trans2.
        * eapply inv_guar; eassumption.
        * eapply inv_rely; eassumption.
  Qed.


  Lemma sep_conj_perm_assoc' p q r :
    q ⊥ r -> (p ** (q ** r)) <= ((p ** q) ** r).
  Proof.
    split; intros.
    - destruct H1 as [[? ?] ?]. split; [ | split ]; assumption.
    - destruct H1 as [[? ?] ?]. split; [ | split ]; assumption.
    - rewrite sep_conj_guar_eq_assoc in H1. assumption.
    - destruct H0 as [[? [? ?]] [? ?]].
      split; [ assumption | ].
      split; [ split; [ | split ]; assumption | ].
      symmetry. rewrite sep_conj_perm_commut.
      apply separate_conj_assoc; symmetry;
        [ rewrite sep_conj_perm_commut | ]; assumption.
  Qed.

  Lemma sep_conj_perm_assoc p q r :
    p ⊥ q -> q ⊥ r -> eq_perm (p ** (q ** r)) ((p ** q) ** r).
  Proof.
    split; [ apply sep_conj_perm_assoc'; assumption | ].
    rewrite (sep_conj_perm_commut (p ** q) r).
    rewrite (sep_conj_perm_commut p (q ** r)).
    rewrite (sep_conj_perm_commut p q).
    rewrite (sep_conj_perm_commut q r).
    apply sep_conj_perm_assoc'; symmetry; assumption.
  Qed.


  Lemma separate_invperm_self_conj p q : invperm (inv (p ** q)) ⊥ p.
  Proof.
    apply separate_bigger_invperm. apply lte_l_sep_conj_perm.
  Qed.

  (* FIXME: sep_conj_perm_assoc_nonsep may not be necessary, and even if it is
  it could probably be proved in a better way using sep_conj_perm_assoc *)

  Lemma sep_conj_perm_assoc_nonsep_helper1 p q r :
    p ⊥ invperm (inv (q ** r)) ** q ->
    p ** (invperm (inv (q ** r)) ** q) ⊥ r ->
    p ⊥ q ** r.
  Proof.
    split; [ | split ]; intros.
    - induction H3; [ destruct H3 | ].
      + apply (sep_l _ _ H);
            [ | | apply sep_conj_invperm_guar_eq ]; try assumption.
        split; [ assumption | ].
        split; [ destruct H1; assumption | ].
        apply separate_invperm_self_conj.
      + destruct H1 as [? [? ?]].
        refine (proj1 (sep_l _ _ H0 _ _ _ _ _)); try assumption.
        split; [ | split ]; try assumption.
        split; [ | split ]; try assumption.
        * split; [ | split ]; try assumption.
        * apply separate_invperm_self_conj.
      + assert (rely p x y); [ apply IHclos_trans1; assumption | ].
        etransitivity; [ eassumption | ].
        apply IHclos_trans2.
        eapply inv_guar; eassumption.
        eapply inv_rely; eassumption.
    - refine (proj2 (sep_r _ _ H _ _ _ _ _)); try assumption.
      split; [ assumption | ].
      split; [ destruct H2; assumption | ].
      apply separate_invperm_self_conj.
    - apply (sep_r _ _ H0); try eassumption.
      + split; [ assumption | ].
        split; [ | assumption ].
        split; [ assumption | ].
        split; [ | apply separate_invperm_self_conj ].
        destruct H2; assumption.
      + destruct H2 as [? [? ?]]; assumption.
      + apply t_step; left; assumption.
  Qed.

  Lemma sep_conj_perm_assoc_nonsep_helper2 p q r :
    q ⊥ r -> p ⊥ q ** r -> p ** (invperm (inv (q ** r)) ** q) ⊥ r.
  Proof.
    split; [ split; [ | split ] | ]; intros.
    - destruct H2 as [? [[? [? ?]] ?]].
      apply (sep_l _ _ H0); try assumption.
      apply t_step; right; assumption.
    - destruct H2 as [? [[? [? ?]] ?]].
      split; [ | split; [ | assumption ] ].
      + eapply inv_rely; try eassumption.
        apply (sep_l _ _ H); assumption.
      + destruct H8 as [? [? ?]]; eapply inv_guar; eassumption.
    - destruct H2 as [? [[? [? ?]] ?]].
      apply (sep_l _ _ H); assumption.
    - rewrite sep_conj_invperm_guar_eq in H3.
      induction H3; [ destruct H3 | ].
      + destruct H1 as [? [[? [? ?]] ?]].
        refine (proj2 (sep_r _ _ H0 _ _ _ _ _)); assumption.
      + destruct H1 as [? [[? [? ?]] ?]]. apply (sep_r _ _ H); assumption.
      + assert (rely r x y); [ apply IHclos_trans1; assumption | ].
        etransitivity; [ eassumption | ].
        apply IHclos_trans2; [ | eapply inv_rely; eassumption ].
        eapply inv_guar; [ | eassumption ].
        rewrite sep_conj_invperm_guar_eq. assumption.
  Qed.

  (* FIXME: the <= direction should use sep_conj_perm_assoc' after first
  rewriting (q ** r) on the left to ((invperm (inv (q ** r)) ** q) ** r) *)
  Lemma sep_conj_perm_assoc_nonsep p q r :
    eq_perm (p ** (q ** r)) ((p ** (invperm (inv (q ** r)) ** q)) ** r).
  Proof.
    split; constructor; intros.
    - destruct H0 as [[? [? ?]] ?]. repeat split; assumption.
    - destruct H0 as [[? [? ?]] ?]. repeat split; assumption.
    - rewrite sep_conj_invperm_guar_eq.
      rewrite sep_conj_guar_eq_assoc in H0.
      assumption.
    - destruct H as [[? [[[? [? ?]] [? ?]] ?]] [? ?]].
      split; [ assumption | ].
      split; [ split; [ | split ]; assumption | ].
      apply sep_conj_perm_assoc_nonsep_helper1; assumption.
    - destruct H0 as [? [? ?]]; repeat split; assumption.
    - destruct H0 as [? [? ?]]. split; [ | assumption ].
      split; [ assumption | ]. split; [ | assumption ].
      destruct H as [? [? ?]]. split.
      + destruct H5. eapply inv_rely; eassumption.
      + destruct H5 as [? [? ?]]; split; [ | assumption ].
        eapply inv_rely; eassumption.
    - rewrite sep_conj_invperm_guar_eq in H0.
      rewrite sep_conj_guar_eq_assoc.
      assumption.
    - destruct H as [? [[? [? ?]] ?]].
      split; [ split; [ | split; [ split; [ | split ] | ] ] | split ];
        try assumption.
      * split; [ | split ]; assumption.
      * apply separate_invperm_self_conj.
      * apply separate_sep_conj_perm_l; assumption.
      * apply sep_conj_perm_assoc_nonsep_helper2; assumption.
  Qed.


  (* rewind_perm f p p is greater than p when f is in the rely of p *)
  Lemma rewind_self_gte f p :
    (forall x, inv p x -> pre p x -> rely p x (f x)) ->
    rewind_perm f p p >= p.
  Proof.
    constructor; intros; try assumption.
    simpl in H0. simpl in H1. destruct_ex_conjs H1; subst.
    eapply pre_respects; [ | eassumption ].
    etransitivity; [ apply H | ]; eassumption.
  Qed.

  (* rewind_perm f (p**q) q is greater than q when f is in the rely of q *)
  Lemma rewind_conj_rely_gte f p q :
    (forall x, inv (p**q) x -> pre (p**q) x -> rely q x (f x)) ->
    rewind_perm f (p ** q) q >= q.
  Proof.
    constructor; intros; try assumption.
    simpl in H0. simpl in H1. destruct_ex_conjs H1; subst.
    eapply pre_respects; [ | eassumption ].
    etransitivity; [ | eassumption ].
    apply H; [ | split; assumption ].
    repeat (split; try assumption).
  Qed.

  (* rewind_perm f (p**q) q is greater than q when f is in the guarantee of p
     and p is separate from q *)
  Lemma rewind_conj_sep_gte f p q :
    (forall x, inv (p**q) x -> pre (p**q) x -> guar p x (f x)) -> p ⊥ q ->
    rewind_perm f (p ** q) q >= q.
  Proof.
    intros; apply rewind_conj_rely_gte; intros.
    destruct H1 as [? [? ?]]. destruct H2.
    eapply sep_r; try apply H; try eassumption; repeat (split; try assumption).
  Qed.

  (* rewind_perm distributes over separating conjunction *)
  Lemma rewind_perm_conj f p q r :
    rewind_perm f p (q ** r) >= rewind_perm f p q ** rewind_perm f p r.
  Proof.
    constructor; intros; try assumption.
    - simpl in H; destruct_ex_conjs H. simpl in H0; destruct_ex_conjs H0; subst.
      split; (exists (f x1); split; [ assumption | ]; split; [ | assumption ];
              eexists; split; [ reflexivity | split; assumption ]).
    - simpl in H. destruct_ex_conjs H.
      split; [ assumption | ]. split; [ assumption | ].
      apply separate_rewind. symmetry. apply separate_rewind. symmetry; assumption.
  Qed.


  (** * Permission sets *)

  (** Perms = upwards-closed sets of permissions *)
  Record Perms :=
    {
      in_Perms : perm -> Prop;
      Perms_upwards_closed : forall p1 p2, in_Perms p1 -> p1 <= p2 -> in_Perms p2
    }.
  Notation "p ∈ P" := (in_Perms P p) (at level 60).

  (* Build a permission set as the upwards closure of a set of permissions *)
  Program Definition mkPerms (Ps : perm -> Prop) : Perms :=
    {| in_Perms p := exists p', Ps p' /\ p' <= p |}.
  Next Obligation.
    eexists; split; [ | etransitivity ]; eassumption.
  Qed.


  (* Permission set ordering, defined as superset *)
  Definition lte_Perms (P Q : Perms) : Prop :=
    forall p, p ∈ Q -> p ∈ P.

  Definition gte_Perms P Q := lte_Perms Q P.

  Notation "P ⊑ Q" := (lte_Perms P Q) (at level 60).
  Notation "P ⊒ Q" := (gte_Perms P Q) (at level 60).

  Global Instance lte_Perms_is_preorder : PreOrder lte_Perms.
  Proof.
    constructor; repeat intro; auto.
  Qed.

  Global Instance gte_Perms_is_preorder : PreOrder gte_Perms.
  Proof. constructor; repeat intro; auto. Qed.

  Global Instance Proper_lte_in_Perms :
    Proper (lte_Perms --> lte_perm ==> Basics.impl) in_Perms.
  Proof.
    repeat intro. apply H. eapply Perms_upwards_closed; eassumption.
  Qed.

  Global Instance Proper_gte_in_Perms :
    Proper (gte_Perms ==> gte_perm --> Basics.impl) in_Perms.
  Proof.
    repeat intro. apply H. eapply Perms_upwards_closed; eassumption.
  Qed.


  (* Permission set equality *)
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

  Global Instance Proper_eq_Perms_gte_Perms :
    Proper (eq_Perms ==> eq_Perms ==> Basics.flip Basics.impl) gte_Perms.
  Proof.
    do 6 red. intros. rewrite H. rewrite H0. auto.
  Qed.

  Global Instance Proper_eq_Perms_eq_perm_in_Perms :
    Proper (eq_Perms ==> eq_perm ==> Basics.flip Basics.impl) in_Perms.
  Proof.
    repeat intro; subst. apply H. eapply Perms_upwards_closed; eauto.
  Qed.


  (* The greatest permission set in the ordering *)
  Program Definition top_Perms : Perms :=
    {|
      in_Perms := fun r => False
    |}.

  (* Top is bigger than anything *)
  Lemma top_Perms_is_top : forall P, P ⊑ top_Perms.
  Proof.
    repeat intro. inversion H.
  Qed.

  (* The least permission set in the ordering *)
  Program Definition bottom_Perms : Perms :=
    {|
      in_Perms := fun r => True
    |}.

  (* Bottom is smaller than anything *)
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

  (* singleton_Perms preserves ordering, for rewriting *)
  Lemma lte_singleton_Perms p q :
    p <= q -> singleton_Perms p ⊑ singleton_Perms q.
  Proof.
    repeat intro. simpl in H0. simpl. etransitivity; eassumption.
  Qed.

  (* singleton_Perms preserves ordering, for rewriting *)
  Global Instance Proper_lte_singleton_Perms :
    Proper (lte_perm --> Basics.flip lte_Perms) singleton_Perms.
  Proof. repeat intro; eapply lte_singleton_Perms; eassumption. Qed.

  (* Same as above but using >= in place of <= *)
  Global Instance Proper_gte_singleton_Perms :
    Proper (gte_perm ==> Basics.flip lte_Perms) singleton_Perms.
  Proof. repeat intro; eapply lte_singleton_Perms; eassumption. Qed.

  (* singleton_Perms preserves equality, for rewriting *)
  Global Instance Proper_eq_singleton_Perms :
    Proper (eq_perm ==> eq_Perms) singleton_Perms.
  Proof.
    intros p q [? ?]; split; apply lte_singleton_Perms; assumption.
  Qed.

  (* The complete join / least upper bound of a set of permission sets = the
  intersection of all permission sets in the set *)
  Program Definition join_Perms (Ps : Perms -> Prop) : Perms :=
    {|
      in_Perms := fun p => forall P, Ps P -> p ∈ P
    |}.
  Next Obligation.
    eapply Perms_upwards_closed; eauto.
  Qed.

  (* A join is an upper bound for all its elements *)
  Lemma lte_join_Perms : forall (Ps : Perms -> Prop) P,
      (exists Q, Ps Q /\ P ⊑ Q) ->
      P ⊑ join_Perms Ps.
  Proof.
    repeat intro. destruct H as [Q [? ?]]. apply H1. apply H0. assumption.
  Qed.

  (* A join is the least upper bound for all its elements *)
  Lemma join_Perms_min : forall (Ps : Perms -> Prop) Q,
      (forall P, Ps P -> P ⊑ Q) ->
      join_Perms Ps ⊑ Q.
  Proof.
    repeat intro.
    eapply H; eauto.
  Qed.

  (* The binary join of two permission sets *)
  Definition join_Perms2 P Q : Perms := join_Perms (fun R => R = P \/ R = Q).

  (* If P is below either Q or R then it is below their binary join *)
  Lemma lte_join_Perms2 P Q R : (P ⊑ Q \/ P ⊑ R) -> P ⊑ join_Perms2 Q R.
  Proof.
    intros [? | ?]; apply lte_join_Perms; [ exists Q | exists R ]; split;
      solve [ assumption | left; reflexivity | right; reflexivity ].
  Qed.

  (* If R is above both P and Q then it is above their binary join *)
  Lemma join_Perms2_min P Q R : P ⊑ R -> Q ⊑ R -> join_Perms2 P Q ⊑ R.
  Proof.
    intros; apply join_Perms_min; intros.
    destruct H1; subst; assumption.
  Qed.

  (* A permission is in join_Perms2 P Q iff it is in P and Q *)
  Lemma join_Perms2_elem P Q p : p ∈ join_Perms2 P Q <-> p ∈ P /\ p ∈ Q.
  Proof.
    split; repeat intro.
    - split; [ apply (H P); left | apply (H Q); right ]; reflexivity.
    - destruct H. destruct H0; subst; assumption.
  Qed.

  (* Binary join is commutative *)
  Lemma join_Perms2_commute P Q : join_Perms2 P Q ≡ join_Perms2 Q P.
  Proof.
    split; apply join_Perms2_min; apply lte_join_Perms2;
      solve [ left; reflexivity | right; reflexivity ].
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

  (* A meet is a lower bound for all its elements *)
  Lemma lte_meet_Perms : forall (Ps : Perms -> Prop) P,
      (exists Q, Ps Q /\ Q ⊑ P) ->
      meet_Perms Ps ⊑ P.
  Proof.
    repeat intro. destruct H as [Q [? ?]]. exists Q.
    split; [ | apply H1 ]; assumption.
  Qed.

  (* A meet is the greatest lower bound for all its elements *)
  Lemma meet_Perms_max : forall (Ps : Perms -> Prop) Q,
      (forall P, Ps P -> Q ⊑ P) ->
      Q ⊑ meet_Perms Ps.
  Proof.
    repeat intro. destruct H0 as [? [? ?]].
    eapply H; eauto.
  Qed.

  (* Meet commutes with any monotonic permission set operation that FIXME *)
  Lemma meet_commutes Ps F `{Proper _ (lte_Perms ==> lte_Perms) F} :
    (forall p, p ∈ F (meet_Perms Ps) -> exists P, p ∈ F P /\ Ps P) ->
    F (meet_Perms Ps) ≡ meet_Perms (fun R => exists P, R = F P /\ Ps P).
  Proof.
    split.
    - apply meet_Perms_max; intros. destruct_ex_conjs H1; subst.
      apply H. apply lte_meet_Perms.
      eexists; split; [ eassumption | reflexivity ].
    - repeat intro. destruct (H0 p H1) as [P [? ?]].
      eexists. split; [ | eassumption ].
      exists P; split; [ reflexivity | assumption ].
  Qed.

  Definition meet_Perms2 P Q : Perms := meet_Perms (fun R => R = P \/ R = Q).

  (* Binary join commutes with meet *)
  Lemma join2_meet_commute P Qs :
    join_Perms2 P (meet_Perms Qs) ≡ meet_Perms (fun R => exists Q,
                                                    R = join_Perms2 P Q /\ Qs Q).
  Proof.
    split.
    - apply meet_Perms_max; intros. destruct_ex_conjs H; subst.
      apply join_Perms2_min; [ apply lte_join_Perms2; left; reflexivity | ].
      apply lte_meet_Perms. exists x. split; [ assumption | ].
      apply lte_join_Perms2; right; reflexivity.
    - repeat intro.
      destruct (H (meet_Perms Qs)) as [Q [? ?]]; [ right; reflexivity | ].
      eexists; split; [ exists Q; split; [ reflexivity | assumption ] | ].
      repeat intro. destruct H2; subst.
      + apply H; left; reflexivity.
      + assumption.
  Qed.

  (* The binary join of two meets can itself be written as a meet *)
  Lemma join2_two_meets Ps Qs :
    join_Perms2 (meet_Perms Ps) (meet_Perms Qs) ≡
      meet_Perms (fun R => exists P Q, R = join_Perms2 P Q /\ Ps P /\ Qs Q).
  Proof.
    rewrite join2_meet_commute. split.
    - apply meet_Perms_max; intros. destruct_ex_conjs H; subst.
      apply lte_meet_Perms.
      eexists; split; [ exists x0; split; [ reflexivity | assumption ] | ].
      apply join_Perms2_min; apply lte_join_Perms2; [ | right; reflexivity ].
      left. apply lte_meet_Perms. exists x; split; [ assumption | reflexivity ].
    - apply meet_Perms_max; intros. destruct_ex_conjs H; subst.
      rewrite join_Perms2_commute. rewrite join2_meet_commute.
      apply meet_Perms_max; intros. destruct_ex_conjs H; subst.
      apply lte_meet_Perms.
      eexists; split; [ | apply join_Perms2_commute ].
      eexists; eexists; split; [ reflexivity | split; try assumption ].
  Qed.

  (* mkPerms is equivalent to a meet of its elements *)
  Lemma mkPerms_meet Ps :
    mkPerms Ps ≡ meet_Perms (fun R => exists p, R = singleton_Perms p /\ Ps p).
  Proof.
    split; repeat intro.
    - simpl in H. destruct_ex_conjs H; subst. exists x0. split; assumption.
    - destruct H as [q [? ?]].
      exists (singleton_Perms q). split; [ | assumption ].
      eexists; split; [ reflexivity | assumption ].
  Qed.


  (* The permission set representing a proposition: if the proposition holds,
     then it is the trivial bottom permission, otherwise it is the inconsistent
     top permission *)
  Program Definition prop_Perms (P:Prop) : Perms :=
    {|
      in_Perms := fun _ => P
    |}.

  (* prop_Perms equals bottom iff P holds *)
  Lemma prop_Perms_bottom P : prop_Perms P ≡ bottom_Perms <-> P.
  Proof.
    split; [ | split ]; repeat intro.
    - destruct H. apply (H bottom_perm). apply I.
    - apply H.
    - apply I.
  Qed.

  (* prop_Perms equals top iff P does not hold *)
  Lemma prop_Perms_top P : prop_Perms P ≡ top_Perms <-> ~ P.
  Proof.
    split; [ | split ]; repeat intro.
    - destruct H. apply (H1 bottom_perm H0).
    - exfalso; assumption.
    - exfalso; apply H; apply H0.
  Qed.


  (* Map a function over a permission set to build a new one *)
  Definition mapPerms (f : perm -> perm) (P : Perms) : Perms :=
    mkPerms (fun y => exists x, in_Perms P x /\ y = f x).

  Global Instance Proper_lte_mapPerms f :
    Proper (lte_Perms ==> lte_Perms) (mapPerms f).
  Proof.
    intros p q lte_pq. repeat intro.
    simpl in H. destruct_ex_conjs H; subst.
    eexists. split; [ | eassumption ].
    eexists; split; [ | reflexivity ].
    apply lte_pq; assumption.
  Qed.

  Global Instance Proper_eq_mapPerms f :
    Proper (eq_Perms ==> eq_Perms) (mapPerms f).
  Proof.
    intros p q [? ?]. split; apply Proper_lte_mapPerms; assumption.
  Qed.

  (* mapPerms commutes with meet *)
  Lemma mapPerms_meet_commutes f Ps :
    mapPerms f (meet_Perms Ps) ≡ meet_Perms (fun R => exists P, R = mapPerms f P /\ Ps P).
  Proof.
    apply meet_commutes; [ typeclasses eauto | ]. intros.
    simpl in H. destruct_ex_conjs H; subst.
    eexists; split; [ | eassumption ].
    eexists; split; [ | eassumption ].
    eexists; split; [ eassumption | reflexivity ].
  Qed.

  (* We could equivalently have defined mapPerms as a meet *)
  Lemma mapPerms_as_meet f P :
    eq_Perms (mapPerms f P)
      (meet_Perms (fun R => exists p, in_Perms P p /\ R = singleton_Perms (f p))).
  Proof.
    split; repeat intro.
    - destruct H as [FP [[q [? ?]] ?]]; subst.
      exists (f q). split; [ | assumption ].
      exists q; split; [ assumption | reflexivity ].
    - destruct H as [fq [[q [? ?]] ?]]; subst.
      exists (singleton_Perms (f q)). split; [ | assumption ].
      eexists; split; [ eassumption | reflexivity ].
  Qed.

  (* f p is in mapPerms f P iff p is in P *)
  Lemma in_mapPerms f P p : in_Perms P p -> in_Perms (mapPerms f P) (f p).
  Proof.
    intros. exists (f p). split; [ | reflexivity ].
    exists p. split; [ assumption | reflexivity ].
  Qed.

  (* Mapping a singleton_Perms is the same as applying the function when the
     function is monotonic *)
  Lemma map_singleton_Perms f (p : perm) `{Proper _ (lte_perm ==> lte_perm) f} :
    eq_Perms (mapPerms f (singleton_Perms p)) (singleton_Perms (f p)).
  Proof.
    split; repeat intro.
    - exists (f p). split; [ | assumption ].
      exists p; split; simpl; reflexivity.
    - destruct H0 as [fp [[p' [? ?]] ?]]. subst. simpl in H0.
      simpl. etransitivity; [ | eassumption ].
      apply H; assumption.
  Qed.

  (* Mapping a mkPerms set with a monotonic function yields what you would
  expect *)
  Lemma map_mkPerms f Ps `{Proper _ (lte_perm ==> lte_perm) f} :
    eq_Perms (mapPerms f (mkPerms Ps))
      (mkPerms (fun p => exists p', Ps p' /\ p = f p')).
  Proof.
    split; repeat intro.
    - destruct H0 as [p' [[p'' [? ?]] ?]]; subst; simpl.
      exists (f p''). split; [ | assumption ].
      exists p''. split; [ | reflexivity ].
      exists p''. split; [ assumption | reflexivity ].
    - destruct H0 as [p1 [[p2 [[p3 [? ?]] ?]] ?]]; subst.
      exists (f p3); split.
      + exists p3. split; [ assumption | reflexivity ].
      + etransitivity; [ | eassumption ].
        apply H; assumption.
  Qed.


  (* Map a binary function over two permission sets to build a new one *)
  Definition mapPerms2 (f : perm -> perm -> perm) P Q : Perms :=
    mkPerms (fun r => exists p q, p ∈ P /\ q ∈ Q /\ r = f p q).

  (* We could equivalently have defined mapPerms2 as a meet *)
  Lemma mapPerms2_as_meet f P Q :
    mapPerms2 f P Q ≡
      meet_Perms (fun R => exists p q, p ∈ P /\ q ∈ Q /\ R = singleton_Perms (f p q)).
  Proof.
    unfold mapPerms2. rewrite mkPerms_meet.
    split; apply meet_Perms_max;
      intros R H; destruct_ex_conjs H; subst; apply lte_meet_Perms.
    - eexists. split; [ | reflexivity ].
      eexists; split; [ reflexivity | ].
      eexists; eexists; split; [ eassumption | split; [ eassumption | reflexivity ]].
    - eexists. split; [ | reflexivity ].
      eexists; eexists; split; [ eassumption | split; [ eassumption | reflexivity ]].
  Qed.

  Global Instance Proper_lte_Perms_mapPerms2 f :
    Proper (lte_Perms ==> lte_Perms ==> lte_Perms) (mapPerms2 f).
  Proof.
    intros P1 P2 lteP Q1 Q2 lteQ.
    repeat rewrite mapPerms2_as_meet.
    apply meet_Perms_max; intros. destruct_ex_conjs H; subst.
    apply lte_meet_Perms; eexists.
    split; [ | reflexivity ]. eexists; eexists.
    split; [ apply lteP; eassumption | ]. split; [ apply lteQ; eassumption | ].
    reflexivity.
  Qed.

  Global Instance Proper_eq_Perms_mapPerms2 f :
    Proper (eq_Perms ==> eq_Perms ==> eq_Perms) (mapPerms2 f).
  Proof.
    intros P1 P2 [? ?] Q1 Q2 [? ?].
    split; apply Proper_lte_Perms_mapPerms2; assumption.
  Qed.

  (* mapPerms2 of a singleton is a singleton *)
  Lemma mapPerms2_singleton f p q `{Proper _ (lte_perm ==> lte_perm ==> lte_perm) f} :
    mapPerms2 f (singleton_Perms p) (singleton_Perms q) ≡ singleton_Perms (f p q).
  Proof.
    split; repeat intro.
    - exists (f p q). split; [ | assumption ].
      exists p; exists q. simpl. split; [ | split ]; reflexivity.
    - simpl in H0. destruct_ex_conjs H0; subst.
      simpl. etransitivity; [ | eassumption ].
      apply H; assumption.
  Qed.

  (* f p q is in mapPerms2 f P Q if p in P and q in Q *)
  Lemma in_mapPerms2 f P Q p q : p ∈ P -> q ∈ Q -> f p q ∈ mapPerms2 f P Q.
  Proof.
    intros. exists (f p q). split; [ | reflexivity ].
    exists p; exists q. split; [ assumption | ].
    split; [ assumption | reflexivity ].
  Qed.


  (* The set of all add_pre_perm pred p permissions for p in P *)
  Definition add_pre pred P : Perms :=
    mkPerms (fun r => exists p, p ∈ P /\ r = add_pre_perm pred p).

  (* add_pre is monotonic wrt the inverse implication ordering on predicates and
     the ordering on permissions *)
  Global Instance Proper_lte_add_pre :
    Proper (pointwise_relation _ Basics.impl --> lte_Perms ==> lte_Perms) add_pre.
  Proof.
    intros pred1 pred2 Rpred P Q R_PQ r H.
    simpl. destruct H as [? [[p [? ?]] ?]]; subst.
    eexists; split;
      [ exists p; split; [ apply R_PQ; assumption | reflexivity ] | ].
    etransitivity; [ | eassumption ].
    apply Proper_lte_add_pre_perm; [ assumption | reflexivity ].
  Qed.

  Global Instance Proper_eq_add_pre :
    Proper (pointwise_relation _ iff ==> eq_Perms ==> eq_Perms) add_pre.
  Proof.
    intros pred1 pred2 H Q1 Q2 [? ?].
    split; apply Proper_lte_add_pre; try assumption;
      repeat intro; subst; apply H; assumption.
  Qed.

  Lemma add_pre_Perms_meet_commute pred Ps :
    add_pre pred (meet_Perms Ps) ≡ meet_Perms (fun Q => exists P, Q = add_pre pred P /\ Ps P).
  Proof.
    apply meet_commutes; [ apply Proper_lte_add_pre; reflexivity | intros ].
    simpl in H; destruct_ex_conjs H; subst.
    eexists; split; [ | eassumption ].
    eexists; split; [ | eassumption ].
    eexists; split; [ eassumption | reflexivity ].
  Qed.

  (* Adding a precondition yields a bigger permission set *)
  Lemma add_pre_gte_P (pred : config -> Prop) P : add_pre pred P ⊒ P.
  Proof.
    repeat intro. simpl in H. destruct_ex_conjs H; subst.
    eapply Perms_upwards_closed; [ eassumption | ].
    etransitivity; [ apply add_pre_perm_gte_p | apply H1 ].
  Qed.


  (* A rewind permission that had the same p before and after f was applied *)
  Definition rewind_same_perm (f : config -> config) p := rewind_perm f p p.

  (* The set of all permissions rewind_perm f p p for p in P *)
  Definition rewind f P : Perms := mapPerms (rewind_same_perm f) P.

  (* rewind is monotonic wrt the permission set ordering *)
  Global Instance Proper_lte_rewind f :
    Proper (lte_Perms ==> lte_Perms) (rewind f).
  Proof.
    repeat intro. simpl in H0; destruct_ex_conjs H0; subst.
    eexists; split; [ | apply H2 ]. eexists; split; [ | reflexivity ].
    apply H; assumption.
  Qed.

  (* rewind is Proper wrt permission set equality *)
  Global Instance Proper_eq_rewind f :
    Proper (eq_Perms ==> eq_Perms) (rewind f).
  Proof.
    intros P1 P2 [? ?]; split; apply Proper_lte_rewind; assumption.
  Qed.


  (* The set of perms rewind_perm f (p**q) q for p in P, q in Q, and p ⊥ q *)
  Definition rewind_conj f P Q : Perms :=
    mkPerms (fun r => exists p q,
                 p ∈ P /\ q ∈ Q /\ p ⊥ q /\ r = rewind_perm f (p ** q) q).

  (* Helper lemma to prove a rewind_perm is in rewind_conj *)
  Lemma rewind_conj_elem f P Q p q :
    p ∈ P -> q ∈ Q -> p ⊥ q -> rewind_perm f (p ** q) q ∈ rewind_conj f P Q.
  Proof.
    intros. eexists; split; [ | reflexivity ].
    exists p; exists q. repeat (split; [ assumption | ]). reflexivity.
  Qed.

  (* rewind_conj is monotonic wrt the permission set ordering *)
  Global Instance Proper_lte_rewind_conj f :
    Proper (lte_Perms ==> lte_Perms ==> lte_Perms) (rewind_conj f).
  Proof.
    intros P1 P2 lteP Q1 Q2 lteQ p H. simpl in H; destruct_ex_conjs H; subst.
    eapply Perms_upwards_closed; [ | eassumption ].
    apply rewind_conj_elem; [ apply lteP | apply lteQ | ]; assumption.
  Qed.

  (* rewind_conj is monotonic wrt permission set equality *)
  Global Instance Proper_eq_rewind_conj f :
    Proper (eq_Perms ==> eq_Perms ==> eq_Perms) (rewind_conj f).
  Proof.
    intros P1 P2 [? ?] Q1 Q2 [? ?].
    split; apply Proper_lte_rewind_conj; assumption.
  Qed.

  (* rewind_conj f P Q is greater than Q when f is in the guarantee of P *)
  Lemma rewind_conj_gte_Q f P Q :
    (forall p x, p ∈ P -> inv p x -> pre p x -> guar p x (f x)) ->
    rewind_conj f P Q ⊒ Q.
  Proof.
    repeat intro. simpl in H0; destruct_ex_conjs H0; subst.
    eapply Perms_upwards_closed; [ eassumption | ].
    etransitivity; [ | apply H2 ].
    apply rewind_conj_sep_gte; [ | assumption ].
    intros. destruct H4 as [? [? ?]]. destruct H5.
    apply H; assumption.
  Qed.

  (* rewind_conj f P commutes with meet *)
  Lemma rewind_conj_meet_commutes f P Qs :
    rewind_conj f P (meet_Perms Qs)
      ≡ meet_Perms (fun R => exists Q, R = rewind_conj f P Q /\ Qs Q).
  Proof.
    apply meet_commutes; [ apply Proper_lte_rewind_conj; reflexivity | ].
    intros. simpl in H. destruct_ex_conjs H; subst.
    eexists; split; [ | eassumption ].
    eexists. split; [ | eassumption ].
    eexists; eexists. repeat (split; [ eassumption | ]). reflexivity.
  Qed.


  (* The permission set built from removing the guarantees of perms in P *)
  Definition no_guar_Perms P : Perms := mapPerms no_guar P.


  (** ** Separating conjunction for permission sets *)
  Program Definition sep_conj_Perms (P Q : Perms) : Perms :=
    {|
      in_Perms := fun r => exists p q, p ∈ P /\ q ∈ Q /\ p ** q <= r /\ p ⊥ q
    |}.
  Next Obligation.
    exists H, H1. split; [| split; [| split]]; auto. etransitivity; eauto.
  Qed.
  Notation "P * Q" := (sep_conj_Perms P Q).

  Lemma lte_l_sep_conj_Perms : forall P Q, P ⊑ P * Q.
  Proof.
    intros P Q p' ?. destruct H as (p & q & ? & ? & ? & ?).
    eapply Perms_upwards_closed; eauto.
    etransitivity; eauto. apply lte_l_sep_conj_perm.
  Qed.

  Lemma lte_r_sep_conj_Perms : forall P Q, Q ⊑ P * Q.
  Proof.
    intros P Q q' ?. destruct H as (p & q & ? & ? & ? & ?).
    eapply Perms_upwards_closed; eauto.
    etransitivity; eauto. apply lte_r_sep_conj_perm.
  Qed.

  Lemma sep_conj_Perms_bottom_identity : forall P, bottom_Perms * P ≡ P.
  Proof.
    constructor; repeat intro.
    - exists bottom_perm, p. split; simpl; [auto | split; auto]. split; auto.
      rewrite sep_conj_perm_commut. apply sep_conj_perm_bottom.
      symmetry. apply separate_bottom.
    - destruct H as [? [? [_ [? [? ?]]]]].
      eapply (Perms_upwards_closed P); eauto.
      etransitivity; eauto. apply lte_r_sep_conj_perm.
  Qed.

  Lemma sep_conj_Perms_top_absorb : forall P, top_Perms * P ≡ top_Perms.
  Proof.
    constructor; repeat intro.
    - inversion H.
    - destruct H as [? [_ [[] _]]].
  Qed.

  Lemma sep_conj_Perms_monotone P P' Q Q' : P' ⊑ P -> Q' ⊑ Q -> P' * Q' ⊑ P * Q.
  Proof.
    repeat intro. destruct H1 as [? [? [? [? [? ?]]]]].
    exists x, x0. auto.
  Qed.

  Global Instance Proper_lte_Perms_sep_conj_Perms :
    Proper (lte_Perms ==> lte_Perms ==> lte_Perms) sep_conj_Perms.
  Proof.
    intros P1 P2 lteP Q1 Q2 lteQ; apply sep_conj_Perms_monotone; assumption.
  Qed.

  Global Instance Proper_eq_Perms_sep_conj_Perms :
    Proper (eq_Perms ==> eq_Perms ==> eq_Perms) sep_conj_Perms.
  Proof.
    repeat intro. etransitivity.
    - split; eapply sep_conj_Perms_monotone; try eapply H0; try eapply H.
    - split; eapply sep_conj_Perms_monotone; try eapply H0; try eapply H; reflexivity.
  Qed.

  Lemma sep_conj_Perms_perm: forall P Q p q,
      p ∈ P ->
      q ∈ Q ->
      p ⊥ q ->
      p ** q ∈ P * Q.
  Proof.
    intros. exists p, q. split; [| split; [| split]]; auto. reflexivity.
  Qed.

  (* Conjunction on permission sets is commutative *)
  Lemma sep_conj_Perms_commut : forall P Q, P * Q ≡ Q * P.
  Proof.
    split; repeat intro.
    - destruct H as [q [p' [? [? [? ?]]]]].
      exists p', q. split; [| split; [| split]]; auto.
      etransitivity; eauto. apply sep_conj_perm_commut.
      symmetry; auto.
    - destruct H as [p' [q [? [? [? ?]]]]].
      exists q, p'. split; [| split; [| split]]; auto.
      etransitivity; eauto. apply sep_conj_perm_commut.
      symmetry; auto.
  Qed.

  (* Helper lemma for associativity of conjunction on permission sets *)
  Lemma sep_conj_Perms_assoc_lte P Q R : P * (Q * R) ⊑ (P * Q) * R.
  Proof.
    intros pqr H.
    destruct H as [pq [r [[p [q [? [? [? ?]]]]] [? [? ?]]]]].
    exists p. exists ((invperm (inv pq) ** q) ** r).
    split; [ assumption | split; [ | split ] ].
    - exists (invperm (inv pq) ** q). exists r.
      split; [ | split; [ | split ] ].
      + eapply Perms_upwards_closed; [ eassumption | apply lte_r_sep_conj_perm ]. 
      + assumption.
      + reflexivity.
      + symmetry; apply separate_antimonotone; [ symmetry; assumption | ].
        etransitivity; [ apply lte_r_sep_conj_perm | eassumption ].
    - etransitivity; [ | eassumption ].
      etransitivity; [ | apply sep_conj_perm_monotone_l; apply H1 ].
      etransitivity; [ apply sep_conj_perm_assoc' | ].
      * symmetry; apply separate_antimonotone; [ symmetry; assumption | ].
        etransitivity; [ apply lte_r_sep_conj_perm | eassumption ].
      * rewrite (sep_conj_perm_commut (invperm (inv pq)) q).
        rewrite (sep_conj_perm_commut _ (p ** q)).
        rewrite sep_conj_perm_assoc; [ reflexivity | assumption | ].
        symmetry; apply separate_bigger_invperm.
        etransitivity; [ apply lte_r_sep_conj_perm | eassumption ].
    - symmetry. rewrite sep_conj_perm_commut. apply separate_conj_assoc.
      + rewrite <- sep_conj_perm_assoc.
        * apply separate_antimonotone;
            [ symmetry | rewrite sep_conj_perm_commut ]; assumption.
        * apply separate_bigger_invperm.
          etransitivity; [ apply lte_r_sep_conj_perm | eassumption ].
        * symmetry; assumption.
      + apply separate_conj_assoc; [ | symmetry; assumption ].
        rewrite sep_conj_perm_commut.
        apply separate_bigger_invperm. assumption.
  Qed.

  (* Conjunction on Perms sets is associative *)
  Lemma sep_conj_Perms_assoc P Q R : P * (Q * R) ≡ (P * Q) * R.
  Proof.
    split; [ apply sep_conj_Perms_assoc_lte | ].
    rewrite (sep_conj_Perms_commut (P * Q)).
    rewrite (sep_conj_Perms_commut P Q).
    rewrite (sep_conj_Perms_commut P (Q * R)).
    rewrite (sep_conj_Perms_commut Q R).
    apply sep_conj_Perms_assoc_lte.
  Qed.

  (* Helper lemma to distribute conjunctions over each other *)
  Lemma sep_conj_Perms_distrib P1 P2 Q1 Q2 :
    eq_Perms ((P1 * P2) * (Q1 * Q2)) ((P1 * Q1) * (P2 * Q2)).
  Proof.
    rewrite (sep_conj_Perms_commut P1 P2).
    rewrite (sep_conj_Perms_assoc _ Q1 Q2).
    rewrite <- (sep_conj_Perms_assoc P2 P1).
    rewrite (sep_conj_Perms_commut P2 (P1 * Q1)).
    rewrite <- (sep_conj_Perms_assoc _ P2 Q2).
    reflexivity.
  Qed.

  (* The conjunction with a meet is another meet *)
  Lemma sep_conj_Perms_meet_commute (Ps : Perms -> Prop) P :
    (meet_Perms Ps) * P ≡ meet_Perms (fun Q => exists P', Q = P' * P /\ Ps P').
  Proof.
    unshelve eapply (meet_commutes _ (fun Q => Q * P));
      [ intros Q1 Q2 ltQ; apply Proper_lte_Perms_sep_conj_Perms;
        [ assumption | reflexivity ] | ].
    intros. simpl in H; destruct_ex_conjs H; subst.
    eexists; split; [ | eassumption ].
    eexists; eexists. repeat (split; [ eassumption | ]). assumption.
  Qed.

  (* The conjunction of two meets is another meet *)
  Lemma sep_conj_Perms_meet2 (Ps Qs : Perms -> Prop) :
    meet_Perms Ps * meet_Perms Qs
      ≡ meet_Perms (fun R => exists P Q, R = P * Q /\ Ps P /\ Qs Q).
  Proof.
    split; repeat intro.
    - simpl in H; destruct_ex_conjs H; subst.
      simpl in H1; destruct_ex_conjs H1; subst.
      eexists; eexists.
      split; [ eexists; split; eassumption | ].
      split; [ eexists; split; eassumption | ]. split; assumption.
    - simpl in H; destruct_ex_conjs H; subst.
      eexists; split; [ eexists; eexists; split; [ reflexivity | ];
                        split; eassumption | ].
      eexists; eexists. repeat (split; try eassumption).
  Qed.

  (* The conjunction of a binary join is an upper bound on conjunctions with the
  Perms sets being joined *)
  Lemma lte_conj_join_Perms2 P Q R1 R2 : (P ⊑ Q * R1 \/ P ⊑ Q * R2) ->
                                         P ⊑ Q * join_Perms2 R1 R2.
  Proof.
    repeat intro. destruct H0 as [ q [ r [? [? [? ?]]]]].
    apply join_Perms2_elem in H1. destruct H1.
    destruct H; apply H; exists q; exists r; auto.
  Qed.


  (* The conjunction of singletons is the singleton of the conjunction *)
  Lemma sep_conj_singleton p q :
    p ⊥ q ->
    eq_Perms (singleton_Perms p * singleton_Perms q) (singleton_Perms (p ** q)).
  Proof.
    split; repeat intro.
    - exists p. exists q. simpl.
      split; [ reflexivity | ]. split; [ reflexivity | ].
      split; assumption.
    - destruct H0 as [p' [q' [? [? [? ?]]]]]. simpl.
      etransitivity; [ | eassumption ].
      apply sep_conj_perm_monotone_sep; assumption.
  Qed.

  (* The rewind of a singleton is a singleton of its rewind *)
  Lemma rewind_singleton f p :
    rewind f (singleton_Perms p) ≡ singleton_Perms (rewind_perm f p p).
  Proof.
    apply (map_singleton_Perms (fun _ => _)).
    repeat intro. apply Proper_lte_rewind_perm; assumption.
  Qed.

  (* The rewind_conj of singletons is a singleton of a rewind_perm *)
  Lemma rewind_conj_singleton f p q :
    p ⊥ q ->
    rewind_conj f (singleton_Perms p) (singleton_Perms q)
      ≡ singleton_Perms (rewind_perm f (p ** q) q).
  Proof.
    split; repeat intro.
    - simpl in H0. eexists; split; [ | eassumption ].
      exists p; exists q. simpl. repeat (split; [ reflexivity | ]).
      split; [ assumption | reflexivity ].
    - simpl in H0. destruct_ex_conjs H0; subst. simpl.
      etransitivity; [ | eassumption ].
      apply Proper_lte_rewind_perm; [ | assumption ].
      apply sep_conj_perm_monotone_sep; assumption.
  Qed.

  (* Distribute a rewind of P * Q when P allowed the update f *)
  Lemma rewind_of_conj f P Q :
    rewind f (P * Q) ⊒ rewind f P * rewind_conj f P Q.
  Proof.
    unfold rewind. rewrite mapPerms_as_meet.
    apply meet_Perms_max; intros R H. destruct_ex_conjs H; subst.
    simpl in H. destruct_ex_conjs H; subst.
    intros p p_in.
    apply (Perms_upwards_closed _ (rewind_perm f x0 x0 ** rewind_perm f (x0 ** x1) x1)).
    - eexists. eexists. split; [ | split; [ | split; [ reflexivity | ]]].
      + eexists; split; [ | reflexivity ]. eexists; split; [ eassumption | reflexivity ].
      + eexists; split; [ | reflexivity ].
        eexists; eexists. repeat (split; [ eassumption | ]). reflexivity.
      + apply separate_rewind. symmetry. apply separate_rewind. symmetry. assumption.
    - etransitivity; [ | apply p_in ].
      transitivity (rewind_perm f (x0 ** x1) (x0 ** x1));
        [ | apply Proper_lte_rewind_perm; assumption ].
      etransitivity; [ | apply rewind_perm_conj ].
      apply sep_conj_perm_monotone_sep.
      + repeat (apply separate_rewind; symmetry). assumption.
      + apply Proper_lte_rewind_perm; [ apply lte_l_sep_conj_perm | reflexivity ].
      + reflexivity.
  Qed.

  (* Distribute a rewind_conj over a separating conjunction *)
  Lemma rewind_conj_of_conj f P Q R :
    rewind_conj f P (Q * R) ⊒ rewind_conj f P Q * rewind_conj f P R.
  Proof.
    repeat intro. simpl in H; destruct_ex_conjs H; subst.
    rewrite <- H1.
    assert (x2 <= x1); [ etransitivity; [ apply lte_l_sep_conj_perm | eassumption ] | ].
    assert (x3 <= x1); [ etransitivity; [ apply lte_r_sep_conj_perm | eassumption ] | ].
    assert (invperm (inv x1) ** x2 ⊥ invperm (inv x1) ** x3).
    1: { rewrite sep_conj_perm_commut. apply separate_conj_assoc.
         - rewrite sep_conj_perm_assoc;
             [ | apply self_sep_invperm | apply separate_bigger_invperm; assumption ].
           rewrite <- invperm_dup.
           symmetry; apply separate_conj_assoc; [ | symmetry; assumption ].
           apply separate_bigger_invperm; rewrite sep_conj_perm_commut; assumption.
         - symmetry; rewrite sep_conj_perm_commut; apply separate_conj_assoc;
             [ | apply self_sep_invperm ].
           rewrite <- invperm_dup. symmetry; apply separate_bigger_invperm; assumption. }
    assert ((invperm (inv x1) ** x2) ** (invperm (inv x1) ** x3) <= x1).
    1: { apply sep_conj_perm_lte; try assumption;
         apply sep_conj_perm_lte; try assumption;
         try (apply lte_invperm; intros; assumption);
         apply separate_bigger_invperm; assumption. }
    assert (x0 ** (invperm (inv x1) ** (x2 ** x3)) <= x0 ** x1);
      [ apply sep_conj_perm_monotone_r; assumption | ].
    assert (x0 ⊥ invperm (inv x1) ** x2);
      [ apply separate_antimonotone; assumption | ].
    assert (x0 ⊥ invperm (inv x1) ** x3);
      [ apply separate_antimonotone; assumption | ].
    rewrite <- (Proper_lte_rewind_perm f _ _ H10 _ _ H9).
    rewrite rewind_perm_conj.
    exists (rewind_perm f (x0 ** (invperm (inv x1) ** x2)) (invperm (inv x1) ** x2)).
    exists (rewind_perm f (x0 ** (invperm (inv x1) ** x3)) (invperm (inv x1) ** x3)).
    split; [ | split; [ | split ]].
    - eexists. split; [ | reflexivity ]. exists x0. exists (invperm (inv x1) ** x2).
      split; [ assumption | ]. split; [ rewrite <- lte_r_sep_conj_perm; assumption | ].
      split; [ assumption | reflexivity ].
    - eexists. split; [ | reflexivity ]. exists x0. exists (invperm (inv x1) ** x3).
      split; [ assumption | ]. split; [ rewrite <- lte_r_sep_conj_perm; assumption | ].
      split; [ assumption | reflexivity ].
    - apply sep_conj_perm_monotone_sep.
      + apply separate_rewind. symmetry; apply separate_rewind. symmetry. assumption.
      + apply Proper_lte_rewind_perm; [ | reflexivity ].
        apply sep_conj_perm_monotone_sep; [ assumption | reflexivity | ].
        apply sep_conj_perm_monotone_sep;
          [ apply separate_bigger_invperm; assumption | reflexivity | ].
        apply lte_l_sep_conj_perm.
      + apply Proper_lte_rewind_perm; [ | reflexivity ].
        apply sep_conj_perm_monotone_sep; [ assumption | reflexivity | ].
        apply sep_conj_perm_monotone_sep;
          [ apply separate_bigger_invperm; assumption | reflexivity | ].
        apply lte_r_sep_conj_perm.
    - apply separate_rewind. symmetry; apply separate_rewind. symmetry. assumption.
  Qed.


  (* The field of a permission set P is the set of all configurations such that
  the precondition and invariant of some p in P holds *)
  Definition Perms_field (P : Perms) (x : config) : Prop :=
    exists p, p ∈ P /\ pre p x /\ inv p x.

  (* The field of a bigger permission is contained in that of a smaller one *)
  Lemma Perms_field_incl P Q x : P ⊒ Q -> Perms_field P x -> Perms_field Q x.
  Proof.
    intros H [p [? [? ?]]]. exists p. split; [ apply H; assumption | split; assumption ].
  Qed.

  (* If x is in the field of a separating conjunction then it is in the field of
     each conjunct *)
  Lemma Perms_field_conj_elim P Q x :
    Perms_field (P * Q) x -> Perms_field P x /\ Perms_field Q x.
  Proof.
    intros [p [? [? ?]]].
    remember H as H2. clear HeqH2.
    rewrite <- lte_r_sep_conj_Perms in H.
    rewrite <- lte_l_sep_conj_Perms in H2.
    split; eexists; split; try split; try eassumption.
  Qed.

  (* If x is in the field of a singleton then it is in the precondition and
     invariant of the permission used to form the singleton *)
  Lemma Perms_field_singleton_elim p x :
    Perms_field (singleton_Perms p) x -> pre p x /\ inv p x.
  Proof.
    intros [q [? [? ?]]]. simpl in H.
    split; [ eapply pre_inc | eapply inv_inc ]; eassumption.
  Qed.


  (* The set of permissions in P where we not only add a predicate to their
  preconditions but also require that the field of the resulting permission is
  possible, meaning that there is a state satisfying it *)
  Definition add_poss_pre pred P : Perms :=
    mkPerms (fun p => p ∈ add_pre pred P /\ exists x, pre p x /\ inv p x /\ pred x).

  (* add_poss_pre is monotonic wrt the inverse implication ordering on
     predicates and the ordering on permissions *)
  Global Instance Proper_lte_add_poss_pre :
    Proper (pointwise_relation _ Basics.impl --> lte_Perms ==> lte_Perms) add_poss_pre.
  Proof.
    intros pred1 pred2 Rpred P Q R_PQ p inQ.
    destruct inQ as [q [[? [x [? [? ?]]]] ?]].
    exists q. split; [ | assumption ].
    split.
    - rewrite R_PQ. rewrite Rpred. assumption.
    - exists x; split; [ | split ]; try assumption.
      apply Rpred; assumption.
  Qed.

  Global Instance Proper_eq_add_poss_pre :
    Proper ((eq ==> iff) ==> eq_Perms ==> eq_Perms) add_poss_pre.
  Proof.
    intros pred1 pred2 H Q1 Q2 [? ?].
    split; apply Proper_lte_add_poss_pre; try assumption;
      repeat intro; subst; apply (H _ _ (reflexivity _)); assumption.
  Qed.


  (** Separating implication *)
  Definition impl_Perms P Q := meet_Perms (fun R => R * P ⊒ Q).

  (* impl_Perms is covariant in its second argument and contravariant in its
     first argument *)
  Global Instance Proper_lte_Perms_impl_Perms :
    Proper (lte_Perms --> lte_Perms ==> lte_Perms) impl_Perms.
  Proof.
    intros P1 P2 lte_P Q1 Q2 lte_Q.
    apply meet_Perms_max; intros. apply lte_meet_Perms.
    exists P. split; [ | reflexivity ].
    etransitivity; [ | apply lte_Q ].
    etransitivity; [ | apply H ].
    apply sep_conj_Perms_monotone; [ reflexivity | assumption ].
  Qed.

  (* impl_Perms is Proper wrt permission set equality *)
  Global Instance Proper_eq_Perms_impl_Perms :
    Proper (eq_Perms ==> eq_Perms ==> eq_Perms) impl_Perms.
  Proof.
    intros P1 P2 [? ?] Q1 Q2 [? ?].
    split; apply Proper_lte_Perms_impl_Perms; assumption.
  Qed.

  (** Implication is the right adjoint of * *)
  Lemma adjunction : forall P Q R, P * Q ⊒ R <-> P ⊒ (impl_Perms Q R).
  Proof.
    intros. split; intros.
    - red. red. intros. simpl. exists P. auto.
    - apply (sep_conj_Perms_monotone _ _ Q Q) in H; intuition.
      red. etransitivity; [ | apply H ].
      unfold impl_Perms.
      rewrite sep_conj_Perms_meet_commute.
      apply meet_Perms_max. intros P' [? [? ?]]. subst. auto.
  Qed.

  (* bottom implies P is the same as P *)
  Lemma bottom_impl_Perms_eq P : eq_Perms (impl_Perms bottom_Perms P) P.
  Proof.
    split.
    - apply lte_meet_Perms. exists P.
      rewrite sep_conj_Perms_commut. rewrite sep_conj_Perms_bottom_identity.
      split; reflexivity.
    - apply meet_Perms_max; intros.
      rewrite sep_conj_Perms_commut in H.
      rewrite sep_conj_Perms_bottom_identity in H. assumption.
  Qed.

  (* An impl_Perms permission can be partially applied *)
  Lemma impl_Perms_partial_apply P1 P2 Q :
    P1 * impl_Perms (P1 * P2) Q ⊒ impl_Perms P2 Q.
  Proof.
    rewrite sep_conj_Perms_commut. unfold impl_Perms.
    rewrite sep_conj_Perms_meet_commute.
    apply meet_Perms_max. intros PQ [Q' [? ?]]; subst.
    apply lte_meet_Perms.
    eexists; split; [ | reflexivity ].
    rewrite <- sep_conj_Perms_assoc. assumption.
  Qed.

  Lemma impl_Perms_apply P Q : P * impl_Perms P Q ⊒ Q.
  Proof.
    transitivity (impl_Perms bottom_Perms Q);
      [ | rewrite bottom_impl_Perms_eq; reflexivity ].
    etransitivity; [ | apply impl_Perms_partial_apply ].
    rewrite (sep_conj_Perms_commut P bottom_Perms).
    rewrite sep_conj_Perms_bottom_identity.
    reflexivity.
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


  (* Lift a permission set to a unary permission set function on unit *)
  Definition liftP1 P : unit -> Perms := fun _ => P.

  (* The separating conjunction of unary permission set functions *)
  Definition sep_conj_Perms1 {A B} (P : A -> Perms) (Q : B -> Perms) :=
    fun ab => P (fst ab) * Q (snd ab).

  Notation "P *1 Q" := (sep_conj_Perms1 P Q) (at level 40, left associativity).

  (* Equality on unary permission set functions *)
  Definition eq_Perms1 {A} (P Q : A -> Perms) := forall a, eq_Perms (P a) (Q a).
  Notation "P ≡1 Q" := (eq_Perms1 P Q) (at level 60).

  Global Instance Equivalence_eq_Perms1 A : Equivalence (@eq_Perms1 A).
  Proof.
    constructor; repeat intro.
    - reflexivity.
    - symmetry; apply H.
    - etransitivity; [ apply H | apply H0 ].
  Qed.


End Permissions.

(* begin hide *)
(* Redefining notations outside the section. *)
Notation "p <= q" := (lte_perm p q).
Notation "p >= q" := (gte_perm p q).
Notation "p ≡≡ q" := (eq_perm p q) (at level 50).
Notation "p ⊥ q" := (separate p q) (at level 50).
Notation "p ** q" := (sep_conj_perm p q) (at level 40).
Notation "p ∈ P" := (in_Perms P p) (at level 60).
Notation "P ⊑ Q" := (lte_Perms P Q) (at level 60).
Notation "P ⊒ Q" := (gte_Perms P Q) (at level 60).
Notation "P ≡ Q" := (eq_Perms P Q) (at level 60).
Notation "P ≡1 Q" := (eq_Perms1 P Q) (at level 60).
Notation "P * Q" := (sep_conj_Perms P Q).
Notation "P *1 Q" := (sep_conj_Perms1 P Q) (at level 40, left associativity).
(*
Notation "P -⊑- Q" := (forall a, P a ⊑ Q a) (at level 60).
Notation "P -≡- Q" := (P -⊑- Q /\ Q -⊑- P) (at level 60).
*)

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
