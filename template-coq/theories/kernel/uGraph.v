Require Import Nat Bool String BinInt List Relations Lia.
Import ListNotations.
Require MSets.MSetWeakList.
Require Import MSetFacts MSetProperties.
From Template Require Import utils config Universes monad_utils.
Import ConstraintType. Import MonadNotation.
Local Open Scope nat_scope.


Module ConstraintSetFact := WFactsOn UnivConstraintDec ConstraintSet.
Module ConstraintSetProp := WPropertiesOn UnivConstraintDec ConstraintSet.



Inductive my_level := mLevel (_ : string) | mVar (_ : nat).

Inductive good_constraint :=
(* l <= l' *)
| gc_le : my_level -> my_level -> good_constraint
(* l < l' *)
| gc_lt : my_level -> my_level -> good_constraint
(* Set < Var n *)
| gc_lt_set : nat -> good_constraint
(* Set = Var n *)
| gc_eq_set : nat -> good_constraint.


Module GoodConstraintDec.
  Definition t : Set := good_constraint.
  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : RelationClasses.Equivalence eq := _.
  Definition my_level_dec : forall x y : my_level, {x = y} + {x <> y}.
    decide equality. apply string_dec. apply Peano_dec.eq_nat_dec.
  Defined.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
    unfold eq.
    decide equality. all: try apply my_level_dec.
    all: apply Peano_dec.eq_nat_dec.
  Defined.
End GoodConstraintDec.
Module GoodConstraintSet := MSets.MSetWeakList.Make GoodConstraintDec.
Module GoodConstraintSetFact := WFactsOn GoodConstraintDec GoodConstraintSet.
Module GoodConstraintSetProp := WPropertiesOn GoodConstraintDec GoodConstraintSet.

Definition GoodConstraintSet_pair x y
  := GoodConstraintSet.add y (GoodConstraintSet.singleton x).

(* None -> not satisfiable *)
(* Some empty -> useless *)
(* else: singleton or two elements set (l = l' -> {l<=l', l'<=l}) *)
Definition gc_of_constraint (uc : univ_constraint) : option GoodConstraintSet.t
  := let empty := Some GoodConstraintSet.empty in
     let singleton := fun x => Some (GoodConstraintSet.singleton x) in
     let pair := fun x y => Some (GoodConstraintSet_pair x y) in
     match uc with
     (* Prop _ _ *)
     | (Level.lProp, Le, _) => empty
     | (Level.lProp, Eq, Level.lProp) => empty
     | (Level.lProp, Eq, _) => None
     | (Level.lProp, Lt, Level.lProp) => None
     | (Level.lProp, Lt, _) => empty

     (* Set _ _ *)
     | (Level.lSet, Le, Level.lProp) => None
     | (Level.lSet, Le, _) => empty
     | (Level.lSet, Eq, Level.lProp) => None
     | (Level.lSet, Eq, Level.lSet) => empty
     | (Level.lSet, Eq, Level.Level _) => None
     | (Level.lSet, Eq, Level.Var n) => singleton (gc_eq_set n)
     | (Level.lSet, Lt, Level.lProp) => None
     | (Level.lSet, Lt, Level.lSet) => None
     | (Level.lSet, Lt, Level.Level _) => empty
     | (Level.lSet, Lt, Level.Var n) => singleton (gc_lt_set n)

     (* Level _ _ *)
     | (Level.Level _, Le, Level.lProp) => None
     | (Level.Level _, Le, Level.lSet) => None
     | (Level.Level l, Le, Level.Level l') => singleton (gc_le (mLevel l) (mLevel l'))
     | (Level.Level l, Le, Level.Var n) => singleton (gc_le (mLevel l) (mVar n))
     | (Level.Level _, Eq, Level.lProp) => None
     | (Level.Level _, Eq, Level.lSet) => None
     | (Level.Level l, Eq, Level.Level l') => pair (gc_le (mLevel l) (mLevel l')) (gc_le (mLevel l') (mLevel l))
     | (Level.Level l, Eq, Level.Var n) => pair (gc_le (mLevel l) (mVar n)) (gc_le (mVar n) (mLevel l))
     | (Level.Level _, Lt, Level.lProp) => None
     | (Level.Level _, Lt, Level.lSet) => None
     | (Level.Level l, Lt, Level.Level l') => singleton (gc_lt (mLevel l) (mLevel l'))
     | (Level.Level l, Lt, Level.Var n) => singleton (gc_lt (mLevel l) (mVar n))

     (* Var _ _ *)
     | (Level.Var _, Le, Level.lProp) => None
     | (Level.Var n, Le, Level.lSet) => singleton (gc_eq_set n)
     | (Level.Var n, Le, Level.Level l) => singleton (gc_le (mVar n) (mLevel l))
     | (Level.Var n, Le, Level.Var n') => singleton (gc_le (mVar n) (mVar n'))
     | (Level.Var _, Eq, Level.lProp) => None
     | (Level.Var n, Eq, Level.lSet) => singleton (gc_eq_set n)
     | (Level.Var n, Eq, Level.Level l) => pair (gc_le (mVar n) (mLevel l)) (gc_le (mLevel l) (mVar n))

     | (Level.Var n, Eq, Level.Var n') => pair (gc_le (mVar n) (mVar n')) (gc_le (mVar n') (mVar n))
     | (Level.Var _, Lt, Level.lProp) => None
     | (Level.Var _, Lt, Level.lSet) => None
     | (Level.Var n, Lt, Level.Level l) => singleton (gc_lt (mVar n) (mLevel l))
     | (Level.Var n, Lt, Level.Var n') => singleton (gc_lt (mVar n) (mVar n'))
     end.

Definition my_val0 (v : valuation) (l : my_level) : nat :=
  match l with
  | mLevel s => Pos.to_nat (v.(valuation_mono) s)
  | mVar x => v.(valuation_poly) x
  end.

Definition my_satisfies0 v (gc : good_constraint) : bool :=
  match gc with
  | gc_le l l' => my_val0 v l <=? my_val0 v l'
  | gc_lt l l' => my_val0 v l <? my_val0 v l'
  | gc_lt_set l => 0 <? v.(valuation_poly) l
  | gc_eq_set l => 0 =? v.(valuation_poly) l
  end.

Inductive on_Some {A} (P : A -> Prop) : option A -> Prop :=
| no_some : forall x, P x -> on_Some P (Some x).

Lemma on_Some_spec {A} (P : A -> Prop) z :
  on_Some P z <-> exists x, z = Some x /\ P x.
Proof.
  split. intros []. now eexists.
  intros [? [e ?]]. subst. now constructor.
Qed.

Definition my_satisfies v : GoodConstraintSet.t -> bool :=
  GoodConstraintSet.for_all (my_satisfies0 v).

Lemma if_true_false (b : bool) : (if b then true else false) = b.
  destruct b; reflexivity.
Qed.

Lemma my_satisfies_pair v gc1 gc2 :
  (my_satisfies0 v gc1 /\ my_satisfies0 v gc2) <->
  my_satisfies v (GoodConstraintSet_pair gc1 gc2).
Proof.
  cbn; destruct (GoodConstraintDec.eq_dec gc2 gc1); cbn;
    rewrite if_true_false.
  now destruct e. symmetry. apply andb_and.
Defined.


Ltac gc_of_constraint_tac :=
  match goal with
  | |- is_true (if _ then true else false) => rewrite if_true_false
  | |- is_true (_ <? _) => apply PeanoNat.Nat.ltb_lt
  | |- is_true (_ <=? _) => apply PeanoNat.Nat.leb_le
  | |- is_true (_ =? _) => apply PeanoNat.Nat.eqb_eq
  | |- is_true (my_satisfies _ (GoodConstraintSet_pair _ _))
               => apply my_satisfies_pair; cbn -[Nat.leb Nat.eqb]; split
  | H : is_true (if _ then true else false) |- _ => rewrite if_true_false in H
  | H : is_true (_ <? _) |- _ => apply PeanoNat.Nat.ltb_lt in H
  | H : is_true (_ <=? _) |- _ => apply PeanoNat.Nat.leb_le in H
  | H : is_true (_ =? _) |- _ => apply PeanoNat.Nat.eqb_eq in H
  | H : is_true (my_satisfies _ (GoodConstraintSet_pair _ _)) |- _
               => apply my_satisfies_pair in H; cbn -[Nat.leb Nat.eqb] in H;
                 destruct H
  end.

Lemma gc_of_constraint_spec v uc :
  satisfies0 v uc <-> on_Some (my_satisfies v) (gc_of_constraint uc).
Proof.
  split.
  - destruct 1; destruct l, l'; try constructor; try reflexivity.
    all: cbn -[Nat.leb Nat.eqb GoodConstraintSet_pair] in *.
    all: repeat gc_of_constraint_tac; lia.
  - destruct uc as [[[] []] []]; cbn; inversion 1; constructor.
    all: cbn -[Nat.leb Nat.eqb GoodConstraintSet_pair] in *; try lia.
    all: repeat gc_of_constraint_tac; lia.
Qed.

Definition add_gc_of_constraint uc (S : option GoodConstraintSet.t)
  := S1 <- S ;; S2 <- gc_of_constraint uc ;;
     ret (GoodConstraintSet.union S1 S2).

Definition gc_of_constraints (ctrs : constraints) : option GoodConstraintSet.t
  := ConstraintSet.fold add_gc_of_constraint
                        ctrs (Some GoodConstraintSet.empty).


Lemma iff_forall {A} B C (H : forall x : A, B x <-> C x)
  : (forall x, B x) <-> (forall x, C x).
  firstorder.
Defined.

Lemma gc_of_constraints_spec v ctrs :
  satisfies v ctrs <-> on_Some (my_satisfies v) (gc_of_constraints ctrs).
Proof.
  unfold my_satisfies, satisfies, ConstraintSet.For_all, gc_of_constraints.
  set (S := GoodConstraintSet.empty).
  rewrite ConstraintSet.fold_spec.
  etransitivity. eapply iff_forall.
  intro; eapply imp_iff_compat_r. eapply ConstraintSetFact.elements_iff.
  set (l := ConstraintSet.elements ctrs). simpl.
  transitivity ((forall uc, InA eq uc l -> satisfies0 v uc) /\
                (forall gc, GoodConstraintSet.In gc S -> my_satisfies0 v gc)). {
    intuition. inversion H0. }
  clearbody S; revert S; induction l; intro S.
  - split.
    + intro; constructor. apply GoodConstraintSetFact.for_all_1.
      intros x y []; reflexivity.
      intro; apply H.
    + intros HS. split. intros ux H; inversion H.
      cbn in HS. inversion_clear HS.
      apply GoodConstraintSetFact.for_all_2.
      intros x y []; reflexivity.
      assumption.
  - simpl. split.
    + intros [H1 H2].
      pose proof (proj1 (gc_of_constraint_spec v a)
                        (H1 a (InA_cons_hd _ eq_refl))) as H.
      apply on_Some_spec in H.
      destruct H as [X [HX1 HX2]].
      assert (add_gc_of_constraint a (Some S)
              = Some (GoodConstraintSet.union S X)). {
        cbn. rewrite HX1; reflexivity. }
      rewrite H. apply IHl. split.
      * intros uc H0. apply H1. now apply InA_cons_tl.
      * intros gc H0. apply GoodConstraintSetFact.union_1 in H0.
        induction H0. intuition.
        apply GoodConstraintSetFact.for_all_2 in HX2.
        apply HX2. assumption.
        intros x y []; reflexivity.
    + intros H.
      unfold add_gc_of_constraint in H at 2.
      cbn -[add_gc_of_constraint] in H.
      remember (gc_of_constraint a) as o; destruct o.
      * destruct (proj2 (IHl _) H) as [IH1 IH2]. clear IHl H.
        split. intuition. apply InA_cons in H. induction H.
        subst. apply gc_of_constraint_spec. rewrite <- Heqo.
        constructor. apply GoodConstraintSetFact.for_all_1.
        intros x y []; reflexivity.
        intros gc Hgc. apply IH2.
        now apply GoodConstraintSetFact.union_3.
        firstorder.
        intros gc Hgc. apply IH2.
        now apply GoodConstraintSetFact.union_2.
      * apply False_rect. revert H; clear.
        induction l. inversion 1.
        cbn -[add_gc_of_constraint].
        assert (add_gc_of_constraint a None = None) by reflexivity.
        now rewrite H.
Qed.



(* vertices of the graph are levels which are not Prop *)
Inductive vertice := lSet | Level (_ : string) | Var (_ : nat).

(* vertive to level *)
Definition vtl (v : vertice) : Level.t :=
  match v with
  | lSet => Level.lSet
  | Level x => Level.Level x
  | Var x => Level.Var x
  end.

(* level to vertice *)
Definition ltv (l : universe_level) : option vertice :=
  match l with
  | Level.lProp => None
  | Level.lSet => Some lSet
  | Level.Level x => Some (Level x)
  | Level.Var x => Some (Var x)
  end.

(* true is for 0, false for -1 *)
Definition edge : Set := vertice * bool * vertice.

(* bool to Z *)
Definition btz (b : bool) : Z := if b then 0 else -1.

Module VerticeDec.
  Definition t : Set := vertice.
  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : RelationClasses.Equivalence eq := _.
  Definition eq_refl : forall x : t, eq x x := @eq_refl _.
  Definition eq_sym : forall x y : t, eq x y -> eq y x := @eq_sym _.
  Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z := @eq_trans _.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
    unfold eq.
    decide equality. apply string_dec. apply Peano_dec.eq_nat_dec.
  Defined.
Definition eqb : t -> t -> bool := fun x y => if eq_dec x y then true else false.
End VerticeDec.
Module VerticeSet <: MSetInterface.WSetsOn VerticeDec := MSets.MSetWeakList.Make VerticeDec.
Module VerticeMap := FSets.FMapWeakList.Make VerticeDec.

Module EdgeDec.
  Definition t : Set := edge.
  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : RelationClasses.Equivalence eq := _.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
    unfold eq.
    decide equality. apply VerticeDec.eq_dec.
    decide equality. apply Bool.bool_dec.
    (* apply ZArith_dec.Z_eq_dec. *)
    apply VerticeDec.eq_dec.
  Defined.
End EdgeDec.
Module EdgeSet <: MSetInterface.WSetsOn EdgeDec := MSets.MSetWeakList.Make EdgeDec.

(* If [None] the constraint is inconsistent *)
(* If [Some empty] the constraint is useless *)
(* Set < l or Set <= l are supposed to be yet present in the graph *)
Definition edges_of_constraint (uc : univ_constraint) : option EdgeSet.t
  := let '(l1, t, l2) := uc in
     match ltv l1, t, ltv l2 with
     (* l <= Prop or l < Prop or l = Prop *)
     | _, _, None => None
     (* Prop <= l *)
     | None, Le, _ => Some EdgeSet.empty
     (* Prop = l *)
     | None, Eq, _ => None
     (* Prop < l  ->  idem as Set <= l *)
     | None, Lt, _ => Some EdgeSet.empty

     | Some lSet, Eq, Some (Level _) => None
     | Some (Level _), Eq, Some lSet => None
     | _, Lt, Some lSet => None
     | Some lSet, Le, Some _ => Some EdgeSet.empty

     | Some l, Le, Some l' => Some (EdgeSet.singleton (l, true, l'))
     | Some l, Lt, Some l' => Some (EdgeSet.singleton (l, false, l'))
     | Some l, Eq, Some l' => Some (EdgeSet.add (l', true, l) (EdgeSet.singleton (l, true, l')))
     end.

     (* (* l <= Prop or l < Prop or l = Prop *) *)
     (* | _, _, Level.lProp => None *)
     (* (* Prop <= l *) *)
     (* | (Level.lProp, Le, _) => Some EdgeSet.empty *)
     (* (* Prop = l *) *)
     (* | (Level.lProp, Eq, _) => None *)
     (* (* Prop < l  ->  idem as Set <= l *) *)
     (* | (Level.lProp, Lt, _) => Some EdgeSet.empty *)

     (* (* Set <= l *) *)
     (* | (Level.lSet, Le, _) => Some EdgeSet.empty *)
     (* (* Set < l *) *)
     (* | (Level.lSet, Lt, Level.lSet) => None *)
     (* | (Level.lSet, Lt, Level.Level _) => Some EdgeSet.empty *)
     (* | (Level.lSet, Lt, Level.Var x) => Some (EdgeSet.singleton (lSet, true, Var x)) *)
     (* (* Set = l *) *)
     (* | (Level.lSet, Eq, Level.lSet) => Some EdgeSet.empty *)
     (* | (Level.lSet, Eq, Level.Level _) => None *)
     (* | (Level.lSet, Eq, Level.Var x) => Some (EdgeSet.singleton (Var x, true, lSet)) *)
     (* (* l <= Set *) *)
     (* | (Level.Level l, Le, Level.lSet) =>  Some (EdgeSet.singleton (Level l, true, lSet)) *)
     (* | (Level.Var l, Le, Level.lSet) =>  Some (EdgeSet.singleton (Var l, true, lSet)) *)
     (* (* l < Set *) *)
     (* | (_, Lt, Level.lSet) => None *)
     (* (* l = Set *) *)
     (* | (Level.Level _, Eq, Level.lSet) =>  None *)
     (* | (Level.Var l, Eq, Level.lSet) =>  Some (EdgeSet.singleton (Var l, true, lSet)) *)
                                            
     (* (* l <= l' *) *)
     (* | (Level.Level l, Le, Level.Level l') =>  Some (EdgeSet.singleton (Level l, true, Level l')) *)
     (* | (Level.Var l, Le, Level.Level l') =>  Some (EdgeSet.singleton (Var l, true, Level l')) *)
     (* | (Level.Level l, Le, Level.Var l') =>  Some (EdgeSet.singleton (Level l, true, Var l')) *)
     (* | (Level.Var l, Le, Level.Var l') =>  Some (EdgeSet.singleton (Var l, true, Var l')) *)
     (* (* l < l' *) *)
     (* | (Level.Level l, Lt, Level.Level l') =>  Some (EdgeSet.singleton (Level l, false, Level l')) *)
     (* | (Level.Var l, Lt, Level.Level l') =>  Some (EdgeSet.singleton (Var l, false, Level l')) *)
     (* | (Level.Level l, Lt, Level.Var l') =>  Some (EdgeSet.singleton (Level l, false, Var l')) *)
     (* | (Level.Var l, Lt, Level.Var l') =>  Some (EdgeSet.singleton (Var l, false, Var l')) *)

     (* (* l = l' *) *)
     (* | (Level.Level l, Eq, Level.Level l') =>  Some (EdgeSet.add (Level l', true, Level l) (EdgeSet.singleton (Level l, true, Level l'))) *)
     (* | (Level.Var l, Eq, Level.Level l') =>  Some (EdgeSet.add (Level l', true, Var l) (EdgeSet.singleton (Var l, true, Level l'))) *)
     (* | (Level.Level l, Eq, Level.Var l') =>  Some (EdgeSet.add (Var l', true, Level l) (EdgeSet.singleton (Level l, true, Var l'))) *)
     (* | (Level.Var l, Eq, Level.Var l') =>  Some (EdgeSet.add (Var l', true, Var l) (EdgeSet.singleton (Var l, true, Var l'))) *)
     (* end. *)

(* If [None] the set of constraints is naively inconsistent *)
Definition edges_of_constraints (ctrs : constraints) : option EdgeSet.t :=
  ConstraintSet.fold (fun uc S => match edges_of_constraint uc, S with
                               | Some S1, Some S2 => Some (EdgeSet.union S1 S2)
                               | _, _ => None end) ctrs (Some EdgeSet.empty).


(* Prop is never in the graph *)
(* Nodes of the graph are nodes of the constraints + Set *)
(* For each universe, at least the constraint l > Set or l >= Set is here *)
Definition t  := VerticeSet.t × EdgeSet.t.

Definition init_graph : t :=
  (VerticeSet.singleton lSet, EdgeSet.empty).

(* without Prop nor Set *)
Definition nodes_of_level (l : universe_level) : VerticeSet.t :=
  match ltv l with
  | None => VerticeSet.empty
  | Some l=> VerticeSet.singleton l
  end.

Definition nodes_of_constraint (ctr : univ_constraint) : VerticeSet.t :=
  let '(l1, _, l2) := ctr in
  VerticeSet.union (nodes_of_level l1) (nodes_of_level l2).

Definition add_nodes_of_constraints (ctrs : constraints) :=
  ConstraintSet.fold (fun ctr => VerticeSet.union (nodes_of_constraint ctr)) ctrs.

(* If [None] the set of constraints is naively inconsistent *)
Definition make_graph (ctrs : constraints) : option t
  := let V := add_nodes_of_constraints ctrs (VerticeSet.singleton lSet) in
     let E0 := VerticeSet.fold (fun v S => match v with
                                 | Level l => EdgeSet.add (lSet, false, Level l) S
                                 | Var l => EdgeSet.add (lSet, true, Var l) S
                                 | _ => S end) V EdgeSet.empty in
     match edges_of_constraints ctrs with
     | Some E1 => Some (V, EdgeSet.union E0 E1)
     | None => None
     end.

Section Graph.
  Context (φ : t).

  Inductive R0s : vertice -> vertice -> Prop :=
  | R00 l : R0s l l
  | R01 l1 l2 l3 : R0s l1 l2 -> EdgeSet.In (l2,true,l3) (snd φ) -> R0s l1 l3.

  (* Definition R0s_dec : forall x y, {R0s y x} + {~ R0s y x}. *)
  (* Proof. *)


  Inductive R : vertice -> vertice -> Prop :=
  | Rintro l1 l2 l3 l4 : R0s l1 l2 -> EdgeSet.In (l2,false,l3) (snd φ)
                         -> R0s l3 l4 -> R l1 l4.

  Definition acyclic := forall l, Acc R l.

  Definition Rs : relation vertice :=
    clos_trans _ (fun l l' => EdgeSet.In (l, true, l') (snd φ)
                           \/ EdgeSet.In (l, false, l') (snd φ)).
  
  Definition R_dec : forall x y, {R y x} + {~ R y x}.
  (* Proof. *)
  (*   intros x y H; revert y; induction H; intro y. *)
  (*   pose (VerticeSet.exists_ (fun pred => EdgeSet.exists_ (fun e => (VerticeDec.eqb (fst (fst e)) pred) && (VerticeDec.eqb (snd e) x)) (snd φ)) (fst φ)). *)
  (*   case_eq b; intro ee. *)
  (*   subst b. apply VerticeSet.exists_spec in ee. *)
    
  (*   remember b. *)
  (*   destruct b0. *)
  (*   assert (pred : vertice). *)
  Admitted.    


  Conjecture Rs_dec : forall x y, {Rs y x} + {~ Rs y x}.

  Fixpoint filter_pack {A} (P : A -> Prop) (HP : forall x, {P x} + {~ P x})
           (l : list A) {struct l} : list {x : A & P x} :=
    match l with
    | [] => []
    | x :: l => match HP x with
               | left p => (existT _ _ p) :: (filter_pack P HP l)
               | right _ => filter_pack P HP l
               end
    end.

  Definition d (s l : vertice) (H : Acc R l) : option Z.
    destruct (Rs_dec s l) as [_|_]; [apply Some|apply None].
    induction H as [v H d].
    simple refine (let preds := filter_pack (fun v' => R v' v) (R_dec v)
                                            (VerticeSet.elements (fst φ)) in _).
    exact (List.fold_left (fun n X => Z.min n (d X.1 X.2)) preds 0).
  Defined.

End Graph.  

Definition d_Set ctrs φ (e : make_graph ctrs = Some φ)
  : forall l, VerticeSet.In l (fst φ) -> Rs φ lSet l.
Abort.

Definition valuation_of_graph φ (H: well_founded (R φ)) : valuation.
Proof.
  pose (V := fst φ). pose (E := snd φ).
  unshelve econstructor.
  refine (fun s => if VerticeSet.mem (Level s) V then BinIntDef.Z.to_pos (option_get 1 (d φ lSet (Level s) (H _))) else 1%positive).
  refine (fun n => if VerticeSet.mem (Var n) V then Z.to_nat (option_get 0 (d φ lSet (Var n) (H _))) else 0%nat).
Defined.

Lemma Acc_ok1 ctrs : (exists φ, make_graph ctrs = Some φ /\ well_founded (R φ)) -> consistent ctrs.
Proof.
  intros [φ [H1 H2]].
  exists (valuation_of_graph φ H2).
  unfold satisfies. intros [[l1 []] l2] Huc; constructor.
  - destruct l1, l2.
        * admit.
        * admit.
        * admit.
        * admit.
        * admit.
        * admit.
        * admit.
        * admit.
        * admit.
        * admit.
        * cbn.
 assert (e: d φ lSet (Level s) (H2 (Level s)) < d φ lSet (Level s0) (H2 (Level s0))).
 

assert (d φ lSet l1 < d φ lSet l2).


  unfold satisfies0. intros uc Huc.
  

  revert φ H1 H2.
  induction ctrs using ConstraintSetProp.set_induction;
    intros φ H1 H2.
  - intros x Hx. apply False_rect.
    apply (ConstraintSetFact.empty_iff x).
    eapply ConstraintSetFact.In_m. reflexivity.
    2: eassumption. symmetry.
    now apply ConstraintSetProp.empty_is_empty_1.
  - assert (satisfies0 (valuation_of_graph φ H2) x) . {
      assert (Hc : ConstraintSet.In x ctrs2). admit. (* ok *)
      clear H H0 IHctrs1 ctrs1.
      destruct x as [[l1 []] l2]; econstructor.
      + destruct l1, l2.
        * admit.
        * admit.
        * admit.
        * admit.
        * admit.
        * admit.
        * admit.
        * admit.
        * admit.
        * admit.
        * cbn. assert (e: VerticeSet.mem (Level s) (fst φ) = true). admit.
          rewrite e.
          assert ((d φ lSet (Level s) (H2 (Level s))) < (d φ lSet (Level s) (H2 (Level s0)))).

}

 unfold make_graph in H1.
    unfold edges_of_constraints in H1.
    rewrite ConstraintSetProp.fold_1b in H1.
    unfold add_nodes_of_constraints in H1.
    rewrite ConstraintSetProp.fold_1b in H1.


Definition is_Some {A} (x : option A) := exists a, x = Some a.

Conjecture Acc_ok : forall ctrs, consistent ctrs <-> exists φ, make_graph ctrs = Some φ /\ well_founded (R φ).

Conjecture d_ok   : forall ctrs φ (e : make_graph ctrs = Some φ) (H : well_founded (R φ)) l l',
    (exists k, forall v, satisfies v ctrs -> (val0 v (vtl l) <= (val0 v (vtl l')) + k)%Z)
    <-> is_Some (d φ l l' (H _)).

Conjecture d_ok2  : forall ctrs φ (e : make_graph ctrs = Some φ) (H : well_founded (R φ)) l l' k,
    (forall v, satisfies v ctrs -> (val0 v (vtl l) <= (val0 v (vtl l')) + k)%Z)
    <-> (forall k', d φ l l' (H _) = Some k' -> k >= k').




Section BellmanFord.

  Context (φ : t).

  (* Z ∪ +∞ *)
  (* None is for +∞ *)
  Definition Zbar := Z.

  (* For each node: predecessor and distance from the source *)
  Definition pred_graph := VerticeMap.t (vertice * Zbar).

  (* Definition add_node_pred_graph n : pred_graph -> pred_graph *)
  (* := VerticeMap.add n None. *)

  Definition init_pred_graph s : pred_graph :=
    (* let G := EdgeSet.fold *)
    (* (fun '(l1,_,l2) G => add_node_pred_graph l2 (add_node_pred_graph l1 G)) *)
    (* φ (VerticeMap.empty _) in *)
    VerticeMap.add s (s, 0) (VerticeMap.empty _).

  Definition relax (e : edge) (G : pred_graph) : pred_graph :=
    let '((u, w), v) := e in
    match VerticeMap.find u G, VerticeMap.find v G with
    | Some (_, ud), Some (_, vd) => if vd >? (ud + btz w) then
                                     VerticeMap.add v (u, ud + btz w) G
                                   else G
    | Some (_, ud), None => VerticeMap.add v (u, ud + btz w) G
    | _, _ => G
    end.

  Definition BellmanFord s : pred_graph :=
    let G := init_pred_graph s in
    let G' := VerticeSet.fold (fun _ => EdgeSet.fold relax (snd φ)) (fst φ) G in
    G'.

  (* true if all is ok *)
  Definition no_universe_inconsistency : bool :=
    let G := BellmanFord lSet in
    let negative_cycle := EdgeSet.exists_ (fun '((u,w),v) =>
                          match VerticeMap.find u G, VerticeMap.find v G with
                          | Some (_, ud), Some (_, vd) => Z.gtb vd (ud + btz w)
                          | _, _ => false
                          end) (snd φ) in
    negb negative_cycle.

  (** *** Universe comparisons *)

  (* If enforce l1 l2 = Some n, the graph enforces that l2 is at least l1 + n *)
  (* i.e. l1 + n <= l2 *)
  (* If None nothing is enforced by the graph between those two levels *)
  Definition enforce (u v : vertice) : option Z :=
    let G := BellmanFord u in
    match VerticeMap.find v G with
    | Some (_, vd) => Some (Z.opp vd)
    | None => None
    end.

  Definition check_le_vertice (l1 l2 : vertice) : bool :=
    match enforce l1 l2 with
    | Some k => Z.geb k 0
    | None => false
    end.

  Definition check_lt_vertice (l1 l2 : vertice) : bool :=
    match enforce l1 l2 with
    | Some k => Z.geb k 1
    | None => false
    end.

  Definition check_eq_vertice (l1 l2 : vertice) : bool :=
    check_le_vertice l1 l2 && check_le_vertice l2 l1.


  Definition check_le_level (l1 l2 : universe_level) : bool :=
    match ltv l1, ltv l2 with
    | None, _ => true
    | _, None => false
    | Some l1, Some l2 => match enforce l1 l2 with
                         | Some k => Z.geb k 0
                         | None => false
                         end
    end.

  Definition check_lt_level (l1 l2 : universe_level) : bool :=
    match ltv l1, ltv l2 with
    | _, None => false
    | None, _ => true
    | Some l1, Some l2 => match enforce l1 l2 with
                         | Some k => Z.geb k 1
                         | None => false
                         end
    end.

  Definition check_eq_level (l1 l2 : universe_level) : bool :=
    check_le_level l1 l2 && check_le_level l2 l1.


  Definition check_constraint (cstr : univ_constraint) : bool :=
    let '(l, d, r) := cstr in
    match d with
    | Eq => check_eq_level l r
    | Lt => check_lt_level l r
    | Le => check_le_level l r
    end.

  Definition check_constraints (cstrs : ConstraintSet.t) : bool :=
    ConstraintSet.for_all check_constraint cstrs.

  Definition check_le_level_expr (e1 e2 : Universe.Expr.t) : bool :=
    match ltv (fst e1), ltv (fst e2) with
    | None, _ => true
    | _, None => false
    | Some l1, Some l2 =>
      match enforce l1 l2 with
      | None => false
      | Some k => match snd e1, snd e2 with
                 | false, false
                 | true, true => k >=? 0
                 | true, false => k >=? 1
                 | false, true => k >=? -1
                 end
      end
    end.

  Definition check_lt_level_expr (e1 e2 : Universe.Expr.t) : bool :=
    match ltv (fst e1), ltv (fst e2) with
    | _, None => false
    | None, _ => true
    | Some l1, Some l2 =>
      match enforce l1 l2 with
      | None => false
      | Some k => match snd e1, snd e2 with
                 | false, false
                 | true, true => k >=? 1
                 | true, false => k >=? 2
                 | false, true => k >=? 0
                 end
      end
    end.

  Definition check_eq_level_expr (e1 e2 : Universe.Expr.t) : bool :=
    check_le_level_expr e1 e2 && check_le_level_expr e2 e1.

  Definition exists_bigger_or_eq (e1 : Universe.Expr.t) (u2 : Universe.t) : bool :=
    Universe.existsb (check_le_level_expr e1) u2.

  Definition exists_strictly_bigger (e1 : Universe.Expr.t) (u2 : Universe.t) : bool :=
    Universe.existsb (check_lt_level_expr e1) u2.

  Definition check_lt (u1 u2 : Universe.t) : bool :=
    Universe.for_all (fun e => exists_strictly_bigger e u2) u1.

  Definition check_leq0 (u1 u2 : Universe.t) : bool :=
    Universe.for_all (fun e => exists_bigger_or_eq e u2) u1.

  (** We try syntactic equality before checking the graph. *)
  Definition check_leq `{checker_flags} s s' :=
    negb check_univs || Universe.equal s s' || check_leq0 s s'.

  Definition check_eq `{checker_flags} s s' :=
    negb check_univs || Universe.equal s s' || (check_leq0 s s' && check_leq0 s' s).

  Definition check_eq_instance `{checker_flags} u v :=
    Instance.equal_upto check_eq_level u v.

End BellmanFord.


Section Specif.
  Conjecture no_universe_inconsistency_ok : forall φ, reflect (well_founded (R φ)) (no_universe_inconsistency φ).

  Local Existing Instance default_checker_flags.

  (* TODO: lower level conjecture *)
  Conjecture check_leq_specif
    : forall ctrs φ (e : make_graph ctrs = Some φ) u1 u2, reflect (leq_universe ctrs u1 u2) (check_leq φ u1 u2).

  Conjecture check_eq_specif
    : forall ctrs φ (e : make_graph ctrs = Some φ) u1 u2, reflect (eq_universe ctrs u1 u2) (check_eq φ u1 u2).
End Specif.

  (* Definition check_eq_refl `{checker_flags} u : check_eq φ u u = true. *)
  (*   unfold check_eq; destruct check_univs; cbn; [|reflexivity]. *)

  (* Conjecture eq_universe_instance_refl : forall `{checker_flags} u, eq_universe_instance u u = true. *)
  (* Conjecture eq_universe_leq_universe : forall `{checker_flags} x y, *)
  (*     eq_universe x y = true -> leq_universe x y = true. *)
  (* Conjecture leq_universe_product_l : forall `{checker_flags} s1 s2, *)
  (*     leq_universe s1 (Universe.sort_of_product s1 s2) = true. *)
  (* Conjecture leq_universe_product_r : forall `{checker_flags} s1 s2, *)
  (*     leq_universe s2 (Universe.sort_of_product s1 s2) = true. *)




    (* Inductive super_result := *)
    (* | SuperSame (_ : bool) *)
    (* (* The level expressions are in cumulativity relation. boolean *)
    (*        indicates if left is smaller than right?  *) *)
    (* | SuperDiff (_ : comparison). *)
    (* (* The level expressions are unrelated, the comparison result *)
    (*        is canonical *) *)

    (* (** [super u v] compares two level expressions, *)
    (*    returning [SuperSame] if they refer to the same level at potentially different *)
    (*    increments or [SuperDiff] if they are different. The booleans indicate if the *)
    (*    left expression is "smaller" than the right one in both cases. *) *)
    (* Definition super (x y : t) : super_result := *)
    (*   match Level.compare (fst x) (fst y) with *)
    (*   | Eq => SuperSame (bool_lt' (snd x) (snd y)) *)
    (*   | cmp => *)
    (*       match x, y with *)
    (*       | (l, false), (l', false) => *)
    (*         match l, l' with *)
    (*         | Level.lProp, Level.lProp => SuperSame false *)
    (*         | Level.lProp, _ => SuperSame true *)
    (*         | _, Level.lProp => SuperSame false *)
    (*         | _, _ => SuperDiff cmp *)
    (*         end *)
    (*       | _, _ => SuperDiff cmp *)
    (*       end *)
    (*   end. *)


  (* Fixpoint merge_univs (fuel : nat) (l1 l2 : list Expr.t) : list Expr.t := *)
  (*   match fuel with *)
  (*   | O => l1 *)
  (*   | S fuel => match l1, l2 with *)
  (*              | [], _ => l2 *)
  (*              | _, [] => l1 *)
  (*              | h1 :: t1, h2 :: t2 => *)
  (*                match Expr.super h1 h2 with *)
  (*                | Expr.SuperSame true (* h1 < h2 *) => merge_univs fuel t1 l2 *)
  (*                | Expr.SuperSame false => merge_univs fuel l1 t2 *)
  (*                | Expr.SuperDiff Lt (* h1 < h2 is name order *) *)
  (*                  => h1 :: (merge_univs fuel t1 l2) *)
  (*                | _ => h2 :: (merge_univs fuel l1 t2) *)
  (*                end *)
  (*              end *)
  (*   end. *)



(* (* The monomorphic levels are > Set while polymorphic ones are >= Set. *) *)
(* Definition add_node (l : Level.t) (G : t) : t *)
(*   := let levels := LevelSet.add l (fst G) in *)
(*      let constraints := *)
(*          match l with *)
(*          | Level.lProp | Level.lSet => snd G (* supposed to be yet here *) *)
(*          | Level.Var _ => ConstraintSet.add (Level.set, ConstraintType.Le, l) (snd G) *)
(*          | Level.Level _ => ConstraintSet.add (Level.set, ConstraintType.Lt, l) (snd G) *)
(*          end in *)
(*      (levels, constraints). *)

(* Definition add_constraint (uc : univ_constraint) (G : t) : t *)
(*   := let '((l, ct),l') := uc in *)
(*      (* maybe useless if we always add constraints *)
(*         in which the universes are declared *) *)
(*      let G := add_node l (add_node l' G) in *)
(*      let constraints := ConstraintSet.add uc (snd G) in *)
(*      (fst G, constraints). *)

(* Definition repr (uctx : universe_context) : UContext.t := *)
(*   match uctx with *)
(*   | Monomorphic_ctx c => c *)
(*   | Polymorphic_ctx c => c *)
(*   | Cumulative_ctx c => CumulativityInfo.univ_context c *)
(*   end. *)

(* Definition add_global_constraints (uctx : universe_context) (G : t) : t *)
(*   := match uctx with *)
(*      | Monomorphic_ctx (inst, cstrs) => *)
(*        let G := List.fold_left (fun s l => add_node l s) inst G in *)
(*        ConstraintSet.fold add_constraint cstrs G *)
(*      | Polymorphic_ctx _ => G *)
(*      | Cumulative_ctx _ => G *)
(*      end. *)



Section Test.

  Definition get_graph G0 := match G0 with
                             | Some φ => φ
                             | None => init_graph
                             end.

  Definition G0 := make_graph ConstraintSet.empty.
  Check (eq_refl : G0 = Some _).
  Definition G := get_graph G0.

  Local Existing Instance default_checker_flags.

  Check (eq_refl : check_leq G Universe.type0m Universe.type0 = true).
  Check (eq_refl : check_lt G Universe.type0m Universe.type0 = true).
  Check (eq_refl : check_lt G Universe.type0m Universe.type0m = false).
  Check (eq_refl : check_lt G Universe.type0 Universe.type0m = false).
  Check (eq_refl : check_lt G Universe.type0 Universe.type0 = false).
  Check (eq_refl : no_universe_inconsistency G = true).

  Definition ctrs0 := ConstraintSet.add (Level.Level "Top.0", Lt, Level.Level "Top.1")
                                        (ConstraintSet.singleton (Level.Var 0, Lt, Level.Var 1)).
  Definition G'0 := make_graph ctrs0.
  Check (eq_refl : G'0 = Some _).
  Definition G' := get_graph G'0.

  Check (eq_refl : check_lt G' (Universe.make (Level.Level "Top.0")) (Universe.make (Level.Var 0)) = false).
  Check (eq_refl : check_leq G' (Universe.make (Level.Level "Top.1")) (Universe.make (Level.lProp)) = false).
  Check (eq_refl : check_leq G' (Universe.super (Level.Level "Top.1")) (Universe.make (Level.Level "Top.1")) = false).
  Check (eq_refl : check_lt G' (Universe.make (Level.Level "Top.1")) (Universe.super (Level.Level "Top.1")) = true).
  Check (eq_refl : check_lt G' (Universe.make (Level.Level "Top.1")) (Universe.make (Level.Level "Top.1")) = false).
  Check (eq_refl : check_eq G' (Universe.make (Level.Level "Top.1")) (Universe.make (Level.Level "Top.1")) = true).
  Check (eq_refl : no_universe_inconsistency G = true).

  Check (eq_refl : check_lt G' (Universe.make (Level.Var 1)) (Universe.make (Level.Var 0)) = false).
  Check (eq_refl : check_leq G' (Universe.make (Level.Var 0)) (Universe.make (Level.Var 1)) = true).
  Check (eq_refl : check_lt G' (Universe.make (Level.Var 0)) (Universe.make (Level.Var 1)) = true).
  Check (eq_refl : check_leq G' Universe.type1 Universe.type0 = false).
  Check (eq_refl : check_lt G' Universe.type1 Universe.type1 = false).


  Definition ctrs1 := ConstraintSet.add (Level.Var 1, Eq, Level.Var 2)
                                        (ConstraintSet.add (Level.Var 2, Le, Level.lSet) ctrs0).
  Definition G''0 := make_graph ctrs1.
  Check (eq_refl : G''0 = Some _).
  Definition G'' := get_graph G''0.

  Check (eq_refl : no_universe_inconsistency G'' = false).

End Test.
