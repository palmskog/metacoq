Require Import Nat Bool String BinInt List Relations Lia.
Import ListNotations.
Require MSets.MSetWeakList.
Require Import MSetFacts MSetProperties.
From Template Require Import utils config Universes wGraph monad_utils.
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

Definition my_consistent ctrs : Prop := exists v, my_satisfies v ctrs.

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
(* ltv : level to vertice *)
Inductive vertice := lSet | ltv (l : my_level).

Coercion ltv : my_level >-> vertice.

Module VerticeDec.
  Definition t : Set := vertice.
  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : RelationClasses.Equivalence eq := _.
  Definition eq_refl : forall x : t, eq x x := @eq_refl _.
  Definition eq_sym : forall x y : t, eq x y -> eq y x := @eq_sym _.
  Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z := @eq_trans _.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
    unfold eq. decide equality. apply GoodConstraintDec.my_level_dec. 
  Defined.
  Definition eqb : t -> t -> bool := fun x y => if eq_dec x y then true else false.
End VerticeDec.

Module Import wGraph := wGraph.WeightedGraph VerticeDec.

Definition init_graph := (VSet.singleton lSet, EdgeSet.empty, lSet).

Lemma init_graph_invariants : invariants init_graph.
Proof.
  repeat split; cbn in *.
  all: try inversion H.
  constructor; reflexivity.
  intros x H. apply VSet.singleton_spec in H.
  rewrite H. apply rt_refl.
Defined.

Definition edge_of_level (l : my_level) : EdgeSet.elt :=
  match l with
  | mLevel l => (lSet, 1, ltv (mLevel l))
  | mVar n => (lSet, 0, ltv (mVar n))
  end.

Definition EdgeSet_pair x y
  := EdgeSet.add y (EdgeSet.singleton x).
Definition EdgeSet_triple x y z
  := EdgeSet.add z (EdgeSet_pair x y).

Definition edges_of_constraint (gc : good_constraint) : list EdgeSet.elt :=
  match gc with
  | gc_le l l' => [(edge_of_level l); (edge_of_level l'); (ltv l, 0, ltv l')]
  | gc_lt l l' => [(edge_of_level l); (edge_of_level l'); (ltv l, 1, ltv l')]
  | gc_lt_set n => [(lSet, 1, ltv (mVar n))]
  | gc_eq_set n => [(ltv (mVar n), 0, lSet); (lSet, 0, ltv (mVar n))]
  end.

Definition add_edges edges := fold_left add_edge edges.

Lemma add_edges_invariants {G} (HG : invariants G) {gc}
  : invariants (add_edges (edges_of_constraint gc) G).
Proof.
  destruct HG as [H1 [H2 H3]].
  repeat split.
Admitted.


Definition make_graph (ctrs : GoodConstraintSet.t) : t
  := GoodConstraintSet.fold (add_edges ∘ edges_of_constraint)
                            ctrs init_graph.

Definition labelling_of_valuation (v : valuation) : labelling
  := fun x => match x with
           | lSet => 0
           | ltv (mLevel l) => Pos.to_nat (v.(valuation_mono) l)
           | ltv (mVar n) => v.(valuation_poly) n
           end.

Definition valuation_of_labelling (l : labelling) : valuation
  := {| valuation_mono := fun s => Pos.of_nat (l (ltv (mLevel s)));
        valuation_poly := fun n => l (ltv (mVar n)) |}.

Section Spec.
  Context (ctrs : GoodConstraintSet.t).
  Let G := make_graph ctrs.

  Lemma make_graph_invariants : invariants G.
  Proof.
    subst G; unfold make_graph. rewrite GoodConstraintSet.fold_spec.
    pose proof init_graph_invariants as HG.
    set (G := init_graph) in *. clearbody G; revert G HG.
    set (l := GoodConstraintSet.elements ctrs). induction l.
    - easy.
    - intros G HG; cbn. apply IHl. now apply add_edges_invariants.
  Qed.

  Definition make_graph_edge
    : forall x, VSet.In (ltv x) (wGraph.V G) -> EdgeSet.In (edge_of_level x) (wGraph.E G).
  Proof.
    subst G; unfold make_graph. rewrite GoodConstraintSet.fold_spec.
    set (G := init_graph) in *. 
    assert (HG : forall x, VSet.In (ltv x) (wGraph.V G)
                      -> EdgeSet.In (edge_of_level x) (wGraph.E G)). {
      subst G. cbn. intros x H; apply VSet.singleton_spec in H.
      inversion H. }
    clearbody G; revert G HG.
    set (l := GoodConstraintSet.elements ctrs). induction l.
    - cbn. easy.
    - intros G HG; cbn. apply IHl. intro x.
      destruct a; cbn.
      + destruct m, m0; cbn.
  Admitted.

  Lemma source_make_graph : wGraph.s G = lSet.
  Proof.
    subst G; unfold make_graph. rewrite GoodConstraintSet.fold_spec.
    set (G := init_graph). 
    assert (HG : wGraph.s G = lSet) by reflexivity.
    clearbody G; revert G HG.
    induction (GoodConstraintSet.elements ctrs).
    intros; assumption.
    intros G HG; cbn. apply IHl.
    clear -HG.
    revert G HG. induction (edges_of_constraint a).
    intros G HG; assumption.
    intros G HG. cbn; apply IHl; assumption.
  Qed.

  Lemma valuation_labelling_eq l (Hl : correct_labelling G l)
    : forall x, VSet.In x (wGraph.V G)
           -> labelling_of_valuation (valuation_of_labelling l) x = l x.
  Proof.
    destruct x; cbn.
    - intros _. apply proj1 in Hl; cbn in Hl.
      etransitivity. symmetry; eassumption.
      f_equal. apply source_make_graph.
    - destruct l0; cbn. 2: reflexivity.
      intro Hs. apply Nat2Pos.id.
      apply make_graph_edge in Hs.
      apply (proj2 Hl) in Hs; cbn in Hs. lia.
  Qed.

  Lemma toto e :
    EdgeSet.In e (wGraph.E G) <-> 
    (exists l, e = edge_of_level l) \/ (GoodConstraintSet.Exists (fun gc => In e (edges_of_constraint gc)) ctrs).
  Admitted.

  Lemma make_graph_gc gc :
    GoodConstraintSet.In gc ctrs
    -> Forall (fun e => EdgeSet.In e (wGraph.E G)) (edges_of_constraint gc).
  Proof.
    subst G; unfold make_graph. rewrite GoodConstraintSet.fold_spec.
    intro H; apply GoodConstraintSetProp.FM.elements_1 in H.
    set (l := GoodConstraintSet.elements ctrs) in *.
    set (G := init_graph). 
    assert (HG : In gc l
        \/ Forall (fun e => EdgeSet.In e (wGraph.E G)) (edges_of_constraint gc)). {
      left. apply InA_alt in H. now destruct H as [y [[]]]. }
    clearbody G; revert G HG; clear H.
    induction l.
    - intros G []. inversion H. assumption.
    - intros G HG; cbn. apply IHl.
      destruct HG as [H1|H2].
      + inversion_clear H1.
        * right. subst.
          destruct gc; cbn; repeat constructor.
          admit.
        * now left.
      + right. admit.
  Qed.
    
  Admitted.

  (* TODO: This proof should be better written *)
  Lemma make_graph_spec v :
    my_satisfies v ctrs <-> correct_labelling G (labelling_of_valuation v).
  Proof.
    unfold my_satisfies, correct_labelling. split; intro H.
    - split. now rewrite source_make_graph.
      intros e He. apply toto in He. induction He.
      + destruct H0 as [[]]; cbn in H0; subst; cbn; lia.
      + apply GoodConstraintSet.for_all_spec in H.
        2: intros x y []; reflexivity.
        destruct H0 as [[] [H1 H2]]; cbn in *.
        * destruct H2 as [|[|[|[]]]].
          -- destruct m; subst; cbn in *; lia.
          -- destruct m0; subst; cbn in *; lia.
          -- specialize (H _ H1); cbn in H. apply PeanoNat.Nat.leb_le in H.
             subst; clear H1. destruct m, m0; simpl in *; lia.
        * destruct H2 as [|[|[|[]]]].
          -- destruct m; subst; cbn in *; lia.
          -- destruct m0; subst; cbn in *; lia.
          -- specialize (H _ H1); cbn in H.
             case_eq (my_val0 v m0). intro eq; rewrite eq in H.
             discriminate.
             intros n eq; rewrite eq in H.
             apply PeanoNat.Nat.leb_le in H.
             subst; clear H1. destruct m, m0; simpl in *; lia.
        * destruct H2 as [|[]]. subst.
          specialize (H _ H1); cbn in H.
          case_eq (valuation_poly v n). intro eq; rewrite eq in H.
          discriminate.
          intros n0 eq; rewrite eq in H.
          cbn. rewrite eq; lia.
        * destruct H2 as [|[|[]]]. subst.
          -- specialize (H _ H1); cbn in H.
             case_eq (valuation_poly v n). intro eq; rewrite eq in H.
             cbn. rewrite eq; lia.
             intros n0 eq; rewrite eq in H; discriminate.
          -- subst; cbn.
             specialize (H _ H1); cbn in H.
             case_eq (valuation_poly v n). intro; lia.
             intros n0 eq; rewrite eq in H; discriminate.
    - apply GoodConstraintSet.for_all_spec.
      intros x y []; reflexivity.
      intros gc Hgc. apply tata in Hgc.
      apply proj2 in H.
      destruct gc; cbn in *.
      + inversion_clear Hgc. inversion_clear H1. inversion_clear H3.
        specialize (H _ H1); clear -H. cbn in *.
        destruct m, m0; cbn; apply PeanoNat.Nat.leb_le; lia.
      + inversion_clear Hgc. inversion_clear H1. inversion_clear H3.
        specialize (H _ H1); clear -H. cbn in *.
        case_eq (my_val0 v m0); intro e.
        destruct m, m0; cbn in *; lia.
        intro ee. apply PeanoNat.Nat.leb_le.
        destruct m, m0; cbn in *; lia.
      + inversion_clear Hgc. specialize (H _ H0); clear -H. cbn in *.
        case_eq (valuation_poly v n); intros; try reflexivity; lia.
      + inversion_clear Hgc. specialize (H _ H0); clear -H. cbn in *.
        case_eq (valuation_poly v n); intros; try reflexivity; lia.
  Qed.



  Corollary make_graph_spec' l :
    (* my_satisfies (valuation_of_labelling l) ctrs <-> correct_labelling G l. *)
    correct_labelling G l -> my_satisfies (valuation_of_labelling l) ctrs.
  Proof.
    intro H. apply (make_graph_spec (valuation_of_labelling l)).
    unfold correct_labelling; intuition.
    now rewrite source_make_graph.
    destruct make_graph_invariants as [H1 _].
    rewrite !valuation_labelling_eq; firstorder. 
  Qed.

  Corollary make_graph_spec2 :
    my_consistent ctrs <-> exists l, correct_labelling G l.
  Proof.
    split.
    - intros [v H]. exists (labelling_of_valuation v).
      apply make_graph_spec. assumption.
    - intros [l Hl]. exists (valuation_of_labelling l).
      apply make_graph_spec'. assumption.
  Defined.
End Spec.



















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
