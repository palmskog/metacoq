Require Import Peano_dec Nat Bool List Relations Structures.Equalities
        MSets.MSetWeakList.
From Template Require Import utils.

Fixpoint filter_pack {A} (P : A -> Prop) (HP : forall x, {P x} + {~ P x})
         (l : list A) {struct l} : list {x : A & P x} :=
  match l with
  | nil => nil
  | x :: l => match HP x with
             | left p => (existT _ _ p) :: (filter_pack P HP l)
             | right _ => filter_pack P HP l
             end
  end.


Module WeightedGraph (V : DecidableType).
  Module VSet := MSets.MSetWeakList.Make V.
  Module Edge.
    Definition t := (V.t * nat * V.t)%type.
    Definition eq (e1 e2 : t) : Prop :=
      let '(x1, n1, y1) := e1 in let '(x2, n2, y2) := e2 in
      V.eq x1 x2 /\ n1 = n2 /\ V.eq y1 y2.
    Definition eq_equiv : RelationClasses.Equivalence eq.
    Admitted.
    Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
      intros [[x1 n1] y1] [[x2 n2] y2]; cbn.
      destruct (V.eq_dec x1 x2). destruct (V.eq_dec y1 y2). 
      destruct (Peano_dec.eq_nat_dec n1 n2).
      left. intuition.
      all: right; intuition.
    Defined.
  End Edge.
  Module EdgeSet:= MSets.MSetWeakList.Make Edge.

  Definition t := (VSet.t * EdgeSet.t * V.t)%type.

  Let V (G : t) := fst (fst G).
  Let E (G : t) := snd (fst G).
  Let s (G : t) := snd G.

  Definition labelling := V.t -> nat.

  Section graph.
    Context (G : t).

    Definition R (x y : V.t) := exists n, EdgeSet.In (x, n, y) (E G).

    Definition Rs := clos_refl_trans _ R.

    Definition invariants :=
      (* E ⊆ V × V *)
      (forall e, EdgeSet.In e (E G)
            -> VSet.In (fst (fst e)) (V G) /\ VSet.In (snd e) (V G))
      (* s ∈ V *)
      /\  VSet.In (s G) (V G)
      (* s is a source *)
      /\ (forall x, VSet.In x (V G) -> Rs (s G) x).

    Definition add_node x : t :=
      (VSet.add x (V G), (E G), (s G)).

    Definition add_edge e : t :=
      (VSet.add (fst (fst e)) (VSet.add (snd e) (V G)), EdgeSet.add e (E G), (s G)).


    Definition R0 (x y : V.t) := EdgeSet.In (x, 0, y) (E G).

    (* paths of weight 0 *)
    Definition R0s := clos_trans _ R0.

    (* paths with one positive edge *)
    Definition R1 (x y : V.t) :=
      exists x0 y0 n, R0s x x0 /\ EdgeSet.In (x0, S n, y0) (E G) /\ R0s y0 y.

    Definition acyclic := well_founded R1.

    Definition correct_labelling (l : labelling) :=
      l (s G) = 0 /\
      forall e, EdgeSet.In e (E G) -> l (fst (fst e)) + (snd (fst e)) <= l (snd e).

    Conjecture R1_dec : forall x y, {R1 x y} + {~ R1 x y}.
    Conjecture Rs_dec : forall x y, {Rs x y} + {~ Rs x y}.

    (* biggest distance from s to x *)
    Definition d (s x : V.t) (H1 : Acc R1 x) (H2 : Rs s x) : nat.
      induction H1 as [x H1 d].
      simple refine (let preds := filter_pack (fun y => Rs s y /\ R1 y x) _
                                              (VSet.elements (V G)) in _).
      - intro y; cbn.
        refine (match Rs_dec s y, R1_dec y x with
                | left _, left _ => left _
                | _, _ => right _
                end); intuition.
      - exact (List.fold_left (fun n X => max n (d X.1 (proj2 X.2) (proj1 X.2)))
                              preds 0).
    Defined.

    Definition d_labelling (HG : acyclic) : labelling
      := fun x => match Rs_dec (s G) x with
               | left p => d (s G) x (HG _) p
               | right _ => 0
               end.

    Definition d_labelling_ok HG : correct_labelling (d_labelling HG).
      split; unfold d_labelling.
      - destruct (Rs_dec (s G) (s G)); [|reflexivity (* impossible in fact *)].
        destruct (HG (s G)). simpl.
        match goal with
        | |- fold_left _ ?l _ = _ => set l
        end.
        destruct l. reflexivity.
        apply False_rect.
        clear -a s0. destruct s0 as [x [H1 H2]]. specialize (a x H2).
        admit.
      - 

    Conjecture acyclic_labelling : acyclic <-> exists l, correct_labelling l.

  End graph.


  Definition path (E : EdgeSet.t) : V.t -> V.t -> bool.
    induction (EdgeSet.elements E) as [|e l path].
    exact (fun x y => if V.eq_dec x y then true else false).
    exact (fun x y => path x y || (path x (fst (fst e)) && path (snd e) y)).
  Defined.

  Conjecture path_spec : forall {G} x y, reflect (Rs G x y) (path (snd (fst G)) x y).

  
  Lemma add_node_invariants {G} (HG : invariants G) {x} (Hx : R G (s G) x)
    : invariants (add_node G x).
  Proof.
    unfold invariants in *.
  Admitted.

  Lemma add_edge_invariants {G} (HG : invariants G) {e}
        (He : R G (s G) (fst (fst e)))
    : invariants (add_edge G e).
  Proof.
    unfold invariants in *.
  Admitted.

End WeightedGraph.









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
