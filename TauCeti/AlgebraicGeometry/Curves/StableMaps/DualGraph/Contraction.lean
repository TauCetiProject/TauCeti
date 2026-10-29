/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Contraction
public import TauCeti.AlgebraicGeometry.Curves.StableMaps.DualGraph.Basic

/-!
# Map-aware stabilization of degree-decorated dual graphs

A prestable map is made stable by repeatedly contracting the rational components on which the map
is constant and which carry at most two special points: an unmarked rational tail is deleted, a
rational tail carrying one marking is deleted and its marking moves to the neighbouring
component, and an unmarked rational bridge is replaced by a node. Components on which the map has
positive degree are never contracted, whatever their genus and special points.

On the dual graph of the source curve, decorated by the degree of the map on each component, such a
contraction is a contraction of the underlying graph (`TauCeti.DualGraph.contractTail` or
`TauCeti.DualGraph.contractBridge`) at a vertex of degree zero, with the decoration restricted to
the remaining vertices. This file transports degree decorations along both contractions and
records how the total degree and the weighted log-canonical degrees change. Since only degree-zero
vertices are contracted, a step preserves the total degree as well as the arithmetic genus.

`TauCeti.DualGraph.DegreeDecoration.StabilizationStep` is the resulting relation on decorated
graphs. Contracting the tails of a component can make that component unstable, so stabilization
is iterated, recomputing flags after every step. In the stable range `2g - 2 + n + 3d > 0`, a
decorated graph admits a step exactly when it is not stable, and iterating steps from any decorated
graph reaches a stable one of the same genus and total degree. For the zero decoration, which
describes a constant map, the steps are exactly the stabilization steps of the pointed source
graph.

## Main definitions

* `TauCeti.DualGraph.DegreeDecoration.contractTail` and
  `TauCeti.DualGraph.DegreeDecoration.contractBridge`: the restriction of a decoration to the
  contracted graph.
* `TauCeti.DualGraph.DegreeDecoration.StabilizationStep`: contraction of a degree-zero rational
  tail with at most one marking or of an unmarked degree-zero rational bridge.

## Main results

* `TauCeti.DualGraph.DegreeDecoration.totalDegree_contractTail` and
  `TauCeti.DualGraph.DegreeDecoration.totalDegree_contractBridge`: the total degree drops by the
  degree of the contracted vertex.
* `TauCeti.DualGraph.DegreeDecoration.isStable_iff_forall_not_stabilizationStep`: in the stable
  range, a decorated graph is stable exactly when it admits no stabilization step.
* `TauCeti.DualGraph.DegreeDecoration.exists_reflTransGen_stabilizationStep_isStable`: in the
  stable range, iterated stabilization steps reach a stable decorated graph.
* `TauCeti.DualGraph.DegreeDecoration.stabilizationStep_zero_iff`: for the zero decoration,
  stabilization steps are the stabilization steps of the underlying graph.

## References

* K. Behrend and Yu. Manin, *Stacks of stable maps and Gromov--Witten invariants*, Duke Math. J.
  85 (1996), 1--60, Section 3, for the contraction of unstable components of prestable maps.
* W. Fulton and R. Pandharipande, *Notes on stable maps and quantum cohomology*, Proc. Sympos.
  Pure Math. 62 (1997), Part 2, 45--96, Section 1.
-/

public section

namespace TauCeti

namespace DualGraph

namespace DegreeDecoration

universe u v

variable {ι : Type v} {G : DualGraph.{u} ι} (D : G.DegreeDecoration)

/-! ### Contracting a tail -/

section Tail

variable {v : G.Vertex} (hv : G.valence v = 1)

/-- The restriction of a degree decoration to the graph obtained by contracting a vertex of
valence one. -/
def contractTail : (G.contractTail hv).DegreeDecoration :=
  ⟨fun w ↦ D.componentDegree w.1⟩

@[simp]
lemma componentDegree_contractTail (w : (G.contractTail hv).Vertex) :
    (D.contractTail hv).componentDegree w = D.componentDegree w.1 :=
  (rfl)

@[simp]
lemma contractTail_zero : (0 : G.DegreeDecoration).contractTail hv = 0 :=
  DegreeDecoration.ext rfl

/-- Contracting a tail lowers the total degree by the degree of the tail. -/
theorem totalDegree_contractTail :
    (D.contractTail hv).totalDegree + D.componentDegree v = D.totalDegree := by
  rw [totalDegree_def, totalDegree_def, Fintype.sum_eq_add_sum_subtype_ne D.componentDegree v,
    ← sum_vertex_contractTail hv D.componentDegree, add_comm]
  simp only [componentDegree_contractTail]

/-- Contracting a tail changes only the weighted log-canonical degree of its attachment, which
changes by the number of markings on the tail minus one. -/
@[simp]
theorem weightedLogCanonicalDegree_contractTail [Fintype ι] (u : G.Vertex) (hu : u ≠ v) :
    (D.contractTail hv).weightedLogCanonicalDegree ⟨u, hu⟩ =
      D.weightedLogCanonicalDegree u +
        if G.attachment hv = u then (G.numMarkings v : ℤ) - 1 else 0 := by
  rw [weightedLogCanonicalDegree_def, weightedLogCanonicalDegree_def,
    logCanonicalDegree_contractTail, componentDegree_contractTail]
  exact add_right_comm _ _ _

end Tail

/-! ### Contracting a bridge -/

section Bridge

variable {v : G.Vertex} (hv : G.valence v = 2)
  (hloop : ∀ e, G.endpoint e 0 = v → G.endpoint e 1 ≠ v) (hm : ∀ i, G.marking i ≠ v)

/-- The restriction of a degree decoration to the graph obtained by contracting an unmarked
loopless vertex of valence two. -/
def contractBridge : (G.contractBridge hv hloop hm).DegreeDecoration :=
  ⟨fun w ↦ D.componentDegree w.1⟩

@[simp]
lemma componentDegree_contractBridge (w : (G.contractBridge hv hloop hm).Vertex) :
    (D.contractBridge hv hloop hm).componentDegree w = D.componentDegree w.1 :=
  (rfl)

@[simp]
lemma contractBridge_zero : (0 : G.DegreeDecoration).contractBridge hv hloop hm = 0 :=
  DegreeDecoration.ext rfl

/-- Contracting a bridge lowers the total degree by the degree of the bridge. -/
theorem totalDegree_contractBridge :
    (D.contractBridge hv hloop hm).totalDegree + D.componentDegree v = D.totalDegree := by
  rw [totalDegree_def, totalDegree_def, Fintype.sum_eq_add_sum_subtype_ne D.componentDegree v,
    ← sum_vertex_contractBridge hv hloop hm D.componentDegree, add_comm]
  simp only [componentDegree_contractBridge]

/-- Contracting a bridge does not change any weighted log-canonical degree. -/
@[simp]
theorem weightedLogCanonicalDegree_contractBridge [Fintype ι] (u : G.Vertex) (hu : u ≠ v) :
    (D.contractBridge hv hloop hm).weightedLogCanonicalDegree ⟨u, hu⟩ =
      D.weightedLogCanonicalDegree u := by
  rw [weightedLogCanonicalDegree_def, weightedLogCanonicalDegree_def,
    logCanonicalDegree_contractBridge, componentDegree_contractBridge]

end Bridge

/-! ### Stabilization -/

variable [Fintype ι]

/-- A **stabilization step** of degree-decorated dual graphs: the second decorated graph is
obtained from the first by contracting a rational tail carrying at most one marking or an unmarked
rational bridge, on which the map has degree zero, and restricting the decoration. These are the
contractions of a component on which the map is constant and whose log-canonical degree is
nonpositive. -/
inductive StabilizationStep :
    (Σ G : DualGraph.{u} ι, G.DegreeDecoration) → (Σ G : DualGraph.{u} ι, G.DegreeDecoration) →
      Prop
  /-- Contract a degree-zero rational tail carrying at most one marking. -/
  | contractTail {G : DualGraph.{u} ι} (D : G.DegreeDecoration) {v : G.Vertex}
      (hv : G.IsRationalTail v) (hm : G.numMarkings v ≤ 1) (hd : D.componentDegree v = 0) :
      StabilizationStep ⟨G, D⟩ ⟨_, D.contractTail (G.isRationalTail_iff.mp hv).2⟩
  /-- Contract an unmarked degree-zero rational bridge. -/
  | contractBridge {G : DualGraph.{u} ι} (D : G.DegreeDecoration) {v : G.Vertex}
      (hv : G.IsRationalBridge v) (hm : ∀ i, G.marking i ≠ v) (hd : D.componentDegree v = 0) :
      StabilizationStep ⟨G, D⟩
        ⟨_, D.contractBridge (G.isRationalBridge_iff.mp hv).2.1 (G.isRationalBridge_iff.mp hv).2.2
          hm⟩

variable {x y : Σ G : DualGraph.{u} ι, G.DegreeDecoration}

namespace StabilizationStep

/-- A stabilization step of decorated graphs is a stabilization step of the underlying graphs. -/
theorem fst (h : StabilizationStep x y) : DualGraph.StabilizationStep x.1 y.1 := by
  cases h with
  | contractTail D hv hm => exact .contractTail _ hv hm
  | contractBridge D hv hm => exact .contractBridge _ hv hm

/-- A stabilization step preserves the arithmetic genus. -/
theorem arithmeticGenus_eq (h : StabilizationStep x y) :
    y.1.arithmeticGenus = x.1.arithmeticGenus :=
  h.fst.arithmeticGenus_eq

/-- A stabilization step removes a vertex. -/
theorem card_vertex_lt (h : StabilizationStep x y) :
    Fintype.card y.1.Vertex < Fintype.card x.1.Vertex :=
  h.fst.card_vertex_lt

/-- A stabilization step preserves the total degree, since it only contracts components of degree
zero. -/
theorem totalDegree_eq (h : StabilizationStep x y) : y.2.totalDegree = x.2.totalDegree := by
  cases h with
  | contractTail D hv hm hd =>
    have := D.totalDegree_contractTail ((isRationalTail_iff _).mp hv).2
    rwa [hd, add_zero] at this
  | contractBridge D hv hm hd =>
    have := D.totalDegree_contractBridge ((isRationalBridge_iff _).mp hv).2.1
      ((isRationalBridge_iff _).mp hv).2.2 hm
    rwa [hd, add_zero] at this

/-- A stabilization step contracts a vertex of degree zero and nonpositive log-canonical degree. -/
theorem exists_componentDegree_eq_zero_and_logCanonicalDegree_nonpos (h : StabilizationStep x y) :
    ∃ v, x.2.componentDegree v = 0 ∧ x.1.logCanonicalDegree v ≤ 0 := by
  cases h with
  | contractTail D hv hm hd => exact ⟨_, hd, by rw [hv.logCanonicalDegree_eq]; omega⟩
  | contractBridge D hv hm hd =>
    exact ⟨_, hd, by rw [hv.logCanonicalDegree_eq, numMarkings_def]; simp [hm]⟩

end StabilizationStep

/-- A stable decorated graph admits no stabilization step. -/
theorem IsStable.not_stabilizationStep (hx : x.2.IsStable) : ¬ StabilizationStep x y := fun h ↦
  have ⟨v, hd, hv⟩ := h.exists_componentDegree_eq_zero_and_logCanonicalDegree_nonpos
  (x.2.isStable_iff.mp hx v hd).not_ge hv

/-- Iterated stabilization steps preserve the arithmetic genus. -/
theorem arithmeticGenus_eq_of_reflTransGen (h : Relation.ReflTransGen StabilizationStep x y) :
    y.1.arithmeticGenus = x.1.arithmeticGenus :=
  DualGraph.arithmeticGenus_eq_of_reflTransGen (h.lift Sigma.fst fun _ _ ↦ StabilizationStep.fst)

/-- Iterated stabilization steps preserve the total degree. -/
theorem totalDegree_eq_of_reflTransGen (h : Relation.ReflTransGen StabilizationStep x y) :
    y.2.totalDegree = x.2.totalDegree := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact hstep.totalDegree_eq.trans ih

/-- In the stable range `2g - 2 + n + 3d > 0`, a decorated graph that is not stable admits a
stabilization step. A degree-zero vertex of nonpositive log-canonical degree is a rational tail
with at most one marking, a rational bridge without markings, or the only vertex; in the last
case the total degree is zero and its log-canonical degree is `2g - 2 + n`. -/
theorem exists_stabilizationStep_of_not_isStable
    (hrange : 0 < 2 * (G.arithmeticGenus : ℤ) - 2 + Fintype.card ι + 3 * D.totalDegree)
    (hD : ¬ D.IsStable) : ∃ y, StabilizationStep ⟨G, D⟩ y := by
  obtain ⟨v, hd, hv⟩ : ∃ v, D.componentDegree v = 0 ∧ G.logCanonicalDegree v ≤ 0 := by
    simpa [isStable_iff, not_forall, not_lt] using hD
  have hw : ∃ w, w ≠ v := by
    by_contra! h
    have := G.logCanonicalDegree_eq_of_forall_eq h
    have htot : D.totalDegree = 0 := by
      rw [totalDegree_def, Fintype.sum_eq_single v fun w hw ↦ absurd (h w) hw, hd]
    omega
  rcases G.isRationalTail_or_isRationalBridge_of_logCanonicalDegree_nonpos hv hw with
    ⟨ht, hm⟩ | ⟨hb, hm⟩
  · exact ⟨_, .contractTail D ht hm hd⟩
  · exact ⟨_, .contractBridge D hb hm hd⟩

/-- In the stable range `2g - 2 + n + 3d > 0`, a decorated graph is stable exactly when it admits
no stabilization step. -/
theorem isStable_iff_forall_not_stabilizationStep
    (hrange : 0 < 2 * (G.arithmeticGenus : ℤ) - 2 + Fintype.card ι + 3 * D.totalDegree) :
    D.IsStable ↔ ∀ y, ¬ StabilizationStep ⟨G, D⟩ y :=
  ⟨fun hD _ ↦ IsStable.not_stabilizationStep (x := ⟨G, D⟩) hD, fun h ↦ by_contra fun hD ↦
    have ⟨y, hy⟩ := D.exists_stabilizationStep_of_not_isStable hrange hD
    h y hy⟩

/-- **Map-aware stabilization terminates.** In the stable range `2g - 2 + n + 3d > 0`, iterating
stabilization steps from any decorated graph reaches a stable decorated graph, of the same
arithmetic genus and total degree by `arithmeticGenus_eq_of_reflTransGen` and
`totalDegree_eq_of_reflTransGen`. Termination holds because every step removes a vertex. -/
theorem exists_reflTransGen_stabilizationStep_isStable
    (hrange : 0 < 2 * (G.arithmeticGenus : ℤ) - 2 + Fintype.card ι + 3 * D.totalDegree) :
    ∃ y, Relation.ReflTransGen StabilizationStep ⟨G, D⟩ y ∧ y.2.IsStable := by
  induction hn : Fintype.card G.Vertex using Nat.strong_induction_on generalizing G with
  | _ n ih =>
    by_cases hD : D.IsStable
    · exact ⟨⟨G, D⟩, .refl, hD⟩
    · obtain ⟨⟨H, E⟩, hE⟩ := D.exists_stabilizationStep_of_not_isStable hrange hD
      obtain ⟨z, hz, hzs⟩ := ih _ (hn ▸ hE.card_vertex_lt) E
        (by rw [hE.arithmeticGenus_eq, hE.totalDegree_eq]; exact hrange) rfl
      exact ⟨z, .head hE hz, hzs⟩

/-! ### Constant maps -/

/-- For the zero decoration, which describes a constant map, the stabilization steps are the
stabilization steps of the underlying graph, with the zero decoration on the result. -/
theorem stabilizationStep_zero_iff {H : DualGraph.{u} ι} {E : H.DegreeDecoration} :
    StabilizationStep ⟨G, 0⟩ ⟨H, E⟩ ↔ DualGraph.StabilizationStep G H ∧ E = 0 := by
  constructor
  · rintro (⟨_, hv, hm, -⟩ | ⟨_, hv, hm, -⟩)
    · exact ⟨.contractTail _ hv hm, contractTail_zero _⟩
    · exact ⟨.contractBridge _ hv hm, contractBridge_zero _ _ _⟩
  · -- The restriction of the zero decoration is the zero decoration on the contracted graph.
    rintro ⟨h, rfl⟩
    cases h with
    | contractTail hv hm => exact contractTail_zero (G := G) _ ▸ .contractTail 0 hv hm rfl
    | contractBridge hv hm =>
      exact contractBridge_zero (G := G) _ _ _ ▸ .contractBridge 0 hv hm rfl

end DegreeDecoration

end DualGraph

end TauCeti
