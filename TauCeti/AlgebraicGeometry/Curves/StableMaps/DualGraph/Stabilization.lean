/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Stabilization
public import TauCeti.AlgebraicGeometry.Curves.StableMaps.DualGraph.Contraction

/-!
# Map-aware stabilization is independent of the order of contractions

A prestable map in the stable range `2g - 2 + n + 3d > 0` is stabilized by repeatedly contracting
a rational component on which the map is constant and which carries at most two special points,
recomputing the special points after every contraction. On the dual graph of the source, decorated
by the degree of the map on each component, these are the stabilization steps
`TauCeti.DualGraph.DegreeDecoration.StabilizationStep`, and iterating them reaches a stable
decorated graph
(`TauCeti.DualGraph.DegreeDecoration.exists_reflTransGen_stabilizationStep_isStable`). This file
shows that the stable decorated graph reached does not depend on the order of the contractions:
any two of them are isomorphic by an isomorphism of dual graphs carrying the degree of each
component to the degree of its image.

A decorated stabilization step is a labelled stabilization step
(`TauCeti.DualGraph.LabelledStabilizationStep`) for the labelling of the vertices by their degrees,
in which only vertices of degree zero may be contracted. The order independence of labelled
stabilization (`TauCeti.DualGraph.exists_iso_of_reflTransGen_labelledStabilizationStep`) needs the
stable range `2g - 2 + n > 0` only when every component has degree zero, and then it is the range
`2g - 2 + n + 3d > 0`. A stable decorated graph admits no labelled step, since a contracted vertex
has degree zero and nonpositive log-canonical degree.

## Main results

* `TauCeti.DualGraph.DegreeDecoration.StabilizationStep.labelledStabilizationStep`: a decorated
  stabilization step is a labelled stabilization step contracting a vertex of degree zero.
* `TauCeti.DualGraph.DegreeDecoration.exists_iso_of_reflTransGen_of_isStable`: in the stable
  range, any two stable decorated graphs reached from the same decorated graph by stabilization
  steps are isomorphic by an isomorphism preserving the component degrees.

## References

* K. Behrend and Yu. Manin, *Stacks of stable maps and Gromov–Witten invariants*, Duke Math. J.
  85 (1996), 1–60, Section 3, for the stabilization of prestable maps.
* F. F. Knudsen, *The projectivity of the moduli space of stable curves, II: The stacks
  `M_{g,n}`*, Math. Scand. 52 (1983), 161–199, §2, for stabilization of pointed curves.
-/

public section

namespace TauCeti

namespace DualGraph

namespace DegreeDecoration

universe u v

variable {ι : Type v} [Fintype ι] {x y : Σ G : DualGraph.{u} ι, G.DegreeDecoration}

/-- A stabilization step of decorated graphs is a labelled stabilization step for the labelling of
the vertices by their degrees, contracting a vertex of degree zero. -/
theorem StabilizationStep.labelledStabilizationStep (h : StabilizationStep x y) :
    LabelledStabilizationStep (· = 0) ⟨x.1, x.2.componentDegree⟩ ⟨y.1, y.2.componentDegree⟩ := by
  cases h with
  | @contractTail G D v hv hm hd =>
    dsimp only
    rw [show (D.contractTail (G.isRationalTail_iff.mp hv).2).componentDegree =
      fun w ↦ D.componentDegree w.1 from funext (D.componentDegree_contractTail _)]
    exact .contractTail _ hv hm hd
  | @contractBridge G D v hv hm hd =>
    dsimp only
    rw [show (D.contractBridge (G.isRationalBridge_iff.mp hv).2.1
        (G.isRationalBridge_iff.mp hv).2.2 hm).componentDegree =
      fun w ↦ D.componentDegree w.1 from funext (D.componentDegree_contractBridge _ _ _)]
    exact .contractBridge _ hv hm hd

/-- Iterated stabilization steps of decorated graphs are iterated labelled stabilization steps for
the labelling of the vertices by their degrees. -/
theorem reflTransGen_labelledStabilizationStep_of_reflTransGen
    (h : Relation.ReflTransGen StabilizationStep x y) :
    Relation.ReflTransGen (LabelledStabilizationStep (· = 0))
      ⟨x.1, x.2.componentDegree⟩ ⟨y.1, y.2.componentDegree⟩ :=
  h.lift (fun x : Σ G : DualGraph.{u} ι, G.DegreeDecoration ↦
      (⟨x.1, x.2.componentDegree⟩ : Σ G : DualGraph.{u} ι, G.Vertex → ℕ))
    fun _ _ ↦ StabilizationStep.labelledStabilizationStep

/-- A stable decorated graph admits no labelled stabilization step contracting a vertex of degree
zero: such a vertex would have nonpositive log-canonical degree. -/
theorem IsStable.not_labelledStabilizationStep {G : DualGraph.{u} ι} {D : G.DegreeDecoration}
    (hD : D.IsStable) {z : Σ G : DualGraph.{u} ι, G.Vertex → ℕ} :
    ¬ LabelledStabilizationStep (· = 0) ⟨G, D.componentDegree⟩ z := fun h ↦
  have ⟨v, hd, hv⟩ := h.exists_logCanonicalDegree_nonpos
  (D.isStable_iff.mp hD v hd).not_ge hv

/-- **Map-aware stabilization is independent of the order of contractions.** In the stable range
`2g - 2 + n + 3d > 0`, any two stable decorated graphs reached from the same decorated graph by
stabilization steps are isomorphic by an isomorphism of dual graphs preserving the component
degrees. -/
theorem exists_iso_of_reflTransGen_of_isStable {G : DualGraph.{u} ι} {D : G.DegreeDecoration}
    (hrange : 0 < 2 * (G.arithmeticGenus : ℤ) - 2 + Fintype.card ι + 3 * D.totalDegree)
    {y₁ y₂ : Σ G : DualGraph.{u} ι, G.DegreeDecoration}
    (h₁ : Relation.ReflTransGen StabilizationStep ⟨G, D⟩ y₁)
    (h₂ : Relation.ReflTransGen StabilizationStep ⟨G, D⟩ y₂) (hy₁ : y₁.2.IsStable)
    (hy₂ : y₂.2.IsStable) :
    ∃ f : y₁.1.Iso y₂.1, ∀ w, y₂.2.componentDegree (f.vertexEquiv w) = y₁.2.componentDegree w :=
  -- If every component has degree zero, the total degree vanishes and the range is that of the
  -- underlying graph.
  exists_iso_of_reflTransGen_labelledStabilizationStep
    (fun hzero ↦ by simpa [(D.totalDegree_eq_zero_iff).mpr hzero] using hrange)
    (reflTransGen_labelledStabilizationStep_of_reflTransGen h₁)
    (reflTransGen_labelledStabilizationStep_of_reflTransGen h₂)
    (fun _ ↦ hy₁.not_labelledStabilizationStep) fun _ ↦ hy₂.not_labelledStabilizationStep

end DegreeDecoration

end DualGraph

end TauCeti
