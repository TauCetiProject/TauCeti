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
has degree zero and nonpositive log-canonical degree. The stable range need not be assumed: a
stable endpoint lies in it, and the steps preserve the genus, the markings and the total degree.

## Main results

* `TauCeti.DualGraph.DegreeDecoration.exists_iso_of_reflTransGen_of_isStable`: any two stable
  decorated graphs reached from the same decorated graph by stabilization steps are isomorphic by
  an isomorphism preserving the component degrees.

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

variable {ι : Type v} [Fintype ι]

/-- **Map-aware stabilization is independent of the order of contractions.** Any two stable
decorated graphs reached from the same decorated graph by stabilization steps are isomorphic by an
isomorphism of dual graphs preserving the component degrees. The starting graph is then in the
stable range `2g - 2 + n + 3d > 0`, since the steps preserve `g`, `n` and `d`. -/
theorem exists_iso_of_reflTransGen_of_isStable {G : DualGraph.{u} ι} {D : G.DegreeDecoration}
    {y₁ y₂ : Σ G : DualGraph.{u} ι, G.DegreeDecoration}
    (h₁ : Relation.ReflTransGen StabilizationStep ⟨G, D⟩ y₁)
    (h₂ : Relation.ReflTransGen StabilizationStep ⟨G, D⟩ y₂) (hy₁ : y₁.2.IsStable)
    (hy₂ : y₂.2.IsStable) :
    ∃ f : y₁.1.Iso y₂.1, ∀ w, y₂.2.componentDegree (f.vertexEquiv w) = y₁.2.componentDegree w :=
  -- The stable endpoint `y₁` lies in the stable range, which is preserved by the steps. If every
  -- component has degree zero, the total degree vanishes and the range is that of the underlying
  -- graph.
  have hrange : 0 < 2 * (G.arithmeticGenus : ℤ) - 2 + Fintype.card ι + 3 * D.totalDegree := by
    simpa [arithmeticGenus_eq_of_reflTransGen h₁, totalDegree_eq_of_reflTransGen h₁] using
      hy₁.two_mul_arithmeticGenus_sub_two_add_card_add_three_mul_totalDegree_pos
  exists_iso_of_reflTransGen_labelledStabilizationStep
    (fun hzero ↦ by simpa [(D.totalDegree_eq_zero_iff).mpr hzero] using hrange)
    (reflTransGen_labelledStabilizationStep_of_reflTransGen h₁)
    (reflTransGen_labelledStabilizationStep_of_reflTransGen h₂)
    (fun _ ↦ hy₁.not_labelledStabilizationStep) fun _ ↦ hy₂.not_labelledStabilizationStep

end DegreeDecoration

end DualGraph

end TauCeti
