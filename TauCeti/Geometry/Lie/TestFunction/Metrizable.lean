/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.TestFunction.Continuity
public import TauCeti.Topology.Algebra.Group.Metrizable

/-!
# Fixed-support spaces of test functions are metrizable

Let `G` be a Lie group and `C ⊆ G`. The fixed-support space `LieTestFunction_C(G)` carries the
topology of the fixed-support seminorms `a ↦ sup_g |L_{X_w} a (g)|` over words `w` in the Lie
algebra; it is Hausdorff and locally convex
(`TauCeti.LieTestFunction.FixedSupport.instT1Space`,
`TauCeti.LieTestFunction.FixedSupport.instLocallyConvexSpace`). When the Lie algebra is
finite-dimensional, the seminorms along the countably many words in a basis already define the
topology (`TauCeti.LieTestFunction.FixedSupport.withSeminorms_basis`), so the topology is first
countable, and, being that of a Hausdorff topological group, metrizable. With local convexity,
these are the metrizable locally convex parts of the Fréchet property of the fixed-support spaces.

## Main results

* `TauCeti.LieTestFunction.FixedSupport.instFirstCountableTopology`,
  `TauCeti.LieTestFunction.FixedSupport.instMetrizableSpace`: for a finite-dimensional Lie
  algebra the fixed-support topology is first countable and metrizable.

## References

* J. Getz, *An introduction to automorphic representations*, course notes, §3.3, pp. 17–18.
-/

public section

noncomputable section

open Function Set TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

namespace LieTestFunction

namespace FixedSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] {C : Set G}

/-- For a finite-dimensional Lie algebra, the fixed-support topology is first countable: the
seminorms along the countably many words in a basis define it. -/
instance instFirstCountableTopology : FirstCountableTopology (FixedSupport I G C) :=
  (withSeminorms_basis (C := C) (Module.finBasis ℝ (GroupLieAlgebra I G))).firstCountableTopology

/-- **For a finite-dimensional Lie algebra, the fixed-support topology is metrizable**: it is the
topology of a first countable Hausdorff topological group. -/
instance instMetrizableSpace : MetrizableSpace (FixedSupport I G C) :=
  IsTopologicalAddGroup.metrizableSpace _

end FixedSupport

end LieTestFunction

end TauCeti
