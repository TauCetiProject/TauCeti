/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.TestFunction.Continuity
public import Mathlib.Topology.Metrizable.Uniformity

/-!
# Fixed-support spaces of test functions are metrizable and locally convex

Let `G` be a Lie group and `C ⊆ G`. The fixed-support space `LieTestFunction_C(G)` carries the
topology of the fixed-support seminorms `a ↦ sup_g |L_{X_w} a (g)|` over words `w` in the Lie
algebra. The seminorm of the empty word is the supremum norm, so the family separates points and
the topology is Hausdorff. The topology of a family of seminorms is locally convex. When the Lie
algebra is finite-dimensional, the seminorms along the countably many words in a basis already
define the topology (`TauCeti.LieTestFunction.FixedSupport.withSeminorms_basis`), so the topology
is first countable, and, being that of a Hausdorff topological group, metrizable. These are the
metrizable locally convex parts of the Fréchet property of the fixed-support spaces.

## Main results

* `TauCeti.LieTestFunction.FixedSupport.instT1Space`: the fixed-support seminorms separate
  points, so the topology is `T₁`, hence Hausdorff as that of a topological group.
* `TauCeti.LieTestFunction.FixedSupport.instLocallyConvexSpace`: it is locally convex.
* `TauCeti.LieTestFunction.FixedSupport.instFirstCountableTopology`,
  `TauCeti.LieTestFunction.FixedSupport.instMetrizableSpace`: for a finite-dimensional Lie
  algebra it is first countable and metrizable.

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] {C : Set G}

/-- **The fixed-support seminorms separate points**: the seminorm of the empty word is the
supremum norm. -/
instance instT1Space : T1Space (FixedSupport I G C) := by
  refine (withSeminorms I G C).T1_of_separating fun a ha ↦ ⟨[], fun h0 ↦ ha ?_⟩
  refine ext (LieTestFunction.ext fun g ↦ ?_)
  have hg := norm_leftDerivWord_le [] (inclusion I G C a) g
  rw [← seminormFamily_apply, h0] at hg
  simpa using norm_le_zero_iff.mp hg

/-- **The fixed-support topology is locally convex.** -/
instance instLocallyConvexSpace : LocallyConvexSpace ℝ (FixedSupport I G C) :=
  (withSeminorms I G C).toLocallyConvexSpace

variable [FiniteDimensional ℝ E]

/-- For a finite-dimensional Lie algebra, the fixed-support topology is first countable: the
seminorms along the countably many words in a basis define it. -/
instance instFirstCountableTopology : FirstCountableTopology (FixedSupport I G C) :=
  (withSeminorms_basis (C := C) (Module.finBasis ℝ (GroupLieAlgebra I G))).firstCountableTopology

/-- **For a finite-dimensional Lie algebra, the fixed-support topology is metrizable**: it is the
topology of a first countable Hausdorff topological group. -/
instance instMetrizableSpace : MetrizableSpace (FixedSupport I G C) :=
  let _ : UniformSpace (FixedSupport I G C) :=
    IsTopologicalAddGroup.rightUniformSpace (FixedSupport I G C)
  have : IsUniformAddGroup (FixedSupport I G C) := isUniformAddGroup_of_addCommGroup
  have : (uniformity (FixedSupport I G C)).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  UniformSpace.metrizableSpace

end FixedSupport

end LieTestFunction

end TauCeti
