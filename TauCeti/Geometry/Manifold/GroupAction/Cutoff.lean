/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Geometry.Manifold.PartitionOfUnity.Cutoff
public import TauCeti.Topology.Algebra.GroupAction.Cutoff

/-!
# Smooth cutoff functions for proper actions on manifolds

Let a group `G` act properly discontinuously on a Hausdorff σ-compact finite-dimensional real
manifold `M` by `C^n` maps. Then `M` carries a `C^n` cutoff function for the action
(`TauCeti.MulAction.exists_isCutoff_contMDiff`): a nonnegative `C^n` function `c` with
`∑ᶠ g, c (g • x) = 1` for every `x`, whose support meets only finitely many translates of each
compact set. No faithfulness or freeness is assumed: every group element is counted, including
those acting trivially, so stabilizers and the ineffective kernel are retained.

For the action presentation `G ⋉ M` this is a cutoff function on the objects, summing to one over
the targets of the arrows with each given source, with the source map proper on the support of `c`
composed with the target (`TauCeti.MulAction.IsCutoff.isProperMap_snd`). Such functions turn
averages over the orbits of a proper action with noncompact orbit space into locally finite sums.

## Implementation notes

The construction first builds a nonnegative smooth function `β` whose support meets each orbit and
has the finiteness property. Since the orbit space is Hausdorff, there is such a `β` whose support
meets the preimage of each compact set of orbits in a compact set
(`TauCeti.exists_contMDiff_nonneg_isCompact_tsupport_inter_preimage`), and proper discontinuity
gives the finiteness property. Then `c = β / ∑ᶠ g, β (g • ·)` by
`TauCeti.MulAction.isCutoff_div_finsum`.

## References

* N. Bourbaki, *Integration II*, Chapter VII, §2, for Bruhat functions of proper actions.
* M. Crainic, *Differentiable and algebroid cohomology, van Est isomorphisms, and characteristic
  classes*, Comment. Math. Helv. **78** (2003), Section 2, for cutoff functions on proper
  groupoids.
-/

public section

open Function MulAction Set Topology
open scoped Manifold ContDiff Pointwise

namespace TauCeti.MulAction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  (G : Type*) [Group G] [MulAction G M]

/-- A properly discontinuous action by homeomorphisms on a Hausdorff σ-compact finite-dimensional
manifold has a nonnegative smooth function meeting every orbit, whose topological support meets only
finitely many translates of each compact set. -/
private theorem exists_contMDiff_nonneg_finite_smul_inter_tsupport [ContinuousConstSMul G M]
    [ProperlyDiscontinuousSMul G M] :
    ∃ β : M → ℝ, CMDiff ∞ β ∧ (∀ x, 0 ≤ β x) ∧
      (∀ ⦃K : Set M⦄, IsCompact K → {g : G | (g • K ∩ tsupport β).Nonempty}.Finite) ∧
      ∀ x, ∃ g : G, β (g • x) ≠ 0 := by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  let π : M → orbitRel.Quotient G M := Quotient.mk _
  have hπsmul (g : G) (x : M) : π (g • x) = π x := Quotient.sound ⟨g, rfl⟩
  obtain ⟨β, hβs, hβ0, hβK, hpos⟩ :=
    exists_contMDiff_nonneg_isCompact_tsupport_inter_preimage I (π := π)
      isOpenQuotientMap_quotientMk
  refine ⟨β, hβs, hβ0, fun K hK ↦ ?_, fun x ↦ ?_⟩
  · -- A translate `g • K` meeting the support of `β` meets it over the image of `K`.
    refine (properlyDiscontinuousSMul_iff.1 ‹_› hK
      (hβK (hK.image continuous_quotient_mk'))).subset ?_
    rintro g ⟨_, ⟨x, hx, rfl⟩, hgx⟩
    exact ⟨g • x, smul_mem_smul_set hx, hgx, x, hx, (hπsmul g x).symm⟩
  · obtain ⟨z, hzx, hz⟩ := hpos x
    obtain ⟨g, rfl⟩ := Quotient.exact hzx
    exact ⟨g, hz⟩

variable {I} {n : ℕ∞} [ContMDiffConstSMul I n G M]

/-- A group acting properly discontinuously by `C^n` maps on a Hausdorff σ-compact
finite-dimensional real manifold has a `C^n` cutoff function. -/
theorem exists_isCutoff_contMDiff [ProperlyDiscontinuousSMul G M] :
    ∃ c : M → ℝ, IsCutoff G c ∧ CMDiff n c := by
  have := ContMDiffConstSMul.continuousConstSMul (I := I) (Γ := G) (M := M) n
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨β, hβs, hβ0, hfin, hpos⟩ :=
    exists_contMDiff_nonneg_finite_smul_inter_tsupport I (M := M) G
  have hc := isCutoff_div_finsum hβ0 hfin hpos
  refine ⟨_, hc, (hβs.of_le (by simp)).div₀ ?_ fun x ↦ ?_⟩
  · exact contMDiff_finsum (fun g ↦ (hβs.of_le (by simp)).comp (contMDiff_const_smul g))
      (locallyFinite_support_apply_smul hfin)
  · exact (finsum_apply_smul_pos hβ0 hfin (hpos x)).ne'

end TauCeti.MulAction
