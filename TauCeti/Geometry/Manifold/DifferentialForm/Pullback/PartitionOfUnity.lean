/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Gluing pullbacks of differential forms with a partition of unity

Given a smooth partition of unity `ρ` on `M` subordinate to an open cover `U`, a smooth map
`b : X → M`, and maps `g i : X → Z` that are smooth only over `b ⁻¹' U i`, the weighted sum
`x ↦ ∑ᵢ ρᵢ (b x) • (g i)^* φ` of pullbacks of a smooth form `φ` on `Z` is a smooth form on `X`
(`TauCeti.isSmoothForm_sum_finsupport_smul_mpullback`). The sum is taken over the finite set
`ρ.finsupport (b x)` of indices whose bump does not vanish at `b x`, so it is pointwise finite and
only involves maps `g i` near points where they are smooth.

This is the smoothness half of the standard partition-of-unity constructions of homotopy
operators and descended forms from local sections, for instance the contracting homotopy of the
alternating pullback complex of a surjective submersion.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 2
  (partitions of unity) and Chapter 14 (pullbacks of differential forms).
-/

public section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable {EX HX X EZ HZ Z EM HM M F : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
  [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
  {IZ : ModelWithCorners ℝ EZ HZ} [TopologicalSpace Z] [ChartedSpace HZ Z]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  [IsManifold IX ∞ X] [IsManifold IZ ∞ Z]

/-- **Gluing pullbacks with a partition of unity.** Let `ρ` be a smooth partition of unity on `M`
subordinate to an open cover `U`, read on `X` through a smooth map `b : X → M`. If each
`g i : X → Z` is smooth at every point of `b ⁻¹' U i`, then for every smooth form `φ` on `Z` the
form `x ↦ ∑ᵢ ρᵢ (b x) • (g i)^* φ` on `X` is smooth, although no `g i` need be smooth
globally. -/
theorem isSmoothForm_sum_finsupport_smul_mpullback {ι : Type*}
    {ρ : SmoothPartitionOfUnity ι IM M univ} {U : ι → Set M} (hρ : ρ.IsSubordinate U)
    (hU : ∀ i, IsOpen (U i)) {b : X → M} (hb : ContMDiff IX IM ∞ b) {g : ι → X → Z}
    (hg : ∀ i x, b x ∈ U i → ContMDiffAt IX IZ ∞ (g i) x) (φ : SmoothForm IZ Z F k) :
    IsSmoothForm IX ∞
      (fun x ↦ ∑ i ∈ ρ.finsupport (b x), ρ i (b x) • mpullback (F := F) IX IZ (g i) φ.val x) := by
  rw [isSmoothForm_def]
  have hsum : ∀ x, ∑ i ∈ ρ.finsupport (b x), ρ i (b x) • mpullback (F := F) IX IZ (g i) φ.val x =
      ∑ᶠ i, ρ i (b x) • mpullback (F := F) IX IZ (g i) φ.val x := fun x ↦
    ρ.sum_finsupport_smul_eq_finsum (x₀ := b x)
      (φ := fun i _ ↦ mpullback (F := F) IX IZ (g i) φ.val x)
  simp_rw [hsum]
  refine ContMDiff.finsum_section_of_locallyFinite
    (t := fun i x ↦ ρ i (b x) • mpullback (F := F) IX IZ (g i) φ.val x) ?_ fun i ↦ ?_
  · refine (ρ.locallyFinite.preimage_continuous hb.continuous).subset fun i x hx ↦ ?_
    exact left_ne_zero_of_smul hx
  · refine ContMDiffOn.smul_section_of_tsupport (u := b ⁻¹' U i)
      ((ρ i).contMDiff.comp hb).contMDiffOn ((hU i).preimage hb.continuous)
      ((tsupport_comp_subset_preimage _ hb.continuous).trans (preimage_mono (hρ i)))
      fun x hx ↦ ?_
    exact ((φ.contMDiff (g i x)).mpullback_form (hg i x hx) (by simp)).contMDiffWithinAt

end TauCeti
