/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.PartitionOfUnity
import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Splitting Čech cocycles with a partition of unity

Let `ρ` be a partition of unity of `s` subordinate to `U`, and let `ξ i j` satisfy the twisted
cocycle relation `ξ i j + ψ i j • ξ j k = ξ i k` on `U i ∩ U j ∩ U k`, for arbitrary overlap
scalars `ψ i j` (the untwisted case is `ψ = 1`). Then `g i = -∑ᶠ k, ρ k • ξ i k` splits it:
`ξ i j = ψ i j • g j - g i` on `s ∩ U i ∩ U j`
(`PartitionOfUnity.IsSubordinate.eq_finsum_smul_sub_smul_finsum_smul`). Being a convex
combination, `∑ᶠ k, ρ k • ξ i k` is bounded by any common bound of the `ξ i k`
(`PartitionOfUnity.IsSubordinate.norm_finsum_smul_le`), whatever the size of `ψ`.

This is the pointwise algebra behind the vanishing of degree one Čech cohomology of fine
sheaves, used for sheaves of smooth sections of line bundles on a Riemann surface in Forster,
*Lectures on Riemann Surfaces*, §14.7.

## References

* O. Forster, *Lectures on Riemann Surfaces*, §14.
-/

public section

open Function

namespace PartitionOfUnity.IsSubordinate

variable {ι X : Type*} [TopologicalSpace X] {s : Set X} {ρ : PartitionOfUnity ι X s}
  {U : ι → Set X}

/-- For a partition of unity `ρ` of `s` subordinate to `U` and a point `x ∈ s`, if `‖g i x‖ ≤ C`
whenever `x ∈ U i`, then `‖∑ᶠ i, ρ i x • g i x‖ ≤ C`. -/
theorem norm_finsum_smul_le {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (hρ : ρ.IsSubordinate U) {g : ι → X → F} {C : ℝ} {x : X}
    (hxs : x ∈ s) (hC : ∀ i, x ∈ U i → ‖g i x‖ ≤ C) : ‖∑ᶠ i, ρ i x • g i x‖ ≤ C :=
  mem_closedBall_zero_iff.1 <| ρ.finsum_smul_mem_convex hxs
    (fun i hi ↦ mem_closedBall_zero_iff.2 (hC i (hρ i (subset_tsupport _ hi))))
    (convex_closedBall 0 C)

/-- For a partition of unity `ρ` of `s` subordinate to `U` and a family `ξ i j` satisfying the
twisted cocycle relation `ξ i j + ψ i j • ξ j k = ξ i k` on triple intersections, the functions
`g i = -∑ᶠ k, ρ k • ξ i k` satisfy `ξ i j = ψ i j • g j - g i` on `s ∩ U i ∩ U j`. No condition
on the overlap scalars `ψ` is needed. -/
theorem eq_finsum_smul_sub_smul_finsum_smul {R F : Type*} [AddCommGroup F] [Module ℝ F]
    [DistribSMul R F] [SMulCommClass ℝ R F] (hρ : ρ.IsSubordinate U) {ψ : ι → ι → X → R}
    {ξ : ι → ι → X → F}
    (hcocycle : ∀ i j k, ∀ x ∈ U i ∩ U j ∩ U k, ξ i j x + ψ i j x • ξ j k x = ξ i k x)
    {i j : ι} {x : X} (hxs : x ∈ s) (hx : x ∈ U i ∩ U j) :
    ξ i j x = (∑ᶠ k, ρ k x • ξ i k x) - ψ i j x • ∑ᶠ k, ρ k x • ξ j k x := by
  have hfin : (support fun k ↦ ρ k x).Finite := ρ.locallyFinite.point_finite x
  have hfin' (l : ι) : (support fun k ↦ ρ k x • ξ l k x).Finite :=
    hfin.subset fun k hk ↦ left_ne_zero_of_smul hk
  have hfin'' : (support fun k ↦ ψ i j x • ρ k x • ξ j k x).Finite :=
    (hfin' j).subset fun k hk h ↦ hk (by simp only [h, smul_zero])
  rw [smul_finsum' _ (hfin' j), ← finsum_sub_distrib (hfin' i) hfin'']
  have hterm : ∀ k, ρ k x • ξ i k x - ψ i j x • ρ k x • ξ j k x = ρ k x • ξ i j x := fun k ↦ by
    by_cases hk : ρ k x = 0
    · simp [hk]
    · have hxk : x ∈ U k := hρ k (subset_tsupport _ hk)
      rw [← smul_comm (ρ k x), ← smul_sub, ← hcocycle i j k x ⟨hx, hxk⟩, add_sub_cancel_right]
  simp_rw [hterm, ← finsum_smul, ρ.sum_eq_one hxs, one_smul]

end PartitionOfUnity.IsSubordinate
