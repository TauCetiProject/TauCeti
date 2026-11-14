/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Splitting smooth Čech cocycles with a partition of unity

Let `U : ι → Set M` be an open cover of a Hausdorff σ-compact finite-dimensional smooth (`C^∞`)
real manifold, let `n ≤ ∞`, and let `ξ i j` be functions which are `C^n` on `U i ∩ U j` and
satisfy the cocycle relation `ξ i j + ξ j k = ξ i k` on `U i ∩ U j ∩ U k`. Then there are
functions `g i`, `C^n` on `U i`, with `ξ i j = g j - g i` on `U i ∩ U j`
(`TauCeti.exists_contMDiffOn_eq_sub_of_cocycle`): for a smooth partition of unity `ρ`
subordinate to `U`, take `g i = ∑ᶠ k, ρ k • ξ k i`. Being a convex combination, this splitting
is bounded by any common bound of the `ξ k i`.

This is the explicit form of the vanishing of degree one Čech cohomology of sheaves of smooth
functions, used to split a holomorphic cocycle on a Riemann surface into smooth functions before
solving the `\bar∂`-equation (Forster, *Lectures on Riemann Surfaces*, §14.7). The categorical
form, for the sheaf of smooth functions and in every degree, is
`TauCeti.smoothSheafModule.isZero_cechCohomology_obj_succ`; the form here keeps the splitting
functions and their sup-norm bound, which the finiteness argument for `H¹` of the structure sheaf
of a compact Riemann surface uses.

## Main results

* `SmoothPartitionOfUnity.IsSubordinate.contMDiffOn_finsum_smul`,
  `PartitionOfUnity.IsSubordinate.norm_finsum_smul_le`: smoothness and the convexity bound
  of `∑ᶠ i, ρ i • g i` for functions `g i` given only on the members of the cover.
* `PartitionOfUnity.IsSubordinate.eq_finsum_smul_sub_finsum_smul`: the splitting identity.
* `TauCeti.exists_contMDiffOn_eq_sub_of_cocycle`: smooth Čech `1`-cocycles split, boundedly.

## References

* O. Forster, *Lectures on Riemann Surfaces*, §14.
-/

public section

open Set Function

open scoped Manifold ContDiff

variable {ι : Type*}

namespace PartitionOfUnity.IsSubordinate

variable {X : Type*} [TopologicalSpace X] {s : Set X} {ρ : PartitionOfUnity ι X s}
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
cocycle relation `ξ i j + ξ j k = ξ i k` on triple intersections, the functions
`g i = ∑ᶠ k, ρ k • ξ k i` satisfy `ξ i j = g j - g i` on `s ∩ U i ∩ U j`. -/
theorem eq_finsum_smul_sub_finsum_smul {F : Type*} [AddCommGroup F] [Module ℝ F]
    (hρ : ρ.IsSubordinate U) {ξ : ι → ι → X → F}
    (hcocycle : ∀ i j k, ∀ x ∈ U i ∩ U j ∩ U k, ξ i j x + ξ j k x = ξ i k x) {i j : ι} {x : X}
    (hxs : x ∈ s) (hx : x ∈ U i ∩ U j) :
    ξ i j x = (∑ᶠ k, ρ k x • ξ k j x) - ∑ᶠ k, ρ k x • ξ k i x := by
  have hfin : (support fun k ↦ ρ k x).Finite := ρ.locallyFinite.point_finite x
  have hfin' (l : ι) : (support fun k ↦ ρ k x • ξ k l x).Finite :=
    hfin.subset fun k hk ↦ left_ne_zero_of_smul hk
  rw [← finsum_sub_distrib (hfin' j) (hfin' i)]
  have hterm : ∀ k, ρ k x • ξ k j x - ρ k x • ξ k i x = ρ k x • ξ i j x := fun k ↦ by
    by_cases hk : ρ k x = 0
    · simp [hk]
    · have hxk : x ∈ U k := hρ k (subset_tsupport _ hk)
      rw [← smul_sub, ← hcocycle k i j x ⟨⟨hxk, hx.1⟩, hx.2⟩, add_sub_cancel_left]
  simp_rw [hterm, ← finsum_smul, ρ.sum_eq_one hxs, one_smul]

end PartitionOfUnity.IsSubordinate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞}

namespace SmoothPartitionOfUnity.IsSubordinate

variable {s : Set M} {ρ : SmoothPartitionOfUnity ι I M s} {U : ι → Set M}

/-- For a partition of unity `ρ` subordinate to an open cover `U`, a set `V` and functions
`g i` that are `C^n` on `U i ∩ V`, the function `∑ᶠ i, ρ i • g i` is `C^n` on `V`. -/
theorem contMDiffOn_finsum_smul (hρ : ρ.IsSubordinate U) (hUo : ∀ i, IsOpen (U i))
    {V : Set M} {g : ι → M → F} (hg : ∀ i, ContMDiffOn I 𝓘(ℝ, F) n (g i) (U i ∩ V)) :
    ContMDiffOn I 𝓘(ℝ, F) n (fun x ↦ ∑ᶠ i, ρ i x • g i x) V := fun x hx ↦ by
  refine contMDiffWithinAt_finsum (ρ.locallyFinite.smul_left _) fun i ↦ ?_
  by_cases hxi : x ∈ tsupport (ρ i)
  · exact (((ρ i).contMDiff.of_le (mod_cast le_top)).contMDiffAt).contMDiffWithinAt.smul
      ((hg i x ⟨hρ i hxi, hx⟩).mono_of_mem_nhdsWithin
        (Filter.inter_mem (mem_nhdsWithin_of_mem_nhds ((hUo i).mem_nhds (hρ i hxi)))
          self_mem_nhdsWithin))
  · exact contMDiffWithinAt_of_notMem (compl_subset_compl.mpr
      (tsupport_smul_subset_left (ρ i) (g i)) hxi) n V

end SmoothPartitionOfUnity.IsSubordinate

namespace TauCeti

variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

/-- **Smooth Čech `1`-cocycles split.** On a Hausdorff σ-compact finite-dimensional smooth (`C^∞`)
real manifold, if `U` is an open cover, `n ≤ ∞`, and `ξ i j` is `C^n` on `U i ∩ U j` with
`ξ i j + ξ j k = ξ i k` on `U i ∩ U j ∩ U k`, then there are functions `g i`, `C^n` on `U i`, with
`ξ i j = g j - g i` on `U i ∩ U j`. Moreover `‖g i‖ ≤ C` on `U i` whenever `‖ξ k i‖ ≤ C` on every
`U k ∩ U i`. -/
theorem exists_contMDiffOn_eq_sub_of_cocycle {U : ι → Set M} (hUo : ∀ i, IsOpen (U i))
    (hU : ⋃ i, U i = univ) {ξ : ι → ι → M → F}
    (hξ : ∀ i j, ContMDiffOn I 𝓘(ℝ, F) n (ξ i j) (U i ∩ U j))
    (hcocycle : ∀ i j k, ∀ x ∈ U i ∩ U j ∩ U k, ξ i j x + ξ j k x = ξ i k x) :
    ∃ g : ι → M → F, (∀ i, ContMDiffOn I 𝓘(ℝ, F) n (g i) (U i)) ∧
      (∀ i j, ∀ x ∈ U i ∩ U j, ξ i j x = g j x - g i x) ∧
      ∀ i C, (∀ k, ∀ x ∈ U k ∩ U i, ‖ξ k i x‖ ≤ C) → ∀ x ∈ U i, ‖g i x‖ ≤ C := by
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ U hUo hU.ge
  exact ⟨fun i x ↦ ∑ᶠ k, ρ k x • ξ k i x,
    fun i ↦ hρ.contMDiffOn_finsum_smul hUo fun k ↦ hξ k i,
    fun i j x hx ↦ hρ.toPartitionOfUnity.eq_finsum_smul_sub_finsum_smul hcocycle (mem_univ x) hx,
    fun _ _ hC x hx ↦
      hρ.toPartitionOfUnity.norm_finsum_smul_le (mem_univ x) fun k hk ↦ hC k x ⟨hk, hx⟩⟩

end TauCeti
