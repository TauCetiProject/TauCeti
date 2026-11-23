/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Topology.PartitionOfUnity.CechSplitting

/-!
# Splitting smooth Čech cocycles with a partition of unity

Let `U : ι → Set M` be an open cover of a Hausdorff σ-compact finite-dimensional smooth (`C^∞`)
real manifold, let `n ≤ ∞`, and let `ξ i j` be functions which are `C^n` on `U i ∩ U j` and
satisfy the twisted cocycle relation `ξ i j + ψ i j • ξ j k = ξ i k` on `U i ∩ U j ∩ U k`, for
arbitrary overlap scalars `ψ i j` (the untwisted case is `ψ = 1`). Then there are functions
`g i`, `C^n` on `U i`, with `ξ i j = ψ i j • g j - g i` on `U i ∩ U j`
(`TauCeti.exists_contMDiffOn_eq_smul_sub_of_cocycle`): for a smooth partition of unity `ρ`
subordinate to `U`, take `g i = -∑ᶠ k, ρ k • ξ i k`. Being a convex combination, this splitting
is bounded by any common bound of the `ξ i k`, with no bound on `ψ`.

This is the explicit form of the vanishing of degree one Čech cohomology of sheaves of smooth
sections, used to split a holomorphic cocycle on a Riemann surface, in the frames of a line
bundle, into smooth functions before solving the `\bar∂`-equation (Forster, *Lectures on Riemann
Surfaces*, §14.7). The categorical form, for the sheaf of smooth functions and in every positive
degree, is `TauCeti.smoothSheafModule.isZero_cechCohomology_obj_succ`; the form here keeps the
splitting functions and their sup-norm bound, which the finiteness argument for `H¹` of the
structure sheaf of a compact Riemann surface uses.

## Main results

* `SmoothPartitionOfUnity.IsSubordinate.contMDiffOn_finsum_smul`: smoothness of
  `∑ᶠ i, ρ i • g i` for functions `g i` given only on the members of the cover.
* `TauCeti.exists_contMDiffOn_eq_smul_sub_of_cocycle`: smooth twisted Čech `1`-cocycles split,
  boundedly.

The pointwise splitting identity and the convexity bound are
`PartitionOfUnity.IsSubordinate.eq_finsum_smul_sub_smul_finsum_smul` and
`PartitionOfUnity.IsSubordinate.norm_finsum_smul_le`.

## References

* O. Forster, *Lectures on Riemann Surfaces*, §14.
-/
public section

open Set Function

open scoped Manifold ContDiff

variable {ι : Type*}

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
`ξ i j + ψ i j • ξ j k = ξ i k` on `U i ∩ U j ∩ U k`, for arbitrary overlap scalars `ψ i j`, then
there are functions `g i`, `C^n` on `U i`, with `ξ i j = ψ i j • g j - g i` on `U i ∩ U j`.
Moreover `‖g i‖ ≤ C` on `U i` whenever `‖ξ i k‖ ≤ C` on every `U i ∩ U k`. -/
theorem exists_contMDiffOn_eq_smul_sub_of_cocycle {R : Type*} [DistribSMul R F]
    [SMulCommClass ℝ R F] {U : ι → Set M} (hUo : ∀ i, IsOpen (U i)) (hU : ⋃ i, U i = univ)
    {ψ : ι → ι → M → R} {ξ : ι → ι → M → F}
    (hξ : ∀ i j, ContMDiffOn I 𝓘(ℝ, F) n (ξ i j) (U i ∩ U j))
    (hcocycle : ∀ i j k, ∀ x ∈ U i ∩ U j ∩ U k, ξ i j x + ψ i j x • ξ j k x = ξ i k x) :
    ∃ g : ι → M → F, (∀ i, ContMDiffOn I 𝓘(ℝ, F) n (g i) (U i)) ∧
      (∀ i j, ∀ x ∈ U i ∩ U j, ξ i j x = ψ i j x • g j x - g i x) ∧
      ∀ i C, (∀ k, ∀ x ∈ U i ∩ U k, ‖ξ i k x‖ ≤ C) → ∀ x ∈ U i, ‖g i x‖ ≤ C := by
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ U hUo hU.ge
  refine ⟨fun i x ↦ -∑ᶠ k, ρ k x • ξ i k x,
    fun i ↦ (hρ.contMDiffOn_finsum_smul hUo fun k ↦ (hξ i k).mono (inter_comm _ _).le).neg,
    fun i j x hx ↦ ?_, fun i _ hC x hx ↦ ?_⟩
  · rw [hρ.toPartitionOfUnity.eq_finsum_smul_sub_smul_finsum_smul hcocycle (mem_univ x) hx,
      smul_neg, sub_neg_eq_add, neg_add_eq_sub]
    rfl
  · rw [norm_neg]
    exact hρ.toPartitionOfUnity.norm_finsum_smul_le (mem_univ x) fun k hk ↦ hC k x ⟨hx, hk⟩

end TauCeti
