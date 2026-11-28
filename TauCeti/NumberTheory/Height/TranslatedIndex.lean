/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.ColengthIndex

/-!
# Index bounds for families in finitely many linear images

Local colength controls a family in the image of a source lattice even when the linear map
has a kernel. For finitely many images the index costs add, with each image charged only
once, regardless of the number of vectors chosen from it.

The application to normalized Poincaré translates is the index argument of
`New.Data.indexLe_of_mem_image_normalizedPoincare` in `grh/src/New/Reduction/ShortAndEnough.lean`
of [grh-lean](https://github.com/lsernau/grh-lean), revision `72fead1`.
-/

public section

open scoped NNReal

namespace TauCeti.PrimePadicIso

/-- Let each of the linear maps `f k`, for `k ∈ S`, have local colength dividing `p ^ j`
for the pullback of the target integral submodule in a source submodule containing `A`.
If `j ≤ D * e p` and the sum of `e p * log p` over any finite set of primes is at most `δ`,
then every finite family from the union of the images `f k '' A` has index at most
`S.card * D * δ`. The source submodule and `j` can vary with both the map and the embedding. -/
theorem indexLe_of_mem_biUnion_image_of_colengthDvd
    {U V I κ : Type*} [AddCommMonoid U] [Module ℂ U] [AddCommMonoid V] [Module ℂ V]
    [Fintype I] [DecidableEq I] {L : (ι : PrimePadicIso) → Submodule ι.integers V}
    {A : Set U} {y : I → V} (S : Finset κ) (f : κ → U →ₗ[ℂ] V) (D : ℝ≥0)
    (e : ℕ → ℝ≥0) {δ : ℝ}
    (hbudget : ∀ T : Finset ℕ, (∀ p ∈ T, p.Prime) → ∑ p ∈ T, (e p : ℝ) * Real.log p ≤ δ)
    (hlocal : ∀ k ∈ S, ∀ ι : PrimePadicIso, ∃ M : Submodule ι.integers U, A ⊆ M ∧
      ∃ j : ℕ, (j : ℝ) ≤ D * e ι.prime ∧
        M.ColengthDvd ((L ι).comap ((f k).restrictScalars ι.integers)) ((ι.prime : ι.integers) ^ j))
    (hy : ∀ i, y i ∈ ⋃ k ∈ S, f k '' A) : IndexLe L y (S.card * (D : ℝ) * δ) := by
  have hscaled (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
      ∑ p ∈ T, ((D * e p : ℝ≥0) : ℝ) * Real.log p ≤ (D : ℝ) * δ := by
    simpa only [NNReal.coe_mul, mul_assoc, ← Finset.mul_sum] using
      mul_le_mul_of_nonneg_left (hbudget T hT) D.coe_nonneg
  have h : IndexLe L y (∑ _k ∈ S, (D : ℝ) * δ) := by
    refine indexLe_of_mem_biUnion S (A := fun k ↦ f k '' A) ?_ hy
    intro k hk J _ _ z hz
    refine indexLe_of_colengthDvd (fun p ↦ D * e p) hscaled fun ι ↦ ?_
    obtain ⟨M, hA, j, hj, hcol⟩ := hlocal k hk ι
    let F := (f k).restrictScalars ι.integers
    refine ⟨M.map F, fun i ↦ ?_, j, hj, ?_⟩
    · obtain ⟨x, hx, heq⟩ := hz i
      exact Submodule.mem_map.mpr ⟨x, hA hx, by
        simpa only [F, LinearMap.restrictScalars_apply] using heq⟩
    · exact hcol.map F le_sup_left (Submodule.map_comap_le _ _)
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_assoc] using h

end TauCeti.PrimePadicIso
