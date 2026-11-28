/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.ColengthIndex

/-!
# Index bounds for images of local lattices

To bound the index of a family of image vectors, it suffices to control the colength of
submodules on the source that are sent into the local integral submodules of the target.
A finite collection of maps with a common source bound costs at most one copy of the index
budget per map. The target family need not come with a partition or a choice of preimages.

This is the index argument of `New.Data.indexLe_normalizedPoincare` and
`New.Data.indexLe_of_mem_image_normalizedPoincare` in `New/Reduction/ShortAndEnough.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) at `72fead1`.
-/

public section

open scoped NNReal

namespace TauCeti.PrimePadicIso

variable {U V : Type*} [AddCommMonoid U] [Module ℂ U] [AddCommMonoid V] [Module ℂ V]
variable {M : (ι : PrimePadicIso) → Submodule ι.integers U}
variable {L : (ι : PrimePadicIso) → Submodule ι.integers V}
variable {I : Type*} [Fintype I] [DecidableEq I] {y : I → V} {δ : ℝ}

/-- A family in the image of `A` under `f` has index at most `δ` if `A` lies in the source
submodules `M`, and the colength of the condition that `f` land in `L` divides a prime power
at each embedding. The logarithmic budget is uniform over embeddings above each prime. -/
theorem indexLe_of_mem_image_of_colengthDvd (f : U →ₗ[ℂ] V) {A : Set U}
    (hA : ∀ ι : PrimePadicIso, A ⊆ M ι) (hy : ∀ i, y i ∈ f '' A) (e : ℕ → ℝ≥0)
    (hbudget : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → ∑ p ∈ S, (e p : ℝ) * Real.log p ≤ δ)
    (hlocal : ∀ ι : PrimePadicIso, ∃ (N : Submodule ι.integers U) (j : ℕ),
      (j : ℝ) ≤ e ι.prime ∧ (M ι).ColengthDvd N ((ι.prime : ι.integers) ^ j) ∧
        N.map (f.restrictScalars ι.integers) ≤ L ι) :
    IndexLe L y δ := by
  apply indexLe_of_colengthDvd e hbudget
  intro ι
  let g := f.restrictScalars ι.integers
  obtain ⟨N, j, hj, hcol, hN⟩ := hlocal ι
  refine ⟨(M ι).map g, fun i ↦ ?_, j, hj, hcol.map g le_sup_left hN⟩
  obtain ⟨x, hx, hxy⟩ := hy i
  exact Submodule.mem_map.mpr ⟨x, hA ι hx, hxy⟩

/-- A family in finitely many images of `A` has index at most `#S * δ`. The good source
submodule may vary by map and embedding, but the budget for its colength in `M` is the same
in every block. -/
theorem indexLe_of_mem_biUnion_image_of_colengthDvd {κ : Type*} (S : Finset κ)
    (f : κ → U →ₗ[ℂ] V) {A : Set U} (hA : ∀ ι : PrimePadicIso, A ⊆ M ι)
    (hy : ∀ i, y i ∈ ⋃ k ∈ S, f k '' A) (e : ℕ → ℝ≥0)
    (hbudget : ∀ T : Finset ℕ, (∀ p ∈ T, p.Prime) → ∑ p ∈ T, (e p : ℝ) * Real.log p ≤ δ)
    (hlocal : ∀ k ∈ S, ∀ ι : PrimePadicIso, ∃ (N : Submodule ι.integers U) (j : ℕ),
      (j : ℝ) ≤ e ι.prime ∧ (M ι).ColengthDvd N ((ι.prime : ι.integers) ^ j) ∧
        N.map ((f k).restrictScalars ι.integers) ≤ L ι) :
    IndexLe L y ((S.card : ℝ) * δ) := by
  have h := indexLe_of_mem_biUnion (d := fun _ ↦ δ) S (fun k hk _ _ _ _ hz ↦
    indexLe_of_mem_image_of_colengthDvd (f k) hA hz e hbudget (hlocal k hk)) hy
  simpa only [Finset.sum_const, nsmul_eq_mul] using h

end TauCeti.PrimePadicIso
