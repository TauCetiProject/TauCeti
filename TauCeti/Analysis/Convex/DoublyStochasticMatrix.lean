/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.DoublyStochasticMatrix
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Order.Monotone.Monovary

import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Convex.Birkhoff

/-!
# Inequalities under doubly stochastic averaging

If `M` is a doubly stochastic matrix and `y = M x`, then every coordinate of `y` is a convex
combination of the coordinates of `x`, with weights the corresponding row of `M`. Jensen's
inequality bounds `φ (y i)` by the same convex combination of the values `φ (x j)`, and summing
over `i`, the column sums of `M` being `1`, gives `∑ i, φ (y i) ≤ ∑ j, φ (x j)` for every convex
`φ`. This is the easy direction of the Hardy–Littlewood–Pólya characterization of majorization;
it is the step through which the forward Schur–Horn inequality passes from the spectrum of a
symmetric operator to its diagonal in an arbitrary orthonormal basis.

Doubly stochastic averaging also cannot increase a sorted pairing. If `x` and `y` monovary (for
instance, both are sorted decreasingly), the rearrangement inequality says that the pairing
`∑ i, x i * y (σ i)` is largest at `σ = 1`. By Birkhoff's theorem every doubly stochastic matrix is
a convex combination of permutation matrices, so `x ⬝ᵥ (M *ᵥ y) ≤ x ⬝ᵥ y`. This is the
combinatorial core of the von Neumann trace inequality.

## Main results

* `ConvexOn.sum_map_mulVec_le_of_mem_doublyStochastic`: for a doubly stochastic `M` and a convex
  `φ`, `∑ i, φ ((M *ᵥ x) i) ≤ ∑ i, φ (x i)`.
* `Monovary.dotProduct_mulVec_le_of_mem_doublyStochastic`: for a doubly stochastic `M` and
  monovarying `x` and `y`, `x ⬝ᵥ (M *ᵥ y) ≤ x ⬝ᵥ y`.

## References

* A. W. Marshall, I. Olkin, B. C. Arnold, *Inequalities: Theory of Majorization and Its
  Applications*, 2nd ed., Springer (2011), Proposition 4.B.1.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer (1997), Chapter II.
-/

public section

open Finset Matrix

variable {𝕜 β n : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup β]
  [PartialOrder β] [IsOrderedAddMonoid β] [Module 𝕜 β] [IsStrictOrderedModule 𝕜 β]
  [Fintype n] [DecidableEq n]

/-- **Convex functions decrease under doubly stochastic averaging.** If `M` is doubly stochastic,
`φ` is convex on `s`, and every coordinate of `x` lies in `s`, then
`∑ i, φ ((M *ᵥ x) i) ≤ ∑ i, φ (x i)`. -/
theorem ConvexOn.sum_map_mulVec_le_of_mem_doublyStochastic {s : Set 𝕜} {φ : 𝕜 → β}
    (hφ : ConvexOn 𝕜 s φ) {M : Matrix n n 𝕜} (hM : M ∈ doublyStochastic 𝕜 n) {x : n → 𝕜}
    (hx : ∀ i, x i ∈ s) : ∑ i, φ ((M *ᵥ x) i) ≤ ∑ i, φ (x i) :=
  calc ∑ i, φ ((M *ᵥ x) i)
      ≤ ∑ i, ∑ j, M i j • φ (x j) := by
        gcongr with i
        simpa [mulVec, dotProduct] using
          hφ.map_sum_le (fun j _ ↦ nonneg_of_mem_doublyStochastic hM)
            (sum_row_of_mem_doublyStochastic hM i) (fun j _ ↦ hx j)
    _ = ∑ j, (∑ i, M i j) • φ (x j) := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_smul]
    _ = ∑ j, φ (x j) := by simp [sum_col_of_mem_doublyStochastic hM]

/-- **Doubly stochastic averaging decreases a sorted pairing.** If `x` and `y` monovary and `M` is
doubly stochastic, then `x ⬝ᵥ (M *ᵥ y) ≤ x ⬝ᵥ y`. -/
theorem Monovary.dotProduct_mulVec_le_of_mem_doublyStochastic {x y : n → 𝕜} (hxy : Monovary x y)
    {M : Matrix n n 𝕜} (hM : M ∈ doublyStochastic 𝕜 n) : x ⬝ᵥ (M *ᵥ y) ≤ x ⬝ᵥ y := by
  rw [← SetLike.mem_coe, doublyStochastic_eq_convexHull_permMatrix] at hM
  refine convexHull_min ?_
    (convex_halfSpace_le (f := fun A : Matrix n n 𝕜 ↦ x ⬝ᵥ (A *ᵥ y)) ?_ (x ⬝ᵥ y)) hM
  · rintro _ ⟨σ, rfl⟩
    simpa [permMatrix_mulVec, dotProduct] using hxy.sum_mul_comp_perm_le_sum_mul (σ := σ)
  · exact ⟨fun A B ↦ by simp [add_mulVec], fun c A ↦ by simp [smul_mulVec]⟩
