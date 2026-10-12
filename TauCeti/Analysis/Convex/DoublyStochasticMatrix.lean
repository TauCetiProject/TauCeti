/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.DoublyStochasticMatrix
public import Mathlib.Analysis.Convex.Jensen

/-!
# Convex functions decrease under doubly stochastic averaging

If `M` is a doubly stochastic matrix and `y = M x`, then every coordinate of `y` is a convex
combination of the coordinates of `x`, with weights the corresponding row of `M`. Jensen's
inequality bounds `φ (y i)` by the same convex combination of the values `φ (x j)`, and summing
over `i`, the column sums of `M` being `1`, gives `∑ i, φ (y i) ≤ ∑ j, φ (x j)` for every convex
`φ`. This is the easy direction of the Hardy–Littlewood–Pólya characterization of majorization;
it is the step through which the forward Schur–Horn inequality passes from the spectrum of a
symmetric operator to its diagonal in an arbitrary orthonormal basis.

## Main results

* `ConvexOn.sum_map_mulVec_le_of_mem_doublyStochastic`: for a doubly stochastic `M` and a convex
  `φ`, `∑ i, φ ((M *ᵥ x) i) ≤ ∑ i, φ (x i)`.

## References

* A. W. Marshall, I. Olkin, B. C. Arnold, *Inequalities: Theory of Majorization and Its
  Applications*, 2nd ed., Springer (2011), Proposition 4.B.1.
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
