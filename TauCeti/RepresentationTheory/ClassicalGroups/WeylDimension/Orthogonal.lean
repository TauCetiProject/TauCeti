/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Diagram

/-!
# The shifted weights of the orthogonal groups

The Weyl dimension formulas for `SO (2n + 1)` (type `Bₙ`) and `SO (2n)` (type `Dₙ`) both read a
Young diagram `μ` through the integers `xᵢ = μᵢ + n - 1 - i`.  For type `Dₙ` the half-sum of the
positive roots is `ρ = (n - 1, …, 0)`, and the `xᵢ` are the entries of `μ + ρ`; for type `Bₙ` it is
`ρ = (n - 1/2, …, 1/2)`, and the `xᵢ` are the entries of `μ + ρ` less `1/2`.  This file records
the sequence and the two properties of it that make the factors of both numerators positive.

## Main definitions

* `TauCeti.orthogonalRhoShift`: the integers `μᵢ + n - 1 - i`.
-/

public section

namespace TauCeti

variable (n : ℕ) (μ : YoungDiagram)

/-- The integers `μᵢ + n - 1 - i`, shared by the orthogonal groups: the entries of `μ + ρ` for the
half-sum `ρ = (n - 1, …, 0)` of the positive roots of type `Dₙ` (`SO (2n)`), and the entries
`μᵢ + n - i - 1/2` of `μ + ρ` less `1/2` for the half-sum `ρ = (n - 1/2, …, 1/2)` of the positive
roots of type `Bₙ` (`SO (2n + 1)`).  Only the indices `i < n` are used. -/
def orthogonalRhoShift (i : ℕ) : ℤ := μ.rowLen i + n - 1 - i

/-- The defining equation of `TauCeti.orthogonalRhoShift`. -/
@[simp]
theorem orthogonalRhoShift_apply (i : ℕ) :
    orthogonalRhoShift n μ i = μ.rowLen i + n - 1 - i := (rfl)

variable {n μ} in
/-- The shifted entries are nonnegative below `n`. -/
theorem orthogonalRhoShift_nonneg {i : ℕ} (hi : i < n) : 0 ≤ orthogonalRhoShift n μ i := by
  rw [orthogonalRhoShift_apply]
  omega

/-- Adding the strictly decreasing `ρ` to the weakly decreasing row lengths gives a strictly
decreasing sequence, which makes every factor of the orthogonal Weyl dimension numerators
positive. -/
theorem orthogonalRhoShift_strictAnti : StrictAnti (orthogonalRhoShift n μ) := by
  intro i j hij
  have := μ.rowLen_anti i j hij.le
  simp only [orthogonalRhoShift_apply]
  omega

end TauCeti
