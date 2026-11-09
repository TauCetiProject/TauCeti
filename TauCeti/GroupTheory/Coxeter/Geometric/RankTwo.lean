/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Geometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Positive rank-two geometric roots

The image of a simple root under an alternating word has two explicit coefficients.
Writing `m = M i j`, these are consecutive terms of the sequence
`S(n) = sin(n π / m) / sin(π / m)` when `m ≥ 2`, and `S(n) = n` when
`m = 0` (an infinite Coxeter entry). Both coefficients are nonnegative before the
braid length. This is the rank-two input to the sign/length theorem for the
geometric representation; no finiteness or nondegeneracy is assumed.

We use Mathlib's Chebyshev polynomials `Polynomial.Chebyshev.U` to define the
coefficients uniformly, including infinite entries, and consume their recurrence
and trigonometric evaluation. The native `CoxeterSystem.alternatingWord i j k`
ends in `j`: its image of the root at `i` has coefficients `(S(k+1), S(k))`
for even `k`, and `(S(k), S(k+1))` for odd `k`.

## Main results

* `CoxeterMatrix.dihedralCoeff`: the coefficients in the rank-two root calculation.
* `CoxeterSystem.geometricRepresentation_alternatingWord`: the exact root formula.
* `CoxeterSystem.rankTwo_nonnegative`: below the braid length, that image is a
  nonnegative combination of the two simple roots.

## References

* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, §5.4, pp. 112–113.
-/

public noncomputable section

open Real Polynomial.Chebyshev

namespace CoxeterMatrix

variable {I : Type*} (M : CoxeterMatrix I)

/-- The rank-two geometric coefficient `S(n)`, defined by evaluating the Chebyshev
polynomial `U_(n-1)` at `cos(π / M i j)`. At an infinite entry it is `n`. -/
def dihedralCoeff (i j : I) (n : ℕ) : ℝ :=
  (U ℝ ((n : ℤ) - 1)).eval (cos (π / M i j))

/-- The rank-two coefficient sequence is symmetric in its two indices. -/
theorem dihedralCoeff_comm (i j : I) : M.dihedralCoeff j i = M.dihedralCoeff i j := by
  funext n
  simp only [dihedralCoeff, M.symmetric j i]

@[simp]
theorem dihedralCoeff_zero (i j : I) : M.dihedralCoeff i j 0 = 0 := by
  simp [dihedralCoeff]

@[simp]
theorem dihedralCoeff_one (i j : I) : M.dihedralCoeff i j 1 = 1 := by
  simp [dihedralCoeff]

/-- The recurrence governing the two coefficients of successive alternating roots. -/
theorem dihedralCoeff_add_two (i j : I) (n : ℕ) :
    M.dihedralCoeff i j (n + 2) =
      2 * cos (π / M i j) * M.dihedralCoeff i j (n + 1) - M.dihedralCoeff i j n := by
  unfold dihedralCoeff
  push_cast
  rw [show (n : ℤ) + 2 - 1 = (n : ℤ) - 1 + 2 by omega, U_add_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, sub_add_cancel, add_sub_cancel_right]

/-- At an infinite Coxeter entry, the rank-two coefficients grow linearly. -/
theorem dihedralCoeff_of_eq_zero {i j : I} (hm : M i j = 0) (n : ℕ) :
    M.dihedralCoeff i j n = n := by
  simp [dihedralCoeff, hm, U_eval_one]

/-- For a finite off-diagonal Coxeter entry the coefficients are sine quotients. -/
theorem dihedralCoeff_eq_sin_div {i j : I} (hm : 2 ≤ M i j) (n : ℕ) :
    M.dihedralCoeff i j n = sin (n * (π / M i j)) / sin (π / M i j) := by
  apply (eq_div_iff
    (TauCeti.sin_pi_div_pos (by exact_mod_cast (show 1 < M i j by omega))).ne').2
  simp [dihedralCoeff]

/-- The coefficient is nonnegative up to and including the finite braid length,
or at every index for an infinite entry. -/
theorem dihedralCoeff_nonneg (i j : I) {n : ℕ} (hn : n ≤ M i j ∨ M i j = 0) :
    0 ≤ M.dihedralCoeff i j n := by
  by_cases hm : M i j = 0
  · rw [M.dihedralCoeff_of_eq_zero hm]
    positivity
  have hn : n ≤ M i j := hn.resolve_right hm
  by_cases hm1 : M i j = 1
  · have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> simp
  have hm2 : 2 ≤ M i j := by omega
  rw [M.dihedralCoeff_eq_sin_div hm2]
  apply div_nonneg
  · apply sin_nonneg_of_nonneg_of_le_pi (by positivity)
    have h : (n : ℝ) ≤ M i j := by exact_mod_cast hn
    calc
      (n : ℝ) * (π / M i j) ≤ (M i j : ℝ) * (π / M i j) :=
        mul_le_mul_of_nonneg_right h (by positivity)
      _ = π := mul_div_cancel₀ π (Nat.cast_ne_zero.mpr hm)
  · exact (TauCeti.sin_pi_div_pos (by exact_mod_cast (show 1 < M i j by omega))).le

end CoxeterMatrix

namespace CoxeterSystem

variable {I W : Type*} [Group W] {M : CoxeterMatrix I} (cs : CoxeterSystem M W)

/-- The exact image of a simple root under the native alternating word ending in
the other index. The consecutive Chebyshev coefficients exchange places at each step. -/
theorem geometricRepresentation_alternatingWord (i j : I) (k : ℕ) :
    cs.geometricRepresentation (cs.wordProd (alternatingWord i j k)) (Finsupp.single i 1) =
      if Even k then
        M.dihedralCoeff i j (k + 1) • Finsupp.single i 1 +
          M.dihedralCoeff i j k • Finsupp.single j 1
      else
        M.dihedralCoeff i j k • Finsupp.single i 1 +
          M.dihedralCoeff i j (k + 1) • Finsupp.single j 1 := by
  classical
  induction k with
  | zero => simp [alternatingWord, wordProd_nil]
  | succ k ih =>
    rw [alternatingWord_succ', wordProd_cons, map_mul, mul_apply_eq_comp, ih]
    by_cases hk : Even k
    · have hk' : ¬Even (k + 1) := by simp only [Nat.even_iff] at *; omega
      simp only [hk, hk', ite_true, ite_false, geometricRepresentation_simple]
      rw [add_comm (M.dihedralCoeff i j (k + 1) • _),
        M.geometricReflection_apply_pair j i, M.symmetric j i, M.dihedralCoeff_add_two]
      module
    · have hk' : Even (k + 1) := by simp only [Nat.even_iff] at *; omega
      simp only [hk, hk', ite_true, ite_false, geometricRepresentation_simple]
      rw [M.geometricReflection_apply_pair, M.dihedralCoeff_add_two]

/-- Before the finite braid length, or at any length for an infinite entry, the
alternating word sends the first simple root to a nonnegative combination of the
two simple roots. The strict bound is necessary at finite entries. -/
theorem rankTwo_nonnegative (i j : I) {k : ℕ} (hk : k < M i j ∨ M i j = 0) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
      cs.geometricRepresentation (cs.wordProd (alternatingWord i j k)) (Finsupp.single i 1) =
        a • Finsupp.single i 1 + b • Finsupp.single j 1 := by
  have h₀ := M.dihedralCoeff_nonneg i j (n := k) (by omega)
  have h₁ := M.dihedralCoeff_nonneg i j (n := k + 1) (by omega)
  rw [cs.geometricRepresentation_alternatingWord]
  split_ifs
  · exact ⟨_, _, h₁, h₀, rfl⟩
  · exact ⟨_, _, h₀, h₁, rfl⟩

end CoxeterSystem
