/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import TauCeti.NumberTheory.HilbertSymbol.Basic
public import TauCeti.NumberTheory.SumTwoSquares
import Mathlib.Tactic.NormNum.Prime

/-!
# The conic-solvability sign

`TauCeti.conicSymbol R r s` is the sign `+1` when the conic `r x² + s y² = 1` has a point with
coordinates in `R`, and `-1` otherwise. Unlike `TauCeti.hilbertSymbol`, which is defined on pairs
of units of a field, it is defined for all coefficients, including zero ones, so it is a total
function on `R × R`.

On units of a field in which `2 ≠ 0`, the two signs agree (`TauCeti.conicSymbol_eq_hilbertSymbol`).
The comparison rests on the norm criterion `TauCeti.conicSymbol_eq_one_iff_exists_eq_sq_sub_mul_sq`:
for `s ≠ 0`, the conic `r x² + s y² = 1` has a point exactly when `s = x² - r y²` is solvable.
The hypothesis `2 ≠ 0` cannot be dropped: over `𝔽₂(t)` the conic `x² + t y² = 1` has the point
`(1, 0)`, while `x² - y² = (x + y)²` never equals `t`.

Over `ℝ` the conic sign is `-1` exactly when both coefficients are nonpositive
(`TauCeti.conicSymbol_real_eq_neg_one_iff`). On nonzero coefficients this is the familiar
negative-quadrant criterion for the real Hilbert symbol; the criterion also covers zero
coefficients, so pairs such as `(0, -1)`, `(-1, 0)` and `(0, 0)` have sign `-1` as well.

The conic sign is not multiplicative over an arbitrary field. Over `ℚ`, the conic
`r x² - y² = 1` has no point when some prime `p ≡ 3 [MOD 4]` has odd valuation in `r`
(`TauCeti.conicSymbol_rat_neg_one_eq_neg_one`), since `r x² = 1 + y²` would be a sum of two
rational squares (`Rat.even_padicValRat_sq_add_sq`). Hence the signs at `(3, -1)`, `(7, -1)` and
`(21, -1)` are all `-1`, and `TauCeti.conicSymbol_rat_mul_ne_mul` records that the sign at
`(3 · 7, -1)` is not the product of those at `(3, -1)` and `(7, -1)`. Bimultiplicativity is a
property of the Hilbert symbol of a local field, not of the conic sign over an arbitrary field.

## Main results

* `TauCeti.conicSymbol_eq_one_iff`, `TauCeti.conicSymbol_eq_neg_one_iff`: the defining property.
* `TauCeti.conicSymbol_comm`: symmetry in the two coefficients.
* `TauCeti.conicSymbol_eq_one_iff_exists_eq_sq_sub_mul_sq`: the norm criterion.
* `TauCeti.conicSymbol_eq_hilbertSymbol`: agreement with the norm-equation Hilbert symbol on units.
* `TauCeti.conicSymbol_real_eq_neg_one_iff`: the real criterion on all real coefficients.
* `TauCeti.conicSymbol_rat_mul_ne_mul`: failure of multiplicativity over `ℚ`.

## References

* C. A. Weibel, *The K-book*, Chapter III, Examples 6.2.2 and 6.2.5.
* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1, Proposition 1.
-/

public section
noncomputable section

namespace TauCeti

section CommRing

variable (R : Type*) [CommRing R]

open Classical in
/-- The conic-solvability sign: `1` when the conic `r x² + s y² = 1` has a point with coordinates
in `R`, and `-1` otherwise. Zero coefficients are allowed. -/
def conicSymbol (r s : R) : ℤˣ :=
  if ∃ x y : R, r * x ^ 2 + s * y ^ 2 = 1 then 1 else -1

open Classical in
/-- The defining case split of the conic sign. -/
theorem conicSymbol_def (r s : R) :
    conicSymbol R r s = if ∃ x y : R, r * x ^ 2 + s * y ^ 2 = 1 then 1 else -1 :=
  (rfl)

variable {R}

/-- The conic sign is `1` exactly when the conic has a point. -/
theorem conicSymbol_eq_one_iff (r s : R) :
    conicSymbol R r s = 1 ↔ ∃ x y : R, r * x ^ 2 + s * y ^ 2 = 1 := by
  classical
  simp [conicSymbol_def]

/-- The conic sign is `-1` exactly when the conic has no point. -/
theorem conicSymbol_eq_neg_one_iff (r s : R) :
    conicSymbol R r s = -1 ↔ ¬∃ x y : R, r * x ^ 2 + s * y ^ 2 = 1 := by
  classical
  simp [conicSymbol_def]

/-- Two conic signs agree exactly when one conic has a point if and only if the other does. -/
theorem conicSymbol_eq_conicSymbol_iff {r s r' s' : R} :
    conicSymbol R r s = conicSymbol R r' s' ↔
      ((∃ x y : R, r * x ^ 2 + s * y ^ 2 = 1) ↔ ∃ x y : R, r' * x ^ 2 + s' * y ^ 2 = 1) := by
  classical
  simp only [conicSymbol_def]
  split_ifs with h h' h' <;> simp_all [Units.ext_iff]

/-- The conic sign is symmetric in its two coefficients. -/
theorem conicSymbol_comm (r s : R) : conicSymbol R r s = conicSymbol R s r :=
  conicSymbol_eq_conicSymbol_iff.mpr
    ⟨fun ⟨x, y, h⟩ => ⟨y, x, by rw [← h, add_comm]⟩,
      fun ⟨x, y, h⟩ => ⟨y, x, by rw [← h, add_comm]⟩⟩

/-- The conic `x² + s y² = 1` has the point `(1, 0)`. -/
@[simp] theorem conicSymbol_one_left (s : R) : conicSymbol R 1 s = 1 :=
  (conicSymbol_eq_one_iff _ _).mpr ⟨1, 0, by ring⟩

/-- The conic `r x² + y² = 1` has the point `(0, 1)`. -/
@[simp] theorem conicSymbol_one_right (r : R) : conicSymbol R r 1 = 1 := by
  rw [conicSymbol_comm, conicSymbol_one_left]

/-- The Steinberg value: the conic `r x² + (1 - r) y² = 1` has the point `(1, 1)`, also when `r`
or `1 - r` is zero. -/
@[simp] theorem conicSymbol_one_sub (r : R) : conicSymbol R r (1 - r) = 1 :=
  (conicSymbol_eq_one_iff _ _).mpr ⟨1, 1, by ring⟩

end CommRing

section Field

variable {F : Type*} [Field F]

/-- **The norm criterion.** In a field with `2 ≠ 0` and for `s ≠ 0`, the conic
`r x² + s y² = 1` has a point exactly when `s` is a norm `x² - r y²` from `F[√r]`. -/
theorem conicSymbol_eq_one_iff_exists_eq_sq_sub_mul_sq (h2 : (2 : F) ≠ 0) (r : F) {s : F}
    (hs : s ≠ 0) : conicSymbol F r s = 1 ↔ ∃ x y : F, s = x ^ 2 - r * y ^ 2 := by
  rw [conicSymbol_eq_one_iff]
  constructor
  · rintro ⟨u, v, h⟩
    by_cases hv : v = 0
    · -- `r u² = 1`, so `x² - r y² = (x - y / u) (x + y / u)` is split.
      subst hv
      refine ⟨(1 + s) / 2, (s - 1) * u / 2, ?_⟩
      field_simp
      linear_combination (s - 1) ^ 2 * h
    · refine ⟨v⁻¹, u / v, ?_⟩
      field_simp
      linear_combination h
  · rintro ⟨x, y, h⟩
    by_cases hx : x = 0
    · -- `s = -r y²` with `r, y ≠ 0`, so the conic is `r (u² - (y v)²) = 1`, again split.
      subst hx
      have hr : r ≠ 0 := by rintro rfl; simp [hs] at h
      have hy : y ≠ 0 := by rintro rfl; simp [hs] at h
      refine ⟨(r⁻¹ + 1) / 2, (r⁻¹ - 1) / 2 / y, ?_⟩
      rw [h]
      field_simp
      ring
    · refine ⟨y / x, x⁻¹, ?_⟩
      rw [h]
      field_simp
      ring

/-- On units of a field with `2 ≠ 0`, the conic sign is the norm-equation Hilbert symbol. -/
theorem conicSymbol_eq_hilbertSymbol (h2 : (2 : F) ≠ 0) (r s : Fˣ) :
    conicSymbol F (r : F) (s : F) = hilbertSymbol r s := by
  have key : conicSymbol F (r : F) (s : F) = 1 ↔ hilbertSymbol r s = 1 := by
    rw [conicSymbol_eq_one_iff_exists_eq_sq_sub_mul_sq h2 _ s.ne_zero, hilbertSymbol_eq_one_iff]
  rcases Int.units_eq_one_or (hilbertSymbol r s) with h | h
  · rw [h, key.mpr h]
  · rw [h, ← Int.units_ne_iff_eq_neg, Ne, key, h]
    decide

end Field

/-- **The real criterion.** Over `ℝ`, the conic `r x² + s y² = 1` has no point exactly when both
coefficients are nonpositive. -/
theorem conicSymbol_real_eq_neg_one_iff (r s : ℝ) :
    conicSymbol ℝ r s = -1 ↔ r ≤ 0 ∧ s ≤ 0 := by
  rw [conicSymbol_eq_neg_one_iff]
  constructor
  · intro h
    by_contra hrs
    rcases not_and_or.mp hrs with hr | hs
    · -- `r > 0`, and `(√r⁻¹, 0)` is a point.
      exact h ⟨√r⁻¹, 0, by
        rw [Real.sq_sqrt (inv_nonneg.mpr (not_le.mp hr).le), mul_inv_cancel₀ (by linarith)]
        ring⟩
    · -- `s > 0`, and `(0, √s⁻¹)` is a point.
      exact h ⟨0, √s⁻¹, by
        rw [Real.sq_sqrt (inv_nonneg.mpr (not_le.mp hs).le), mul_inv_cancel₀ (by linarith)]
        ring⟩
  · rintro ⟨hr, hs⟩ ⟨x, y, h⟩
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hr (sq_nonneg x),
      mul_nonpos_of_nonpos_of_nonneg hs (sq_nonneg y)]

/-- Over `ℚ`, the conic `r x² - y² = 1` has no point when some prime `p ≡ 3 [MOD 4]` has odd
valuation in `r`. -/
theorem conicSymbol_rat_neg_one_eq_neg_one {r : ℚ} {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3)
    (hr : Odd (padicValRat p r)) : conicSymbol ℚ r (-1) = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [conicSymbol_eq_neg_one_iff]
  rintro ⟨x, y, h⟩
  -- `r x² = 1² + y²` is a sum of two squares, so its valuation at `p` is even.
  have hsum : r * x ^ 2 = 1 ^ 2 + y ^ 2 := by linear_combination h
  have hne : r * x ^ 2 ≠ 0 := by rw [hsum]; positivity
  have heven := Rat.even_padicValRat_sq_add_sq 1 y hp hp4
  rw [← hsum, padicValRat.mul (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne),
    padicValRat.pow] at heven
  exact Int.not_even_iff_odd.mpr hr <| by simpa [Int.even_add, Int.even_mul] using heven

/-- The conic sign over `ℚ` is not multiplicative in its first coefficient: its value at
`(3 · 7, -1)` is not the product of its values at `(3, -1)` and `(7, -1)`. All three values are
`-1`, by `TauCeti.conicSymbol_rat_neg_one_eq_neg_one`. -/
theorem conicSymbol_rat_mul_ne_mul :
    conicSymbol ℚ (3 * 7) (-1) ≠ conicSymbol ℚ 3 (-1) * conicSymbol ℚ 7 (-1) := by
  have hv3 : padicValRat 3 3 = 1 := by exact_mod_cast padicValRat.self (p := 3) (by norm_num)
  have hv7 : padicValRat 7 7 = 1 := by exact_mod_cast padicValRat.self (p := 7) (by norm_num)
  have hv37 : padicValRat 3 7 = 0 := by
    rw [show (7 : ℚ) = ((7 : ℤ) : ℚ) by norm_num, padicValRat.of_int,
      padicValInt.eq_zero_of_not_dvd (by norm_num), Nat.cast_zero]
  have h3 : conicSymbol ℚ 3 (-1) = -1 :=
    conicSymbol_rat_neg_one_eq_neg_one Nat.prime_three rfl (by rw [hv3]; exact odd_one)
  have h7 : conicSymbol ℚ 7 (-1) = -1 :=
    conicSymbol_rat_neg_one_eq_neg_one (p := 7) (by norm_num) rfl (by rw [hv7]; exact odd_one)
  have h21 : conicSymbol ℚ (3 * 7) (-1) = -1 :=
    conicSymbol_rat_neg_one_eq_neg_one Nat.prime_three rfl <| by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      rw [padicValRat.mul (by norm_num) (by norm_num), hv3, hv37]
      exact odd_one
  rw [h3, h7, h21]
  decide

end TauCeti
