/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Euler-product sieve dimension on prime sets

An arithmetic density `g : ℕ → ℝ` on a prime set `P : Set ℕ` has Euler-product sieve dimension `κ`
with constant `K` if for all `2 ≤ w ≤ z`,
`∏_{p ∈ P, p prime, w ≤ p < z} (1 - g(p))⁻¹ ≤ K * (log z / log w) ^ κ`.

Evaluating at `w = z = 2` yields an empty prime product on the left and `K` on the right, so any
satisfying constant `K` automatically obeys `1 ≤ K` (`0 ≤ K`), giving unconditional monotonicity in
the dimension parameter `κ` as well as in `K`.

## Main definitions and results

* `TauCeti.HasProductSieveDimension`: standalone Euler-product sieve dimension predicate on a prime
  set `P : Set ℕ` and density `g : ℕ → ℝ`.
* `TauCeti.hasProductSieveDimension_def`, `TauCeti.HasProductSieveDimension.prod_le`: explicit
  quantifier formula and interval application on `2 ≤ w ≤ z`.
* `TauCeti.hasProductSieveDimension_zero`: zero density has product sieve dimension `κ ≥ 0` with
  any constant `K ≥ 1`.
* `TauCeti.HasProductSieveDimension.mono_const`, `TauCeti.HasProductSieveDimension.mono_dim`:
  monotonicity in the multiplicative constant `K` and in the dimension `κ`.

## References

* K. S. Kedlaya, *Notes on Analytic Number Theory*, Chapter 12, §12.4.
* D. R. Heath-Brown, *Lectures on sieves*, §1 (2002).
-/

public noncomputable section

open Finset Nat Real

namespace TauCeti

/-- Standalone Euler-product sieve dimension predicate for a prime set `P : Set ℕ` and prime
density `g : ℕ → ℝ`: for all `2 ≤ w ≤ z`, the Euler-product ratio over primes `p ∈ P` in `[w, z)`
is at most `K * (log z / log w) ^ κ`. -/
def HasProductSieveDimension (P : Set ℕ) (g : ℕ → ℝ) (κ K : ℝ) : Prop :=
  by
    classical
    exact ∀ w z : ℝ, 2 ≤ w → w ≤ z →
      (∏ p ∈ (Finset.range ⌈z⌉₊).filter (fun p : ℕ ↦ p ∈ P ∧ p.Prime ∧ w ≤ (p : ℝ)),
        (1 - g p)⁻¹) ≤ K * (Real.log z / Real.log w) ^ κ

/-- Explicit formula for `TauCeti.HasProductSieveDimension`. -/
theorem hasProductSieveDimension_def (P : Set ℕ) (g : ℕ → ℝ) (κ K : ℝ) :
    HasProductSieveDimension P g κ K ↔
      by
        classical
        exact ∀ w z : ℝ, 2 ≤ w → w ≤ z →
          (∏ p ∈ (Finset.range ⌈z⌉₊).filter (fun p : ℕ ↦ p ∈ P ∧ p.Prime ∧ w ≤ (p : ℝ)),
            (1 - g p)⁻¹) ≤ K * (Real.log z / Real.log w) ^ κ := Iff.rfl

open Classical in
/-- Applying `HasProductSieveDimension` on an interval `2 ≤ w ≤ z` bounds the prime Euler product
on `[w, z)` by `K * (log z / log w) ^ κ`. -/
theorem HasProductSieveDimension.prod_le {P : Set ℕ} {g : ℕ → ℝ} {κ K w z : ℝ}
    (h : HasProductSieveDimension P g κ K) (hw : 2 ≤ w) (hwz : w ≤ z) :
    (∏ p ∈ (Finset.range ⌈z⌉₊).filter (fun p : ℕ ↦ p ∈ P ∧ p.Prime ∧ w ≤ (p : ℝ)),
      (1 - g p)⁻¹) ≤ K * (Real.log z / Real.log w) ^ κ :=
  h w z hw hwz

/-- Zero density satisfies `HasProductSieveDimension P 0 κ K` whenever `0 ≤ κ` and `1 ≤ K`. -/
theorem hasProductSieveDimension_zero (P : Set ℕ) {κ K : ℝ} (hκ : 0 ≤ κ) (hK : 1 ≤ K) :
    HasProductSieveDimension P 0 κ K := by
  classical
  intro w z hw hwz
  have hlw : 0 < Real.log w := Real.log_pos (by linarith)
  have h1 : 1 ≤ Real.log z / Real.log w :=
    (one_le_div hlw).mpr (Real.log_le_log (by linarith) hwz)
  simpa using one_le_mul_of_one_le_of_one_le hK (one_le_rpow h1 hκ)

/-- Monotonicity of `HasProductSieveDimension` in the multiplicative constant `K`. -/
theorem HasProductSieveDimension.mono_const {P : Set ℕ} {g : ℕ → ℝ} {κ K₁ K₂ : ℝ}
    (h : HasProductSieveDimension P g κ K₁) (hK : K₁ ≤ K₂) :
    HasProductSieveDimension P g κ K₂ := by
  classical
  intro w z hw hwz
  have hlw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlz : 0 ≤ Real.log z := hlw.le.trans (Real.log_le_log (by linarith) hwz)
  exact (h.prod_le hw hwz).trans
    (mul_le_mul_of_nonneg_right hK (rpow_nonneg (div_nonneg hlz hlw.le) _))

/-- Monotonicity of `HasProductSieveDimension` in the dimension parameter `κ`. -/
theorem HasProductSieveDimension.mono_dim {P : Set ℕ} {g : ℕ → ℝ} {κ₁ κ₂ K : ℝ}
    (h : HasProductSieveDimension P g κ₁ K) (hκ : κ₁ ≤ κ₂) :
    HasProductSieveDimension P g κ₂ K := by
  classical
  have hK : 0 ≤ K := by
    have h2 := h.prod_le (w := 2) (z := 2) le_rfl le_rfl
    have hemp : (Finset.range ⌈(2 : ℝ)⌉₊).filter
        (fun p : ℕ ↦ p ∈ P ∧ p.Prime ∧ 2 ≤ (p : ℝ)) = ∅ :=
      filter_eq_empty_iff.mpr fun p hp h' ↦ not_lt_of_ge h'.2.2 (Nat.lt_ceil.mp (mem_range.mp hp))
    rw [hemp, prod_empty, div_self (Real.log_pos one_lt_two).ne', one_rpow, mul_one] at h2
    exact zero_le_one.trans h2
  intro w z hw hwz
  have hlw : 0 < Real.log w := Real.log_pos (by linarith)
  have h1 : 1 ≤ Real.log z / Real.log w :=
    (one_le_div hlw).mpr (Real.log_le_log (by linarith) hwz)
  exact (h.prod_le hw hwz).trans
    (mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le h1 hκ) hK)

end TauCeti
