/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Valuation.Basic
import TauCeti.RingTheory.Polynomial.Gauss.Valuation.Basic

/-!
# Valuations of polynomial expressions

A valuation takes value at most `1` on every polynomial expression in an element of value at most
`1`, provided the images of the coefficients also have value at most `1`.

Weighted coefficient bounds for products, powers, evaluation, and compositions of polynomials live
in `TauCeti/RingTheory/Valuation/Polynomial/Weighted.lean`. The constant-term estimate for
valuation subrings (`TauCeti.valuation_aeval_eq_one`) lives in
`TauCeti/RingTheory/Valuation/Polynomial/LocalSubring.lean`.

Over a valued field, a nonzero polynomial can be rescaled so that its coefficients have value at
most `1`, one coefficient is `1`, and all coefficients of higher degree have value below `1`. This
normalizes the polynomial relations used to bound the fibres of the valuation spectrum of a finite
algebra over a field.

## Main results

* `Valuation.aeval_le_one`: `v (Polynomial.aeval t p) ≤ 1` whenever `v t ≤ 1` and the images of
  the coefficients have value at most `1`.
* `Valuation.exists_C_mul_coeff_eq_one`: a nonzero polynomial over a valued field has a scalar
  multiple with all coefficients of value at most `1`, a coefficient equal to `1`, and all
  coefficients of higher degree of value below `1`.

## Uses

The place-at-infinity argument for isogenies in
`AlgebraicGeometry/EllipticCurve/Isogeny/InfinityPlace/Basic.lean` needs `Valuation.aeval_le_one`
to see that a pulled-back affine function of a Weierstrass curve — a polynomial in the pulled-back
coordinates — stays in the valuation ring at infinity.
-/

public section

namespace Valuation

variable {R L Γ₀ : Type*} [CommSemiring R] [Ring L] [Algebra R L]
  [LinearOrderedCommMonoidWithZero Γ₀]

/-- **A valuation integral on the coefficients is at most `1` on polynomial expressions in an
element of the integers.** -/
theorem aeval_le_one (v : Valuation L Γ₀) (hR : ∀ r : R, v (algebraMap R L r) ≤ 1)
    {t : L} (ht : v t ≤ 1) (p : Polynomial R) : v (Polynomial.aeval t p) ≤ 1 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  exact (Polynomial.valuation_eval_le_gaussValuation v 1 _ ht).trans <|
    (Polynomial.gaussValuation_le_iff v 1).mpr fun i ↦ by
      rw [Polynomial.coeff_map, one_pow, mul_one]
      exact hR (p.coeff i)

end Valuation

namespace Valuation

open Polynomial

section Field

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

/-- **Normalizing a polynomial.** A nonzero polynomial over a valued field can be rescaled so that
its coefficients have value at most `1`, its coefficient in some degree `D` is `1`, and its
coefficients of degree above `D` have value below `1`: divide by the coefficient of largest degree
among those of maximal value. -/
theorem exists_C_mul_coeff_eq_one (v : Valuation K Γ₀) {P : K[X]} (hP : P ≠ 0) :
    ∃ c : K, ∃ D : ℕ, (C c * P).coeff D = 1 ∧ (∀ n, v ((C c * P).coeff n) ≤ 1) ∧
      ∀ n, D < n → v ((C c * P).coeff n) < 1 := by
  classical
  set f : ℕ → Γ₀ := fun n ↦ v (P.coeff n)
  obtain ⟨n₀, -, hn₀⟩ := Finset.exists_max_image (Finset.range (P.natDegree + 1)) f
    ⟨0, by simp⟩
  have hmax₀ : ∀ k, f k ≤ f n₀ := fun k ↦ by
    by_cases hk : k ≤ P.natDegree
    · exact hn₀ k (by simpa [Nat.lt_succ_iff] using hk)
    · simp [f, coeff_eq_zero_of_natDegree_lt (not_le.mp hk)]
  -- the largest degree at which the coefficient has maximal value
  set S := (Finset.range (P.natDegree + 1)).filter fun n ↦ ∀ k, f k ≤ f n
  have hpos : ∀ n, (∀ k, f k ≤ f n) → f n ≠ 0 := fun n hn h ↦ by
    have := hn P.natDegree
    rw [h, nonpos_iff_eq_zero] at this
    exact leadingCoeff_ne_zero.mpr hP ((map_eq_zero _).mp this)
  have hmemS : ∀ n, (∀ k, f k ≤ f n) → n ∈ S := fun n hn ↦ by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ?_), hn⟩
    exact le_natDegree_of_ne_zero fun h ↦ hpos n hn (by simp [f, h])
  have hS : S.Nonempty := ⟨n₀, hmemS n₀ hmax₀⟩
  set D := S.max' hS
  have hD : ∀ k, f k ≤ f D := (Finset.mem_filter.mp (S.max'_mem hS)).2
  have hcD : P.coeff D ≠ 0 := fun h ↦ hpos D hD (by simp [f, h])
  have hfD : 0 < f D := pos_iff_ne_zero.mpr (hpos D hD)
  refine ⟨(P.coeff D)⁻¹, D, by simp [hcD], fun n ↦ ?_, fun n hn ↦ ?_⟩
  · rw [coeff_C_mul, map_mul, map_inv₀]
    exact inv_mul_le_one_of_le₀ (hD n) hfD.le
  · rw [coeff_C_mul, map_mul, map_inv₀]
    refine (inv_mul_lt_one₀ hfD).mpr (lt_of_not_ge fun h ↦ ?_)
    exact (S.le_max' n (hmemS n fun k ↦ (hD k).trans h)).not_gt hn

end Field

end Valuation

end
