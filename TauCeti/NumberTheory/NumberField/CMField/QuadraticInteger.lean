/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
import TauCeti.NumberTheory.NumberField.IntegralSqrt

/-!
# The trace and norm of an imaginary quadratic half-generator

For `d ≡ 3 (mod 4)`, the integer `(1 + √(-d)) / 2` has trace one and norm `(d + 1) / 4`
over the maximal real subfield of any CM field containing it. The norm identifies the
rational primes where the half-generator can vanish after reduction.

The formulas follow `New.Parameters.star_betaKInE` and `New.Parameters.betaKInE_mul_one_sub`
in `New/Derivatives/Field/PrimeDecomposition.lean` of [grh-lean](https://github.com/lsernau/grh-lean)
at `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open NumberField

namespace NumberField.IsCMField

/-- The integral half-generator of an imaginary quadratic square root with `d ≡ 3 (mod 4)`
has relative trace one and norm `(d + 1) / 4`, even in a larger CM field. -/
theorem exists_halfGenerator_trace_norm {K : Type*} [Field K] [CharZero K]
    [Algebra.IsIntegral ℚ K] [IsCMField K] {d : ℕ} {δ : K} (hd : d % 4 = 3)
    (hδ : δ ^ 2 = -(d : K)) :
    ∃ β : 𝓞 K, (β : K) = (1 + δ) / 2 ∧ β + ringOfIntegersComplexConj K β = 1 ∧
      β * ringOfIntegersComplexConj K β = (((d + 1) / 4 : ℕ) : 𝓞 K) := by
  have hd' : (-(d : ℤ)) % 4 = 1 := by omega
  have hδ' : δ ^ 2 = algebraMap ℤ K (-(d : ℤ)) := by simpa using hδ
  let β : 𝓞 K := ⟨(1 + δ) / 2, TauCeti.isIntegral_one_add_div_two_of_sq_eq hδ' hd'⟩
  let n := (d + 1) / 4
  have hβcoe : (β : K) = (1 + δ) / 2 := rfl
  have hcast : (-(d : ℤ)) / 4 = -(n : ℤ) := by dsimp [n]; omega
  have hβ : (β : K) ^ 2 - (β : K) = -(n : K) := by
    rw [hβcoe]
    simpa only [hcast, map_neg, map_natCast, map_intCast, Int.cast_natCast] using
      TauCeti.sq_one_add_div_two_sub_self hδ' hd'
  -- The conjugate solves the same quadratic. The two roots are distinct since a real root
  -- would have to satisfy `(Re β - 1/2)² = 1/4 - n < 0`.
  have hconj : complexConj K (β : K) = 1 - (β : K) := by
    let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty (K →+* ℂ))
    let z := φ (β : K)
    have hz : z ^ 2 - z = -(n : ℂ) := by
      simpa only [z, map_sub, map_pow, map_neg, map_natCast] using congrArg φ hβ
    have hne : star z ≠ z := by
      intro h
      have him : z.im = 0 := by
        have h' := congrArg Complex.im h
        simp only [Complex.star_def, Complex.conj_im] at h'
        linarith
      have hr := congrArg Complex.re hz
      simp only [pow_two, Complex.sub_re, Complex.mul_re, Complex.neg_re, Complex.natCast_re,
        him, mul_zero, sub_zero] at hr
      have hn : (1 : ℝ) ≤ n := by exact_mod_cast (by dsimp [n]; omega : 1 ≤ n)
      nlinarith [sq_nonneg (z.re - 1 / 2)]
    have hc : (star z) ^ 2 - star z = -(n : ℂ) := by simpa using congrArg star hz
    have hroots : (star z - z) * (star z + z - 1) = 0 := by linear_combination hc - hz
    apply φ.injective
    rw [complexEmbedding_complexConj, map_sub, map_one]
    have hsum := (mul_eq_zero.mp hroots).resolve_left (sub_ne_zero.mpr hne)
    exact eq_sub_of_add_eq (sub_eq_zero.mp hsum)
  refine ⟨β, hβcoe, RingOfIntegers.coe_injective ?_, RingOfIntegers.coe_injective ?_⟩
  · simp [hconj, add_sub_cancel]
  · simp only [map_mul, map_natCast, coe_ringOfIntegersComplexConj, hconj]
    linear_combination -hβ

end NumberField.IsCMField
