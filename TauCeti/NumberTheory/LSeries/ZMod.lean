/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import TauCeti.Analysis.Fourier.ZMod

/-!
# Values at positive integers of the series of a periodic function

For a function `Φ` on `ZMod N` and a natural number `k ≥ 2`, the absolutely convergent series
`∑_{n ∈ ℤ} Φ(n) n⁻ᵏ` (whose term at `n = 0` is `0`) has the value
`-(2πi)ᵏ / (k! N) ∑_{j mod N} 𝓕Φ(j) Bₖ(j / N)`,
where `𝓕Φ` is the discrete Fourier transform of `Φ`, `Bₖ` is the `k`-th Bernoulli polynomial and
`j` is read as its representative in `[0, N)`. So up to the factor `(2πi)ᵏ` the value is a
combination of the values of `𝓕Φ` with rational coefficients depending only on `N` and `k`.

These sums are the constant terms of the Eisenstein series of level `N` at the cusps. The formula
shows that they have bounded denominators: if `Φ` takes values in a subring `R ⊆ ℂ` containing the
`N`-th roots of unity, then a positive integer `D` depending only on `N` and `k` makes
`D (2πi)⁻ᵏ ∑_{n ∈ ℤ} Φ(n) n⁻ᵏ` an element of `R`.

The proof expands `Φ` by Fourier inversion into the additive characters `n ↦ e^{2πi j n / N}`
and sums each against `n⁻ᵏ` by the Fourier series of the periodized Bernoulli polynomial,
Mathlib's `hasSum_one_div_pow_mul_fourier_mul_bernoulliFun`, as in the special case of Dirichlet
characters, `DirichletCharacter.gaussSum_mul_tsum_inv_pow_eq_generalizedBernoulli`.

## Main results

* `ZMod.hasSum_mul_zpow_neg_bernoulli`: the value of `∑_{n ∈ ℤ} Φ(n) n⁻ᵏ`.
* `ZMod.exists_natCast_mul_tsum_div_mem`: the bounded denominators of these values.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 4.
-/

public section

open Complex
open scoped Real

namespace ZMod

variable {N : ℕ} [NeZero N]

/-- **The series of a periodic function against `n⁻ᵏ`.** For `Φ : ZMod N → ℂ` and `k ≥ 2`,
`∑_{n ∈ ℤ} Φ(n) n⁻ᵏ = -(2πi)ᵏ / (k! N) ∑_{j mod N} 𝓕Φ(j) Bₖ(j / N)`, where `𝓕Φ` is the discrete
Fourier transform, `Bₖ` the `k`-th Bernoulli polynomial, and `j` runs over the representatives
`0 ≤ j < N`. -/
theorem hasSum_mul_zpow_neg_bernoulli (Φ : ZMod N → ℂ) {k : ℕ} (hk : 2 ≤ k) :
    HasSum (fun n : ℤ ↦ Φ n * (n : ℂ) ^ (-(k : ℤ)))
      (-(2 * π * I) ^ k / (k.factorial * N) *
        ∑ j : ZMod N, 𝓕 Φ j * (((Polynomial.bernoulli k).eval ((j.val : ℚ) / N) : ℚ) : ℂ)) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  -- Fourier inversion expands `Φ` into the additive characters
  have hinv (n : ℤ) : Φ n = (N : ℂ)⁻¹ * ∑ j : ZMod N, 𝓕 Φ j * stdAddChar (j * (n : ZMod N)) := by
    conv_lhs => rw [← dft.symm_apply_apply Φ]
    rw [invDFT_apply, smul_eq_mul]
    simp only [smul_eq_mul, mul_comm (stdAddChar _)]
  -- the additive character at `j n` is the Fourier mode `n` at the point `j / N`
  have hfourier (j : ZMod N) (n : ℤ) :
      fourier n ((j.val / (N : ℝ) : ℝ) : UnitAddCircle) = stdAddChar (j * (n : ZMod N)) := by
    rw [fourier_coe_apply, stdAddChar_apply]
    have h := toCircle_intCast (N := N) (n * j.val)
    rw [Int.cast_mul, Int.cast_natCast, natCast_zmod_val, mul_comm] at h
    rw [h]
    push_cast
    congr 1
    ring
  have hx (j : ZMod N) : (j.val / (N : ℝ) : ℝ) ∈ Set.Icc 0 1 :=
    ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      (div_le_one (Nat.cast_pos.mpr (NeZero.pos N))).mpr (by exact_mod_cast (val_lt j).le)⟩
  -- the Bernoulli function at a rational point is the rational value of the polynomial
  have hB (j : ZMod N) : (bernoulliFun k (j.val / (N : ℝ)) : ℂ) =
      (((Polynomial.bernoulli k).eval ((j.val : ℚ) / N) : ℚ) : ℂ) := by
    have hcast (x : ℚ) :
        algebraMap ℚ ℂ ((Polynomial.bernoulli k).eval x) = bernoulliFun k (x : ℝ) := by
      simp only [bernoulliFun, Polynomial.eval_map, ← map_ratCast (algebraMap ℚ ℝ),
        Polynomial.eval₂_at_apply]
      norm_cast
    rw [← eq_ratCast (algebraMap ℚ ℂ), hcast]
    push_cast
    rfl
  have hs (j : ZMod N) := (hasSum_one_div_pow_mul_fourier_mul_bernoulliFun hk (hx j)).mul_left
    ((N : ℂ)⁻¹ * 𝓕 Φ j)
  convert hasSum_sum (s := Finset.univ) fun j _ ↦ hs j using 1
  · ext n
    rw [hinv n, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hfourier, zpow_neg, zpow_natCast, one_div]
    ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hB]
    field_simp

/-- **Bounded denominators.** If a subring `R ⊆ ℂ` contains the `N`-th roots of unity, then for
`k ≥ 2` there is a positive integer `D`, depending only on `N` and `k`, such that
`D (2πi)⁻ᵏ ∑_{n ∈ ℤ} Φ(n) n⁻ᵏ ∈ R` for every `R`-valued function `Φ` on `ZMod N`. -/
theorem exists_natCast_mul_tsum_div_mem {R : Subring ℂ} (hR : ∀ ζ : ℂ, ζ ^ N = 1 → ζ ∈ R)
    {k : ℕ} (hk : 2 ≤ k) :
    ∃ D : ℕ, D ≠ 0 ∧ ∀ Φ : ZMod N → ℂ, (∀ j, Φ j ∈ R) →
      D * (∑' n : ℤ, Φ n * (n : ℂ) ^ (-(k : ℤ))) / (2 * π * I) ^ k ∈ R := by
  -- the rational coefficients of the values of `𝓕Φ`, and their common denominator
  set ρ : ZMod N → ℚ := fun j ↦
    -(Polynomial.bernoulli k).eval ((j.val : ℚ) / N) / (k.factorial * N)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) ρ
  refine ⟨(b : ℤ).natAbs, Int.natAbs_ne_zero.mpr (nonZeroDivisors.coe_ne_zero b),
    fun Φ hΦ ↦ ?_⟩
  rw [(hasSum_mul_zpow_neg_bernoulli Φ hk).tsum_eq, Finset.mul_sum, Finset.mul_sum,
    Finset.sum_div]
  refine R.sum_mem fun j _ ↦ ?_
  obtain ⟨m, hm⟩ : ∃ m : ℤ, ((b : ℤ).natAbs : ℚ) * ρ j = m := by
    obtain ⟨m, hm⟩ := hb j
    refine ⟨(b : ℤ).sign * m, ?_⟩
    rw [Int.cast_mul, ← eq_intCast (algebraMap ℤ ℚ) m, hm, zsmul_eq_mul, ← mul_assoc,
      ← Int.cast_mul, Int.sign_mul_self, Int.cast_natCast]
  convert R.mul_mem (dft_apply_mem hR hΦ j) (intCast_mem R m) using 1
  rw [← Rat.cast_intCast (α := ℂ), ← hm]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hπ : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  simp only [ρ]
  push_cast
  field_simp

end ZMod
