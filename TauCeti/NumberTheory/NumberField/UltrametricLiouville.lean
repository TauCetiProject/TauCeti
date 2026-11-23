/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import TauCeti.NumberTheory.NumberField.House

import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import TauCeti.Analysis.AbsoluteValue.Nonarchimedean
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Norm
import TauCeti.NumberTheory.Padics.Basic

/-!
# Liouville's inequality at an ultrametric place

Let `K` be a number field of degree `d`, let `c` be a nonzero integer and let `x ∈ K` be nonzero
with `c x` an algebraic integer of house at most `H`. For every ring homomorphism `σ : K → L` into
an ultrametric normed field `L` in which every integer `n` has norm at least `1 / |n|`,

  `1 ≤ H ^ d * ‖σ x‖`.

This rests on the norm `N` of `c x` from `K` to `ℚ`: a nonzero integer with `|N| ≤ H ^ d` that is
a multiple of `c x` in the ring of integers of `K`. The exponent is `d`, not the `d - 1` of the
archimedean inequality (`TauCeti.one_le_house_pow_mul_norm_of_mem_rootSet`), and the bound is
attained by `x = p` in `ℚ_p`.

Every normed field over `ℚ_p`, such as `ℂ_p`, satisfies the hypotheses on `L`: it is ultrametric
(Mathlib's `IsUltrametricDist.of_normedAlgebra`) and integers satisfy the norm bound
(`TauCeti.inv_abs_le_norm_intCast`). The inequality is the lower bound for nonzero algebraic
values that p-adic transcendence arguments set against analytic upper bounds.

## Main results

* `NumberField.one_le_house_pow_mul_norm_of_isUltrametricDist`: Liouville's inequality
  `1 ≤ H ^ d * ‖σ x‖` in an ultrametric normed field.
* `NumberField.one_le_house_pow_mul_norm_of_normedAlgebra`: the same inequality in every normed
  field over `ℚ_p`.

## References

* A. Baker, *Transcendental Number Theory*, Cambridge University Press, 1975, Chapter 1.
-/

public section

open Module

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Liouville's inequality at an ultrametric place.** Let `L` be an ultrametric normed field in
which every integer `n` has norm at least `1 / |n|`. If `c ≠ 0` is an integer and `x ∈ K` is
nonzero with `c x` an algebraic integer of house at most `H`, then `1 ≤ H ^ [K : ℚ] * ‖σ x‖` for
every ring homomorphism `σ : K → L`. -/
theorem one_le_house_pow_mul_norm_of_isUltrametricDist {L : Type*} [NormedField L]
    [IsUltrametricDist L] (hL : ∀ n : ℤ, (|n| : ℝ)⁻¹ ≤ ‖(n : L)‖) {c : ℤ} (hc : c ≠ 0)
    {x : K} (hx : x ≠ 0) (hint : IsIntegral ℤ ((c : K) * x)) {H : ℝ}
    (hH : house ((c : K) * x) ≤ H) (σ : K →+* L) :
    1 ≤ H ^ finrank ℚ K * ‖σ x‖ := by
  obtain ⟨y, hyK⟩ : ∃ y : 𝓞 K, (y : K) = c * x := ⟨⟨_, hint⟩, rfl⟩
  have hy : y ≠ 0 := by
    rw [ne_eq, RingOfIntegers.ext_iff, hyK]
    exact mul_ne_zero (Int.cast_ne_zero.mpr hc) hx
  set N := Algebra.norm ℤ y
  have hN : N ≠ 0 := by simpa [N] using hy
  -- `y = c x` divides its norm `N` in `𝓞 K`, so in `L` the integer `N` is `c σ(x)` times the
  -- image of an algebraic integer, which has norm at most `1`.
  obtain ⟨z, hz⟩ := Algebra.dvd_algebraMap_intNorm_self ℤ (𝓞 K) y
  rw [Algebra.intNorm_eq_norm] at hz
  have hNK : (N : K) = c * x * z := by
    simpa [hyK] using congrArg ((↑) : 𝓞 K → K) hz
  -- The norm of `L` as an absolute value, which is nonarchimedean since `L` is ultrametric.
  have hv : IsNonarchimedean (NormedField.toAbsoluteValue L) := fun a b ↦ by
    simpa only [NormedField.toAbsoluteValue_apply] using
      IsUltrametricDist.isNonarchimedean_norm a b
  have hzσ : IsIntegral ℤ (σ (z : K)) := (RingOfIntegers.isIntegral_coe z).map σ.toIntAlgHom
  have hz1 : ‖σ (z : K)‖ ≤ 1 := by
    simpa only [NormedField.toAbsoluteValue_apply] using hv.apply_le_one_of_isIntegral_int hzσ
  have hNσ : ‖(N : L)‖ ≤ ‖σ x‖ := by
    rw [← map_intCast σ, hNK, map_mul, map_mul, map_intCast, norm_mul, norm_mul]
    calc ‖(c : L)‖ * ‖σ x‖ * ‖σ (z : K)‖ ≤ 1 * ‖σ x‖ * 1 := by
          gcongr
          exact IsUltrametricDist.norm_intCast_le_one L c
      _ = ‖σ x‖ := by ring
  -- In `ℝ`, the integer `N` is the norm of `c x`, which is bounded by its house.
  have hNH : |(N : ℝ)| ≤ H ^ finrank ℚ K :=
    RingOfIntegers.abs_norm_le_pow y fun σ ↦ (norm_embedding_le_house _ σ).trans (hyK ▸ hH)
  have hN0 : (0 : ℝ) < |(N : ℝ)| := by exact_mod_cast abs_pos.mpr hN
  calc (1 : ℝ) = |(N : ℝ)| * |(N : ℝ)|⁻¹ := (mul_inv_cancel₀ hN0.ne').symm
    _ ≤ H ^ finrank ℚ K * ‖σ x‖ :=
      mul_le_mul hNH ((hL N).trans hNσ) (by positivity) (hN0.le.trans hNH)

/-- **Liouville's inequality over `ℚ_p`.** If `c ≠ 0` is an integer and `x ∈ K` is nonzero with
`c x` an algebraic integer of house at most `H`, then `1 ≤ H ^ [K : ℚ] * ‖σ x‖` for every ring
homomorphism `σ` from `K` to a normed field over `ℚ_p`, such as `ℂ_p`. -/
theorem one_le_house_pow_mul_norm_of_normedAlgebra (p : ℕ) [Fact p.Prime] {L : Type*}
    [NormedField L] [NormedAlgebra ℚ_[p] L] {c : ℤ} (hc : c ≠ 0) {x : K} (hx : x ≠ 0)
    (hint : IsIntegral ℤ ((c : K) * x)) {H : ℝ} (hH : house ((c : K) * x) ≤ H) (σ : K →+* L) :
    1 ≤ H ^ finrank ℚ K * ‖σ x‖ :=
  have := IsUltrametricDist.of_normedAlgebra ℚ_[p] (L := L)
  one_le_house_pow_mul_norm_of_isUltrametricDist (TauCeti.inv_abs_le_norm_intCast p) hc hx hint
    hH σ

/-! ### Examples -/

/-- The inequality is sharp: in `ℚ_p`, the integer `x = p` of house `p` has norm `p⁻¹`, so that
`1 ≤ p ^ 1 * ‖p‖` holds with equality. -/
example (p : ℕ) [Fact p.Prime] : (p : ℝ) ^ finrank ℚ ℚ * ‖(p : ℚ_[p])‖ = 1 := by
  rw [finrank_self, pow_one, Padic.norm_p,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)]

end NumberField
