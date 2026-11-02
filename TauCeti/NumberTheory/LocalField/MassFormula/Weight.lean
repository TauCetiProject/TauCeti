/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The weights of Serre's mass formula

Let `K` be a nonarchimedean local field with residue field of cardinality `q`. Serre's mass
formula weights each `L ∈ σ_K(n)` by `q ^ (-c(L))`, where `c(L) = d(L) - n + 1` is the wild
exponent. Serre proves it by integrating root counts over the Eisenstein region, whose volume is
`q ^ (-n) · (1 - q⁻¹)` for `0 < n`: the root count of `L` integrates to
`q ^ (-(d(L) + 1)) · (1 - q⁻¹)`, and since `d(L) + 1 = n + c(L)`, this is the volume of the region
times `q ^ (-c(L))`. This file records that factorization and its consequence: the mass formula
`∑_{L ∈ σ_K(n)} q ^ (-c(L)) = n` is equivalent to
`∑_{L ∈ σ_K(n)} q ^ (-(d(L) + 1)) · (1 - q⁻¹) = n · q ^ (-n) · (1 - q⁻¹)`, the form in which the
integration produces it.

The weighted count is a sum in `ℝ≥0∞`, which needs no convergence hypothesis. Its real-valued
form, a series of positive reals, converges exactly when the `ℝ≥0∞` sum is finite, and then has
the same value. When `σ_K(n)` is infinite, this is the convergence half of Serre's Remark 1°.

## Main results

* `TauCeti.tsum_one_div_natCard_residueField_pow_discriminantExponent_add_one_mul`:
  `∑_{L ∈ σ_K(n)} q ^ (-(d(L) + 1)) · (1 - q⁻¹)` is
  `q ^ (-n) · (1 - q⁻¹) · ∑_{L ∈ σ_K(n)} q ^ (-c(L))`.
* `TauCeti.tsum_one_div_natCard_residueField_pow_wildExponent_eq_iff`: the mass formula is
  equivalent to `∑_{L ∈ σ_K(n)} q ^ (-(d(L) + 1)) · (1 - q⁻¹) = n · q ^ (-n) · (1 - q⁻¹)`.
* `TauCeti.hasSum_one_div_natCard_residueField_pow_wildExponent_iff` and
  `TauCeti.summable_one_div_natCard_residueField_pow_wildExponent_iff`: the real series
  `∑_{L ∈ σ_K(n)} q ^ (-c(L))` converges exactly when the `ℝ≥0∞` sum is finite, with the same sum.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, §3 and
  Remarque 1°.
-/

public section

open ValuativeRel

open scoped ENNReal NNReal

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {n : ℕ}

/-- The common factor `q ^ (-n) · (1 - q⁻¹)` of the weights is nonzero. For `0 < n`, it is the
volume of the Eisenstein region. -/
private theorem one_div_natCard_residueField_pow_mul_one_sub_ne_zero :
    1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ n * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) ≠ 0 := by
  have hq : (1 : ℝ≥0∞) < Nat.card 𝓀[K] := by exact_mod_cast Finite.one_lt_card
  refine mul_ne_zero (ENNReal.div_pos one_ne_zero
    (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))).ne' (tsub_pos_of_lt ?_).ne'
  rwa [one_div, ENNReal.inv_lt_one]

/-- The common factor `q ^ (-n) · (1 - q⁻¹)` of the weights is finite. -/
private theorem one_div_natCard_residueField_pow_mul_one_sub_ne_top :
    1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ n * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) ≠ ∞ := by
  have hq : (1 : ℝ≥0∞) ≤ Nat.card 𝓀[K] := by exact_mod_cast Nat.card_pos
  refine ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top ?_)
    (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  rw [one_div]
  exact ENNReal.inv_le_one.2 (one_le_pow₀ hq)

/-- **The discriminant weights factor through the wild exponents**: the weights
`q ^ (-(d(L) + 1)) · (1 - q⁻¹)` of the members of `σ_K(n)` sum to `q ^ (-n) · (1 - q⁻¹)` times the
weighted count `∑_{L ∈ σ_K(n)} q ^ (-c(L))` of the mass formula. -/
theorem tsum_one_div_natCard_residueField_pow_discriminantExponent_add_one_mul :
    ∑' L : totallyRamifiedOfDegree K n,
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (L.1.discriminantExponent + 1) *
        (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ n * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) *
        ∑' L : totallyRamifiedOfDegree K n, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.wildExponent := by
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun L ↦ ?_
  rw [← IntermediateField.wildExponent_add_eq_discriminantExponent_add_one L.2, pow_add,
    one_div, ENNReal.mul_inv (.inr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))
      (.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))]
  simp only [one_div]
  ring

/-- **The mass formula in discriminant weights**: the weighted count `∑_{L ∈ σ_K(n)} q ^ (-c(L))`
is `n` exactly when the weights `q ^ (-(d(L) + 1)) · (1 - q⁻¹)` sum to `n · q ^ (-n) · (1 - q⁻¹)`,
which for `0 < n` is `n` times the volume of the Eisenstein region for the Haar measure normalized
on the integer box. By `TauCeti.tsum_lintegral_rootCount_eq_of_normalized`, the right side holds
once each root-count integral over the Eisenstein region is evaluated as
`q ^ (-(d(L) + 1)) · (1 - q⁻¹)`. -/
theorem tsum_one_div_natCard_residueField_pow_wildExponent_eq_iff :
    ∑' L : totallyRamifiedOfDegree K n, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.wildExponent = n ↔
      ∑' L : totallyRamifiedOfDegree K n,
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (L.1.discriminantExponent + 1) *
          (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) =
        n * (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ n * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))) := by
  rw [tsum_one_div_natCard_residueField_pow_discriminantExponent_add_one_mul, mul_comm (n : ℝ≥0∞),
    ENNReal.mul_right_inj one_div_natCard_residueField_pow_mul_one_sub_ne_zero
      one_div_natCard_residueField_pow_mul_one_sub_ne_top]

/-- The weight `q ^ (-k)` in `ℝ≥0∞` is the cast of the weight in `ℝ≥0`. -/
private theorem coe_one_div_natCard_residueField_pow (k : ℕ) :
    ((1 / (Nat.card 𝓀[K] : ℝ≥0) ^ k : ℝ≥0) : ℝ≥0∞) = 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k := by
  rw [ENNReal.coe_div (pow_ne_zero _ (Nat.cast_ne_zero.2 Nat.card_pos.ne'))]
  push_cast
  rfl

/-- **The real-valued form of the weighted count**: the real series
`∑_{L ∈ σ_K(n)} q ^ (-c(L))` sums to `s` exactly when the `ℝ≥0∞` sum is `s`. At `s = n`, this
relates the mass formula to its real-valued restatement. -/
theorem hasSum_one_div_natCard_residueField_pow_wildExponent_iff {s : ℝ≥0} :
    HasSum (fun L : totallyRamifiedOfDegree K n ↦
      1 / (Nat.card 𝓀[K] : ℝ) ^ L.1.wildExponent) s ↔
      ∑' L : totallyRamifiedOfDegree K n, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.wildExponent = s := by
  simp only [← coe_one_div_natCard_residueField_pow, ← ENNReal.summable.hasSum_iff,
    ENNReal.hasSum_coe, ← NNReal.hasSum_coe, NNReal.coe_div, NNReal.coe_one, NNReal.coe_pow,
    NNReal.coe_natCast]

/-- **The real-valued weighted count converges exactly when the `ℝ≥0∞` sum is finite.** With the
mass formula, this makes the real series `∑_{L ∈ σ_K(n)} q ^ (-c(L))` converge, also when `σ_K(n)`
is infinite. -/
theorem summable_one_div_natCard_residueField_pow_wildExponent_iff :
    Summable (fun L : totallyRamifiedOfDegree K n ↦
      1 / (Nat.card 𝓀[K] : ℝ) ^ L.1.wildExponent) ↔
      ∑' L : totallyRamifiedOfDegree K n, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.wildExponent ≠ ∞ := by
  simp only [← coe_one_div_natCard_residueField_pow, ENNReal.tsum_coe_ne_top_iff_summable_coe,
    NNReal.coe_div, NNReal.coe_one, NNReal.coe_pow, NNReal.coe_natCast]

end TauCeti
