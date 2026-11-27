/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.Remainder
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.Floor
import TauCeti.Analysis.SpecialFunctions.Integrals.StretchedExponential
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.SummatoryTail
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Basic

/-!
# Transfer from twisted prime sums to first Riesz remainders

The corrected first Riesz sum for a nonprincipal character is minus the length times
an integral of the twisted Chebyshev sum against `t⁻²`. Consequently a summatory
term `B t^β` contributes `−B y^β / (1 − β)` to the Riesz remainder. The mixed
exponential error transfers with at most one extra power of the logarithm of the
conductor. For the unsmoothed estimate and its exceptional term, see Iwaniec–Kowalski,
*Analytic Number Theory*, Theorem 5.27. The nonprincipal remainder normalization is that
of Levent Alpöge's `Deduction.Gchi`
(<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open ArithmeticFunction Complex Filter MeasureTheory Set TauCeti
open scoped Topology

namespace DirichletCharacter

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- The first Riesz remainder of a nonprincipal character is `−y` times the tail of
its twisted Chebyshev sum weighted by `t⁻²`, whenever that weighted sum is integrable. -/
theorem rieszSum_add_mul_logDeriv_eq_neg_mul_integral (hχ : χ ≠ 1)
    (hint : IntegrableOn (fun t : ℝ ↦ (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ n * Λ n) / (t : ℂ) ^ 2)
      (Ioi 1)) {y : ℝ} (hy : 1 ≤ y) :
    rieszSum (fun n ↦ χ n * Λ n) y + y * logDeriv χ.LFunction 1 =
      -(y : ℂ) * ∫ t in Ioi y, (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ n * Λ n) / (t : ℂ) ^ 2 := by
  have hs : ∀ᶠ σ : ℝ in 𝓝[>] 1, 1 < σ := self_mem_nhdsWithin
  have ha : ∀ᶠ σ : ℝ in 𝓝[>] 1, LSeriesSummable (fun n ↦ χ n * Λ n) (σ : ℂ) :=
    hs.mono fun σ hσ ↦ χ.LSeriesSummable_twist_vonMangoldt (by simpa using hσ)
  have hc : ContinuousAt (logDeriv χ.LFunction) 1 :=
    (χ.differentiable_LFunction hχ).deriv.continuous.continuousAt.div
      (χ.differentiable_LFunction hχ).continuous.continuousAt (χ.LFunction_apply_one_ne_zero hχ)
  have hlim : Tendsto (fun σ : ℝ ↦ LSeries (fun n ↦ χ n * Λ n) (σ : ℂ))
      (𝓝[>] 1) (𝓝 (-logDeriv χ.LFunction 1)) := by
    have ht : Tendsto (fun σ : ℝ ↦ -logDeriv χ.LFunction (σ : ℂ))
        (𝓝[>] 1) (𝓝 (-logDeriv χ.LFunction 1)) := by
      exact ((hc.neg.tendsto.comp (continuous_ofReal.tendsto 1)).mono_left nhdsWithin_le_nhds)
    refine ht.congr' (hs.mono fun σ hσ ↦ ?_)
    have hz : 1 < (σ : ℂ).re := by simpa using hσ
    simp only [χ.logDeriv_LFunction_eq_neg_LSeries hz, neg_neg]
    rfl
  have htail := rieszSum_div_sub_log_sub_eq_neg_integral_of_tendsto (A := 0) ha
    (by simpa using hint) (by simpa using hlim) hy
  simp only [zero_mul, sub_zero, sub_neg_eq_add] at htail
  have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  calc
    _ = (rieszSum (fun n ↦ χ n * Λ n) y / (y : ℂ) + logDeriv χ.LFunction 1) * y := by
      rw [add_mul, div_mul_cancel₀ _ hy0, mul_comm (logDeriv χ.LFunction 1)]
    _ = _ := by rw [← mul_comm (y : ℂ), htail, mul_neg, neg_mul]

/-- A mixed-exponential error in the twisted Chebyshev sum transfers to the first Riesz
remainder, with one extra factor `1 + ℓ`. A term `B t^β` with `β < 1` contributes exactly
`−B y^β / (1 − β)`. In particular `B = −1/β` yields the positive exceptional-zero term,
and `B = 0` gives the transfer without an exceptional term. -/
theorem norm_rieszSum_add_mul_logDeriv_add_power_le (hχ : χ ≠ 1) {c ℓ C β y : ℝ}
    (hc : 0 < c) (hℓ : 0 ≤ ℓ) (hβ : β < 1) (hy : 1 ≤ y) (B : ℂ)
    (hψ : ∀ t > 1, ‖(∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ n * Λ n) - B * (t ^ β : ℝ)‖ ≤
      C * t * Real.exp (-(c * (Real.log t / (√(Real.log t) + ℓ))))) :
    ‖rieszSum (fun n ↦ χ n * Λ n) y + y * logDeriv χ.LFunction 1 +
      B * (y ^ β : ℝ) / (1 - (β : ℂ))‖ ≤
      C * y * (1 + ℓ) * (32 / c ^ 2 + 4 / c) *
        Real.exp (-(c / 2) * (Real.log y / (√(Real.log y) + ℓ))) := by
  let ψ (t : ℝ) : ℂ := ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ n * Λ n
  let f (t : ℝ) := (ψ t - B * (t ^ β : ℝ)) / (t : ℂ)
  let k (t : ℝ) := B * (t ^ (β - 2) : ℝ)
  have hψm : Measurable ψ :=
    (measurable_of_countable (fun m : ℕ ↦ ∑ n ∈ Finset.Icc 1 m, χ n * Λ n)).comp
      Nat.measurable_floor
  have hf : StronglyMeasurable f := by
    exact ((hψm.sub (by fun_prop)).div continuous_ofReal.measurable).stronglyMeasurable
  have hb (t : ℝ) (ht : 1 < t) : ‖f t‖ ≤
      C * Real.exp (-(c * (Real.log t / (√(Real.log t) + ℓ)))) := by
    have ht₀ := zero_lt_one.trans ht
    dsimp only [f]
    rw [norm_div, norm_real, Real.norm_of_nonneg ht₀.le, div_le_iff₀ ht₀]
    simpa only [mul_right_comm] using hψ t ht
  have hk {a : ℝ} (ha : 0 < a) : IntegrableOn k (Ioi a) :=
    ((integrableOn_Ioi_rpow_of_lt (by linarith : β - 2 < -1) ha).ofReal).const_mul B
  have he (t : ℝ) (ht : 0 < t) : t⁻¹ • f t + k t = ψ t / (t : ℂ) ^ 2 := by
    dsimp [f, k]
    rw [ofReal_inv, Real.rpow_sub ht, Real.rpow_two, ofReal_div, ofReal_pow]
    field_simp [ofReal_ne_zero.mpr ht.ne']
    ring
  have hfi := integrableOn_inv_smul_of_norm_le_exp_neg_div_sqrt_add hf hc hℓ hb
  have hi := (hfi.add (hk zero_lt_one)).congr_fun
    (fun t ht ↦ he t (zero_lt_one.trans ht)) measurableSet_Ioi
  have hy₀ := zero_lt_one.trans_le hy
  have hp : (y : ℂ) * (∫ t in Ioi y, k t) = B * (y ^ β : ℝ) / (1 - (β : ℂ)) := by
    have hval : y * (-(y ^ (β - 2 + 1)) / (β - 2 + 1)) = y ^ β / (1 - β) := by
      rw [show β - 2 + 1 = β - 1 by ring, Real.rpow_sub_one hy₀.ne']
      have hcancel : y * (y ^ β / y) = y ^ β := by
        rw [mul_comm, div_mul_cancel₀ _ hy₀.ne']
      rw [← mul_div_assoc, mul_neg, hcancel, neg_div, ← div_neg, neg_sub]
    rw [integral_const_mul, integral_complex_ofReal, integral_Ioi_rpow_of_lt (by linarith) hy₀,
      mul_left_comm, ← ofReal_mul, hval, ofReal_div, ofReal_sub, ofReal_one, mul_div_assoc]
  have hs := Ioi_subset_Ioi hy
  have hsplit : (∫ t in Ioi y, ψ t / (t : ℂ) ^ 2) =
      (∫ t in Ioi y, t⁻¹ • f t) + ∫ t in Ioi y, k t := by
    rw [← integral_add (hfi.mono_set hs) (hk hy₀)]
    exact setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ (he t (hy₀.trans ht)).symm
  rw [χ.rieszSum_add_mul_logDeriv_eq_neg_mul_integral hχ hi hy, hsplit, ← hp, neg_mul, mul_add,
    neg_add, neg_add_cancel_right, norm_neg, norm_mul, norm_real, Real.norm_of_nonneg hy₀.le]
  exact (mul_le_mul_of_nonneg_left
    (norm_integral_Ioi_inv_smul_le_of_norm_le_exp_neg_div_sqrt_add hc hℓ hy hb) hy₀.le).trans_eq
      (by ring)

end DirichletCharacter
