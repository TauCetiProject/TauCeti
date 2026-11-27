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
term `B t^β` contributes `−B y^β / (1 − β)` to the Riesz remainder. A mixed
exponential error `C t exp(-c log t / (√(log t) + ℓ))` transfers at half the decay rate
`c / 2` and with the constant multiplied by `(1 + ℓ) (32 / c² + 4 / c)`, where `ℓ ≥ 0` is
a free parameter (the logarithm of the conductor in applications). For the unsmoothed
estimate and its exceptional term, see Iwaniec–Kowalski, *Analytic Number Theory*,
Theorem 5.27. The nonprincipal remainder normalization is that of Levent Alpöge's
`Deduction.Gchi`
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
    hs.mono fun σ hσ ↦ by
      simpa only [Pi.mul_def] using χ.LSeriesSummable_twist_vonMangoldt (by simpa using hσ)
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
    simp only [χ.logDeriv_LFunction_eq_neg_LSeries hz, neg_neg, Pi.mul_def]
  have htail := rieszSum_div_sub_log_sub_eq_neg_integral_of_tendsto (A := 0) ha
    (by simpa using hint) (by simpa using hlim) hy
  simp only [zero_mul, sub_zero, sub_neg_eq_add] at htail
  have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  calc
    _ = (rieszSum (fun n ↦ χ n * Λ n) y / (y : ℂ) + logDeriv χ.LFunction 1) * y := by
      rw [add_mul, div_mul_cancel₀ _ hy0, mul_comm (logDeriv χ.LFunction 1)]
    _ = _ := by rw [← mul_comm (y : ℂ), htail, mul_neg, neg_mul]

/-- The first Riesz remainder of a nonprincipal character, corrected by the contribution
`B y^β / (1 - β)` of a term `B t^β` with `β < 1`, is `−y` times the tail of the error
`ψ_χ(t) - B t^β` weighted by `t⁻²`, whenever that weighted error is integrable. -/
theorem rieszSum_add_mul_logDeriv_add_mul_rpow_div_eq_neg_mul_integral (hχ : χ ≠ 1)
    {β y : ℝ} (hβ : β < 1) (hy : 1 ≤ y) (B : ℂ)
    (hE : IntegrableOn (fun t : ℝ ↦
      ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ n * Λ n) - B * (t ^ β : ℝ)) / (t : ℂ) ^ 2) (Ioi 1)) :
    rieszSum (fun n ↦ χ n * Λ n) y + y * logDeriv χ.LFunction 1 +
      B * (y ^ β : ℝ) / (1 - (β : ℂ)) =
      -(y : ℂ) * ∫ t in Ioi y,
        ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ n * Λ n) - B * (t ^ β : ℝ)) / (t : ℂ) ^ 2 := by
  let ψ (t : ℝ) : ℂ := ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ n * Λ n
  let k (t : ℝ) : ℂ := B * (t ^ (β - 2) : ℝ)
  have hy₀ := zero_lt_one.trans_le hy
  have hk {a : ℝ} (ha : 0 < a) : IntegrableOn k (Ioi a) :=
    ((integrableOn_Ioi_rpow_of_lt (by linarith : β - 2 < -1) ha).ofReal).const_mul B
  have he (t : ℝ) (ht : 0 < t) :
      (ψ t - B * (t ^ β : ℝ)) / (t : ℂ) ^ 2 + k t = ψ t / (t : ℂ) ^ 2 := by
    dsimp only [k]
    rw [Real.rpow_sub ht, Real.rpow_two, ofReal_div, ofReal_pow]
    field_simp [ofReal_ne_zero.mpr ht.ne']
    ring
  have hi := (hE.add (hk zero_lt_one)).congr_fun
    (fun t ht ↦ he t (zero_lt_one.trans ht)) measurableSet_Ioi
  have hp : (y : ℂ) * (∫ t in Ioi y, k t) = B * (y ^ β : ℝ) / (1 - (β : ℂ)) := by
    have hval : y * (-(y ^ (β - 2 + 1)) / (β - 2 + 1)) = y ^ β / (1 - β) := by
      rw [show β - 2 + 1 = β - 1 by ring, Real.rpow_sub_one hy₀.ne']
      field_simp [hy₀.ne', (by linarith : β - 1 ≠ 0), (by linarith : 1 - β ≠ 0)]
      ring
    rw [integral_const_mul, integral_complex_ofReal, integral_Ioi_rpow_of_lt (by linarith) hy₀,
      mul_left_comm, ← ofReal_mul, hval]
    push_cast
    ring
  have hsplit : (∫ t in Ioi y, ψ t / (t : ℂ) ^ 2) =
      (∫ t in Ioi y, (ψ t - B * (t ^ β : ℝ)) / (t : ℂ) ^ 2) + ∫ t in Ioi y, k t := by
    rw [← integral_add (hE.mono_set (Ioi_subset_Ioi hy)) (hk hy₀)]
    exact setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ (he t (hy₀.trans ht)).symm
  rw [χ.rieszSum_add_mul_logDeriv_eq_neg_mul_integral hχ hi hy, hsplit, ← hp]
  ring

/-- A mixed-exponential error in the twisted Chebyshev sum transfers to the first Riesz
remainder at half the decay rate `c / 2` and with constant factor
`(1 + ℓ) (32 / c ^ 2 + 4 / c)`. A term `B t^β` with `β < 1` contributes exactly
`−B y^β / (1 − β)`. In particular `B = −1/β` yields the positive exceptional-zero term,
and `B = 0` gives the transfer without an exceptional term. -/
theorem norm_rieszSum_add_mul_logDeriv_add_mul_rpow_div_le (hχ : χ ≠ 1) {c ℓ C β y : ℝ}
    (hc : 0 < c) (hℓ : 0 ≤ ℓ) (hβ : β < 1) (hy : 1 ≤ y) (B : ℂ)
    (hψ : ∀ t > 1, ‖(∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ n * Λ n) - B * (t ^ β : ℝ)‖ ≤
      C * t * Real.exp (-(c * (Real.log t / (√(Real.log t) + ℓ))))) :
    ‖rieszSum (fun n ↦ χ n * Λ n) y + y * logDeriv χ.LFunction 1 +
      B * (y ^ β : ℝ) / (1 - (β : ℂ))‖ ≤
      C * y * (1 + ℓ) * (32 / c ^ 2 + 4 / c) *
        Real.exp (-(c / 2) * (Real.log y / (√(Real.log y) + ℓ))) := by
  let ψ (t : ℝ) : ℂ := ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ n * Λ n
  let f (t : ℝ) := (ψ t - B * (t ^ β : ℝ)) / (t : ℂ)
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
    exact (hψ t ht).trans_eq (by ring)
  have hfun : (fun t : ℝ ↦ ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ n * Λ n) - B * (t ^ β : ℝ)) /
      (t : ℂ) ^ 2) = fun t ↦ t⁻¹ • f t := by
    ext t
    simp only [f, ψ, real_smul, ofReal_inv]
    ring
  have hfi := integrableOn_inv_smul_of_norm_le_exp_neg_div_sqrt_add hf hc hℓ hb
  have hy₀ := zero_lt_one.trans_le hy
  rw [χ.rieszSum_add_mul_logDeriv_add_mul_rpow_div_eq_neg_mul_integral hχ hβ hy B
    (by rw [hfun]; exact hfi), hfun]
  calc
    _ = y * ‖∫ t in Ioi y, t⁻¹ • f t‖ := by
      rw [norm_mul, norm_neg, norm_real, Real.norm_of_nonneg hy₀.le]
    _ ≤ y * (C * ((1 + ℓ) * (32 / c ^ 2 + 4 / c)) *
        Real.exp (-(c / 2) * (Real.log y / (√(Real.log y) + ℓ)))) := by
      gcongr
      exact norm_integral_Ioi_inv_smul_le_of_norm_le_exp_neg_div_sqrt_add hc hℓ hy hb
    _ = _ := by ring

end DirichletCharacter
