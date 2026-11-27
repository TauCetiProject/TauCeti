/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Entire
import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.SummatoryTail
import TauCeti.NumberTheory.Chebyshev.ResidueClass
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.Analysis.Calculus.LogDeriv
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.LSeries.Linearity

/-!
# First Riesz sums under a change of Dirichlet level

Inducing a Dirichlet character at a larger level deletes some Euler factors. In the first
Riesz sum this deletion can incur a linear error, but the change of the logarithmic derivative
at one cancels the linear term. The remaining error is a tail integral over the deleted prime
powers and is at most `ω(N) (1 + log y)` at cutoff `y ≥ 1`, where `ω(N)` counts the distinct primes
of the larger level. This allows a prime-number estimate for primitive Riesz remainders to be used
at the level of a residue class. The same comparison works for the principal character: its pole
term cancels between the two levels.

The normalization uses the first Riesz sum and its summatory-error integral, as in the
partial-summation treatment of prime counting in Montgomery and Vaughan, *Multiplicative Number
Theory I*, §6.2.
-/

public section

open ArithmeticFunction Complex Filter Finset MeasureTheory Set TauCeti
open scoped Topology

namespace DirichletCharacter

variable {M N : ℕ} [NeZero N]
  (χ : DirichletCharacter ℂ M) (hMN : M ∣ N)

/-- Inducing a character at level `N` changes its twisted Chebyshev sum by at most
`ω(N) log x`, since only nonunits at the new level are deleted. -/
theorem norm_sum_vonMangoldt_changeLevel_sub_le {x : ℝ} (hx : 1 ≤ x) :
    ‖∑ n ∈ Icc 1 ⌊x⌋₊, ((χ.changeLevel hMN n - χ n) * Λ n)‖ ≤
      N.primeFactors.card * Real.log x := by
  classical
  let f (a : ZMod N) : ℝ := if IsUnit a then 0 else 1
  have hmass : (∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * f n) =
      ∑ a : ZMod N with ¬IsUnit a, Chebyshev.psiAP N a x := by
    simpa [f, sum_filter, ← Finset.Icc_add_one_left_eq_Ioc] using
      (Chebyshev.sum_psiAP_smul f x).symm
  refine (norm_sum_le _ _).trans <| (sum_le_sum fun n _ ↦ ?_).trans <|
    hmass.symm ▸ Chebyshev.sum_psiAP_not_isUnit_le_card_mul_log hx
  by_cases hn : n.Coprime N
  · rw [χ.changeLevel_natCast_of_coprime hMN hn]
    simp only [sub_self, zero_mul, norm_zero, f, ZMod.isUnit_iff_coprime, ite_eq_left hn,
      mul_zero, le_refl]
  · rw [changeLevel_natCast, ite_eq_right hn, zero_sub, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg vonMangoldt_nonneg]
    simp only [f, ZMod.isUnit_iff_coprime, ite_eq_right hn, mul_one]
    exact mul_le_of_le_one_left vonMangoldt_nonneg (χ.norm_le_one n)

-- Divide the summatory bound by t² to get the majorant used in both integral arguments.
private theorem norm_sum_vonMangoldt_changeLevel_sub_div_sq_le {t : ℝ} (ht : 1 ≤ t) :
    ‖(∑ n ∈ Icc 1 ⌊t⌋₊, (χ.changeLevel hMN n - χ n) * Λ n) / (t : ℂ) ^ 2‖ ≤
      N.primeFactors.card * (t ^ (-2 : ℝ) * Real.log t) := by
  have ht₀ := zero_le_one.trans ht
  rw [norm_div, norm_pow, norm_real, Real.norm_of_nonneg ht₀, Real.rpow_neg ht₀, Real.rpow_two,
    mul_comm ((t ^ 2)⁻¹), ← mul_assoc, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right (χ.norm_sum_vonMangoldt_changeLevel_sub_le hMN ht) (sq_nonneg t)

private theorem integrableOn_changeLevel_vonMangoldt_div_sq :
    IntegrableOn (fun t : ℝ ↦
      (∑ n ∈ Icc 1 ⌊t⌋₊, (χ.changeLevel hMN n - χ n) * Λ n) / (t : ℂ) ^ 2) (Ioi 1) := by
  have hg := (integrableOn_Ioi_rpow_mul_log_of_lt (by norm_num : (-2 : ℝ) < -1)
    zero_lt_one).const_mul (N.primeFactors.card : ℝ)
  have hm : Measurable (fun t : ℝ ↦
      ∑ n ∈ Icc 1 ⌊t⌋₊, (χ.changeLevel hMN n - χ n) * Λ n) :=
    (measurable_of_countable (fun k : ℕ ↦ ∑ n ∈ Icc 1 k,
      (χ.changeLevel hMN n - χ n) * Λ n)).comp Nat.measurable_floor
  refine hg.mono' (hm.div (by fun_prop)).aestronglyMeasurable ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioi fun _ ht ↦
    χ.norm_sum_vonMangoldt_changeLevel_sub_div_sq_le hMN ht.le

variable [NeZero M]

open Classical in
private theorem rieszSum_changeLevel_sub_add_mul_logDeriv_entireLFunction_eq_of_one_le
    {y : ℝ} (hy : 1 ≤ y) :
    rieszSum (fun n ↦ χ.changeLevel hMN n * Λ n) y - rieszSum (fun n ↦ χ n * Λ n) y +
      y * (logDeriv (χ.changeLevel hMN).entireLFunction 1 - logDeriv χ.entireLFunction 1) =
      -(y : ℂ) * ∫ t in Ioi y,
        (∑ n ∈ Icc 1 ⌊t⌋₊, (χ.changeLevel hMN n - χ n) * Λ n) / (t : ℂ) ^ 2 := by
  let a (n : ℕ) : ℂ := (χ.changeLevel hMN n - χ n) * Λ n
  let D (s : ℂ) : ℂ := logDeriv χ.entireLFunction s - logDeriv (χ.changeLevel hMN).entireLFunction s
  have hseries (σ : ℝ) (hσ : 1 < σ) : LSeriesHasSum a (σ : ℂ) (D σ) := by
    have hre : 1 < (σ : ℂ).re := by simpa using hσ
    have h := ((χ.changeLevel hMN).LSeriesHasSum_twist_vonMangoldt hre).sub
      (χ.LSeriesHasSum_twist_vonMangoldt hre)
    have ha : a = (fun n : ℕ ↦ χ.changeLevel hMN n * (Λ n : ℂ)) - (fun n : ℕ ↦ χ n * Λ n) := by
      funext n
      exact sub_mul _ _ _
    simpa only [ha, D, changeLevel_eq_one_iff hMN, sub_sub_sub_cancel_left] using h
  have hcont (ψ : DirichletCharacter ℂ N) : ContinuousAt (logDeriv ψ.entireLFunction) 1 :=
    (ψ.analyticAt_entireLFunction 1).logDeriv
      (ψ.entireLFunction_ne_zero_of_one_le_re (by simp)) |>.continuousAt
  have hD : ContinuousAt D 1 :=
    ((χ.analyticAt_entireLFunction 1).logDeriv
      (χ.entireLFunction_ne_zero_of_one_le_re (by simp))).continuousAt.sub (hcont _)
  have hright : ∀ᶠ σ : ℝ in 𝓝[>] 1, 1 < σ := self_mem_nhdsWithin
  have hlim : Tendsto (fun σ : ℝ ↦ LSeries a (σ : ℂ)) (𝓝[>] 1) (𝓝 (D 1)) := by
    refine ((hD.tendsto.comp (continuous_ofReal.tendsto 1)).mono_left nhdsWithin_le_nhds).congr' ?_
    exact hright.mono fun σ hσ ↦ (hseries σ hσ).LSeries_eq.symm
  have h := rieszSum_div_sub_log_sub_eq_neg_integral_of_tendsto (A := 0) (a := a)
    (hright.mono fun σ hσ ↦ (hseries σ hσ).LSeriesSummable)
    (by simpa using χ.integrableOn_changeLevel_vonMangoldt_div_sq hMN)
    (by simpa using hlim) hy
  have hriesz : rieszSum a y =
      rieszSum (fun n ↦ χ.changeLevel hMN n * Λ n) y - rieszSum (fun n ↦ χ n * Λ n) y := by
    simp only [rieszSum_def, a, sub_mul, Finset.sum_sub_distrib]
  have hy₀ : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  simp only [zero_mul, sub_zero] at h
  rw [← hriesz]
  have he := congrArg (fun z : ℂ ↦ z * (y : ℂ)) h
  simp only [sub_mul, div_mul_cancel₀ _ hy₀, neg_mul] at he
  calc
    _ = rieszSum a y - D 1 * y := by dsimp [D]; ring
    _ = _ := by rw [he, mul_comm, neg_mul]

/-- The change in the first Riesz sum, compensated by the change in the pole-cleared
logarithmic derivative at one, is exactly a tail integral of the deleted coefficients. The tail
starts at `max 1 y` because the first Riesz sums vanish for `y ≤ 1`. -/
theorem rieszSum_changeLevel_sub_add_mul_logDeriv_entireLFunction_eq (y : ℝ) :
    rieszSum (fun n ↦ χ.changeLevel hMN n * Λ n) y - rieszSum (fun n ↦ χ n * Λ n) y +
      y * (logDeriv (χ.changeLevel hMN).entireLFunction 1 - logDeriv χ.entireLFunction 1) =
      -(y : ℂ) * ∫ t in Ioi (max 1 y),
        (∑ n ∈ Icc 1 ⌊t⌋₊, (χ.changeLevel hMN n - χ n) * Λ n) / (t : ℂ) ^ 2 := by
  rcases le_total 1 y with hy | hy
  · rw [max_eq_right hy]
    exact χ.rieszSum_changeLevel_sub_add_mul_logDeriv_entireLFunction_eq_of_one_le hMN hy
  · have h := χ.rieszSum_changeLevel_sub_add_mul_logDeriv_entireLFunction_eq_of_one_le hMN le_rfl
    simp only [rieszSum_eq_zero_of_le_one _ le_rfl, sub_self, ofReal_one, one_mul, zero_add,
      neg_one_mul] at h
    simp only [max_eq_left hy, rieszSum_eq_zero_of_le_one _ hy, sub_self, zero_add, h, mul_neg,
      neg_mul]

/-- Raising the level from `M` to `N` changes the pole-compensated first Riesz remainder
by at most `ω(N) (1 + log y)`. This estimate includes principal and imprimitive characters. -/
theorem norm_rieszSum_changeLevel_sub_add_mul_logDeriv_entireLFunction_le {y : ℝ} (hy : 1 ≤ y) :
    ‖rieszSum (fun n ↦ χ.changeLevel hMN n * Λ n) y - rieszSum (fun n ↦ χ n * Λ n) y +
      y * (logDeriv (χ.changeLevel hMN).entireLFunction 1 - logDeriv χ.entireLFunction 1)‖ ≤
      N.primeFactors.card * (1 + Real.log y) := by
  let g (t : ℝ) := (N.primeFactors.card : ℝ) * (t ^ (-2 : ℝ) * Real.log t)
  have hy₀ := zero_lt_one.trans_le hy
  have hg : IntegrableOn g (Ioi y) :=
    (integrableOn_Ioi_rpow_mul_log_of_lt (by norm_num) hy₀).const_mul _
  have hbound (t : ℝ) (ht : t ∈ Ioi y) : ‖(∑ n ∈ Icc 1 ⌊t⌋₊,
      (χ.changeLevel hMN n - χ n) * Λ n) / (t : ℂ) ^ 2‖ ≤ g t :=
    χ.norm_sum_vonMangoldt_changeLevel_sub_div_sq_le hMN (hy.trans ht.le)
  rw [χ.rieszSum_changeLevel_sub_add_mul_logDeriv_entireLFunction_eq hMN y, max_eq_right hy,
    norm_mul, norm_neg, norm_real, Real.norm_of_nonneg hy₀.le]
  calc
    _ ≤ y * ∫ t in Ioi y, g t := by
      exact mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le hg
        (ae_restrict_of_forall_mem measurableSet_Ioi hbound)) hy₀.le
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_mul_log_of_lt (by norm_num) hy₀]
      norm_num [Real.rpow_neg_one]
      field_simp

end DirichletCharacter
