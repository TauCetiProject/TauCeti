/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Hadamard.Riesz
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Riesz.Gamma
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Riesz.Mellin
public import TauCeti.NumberTheory.LFunctions.Hecke.RieszRemainder
import TauCeti.Analysis.MellinTransform.PowerLog
import TauCeti.Analysis.MellinTransform.Uniqueness
import TauCeti.NumberTheory.LFunctions.DedekindZeta.Growth
import TauCeti.NumberTheory.LFunctions.DedekindZeta.Nonvanishing
import TauCeti.NumberTheory.LFunctions.DedekindZeta.TrivialZeros
import TauCeti.NumberTheory.LFunctions.GammaFactor.Order
import TauCeti.Topology.Separation.Hausdorff

/-!
# The first Riesz explicit formula for Dedekind zeta

The first Riesz sum of the ideal von Mangoldt coefficients, after main-term subtraction,
is a sum over the zeros of the pole-cleared completion, together with a gamma correction
and an affine function of `log y` from the origin. As in the Riemann zeta case
(`TauCeti.riemannZetaRieszZeroSide`), the proof matches Mellin transforms using the
Hadamard expansion rather than shifting a contour. The remainder uses the normalization
of Levent Alpöge's `Deduction.Gchi` (<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open Complex Filter MeasureTheory NumberField NumberField.InfinitePlace Set
open scoped Topology

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

private noncomputable abbrev clearedCompletion : ℂ → ℂ :=
  toMeromorphicNFOn (fun s : ℂ ↦ s * (s - 1) * completedDedekindZeta K s) univ

private noncomputable abbrev dedekindGamma : ℂ → ℂ := (dedekindZetaData K).gammaFactor

private theorem clearedCompletion_ne_zero_zero : clearedCompletion K 0 ≠ 0 := by
  simpa only [clearedCompletion, toMeromorphicNFOn_mul_completedDedekindZeta_zero,
    toMeromorphicNFOn_mul_completedDedekindZeta_one] using
    toMeromorphicNFOn_mul_completedDedekindZeta_ne_zero_of_one_le_re K (s := 1) (by simp)

private theorem logDeriv_clearedCompletion {s : ℂ} (h₀ : s ≠ 0) (h₁ : s ≠ 1)
    (hγ : dedekindGamma K s ≠ 0) (hζ : dedekindZetaC K s ≠ 0) :
    logDeriv (clearedCompletion K) s = s⁻¹ + (s - 1)⁻¹ + log ((|discr K| : ℤ) : ℂ) / 2 +
      logDeriv (dedekindGamma K) s + logDeriv (dedekindZetaC K) s := by
  let D : ℂ := ((|discr K| : ℤ) : ℂ)
  have hD : D ≠ 0 := Int.cast_ne_zero.mpr (abs_ne_zero.mpr (discr_ne_zero K))
  have hA (z : ℂ) : D ^ (z / 2) ≠ 0 := cpow_ne_zero_iff.mpr (.inl hD)
  have hdA (z : ℂ) : DifferentiableAt ℂ (fun w : ℂ ↦ D ^ (w / 2)) z :=
    (by fun_prop : DifferentiableAt ℂ (fun w : ℂ ↦ w / 2) z).const_cpow (.inl hD)
  have haγ := (dedekindZetaData K).analyticAt_gammaFactor hγ
  have heq : clearedCompletion K =ᶠ[𝓝 s] fun z ↦
      z * (z - 1) * (D ^ (z / 2) * dedekindGamma K z * dedekindZetaC K z) := by
    filter_upwards [eventually_ne_nhds h₀, eventually_ne_nhds h₁,
      haγ.continuousAt.eventually_ne hγ] with z hz₀ hz₁ hzγ
    rw [clearedCompletion, toMeromorphicNFOn_mul_completedDedekindZeta_eq K hz₀ hz₁,
      dedekindZetaC_eq_mul_completedDedekindZeta K hz₀ hz₁]
    have hneg : D ^ (-z / 2) = (D ^ (z / 2))⁻¹ := by rw [neg_div, cpow_neg]
    rw [hneg, dedekindGamma, dedekindZetaData_gammaFactor]
    rw [dedekindZetaData_gammaFactor] at hzγ
    have hR := left_ne_zero_of_mul hzγ
    have hC := right_ne_zero_of_mul hzγ
    rw [inv_pow, inv_pow]
    field_simp [hA z, hR, hC]
  have hz₁ : s - 1 ≠ 0 := sub_ne_zero.mpr h₁
  have hdζ := (analyticAt_dedekindZetaC K h₁).differentiableAt
  have hdγ := haγ.differentiableAt
  have hsub : logDeriv (fun z : ℂ ↦ z - 1) s = (s - 1)⁻¹ := by
    simp [logDeriv_apply]
  have hpow : logDeriv (fun z : ℂ ↦ D ^ (z / 2)) s = log D / 2 := by
    have h := logDeriv_comp (f := fun z : ℂ ↦ D ^ z) (g := fun z : ℂ ↦ z / 2)
      (differentiableAt_id.const_cpow (.inl hD)) (by fun_prop) (x := s)
    simpa [Function.comp_def, logDeriv_const_cpow hD, div_eq_mul_inv] using h
  rw [(logDeriv_congr_nhds heq).eq_of_nhds,
    logDeriv_fun_mul (f := fun z ↦ z * (z - 1))
      (g := fun z ↦ D ^ (z / 2) * dedekindGamma K z * dedekindZetaC K z) s
      (mul_ne_zero h₀ hz₁) (mul_ne_zero (mul_ne_zero (hA s) hγ) hζ)
      (by fun_prop) (((hdA s).mul hdγ).mul hdζ),
    logDeriv_fun_mul (f := fun z ↦ z) (g := fun z ↦ z - 1) s h₀ hz₁ (by fun_prop) (by fun_prop),
    logDeriv_fun_mul (f := fun z ↦ D ^ (z / 2) * dedekindGamma K z) (g := dedekindZetaC K) s
      (mul_ne_zero (hA s) hγ) hζ ((hdA s).mul hdγ) hdζ,
    logDeriv_fun_mul (f := fun z ↦ D ^ (z / 2)) (g := dedekindGamma K) s (hA s) hγ (hdA s) hdγ,
    logDeriv_id', one_div, hsub, hpow]
  ring

private theorem dedekindGamma_ne_zero {s : ℂ} (hs : 0 < s.re) : dedekindGamma K s ≠ 0 := by
  rw [dedekindGamma, dedekindZetaData_gammaFactor]
  exact mul_ne_zero (pow_ne_zero _ (Gammaℝ_ne_zero_of_re_pos hs))
    (pow_ne_zero _ (Gammaℂ_ne_zero_of_re_pos hs))

private theorem logDeriv_clearedCompletion_zero :
    logDeriv (clearedCompletion K) 0 = logDerivFinitePart (dedekindZetaC K) 0 +
      logDerivFinitePart (dedekindGamma K) 0 + log ((|discr K| : ℤ) : ℂ) / 2 - 1 := by
  have hordζ := meromorphicOrderAt_dedekindZetaC_zero K
  have hordγ := meromorphicOrderAt_dedekindZetaData_gammaFactor_zero K
  have hmζ := meromorphic_dedekindZetaC K (0 : ℂ)
  obtain ⟨f, hf, hfEq⟩ := hmζ.exists_analyticAt_logDeriv_sub_order_div
  have hmγ := (dedekindZetaData K).meromorphic_gammaFactor 0
  obtain ⟨g, hg, hgEq⟩ := hmγ.exists_analyticAt_logDeriv_sub_order_div
  rw [hf.logDerivFinitePart_eq hfEq, hg.logDerivFinitePart_eq hgEq]
  have hζ := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hmζ).mp (by simp [hordζ])
  have h₁ : ∀ᶠ z : ℂ in 𝓝[≠] 0, z ≠ 1 := (eventually_ne_nhds zero_ne_one).filter_mono
    nhdsWithin_le_nhds
  have hd := differentiable_toMeromorphicNFOn_mul_completedDedekindZeta K
  have hcont := (hd.analyticAt 0).logDeriv (clearedCompletion_ne_zero_zero K)
  have hcont' : ContinuousAt (fun z : ℂ ↦ f z + g z + log ((|discr K| : ℤ) : ℂ) / 2 +
      (z - 1)⁻¹) 0 := by
    have := hf.continuousAt
    have := hg.continuousAt
    fun_prop (disch := norm_num)
  have hrank : (NumberField.Units.rank K : ℂ) + 1 = nrRealPlaces K + nrComplexPlaces K := by
    exact_mod_cast NumberField.Units.rank_add_one_eq_nrRealPlaces_add_nrComplexPlaces K
  have heq := hcont.continuousAt.eq_of_eventuallyEq_nhdsNE hcont' (by
    filter_upwards [hfEq, hgEq, hζ, (dedekindZetaData K).eventually_gammaFactor_ne_zero 0,
      h₁, self_mem_nhdsWithin] with z hzF hzG hzζ hzγ hz₁ hz₀
    have hz₀' : z ≠ 0 := hz₀
    rw [logDeriv_clearedCompletion K hz₀' hz₁ hzγ hzζ, ← hzF, ← hzG, hordζ, hordγ]
    simp only [sub_zero, WithTop.untop₀_coe, Int.cast_add, Int.cast_neg, Int.cast_natCast,
      div_eq_mul_inv]
    rw [← hrank]
    ring)
  simpa [clearedCompletion, sub_eq_add_neg] using heq

private theorem logDeriv_clearedCompletion_one :
    logDeriv (clearedCompletion K) 1 = (eulerKroneckerConstant K : ℂ) +
      logDeriv (dedekindGamma K) 1 + log ((|discr K| : ℤ) : ℂ) / 2 + 1 := by
  have hγ := dedekindGamma_ne_zero K (s := 1) (by norm_num)
  have hG := (dedekindZetaData K).analyticAt_gammaFactor hγ
  have hF := analyticAt_logDeriv_dedekindZetaPoleRemoved_one K
  have hd := differentiable_toMeromorphicNFOn_mul_completedDedekindZeta K
  have hX := (hd.analyticAt 1).logDeriv
    (toMeromorphicNFOn_mul_completedDedekindZeta_ne_zero_of_one_le_re K (by simp))
  have hmζ := meromorphic_dedekindZetaC K 1
  have hζ := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hmζ).mp
    (by simp [meromorphicOrderAt_dedekindZetaC_one])
  have hcont : ContinuousAt (fun z : ℂ ↦ logDeriv (dedekindZetaPoleRemoved K) z +
      logDeriv (dedekindGamma K) z + log ((|discr K| : ℤ) : ℂ) / 2 + z⁻¹) 1 := by
    have := hF.continuousAt
    have := (hG.logDeriv hγ).continuousAt
    fun_prop (disch := norm_num)
  have heq := hX.continuousAt.eq_of_eventuallyEq_nhdsNE hcont (by
    filter_upwards [logDeriv_dedekindZetaC_sub_order_eventuallyEq K, hζ,
      (hG.continuousAt.eventually_ne hγ).filter_mono nhdsWithin_le_nhds,
      (eventually_ne_nhds one_ne_zero).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with z hzF hzζ hzγ hz₀ hz₁
    have hz₁' : z ≠ 1 := hz₁
    rw [logDeriv_clearedCompletion K hz₀ hz₁' hzγ hzζ, ← hzF,
      meromorphicOrderAt_dedekindZetaC_one]
    simp only [WithTop.untop₀_coe, Int.cast_neg, Int.cast_one, div_eq_mul_inv]
    ring)
  simpa [logDeriv_dedekindZetaPoleRemoved_one] using heq

/-- The zero side of the first Riesz formula for Dedekind zeta. The nontrivial zeros are
counted with their orders by `rieszZeroSeries`; the two corrections account for strictly
negative trivial zeros and the origin, respectively. -/
noncomputable def dedekindZetaRieszZeroSide (y : ℝ) : ℂ :=
  rieszZeroSeries (clearedCompletion K) y + dedekindZetaRieszGammaCorrection K y +
    (logDerivFinitePart (dedekindZetaC K) 0 +
      ((nrRealPlaces K : ℂ) + nrComplexPlaces K - 1) * (1 + (Real.log y : ℂ)))

/-- Decompose the zero side into its nontrivial-zero, gamma and origin terms. -/
theorem dedekindZetaRieszZeroSide_def (y : ℝ) :
    dedekindZetaRieszZeroSide K y =
      rieszZeroSeries (toMeromorphicNFOn
        (fun s : ℂ ↦ s * (s - 1) * completedDedekindZeta K s) univ) y +
        dedekindZetaRieszGammaCorrection K y + (logDerivFinitePart (dedekindZetaC K) 0 +
          ((nrRealPlaces K : ℂ) + nrComplexPlaces K - 1) * (1 + (Real.log y : ℂ))) := (rfl)

/-- The explicit zero expression is continuous up to and including the cutoff `1`. -/
theorem continuousOn_dedekindZetaRieszZeroSide :
    ContinuousOn (dedekindZetaRieszZeroSide K) (Ici 1) := by
  have hZ := (orderLE_toMeromorphicNFOn_mul_completedDedekindZeta K).continuousOn_rieszZeroSeries
    (differentiable_toMeromorphicNFOn_mul_completedDedekindZeta K) (by norm_num)
    (fun ρ hρ ↦ (re_lt_one_of_toMeromorphicNFOn_mul_completedDedekindZeta_eq_zero K hρ).le)
  have hlog : ContinuousOn (fun y : ℝ ↦ (Real.log y : ℂ)) (Ici 1) :=
    continuous_ofReal.comp_continuousOn (Real.continuousOn_log.mono fun y hy ↦
      (zero_lt_one.trans_le (mem_Ici.mp hy)).ne')
  simp only [funext (dedekindZetaRieszZeroSide_def K)]
  exact (hZ.add (continuousOn_dedekindZetaRieszGammaCorrection K)).add
    (continuousOn_const.add (continuousOn_const.mul (continuousOn_const.add hlog)))

private theorem mellin_dedekindZetaRieszOrigin {s : ℂ} (hs : 0 < s.re) :
    let m : ℂ := (nrRealPlaces K : ℂ) + nrComplexPlaces K - 1
    let a := logDerivFinitePart (dedekindZetaC K) 0
    IntegrableOn (fun y : ℝ ↦ (a + m * (1 + (Real.log y : ℂ))) * (y : ℂ) ^ (-s - 1)) (Ioi 1) ∧
      (∫ y : ℝ in Ioi 1, (a + m * (1 + (Real.log y : ℂ))) * (y : ℂ) ^ (-s - 1)) =
        (a + m) / s + m / s ^ 2 := by
  dsimp only
  have hp : (-s - 1).re < -1 := by simp; linarith
  have hz : -(-s - 1 + 1) = s := by ring
  simp_rw [mul_add, mul_one, ← add_assoc]
  simp_rw [mul_comm (_ + _) (_ ^ _)]
  exact ⟨integrableOn_cpow_mul_affine_log_Ioi_one _ _ hp,
    (integral_cpow_mul_affine_log_Ioi_one _ _ hp).trans (by rw [hz])⟩

/-- The zero side has absolutely convergent Mellin transform on `Re s > 1`, and that
transform is the same pole-subtracted quotient as on the prime side. -/
theorem integrableOn_and_integral_dedekindZetaRieszZeroSide_mul_cpow {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ ↦ dedekindZetaRieszZeroSide K y * (y : ℂ) ^ (-s - 1)) (Ioi 1) ∧
    (∫ y : ℝ in Ioi 1, dedekindZetaRieszZeroSide K y * (y : ℂ) ^ (-s - 1)) =
      rieszRemainderMellin (dedekindZetaC K) s := by
  have hs₀ := Complex.ne_zero_of_re_pos (zero_lt_one.trans hs)
  have hs₁ : s ≠ 1 := by rintro rfl; simp at hs
  have hΞ := orderLE_toMeromorphicNFOn_mul_completedDedekindZeta K
  have hd := differentiable_toMeromorphicNFOn_mul_completedDedekindZeta K
  have hb (ρ : ℂ) (hρ : clearedCompletion K ρ = 0) :=
    (re_lt_one_of_toMeromorphicNFOn_mul_completedDedekindZeta_eq_zero K hρ).le
  have hZ := hΞ.integrableOn_rieszZeroSeries_mul_cpow hd (by norm_num) hb hs
  have hG := integrableOn_dedekindZetaRieszGammaCorrection_mul_cpow K (by linarith : -1 < s.re)
  obtain ⟨hO, hOeq⟩ := mellin_dedekindZetaRieszOrigin K (zero_lt_one.trans hs)
  simp only [dedekindZetaRieszZeroSide_def, add_mul] at hO hOeq ⊢
  refine ⟨(hZ.add hG).add hO, ?_⟩
  have hZG := integral_add hZ hG
  have hZGO := integral_add (hZ.add hG) hO
  simp only [Pi.add_apply] at hZG hZGO
  rw [hZGO, hZG, hOeq]
  have hZeq := hΞ.mul_integral_rieszZeroSeries_mul_cpow hd (clearedCompletion_ne_zero_zero K)
    (toMeromorphicNFOn_mul_completedDedekindZeta_ne_zero_of_one_le_re K (by simp)) hb hs
  have hGeq := mul_integral_dedekindZetaRieszGammaCorrection K (by linarith : -1 < s.re) hs₀
  have hn := dedekindZetaC_ne_zero_of_one_le_re K hs.le hs₁
  have hXeq := logDeriv_clearedCompletion K hs₀ hs₁
    (dedekindGamma_ne_zero K (zero_lt_one.trans hs)) hn
  rw [logDeriv_clearedCompletion_zero K, logDeriv_clearedCompletion_one K, hXeq] at hZeq
  rw [((meromorphic_dedekindZetaC K).rieszRemainderMellin_eq_and_analyticAt hs₀ hs₁
    (analyticAt_dedekindZetaC K hs₁) hn).1, logDerivFinitePart_dedekindZetaC_one,
    meromorphicOrderAt_dedekindZetaC_one, eq_div_iff (mul_ne_zero hs₀ (sub_ne_zero.mpr hs₁))]
  -- The discriminant term cancels in the affine Hadamard subtraction. The remaining poles
  -- from the gamma correction at zero cancel against the affine logarithm's transform.
  simp only [WithTop.untop₀_coe, Int.cast_neg, Int.cast_one] at ⊢
  linear_combination (norm := skip) hZeq + hGeq
  field_simp [hs₀, sub_ne_zero.mpr hs₁]
  ring

/-- The first Riesz remainder of the trivial primitive ray class character of `K` is the
Dedekind zeta zero side for every real cutoff `y ≥ 1`, including the endpoint. -/
theorem PrimitiveRayClassCharacter.rieszRemainder_one_eq_dedekindZetaRieszZeroSide {y : ℝ}
    (hy : 1 ≤ y) : (1 : PrimitiveRayClassCharacter K).rieszRemainder y =
      dedekindZetaRieszZeroSide K y := by
  have htwo : 1 < (2 : ℂ).re := by norm_num
  have hcont := (1 : PrimitiveRayClassCharacter K).continuous_rieszRemainder
  refine eqOn_Ici_of_mellin_integral_Ioi_eq_on_verticalLine (c := 2) zero_le_one
    hcont.continuousOn (continuousOn_dedekindZetaRieszZeroSide K) ?_ ?_ ?_ hy
  · simpa only [ofReal_ofNat, smul_eq_mul, mul_comm] using
      (1 : PrimitiveRayClassCharacter K).integrableOn_rieszRemainder_mul_cpow htwo
  · simpa only [ofReal_ofNat, smul_eq_mul, mul_comm] using
      (integrableOn_and_integral_dedekindZetaRieszZeroSide_mul_cpow K htwo).1
  · intro s hs
    have hs' : 1 < s.re := hs.symm ▸ (one_lt_two : (1 : ℝ) < 2)
    have hval := (integrableOn_and_integral_rieszSum_normCoeff_vonMangoldt_add_mul_cpow K hs').2
    simp_rw [smul_eq_mul, mul_comm (_ ^ _)]
    rw [(integrableOn_and_integral_dedekindZetaRieszZeroSide_mul_cpow K hs').2]
    simpa only [PrimitiveRayClassCharacter.rieszRemainder_one, ofReal_sub, ofReal_mul,
      ofReal_add, ofReal_one, mul_comm (_ : ℂ) (1 + (eulerKroneckerConstant K : ℂ))] using hval

end TauCeti.LFunctions
