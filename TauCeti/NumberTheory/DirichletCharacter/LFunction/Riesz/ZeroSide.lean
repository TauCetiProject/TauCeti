/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Hadamard.Riesz
public import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv.Riesz
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.Mellin
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Basic
import TauCeti.Analysis.LaplaceTransform.Elementary
import TauCeti.Analysis.LaplaceTransform.Mellin
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Growth
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.LogDeriv
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Origin
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Zeros

/-!
# The zero side of the Dirichlet Riesz formula

For a primitive nonprincipal Dirichlet character the zero side consists of the sum over
zeros of the entire completion, the strictly negative gamma-pole sum, and the origin
term. For an even character, the trivial zero at the origin contributes a logarithm; it
is not included in the negative gamma-pole sum. The upper Mellin integral of the combined
expression recovers `TauCeti.rieszRemainderMellin` on `1 < re s`. This allows the
explicit formula to be verified by Mellin uniqueness on one line of absolute convergence.

The completion and its Hadamard expansion use the conventions of Davenport,
*Multiplicative Number Theory*, 3rd ed., Chapters 12 and 14.
-/

public section

open Complex Filter MeasureTheory Set TauCeti TauCeti.LFunctions Topology

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)

open scoped Classical in
/-- The completed zero sum with the negative gamma-pole and origin corrections. The gamma
poles start at `-2` for even characters and at `-1` for odd characters. For nonprincipal
characters,
`DirichletCharacter.integrableOn_rieszZeroSide_mul_cpow_and_setIntegral_eq_rieszRemainderMellin`
identifies its upper Mellin integral. -/
noncomputable def rieszZeroSide (y : ℝ) : ℂ :=
  let a : ℝ := if χ.Even then 2 else 1
  rieszZeroSeries (dirichletData χ hχ).entireCompletion y + rieszGammaCorrection a 2 y +
    (logDerivFinitePart χ.LFunction 0 +
      (meromorphicOrderAt χ.LFunction 0).untop₀ * (1 + (Real.log y : ℂ)))

open scoped Classical in
/-- Expansion of the spectral side into the completed zero sum, negative gamma-pole sum,
and the origin term. -/
theorem rieszZeroSide_def (y : ℝ) :
    χ.rieszZeroSide hχ y =
      let a : ℝ := if χ.Even then 2 else 1
      rieszZeroSeries (dirichletData χ hχ).entireCompletion y + rieszGammaCorrection a 2 y +
        (logDerivFinitePart χ.LFunction 0 +
          (meromorphicOrderAt χ.LFunction 0).untop₀ * (1 + (Real.log y : ℂ))) := (rfl)

/-- The spectral side is continuous on the closed ray, including the cutoff `y = 1`. -/
theorem continuousOn_rieszZeroSide : ContinuousOn (χ.rieszZeroSide hχ) (Ici 1) := by
  classical
  rw [funext (χ.rieszZeroSide_def hχ)]
  let a : ℝ := if χ.Even then 2 else 1
  have ha : 0 < a := by dsimp [a]; split <;> norm_num
  have hZ := (dirichletData_entireCompletion_orderLE_one χ hχ).continuousOn_rieszZeroSeries
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (by norm_num) (fun _ hz ↦ (re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero χ hχ hz).2.le)
  refine (hZ.add (continuousOn_rieszGammaCorrection ha (by norm_num))).add ?_
  have hlog : ContinuousOn (fun y : ℝ ↦ (Real.log y : ℂ)) (Ici 1) :=
    Complex.continuous_ofReal.comp_continuousOn (Real.continuousOn_log.mono fun _ hy ↦
      Set.mem_compl_singleton_iff.mpr (zero_lt_one.trans_le hy).ne')
  exact continuousOn_const.add (continuousOn_const.mul (continuousOn_const.add hlog))

/-- The two terms at the origin, the constant and the logarithm, have elementary Laplace
transforms in the logarithmic variable. -/
private theorem integrableOn_origin_mul_cpow_and_setIntegral_eq {s : ℂ} (hs : 0 < s.re) :
    let c := logDerivFinitePart χ.LFunction 0
    let m : ℂ := (meromorphicOrderAt χ.LFunction 0).untop₀
    IntegrableOn (fun y : ℝ ↦ (c + m * (1 + (Real.log y : ℂ))) * (y : ℂ) ^ (-s - 1)) (Ioi 1) ∧
      (∫ y : ℝ in Ioi 1, (c + m * (1 + (Real.log y : ℂ))) * (y : ℂ) ^ (-s - 1)) =
        s⁻¹ * (c + m) + m * (1 / s ^ 2) := by
  let c := logDerivFinitePart χ.LFunction 0
  let m : ℂ := (meromorphicOrderAt χ.LFunction 0).untop₀
  have hp : HasLaplace (fun u : ℝ ↦ (u : ℂ)) s (1 / s ^ 2) := by
    simpa using hasLaplace_pow 1 hs
  have h := (hasLaplace_const (c + m) hs).add (hp.const_smul m)
  have heq : (fun y : ℝ ↦ c + m * (1 + (Real.log y : ℂ))) ∘ Real.exp =
      fun u : ℝ ↦ (c + m) + m • (u : ℂ) := by
    ext u
    simp [mul_add, add_assoc]
  have hmul (y : ℝ) :
      (y : ℂ) ^ (-s + -1) * (c + m * (1 + (Real.log y : ℂ))) =
        (c + m * (1 + (Real.log y : ℂ))) * (y : ℂ) ^ (-s + -1) := mul_comm _ _
  simpa only [Real.exp_zero, neg_add, sub_eq_add_neg, smul_eq_mul, hmul] using
    (hasLaplace_comp_exp_iff (fun y ↦ c + m * (1 + (Real.log y : ℂ))) s
      (s⁻¹ * (c + m) + m * (1 / s ^ 2)) 0).mp (heq ▸ h)

/-- The zero side of the first Riesz formula has absolutely convergent Mellin integral on
`1 < re s`, with value the meromorphic Riesz remainder expression of the L-function. -/
theorem integrableOn_rieszZeroSide_mul_cpow_and_setIntegral_eq_rieszRemainderMellin (hne : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ ↦ χ.rieszZeroSide hχ y * (y : ℂ) ^ (-s - 1)) (Ioi 1) ∧
      (∫ y : ℝ in Ioi 1, χ.rieszZeroSide hχ y * (y : ℂ) ^ (-s - 1)) =
        rieszRemainderMellin χ.LFunction s := by
  classical
  let a : ℝ := if χ.Even then 2 else 1
  let F := (dirichletData χ hχ).entireCompletion
  let c := logDerivFinitePart χ.LFunction 0
  let m : ℂ := (meromorphicOrderAt χ.LFunction 0).untop₀
  have ha : 0 < a := by dsimp [a]; split <;> norm_num
  have hσ : ∀ z, F z = 0 → z.re ≤ 1 := fun _ hz ↦
    (re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero χ hχ hz).2.le
  have ho := dirichletData_entireCompletion_orderLE_one χ hχ
  have hd := (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
  have hZ := ho.integrableOn_rieszZeroSeries_mul_cpow hd (by norm_num) hσ hs
  have hG := integrableOn_rieszGammaCorrection_mul_cpow (d := 2) ha (by norm_num)
    (by linarith : -a < s.re)
  obtain ⟨hE, hEval⟩ := χ.integrableOn_origin_mul_cpow_and_setIntegral_eq (one_pos.trans hs)
  have hm : ((meromorphicOrderAt χ.LFunction 0).untop₀ : ℂ) = (a : ℂ) - 1 :=
    χ.untop₀_meromorphicOrderAt_LFunction_zero hχ hne
  have hc : logDerivFinitePart χ.LFunction 0 = logDeriv F 0 - (Real.log N : ℂ) / 2 -
      logDeriv Gammaℝ a := χ.logDerivFinitePart_LFunction_zero hχ hne
  have hneL {z : ℂ} (hz : 1 ≤ z.re) := χ.LFunction_ne_zero_of_one_le_re (.inl hne) hz
  have hlog {z : ℂ} (hz : 1 ≤ z.re) := logDeriv_dirichletData_entireCompletion χ hχ hne
    (one_pos.trans_le hz) (hneL hz)
  have h₀ : s ≠ 0 := by rintro rfl; norm_num at hs
  have h₁ : s ≠ 1 := by rintro rfl; simp at hs
  have hF₀ : F 0 ≠ 0 := dirichletData_entireCompletion_ne_zero_of_re_nonpos χ hχ (by simp)
  have hF₁ : F 1 ≠ 0 := dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ (by simp)
  have hsplit (y : ℝ) : χ.rieszZeroSide hχ y * (y : ℂ) ^ (-s - 1) =
      rieszZeroSeries F y * (y : ℂ) ^ (-s - 1) +
        rieszGammaCorrection a 2 y * (y : ℂ) ^ (-s - 1) +
          (c + m * (1 + (Real.log y : ℂ))) * (y : ℂ) ^ (-s - 1) := by
    rw [χ.rieszZeroSide_def hχ, add_mul, add_mul (rieszZeroSeries _ _)]
  simp only [hsplit]
  refine ⟨(hZ.add hG).add hE, ?_⟩
  rw [integral_add (f := fun y : ℝ ↦ rieszZeroSeries F y * (y : ℂ) ^ (-s - 1) +
      rieszGammaCorrection a 2 y * (y : ℂ) ^ (-s - 1)) (hZ.add hG) hE,
    integral_add hZ hG, hEval,
    χ.rieszRemainderMellin_LFunction_of_ne_one hne hs,
    eq_div_iff_mul_eq (mul_ne_zero h₀ (sub_ne_zero.mpr h₁))]
  conv_lhs => rw [mul_comm]
  rw [mul_add, mul_add, ho.mul_integral_rieszZeroSeries_mul_cpow hd hF₀ hF₁ hσ hs,
    mul_integral_rieszGammaCorrection_eq_logDeriv_Gammaℝ ha (by linarith),
    hlog hs.le, hlog (by simp : 1 ≤ (1 : ℂ).re),
    χ.logDeriv_gammaFactor_eq_logDeriv_Gammaℝ_add_sub_div
      (χ.gammaFactor_ne_zero_of_re_pos (one_pos.trans hs)),
    χ.logDeriv_gammaFactor_eq_logDeriv_Gammaℝ_add_sub_div
      (χ.gammaFactor_ne_zero_of_re_pos (by simp : 0 < (1 : ℂ).re))]
  rw [hm, hc]
  push_cast only [ofReal_sub, ofReal_one]
  field_simp
  ring

end DirichletCharacter
