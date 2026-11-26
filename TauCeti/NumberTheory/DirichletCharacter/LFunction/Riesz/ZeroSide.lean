/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Hadamard.Riesz
public import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv.Riesz
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Completed.LogDeriv
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.Mellin
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Basic
import TauCeti.Analysis.MellinTransform.PowerLog
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

/-- The completed zero sum with the negative gamma-pole and origin corrections. The gamma
poles start at `-2` for even characters and at `-1` for odd characters. For nonprincipal
characters,
`DirichletCharacter.integrableOn_rieszZeroSide_mul_cpow_and_setIntegral_eq_rieszRemainderMellin`
identifies its upper Mellin integral. -/
noncomputable def rieszZeroSide (y : ℝ) : ℂ :=
  rieszZeroSeries (dirichletData χ hχ).entireCompletion y +
    rieszGammaCorrection χ.gammaPoleOffset 2 y +
    (logDerivFinitePart χ.LFunction 0 +
      (meromorphicOrderAt χ.LFunction 0).untop₀ * (1 + (Real.log y : ℂ)))

/-- Expansion of the spectral side into the completed zero sum, negative gamma-pole sum,
and the origin term. -/
theorem rieszZeroSide_def (y : ℝ) :
    χ.rieszZeroSide hχ y =
      rieszZeroSeries (dirichletData χ hχ).entireCompletion y +
        rieszGammaCorrection χ.gammaPoleOffset 2 y +
        (logDerivFinitePart χ.LFunction 0 +
          (meromorphicOrderAt χ.LFunction 0).untop₀ * (1 + (Real.log y : ℂ))) := (rfl)

/-- The spectral side is continuous on the closed ray, including the cutoff `y = 1`. -/
theorem continuousOn_rieszZeroSide : ContinuousOn (χ.rieszZeroSide hχ) (Ici 1) := by
  classical
  rw [funext (χ.rieszZeroSide_def hχ)]
  have hZ := (dirichletData_entireCompletion_orderLE_one χ hχ).continuousOn_rieszZeroSeries
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (by norm_num) (fun _ hz ↦ (re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero χ hχ hz).2.le)
  refine (hZ.add (continuousOn_rieszGammaCorrection χ.gammaPoleOffset_pos (by norm_num))).add ?_
  have hlog : ContinuousOn (fun y : ℝ ↦ (Real.log y : ℂ)) (Ici 1) :=
    Complex.continuous_ofReal.comp_continuousOn (Real.continuousOn_log.mono fun _ hy ↦
      Set.mem_compl_singleton_iff.mpr (zero_lt_one.trans_le hy).ne')
  exact continuousOn_const.add (continuousOn_const.mul (continuousOn_const.add hlog))

/-- The zero side of the first Riesz formula has absolutely convergent Mellin integral on
`1 < re s`, with value the meromorphic Riesz remainder expression of the L-function. -/
theorem integrableOn_rieszZeroSide_mul_cpow_and_setIntegral_eq_rieszRemainderMellin (hne : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ ↦ χ.rieszZeroSide hχ y * (y : ℂ) ^ (-s - 1)) (Ioi 1) ∧
      (∫ y : ℝ in Ioi 1, χ.rieszZeroSide hχ y * (y : ℂ) ^ (-s - 1)) =
        rieszRemainderMellin χ.LFunction s := by
  classical
  let a := χ.gammaPoleOffset
  let F := (dirichletData χ hχ).entireCompletion
  let c := logDerivFinitePart χ.LFunction 0
  let m : ℂ := (meromorphicOrderAt χ.LFunction 0).untop₀
  have ha : 0 < a := χ.gammaPoleOffset_pos
  have hσ : ∀ z, F z = 0 → z.re ≤ 1 := fun _ hz ↦
    (re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero χ hχ hz).2.le
  have ho := dirichletData_entireCompletion_orderLE_one χ hχ
  have hd := (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
  have hZ := ho.integrableOn_rieszZeroSeries_mul_cpow hd (by norm_num) hσ hs
  have hneg : -a < s.re := by linarith
  have hG := integrableOn_rieszGammaCorrection_mul_cpow (d := 2) ha (by norm_num) hneg
  have hp : (-s - 1).re < -1 := by simp only [sub_re, neg_re, one_re]; linarith
  have hE := integrableOn_cpow_mul_affine_log_Ioi_one (c + m) m hp
  have h₀ : s ≠ 0 := by rintro rfl; norm_num at hs
  have h₁ : s ≠ 1 := by rintro rfl; simp at hs
  have hF₀ : F 0 ≠ 0 := dirichletData_entireCompletion_ne_zero_of_re_nonpos χ hχ (by simp)
  have hF₁ : F 1 ≠ 0 := dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ (by simp)
  have hsplit (y : ℝ) : χ.rieszZeroSide hχ y * (y : ℂ) ^ (-s - 1) =
      rieszZeroSeries F y * (y : ℂ) ^ (-s - 1) +
        rieszGammaCorrection a 2 y * (y : ℂ) ^ (-s - 1) +
          (y : ℂ) ^ (-s - 1) * (c + m + m * (Real.log y : ℂ)) := by
    rw [χ.rieszZeroSide_def hχ]
    ring
  simp only [hsplit]
  refine ⟨(hZ.add hG).add hE, ?_⟩
  -- Substitute the Mellin integrals of the zero series, the gamma correction, and the origin term.
  have hZval := ho.mul_integral_rieszZeroSeries_mul_cpow hd hF₀ hF₁ hσ hs
  have hGval := mul_integral_rieszGammaCorrection_eq_logDeriv_Gammaℝ ha hneg
  have hEval := integral_cpow_mul_affine_log_Ioi_one (c + m) m hp
  have hexponent : -(-s - 1 + 1) = s := by ring
  rw [hexponent] at hEval
  rw [integral_add (f := fun y : ℝ ↦ rieszZeroSeries F y * (y : ℂ) ^ (-s - 1) +
      rieszGammaCorrection a 2 y * (y : ℂ) ^ (-s - 1)) (hZ.add hG) hE,
    integral_add hZ hG, hEval, χ.rieszRemainderMellin_LFunction_of_ne_one hne hs]
  rw [χ.logDeriv_dirichletData_entireCompletion_eq_logDeriv_Gammaℝ_add hχ hne
    (χ.LFunction_ne_zero_of_one_le_re (.inl hne) hs.le),
    χ.logDeriv_dirichletData_entireCompletion_eq_logDeriv_Gammaℝ_add hχ hne
      (χ.LFunction_ne_zero_of_one_le_re (.inl hne) (by simp : 1 ≤ (1 : ℂ).re))] at hZval
  dsimp only [c, m]
  rw [χ.untop₀_meromorphicOrderAt_LFunction_zero hχ hne, χ.logDerivFinitePart_LFunction_zero hχ hne]
  apply (eq_div_iff_mul_eq (mul_ne_zero h₀ (sub_ne_zero.mpr h₁))).2
  linear_combination (norm := skip) hZval + hGval
  field_simp
  ring

end DirichletCharacter
