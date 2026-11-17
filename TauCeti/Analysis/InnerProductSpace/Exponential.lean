/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, OpenAI GPT-6, OpenAI gpt-6.1-sol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.CStarAlgebra.Exponential
import TauCeti.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import TauCeti.Analysis.Semigroups.Group.Stone.Basic

/-!
# Exponential estimates for bounded self-adjoint operators

Exponentials of imaginary multiples of self-adjoint operators are isometries.
For commuting operators their exponential orbits satisfy a Duhamel estimate.

## Provenance

Adapted from `ForTauCeti/Analysis/InnerProductSpace/SkewAdjointExponential.lean`
in the Kitware DKPS formalization at `b9a02d00c` (Jon Crall, Claude Opus 5,
Kitware, 2026, Apache-2.0). The Duhamel proof adapts Spectra
`YosidaHille/Approximation/Commutation.lean` at `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`
(Adam Bornemann, Spectra Formalization Project, 2026, Apache-2.0). The interpolation
and FTC proof is now replaced by the native `TauCeti.exp_add_sub_exp_eq_integral`;
the commuting-generator reduction and unitarity bound preserve the original scope.
-/

public section

open Complex NormedSpace TauCeti
open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Duhamel estimate for commuting bounded self-adjoint operators. -/
theorem norm_exp_smul_I_sub_exp_smul_I_apply_le
    {S T : H →L[ℂ] H} (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T)
    (hcomm : Commute S T) (t : ℝ) (x : H) :
    ‖NormedSpace.exp (t • (I • S)) x - NormedSpace.exp (t • (I • T)) x‖ ≤
      |t| * ‖(I • S - I • T) x‖ := by
  have hnorm (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (u : ℝ) (y : H) :
      ‖exp (u • (I • A)) y‖ = ‖y‖ := by
    have h := (Semigroups.StronglyContinuousGroup.isUnitary_ofBoundedExp A hA).norm_map u y
    rw [Semigroups.StronglyContinuousGroup.ofBoundedExp_apply] at h
    -- Evaluate the real-linear restriction in the native bounded Stone group.
    change ‖exp ((u : ℂ) • (I • A)) y‖ = ‖y‖ at h
    simpa only [Complex.coe_smul] using h
  set Bm : H →L[ℂ] H := I • S with hBm
  set Bn : H →L[ℂ] H := I • T with hBn
  have hBcomm : Commute Bm Bn := (hcomm.smul_left I).smul_right I
  let +nondep : NormedAlgebra ℚ (H →L[ℂ] H) := .restrictScalars ℚ ℂ _
  have hsum : t • Bn + t • (Bm - Bn) = t • Bm := by module
  have hint := intervalIntegrable_exp_smul_mul_mul_exp_smul
    (t • Bm) (t • (Bm - Bn)) (t • Bn)
  have hduhamel := exp_add_sub_exp_eq_integral (t • Bn) (t • (Bm - Bn))
  rw [hsum] at hduhamel
  have happly := congrArg (fun A : H →L[ℂ] H => A x) hduhamel
  rw [ContinuousLinearMap.intervalIntegral_apply hint x] at happly
  simp only [sub_apply] at happly
  rw [happly]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := |t| * ‖(Bm - Bn) x‖) ?_).trans_eq ?_
  · intro s _
    have hmove : (t • (Bm - Bn)) * exp ((s * t) • Bn) =
        exp ((s * t) • Bn) * (t • (Bm - Bn)) :=
      (((hBcomm.sub_left (Commute.refl Bn)).smul_left t).smul_right (s * t)).exp_right.eq
    simp only [smul_smul]
    rw [mul_assoc, hmove]
    simp only [mul_apply_eq_comp]
    rw [hBm, hnorm S hS, hBn, hnorm T hT]
    simp only [smul_apply, norm_smul, Real.norm_eq_abs]
    exact le_rfl
  · simp

end ContinuousLinearMap
