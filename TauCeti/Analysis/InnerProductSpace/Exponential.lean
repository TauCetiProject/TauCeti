/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, OpenAI GPT-6, OpenAI gpt-6.1-sol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.CStarAlgebra.Exponential
import TauCeti.Analysis.Semigroups.BoundedGenerator.Perturbation
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import TauCeti.Analysis.Semigroups.Group.Stone.Basic

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

/-- **The Duhamel estimate.**  For commuting skew-adjoint generators the two
unitary flows differ by at most `|t|` times the difference of the generators. -/
theorem norm_exp_smul_I_sub_exp_smul_I_apply_le {Sm Sn : H →L[ℂ] H}
    (hm : IsSelfAdjoint Sm) (hn : IsSelfAdjoint Sn) (hcomm : Commute Sm Sn)
    (t : ℝ) (ψ : H) :
    ‖exp (t • (I • Sm)) ψ - exp (t • (I • Sn)) ψ‖
      ≤ |t| * ‖(I • Sm - I • Sn) ψ‖ := by
  have hexp (S : H →L[ℂ] H) (s : ℝ) :
      exp (s • (t • (I • S)).restrictScalars ℝ) =
        (exp ((s * t) • (I • S))).restrictScalars ℝ := by
    rw [Semigroups.StronglyContinuousGroup.restrictScalars_exp]
    simp only [Complex.coe_smul, smul_smul]
  have hbound (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (s : ℝ) (_hs : 0 ≤ s) :
      ‖exp (s • (t • (I • S)).restrictScalars ℝ)‖ ≤ (1 : ℝ) := by
    rw [hexp, norm_restrictScalars]
    exact Semigroups.StronglyContinuousGroup.norm_exp_smul_I_le S hS (s * t)
  have hc : Commute ((t • (I • Sm)).restrictScalars ℝ) ((t • (I • Sn)).restrictScalars ℝ) := by
    ext x
    exact congrArg (fun C : H →L[ℂ] H => C x)
      ((((hcomm.smul_left I).smul_right I).smul_left t).smul_right t).eq
  have h := Semigroups.norm_exp_smul_sub_exp_smul_apply_le_of_commute
    ((t • (I • Sm)).restrictScalars ℝ) ((t • (I • Sn)).restrictScalars ℝ) hc
    (hbound Sm hm) (hbound Sn hn) (by norm_num : (0 : ℝ) ≤ 1) ψ
  simpa only [one_mul, hexp, ← smul_sub, sub_apply, coe_restrictScalars', smul_apply,
    norm_smul, Real.norm_eq_abs] using h



end ContinuousLinearMap
