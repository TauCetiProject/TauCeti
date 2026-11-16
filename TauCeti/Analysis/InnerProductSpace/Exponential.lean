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

namespace TauCeti

open Complex NormedSpace
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The exponential of a bounded operator scaled by a real time. -/
private noncomputable def expTime (B : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  exp (t • B)

/-! ### Unitarity -/

omit [CompleteSpace H] in
/-- `t • (I • S) = I • ((t : ℂ) • S)`: the real and complex scalings agree. -/
private theorem real_smul_I_smul (S : H →L[ℂ] H) (t : ℝ) :
    t • (I • S) = I • ((t : ℂ) • S) := by
  rw [smul_comm]
  congr 1

/-- For self-adjoint `S`, `exp (t • (I • S))` is unitary, hence norm-preserving. -/
private theorem norm_expTime_I_smul (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (t : ℝ) (ψ : H) :
    ‖expTime (I • S) t ψ‖ = ‖ψ‖ := by
  have hsa : ((t : ℂ) • S) ∈ selfAdjoint (H →L[ℂ] H) := by
    rw [selfAdjoint.mem_iff, star_smul, hS.star_eq, Complex.star_def, Complex.conj_ofReal]
  have hval : expTime (I • S) t = (selfAdjoint.expUnitary ⟨(t : ℂ) • S, hsa⟩ : H →L[ℂ] H) := by
    rw [expTime, real_smul_I_smul]
    rfl
  rw [hval]
  exact Unitary.norm_map _ ψ

/-! ### The Duhamel estimate -/

/-- **The Duhamel estimate.**  For commuting skew-adjoint generators the two
unitary flows differ by at most `|t|` times the difference of the generators. -/
private theorem norm_expTime_sub_expTime_le {Sm Sn : H →L[ℂ] H}
    (hm : IsSelfAdjoint Sm) (hn : IsSelfAdjoint Sn) (hcomm : Commute Sm Sn)
    (t : ℝ) (ψ : H) :
    ‖expTime (I • Sm) t ψ - expTime (I • Sn) t ψ‖
      ≤ |t| * ‖(I • Sm - I • Sn) ψ‖ := by
  set Bm : H →L[ℂ] H := I • Sm with hBm
  set Bn : H →L[ℂ] H := I • Sn with hBn
  have hBcomm : Commute Bm Bn := (hcomm.smul_left I).smul_right I
  let +nondep : NormedAlgebra ℚ (H →L[ℂ] H) := .restrictScalars ℚ ℂ _
  have hsum : t • Bn + t • (Bm - Bn) = t • Bm := by module
  have hint := intervalIntegrable_exp_smul_mul_mul_exp_smul
    (t • Bm) (t • (Bm - Bn)) (t • Bn)
  have hduhamel := exp_add_sub_exp_eq_integral (t • Bn) (t • (Bm - Bn))
  rw [hsum] at hduhamel
  have happly := congrArg (fun T : H →L[ℂ] H => T ψ) hduhamel
  rw [ContinuousLinearMap.intervalIntegral_apply hint ψ] at happly
  simp only [sub_apply] at happly
  change ‖exp (t • Bm) ψ - exp (t • Bn) ψ‖ ≤ _
  rw [happly]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := |t| * ‖(Bm - Bn) ψ‖) ?_).trans_eq ?_
  · intro s _
    have hmove : (t • (Bm - Bn)) * exp ((s * t) • Bn) =
        exp ((s * t) • Bn) * (t • (Bm - Bn)) :=
      (((hBcomm.sub_left (Commute.refl Bn)).smul_left t).smul_right (s * t)).exp_right.eq
    simp only [smul_smul]
    rw [mul_assoc, hmove]
    simp only [mul_apply_eq_comp]
    change ‖expTime Bm ((1 - s) * t)
      (expTime Bn (s * t) ((t • (Bm - Bn)) ψ))‖ ≤ _
    rw [hBm, norm_expTime_I_smul Sm hm, hBn, norm_expTime_I_smul Sn hn]
    simp only [smul_apply, norm_smul, Real.norm_eq_abs]
    exact le_rfl
  · simp


/-- Exponentials of imaginary multiples of self-adjoint operators preserve norms. -/
@[simp] theorem _root_.ContinuousLinearMap.norm_exp_smul_I_apply
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (t : ℝ) (x : H) :
    ‖NormedSpace.exp (t • (I • S)) x‖ = ‖x‖ := by
  exact norm_expTime_I_smul S hS t x

/-- The Duhamel estimate for commuting self-adjoint operators. -/
theorem _root_.ContinuousLinearMap.norm_exp_smul_I_sub_exp_smul_I_apply_le
    {S T : H →L[ℂ] H} (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T)
    (hcomm : Commute S T) (t : ℝ) (x : H) :
    ‖NormedSpace.exp (t • (I • S)) x - NormedSpace.exp (t • (I • T)) x‖ ≤
      |t| * ‖(I • S - I • T) x‖ := by
  exact norm_expTime_sub_expTime_le hS hT hcomm t x

end TauCeti
