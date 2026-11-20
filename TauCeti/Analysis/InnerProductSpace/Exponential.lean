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

/-- The native bounded-semigroup comparison at nonnegative times, after scalar restriction. -/
private theorem norm_exp_smul_I_sub_exp_smul_I_apply_le_of_nonneg {Sm Sn : H →L[ℂ] H}
    (hm : IsSelfAdjoint Sm) (hn : IsSelfAdjoint Sn) (hcomm : Commute Sm Sn)
    {t : ℝ} (ht : 0 ≤ t) (ψ : H) :
    ‖exp (t • (I • Sm)) ψ - exp (t • (I • Sn)) ψ‖ ≤
      t * ‖(I • Sm - I • Sn) ψ‖ := by
  have hexp (S : H →L[ℂ] H) (u : ℝ) (x : H) :
      exp (u • (I • S).restrictScalars ℝ) x = exp (u • (I • S)) x := by
    let _i : Module ℚ H := Module.compHom H (algebraMap ℚ ℂ)
    let +nondep : NormedAlgebra ℚ (H →L[ℂ] H) := .restrictScalars ℚ ℂ _
    let +nondep : NormedAlgebra ℚ (H →L[ℝ] H) := .restrictScalars ℚ ℝ _
    let ρ : (H →L[ℂ] H) →+* (H →L[ℝ] H) :=
      { toFun := fun C => C.restrictScalars ℝ
        map_one' := by ext; rfl
        map_mul' := by intros; ext; rfl
        map_zero' := by ext; rfl
        map_add' := by intros; ext; rfl }
    -- The ring hom and the scalar-restriction isometry have the same underlying map.
    have hρ : Continuous ρ :=
      (ContinuousLinearMap.restrictScalarsIsometry ℂ H H ℝ ℝ).continuous
    have h := NormedSpace.map_exp ρ hρ (u • (I • S))
    have hsmul : ρ (u • (I • S)) = u • (I • S).restrictScalars ℝ := by
      ext x
      rfl
    rw [hsmul] at h
    -- Scalar restriction preserves real time scaling; evaluate the operator identity at `x`.
    have hx := congrArg (fun C : H →L[ℝ] H => C x) h
    simpa [ρ] using hx.symm
  have hbound (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (u : ℝ) (_hu : 0 ≤ u) :
      ‖exp (u • (I • S).restrictScalars ℝ)‖ ≤ (1 : ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    rw [hexp, one_mul]
    have h := (Semigroups.StronglyContinuousGroup.isUnitary_ofBoundedExp S hS).norm_map u x
    rw [Semigroups.StronglyContinuousGroup.ofBoundedExp_apply] at h
    -- Evaluate the real-linear restriction of the native Stone group.
    change ‖exp ((u : ℂ) • (I • S)) x‖ = ‖x‖ at h
    exact le_of_eq (by simpa only [Complex.coe_smul] using h)
  have hc : Commute ((I • Sm).restrictScalars ℝ) ((I • Sn).restrictScalars ℝ) := by
    ext x
    exact congrArg (fun C : H →L[ℂ] H => C x) ((hcomm.smul_left I).smul_right I).eq
  have h := Semigroups.norm_exp_smul_sub_exp_smul_apply_le_of_commute
    ((I • Sm).restrictScalars ℝ) ((I • Sn).restrictScalars ℝ) hc
    (hbound Sm hm) (hbound Sn hn) ht ψ
  simpa only [one_mul, hexp, sub_apply, ContinuousLinearMap.coe_restrictScalars'] using h

/-- **The Duhamel estimate.**  For commuting skew-adjoint generators the two
unitary flows differ by at most `|t|` times the difference of the generators. -/
theorem norm_exp_smul_I_sub_exp_smul_I_apply_le {Sm Sn : H →L[ℂ] H}
    (hm : IsSelfAdjoint Sm) (hn : IsSelfAdjoint Sn) (hcomm : Commute Sm Sn)
    (t : ℝ) (ψ : H) :
    ‖exp (t • (I • Sm)) ψ - exp (t • (I • Sn)) ψ‖
      ≤ |t| * ‖(I • Sm - I • Sn) ψ‖ := by
  by_cases ht : 0 ≤ t
  · simpa only [abs_of_nonneg ht] using
      norm_exp_smul_I_sub_exp_smul_I_apply_le_of_nonneg hm hn hcomm ht ψ
  · have h := norm_exp_smul_I_sub_exp_smul_I_apply_le_of_nonneg hm.neg hn.neg
      (hcomm.neg_left.neg_right) (by linarith : 0 ≤ -t) ψ
    simp only [smul_neg, neg_smul, neg_neg, neg_sub_neg, sub_apply] at h ⊢
    rw [norm_sub_rev ((I • Sn) ψ) ((I • Sm) ψ)] at h
    simpa only [abs_of_neg (lt_of_not_ge ht)] using h


end ContinuousLinearMap
