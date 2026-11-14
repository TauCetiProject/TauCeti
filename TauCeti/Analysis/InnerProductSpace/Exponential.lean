/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, OpenAI GPT-6
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Exponential estimates for bounded self-adjoint operators

Exponentials of imaginary multiples of self-adjoint operators are isometries.
For commuting operators their exponential orbits satisfy a Duhamel estimate.

## Provenance

Adapted from `ForTauCeti/Analysis/InnerProductSpace/SkewAdjointExponential.lean`
in the Kitware DKPS formalization at `b9a02d00c` (Jon Crall, Claude Opus 5,
Kitware, 2026, Apache-2.0). The Duhamel proof adapts Spectra
`YosidaHille/Approximation/Commutation.lean` at `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`
(Adam Bornemann, Spectra Formalization Project, 2026, Apache-2.0).
-/

public section

namespace TauCeti

open Complex NormedSpace
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The exponential of a bounded operator scaled by a real time. -/
private noncomputable def expTime (B : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  exp (t • B)

@[simp] private theorem expTime_zero (B : H →L[ℂ] H) : expTime B 0 = 1 := by
  simp [expTime]

/-- `t ↦ exp (t • B)` has derivative `exp (t • B) * B`. -/
private theorem hasDerivAt_expTime (B : H →L[ℂ] H) (t : ℝ) :
    HasDerivAt (expTime B) (expTime B t * B) t :=
  hasDerivAt_exp_smul_const (𝕂 := ℝ) B t

/-- Commuting operators have commuting exponentials. -/
private theorem commute_expTime_of_commute {B C : H →L[ℂ] H} (h : Commute B C) (t : ℝ) :
    Commute C (expTime B t) :=
  ((h.symm.smul_right t)).exp_right

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

/-- `s ↦ exp((t-s) • Bₙ)` differentiates to `-(exp((t-s) • Bₙ) * Bₙ)`. -/
private theorem hasDerivAt_expTime_sub (B : H →L[ℂ] H) (t s : ℝ) :
    HasDerivAt (fun s : ℝ => expTime B (t - s)) (-(expTime B (t - s) * B)) s := by
  have h2 : HasDerivAt (fun s : ℝ => t - s) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub t
  simpa [Function.comp_def] using (hasDerivAt_expTime B (t - s)).scomp s h2

/-- `s ↦ exp(s • B) ψ` differentiates to `(exp(s • B) * B) ψ`. -/
private theorem hasDerivAt_expTime_apply (B : H →L[ℂ] H) (ψ : H) (s : ℝ) :
    HasDerivAt (fun s : ℝ => expTime B s ψ) ((expTime B s * B) ψ) s := by
  have h := ((ContinuousLinearMap.apply ℂ H ψ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
    (hasDerivAt_expTime B s)
  exact HasDerivAt.congr_deriv h rfl

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
  -- the derivative of the interpolating path
  have hderiv : ∀ s : ℝ, HasDerivAt
      (fun s => expTime Bn (t - s) (expTime Bm s ψ))
      (expTime Bn (t - s) (expTime Bm s ((Bm - Bn) ψ))) s := by
    intro s
    have hf := hasDerivAt_expTime_sub Bn t s
    have hu := hasDerivAt_expTime_apply Bm ψ s
    -- `Bn` commutes with `exp(s • Bm)`
    have hcEn : Commute Bn (expTime Bm s) := commute_expTime_of_commute hBcomm s
    have hswap : Bn (expTime Bm s ψ) = expTime Bm s (Bn ψ) := by
      have h := congrArg (fun T : H →L[ℂ] H => T ψ) hcEn
      simpa using h
    have hval : expTime Bn (t - s) (expTime Bm s ((Bm - Bn) ψ))
        = (-(expTime Bn (t - s) * Bn)) (expTime Bm s ψ)
          + expTime Bn (t - s) ((expTime Bm s * Bm) ψ) := by
      have hsub : expTime Bm s ((Bm - Bn) ψ)
          = (expTime Bm s * Bm) ψ - Bn (expTime Bm s ψ) := by
        rw [hswap]
        simp only [sub_apply, map_sub]
        rfl
      rw [hsub, map_sub]
      simp only [neg_apply]
      abel
    -- `clm_apply` differentiates in `ℝ`, so the ℂ-linear operators must have their
    -- scalars restricted first
    have hf' := (ContinuousLinearMap.restrictScalarsL ℂ H H ℝ ℝ).hasFDerivAt.comp_hasDerivAt s hf
    rw [hval]
    simpa using HasDerivAt.clm_apply hf' hu
  -- continuity of the derivative, for integrability
  have hcont : Continuous
      (fun s : ℝ => expTime Bn (t - s) (expTime Bm s ((Bm - Bn) ψ))) := by
    have cBn : Continuous (fun τ : ℝ => expTime Bn τ) :=
      Differentiable.continuous fun τ => (hasDerivAt_expTime Bn τ).differentiableAt
    have cBm : Continuous (fun τ : ℝ => expTime Bm τ) :=
      Differentiable.continuous fun τ => (hasDerivAt_expTime Bm τ).differentiableAt
    exact (cBn.comp (continuous_const.sub continuous_id)).clm_apply
      (cBm.clm_apply continuous_const)
  -- fundamental theorem of calculus
  have hftc : (∫ s in (0 : ℝ)..t, expTime Bn (t - s) (expTime Bm s ((Bm - Bn) ψ)))
      = expTime Bm t ψ - expTime Bn t ψ := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s => expTime Bn (t - s) (expTime Bm s ψ))
      (fun s _ => hderiv s) (hcont.intervalIntegrable 0 t)
    simpa using h
  -- the integrand has constant norm, by unitarity of both flows
  have hnorm : ∀ s : ℝ,
      ‖expTime Bn (t - s) (expTime Bm s ((Bm - Bn) ψ))‖ = ‖(Bm - Bn) ψ‖ := by
    intro s
    rw [hBn, norm_expTime_I_smul Sn hn, hBm, norm_expTime_I_smul Sm hm]
  calc ‖expTime Bm t ψ - expTime Bn t ψ‖
      = ‖∫ s in (0 : ℝ)..t, expTime Bn (t - s) (expTime Bm s ((Bm - Bn) ψ))‖ := by rw [hftc]
    _ ≤ ‖(Bm - Bn) ψ‖ * |t - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => ?_
        exact le_of_eq (hnorm s)
    _ = |t| * ‖(Bm - Bn) ψ‖ := by rw [sub_zero, mul_comm]

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
