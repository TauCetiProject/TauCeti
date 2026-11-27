/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import TauCeti.Analysis.Fourier.DirichletJordan
import TauCeti.Topology.EMetricSpace.BoundedVariation

/-!
# Dirichlet–Jordan inversion of the bilateral Laplace transform

If a function is integrable after exponential damping, and has bounded variation near the
evaluation point, the symmetric vertical truncations of its inverse bilateral Laplace integral
converge to the mean of its one-sided limits. The truncated integral reduces to truncated Fourier
inversion of the damped function, with the frequency scaled by `2π`.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, §5.1, for the
  symmetric vertical truncation in Perron's formula.
* Robby Sneiderman, `PrimeNumberTheoremAnd/LaplaceInversion.lean`, for the reduction to truncated
  Fourier inversion.
-/

public section

open Complex Filter MeasureTheory Real Set Topology
open scoped FourierTransform

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem intervalIntegral_bilateralLaplace_eq_fourier (g : ℝ → E) (c x T : ℝ) :
    (1 / (2 * π)) • ∫ y in -T..T, Complex.exp ((c + y * I) * x) •
      (∫ u : ℝ, Complex.exp (-(c + y * I) * u) • g u) =
    Real.exp (c * x) • ∫ t in -(T / (2 * π))..T / (2 * π),
      𝐞 (t * x) • 𝓕 (fun u : ℝ ↦ Real.exp (-c * u) • g u) t := by
  have htransform (y : ℝ) :
      (∫ u : ℝ, Complex.exp (-(c + y * I) * u) • g u) =
        𝓕 (fun u : ℝ ↦ Real.exp (-c * u) • g u) (y / (2 * π)) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with u
    rw [← Complex.coe_smul, Complex.ofReal_exp, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  have hphase (y : ℝ) :
      Complex.exp ((c + y * I) * x) =
        (Real.exp (c * x) : ℂ) * 𝐞 (y / (2 * π) * x) := by
    rw [fourierChar_apply, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
  have hint (y : ℝ) :
      Complex.exp ((c + y * I) * x) •
        (∫ u : ℝ, Complex.exp (-(c + y * I) * u) • g u) =
      Real.exp (c * x) • (𝐞 (y / (2 * π) * x) •
        𝓕 (fun u : ℝ ↦ Real.exp (-c * u) • g u) (y / (2 * π))) := by
    rw [htransform, hphase, mul_smul, ← Circle.smul_def, Complex.coe_smul]
  simp_rw [hint, intervalIntegral.integral_smul]
  rw [smul_comm, one_div, intervalIntegral.inv_smul_integral_comp_div
    (f := fun t ↦ 𝐞 (t * x) • 𝓕 (fun u : ℝ ↦ Real.exp (-c * u) • g u) t), neg_div]

/-- **Pointwise inversion on a vertical Laplace line.** The inverse bilateral Laplace integrals
at heights `[-T, T]` converge to the mean of the left and right limits wherever the original
function has bounded variation on a neighbourhood. The damped function must be integrable on
the whole real line. -/
theorem tendsto_truncated_bilateralLaplaceInv (c : ℝ) {g : ℝ → E}
    (hgi : Integrable (fun u : ℝ ↦ Real.exp (-c * u) • g u))
    {x δ : ℝ} (hδ : 0 < δ) (hvar : BoundedVariationOn g (Icc (x - δ) (x + δ))) :
    Tendsto (fun T : ℝ ↦ (1 / (2 * π)) •
      ∫ y in -T..T, Complex.exp ((c + y * I) * x) •
        (∫ u : ℝ, Complex.exp (-(c + y * I) * u) • g u)) atTop
      (𝓝 ((1 / 2 : ℝ) • (g.leftLim x + g.rightLim x))) := by
  let w := fun u : ℝ ↦ Real.exp (-c * u)
  let g₀ := fun u : ℝ ↦ w u • g u
  let s := Icc (x - δ) (x + δ)
  have hd : ContDiff ℝ 1 w := by dsimp only [w]; fun_prop
  obtain ⟨K, hK⟩ := (hd.contDiffOn (s := s)).exists_lipschitzOnWith
    one_ne_zero (convex_Icc _ _) isCompact_Icc
  have hwvar : BoundedVariationOn w s :=
    hK.comp_boundedVariationOn (mapsTo_id _) (BoundedVariationOn.id_Icc _ _)
  have hgvar : BoundedVariationOn g₀ s := hwvar.smul hvar
  have hx : x ∈ interior s := by
    simp only [s, interior_Icc, mem_Ioo]
    constructor <;> linarith
  have hl : g₀.leftLim x = w x • g.leftLim x :=
    leftLim_eq_of_tendsto (hd.continuous.continuousWithinAt.tendsto.smul
      (hvar.tendsto_leftLim_of_mem_interior hx))
  have hr : g₀.rightLim x = w x • g.rightLim x :=
    rightLim_eq_of_tendsto (hd.continuous.continuousWithinAt.tendsto.smul
      (hvar.tendsto_rightLim_of_mem_interior hx))
  have hfourier := (hgi.tendsto_intervalIntegral_fourierInv_of_boundedVariationOn hδ hgvar)
    |>.comp (tendsto_id.atTop_div_const (by positivity : 0 < 2 * π))
  have h := hfourier.const_smul (Real.exp (c * x))
  have hw : Real.exp (c * x) * w x = 1 := by
    simp only [w, neg_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [hl, hr, ← smul_add, smul_comm (1 / 2 : ℝ), smul_smul, hw, one_smul] at h
  exact h.congr fun T ↦ (intervalIntegral_bilateralLaplace_eq_fourier g c x T).symm

end TauCeti
