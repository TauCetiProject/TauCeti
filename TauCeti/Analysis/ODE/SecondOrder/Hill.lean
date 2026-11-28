/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import TauCeti.Analysis.ODE.Propagator
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.Analysis.Calculus.IteratedDeriv.Basic
import TauCeti.Analysis.Normed.Algebra.NilpotentExponential
import TauCeti.Analysis.ODE.Propagator.Holomorphic.Basic
import TauCeti.Analysis.ODE.SecondOrder.Linear
public import TauCeti.Analysis.ODE.SecondOrder.Companion
import TauCeti.Analysis.ODE.Wronskian
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Fundamental solutions of Hill's equation

For a continuous real potential `Q`, Hill's equation on the real line is
`w'' + (λ + Q) w = 0`, with complex spectral parameter `λ`. The solutions
`hillWI Q λ` and `hillWII Q λ` have initial data `(1, 0)` and `(0, 1)` at zero.
They span the solution space, have Wronskian one, and give the translation formulas
for any period of `Q`. At each point of the real line their values and first derivatives
are entire in `λ`. The values and first derivatives of the normalized pair at a period
form the columns of the monodromy matrix, which propagates initial data through that period.

The construction applies `TauCeti.propagator` to the system
`(w, v)' = (v, -(λ + Q) w)`, using `ContinuousLinearMap.jacobiODECoeff` for the companion
operator. The coefficient is affine in `λ`, so `TauCeti.differentiable_propagator_smul_add`
gives entireness.

## References

* NIST Digital Library of Mathematical Functions, [§28.29](https://dlmf.nist.gov/28.29),
  equations 28.29.1 and 28.29.4–5.
-/

public section

open Set ContinuousLinearMap
open scoped ComplexConjugate

namespace TauCeti

/-- A classical solution of Hill's equation on the real line with potential `Q` and parameter
`λ`. The equation is written as `w'' = -(λ + Q) w` to match the second-order ODE API. -/
structure IsHillSolution (Q : ℝ → ℝ) (lam : ℂ) (w : ℝ → ℂ) : Prop where
  /-- The solution is twice continuously differentiable in the real variable. -/
  contDiff : ContDiff ℝ 2 w
  /-- Hill's equation in solved form for the second derivative. -/
  iteratedDeriv_two (x : ℝ) : iteratedDeriv 2 w x = -(lam + (Q x : ℂ)) * w x

variable {Q : ℝ → ℝ} {lam : ℂ} {u w : ℝ → ℂ}

/-- The first derivative of a Hill solution has the derivative prescribed by the equation. -/
theorem IsHillSolution.hasDerivAt_deriv (hw : IsHillSolution Q lam w) (x : ℝ) :
    HasDerivAt (deriv w) (-(lam + (Q x : ℂ)) * w x) x := by
  rw [← hw.iteratedDeriv_two x]
  exact (hw.contDiff.contDiffOn (s := univ)).hasDerivAt_and_hasDerivAt_deriv
    isOpen_univ (mem_univ x) |>.2

/-- A function with two successive derivatives satisfying the first-order system for Hill's
equation is a classical solution when the prescribed second derivative is continuous. -/
theorem isHillSolution_of_hasDerivAt {v : ℝ → ℂ}
    (hqw : Continuous (fun x ↦ -(lam + (Q x : ℂ)) * w x))
    (hw : ∀ x, HasDerivAt w (v x) x)
    (hv : ∀ x, HasDerivAt v (-(lam + (Q x : ℂ)) * w x) x) :
    IsHillSolution Q lam w := by
  obtain ⟨hcw, heq⟩ := contDiffOn_two_of_hasDerivAt isOpen_univ hqw.continuousOn
    (fun x _ ↦ hw x) (fun x _ ↦ hv x)
  exact ⟨contDiffOn_univ.mp hcw, fun x ↦ heq x (mem_univ x)⟩

/-- The zero function solves Hill's equation for every potential. -/
@[simp] theorem isHillSolution_zero : IsHillSolution Q lam (0 : ℝ → ℂ) := by
  refine ⟨contDiff_const, fun x ↦ ?_⟩
  simp

/-- The sum of two classical Hill solutions solves the same equation. -/
theorem IsHillSolution.add (hu : IsHillSolution Q lam u) (hw : IsHillSolution Q lam w) :
    IsHillSolution Q lam (u + w) := by
  refine ⟨hu.contDiff.add hw.contDiff, fun x ↦ ?_⟩
  rw [iteratedDeriv_add hu.contDiff.contDiffAt hw.contDiff.contDiffAt]
  simp only [Pi.add_apply, hu.iteratedDeriv_two, hw.iteratedDeriv_two, mul_add]

/-- A scalar multiple of a classical Hill solution solves the same equation. -/
theorem IsHillSolution.smul (hw : IsHillSolution Q lam w) (c : ℂ) :
    IsHillSolution Q lam (c • w) := by
  refine ⟨contDiff_const.smul hw.contDiff, fun x ↦ ?_⟩
  -- Write pointwise scalar multiplication as multiplication to apply the scalar derivative rule.
  change iteratedDeriv 2 (fun t ↦ c * w t) x = -(lam + (Q x : ℂ)) * (c * w x)
  rw [iteratedDeriv_const_mul_field, hw.iteratedDeriv_two]
  ring

/-- The companion operator for Hill's equation. -/
noncomputable def hillCoefficient (Q : ℝ → ℝ) (lam : ℂ) (x : ℝ) :
    (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  jacobiODECoeff ((lam + (Q x : ℂ)) • (1 : ℂ →L[ℂ] ℂ))

/-- The Hill coefficient sends a value–velocity pair to its prescribed time derivative. -/
@[simp] theorem hillCoefficient_apply (v : ℂ × ℂ) (x : ℝ) :
    hillCoefficient Q lam x v = (v.2, -(lam + (Q x : ℂ)) * v.1) := by
  simp only [hillCoefficient, jacobiODECoeff_apply, smul_apply, one_apply_eq_self, smul_eq_mul,
    neg_mul]

/-- A continuous potential gives a continuous Hill companion coefficient. -/
theorem continuous_hillCoefficient (hQ : Continuous Q) :
    Continuous (hillCoefficient Q lam) :=
  (contDiff_jacobiODECoeff (𝕜 := ℂ) (F := ℂ) (n := 0)).continuous.comp
    ((continuous_const.add (Complex.continuous_ofReal.comp hQ)).smul continuous_const)

/-- The affine form of the companion operator in the spectral parameter. -/
theorem hillCoefficient_eq_smul_add (x : ℝ) :
    hillCoefficient Q lam x =
      lam • jacobiODECoeffVariation (1 : ℂ →L[ℂ] ℂ) + hillCoefficient Q 0 x := by
  have hs := (add_smul lam (Q x : ℂ) (1 : ℂ →L[ℂ] ℂ)).trans (add_comm _ _)
  have h := (congrArg (jacobiODECoeff (𝕜 := ℂ) (F := ℂ)) hs).trans
    (jacobiODECoeff_add ((Q x : ℂ) • 1) (lam • 1))
  simpa only [hillCoefficient, zero_add, map_smul] using h.trans (add_comm _ _)

/-- Segment integrability of the potential gives integrability of the Hill coefficient. -/
theorem integrableOn_hillCoefficient {a b : ℝ}
    (hQ : MeasureTheory.IntegrableOn Q (Icc a b)) :
    MeasureTheory.IntegrableOn (hillCoefficient Q lam) (Icc a b) := by
  have hR := ((Complex.ofRealCLM.integrableOn_comp hQ).add
    (MeasureTheory.integrableOn_const (μ := MeasureTheory.volume)
      (s := Icc a b) (by simp))).smul_const (1 : ℂ →L[ℂ] ℂ)
  have hV := (jacobiODECoeffVariation (𝕜 := ℂ) (F := ℂ)).integrableOn_comp hR
  have heq : hillCoefficient Q lam = fun r ↦ jacobiODECoeff (0 : ℂ →L[ℂ] ℂ) +
      jacobiODECoeffVariation (((Q r : ℂ) + lam) • (1 : ℂ →L[ℂ] ℂ)) := by
    funext r
    simpa only [hillCoefficient, add_comm] using
      jacobiODECoeff_eq_jacobiODECoeff_zero_add (((Q r : ℂ) + lam) • (1 : ℂ →L[ℂ] ℂ))
  rw [heq]
  exact (MeasureTheory.integrableOn_const (μ := MeasureTheory.volume)
    (s := Icc a b) (by simp)).add hV

/-- A classical Hill solution is propagated from its value and derivative at any reference
time, provided the potential is integrable between that time and the evaluation time. -/
theorem IsHillSolution.eq_propagator_apply (hw : IsHillSolution Q lam w) (x s : ℝ)
    (hQ : MeasureTheory.IntegrableOn Q (uIcc s x)) :
    (w x, deriv w x) = propagator (hillCoefficient Q lam) x s (w s, deriv w s) := by
  have hP := integrableOn_hillCoefficient (lam := lam) hQ
  have hc : Continuous (fun t ↦ (w t, deriv w t)) := hw.contDiff.continuous.prodMk
    (continuousOn_univ.mp
      (hw.contDiff.contDiffOn.continuousOn_deriv_of_isOpen isOpen_univ (by norm_num)))
  have hd (t : ℝ) : HasDerivAt (fun t ↦ (w t, deriv w t))
      (hillCoefficient Q lam t (w t, deriv w t)) t := by
    rw [hillCoefficient_apply]
    exact ((hw.contDiff.differentiable (by norm_num) t).hasDerivAt).prodMk
      (hw.hasDerivAt_deriv t)
  refine TauCeti.eq_propagator_apply hP left_mem_uIcc right_mem_uIcc hc.continuousOn fun r hr ↦ ?_
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
    (((hP.clm_apply_continuousOn hc.continuousOn isCompact_Icc).mono_set
      (uIcc_subset_Icc left_mem_uIcc hr)).intervalIntegrable)]
  exact (add_sub_cancel _ _).symm

/-- Two Hill solutions for a locally integrable potential agree if their values and derivatives
agree at one point. -/
theorem IsHillSolution.eq_of_initial_data (hu : IsHillSolution Q lam u)
    (hw : IsHillSolution Q lam w) (hQ : MeasureTheory.LocallyIntegrable Q) {x : ℝ}
    (h₀ : u x = w x) (h₁ : deriv u x = deriv w x) : u = w := by
  funext t
  have hi := hQ.integrableOn_isCompact (isCompact_uIcc (a := x) (b := t))
  have heq := (hu.eq_propagator_apply t x hi).trans
    (by rw [h₀, h₁, ← hw.eq_propagator_apply t x hi])
  exact congrArg Prod.fst heq

/-- The state of the first-order system, evolved from the data `v` at zero. -/
private noncomputable def hillState (Q : ℝ → ℝ) (lam : ℂ) (v : ℂ × ℂ)
    (x : ℝ) : ℂ × ℂ :=
  propagator (hillCoefficient Q lam) x 0 v

private theorem hillState_eq_propagator_apply (v : ℂ × ℂ) (x : ℝ) :
    hillState Q lam v x = propagator (hillCoefficient Q lam) x 0 v := rfl

@[simp]
private theorem hillState_zero (v : ℂ × ℂ) : hillState Q lam v 0 = v := by
  simp [hillState]

private theorem hasDerivAt_hillState (hQ : Continuous Q) (v : ℂ × ℂ) (x : ℝ) :
    HasDerivAt (hillState Q lam v)
      ((hillState Q lam v x).2, -(lam + (Q x : ℂ)) * (hillState Q lam v x).1) x := by
  unfold hillState
  simpa only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.comp_apply, hillCoefficient_apply] using
    ((ContinuousLinearMap.apply ℂ (ℂ × ℂ) v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x
      (hasDerivAt_propagator_left (continuous_hillCoefficient (lam := lam) hQ) x 0)

private theorem hasDerivAt_fst_hillState_integrable {a b : ℝ}
    (hQ : MeasureTheory.IntegrableOn Q (Icc a b)) (h₀ : 0 ∈ Icc a b)
    (v : ℂ × ℂ) {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt (fun t ↦ (hillState Q lam v t).1) (hillState Q lam v x).2 x := by
  have hP := integrableOn_hillCoefficient (lam := lam) hQ
  have hc : ContinuousOn (fun t ↦ propagator (hillCoefficient Q lam) t 0 v) (Icc a b) :=
    (continuousOn_propagator_left hP h₀).clm_apply continuousOn_const
  have hs := continuous_snd.comp_continuousOn hc
  have hi : IntervalIntegrable (fun t ↦ (propagator (hillCoefficient Q lam) t 0 v).2)
      MeasureTheory.volume 0 x :=
    (hs.mono (uIcc_subset_Icc h₀ (Ioo_subset_Icc_self hx))).intervalIntegrable
  have hd := (intervalIntegral.integral_hasDerivAt_right hi
    ((hs.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx)
    (hs.continuousAt (Icc_mem_nhds hx.1 hx.2))).const_add v.1
  refine hd.congr_of_eventuallyEq <| Filter.eventually_of_mem (Icc_mem_nhds hx.1 hx.2)
    fun t ht ↦ ?_
  have h := congrArg Prod.fst (propagator_apply_eq_add_integral hP h₀ ht v)
  have hI := hP.clm_apply_continuousOn hc isCompact_Icc
  have hp := (ContinuousLinearMap.fst ℝ ℂ ℂ).intervalIntegral_comp_comm
    ((hI.mono_set (uIcc_subset_Icc h₀ ht)).intervalIntegrable)
  simp only [ContinuousLinearMap.coe_fst'] at hp
  rw [Prod.fst_add, ← hp] at h
  simp only [hillCoefficient_apply] at h
  simpa only [hillState] using h

private theorem hasDerivAt_fst_hillState (hQ : Continuous Q) (v : ℂ × ℂ) (x : ℝ) :
    HasDerivAt (fun t ↦ (hillState Q lam v t).1) (hillState Q lam v x).2 x :=
  (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x
    (hasDerivAt_hillState (lam := lam) hQ v x)

private theorem isHillSolution_fst_hillState (hQ : Continuous Q) (v : ℂ × ℂ) :
    IsHillSolution Q lam (fun x ↦ (hillState Q lam v x).1) :=
  isHillSolution_of_hasDerivAt
    (((continuous_const.add (Complex.continuous_ofReal.comp hQ)).neg).mul
      (continuous_iff_continuousAt.mpr
        (fun x ↦ (hasDerivAt_fst_hillState (lam := lam) hQ v x).continuousAt)))
    (hasDerivAt_fst_hillState hQ v) fun x ↦
    (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x
      (hasDerivAt_hillState (lam := lam) hQ v x)

private theorem differentiable_hillState_parameter (x : ℝ)
    (hQ : MeasureTheory.IntegrableOn Q (uIcc 0 x)) (v : ℂ × ℂ) :
    Differentiable ℂ (fun lam ↦ hillState Q lam v x) := by
  let A := jacobiODECoeffVariation (1 : ℂ →L[ℂ] ℂ)
  have hB := integrableOn_hillCoefficient (lam := 0) hQ
  have h (z : ℂ) : hillCoefficient Q z = fun r ↦ z • A + hillCoefficient Q 0 r :=
    funext (hillCoefficient_eq_smul_add (lam := z))
  have heq : (fun z ↦ hillState Q z v x) =
      fun z ↦ propagator (fun r ↦ z • A + hillCoefficient Q 0 r) x 0 v :=
    funext fun z ↦ congrArg (fun P ↦ propagator P x 0 v) (h z)
  rw [heq]
  exact (differentiable_propagator_smul_add A hB
    (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 x) (right_mem_uIcc : x ∈ uIcc 0 x)).clm_apply
    (differentiable_const v)

private theorem analyticOnNhd_deriv_fst_hillState {a b : ℝ}
    (hQ : MeasureTheory.IntegrableOn Q (Icc a b)) (h₀ : 0 ∈ Icc a b)
    (v : ℂ × ℂ) {x : ℝ} (hx : x ∈ Ioo a b) :
    AnalyticOnNhd ℂ (fun lam ↦ deriv (fun t ↦ (hillState Q lam v t).1) x) univ := by
  simp_rw [(hasDerivAt_fst_hillState_integrable hQ h₀ v hx).deriv]
  have h := (differentiable_hillState_parameter x
    (hQ.mono_set (uIcc_subset_Icc h₀ (Ioo_subset_Icc_self hx))) v).snd
  exact h.differentiableOn.analyticOnNhd isOpen_univ

/-- The first fundamental solution of Hill's equation, with value one and derivative zero
at the origin for continuous `Q`. -/
noncomputable def hillWI (Q : ℝ → ℝ) (lam : ℂ) (x : ℝ) : ℂ :=
  (hillState Q lam (1, 0) x).1

/-- The second fundamental solution of Hill's equation, with value zero and derivative one
at the origin for continuous `Q`. -/
noncomputable def hillWII (Q : ℝ → ℝ) (lam : ℂ) (x : ℝ) : ℂ :=
  (hillState Q lam (0, 1) x).1

/-- The first fundamental solution is the first coordinate of the propagated initial data,
without any regularity assumption on the potential. -/
theorem hillWI_eq_propagator_apply (x : ℝ) :
    hillWI Q lam x = (propagator (hillCoefficient Q lam) x 0 (1, 0)).1 := by rfl

/-- The second fundamental solution is the first coordinate of the propagated initial data,
without any regularity assumption on the potential. -/
theorem hillWII_eq_propagator_apply (x : ℝ) :
    hillWII Q lam x = (propagator (hillCoefficient Q lam) x 0 (0, 1)).1 := by rfl

/-- The initial value of the first fundamental solution. -/
@[simp] theorem hillWI_zero : hillWI Q lam 0 = 1 := by simp [hillWI]

/-- The initial value of the second fundamental solution. -/
@[simp] theorem hillWII_zero : hillWII Q lam 0 = 0 := by simp [hillWII]

/-- The initial derivative of the first fundamental solution. -/
theorem deriv_hillWI_zero {a b : ℝ}
    (hQ : MeasureTheory.IntegrableOn Q (Icc a b)) (h₀ : 0 ∈ Ioo a b) :
    deriv (hillWI Q lam) 0 = 0 := by
  unfold hillWI
  simpa only [hillState_zero] using
    (hasDerivAt_fst_hillState_integrable (lam := lam) hQ (Ioo_subset_Icc_self h₀) (1, 0) h₀).deriv

/-- The initial derivative of the second fundamental solution. -/
theorem deriv_hillWII_zero {a b : ℝ}
    (hQ : MeasureTheory.IntegrableOn Q (Icc a b)) (h₀ : 0 ∈ Ioo a b) :
    deriv (hillWII Q lam) 0 = 1 := by
  unfold hillWII
  simpa only [hillState_zero] using
    (hasDerivAt_fst_hillState_integrable (lam := lam) hQ (Ioo_subset_Icc_self h₀) (0, 1) h₀).deriv

/-- The first fundamental solution solves Hill's equation. -/
theorem isHillSolution_hillWI (hQ : Continuous Q) : IsHillSolution Q lam (hillWI Q lam) :=
  isHillSolution_fst_hillState hQ (1, 0)

/-- The second fundamental solution solves Hill's equation. -/
theorem isHillSolution_hillWII (hQ : Continuous Q) : IsHillSolution Q lam (hillWII Q lam) :=
  isHillSolution_fst_hillState hQ (0, 1)

/-- For fixed time, the first fundamental solution is entire in the spectral parameter when
`Q` is integrable on the segment from zero to that time. -/
theorem analyticOnNhd_hillWI (x : ℝ) (hQ : MeasureTheory.IntegrableOn Q (uIcc 0 x)) :
    AnalyticOnNhd ℂ (fun lam ↦ hillWI Q lam x) univ :=
  (differentiable_hillState_parameter x hQ (1, 0)).fst.differentiableOn.analyticOnNhd isOpen_univ

/-- For fixed time, the second fundamental solution is entire in the spectral parameter when
`Q` is integrable on the segment from zero to that time. -/
theorem analyticOnNhd_hillWII (x : ℝ) (hQ : MeasureTheory.IntegrableOn Q (uIcc 0 x)) :
    AnalyticOnNhd ℂ (fun lam ↦ hillWII Q lam x) univ :=
  (differentiable_hillState_parameter x hQ (0, 1)).fst.differentiableOn.analyticOnNhd isOpen_univ

/-- For fixed time, the time derivative of the first fundamental solution is entire in the
spectral parameter when `Q` is integrable on an interval containing zero and having the
evaluation time in its interior. -/
theorem analyticOnNhd_deriv_hillWI {a b : ℝ}
    (hQ : MeasureTheory.IntegrableOn Q (Icc a b)) (h₀ : 0 ∈ Icc a b)
    {x : ℝ} (hx : x ∈ Ioo a b) :
    AnalyticOnNhd ℂ (fun lam ↦ deriv (hillWI Q lam) x) univ :=
  analyticOnNhd_deriv_fst_hillState hQ h₀ (1, 0) hx

/-- For fixed time, the time derivative of the second fundamental solution is entire in the
spectral parameter when `Q` is integrable on an interval containing zero and having the
evaluation time in its interior. -/
theorem analyticOnNhd_deriv_hillWII {a b : ℝ}
    (hQ : MeasureTheory.IntegrableOn Q (Icc a b)) (h₀ : 0 ∈ Icc a b)
    {x : ℝ} (hx : x ∈ Ioo a b) :
    AnalyticOnNhd ℂ (fun lam ↦ deriv (hillWII Q lam) x) univ :=
  analyticOnNhd_deriv_fst_hillState hQ h₀ (0, 1) hx

private theorem fst_hillState_eq_linearCombination (a b : ℂ) :
    (fun x ↦ (hillState Q lam (a, b) x).1) =
      fun x ↦ a * hillWI Q lam x + b * hillWII Q lam x := by
  funext x
  have hv : (a, b) = a • ((1, 0) : ℂ × ℂ) + b • ((0, 1) : ℂ × ℂ) := by
    simp [Prod.smul_mk]
  conv_lhs => rw [hv]
  simp only [hillState, hillWI, hillWII, map_add, map_smul, Prod.fst_add, Prod.smul_fst,
    smul_eq_mul]

/-- The propagated initial data are the value and derivative of the corresponding
linear combination of the normalized Hill pair. -/
theorem propagator_hill_apply_eq_value_deriv {l r : ℝ}
    (hQ : MeasureTheory.IntegrableOn Q (Icc l r)) (h₀ : 0 ∈ Icc l r)
    (a b : ℂ) {x : ℝ} (hx : x ∈ Ioo l r) :
    let w := fun t ↦ a * hillWI Q lam t + b * hillWII Q lam t
    propagator (hillCoefficient Q lam) x 0 (a, b) =
      (w x, deriv w x) := by
  rw [← hillState_eq_propagator_apply]
  apply Prod.ext
  · exact congrFun (fst_hillState_eq_linearCombination a b) x
  · exact (hasDerivAt_fst_hillState_integrable (lam := lam) hQ h₀ (a, b) hx).deriv.symm.trans
      (congrArg (fun f : ℝ → ℂ ↦ deriv f x) (fst_hillState_eq_linearCombination a b))

/-- A linear combination of the fundamental solutions again solves Hill's equation. -/
theorem isHillSolution_linearCombination (hQ : Continuous Q) (a b : ℂ) :
    IsHillSolution Q lam (fun x ↦ a * hillWI Q lam x + b * hillWII Q lam x) := by
  rw [← fst_hillState_eq_linearCombination]
  exact isHillSolution_fst_hillState hQ (a, b)

/-- A Hill solution is the linear combination of the fundamental solutions with coefficients
equal to its initial value and initial derivative. -/
theorem IsHillSolution.eq_linearCombination (hw : IsHillSolution Q lam w) (x : ℝ)
    (hQ : MeasureTheory.IntegrableOn Q (uIcc 0 x)) :
    w x = w 0 * hillWI Q lam x + deriv w 0 * hillWII Q lam x := by
  have h := congrArg Prod.fst (hw.eq_propagator_apply x 0 hQ)
  rw [← hillState_eq_propagator_apply] at h
  exact h.trans (congrFun (fst_hillState_eq_linearCombination (w 0) (deriv w 0)) x)

/-- A classical Hill solution is exactly a unique linear combination of the normalized pair.
The unique coefficient pair is its value and first derivative at zero. -/
theorem isHillSolution_iff_existsUnique_linearCombination (hQ : Continuous Q) :
    IsHillSolution Q lam w ↔ ∃! c : ℂ × ℂ,
      w = fun x ↦ c.1 * hillWI Q lam x + c.2 * hillWII Q lam x := by
  constructor
  · intro hw
    refine ⟨(w 0, deriv w 0), funext (fun x ↦ hw.eq_linearCombination x hQ.integrableOn_Icc), ?_⟩
    rintro ⟨a, b⟩ hc
    have h₀ : w 0 = a := by simpa using congrFun hc 0
    have h₁ : deriv w 0 = b := by
      rw [hc]
      simpa using (congrArg Prod.snd
        (propagator_hill_apply_eq_value_deriv (lam := lam) (a := a) (b := b) (x := 0)
          (l := -1) (r := 1) hQ.integrableOn_Icc (by constructor <;> norm_num)
          (by constructor <;> norm_num))).symm
    exact Prod.ext h₀.symm h₁.symm
  · rintro ⟨c, hc, _⟩
    rw [hc]
    exact isHillSolution_linearCombination hQ c.1 c.2

/-- The Wronskian of the ordered fundamental pair of Hill solutions is one. -/
@[simp] theorem hill_wronskian_eq_one (hQ : Continuous Q) (x : ℝ) :
    hillWI Q lam x * deriv (hillWII Q lam) x - deriv (hillWI Q lam) x * hillWII Q lam x = 1 := by
  have hI := isHillSolution_hillWI (lam := lam) hQ
  have hII := isHillSolution_hillWII (lam := lam) hQ
  rw [mul_comm (deriv (hillWI Q lam) x)]
  exact wronskian_eq_one_of_hasDerivAt
    (fun t ↦ (hII.contDiff.differentiable (by norm_num) t).hasDerivAt) hII.hasDerivAt_deriv
    (fun t ↦ (hI.contDiff.differentiable (by norm_num) t).hasDerivAt) hI.hasDerivAt_deriv
    hillWII_zero (deriv_hillWII_zero hQ.integrableOn_Icc
      (by norm_num : (0 : ℝ) ∈ Ioo (-1) 1)) hillWI_zero x

/-- Translating a solution by any period of the potential gives another solution. -/
theorem IsHillSolution.comp_add_period (hw : IsHillSolution Q lam w)
    {p : ℝ} (hp : Function.Periodic Q p) : IsHillSolution Q lam (fun x ↦ w (x + p)) := by
  refine ⟨hw.contDiff.comp (contDiff_id.add contDiff_const), fun x ↦ ?_⟩
  simpa only [iteratedDeriv_comp_add_const, hp x] using hw.iteratedDeriv_two (x + p)

/-- Translation by a period acts on the solution by re-expanding its value and derivative at
the end of that period in the fundamental pair. Applied to the two basic solutions at
`p = π`, this gives DLMF 28.29.4–5. -/
theorem IsHillSolution.add_period_eq (hw : IsHillSolution Q lam w)
    {p : ℝ} (hp : Function.Periodic Q p) (x : ℝ)
    (hQ : MeasureTheory.IntegrableOn Q (uIcc 0 x)) :
    w (x + p) = w p * hillWI Q lam x + deriv w p * hillWII Q lam x := by
  simpa only [deriv_comp_add_const, zero_add] using
    (hw.comp_add_period hp).eq_linearCombination x hQ

/-- Conjugation takes solutions at `λ` to solutions at the conjugate spectral parameter. -/
theorem IsHillSolution.conj (hw : IsHillSolution Q lam w) :
    IsHillSolution Q (conj lam) (fun x ↦ conj (w x)) := by
  refine ⟨Complex.conjCLE.contDiff.comp hw.contDiff, fun x ↦ ?_⟩
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, ← Complex.star_def, deriv.star']
  rw [(hw.hasDerivAt_deriv x).deriv]
  simp

private theorem conj_fst_hillState (hQ : Continuous Q) (v : ℂ × ℂ) :
    (fun t ↦ conj (hillState Q lam v t).1) =
      fun t ↦ (hillState Q (conj lam) (conj v.1, conj v.2) t).1 := by
  refine (isHillSolution_fst_hillState (lam := lam) hQ v).conj.eq_of_initial_data
    (isHillSolution_fst_hillState hQ (conj v.1, conj v.2)) hQ.locallyIntegrable
    (x := 0) (by simp) ?_
  simp only [← Complex.star_def, deriv.star,
    (hasDerivAt_fst_hillState hQ _ 0).deriv, hillState_zero]

/-- Conjugating the first fundamental solution conjugates its spectral parameter. -/
@[simp] theorem conj_hillWI (hQ : Continuous Q) (x : ℝ) :
    conj (hillWI Q lam x) = hillWI Q (conj lam) x := by
  simpa only [hillWI, map_one, map_zero] using
    congrFun (conj_fst_hillState (lam := lam) hQ (1, 0)) x

/-- Conjugating the second fundamental solution conjugates its spectral parameter. -/
@[simp] theorem conj_hillWII (hQ : Continuous Q) (x : ℝ) :
    conj (hillWII Q lam x) = hillWII Q (conj lam) x := by
  simpa only [hillWII, map_one, map_zero] using
    congrFun (conj_fst_hillState (lam := lam) hQ (0, 1)) x

/-- Conjugation commutes with the time derivative and conjugates the spectral parameter. -/
@[simp] theorem conj_deriv_hillWI (hQ : Continuous Q) (x : ℝ) :
    conj (deriv (hillWI Q lam) x) = deriv (hillWI Q (conj lam)) x := by
  have h := congrArg (fun f : ℝ → ℂ ↦ deriv f x)
    (funext (conj_hillWI (lam := lam) hQ))
  simpa only [← Complex.star_def, deriv.star'] using h

/-- Conjugation commutes with the time derivative and conjugates the spectral parameter. -/
@[simp] theorem conj_deriv_hillWII (hQ : Continuous Q) (x : ℝ) :
    conj (deriv (hillWII Q lam) x) = deriv (hillWII Q (conj lam)) x := by
  have h := congrArg (fun f : ℝ → ℂ ↦ deriv f x)
    (funext (conj_hillWII (lam := lam) hQ))
  simpa only [← Complex.star_def, deriv.star'] using h

/-- At a real spectral parameter the first fundamental solution is real-valued. -/
@[simp] theorem hillWI_ofReal_im (hQ : Continuous Q) (a x : ℝ) :
    (hillWI Q (a : ℂ) x).im = 0 :=
  Complex.conj_eq_iff_im.mp (by simpa using conj_hillWI (lam := (a : ℂ)) hQ x)

/-- At a real spectral parameter the second fundamental solution is real-valued. -/
@[simp] theorem hillWII_ofReal_im (hQ : Continuous Q) (a x : ℝ) :
    (hillWII Q (a : ℂ) x).im = 0 :=
  Complex.conj_eq_iff_im.mp (by simpa using conj_hillWII (lam := (a : ℂ)) hQ x)

/-- The first fundamental solution has a real first derivative at a real spectral parameter. -/
@[simp] theorem deriv_hillWI_ofReal_im (hQ : Continuous Q) (a x : ℝ) :
    (deriv (hillWI Q (a : ℂ)) x).im = 0 :=
  Complex.conj_eq_iff_im.mp (by simpa using conj_deriv_hillWI (lam := (a : ℂ)) hQ x)

/-- The second fundamental solution has a real first derivative at a real spectral parameter. -/
@[simp] theorem deriv_hillWII_ofReal_im (hQ : Continuous Q) (a x : ℝ) :
    (deriv (hillWII Q (a : ℂ)) x).im = 0 :=
  Complex.conj_eq_iff_im.mp (by simpa using conj_deriv_hillWII (lam := (a : ℂ)) hQ x)

/-- The cosine and the normalized sine satisfy the zero-potential equation with their
respective initial slopes. -/
private theorem hill_zero_potential_data (k : ℂ) :
    (IsHillSolution 0 (k ^ 2) (fun x ↦ Complex.cos (k * (x : ℂ))) ∧
      deriv (fun x : ℝ ↦ Complex.cos (k * (x : ℂ))) 0 = 0) ∧
    (k ≠ 0 → IsHillSolution 0 (k ^ 2) (fun x ↦ Complex.sin (k * (x : ℂ)) / k) ∧
      deriv (fun x : ℝ ↦ Complex.sin (k * (x : ℂ)) / k) 0 = 1) := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ ↦ k * (t : ℂ)) k t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul k
  have hc (t : ℝ) : HasDerivAt (fun s : ℝ ↦ Complex.cos (k * (s : ℂ)))
      (-k * Complex.sin (k * (t : ℂ))) t := by
    simpa [Function.comp_def] using (Complex.hasDerivAt_cos _).scomp t (hd t)
  have hs (t : ℝ) : HasDerivAt (fun s : ℝ ↦ Complex.sin (k * (s : ℂ)))
      (k * Complex.cos (k * (t : ℂ))) t := by
    simpa [Function.comp_def] using (Complex.hasDerivAt_sin _).scomp t (hd t)
  constructor
  · refine ⟨isHillSolution_of_hasDerivAt (by fun_prop) hc (fun t ↦ ?_), by simp [(hc 0).deriv]⟩
    exact ((hs t).const_mul (-k)).congr_deriv (by simp; ring)
  · intro hk
    have h (t : ℝ) : HasDerivAt (fun s : ℝ ↦ Complex.sin (k * (s : ℂ)) / k)
        (Complex.cos (k * (t : ℂ))) t := by simpa [hk] using (hs t).div_const k
    refine ⟨isHillSolution_of_hasDerivAt (by fun_prop) h (fun t ↦ ?_), by simp [(h 0).deriv]⟩
    exact (hc t).congr_deriv (by simp; field_simp)

/-- In zero potential the first solution is the cosine of a square root of the spectral
parameter times the real variable. -/
theorem hillWI_zero_potential (k : ℂ) (x : ℝ) :
    hillWI 0 (k ^ 2) x = Complex.cos (k * (x : ℂ)) := by
  obtain ⟨hc, hd⟩ := (hill_zero_potential_data k).1
  have hQ : Continuous (0 : ℝ → ℝ) := continuous_const
  exact congrFun ((isHillSolution_hillWI hQ).eq_of_initial_data hc hQ.locallyIntegrable
    (x := 0) (by simp) (by
      simpa only [deriv_hillWI_zero hQ.integrableOn_Icc
        (by norm_num : (0 : ℝ) ∈ Ioo (-1) 1)] using hd.symm)) x

/-- In zero potential and at a nonzero spectral parameter, the second solution is the sine of
a square root of the parameter times the variable, divided by that square root. -/
theorem hillWII_zero_potential {k : ℂ} (hk : k ≠ 0) (x : ℝ) :
    hillWII 0 (k ^ 2) x = Complex.sin (k * (x : ℂ)) / k := by
  obtain ⟨hs, hd⟩ := (hill_zero_potential_data k).2 hk
  have hQ : Continuous (0 : ℝ → ℝ) := continuous_const
  exact congrFun ((isHillSolution_hillWII hQ).eq_of_initial_data hs hQ.locallyIntegrable
    (x := 0) (by simp) (by
      simpa only [deriv_hillWII_zero hQ.integrableOn_Icc
        (by norm_num : (0 : ℝ) ∈ Ioo (-1) 1)] using hd.symm)) x

/-- In zero potential and at spectral parameter zero, the second solution is the identity. -/
@[simp] theorem hillWII_zero_potential_zero (x : ℝ) : hillWII 0 0 x = (x : ℂ) := by
  have heq : hillCoefficient 0 0 = fun _ ↦ jacobiODECoeff (0 : ℂ →L[ℂ] ℂ) := by
    funext t
    unfold hillCoefficient
    congr 1
    ext
    simp
  rw [hillWII_eq_propagator_apply, heq, propagator_const, sub_zero]
  -- Fix the canonical complex operator algebra before using the algebraic exponential identity.
  change ((NormedSpace.exp ((x : ℂ) • jacobiODECoeff (0 : ℂ →L[ℂ] ℂ))) (0, 1)).1 = (x : ℂ)
  have hsq : ((x : ℂ) • jacobiODECoeff (0 : ℂ →L[ℂ] ℂ)) ^ 2 = 0 := by
    ext <;> simp [pow_two, jacobiODECoeff_apply]
  rw [NormedSpace.exp_eq_one_add_of_sq_eq_zero (𝕂 := ℂ) hsq]
  simp [jacobiODECoeff_apply]

end TauCeti
