/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Statistics.ExponentialFamily.LogPartition

import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The mean map of a natural exponential family

The mean map of an exponential family is the gradient of its log partition function.
It is analytic in the interior of the natural parameter space. For a minimal family,
the covariance formula makes its derivative invertible and the map strictly monotone
along every nonconstant line segment, hence injective.

## References

* L. D. Brown, *Fundamentals of Statistical Exponential Families* (1986), Corollary 2.5 and
  Theorem 3.6.
-/

public section

noncomputable section

open MeasureTheory Set InnerProductSpace
open scoped RealInnerProductSpace Topology

namespace TauCeti

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ν : Measure X} {T : X → E} {η : E}

/-- The mean of an exponential family is analytic in the interior of the natural domain. -/
theorem analyticOnNhd_integral_exponentialFamilyMeasure :
    AnalyticOnNhd ℝ (fun t ↦ ∫ x, T x ∂exponentialFamilyMeasure ν T t)
      (interior (naturalParameterSpace ν T)) := by
  let R : StrongDual ℝ E →L[ℝ] E :=
    (toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  intro t ht
  refine ((R.analyticAt _).comp (analyticOnNhd_logPartition t ht).fderiv).congr ?_
  filter_upwards [isOpen_interior.mem_nhds ht] with s hs
  rw [Function.comp_apply, (hasFDerivAt_logPartition hs).fderiv]
  exact (toDual ℝ E).symm_apply_apply _

/-- Under the Riesz identification the derivative of the mean is the Hessian of the
log partition function. -/
theorem fderiv_integral_exponentialFamilyMeasure_inner
    (hη : η ∈ interior (naturalParameterSpace ν T)) (u v : E) :
    ⟪fderiv ℝ (fun t ↦ ∫ x, T x ∂exponentialFamilyMeasure ν T t) η u, v⟫ =
      fderiv ℝ (fderiv ℝ (logPartition ν T)) η u v := by
  let R := (toDual ℝ E).toContinuousLinearEquiv
  have hd := (analyticOnNhd_integral_exponentialFamilyMeasure η hη)
    |>.differentiableAt.hasFDerivAt
  have heq : (fderiv ℝ (logPartition ν T)) =ᶠ[𝓝 η]
      R.toContinuousLinearMap ∘ (fun t ↦ ∫ x, T x ∂exponentialFamilyMeasure ν T t) := by
    filter_upwards [isOpen_interior.mem_nhds hη] with s hs
    rw [(hasFDerivAt_logPartition hs).fderiv]
    ext z
    simp [R, innerSL_apply_apply, toDual_apply_apply]
  rw [((R.toContinuousLinearMap.hasFDerivAt.comp η hd).congr_of_eventuallyEq heq).fderiv]
  simp [R, ContinuousLinearMap.comp_apply, toDual_apply_apply]

/-- The mean of a minimal family has an invertible strict derivative at every interior
natural parameter. -/
theorem IsMinimalExponentialFamily.exists_hasStrictFDerivAt_integral
    (hmin : IsMinimalExponentialFamily ν T)
    (hη : η ∈ interior (naturalParameterSpace ν T)) :
    ∃ D : E ≃L[ℝ] E, HasStrictFDerivAt
      (fun t ↦ ∫ x, T x ∂exponentialFamilyMeasure ν T t) (D : E →L[ℝ] E) η := by
  let M : E → E := fun t ↦ ∫ x, T x ∂exponentialFamilyMeasure ν T t
  let D := fderiv ℝ M η
  have hker : D.ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    by_contra hne
    have hp := hmin.fderiv_fderiv_logPartition_pos hη hne
    rw [← fderiv_integral_exponentialFamilyMeasure_inner hη] at hp
    have hz : D v = 0 := hv
    have hp' : 0 < ⟪D v, v⟫ := hp
    rw [hz, inner_zero_left] at hp'
    exact (lt_irrefl (0 : ℝ)) hp'
  let e := ContinuousLinearEquiv.ofBijective D hker (LinearMap.ker_eq_bot_iff_range_eq_top.mp hker)
  refine ⟨e, ?_⟩
  rw [ContinuousLinearEquiv.coe_ofBijective]
  exact (analyticOnNhd_integral_exponentialFamilyMeasure η hη).hasStrictFDerivAt

/-- The means at two distinct interior parameters are strictly ordered in the
direction from the first parameter to the second. -/
theorem IsMinimalExponentialFamily.inner_integral_lt_of_ne
    (hmin : IsMinimalExponentialFamily ν T) {p q : E}
    (hp : p ∈ interior (naturalParameterSpace ν T))
    (hq : q ∈ interior (naturalParameterSpace ν T)) (hpq : p ≠ q) :
    ⟪(∫ x, T x ∂exponentialFamilyMeasure ν T p), q - p⟫ <
      ⟪(∫ x, T x ∂exponentialFamilyMeasure ν T q), q - p⟫ := by
  let M : E → E := fun t ↦ ∫ x, T x ∂exponentialFamilyMeasure ν T t
  let line : ℝ → E := fun t ↦ p + t • (q - p)
  let f : ℝ → ℝ := fun t ↦ ⟪M (line t), q - p⟫
  have hm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      line t ∈ interior (naturalParameterSpace ν T) := by
    have hc := (convex_naturalParameterSpace ν T).interior hp hq
      (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
    have heq : (1 - t) • p + t • q = line t := by
      dsimp only [line]
      module
    exact heq ▸ hc
  have hf (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt f ⟪fderiv ℝ M (line t) (q - p), q - p⟫ t := by
    have hd := (analyticOnNhd_integral_exponentialFamilyMeasure _ (hm t ht))
      |>.differentiableAt.hasFDerivAt
    have hl : HasDerivAt line (q - p) t := by
      simpa only [one_smul, line, id_eq] using
        ((hasDerivAt_id t).smul_const (q - p)).const_add p
    have h := ((innerSL ℝ (q - p)).hasFDerivAt.comp (line t) hd)
      |>.comp_hasDerivAt t (f := line) hl
    simpa only [f, Function.comp_def, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, real_inner_comm (x := q - p)] using h
  have hmono : StrictMonoOn f (Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
    · exact fun t ht ↦ (hf t ht).continuousAt.continuousWithinAt
    · intro t ht
      have ht' := interior_subset ht
      rw [(hf t ht').deriv, fderiv_integral_exponentialFamilyMeasure_inner (hm t ht')]
      exact hmin.fderiv_fderiv_logPartition_pos (hm t ht') (sub_ne_zero.mpr hpq.symm)
  simpa [f, line, M] using hmono (by simp : (0 : ℝ) ∈ Icc 0 1)
    (by simp : (1 : ℝ) ∈ Icc 0 1) zero_lt_one

/-- A minimal family has an injective mean map on the interior of its natural domain. -/
theorem IsMinimalExponentialFamily.injOn_integral
    (hmin : IsMinimalExponentialFamily ν T) :
    InjOn (fun t ↦ ∫ x, T x ∂exponentialFamilyMeasure ν T t)
      (interior (naturalParameterSpace ν T)) := by
  intro p hp q hq h
  by_contra hpq
  have hlt := hmin.inner_integral_lt_of_ne hp hq hpq
  have heq : (∫ x, T x ∂exponentialFamilyMeasure ν T p) =
      ∫ x, T x ∂exponentialFamilyMeasure ν T q := h
  rw [heq] at hlt
  exact lt_irrefl _ hlt

end TauCeti
