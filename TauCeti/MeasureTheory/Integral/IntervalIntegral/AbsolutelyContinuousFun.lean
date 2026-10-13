/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Calculus along absolutely continuous curves

Mathlib's `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` is the fundamental theorem of
calculus for an absolutely continuous real function. This file composes it with a `C¹` function:
if `γ : ℝ → F` is an absolutely continuous curve in a normed space with derivative `V t` at almost
every time and `φ : F → ℝ` is `C¹`, then `∫_a^b φ'(γ t) (V t) dt = φ (γ b) - φ (γ a)`.
In finite dimension, it also extends Mathlib's real-valued differentiation, derivative
integrability, and fundamental-theorem results to curves.

## Main results

* `AbsolutelyContinuousOnInterval.integral_fderiv_apply_eq_sub`: the fundamental theorem of
  calculus for the composition of a `C¹` function with an absolutely continuous curve.
* `AbsolutelyContinuousOnInterval.intervalIntegrable_of_ae_hasDerivAt`: the almost-everywhere
  derivative of an absolutely continuous curve in a finite-dimensional space is interval
  integrable.
* `AbsolutelyContinuousOnInterval.ae_differentiableAt_of_finiteDimensional`: an absolutely
  continuous curve in a finite-dimensional space is differentiable almost everywhere.
* `AbsolutelyContinuousOnInterval.intervalIntegrable_deriv_of_finiteDimensional` and
  `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub_of_finiteDimensional`: integrability and
  the fundamental theorem for the canonical derivative of such a curve.
-/

public section

open MeasureTheory Set

namespace AbsolutelyContinuousOnInterval

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {γ V : ℝ → F} {a b : ℝ}

/-- An absolutely continuous curve in a finite-dimensional real normed space is differentiable
almost everywhere on its parameter interval. -/
theorem ae_differentiableAt_of_finiteDimensional [FiniteDimensional ℝ F]
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    ∀ᵐ t, t ∈ uIcc a b → DifferentiableAt ℝ γ t := by
  let e := (Module.finBasis ℝ F).equivFun.toContinuousLinearEquiv
  have hcoord (i : Fin (Module.finrank ℝ F)) :
      ∀ᵐ t, t ∈ uIcc a b → DifferentiableAt ℝ (fun t ↦ e (γ t) i) t := by
    let L : F →L[ℝ] ℝ := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ ℝ) i).comp
      (e : F →L[ℝ] _)
    exact (L.lipschitzWith.comp_absolutelyContinuousOnInterval hγ).ae_differentiableAt
  filter_upwards [Filter.eventually_all.mpr hcoord] with t ht hmem
  apply e.comp_differentiableAt_iff.mp
  exact differentiableAt_pi.mpr fun i ↦ ht i hmem

/-- *Fundamental theorem of calculus* along an absolutely continuous curve: if `γ` is absolutely
continuous on `uIcc a b` with derivative `V t` at almost every `t ∈ uIoc a b` and `φ` is `C¹`, then
`∫ t in a..b, fderiv ℝ φ (γ t) (V t) = φ (γ b) - φ (γ a)`. The composition `φ ∘ γ` is absolutely
continuous because `φ` is Lipschitz on the compact image `γ '' uIcc a b`. -/
theorem integral_fderiv_apply_eq_sub (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hV : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt γ (V t) t) {φ : F → ℝ} (hφ : ContDiff ℝ 1 φ) :
    ∫ t in a..b, fderiv ℝ φ (γ t) (V t) = φ (γ b) - φ (γ a) := by
  obtain ⟨K, hK⟩ := hφ.locallyLipschitz.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_uIcc.image_of_continuousOn hγ.continuousOn)
  refine Eq.trans (intervalIntegral.integral_congr_ae ?_)
    (hK.comp_absolutelyContinuousOnInterval (mapsTo_image _ _) hγ).integral_deriv_eq_sub
  filter_upwards [hV] with t ht hmem
  exact (HasFDerivAt.comp_hasDerivAt t (hφ.differentiable one_ne_zero (γ t)).hasFDerivAt
    (ht hmem)).deriv.symm

/-- The almost-everywhere derivative `V` of a curve `γ` which is absolutely continuous on
`uIcc a b` in a finite-dimensional real normed space is interval integrable on `a..b`. This reduces
to Mathlib's real-valued `AbsolutelyContinuousOnInterval.intervalIntegrable_deriv` in the
coordinates of a basis. -/
theorem intervalIntegrable_of_ae_hasDerivAt [FiniteDimensional ℝ F]
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hV : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt γ (V t) t) :
    IntervalIntegrable V volume a b := by
  let e := (Module.finBasis ℝ F).equivFun.toContinuousLinearEquiv
  rw [intervalIntegrable_iff, IntegrableOn, ← e.integrable_comp_iff,
    integrable_pi_iff]
  intro i
  let L : F →L[ℝ] ℝ := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ ℝ) i).comp (e : F →L[ℝ] _)
  refine (intervalIntegrable_iff.1
    (L.lipschitzWith.comp_absolutelyContinuousOnInterval hγ).intervalIntegrable_deriv).congr ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [hV] with t ht hmem
  exact (L.hasFDerivAt.comp_hasDerivAt t (ht hmem)).deriv

/-- The derivative of an absolutely continuous curve in a finite-dimensional real normed space
is interval integrable. -/
theorem intervalIntegrable_deriv_of_finiteDimensional [FiniteDimensional ℝ F]
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    IntervalIntegrable (deriv γ) volume a b := by
  apply hγ.intervalIntegrable_of_ae_hasDerivAt
  filter_upwards [hγ.ae_differentiableAt_of_finiteDimensional] with t ht hmem
  exact (ht (uIoc_subset_uIcc hmem)).hasDerivAt

/-- The fundamental theorem of calculus for the almost-everywhere derivative of an absolutely
continuous curve in a finite-dimensional real normed space. -/
theorem integral_eq_sub_of_ae_hasDerivAt [FiniteDimensional ℝ F]
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hV : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt γ (V t) t) :
    ∫ t in a..b, V t = γ b - γ a := by
  let e := (Module.finBasis ℝ F).equivFun.toContinuousLinearEquiv
  apply e.injective
  ext i
  let L : F →L[ℝ] ℝ := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ ℝ) i).comp
    (e : F →L[ℝ] _)
  -- Express equality of the chosen coordinates through their continuous linear projection.
  change L (∫ t in a..b, V t) = L (γ b - γ a)
  rw [← L.intervalIntegral_comp_comm (hγ.intervalIntegrable_of_ae_hasDerivAt hV), L.map_sub]
  refine Eq.trans (intervalIntegral.integral_congr_ae ?_)
    (L.lipschitzWith.comp_absolutelyContinuousOnInterval hγ).integral_deriv_eq_sub
  filter_upwards [hV] with t ht hmem
  exact (L.hasFDerivAt.comp_hasDerivAt t (ht hmem)).deriv.symm

/-- The fundamental theorem of calculus for an absolutely continuous curve in a
finite-dimensional real normed space. -/
theorem integral_deriv_eq_sub_of_finiteDimensional [FiniteDimensional ℝ F]
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    ∫ t in a..b, deriv γ t = γ b - γ a := by
  apply hγ.integral_eq_sub_of_ae_hasDerivAt
  filter_upwards [hγ.ae_differentiableAt_of_finiteDimensional] with t ht hmem
  exact (ht (uIoc_subset_uIcc hmem)).hasDerivAt

end AbsolutelyContinuousOnInterval
