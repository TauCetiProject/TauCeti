/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Calculus along absolutely continuous curves

Mathlib's `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` is the fundamental theorem of
calculus for an absolutely continuous real function. This file composes it with a `C¹` function:
if `γ : ℝ → F` is an absolutely continuous curve in a normed space with derivative `V t` at almost
every time and `φ : F → ℝ` is `C¹`, then `∫_a^b φ'(γ t) (V t) dt = φ (γ b) - φ (γ a)`.
In finite dimension, it also extends Mathlib's real-valued derivative integrability and
fundamental-theorem results to curves.

## Main results

* `AbsolutelyContinuousOnInterval.integral_fderiv_apply_eq_sub`: the fundamental theorem of
  calculus for the composition of a `C¹` function with an absolutely continuous curve.
* `AbsolutelyContinuousOnInterval.intervalIntegrable_of_ae_hasDerivAt`: the almost-everywhere
  derivative of an absolutely continuous curve in a finite-dimensional space is interval
  integrable.
* `AbsolutelyContinuousOnInterval.integral_eq_sub_of_ae_hasDerivAt`: the fundamental theorem for
  the almost-everywhere derivative of an absolutely continuous curve in finite dimension.
* `AbsolutelyContinuousOnInterval.intervalIntegrable_deriv_of_finiteDimensional` and
  `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub_of_finiteDimensional`: integrability and
  the fundamental theorem for the canonical derivative of such a curve.
* `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_of_finiteDimensional`:
  indefinite integrals of interval-integrable functions in finite dimension are absolutely
  continuous.
-/

public section

open MeasureTheory Set

namespace AbsolutelyContinuousOnInterval

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {γ V : ℝ → F} {a b : ℝ}

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
  filter_upwards [hγ.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with t ht hmem
  exact (ht (uIoc_subset_uIcc hmem)).hasDerivAt

/-- The fundamental theorem of calculus for the almost-everywhere derivative of an absolutely
continuous curve in a finite-dimensional real normed space. -/
theorem integral_eq_sub_of_ae_hasDerivAt [FiniteDimensional ℝ F]
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hV : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt γ (V t) t) :
    ∫ t in a..b, V t = γ b - γ a := by
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun g ↦ ?_
  rw [← g.intervalIntegral_comp_comm (hγ.intervalIntegrable_of_ae_hasDerivAt hV), map_sub]
  simpa [g.fderiv] using hγ.integral_fderiv_apply_eq_sub hV g.contDiff

/-- The fundamental theorem of calculus for an absolutely continuous curve in a
finite-dimensional real normed space. -/
theorem integral_deriv_eq_sub_of_finiteDimensional [FiniteDimensional ℝ F]
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    ∫ t in a..b, deriv γ t = γ b - γ a := by
  apply hγ.integral_eq_sub_of_ae_hasDerivAt
  filter_upwards [hγ.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with t ht hmem
  exact (ht (uIoc_subset_uIcc hmem)).hasDerivAt

end AbsolutelyContinuousOnInterval

/-- An indefinite interval integral with values in a finite-dimensional real normed space is
absolutely continuous on every interval on which its integrand is interval integrable. -/
theorem IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_of_finiteDimensional
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : ℝ → F} {a b c : ℝ} (hf : IntervalIntegrable f volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun t ↦ ∫ v in c..t, f v) a b := by
  let B := Module.finBasis ℝ F
  let e := B.equivFun.toContinuousLinearEquiv
  let L (i : Fin (Module.finrank ℝ F)) : F →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ ℝ) i).comp (e : F →L[ℝ] _)
  have hcoord (i) : AbsolutelyContinuousOnInterval
      (fun t ↦ (∫ v in c..t, L i (f v)) • B i) a b := by
    have hi : IntervalIntegrable (fun t ↦ L i (f t)) volume a b :=
      ⟨(L i).integrable_comp hf.1, (L i).integrable_comp hf.2⟩
    exact hi.absolutelyContinuousOnInterval_intervalIntegral hc |>.smul
      (LipschitzOnWith.absolutelyContinuousOnInterval (LipschitzWith.const (B i)).lipschitzOnWith)
  have hsum (s : Finset (Fin (Module.finrank ℝ F))) : AbsolutelyContinuousOnInterval
      (fun t ↦ ∑ i ∈ s, (∫ v in c..t, L i (f v)) • B i) a b := by
    induction s using Finset.induction_on with
    | empty =>
      simpa using LipschitzOnWith.absolutelyContinuousOnInterval
        (LipschitzWith.const (α := ℝ) (0 : F)).lipschitzOnWith
    | @insert i s hi ih => simpa [Finset.sum_insert hi] using (hcoord i).fun_add ih
  apply (hsum Finset.univ).congr
  intro t ht
  simp_rw [(L _).intervalIntegral_comp_comm (hf.mono_set (uIcc_subset_uIcc hc ht))]
  exact B.sum_equivFun _
