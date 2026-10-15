/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
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
* `AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul_of_ae_hasDerivAt`:
  integration by parts with supplied almost-everywhere derivatives.
* `ContinuousOn.absolutelyContinuousOnInterval_of_hasDerivAt_off_countable`: a continuous curve
  with an integrable derivative off a countable set is absolutely continuous.
* `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral'`: indefinite integrals
  with base point in the integrability interval are absolutely continuous in any real normed space.
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
  refine Eq.trans (intervalIntegral.integral_congr_ae ?_)
    (hγ.comp_of_contDiffAt fun _ _ ↦ hφ.contDiffAt).integral_deriv_eq_sub
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

/-- For two absolutely continuous curves with the same left endpoint, their pointwise distance
is bounded by the `L¹` difference of their velocities over the whole interval. -/
theorem norm_sub_le_integral_norm_deriv_sub [FiniteDimensional ℝ F] {p : ℝ → F}
    (hp : AbsolutelyContinuousOnInterval p a b) (hγ : AbsolutelyContinuousOnInterval γ a b)
    (ha : p a = γ a) {t : ℝ} (ht : t ∈ Icc a b) :
    ‖p t - γ t‖ ≤ ∫ v in a..b, ‖deriv p v - deriv γ v‖ := by
  have hpI := hp.intervalIntegrable_deriv_of_finiteDimensional
  have hγI := hγ.intervalIntegrable_deriv_of_finiteDimensional
  have hsub : uIcc a t ⊆ uIcc a b := uIcc_subset_uIcc left_mem_uIcc
    ((uIcc_of_le (ht.1.trans ht.2)).symm ▸ ht)
  have heq : ∫ v in a..t, deriv p v - deriv γ v = p t - γ t := by
    rw [intervalIntegral.integral_sub (hpI.mono_set hsub) (hγI.mono_set hsub),
      (hp.mono hsub).integral_deriv_eq_sub_of_finiteDimensional,
      (hγ.mono hsub).integral_deriv_eq_sub_of_finiteDimensional, ha]
    abel
  rw [← heq]
  exact (intervalIntegral.norm_integral_le_integral_norm ht.1).trans
    (intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _) (hpI.sub hγI).norm)

omit [NormedSpace ℝ F] in
/-- An AC curve is almost everywhere measurable on the ordered half-open parameter interval. -/
theorem aemeasurable_restrict_Ioc [MeasurableSpace F] [BorelSpace F]
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hab : a ≤ b) :
    AEMeasurable γ (volume.restrict (Ioc a b)) :=
  (hγ.continuousOn.mono
    (fun _ ht ↦ (uIcc_of_le hab).symm ▸ Ioc_subset_Icc_self ht)).aemeasurable measurableSet_Ioc

/-- The derivative of a finite-dimensional AC curve is integrable on the ordered half-open
parameter interval. -/
theorem integrableOn_deriv_Ioc [FiniteDimensional ℝ F]
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hab : a ≤ b) :
    IntegrableOn (deriv γ) (Ioc a b) := by
  simpa only [uIoc_of_le hab] using hγ.intervalIntegrable_deriv_of_finiteDimensional.def'

end AbsolutelyContinuousOnInterval

namespace AbsolutelyContinuousOnInterval

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]
  {f f' g g' : ℝ → A} {a b : ℝ}

/-- **Integration by parts** for absolutely continuous functions valued in a finite-dimensional
real normed ring. The derivatives may be supplied only almost everywhere. -/
theorem integral_mul_deriv_eq_deriv_mul_of_ae_hasDerivAt
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hff' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt f (f' t) t)
    (hgg' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt g (g' t) t) :
    ∫ t in a..b, f t * g' t = f b * g b - f a * g a - ∫ t in a..b, f' t * g t := by
  have hprod : AbsolutelyContinuousOnInterval (fun t ↦ f t * g t) a b := by
    have hmul : ContDiff ℝ 1 (fun p : A × A ↦ p.1 * p.2) := contDiff_mul
    exact (hf.prodMk hg).comp_of_contDiffAt (φ := fun p : A × A ↦ p.1 * p.2)
      (fun _ _ ↦ hmul.contDiffAt)
  have hder : ∀ᵐ t, t ∈ uIoc a b →
      HasDerivAt (fun t ↦ f t * g t) (f' t * g t + f t * g' t) t := by
    filter_upwards [hff', hgg'] with t ht hu hmem
    exact (ht hmem).mul (hu hmem)
  have h := hprod.integral_eq_sub_of_ae_hasDerivAt hder
  rw [intervalIntegral.integral_add
    ((hf.intervalIntegrable_of_ae_hasDerivAt hff').mul_continuousOn hg.continuousOn)
    ((hg.intervalIntegrable_of_ae_hasDerivAt hgg').continuousOn_mul hf.continuousOn)] at h
  exact eq_sub_of_add_eq' h

end AbsolutelyContinuousOnInterval

/-- An indefinite interval integral in a real normed space is absolutely continuous on its
integrability interval, provided its base point belongs to that interval. -/
theorem IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral'
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {a b c : ℝ} (hf : IntervalIntegrable f volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun t ↦ ∫ v in c..t, f v) a b := by
  have hn := hf.norm.absolutelyContinuousOnInterval_intervalIntegral hc
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ ↦
    Finset.sum_nonneg fun _ _ ↦ dist_nonneg) ?_ hn
  have he : ∀ᶠ E in AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
      Filter.principal (AbsolutelyContinuousOnInterval.disjWithin a b),
      E ∈ AbsolutelyContinuousOnInterval.disjWithin a b :=
    Filter.eventually_inf_principal.mpr (by simp)
  filter_upwards [he] with E hE
  apply Finset.sum_le_sum
  intro i hi
  have hx := hf.mono_set (uIcc_subset_uIcc hc (hE.1 i hi).1)
  have hy := hf.mono_set (uIcc_subset_uIcc hc (hE.1 i hi).2)
  rw [dist_eq_norm, intervalIntegral.integral_interval_sub_left hx hy,
    Real.dist_eq, intervalIntegral.integral_interval_sub_left hx.norm hy.norm]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

/-- A continuous curve with an integrable derivative outside a countable exceptional set is
absolutely continuous on its parameter interval. -/
theorem ContinuousOn.absolutelyContinuousOnInterval_of_hasDerivAt_off_countable
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f f' : ℝ → F} {a b : ℝ} {s : Set ℝ} (hf : ContinuousOn f (uIcc a b))
    (hs : s.Countable)
    (hd : ∀ t ∈ Ioo (min a b) (max a b) \ s, HasDerivAt f (f' t) t)
    (hi : IntervalIntegrable f' volume a b) : AbsolutelyContinuousOnInterval f a b := by
  have hbase : min a b ∈ uIcc a b := ⟨le_rfl, min_le_max⟩
  have hI := hi.absolutelyContinuousOnInterval_intervalIntegral' hbase
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ f (min a b)) a b :=
    (LipschitzWith.const (f (min a b))).lipschitzOnWith.absolutelyContinuousOnInterval
  apply (hc.add hI).congr
  intro t ht
  have hsub : uIcc (min a b) t ⊆ uIcc a b := uIcc_subset_uIcc hbase ht
  have hFTC := integral_eq_of_hasDerivAt_off_countable f f' hs (hf.mono hsub)
    (fun u hu ↦ hd u ⟨⟨by simpa only [min_eq_left ht.1] using hu.1.1,
      (by simpa only [max_eq_right ht.1] using hu.1.2 : u < t).trans_le ht.2⟩, hu.2⟩)
    (hi.mono_set hsub)
  change f (min a b) + (∫ u in min a b..t, f' u) = f t
  rw [hFTC]
  abel
