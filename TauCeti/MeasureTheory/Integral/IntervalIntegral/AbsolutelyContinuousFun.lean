/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp

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
* `AbsolutelyContinuousOnInterval.integral_div_eq_log_sub_log`: the fundamental theorem for the
  logarithmic derivative of a nonvanishing absolutely continuous real function.
* `AbsolutelyContinuousOnInterval.ae_hasDerivAt_and_eq_zero_imp_deriv_eq_zero_of_nonneg` and
  `AbsolutelyContinuousOnInterval.sqrt_sub_sqrt_eq_intervalIntegral`: a nonnegative absolutely
  continuous real function has zero derivative almost everywhere on its zero set, and when
  `deriv η / (2 √η)` is interval integrable, `√(η b) - √(η a) = ∫_a^b deriv η / (2 √η)`.
* `TauCeti.Probability.survival_eq_exp_integral_hazard`: a positive absolutely continuous
  survival function is reconstructed from its hazard rate.
* `ContinuousOn.absolutelyContinuousOnInterval_of_hasDerivAt_off_countable`: a continuous curve
  with an integrable derivative off a countable set is absolutely continuous.
* `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral'`: indefinite integrals
  with base point in the integrability interval are absolutely continuous in any real normed space.
* `IntervalIntegrable.integral_mul_pow_integral`: for a real `g` with primitive `G` based at `c`,
  `∫ s in c..d, g s * G s ^ k = G d ^ (k + 1) / (k + 1)`;
  `IntervalIntegrable.abs_integral_mul_abs_pow_integral` is its form with `|G|` for nonnegative `g`.
* `TauCeti.abs_integral_norm_mul_abs_pow`: with `Λ s = ∫ r in t₀..s, ‖M r‖`,
  `|∫ s in t₀..t, ‖M s‖ * |Λ s| ^ n| = |Λ t| ^ (n + 1) / (n + 1)`, and
  `TauCeti.norm_integral_le_abs_integral_norm_pow_div_factorial_mul`, the resulting inductive step
  of factorial bounds on iterated integrals.
* `IntervalIntegrable.absolutelyContinuousOnInterval_of_eq_integral` and
  `MeasureTheory.LocallyIntegrable.ae_hasDerivAt_of_eq_integral`: a function represented as an
  indefinite interval integral is absolutely continuous on every subinterval and is differentiable
  almost everywhere with the integrand as its derivative.

## References

* P. J. Bickel, C. A. J. Klaassen, Y. Ritov, and J. A. Wellner, *Efficient and Adaptive Estimation
  for Semiparametric Models*, Johns Hopkins University Press, 1993, Appendix A.5, Corollary 1
  (citing J. Hájek and Z. Šidák, *Theory of Rank Tests*, Academic Press, 1967).
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

/-- The derivative of a finite-dimensional AC curve is integrable on the ordered half-open
parameter interval. -/
theorem integrableOn_deriv_Ioc [FiniteDimensional ℝ F]
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    IntegrableOn (deriv γ) (Ioc a b) :=
  hγ.intervalIntegrable_deriv_of_finiteDimensional.1

/-- If an interval-integrable function `s` approximates the velocity of `γ` in `L¹` on `(a, b]`
to within `ε`, then the endpoint defect `γ b - γ a - ∫ s` has norm at most `ε`. For `a < b`, this
says that the average correction `(γ b - γ a - ∫ s) / (b - a)` to `s` has norm at most
`ε / (b - a)`. -/
theorem norm_sub_integral_le [FiniteDimensional ℝ F]
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hab : a ≤ b) {s : ℝ → F}
    (hsi : IntervalIntegrable s volume a b) {ε : ℝ}
    (hg : (∫ t in Ioc a b, ‖s t - deriv γ t‖) ≤ ε) :
    ‖γ b - γ a - ∫ t in a..b, s t‖ ≤ ε := by
  have hγi := hγ.intervalIntegrable_deriv_of_finiteDimensional
  have hEq : γ b - γ a - ∫ t in a..b, s t = ∫ t in a..b, deriv γ t - s t := by
    rw [intervalIntegral.integral_sub hγi hsi, hγ.integral_deriv_eq_sub_of_finiteDimensional]
  rw [hEq]
  apply (intervalIntegral.norm_integral_le_integral_norm hab).trans
  simpa only [intervalIntegral.integral_of_le hab, norm_sub_rev] using hg

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

namespace AbsolutelyContinuousOnInterval

variable {f V : ℝ → ℝ} {a b : ℝ}

private theorem ae_hasDerivAt_log (h0 : ∀ t ∈ uIcc a b, f t ≠ 0)
    (hV : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt f (V t) t) :
    ∀ᵐ t, t ∈ uIoc a b → HasDerivAt (fun t ↦ Real.log (f t)) (V t / f t) t := by
  filter_upwards [hV] with t ht hmem
  exact (ht hmem).log (h0 t (uIoc_subset_uIcc hmem))

/-- The logarithmic derivative `V / f` of an absolutely continuous real function `f` that does not
vanish on the interval is interval integrable, where `V` is the derivative of `f` at almost every
point. -/
theorem intervalIntegrable_div_of_ae_hasDerivAt (hf : AbsolutelyContinuousOnInterval f a b)
    (h0 : ∀ t ∈ uIcc a b, f t ≠ 0) (hV : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt f (V t) t) :
    IntervalIntegrable (fun t ↦ V t / f t) volume a b :=
  (hf.log h0).intervalIntegrable_of_ae_hasDerivAt (ae_hasDerivAt_log h0 hV)

/-- The fundamental theorem of calculus for the logarithmic derivative: if `f` is absolutely
continuous and nonvanishing on the interval, with derivative `V` at almost every point, then
`∫ t in a..b, V t / f t = log (f b) - log (f a)`. -/
theorem integral_div_eq_log_sub_log (hf : AbsolutelyContinuousOnInterval f a b)
    (h0 : ∀ t ∈ uIcc a b, f t ≠ 0) (hV : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt f (V t) t) :
    ∫ t in a..b, V t / f t = Real.log (f b) - Real.log (f a) :=
  (hf.log h0).integral_eq_sub_of_ae_hasDerivAt (ae_hasDerivAt_log h0 hV)

/-- If a nonnegative function `η : ℝ → ℝ` is absolutely continuous on `uIcc a b`, then for almost
every `u ∈ uIoc a b`, `η` is differentiable at `u` and `η u = 0` implies `deriv η u = 0`. -/
theorem ae_hasDerivAt_and_eq_zero_imp_deriv_eq_zero_of_nonneg {η : ℝ → ℝ}
    (hac : AbsolutelyContinuousOnInterval η a b) (hη : ∀ x ∈ uIcc a b, 0 ≤ η x) :
    ∀ᵐ u ∂volume, u ∈ uIoc a b → HasDerivAt η (deriv η u) u ∧ (η u = 0 → deriv η u = 0) := by
  have hne_max : ∀ᵐ u ∂volume, u ≠ max a b := by simp [ae_iff, measure_singleton]
  filter_upwards [hac.ae_differentiableAt, hne_max] with u hdiff hne hu
  refine ⟨(hdiff (uIoc_subset_uIcc hu)).hasDerivAt, fun hu0 ↦ ?_⟩
  have hu_ioo : u ∈ Ioo (min a b) (max a b) := ⟨hu.1, lt_of_le_of_ne hu.2 hne⟩
  have hmin : IsLocalMin η u := by
    refine Filter.mem_of_superset (isOpen_Ioo.mem_nhds hu_ioo) fun y hy ↦ ?_
    rw [hu0]
    exact hη y (Ioo_subset_Icc_self hy)
  exact hmin.deriv_eq_zero

/-- **Increments of a square-root function** (Bickel–Klaassen–Ritov–Wellner, Appendix A.5,
Corollary 1, part A, after Hájek–Šidák). If `η : ℝ → ℝ` is nonnegative and absolutely continuous on
`uIcc a b`, and `deriv η / (2 √η)` is interval integrable on `a..b`, then
`√(η b) - √(η a) = ∫ u in a..b, deriv η u / (2 √(η u))`. -/
theorem sqrt_sub_sqrt_eq_intervalIntegral {η : ℝ → ℝ}
    (hac : AbsolutelyContinuousOnInterval η a b) (hη : ∀ x ∈ uIcc a b, 0 ≤ η x)
    (hint : IntervalIntegrable (fun u ↦ deriv η u / (2 * Real.sqrt (η u))) volume a b) :
    Real.sqrt (η b) - Real.sqrt (η a) = ∫ u in a..b, deriv η u / (2 * Real.sqrt (η u)) := by
  -- Step 1: Differentiability and zero-minimum property a.e. on `uIoc a b` (following the direct
  -- argument of Hájek–Šidák as cited in Bickel–Klaassen–Ritov–Wellner, Appendix A.5, Corollary 1).
  have hae := hac.ae_hasDerivAt_and_eq_zero_imp_deriv_eq_zero_of_nonneg hη
  have hη_asm : AEStronglyMeasurable η (volume.restrict (uIoc a b)) :=
    (hac.continuousOn.mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have hd_asm : AEStronglyMeasurable (deriv η) (volume.restrict (uIoc a b)) :=
    (intervalIntegrable_iff.mp hac.intervalIntegrable_deriv).aestronglyMeasurable
  -- Step 2: Regularize `η` to `η + ε` (`ε > 0`), compose with the `C¹` function `y ↦ √(y + ε)`,
  -- and apply the fundamental theorem of calculus for absolutely continuous functions.
  have hftc : ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
      (∫ u in a..b, deriv η u / (2 * Real.sqrt (η u + ε))) =
        Real.sqrt (η b + ε) - Real.sqrt (η a + ε) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have hf_ac : AbsolutelyContinuousOnInterval (fun u ↦ Real.sqrt (η u + ε)) a b :=
      hac.comp_of_contDiffAt (φ := fun y ↦ Real.sqrt (y + ε)) fun _ ⟨u, hu, heq⟩ ↦
        (contDiffAt_id.add contDiffAt_const).sqrt
          (by rw [← heq]; exact (add_pos_of_nonneg_of_pos (hη u hu) hε).ne')
    refine hf_ac.integral_eq_sub_of_ae_hasDerivAt ?_
    filter_upwards [hae] with u hu hmem
    exact ((hu hmem).1.add_const ε).sqrt
      (add_pos_of_nonneg_of_pos (hη u (uIoc_subset_uIcc hmem)) hε).ne'
  -- Step 3: Pass to the limit `ε → 0⁺` via dominated convergence with bound `‖deriv η / (2 √η)‖`.
  have hlim_lhs : Filter.Tendsto (fun ε : ℝ ↦ ∫ u in a..b, deriv η u / (2 * Real.sqrt (η u + ε)))
      (nhdsWithin 0 (Ioi 0)) (nhds (∫ u in a..b, deriv η u / (2 * Real.sqrt (η u)))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun u ↦ ‖deriv η u / (2 * Real.sqrt (η u))‖) ?_ ?_ hint.norm ?_
    · exact Filter.Eventually.of_forall fun ε ↦
        (hd_asm.aemeasurable.div
          (aemeasurable_const.mul (hη_asm.aemeasurable.add_const ε).sqrt)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      filter_upwards [hae] with u hu hmem
      rcases eq_or_ne (η u) 0 with h0 | h0
      · simp [(hu hmem).2 h0]
      · have hpos : 0 < η u := lt_of_le_of_ne (hη u (uIoc_subset_uIcc hmem)) (Ne.symm h0)
        simp only [Real.norm_eq_abs, abs_div,
          abs_of_pos (by positivity : 0 < 2 * Real.sqrt (η u + ε)),
          abs_of_pos (by positivity : 0 < 2 * Real.sqrt (η u))]
        gcongr; linarith
    · filter_upwards [hae] with u hu hmem
      rcases eq_or_ne (η u) 0 with h0 | h0
      · simp [(hu hmem).2 h0]
      · have hpos : 0 < η u := lt_of_le_of_ne (hη u (uIoc_subset_uIcc hmem)) (Ne.symm h0)
        have hden_ne : 2 * Real.sqrt (η u + 0) ≠ 0 := by rw [add_zero]; positivity
        have hc : ContinuousAt (fun ε : ℝ ↦ deriv η u / (2 * Real.sqrt (η u + ε))) 0 :=
          ContinuousAt.div continuousAt_const
            (continuousAt_const.mul ((continuousAt_const.add continuousAt_id).sqrt)) hden_ne
        simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hlim_rhs : Filter.Tendsto (fun ε : ℝ ↦ Real.sqrt (η b + ε) - Real.sqrt (η a + ε))
      (nhdsWithin 0 (Ioi 0)) (nhds (Real.sqrt (η b) - Real.sqrt (η a))) := by
    have hc : Continuous fun ε : ℝ ↦ Real.sqrt (η b + ε) - Real.sqrt (η a + ε) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique hlim_rhs (hlim_lhs.congr' hftc)

end AbsolutelyContinuousOnInterval

namespace TauCeti.Probability

variable {f : ℝ → ℝ} {a x : ℝ}

/-- **Survival reconstruction from the hazard rate.** If `S` is absolutely continuous on the
interval between `a` and `x`, is positive there, and has derivative `-f` almost everywhere, then
the hazard rate `f / S` is interval integrable and
`S x = S a * exp (-∫ t in a..x, f t / S t)`. -/
theorem survival_eq_exp_integral_hazard {S : ℝ → ℝ}
    (hS : AbsolutelyContinuousOnInterval S a x) (hpos : ∀ t ∈ uIcc a x, 0 < S t)
    (hderiv : ∀ᵐ t, t ∈ uIoc a x → HasDerivAt S (-f t) t) :
    IntervalIntegrable (fun t => f t / S t) volume a x ∧
      S x = S a * Real.exp (-∫ t in a..x, f t / S t) := by
  have hne : ∀ t ∈ uIcc a x, S t ≠ 0 := fun t ht => (hpos t ht).ne'
  have hint : IntervalIntegrable (fun t => f t / S t) volume a x := by
    have h : (fun t => f t / S t) = -fun t => -f t / S t := by
      ext t
      simp [neg_div]
    rw [h]
    exact (hS.intervalIntegrable_div_of_ae_hasDerivAt hne hderiv).neg
  refine ⟨hint, ?_⟩
  have h := hS.integral_div_eq_log_sub_log hne hderiv
  simp only [neg_div, intervalIntegral.integral_neg] at h
  have ha : 0 < S a := hpos a left_mem_uIcc
  have hx : 0 < S x := hpos x right_mem_uIcc
  rw [h, Real.exp_sub, Real.exp_log hx, Real.exp_log ha]
  field_simp

end TauCeti.Probability

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

/-- For `g` interval integrable on `c..d`, with primitive `G s = ∫ u in c..s, g u`, the integral
of `g * G ^ k` over `c..d` is `G d ^ (k + 1) / (k + 1)`, whatever the order of `c` and `d`. This
is the finite-interval form of `MeasureTheory.IntegrableOn.integral_Ioi_mul_pow_integral_Ioi`;
it gives the factorial decay of the Picard iterates of linear equations with integrable
coefficients. -/
theorem IntervalIntegrable.integral_mul_pow_integral {g : ℝ → ℝ} {c d : ℝ}
    (hg : IntervalIntegrable g volume c d) (k : ℕ) :
    ∫ s in c..d, g s * (∫ u in c..s, g u) ^ k = (∫ u in c..d, g u) ^ (k + 1) / (k + 1) := by
  set G : ℝ → ℝ := fun s ↦ ∫ u in c..s, g u
  have hpow : AbsolutelyContinuousOnInterval (fun s ↦ G s ^ (k + 1)) c d :=
    (hg.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).comp_of_contDiffAt
      (φ := fun x : ℝ ↦ x ^ (k + 1)) fun _ _ ↦ (contDiff_id.pow _).contDiffAt
  have hderiv : ∀ᵐ s, s ∈ uIoc c d →
      deriv (fun s ↦ G s ^ (k + 1)) s = (k + 1) * (g s * G s ^ k) := by
    filter_upwards [hg.ae_hasDerivAt_integral] with s hs hsI
    rw [((hs (uIoc_subset_uIcc hsI) c left_mem_uIcc).fun_pow (k + 1)).deriv]
    push_cast
    ring
  have h := hpow.integral_deriv_eq_sub
  rw [intervalIntegral.integral_congr_ae hderiv, intervalIntegral.integral_const_mul] at h
  simp only [G, intervalIntegral.integral_same, zero_pow k.succ_ne_zero, sub_zero] at h
  rw [← h]
  field_simp

/-- For `g` interval integrable and almost everywhere nonnegative between `c` and `d`, with
primitive `G s = ∫ u in c..s, g u`, the integral of `g * |G| ^ k` over `c..d` has absolute value
`|G d| ^ (k + 1) / (k + 1)`, whatever the order of `c` and `d`. -/
theorem IntervalIntegrable.abs_integral_mul_abs_pow_integral {g : ℝ → ℝ} {c d : ℝ}
    (hg : IntervalIntegrable g volume c d) (hg₀ : ∀ᵐ s ∂volume.restrict (uIcc c d), 0 ≤ g s)
    (k : ℕ) :
    |∫ s in c..d, g s * |∫ u in c..s, g u| ^ k| = |∫ u in c..d, g u| ^ (k + 1) / (k + 1) := by
  set G : ℝ → ℝ := fun s ↦ ∫ u in c..s, g u
  -- `G` has a constant sign `σ` between `c` and `d`.
  obtain ⟨σ, hσ, hG⟩ : ∃ σ : ℝ, |σ| = 1 ∧ ∀ s ∈ uIcc c d, |G s| = σ * G s := by
    rcases le_total c d with h | h
    · rw [uIcc_of_le h] at hg₀
      refine ⟨1, abs_one, fun s hs ↦ ?_⟩
      rw [uIcc_of_le h] at hs
      rw [one_mul, abs_of_nonneg (intervalIntegral.integral_nonneg_of_ae_restrict hs.1
        (ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc_right hs.2) hg₀))]
    · rw [uIcc_of_ge h] at hg₀
      refine ⟨-1, by simp, fun s hs ↦ ?_⟩
      rw [uIcc_of_ge h] at hs
      rw [neg_one_mul, abs_of_nonpos]
      simp only [G]
      rw [intervalIntegral.integral_symm, neg_nonpos]
      exact intervalIntegral.integral_nonneg_of_ae_restrict hs.2
        (ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc_left hs.1) hg₀)
  have h : ∫ s in c..d, g s * |G s| ^ k = σ ^ k * ∫ s in c..d, g s * G s ^ k := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    simp only [hG s hs, mul_pow]
    ring
  rw [h, hg.integral_mul_pow_integral]
  simp [abs_mul, abs_div, abs_pow, hσ, abs_of_pos (by positivity : (0 : ℝ) < k + 1)]

namespace TauCeti

open intervalIntegral
open scoped Nat

/-- With `Λ s = ∫ r in t₀..s, ‖M r‖` for a function `M` into a normed group, the integral of
`‖M‖ |Λ| ^ n` from `t₀` to `t` is `|Λ t| ^ (n + 1) / (n + 1)`, in either order of `t₀` and `t`. -/
theorem abs_integral_norm_mul_abs_pow {G : Type*} [NormedAddCommGroup G] {M : ℝ → G} {t₀ t : ℝ}
    (hM : IntervalIntegrable (fun s ↦ ‖M s‖) volume t₀ t) (n : ℕ) :
    |∫ s in t₀..t, ‖M s‖ * |∫ r in t₀..s, ‖M r‖| ^ n| =
      |∫ s in t₀..t, ‖M s‖| ^ (n + 1) / (n + 1) :=
  hM.abs_integral_mul_abs_pow_integral (.of_forall fun _ ↦ norm_nonneg _) n

/-- **The inductive step of a factorial bound.** With `Λ r = ∫ u in t₀..r, ‖M u‖` for a function
`M` into a normed group, if `‖f r‖ ≤ ‖M r‖ * (|Λ r| ^ n / n! * K)` for almost every `r` between
`t₀` and `t`, with `0 ≤ K`, then `‖∫ r in t₀..t, f r‖ ≤ |Λ t| ^ (n + 1) / (n + 1)! * K`. -/
theorem norm_integral_le_abs_integral_norm_pow_div_factorial_mul {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] {f : ℝ → F} {M : ℝ → G}
    {t₀ t K : ℝ} (hK : 0 ≤ K) (hM : IntervalIntegrable (fun s ↦ ‖M s‖) volume t₀ t) {n : ℕ}
    (hf : ∀ᵐ r ∂volume.restrict (uIoc t₀ t),
      ‖f r‖ ≤ ‖M r‖ * (|∫ u in t₀..r, ‖M u‖| ^ n / n ! * K)) :
    ‖∫ r in t₀..t, f r‖ ≤ |∫ r in t₀..t, ‖M r‖| ^ (n + 1) / (n + 1)! * K := by
  refine (norm_integral_le_abs_of_norm_le hf (hM.mul_continuousOn
    ((((continuousOn_primitive_interval' hM left_mem_uIcc).abs.pow n).div_const _).mul
      continuousOn_const))).trans_eq ?_
  have : (fun s ↦ ‖M s‖ * (|∫ r in t₀..s, ‖M r‖| ^ n / n ! * K)) =
      fun s ↦ K / n ! * (‖M s‖ * |∫ r in t₀..s, ‖M r‖| ^ n) := by
    ext s
    ring
  rw [this, intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg (by positivity),
    abs_integral_norm_mul_abs_pow hM, Nat.factorial_succ]
  push_cast
  field_simp

end TauCeti

/-- A continuous curve with an integrable derivative outside a countable exceptional set is
absolutely continuous on its parameter interval. -/
theorem ContinuousOn.absolutelyContinuousOnInterval_of_hasDerivAt_off_countable
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f f' : ℝ → F} {a b : ℝ} {s : Set ℝ} (hf : ContinuousOn f (uIcc a b))
    (hs : s.Countable)
    (hd : ∀ t ∈ Ioo (min a b) (max a b) \ s, HasDerivAt f (f' t) t)
    (hi : IntervalIntegrable f' volume a b) : AbsolutelyContinuousOnInterval f a b := by
  -- Embed `F` isometrically in its completion, where the fundamental theorem of calculus holds.
  let L : F →L[ℝ] UniformSpace.Completion F := UniformSpace.Completion.toComplL
  have hL : Isometry L := (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℝ) (E := F)).isometry
  rw [← hL.absolutelyContinuousOnInterval_comp_iff]
  have hf : ContinuousOn (L ∘ f) (uIcc a b) := L.continuous.comp_continuousOn hf
  have hd : ∀ t ∈ Ioo (min a b) (max a b) \ s, HasDerivAt (L ∘ f) (L (f' t)) t :=
    fun t ht ↦ L.hasFDerivAt.comp_hasDerivAt t (hd t ht)
  have hi : IntervalIntegrable (L ∘ f') volume a b := by
    rw [intervalIntegrable_iff] at hi ⊢
    exact L.integrable_comp hi
  have hbase : min a b ∈ uIcc a b := ⟨le_rfl, min_le_max⟩
  have hI := hi.absolutelyContinuousOnInterval_intervalIntegral' hbase
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ L (f (min a b))) a b :=
    (LipschitzWith.const (L (f (min a b)))).lipschitzOnWith.absolutelyContinuousOnInterval
  apply (hc.add hI).congr
  intro t ht
  have hsub : uIcc (min a b) t ⊆ uIcc a b := uIcc_subset_uIcc hbase ht
  have hFTC := integral_eq_of_hasDerivAt_off_countable (L ∘ f) (L ∘ f') hs (hf.mono hsub)
    (fun u hu ↦ hd u ⟨⟨by simpa only [min_eq_left ht.1] using hu.1.1,
      (by simpa only [max_eq_right ht.1] using hu.1.2 : u < t).trans_le ht.2⟩, hu.2⟩)
    (hi.mono_set hsub)
  simp only [Pi.add_apply, Function.comp_apply] at hFTC ⊢
  rw [hFTC]
  abel

/-- A function `f` that agrees on `uIcc a b` with `f c + ∫ t in c..x, f' t` (with `f'` interval
integrable on `c..a` and `a..b`) is absolutely continuous on `uIcc a b`. -/
theorem IntervalIntegrable.absolutelyContinuousOnInterval_of_eq_integral
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f f' : ℝ → F} {a b c : ℝ} (hca : IntervalIntegrable f' volume c a)
    (hab : IntervalIntegrable f' volume a b)
    (heq : ∀ x ∈ uIcc a b, f x = f c + ∫ t in c..x, f' t) :
    AbsolutelyContinuousOnInterval f a b := by
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ f a) a b :=
    (LipschitzWith.const (f a)).lipschitzOnWith.absolutelyContinuousOnInterval
  refine (hconst.add (hab.absolutelyContinuousOnInterval_intervalIntegral'
    left_mem_uIcc)).congr fun x hx ↦ ?_
  have hax : IntervalIntegrable f' volume a x :=
    hab.mono_set (uIcc_subset_uIcc left_mem_uIcc hx)
  simp only [Pi.add_apply]
  rw [heq x hx, heq a left_mem_uIcc, add_assoc,
    intervalIntegral.integral_add_adjacent_intervals hca hax]

/-- A function represented globally as an indefinite integral `f x = f c + ∫ t in c..x, f' t` of a
locally integrable function `f'` has derivative `f' x` at Lebesgue-almost every `x`. -/
theorem MeasureTheory.LocallyIntegrable.ae_hasDerivAt_of_eq_integral {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f f' : ℝ → F} {c : ℝ}
    (hf' : LocallyIntegrable f' volume) (heq : ∀ x, f x = f c + ∫ t in c..x, f' t) :
    ∀ᵐ x ∂volume, HasDerivAt f (f' x) x := by
  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hf'] with x hx
  rw [funext heq]
  simpa [Pi.add_def] using (hasDerivAt_const x (f c)).add (hx c)
