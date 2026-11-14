/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import TauCeti.MeasureTheory.Integral.OddSymmetric
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-!
# Symmetry of Gaussian measures

A centered Gaussian measure on a real separable Banach space is invariant under negation.
Consequently, an odd function of a Gaussian vector centered at its mean has integral zero.
This applies in particular to odd products of centered linear observables, without assuming
independence or a nonsingular covariance.
The standard real Gaussian product law is also invariant under planar reflections, centered
real Gaussian laws assign equal mass to opposite half-lines (giving positive-variance half-line
mass `1 / 2`), and centered real Gaussian laws and their independent products are invariant under
multiplication by deterministic scalars of unit modulus.
-/

public section

noncomputable section

open MeasureTheory

namespace ProbabilityTheory.IsGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- A Gaussian measure with mean zero is invariant under negation. -/
@[simp]
theorem map_neg_eq_self (μ : Measure E) [IsGaussian μ] (hμ : (∫ x, x ∂μ) = 0) :
    μ.map (fun x ↦ -x) = μ := by
  apply Measure.ext_of_charFunDual
  ext L
  calc
    _ = charFunDual μ (-L) := by
      rw [charFunDual_apply, charFunDual_apply,
        integral_map (by fun_prop) (by fun_prop)]
      simp
    _ = _ := by
      simp only [charFunDual_eq, integral_complex_ofReal, FunLike.coe_neg, Pi.neg_apply,
        integral_neg, variance_neg, integral_dual, hμ, map_zero, neg_zero]

/-- An odd function of a Gaussian vector centered at its mean has integral zero.
The statement also holds for nonintegrable functions, with the usual Bochner integral
totalization. -/
theorem integral_comp_sub_eq_zero_of_odd (μ : Measure E) [IsGaussian μ]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : Function.Odd f) : (∫ x, f (x - μ[id]) ∂μ) = 0 := by
  let ν := μ.map (fun x ↦ x - μ[id])
  have hν : ν[id] = 0 := by
    rw [integral_map (by fun_prop) (by fun_prop)]
    simp only [id_eq]
    rw [integral_sub integrable_fun_id (integrable_const _), integral_const]
    simp
  have : ν.IsNegInvariant := ⟨map_neg_eq_self ν hν⟩
  calc
    _ = ∫ x, f x ∂ν := by
      simpa only [ν, MeasurableEquiv.coe_addRight, sub_eq_add_neg] using
        (integral_map_equiv (μ := μ) (MeasurableEquiv.addRight (-μ[id])) f).symm
    _ = 0 := integral_eq_zero_of_odd hf

end ProbabilityTheory.IsGaussian

namespace TauCeti.Probability

open ProbabilityTheory Real Set
open scoped NNReal ENNReal Pointwise

/-- Every centered real Gaussian law is invariant under negation. -/
instance isNegInvariant_gaussianReal_zero (v : ℝ≥0) : (gaussianReal 0 v).IsNegInvariant :=
  ⟨by simp [Measure.neg_def]⟩

/-- Twice the closed upper half-line mass of a centered real Gaussian law is at least `1`,
including the degenerate case `v = 0`. -/
theorem one_le_two_mul_gaussianReal_Ici (v : ℝ≥0) :
    (1 : ℝ≥0∞) ≤ 2 * gaussianReal 0 v (Ici 0) := by
  have hneg : gaussianReal 0 v (Iic 0) = gaussianReal 0 v (Ici 0) := by
    simpa only [Set.neg_preimage, Set.neg_Ici, neg_zero] using
      Measure.measure_preimage_neg (gaussianReal 0 v) (Ici (0 : ℝ))
  calc (1 : ℝ≥0∞) = gaussianReal 0 v (Iic 0 ∪ Ici 0) := by rw [Iic_union_Ici, measure_univ]
    _ ≤ gaussianReal 0 v (Iic 0) + gaussianReal 0 v (Ici 0) := measure_union_le _ _
    _ = 2 * gaussianReal 0 v (Ici 0) := by rw [hneg, two_mul]

/-- Twice the strict upper half-line mass of a centered real Gaussian law is at most `1`,
including the degenerate case `v = 0`. -/
theorem two_mul_gaussianReal_Ioi_le_one (v : ℝ≥0) :
    2 * gaussianReal 0 v (Ioi 0) ≤ (1 : ℝ≥0∞) := by
  have hneg : gaussianReal 0 v (Iio 0) = gaussianReal 0 v (Ioi 0) := by
    simpa only [Set.neg_preimage, Set.neg_Ioi, neg_zero] using
      Measure.measure_preimage_neg (gaussianReal 0 v) (Ioi (0 : ℝ))
  have hdisj : Disjoint (Iio (0 : ℝ)) (Ioi 0) :=
    disjoint_left.mpr fun _ (hx₁ : _ < 0) (hx₂ : 0 < _) ↦ (hx₁.trans hx₂).false
  calc 2 * gaussianReal 0 v (Ioi 0)
      = gaussianReal 0 v (Iio 0) + gaussianReal 0 v (Ioi 0) := by rw [hneg, two_mul]
    _ = gaussianReal 0 v (Iio 0 ∪ Ioi 0) := (measure_union hdisj measurableSet_Ioi).symm
    _ ≤ 1 := (measure_mono (subset_univ _)).trans_eq measure_univ

/-- For a nondegenerate centered real Gaussian law, twice the strict upper half-line mass is `1`. -/
theorem two_mul_gaussianReal_Ioi_eq_one {v : ℝ≥0} (hv : v ≠ 0) :
    2 * gaussianReal 0 v (Ioi 0) = (1 : ℝ≥0∞) :=
  have := nullSingletonClass_gaussianReal (μ := 0) hv
  le_antisymm (two_mul_gaussianReal_Ioi_le_one v)
    (measure_congr (μ := gaussianReal 0 v) (Ioi_ae_eq_Ici (a := (0 : ℝ))) ▸
      one_le_two_mul_gaussianReal_Ici v)

/-- The standard Gaussian product law is invariant under reflection across a line. -/
theorem measurePreserving_reflection_gaussianReal (θ : ℝ) :
    MeasurePreserving
      (fun p : ℝ × ℝ => (cos θ * p.1 + sin θ * p.2, sin θ * p.1 - cos θ * p.2))
      (Measure.prod (gaussianReal 0 1) (gaussianReal 0 1))
      (Measure.prod (gaussianReal 0 1) (gaussianReal 0 1)) := by
  have hrot : MeasurePreserving (ContinuousLinearMap.rotation θ : ℝ × ℝ →L[ℝ] ℝ × ℝ)
      (Measure.prod (gaussianReal 0 1) (gaussianReal 0 1))
      (Measure.prod (gaussianReal 0 1) (gaussianReal 0 1)) :=
    ⟨by fun_prop, IsGaussian.map_rotation_eq_self (μ := gaussianReal 0 1)
      (by simp [integral_id_gaussianReal]) _⟩
  have hneg : MeasurePreserving (fun x : ℝ => -x) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨by fun_prop, by simp⟩
  convert ((MeasurePreserving.id (gaussianReal 0 1)).prod hneg).comp hrot using 1
  funext p
  simp [ContinuousLinearMap.rotation_apply, sub_eq_add_neg, add_comm]

end TauCeti.Probability

namespace ProbabilityTheory

open scoped NNReal

/-- Multiplying a centered real Gaussian random variable by a scalar of unit modulus preserves its
law. -/
theorem HasLaw.gaussianReal_const_mul_of_abs_eq_one {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) P)
    {c : ℝ} (hc : |c| = 1) :
    HasLaw (fun ω ↦ c * X ω) (gaussianReal 0 v) P := by
  have hc2 : NNReal.mk (c ^ 2) (sq_nonneg c) = 1 :=
    NNReal.eq (by simp [← sq_abs, hc])
  simpa [hc2] using gaussianReal_const_mul hX c

/-- Multiplying independent centered real Gaussian random variables by deterministic signs `η i`
with `|η i| = 1` preserves their joint product law. -/
theorem iIndepFun.hasLaw_pi_mul_gaussianReal_of_abs_eq_one {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] {P : Measure Ω} {g : ι → Ω → ℝ} {σ : ι → ℝ≥0}
    (hindep : iIndepFun g P) (hlaw : ∀ i, HasLaw (g i) (gaussianReal 0 (σ i)) P)
    {η : ι → ℝ} (hη : ∀ i, |η i| = 1) :
    HasLaw (fun ω i ↦ η i * g i ω) (Measure.pi fun i ↦ gaussianReal 0 (σ i)) P :=
  (hindep.comp (fun i x ↦ η i * x) fun _ ↦ by fun_prop).hasLaw_pi fun i ↦
    (hlaw i).gaussianReal_const_mul_of_abs_eq_one (hη i)

end ProbabilityTheory
