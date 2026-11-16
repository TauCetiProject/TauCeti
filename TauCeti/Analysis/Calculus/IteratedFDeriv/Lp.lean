/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
public import TauCeti.MeasureTheory.Function.Lp.Dilation
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import TauCeti.Topology.MetricSpace.Thickening
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear
import TauCeti.MeasureTheory.Function.LpSeminorm.Support

/-!
# Iterated derivative seminorms: linear changes of variables and the Euclidean Hessian

Composing a vector-valued function with a linear automorphism `e` multiplies the `Lᵖ` seminorm
of its `i`-th derivative by at most `‖e‖ ^ i * |det e|^(-1 / p)`. The estimate compares a set
with its preimage under `e`, works against any additive Haar measure on a finite-dimensional
real normed space, and requires no differentiability of the function. Only the derivative of
the composite must be a.e. strongly measurable on the preimage.

For a finite-dimensional real normed space it also records the consequence for second derivatives
of a `C²` function on a thickening: the `L²` norm of `D²u` on a thickening of a bounded set is
finite (`MeasureTheory.Measure.eLpNorm_iteratedFDeriv_two_thickening_ne_top`), and `D²(u ∘ e)` on
the preimage thickening is controlled by `D²u` through the ellipticity constants of `e`
(`MeasureTheory.Measure.toReal_eLpNorm_iteratedFDeriv_two_comp_le`).

On a finite-dimensional inner product space with an additive Haar measure, the `Lᵖ` norm of the
Hessian of a function with continuous second derivative supported in a closed ball, with all second
partial derivatives along an orthonormal basis bounded by `B`, is at most the `1/p`-th power of the
measure of the ball times `(card ι)² B`
(`MeasureTheory.Measure.toReal_eLpNorm_iteratedFDeriv_two_le_of_support_subset_closedBall`).
-/

public section

namespace ContinuousLinearEquiv

open MeasureTheory
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Under a linear change of variables `e`, the `Lᵖ` seminorm of `Dⁱ(f ∘ e)` on `e ⁻¹' s` is at
most `‖e‖ⁱ |det e|^(-1/p)` times the `Lᵖ` seminorm of `Dⁱf` on `s`, against any additive Haar
measure. The set need not be measurable, and no differentiability of `f` is required. -/
theorem eLpNorm_iteratedFDeriv_comp_right_restrict_preimage_le (e : E ≃L[ℝ] E)
    (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → F) {s : Set E} (i : ℕ) (p : ℝ≥0∞)
    (hm : AEStronglyMeasurable (iteratedFDeriv ℝ i (f ∘ e)) (μ.restrict (e ⁻¹' s))) :
    eLpNorm (iteratedFDeriv ℝ i (f ∘ e)) p (μ.restrict (e ⁻¹' s)) ≤
      ENNReal.ofReal (‖(e : E →L[ℝ] E)‖ ^ i) *
        (ENNReal.ofReal |(LinearMap.det (e : E →ₗ[ℝ] E))⁻¹| ^ (1 / p).toReal *
          eLpNorm (iteratedFDeriv ℝ i f) p (μ.restrict s)) := by
  rw [← Measure.eLpNorm_comp_continuousLinearEquiv_restrict_preimage]
  exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm
    (ae_of_all _ fun y => e.norm_iteratedFDeriv_comp_right_le f y i) p

end ContinuousLinearEquiv

namespace MeasureTheory.Measure

open Metric Set
open scoped ENNReal

section Thickening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)

/-- The `L²` norm of `D²u` on the open `R`-thickening of a bounded set `S` is finite when `u` is
`C²` on an open set containing the closed `R`-thickening. -/
theorem eLpNorm_iteratedFDeriv_two_thickening_ne_top [IsFiniteMeasureOnCompacts μ]
    {U S : Set E} {u : E → ℝ} {R : ℝ} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) (hS : Bornology.IsBounded S)
    (hSU : cthickening R S ⊆ U) :
    eLpNorm (iteratedFDeriv ℝ 2 u) 2 (μ.restrict (thickening R S)) ≠ ∞ :=
  (((ContinuousOn.continuousOn_iteratedFDeriv hu hU le_rfl).mono
    ((closure_thickening_subset_cthickening R S).trans hSU)).memLp_restrict_of_subset_isCompact
      hS.thickening.isCompact_closure isOpen_thickening.measurableSet subset_closure
        2).eLpNorm_ne_top

/-- The `L²` norm of `D²(u ∘ e)` on the `R / √Λ`-thickening of `e ⁻¹' S` is at most
`Λ λ^{-d/4}` times the `L²` norm of `D²u` on the `R`-thickening of `S`, where `d` is the dimension
of `E`. -/
theorem toReal_eLpNorm_iteratedFDeriv_two_comp_le [μ.IsAddHaarMeasure]
    {e : E ≃L[ℝ] E} {lam Lam R : ℝ} {U S : Set E} {u : E → ℝ} (hlam : 0 < lam) (hLam : 0 < Lam)
    (he' : ∀ ξ, ‖e ξ‖ ≤ √Lam * ‖ξ‖) (hesn : ‖(e.symm : E →L[ℝ] E)‖ ≤ (√lam)⁻¹)
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hS : Bornology.IsBounded S)
    (hSU : cthickening R S ⊆ U) :
    (eLpNorm (iteratedFDeriv ℝ 2 (u ∘ e)) 2
        (μ.restrict (thickening (R / √Lam) (e ⁻¹' S)))).toReal ≤
      Lam * lam ^ (-((Module.finrank ℝ E : ℝ) / 4)) *
        (eLpNorm (iteratedFDeriv ℝ 2 u) 2 (μ.restrict (thickening R S))).toReal := by
  -- `D²(u ∘ e) = D²u ∘ e (e, e)` and `|det e⁻¹| ≤ ‖e⁻¹‖^d ≤ λ^{-d/2}`.
  have hlip : LipschitzWith (√Lam).toNNReal e := LipschitzWith.of_dist_le_mul fun y y' => by
    rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _), dist_eq_norm, dist_eq_norm, ← map_sub]
    exact he' _
  have hthick : thickening (R / √Lam) (e ⁻¹' S) ⊆ e ⁻¹' thickening R S := by
    simpa only [Real.coe_toNNReal _ (Real.sqrt_nonneg _)] using
      hlip.thickening_preimage_subset_preimage_thickening (R := R) S
  have hU' : IsOpen (e ⁻¹' U) := hU.preimage e.continuous
  have hv : ContDiffOn ℝ 2 (u ∘ e) (e ⁻¹' U) :=
    hu.comp (e : E →L[ℝ] E).contDiff.contDiffOn (mapsTo_preimage _ _)
  have hdet : |(LinearMap.det (e : E →ₗ[ℝ] E))⁻¹| ≤ lam ^ (-((Module.finrank ℝ E : ℝ) / 2)) := by
    have h2 := (e.symm : E →L[ℝ] E).abs_det_le_opNorm_pow
    rw [e.det_coe_symm] at h2
    refine h2.trans ((pow_le_pow_left₀ (norm_nonneg _) hesn _).trans_eq ?_)
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hlam.le, ← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
    ring_nf
  have hT : MeasurableSet (thickening R S) := isOpen_thickening.measurableSet
  have hL2 : eLpNorm (iteratedFDeriv ℝ 2 (u ∘ e)) 2
        (μ.restrict (thickening (R / √Lam) (e ⁻¹' S))) ≤
      ENNReal.ofReal (Lam * lam ^ (-((Module.finrank ℝ E : ℝ) / 4))) *
        eLpNorm (iteratedFDeriv ℝ 2 u) 2 (μ.restrict (thickening R S)) := by
    have hcont : ContinuousOn (iteratedFDeriv ℝ 2 (u ∘ e)) (e ⁻¹' thickening R S) :=
      (ContinuousOn.continuousOn_iteratedFDeriv hv hU' le_rfl).mono
        (preimage_mono ((thickening_subset_cthickening R S).trans hSU))
    refine (eLpNorm_mono_measure _ (Measure.restrict_mono hthick le_rfl)).trans
      ((e.eLpNorm_iteratedFDeriv_comp_right_restrict_preimage_le μ u 2 2
        (hcont.aestronglyMeasurable (hT.preimage e.continuous.measurable))).trans ?_)
    rw [ENNReal.ofReal_mul hLam.le, mul_assoc]
    gcongr
    · calc ‖(e : E →L[ℝ] E)‖ ^ 2 ≤ √Lam ^ 2 := by
            gcongr
            exact ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) he'
        _ = Lam := Real.sq_sqrt hLam.le
    · rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by simp)]
      refine ENNReal.ofReal_le_ofReal ((Real.rpow_le_rpow (abs_nonneg _) hdet
        (by simp)).trans_eq ?_)
      rw [← Real.rpow_mul hlam.le]
      norm_num
      ring_nf
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (eLpNorm_iteratedFDeriv_two_thickening_ne_top μ hU hu hS hSU)) hL2).trans_eq ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

end Thickening

section InnerHessian

/-- The `Lᵖ` norm of the second derivative of a function `w` with continuous second derivative on a
finite-dimensional real inner product space with an additive Haar measure `μ` is at most
`μ (closedBall 0 R) ^ (1/p) * (card ι) ^ 2 * B`, when the second derivative of `w` is supported in
the closed ball `closedBall x₀ R` and all its second partial derivatives along an orthonormal basis
`b` are bounded by `B`. Only the second derivative needs to be supported there, so `w` itself may be
nonzero outside. -/
theorem toReal_eLpNorm_iteratedFDeriv_two_le_of_support_subset_closedBall
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    [Fintype ι] [Nonempty ι] (b : OrthonormalBasis ι ℝ E) {w : E → ℝ}
    (hw : Continuous (iteratedFDeriv ℝ 2 w)) {x₀ : E} {R B : ℝ} {p : ℝ≥0∞}
    (hsupp : Function.support (iteratedFDeriv ℝ 2 w) ⊆ closedBall x₀ R)
    (hB : ∀ x i j, |fderiv ℝ (fderiv ℝ w) x (b i) (b j)| ≤ B) :
    (eLpNorm (iteratedFDeriv ℝ 2 w) p μ).toReal ≤
      (μ (closedBall (0 : E) R)).toReal ^ p.toReal⁻¹ * ((Fintype.card ι : ℝ) ^ 2 * B) := by
  have hB₀ : 0 ≤ B :=
    (abs_nonneg _).trans (hB 0 (Classical.arbitrary ι) (Classical.arbitrary ι))
  have hnorm (x : E) : ‖iteratedFDeriv ℝ 2 w x‖ ≤ (Fintype.card ι : ℝ) ^ 2 * B := by
    refine (iteratedFDeriv ℝ 2 w x).opNorm_le_card_sq_mul_of_norm_apply_le b (B := B) fun i j => ?_
    simpa [iteratedFDeriv_two_apply] using hB x i j
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity)
    measure_closedBall_lt_top.ne) ENNReal.ofReal_ne_top) (eLpNorm_le_of_ae_bound_of_support_subset
    hw.aestronglyMeasurable hsupp (ae_of_all _ hnorm))).trans
    (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (by positivity),
    Measure.addHaar_closedBall_center]

end InnerHessian

end MeasureTheory.Measure
