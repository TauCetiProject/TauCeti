/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.IndexForm.Basic
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Curvature.Cotangent
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# Index minimization and upper Jacobi comparison

The native index form of a Jacobi field is minimal among fields with the same endpoints
exactly when the index of their difference is nonnegative. Nonpositive radial curvature
supplies this nonnegativity directly. Parallel comparison fields give the upper
constant-curvature bound for the terminal Jacobi pairing.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 10.
* [lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions).
* [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public noncomputable section

open Bundle CovariantDerivative Filter Set MeasureTheory
open scoped ContDiff Manifold Topology InnerProductSpace

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {V W P : ∀ t, TangentSpace I (γ t)} {s : Set ℝ} {a b κ : ℝ}

/-- For a Jacobi field and a competitor with the same endpoints, index minimization is
equivalent to nonnegativity of the endpoint-zero difference. Either interval orientation is
allowed. -/
theorem IsJacobiFieldOn.indexForm_self_le_iff (h : IsJacobiFieldOn I γ V s)
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun t ↦ TotalSpace.mk' E (γ t) (W t)) (uIcc a b))
    (hs : uIcc a b ⊆ s) (ha : W a = V a) (hb : W b = V b) :
    indexForm I γ V V a b ≤ indexForm I γ W W a b ↔
      0 ≤ indexForm I γ (V - W) (V - W) a b := by
  have hV := (h.contMDiffOn.mono hs).of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  have hcross : indexForm I γ V W a b = indexForm I γ V V a b := by
    rw [h.indexForm_eq_inner_sub_inner hW hs, h.indexForm_eq_inner_sub_inner hV hs, ha, hb]
  rw [indexForm_sub_sub_self hV hW, hcross]
  constructor <;> intro hle <;> linarith

/-- A Jacobi field minimizes the index among fields with its endpoints when radial curvature
is nonpositive along their difference. -/
theorem IsJacobiFieldOn.indexForm_self_le_of_curvature_nonpos
    (h : IsJacobiFieldOn I γ V s) (hab : a ≤ b)
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun t ↦ TotalSpace.mk' E (γ t) (W t)) (uIcc a b))
    (hs : uIcc a b ⊆ s) (ha : W a = V a) (hb : W b = V b)
    (hR : ∀ t ∈ Ioo a b, inner ℝ
      ((leviCivitaConnection I M).curvatureTensor (γ t) (V t - W t)
        (curveVelocity I γ t) (curveVelocity I γ t)) (V t - W t) ≤ 0) :
    indexForm I γ V V a b ≤ indexForm I γ W W a b := by
  exact (h.indexForm_self_le_iff hW hs ha hb).2
    (indexForm_self_nonneg_of_curvature_nonpos hab hR)

/-- A lower curvature bound along a parallel field bounds the index of its scalar multiples.
Differentiability and pointwise bounds are required only in the open interval. -/
theorem indexForm_self_smul_le_integral_of_parallel {f f' : ℝ → ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hP : ∀ t ∈ Ioo a b, MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun r ↦ TotalSpace.mk' E (γ r) (P r)) t)
    (hparallel : ∀ t ∈ Ioo a b, alongCurve (leviCivitaConnection I M) γ P t = 0)
    (hindex : IntervalIntegrable
      (indexFormIntegrand I γ (fun t ↦ f t • P t) (fun t ↦ f t • P t)) volume a b)
    (hmodel : IntervalIntegrable (fun t ↦ (f' t ^ 2 - κ * f t ^ 2) * ‖P t‖ ^ 2)
      volume a b)
    (hR : ∀ t ∈ Ioo a b, κ * ‖P t‖ ^ 2 ≤ inner ℝ
      ((leviCivitaConnection I M).curvatureTensor (γ t) (P t)
        (curveVelocity I γ t) (curveVelocity I γ t)) (P t)) :
    indexForm I γ (fun t ↦ f t • P t) (fun t ↦ f t • P t) a b ≤
      ∫ t in a..b, (f' t ^ 2 - κ * f t ^ 2) * ‖P t‖ ^ 2 := by
  rw [indexForm_def]
  apply intervalIntegral.integral_mono_on_of_le_Ioo hab hindex hmodel
  intro t ht
  rw [indexFormIntegrand_def, alongCurve_smul _ γ P f (hf t ht).differentiableAt
    (differentiableAt_sectionCoord γ P (hP t ht)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))),
    (hf t ht).deriv, hparallel t ht, smul_zero, add_zero]
  simp only [map_smul, LinearMap.smul_apply, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  have hbound := mul_le_mul_of_nonneg_left (hR t ht) (sq_nonneg (f t))
  nlinarith

/-- The normalized model sine times a parallel field has index at most its model terminal pairing,
under the lower curvature bound along that field. -/
theorem indexForm_self_curvatureSine_smul_le (hab : a ≤ b)
    (hP : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun t ↦ TotalSpace.mk' E (γ t) (P t)) (uIcc a b))
    (hparallel : ∀ t ∈ uIcc a b,
      alongCurveWithin (leviCivitaConnection I M) γ P (uIcc a b) t = 0)
    (hR : ∀ t ∈ Ioo a b, κ * ‖P t‖ ^ 2 ≤ inner ℝ
      ((leviCivitaConnection I M).curvatureTensor (γ t) (P t)
        (curveVelocity I γ t) (curveVelocity I γ t)) (P t)) :
    indexForm I γ
      (fun t ↦ (curvatureSine κ (t - a) / curvatureSine κ (b - a)) • P t)
      (fun t ↦ (curvatureSine κ (t - a) / curvatureSine κ (b - a)) • P t) a b ≤
      curvatureCotangent κ (b - a) * ‖P b‖ ^ 2 := by
  obtain rfl | _hlt := hab.eq_or_lt
  · simp [indexForm_same, curvatureCotangent_def]
  let f := fun t ↦ curvatureSine κ (t - a) / curvatureSine κ (b - a)
  let f' := fun t ↦ curvatureCosine κ (t - a) / curvatureSine κ (b - a)
  have hf (t : ℝ) : HasDerivAt f (f' t) t :=
    ((hasDerivAt_curvatureSine κ (t - a)).comp_sub_const t a).div_const _
  have hfc : ContDiff ℝ 1 f :=
    (((contDiff_curvatureSine κ).comp (contDiff_id.sub contDiff_const)).div_const _).of_le
      (by simp)
  have hopen : Ioo a b ⊆ uIcc a b := Ioo_subset_Icc_self.trans Icc_subset_uIcc
  have hZ := hfc.contMDiff.contMDiffOn.smul_totalSpace hP
  have hγ := ((Bundle.contMDiff_proj (fun x : M ↦ TangentSpace I x)
    (IB := I) (n := 1)).comp_contMDiffOn hP).mdifferentiableOn one_ne_zero
  have hcoord t ht := TauCeti.Manifold.differentiableWithinAt_sectionCoord γ P
    ((hP t ht).mdifferentiableWithinAt one_ne_zero)
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hnorm (t : ℝ) (ht : t ∈ uIcc a b) : ‖P t‖ ^ 2 = ‖P b‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using
      (isMetricCompatible_leviCivitaConnection I).inner_eq_of_alongCurveWithin_eq_zero
        isPreconnected_uIcc hγ hcoord hcoord hparallel hparallel ht right_mem_uIcc
  have hmodel : IntervalIntegrable (fun t ↦ (f' t ^ 2 - κ * f t ^ 2) * ‖P b‖ ^ 2)
      volume a b :=
    (((((contDiff_curvatureCosine κ).continuous.comp
      (continuous_id.sub continuous_const)).div_const _).pow 2).sub
        (continuous_const.mul (hfc.continuous.pow 2))).mul continuous_const
      |>.intervalIntegrable _ _
  have h := indexForm_self_smul_le_integral_of_parallel hab (fun t _ ↦ hf t)
    (fun t ht ↦ ((hP t (hopen ht)).contMDiffAt
      (mem_of_superset (isOpen_Ioo.mem_nhds ht) hopen)).mdifferentiableAt one_ne_zero)
    (fun t ht ↦ by
      rw [← alongCurveWithin_of_mem_nhds _ γ P
        (mem_of_superset (isOpen_Ioo.mem_nhds ht) hopen)]
      exact hparallel t (hopen ht))
    (intervalIntegrable_indexFormIntegrand hZ hZ)
    (hmodel.congr_uIoo fun t ht ↦ by rw [hnorm t (uIoo_subset_uIcc_self ht)]) hR
  refine h.trans_eq ?_
  rw [intervalIntegral.integral_congr_uIoo (fun t ht ↦ by
    rw [hnorm t (uIoo_subset_uIcc_self ht)]), intervalIntegral.integral_mul_const]
  rw [integral_curvatureCosine_div_sq_sub_mul_curvatureSine_div_sq]

/-- A Jacobi field initially zero has its terminal pairing bounded above by the model
cotangent, provided its difference from the parallel model competitor has nonnegative index.
The curvature bound is checked along the unscaled parallel field. -/
theorem IsJacobiFieldOn.inner_alongCurveWithin_self_le_curvatureCotangent_mul_norm_sq
    (h : IsJacobiFieldOn I γ V s) (hab : a ≤ b) (hs : uIcc a b ⊆ s)
    (hVa : V a = 0) (hsin : a < b → curvatureSine κ (b - a) ≠ 0)
    (hP : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun t ↦ TotalSpace.mk' E (γ t) (P t)) (uIcc a b))
    (hparallel : ∀ t ∈ uIcc a b,
      alongCurveWithin (leviCivitaConnection I M) γ P (uIcc a b) t = 0)
    (hPb : P b = V b)
    (hR : ∀ t ∈ Ioo a b, κ * ‖P t‖ ^ 2 ≤ inner ℝ
      ((leviCivitaConnection I M).curvatureTensor (γ t) (P t)
        (curveVelocity I γ t) (curveVelocity I γ t)) (P t))
    (hindex : 0 ≤ indexForm I γ
      (V - fun t ↦ (curvatureSine κ (t - a) / curvatureSine κ (b - a)) • P t)
      (V - fun t ↦ (curvatureSine κ (t - a) / curvatureSine κ (b - a)) • P t) a b) :
    inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s b) (V b) ≤
      curvatureCotangent κ (b - a) * ‖V b‖ ^ 2 := by
  obtain rfl | hlt := hab.eq_or_lt
  · simp [hVa]
  have hfc : ContDiff ℝ 1
      (fun t ↦ curvatureSine κ (t - a) / curvatureSine κ (b - a)) :=
    (((contDiff_curvatureSine κ).comp (contDiff_id.sub contDiff_const)).div_const _).of_le
      (by simp)
  have hW := hfc.contMDiff.contMDiffOn.smul_totalSpace hP
  have hle := (h.indexForm_self_le_iff hW hs (by simp [hVa])
    (by simp [hsin hlt, hPb])).2 hindex
  have hupper := indexForm_self_curvatureSine_smul_le hab hP hparallel hR
  rw [hPb] at hupper
  have hV := (h.contMDiffOn.mono hs).of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  rw [h.indexForm_eq_inner_sub_inner hV hs, hVa, inner_zero_right, sub_zero] at hle
  exact hle.trans hupper

/-- The upper terminal-pairing comparison under nonpositive radial curvature, without a
separate index-nonnegativity premise. -/
theorem IsJacobiFieldOn.inner_alongCurveWithin_self_le_curvatureCotangent_mul_norm_sq_of_nonpos
    (h : IsJacobiFieldOn I γ V s) (hab : a ≤ b) (hs : uIcc a b ⊆ s)
    (hVa : V a = 0)
    (hP : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun t ↦ TotalSpace.mk' E (γ t) (P t)) (uIcc a b))
    (hparallel : ∀ t ∈ uIcc a b,
      alongCurveWithin (leviCivitaConnection I M) γ P (uIcc a b) t = 0)
    (hPb : P b = V b)
    (hupper : ∀ t ∈ Ioo a b, ∀ u : TangentSpace I (γ t), inner ℝ
      ((leviCivitaConnection I M).curvatureTensor (γ t) u
        (curveVelocity I γ t) (curveVelocity I γ t)) u ≤ 0)
    (hlower : ∀ t ∈ Ioo a b, κ * ‖P t‖ ^ 2 ≤ inner ℝ
      ((leviCivitaConnection I M).curvatureTensor (γ t) (P t)
        (curveVelocity I γ t) (curveVelocity I γ t)) (P t)) :
    inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s b) (V b) ≤
      curvatureCotangent κ (b - a) * ‖V b‖ ^ 2 := by
  by_cases hVb : V b = 0
  · simp [hVb]
  obtain rfl | hlt := hab.eq_or_lt
  · exact (hVb hVa).elim
  have ht : (a + b) / 2 ∈ Ioo a b := by constructor <;> linarith
  have hcoord t ht := TauCeti.Manifold.differentiableWithinAt_sectionCoord γ P
    ((hP t ht).mdifferentiableWithinAt one_ne_zero)
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hnorm : ‖P ((a + b) / 2)‖ ^ 2 = ‖V b‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq, hPb] using
      (isMetricCompatible_leviCivitaConnection I).inner_eq_of_alongCurveWithin_eq_zero
        isPreconnected_uIcc (h.isGeodesicCurveOn.mdifferentiableOn.mono hs)
        hcoord hcoord hparallel hparallel (Icc_subset_uIcc (Ioo_subset_Icc_self ht))
        right_mem_uIcc
  have hκ : κ ≤ 0 := by
    have hbpos := sq_pos_of_pos (norm_pos_iff.mpr hVb)
    have hcurv := (hlower ((a + b) / 2) ht).trans (hupper ((a + b) / 2) ht _)
    rw [hnorm] at hcurv
    nlinarith
  have hsin : curvatureSine κ (b - a) ≠ 0 :=
    (curvatureSine_pos (sub_pos.mpr hlt) fun hκpos ↦ (hκpos.not_ge hκ).elim).ne'
  apply h.inner_alongCurveWithin_self_le_curvatureCotangent_mul_norm_sq
    hab hs hVa (fun _ ↦ hsin) hP hparallel hPb hlower
  exact indexForm_self_nonneg_of_curvature_nonpos hab fun t ht ↦ hupper t ht _

end TauCeti.Manifold
