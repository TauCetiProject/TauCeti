/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.ODE.Jacobi.IndexForm
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!+# Index comparison for ordinary Jacobi equations

A Jacobi field minimizes its index among fields with the same endpoints whenever the
index of their difference is nonnegative. Comparing coefficient quadratic forms then compares
the boundary pairings of two Jacobi fields. The hyperbolic model gives the sharp estimate
`⟪v T, y T⟫ ≤ C coth(C T) ‖y T‖²` under the curvature bound `R ≥ -C²`.

Index nonnegativity is an explicit hypothesis. This is the analytic comparison argument,
without a claim about minimizing geodesics or an identification with a covariant index form.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 10.
* [lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions).
* [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace TauCeti.Jacobi

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A Jacobi field has no larger index than a competitor with the same endpoints if the
index of their difference is nonnegative. -/
theorem indexForm_le_of_sub_nonneg {R : ℝ → F →L[ℝ] F} {a b : ℝ}
    {y v z w : ℝ → F} (hab : a ≤ b) (hR : ContinuousOn R (Icc a b))
    (hSym : ∀ t ∈ Icc a b, LinearMap.IsSymmetric (R t).toLinearMap)
    (hy : ∀ t ∈ Icc a b, HasDerivWithinAt y (v t) (Icc a b) t)
    (hv : ∀ t ∈ Icc a b, HasDerivWithinAt v (-(R t) (y t)) (Icc a b) t)
    (hz : ∀ t ∈ Icc a b, HasDerivWithinAt z (w t) (Icc a b) t)
    (hw : ContinuousOn w (Icc a b)) (ha : z a = y a) (hb : z b = y b)
    (hindex : 0 ≤ indexForm R a b (y - z) (v - w) (y - z) (v - w)) :
    indexForm R a b y v y v ≤ indexForm R a b z w z w := by
  have hyc : ContinuousOn y (Icc a b) := fun t ht ↦ (hy t ht).continuousWithinAt
  have hvc : ContinuousOn v (Icc a b) := fun t ht ↦ (hv t ht).continuousWithinAt
  have hzc : ContinuousOn z (Icc a b) := fun t ht ↦ (hz t ht).continuousWithinAt
  have hcross : indexForm R a b y v z w = indexForm R a b y v y v := by
    rw [indexForm_eq_sub_of_continuousOn hab hR hyc hv hz hw,
      indexForm_eq_sub_of_continuousOn hab hR hyc hv hy hvc, ha, hb]
  have hexpand := indexForm_add_smul_of_continuousOn hab hSym hR hyc hvc hzc hw (-1)
  simp only [neg_one_smul, ← sub_eq_add_neg] at hexpand
  rw [hcross] at hexpand
  linarith

/-- Comparing the coefficient forms along a test field compares its self-index. -/
theorem indexForm_self_le_of_le {R S : ℝ → F →L[ℝ] F} {a b : ℝ} {z w : ℝ → F}
    (hab : a ≤ b)
    (hR : IntervalIntegrable (indexIntegrand R z w z w) volume a b)
    (hS : IntervalIntegrable (indexIntegrand S z w z w) volume a b)
    (hbound : ∀ t ∈ Icc a b, ⟪S t (z t), z t⟫ ≤ ⟪R t (z t), z t⟫) :
    indexForm R a b z w z w ≤ indexForm S a b z w z w := by
  rw [indexForm_def, indexForm_def]
  exact intervalIntegral.integral_mono_on hab hR hS fun t ht ↦
    by simpa only [indexIntegrand_def] using sub_le_sub_left (hbound t ht) ⟪w t, w t⟫

/-- Two ordinary Jacobi fields with the same endpoint positions have ordered boundary
pairings when the coefficient forms are ordered and the difference has nonnegative index. -/
theorem inner_sub_le_of_index_sub_nonneg {R S : ℝ → F →L[ℝ] F} {a b : ℝ}
    {y v z w : ℝ → F} (hab : a ≤ b)
    (hR : ContinuousOn R (Icc a b)) (hS : ContinuousOn S (Icc a b))
    (hSym : ∀ t ∈ Icc a b, LinearMap.IsSymmetric (R t).toLinearMap)
    (hy : ∀ t ∈ Icc a b, HasDerivWithinAt y (v t) (Icc a b) t)
    (hv : ∀ t ∈ Icc a b, HasDerivWithinAt v (-(R t) (y t)) (Icc a b) t)
    (hz : ∀ t ∈ Icc a b, HasDerivWithinAt z (w t) (Icc a b) t)
    (hw : ∀ t ∈ Icc a b, HasDerivWithinAt w (-(S t) (z t)) (Icc a b) t)
    (ha : z a = y a) (hb : z b = y b)
    (hbound : ∀ t ∈ Icc a b, ⟪S t (z t), z t⟫ ≤ ⟪R t (z t), z t⟫)
    (hindex : 0 ≤ indexForm R a b (y - z) (v - w) (y - z) (v - w)) :
    ⟪v b, y b⟫ - ⟪v a, y a⟫ ≤ ⟪w b, z b⟫ - ⟪w a, z a⟫ := by
  have hzc : ContinuousOn z (Icc a b) := fun t ht ↦ (hz t ht).continuousWithinAt
  have hwc : ContinuousOn w (Icc a b) := fun t ht ↦ (hw t ht).continuousWithinAt
  have hint (K : ℝ → F →L[ℝ] F) (hK : ContinuousOn K (Icc a b)) :
      IntervalIntegrable (indexIntegrand K z w z w) volume a b := by
    apply intervalIntegrable_indexIntegrand <;> rw [uIcc_of_le hab]
    exacts [hK, hzc, hwc, hzc, hwc]
  have h := (indexForm_le_of_sub_nonneg hab hR hSym hy hv hz hwc ha hb hindex).trans
    (indexForm_self_le_of_le hab (hint R hR) (hint S hS) hbound)
  rwa [indexForm_eq_sub_of_continuousOn hab hR
      (fun t ht ↦ (hy t ht).continuousWithinAt) hv hy (fun t ht ↦ (hv t ht).continuousWithinAt),
    indexForm_eq_sub_of_continuousOn hab hS hzc hw hz hwc] at h

/-- The affine comparison field gives the Euclidean terminal pairing estimate on `[0,T]`.
The curvature coefficient need only be nonnegative along this comparison field. -/
theorem inner_endpoint_le_affine_of_index_sub_nonneg
    {R : ℝ → F →L[ℝ] F} {y v : ℝ → F} {T : ℝ} (hT : 0 < T)
    (hR : ContinuousOn R (Icc 0 T))
    (hSym : ∀ t ∈ Icc 0 T, LinearMap.IsSymmetric (R t).toLinearMap)
    (hy : ∀ t ∈ Icc 0 T, HasDerivWithinAt y (v t) (Icc 0 T) t)
    (hv : ∀ t ∈ Icc 0 T, HasDerivWithinAt v (-(R t) (y t)) (Icc 0 T) t)
    (hbound : ∀ t ∈ Icc 0 T,
      0 ≤ ⟪R t ((t / T) • y T), (t / T) • y T⟫) (hy0 : y 0 = 0)
    (hindex : 0 ≤ indexForm R 0 T
      (y - fun t ↦ (t / T) • y T) (v - fun _ ↦ (1 / T) • y T)
      (y - fun t ↦ (t / T) • y T) (v - fun _ ↦ (1 / T) • y T)) :
    ⟪v T, y T⟫ ≤ (1 / T) * ⟪y T, y T⟫ := by
  let z : ℝ → F := fun t ↦ (t / T) • y T
  let w : ℝ → F := fun _ ↦ (1 / T) • y T
  have hz0 : z 0 = 0 := by simp [z]
  have hzT : z T = y T := by simp [z, hT.ne']
  have hzd (t : ℝ) : HasDerivAt z (w t) t :=
    ((hasDerivAt_id t).div_const T).smul_const (y T)
  have hwd (t : ℝ) : HasDerivAt w (-((0 : F →L[ℝ] F) (z t))) t := by
    simpa only [w, zero_apply, neg_zero] using hasDerivAt_const t ((1 / T) • y T)
  have h := inner_sub_le_of_index_sub_nonneg hT.le hR continuousOn_const hSym hy hv
    (fun t _ ↦ (hzd t).hasDerivWithinAt) (fun t _ ↦ (hwd t).hasDerivWithinAt)
    (hz0.trans hy0.symm) hzT (fun t ht ↦ by simpa [z] using hbound t ht) hindex
  simpa [hy0, hz0, hzT, w, real_inner_smul_left] using h

/-- The hyperbolic comparison field gives the sharp terminal pairing estimate on `[0,T]`.
The index hypothesis concerns the endpoint-zero difference with this explicit field. -/
theorem inner_endpoint_le_hyperbolic_of_index_sub_nonneg
    {R : ℝ → F →L[ℝ] F} {y v : ℝ → F} {C T : ℝ} (hC : 0 < C) (hT : 0 < T)
    (hR : ContinuousOn R (Icc 0 T))
    (hSym : ∀ t ∈ Icc 0 T, LinearMap.IsSymmetric (R t).toLinearMap)
    (hy : ∀ t ∈ Icc 0 T, HasDerivWithinAt y (v t) (Icc 0 T) t)
    (hv : ∀ t ∈ Icc 0 T, HasDerivWithinAt v (-(R t) (y t)) (Icc 0 T) t)
    (hbound : ∀ t ∈ Icc 0 T, ∀ u : F, -(C ^ 2) * ⟪u, u⟫ ≤ ⟪R t u, u⟫)
    (hy0 : y 0 = 0)
    (hindex : 0 ≤ indexForm R 0 T
      (y - fun t ↦ (Real.sinh (C * t) / Real.sinh (C * T)) • y T)
      (v - fun t ↦ (C * Real.cosh (C * t) / Real.sinh (C * T)) • y T)
      (y - fun t ↦ (Real.sinh (C * t) / Real.sinh (C * T)) • y T)
      (v - fun t ↦ (C * Real.cosh (C * t) / Real.sinh (C * T)) • y T)) :
    ⟪v T, y T⟫ ≤ (C * Real.cosh (C * T) / Real.sinh (C * T)) * ⟪y T, y T⟫ := by
  let z : ℝ → F := fun t ↦ (Real.sinh (C * t) / Real.sinh (C * T)) • y T
  let w : ℝ → F := fun t ↦ (C * Real.cosh (C * t) / Real.sinh (C * T)) • y T
  let S : ℝ → F →L[ℝ] F := fun _ ↦ -(C ^ 2) • ContinuousLinearMap.id ℝ F
  have hS (t : ℝ) (u : F) : S t u = -(C ^ 2) • u := (rfl)
  have hsinh : Real.sinh (C * T) ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr (mul_pos hC hT))
  have hz0 : z 0 = 0 := by simp [z]
  have hzT : z T = y T := by simp [z, hsinh]
  have hzd (t : ℝ) : HasDerivAt z (w t) t := by
    convert (((hasDerivAt_id t).const_mul C).sinh.div_const
      (Real.sinh (C * T))).smul_const (y T) using 1 <;> simp [z, w, mul_comm]
  have hwd (t : ℝ) : HasDerivAt w (-(S t) (z t)) t := by
    convert ((((hasDerivAt_id t).const_mul C).cosh.const_mul C).div_const
      (Real.sinh (C * T))).smul_const (y T) using 1
    · rfl
    · simp only [z, S, neg_apply, smul_apply,
        ContinuousLinearMap.id_apply, neg_smul, neg_neg, smul_smul, id_eq]
      congr 1
      ring
  have h := inner_sub_le_of_index_sub_nonneg hT.le hR continuousOn_const hSym hy hv
    (fun t _ ↦ (hzd t).hasDerivWithinAt) (fun t _ ↦ (hwd t).hasDerivWithinAt)
    (hz0.trans hy0.symm) hzT (fun t ht ↦ by
      change ⟪S t (z t), z t⟫ ≤ _
      rw [hS t (z t), real_inner_smul_left]
      exact hbound t ht (z t)) hindex
  simpa [hy0, hz0, hzT, w, real_inner_smul_left] using h

end TauCeti.Jacobi
