/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The ordinary Jacobi index form

The index form integrates `⟪v, w⟫ - ⟪R y, z⟫`. A symmetric coefficient gives a symmetric
bilinear form. The ordinary Jacobi equations give its Green boundary identity. These facts
supply the analytic index comparison argument; identifying ordinary and covariant derivatives
and proving index nonnegativity for minimizing geodesics are separate geometric steps.

No finite-dimensionality or completeness assumption is used.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, equations (10.23)
  and Proposition 10.24.
* Public formalization references:
  [lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
  [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).

The index calculus incorporates work from *DifferentialGeometry*, Chow, Liao and Qin,
Copyright 2026 The DifferentialGeometry contributors, released under Apache 2.0.
-/

public noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace TauCeti.Jacobi

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The actual bilinear density of the ordinary Jacobi index form. -/
def indexIntegrand (R : ℝ → F →L[ℝ] F) (y v z w : ℝ → F) (t : ℝ) : ℝ :=
  ⟪v t, w t⟫ - ⟪R t (y t), z t⟫

/-- The pointwise formula for the Jacobi index density. -/
theorem indexIntegrand_def (R : ℝ → F →L[ℝ] F) (y v z w : ℝ → F) (t : ℝ) :
    indexIntegrand R y v z w t = ⟪v t, w t⟫ - ⟪R t (y t), z t⟫ := (rfl)

/-- The oriented interval integral of the actual Jacobi index density. -/
def indexForm (R : ℝ → F →L[ℝ] F) (a b : ℝ) (y v z w : ℝ → F) : ℝ :=
  ∫ t in a..b, indexIntegrand R y v z w t

/-- Unfold the interval index form. -/
theorem indexForm_def (R : ℝ → F →L[ℝ] F) (a b : ℝ) (y v z w : ℝ → F) :
    indexForm R a b y v z w = ∫ t in a..b, indexIntegrand R y v z w t := (rfl)

@[simp]
theorem indexIntegrand_zero_left (R : ℝ → F →L[ℝ] F) (z w : ℝ → F) (t : ℝ) :
    indexIntegrand R 0 0 z w t = 0 := by simp [indexIntegrand]

@[simp]
theorem indexIntegrand_zero_right (R : ℝ → F →L[ℝ] F) (y v : ℝ → F) (t : ℝ) :
    indexIntegrand R y v 0 0 t = 0 := by simp [indexIntegrand]

theorem indexIntegrand_add_left (R : ℝ → F →L[ℝ] F)
    (y v y' v' z w : ℝ → F) (t : ℝ) :
    indexIntegrand R (y + y') (v + v') z w t =
      indexIntegrand R y v z w t + indexIntegrand R y' v' z w t := by
  simp only [indexIntegrand, Pi.add_apply, map_add, inner_add_left]
  ring

theorem indexIntegrand_add_right (R : ℝ → F →L[ℝ] F)
    (y v z w z' w' : ℝ → F) (t : ℝ) :
    indexIntegrand R y v (z + z') (w + w') t =
      indexIntegrand R y v z w t + indexIntegrand R y v z' w' t := by
  simp only [indexIntegrand, Pi.add_apply, inner_add_right]
  ring

theorem indexIntegrand_smul_left (R : ℝ → F →L[ℝ] F)
    (y v z w : ℝ → F) (c t : ℝ) :
    indexIntegrand R (c • y) (c • v) z w t = c * indexIntegrand R y v z w t := by
  simp only [indexIntegrand, Pi.smul_apply, map_smul, real_inner_smul_left]
  ring

theorem indexIntegrand_smul_right (R : ℝ → F →L[ℝ] F)
    (y v z w : ℝ → F) (c t : ℝ) :
    indexIntegrand R y v (c • z) (c • w) t = c * indexIntegrand R y v z w t := by
  simp only [indexIntegrand, Pi.smul_apply, real_inner_smul_right]
  ring

@[simp]
theorem indexForm_zero_left (R : ℝ → F →L[ℝ] F) (a b : ℝ) (z w : ℝ → F) :
    indexForm R a b 0 0 z w = 0 := by simp [indexForm]

@[simp]
theorem indexForm_zero_right (R : ℝ → F →L[ℝ] F) (a b : ℝ) (y v : ℝ → F) :
    indexForm R a b y v 0 0 = 0 := by simp [indexForm]

theorem indexForm_add_left {R : ℝ → F →L[ℝ] F} {a b : ℝ}
    {y v y' v' z w : ℝ → F}
    (h : IntervalIntegrable (indexIntegrand R y v z w) volume a b)
    (h' : IntervalIntegrable (indexIntegrand R y' v' z w) volume a b) :
    indexForm R a b (y + y') (v + v') z w =
      indexForm R a b y v z w + indexForm R a b y' v' z w := by
  simp only [indexForm, indexIntegrand_add_left]
  exact intervalIntegral.integral_add h h'

theorem indexForm_add_right {R : ℝ → F →L[ℝ] F} {a b : ℝ}
    {y v z w z' w' : ℝ → F}
    (h : IntervalIntegrable (indexIntegrand R y v z w) volume a b)
    (h' : IntervalIntegrable (indexIntegrand R y v z' w') volume a b) :
    indexForm R a b y v (z + z') (w + w') =
      indexForm R a b y v z w + indexForm R a b y v z' w' := by
  simp only [indexForm, indexIntegrand_add_right]
  exact intervalIntegral.integral_add h h'

theorem indexForm_smul_left (R : ℝ → F →L[ℝ] F) (a b : ℝ) (y v z w : ℝ → F)
    (c : ℝ) : indexForm R a b (c • y) (c • v) z w = c * indexForm R a b y v z w := by
  simp only [indexForm, indexIntegrand_smul_left, intervalIntegral.integral_const_mul]

theorem indexForm_smul_right (R : ℝ → F →L[ℝ] F) (a b : ℝ) (y v z w : ℝ → F)
    (c : ℝ) : indexForm R a b y v (c • z) (c • w) = c * indexForm R a b y v z w := by
  simp only [indexForm, indexIntegrand_smul_right, intervalIntegral.integral_const_mul]

/-- A pointwise self-adjoint coefficient makes the density symmetric. -/
theorem indexIntegrand_symm {R : ℝ → F →L[ℝ] F}
    {t : ℝ} (hR : LinearMap.IsSymmetric (R t).toLinearMap)
    (y v z w : ℝ → F) :
    indexIntegrand R y v z w t = indexIntegrand R z w y v t := by
  unfold indexIntegrand
  have hk : ⟪R t (y t), z t⟫ = ⟪y t, R t (z t)⟫ := hR (y t) (z t)
  rw [real_inner_comm (v t) (w t), hk,
    real_inner_comm (y t) (R t (z t))]

/-- A pointwise self-adjoint coefficient makes the index pairing symmetric. -/
theorem indexForm_symm {R : ℝ → F →L[ℝ] F}
    (a b : ℝ) (hR : ∀ t ∈ uIcc a b, LinearMap.IsSymmetric (R t).toLinearMap)
    (y v z w : ℝ → F) :
    indexForm R a b y v z w = indexForm R a b z w y v :=
  intervalIntegral.integral_congr fun t ht ↦ indexIntegrand_symm (hR t ht) y v z w

/-- Continuous coefficients and fields give a continuous index density. -/
theorem continuousOn_indexIntegrand {R : ℝ → F →L[ℝ] F} {y v z w : ℝ → F} {s : Set ℝ}
    (hR : ContinuousOn R s) (hy : ContinuousOn y s) (hv : ContinuousOn v s)
    (hz : ContinuousOn z s) (hw : ContinuousOn w s) :
    ContinuousOn (indexIntegrand R y v z w) s :=
  (hv.inner hw).sub ((hR.clm_apply hy).inner hz)

/-- Continuity on the unordered interval gives interval integrability. -/
theorem intervalIntegrable_indexIntegrand {R : ℝ → F →L[ℝ] F} {y v z w : ℝ → F} {a b : ℝ}
    (hR : ContinuousOn R (uIcc a b)) (hy : ContinuousOn y (uIcc a b))
    (hv : ContinuousOn v (uIcc a b)) (hz : ContinuousOn z (uIcc a b))
    (hw : ContinuousOn w (uIcc a b)) :
    IntervalIntegrable (indexIntegrand R y v z w) volume a b :=
  (continuousOn_indexIntegrand hR hy hv hz hw).intervalIntegrable

/-- Add the actual index integrals across a common endpoint. -/
theorem indexForm_add_adjacent {R : ℝ → F →L[ℝ] F} {a c b : ℝ}
    {y v z w : ℝ → F}
    (h₁ : IntervalIntegrable (indexIntegrand R y v z w) volume a c)
    (h₂ : IntervalIntegrable (indexIntegrand R y v z w) volume c b) :
    indexForm R a c y v z w + indexForm R c b y v z w
      = indexForm R a b y v z w :=
  intervalIntegral.integral_add_adjacent_intervals h₁ h₂

/-- The index integral on a degenerate interval vanishes. -/
@[simp] theorem indexForm_same (R : ℝ → F →L[ℝ] F) (a : ℝ) (y v z w : ℝ → F) :
    indexForm R a a y v z w = 0 := intervalIntegral.integral_same

/-- Expand a symmetric density under a common scalar perturbation. -/
theorem indexIntegrand_add_smul {R : ℝ → F →L[ℝ] F}
    {t : ℝ} (hR : LinearMap.IsSymmetric (R t).toLinearMap)
    (y v z w : ℝ → F) (c : ℝ) :
    indexIntegrand R (y + c • z) (v + c • w) (y + c • z) (v + c • w) t
      = indexIntegrand R y v y v t + 2 * c * indexIntegrand R y v z w t
        + c ^ 2 * indexIntegrand R z w z w t := by
  simp only [indexIntegrand_add_left, indexIntegrand_add_right,
    indexIntegrand_smul_left, indexIntegrand_smul_right]
  rw [indexIntegrand_symm hR z w y v]
  ring

/-- Integrate the full quadratic perturbation identity. -/
theorem indexForm_add_smul {R : ℝ → F →L[ℝ] F} {a b : ℝ} {y v z w : ℝ → F}
    (hR : ∀ t ∈ uIcc a b, LinearMap.IsSymmetric (R t).toLinearMap)
    (hyy : IntervalIntegrable (indexIntegrand R y v y v) volume a b)
    (hyz : IntervalIntegrable (indexIntegrand R y v z w) volume a b)
    (hzz : IntervalIntegrable (indexIntegrand R z w z w) volume a b)
    (c : ℝ) :
    indexForm R a b (y + c • z) (v + c • w) (y + c • z) (v + c • w)
      = indexForm R a b y v y v + 2 * c * indexForm R a b y v z w
        + c ^ 2 * indexForm R a b z w z w := by
  unfold indexForm
  rw [intervalIntegral.integral_congr
    (g := fun t ↦ indexIntegrand R y v y v t
      + 2 * c * indexIntegrand R y v z w t
      + c ^ 2 * indexIntegrand R z w z w t)
    (fun t ht ↦ indexIntegrand_add_smul (hR t ht) y v z w c)]
  rw [intervalIntegral.integral_add
      (hyy.add (hyz.const_mul (2 * c))) (hzz.const_mul (c ^ 2)),
    intervalIntegral.integral_add hyy (hyz.const_mul (2 * c)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- Continuous coefficient and fields on a closed interval supply all three
integrability obligations in the symmetric quadratic index expansion. -/
theorem indexForm_add_smul_of_continuousOn
    {R : ℝ → F →L[ℝ] F} {a b : ℝ} {y v z w : ℝ → F}
    (hab : a ≤ b)
    (hSym : ∀ t ∈ Icc a b, LinearMap.IsSymmetric (R t).toLinearMap)
    (hR : ContinuousOn R (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hv : ContinuousOn v (Icc a b)) (hz : ContinuousOn z (Icc a b))
    (hw : ContinuousOn w (Icc a b)) (c : ℝ) :
    indexForm R a b (y + c • z) (v + c • w) (y + c • z) (v + c • w)
      = indexForm R a b y v y v + 2 * c * indexForm R a b y v z w
        + c ^ 2 * indexForm R a b z w z w := by
  have hint {f f' g g' : ℝ → F}
      (hf : ContinuousOn f (Icc a b)) (hf' : ContinuousOn f' (Icc a b))
      (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b)) :
      IntervalIntegrable (indexIntegrand R f f' g g') volume a b := by
    apply intervalIntegrable_indexIntegrand <;> rw [uIcc_of_le hab]
    exacts [hR, hf, hf', hg, hg']
  exact indexForm_add_smul (fun t ht ↦ hSym t ((uIcc_of_le hab) ▸ ht))
    (hint hy hv hy hv) (hint hy hv hz hw)
    (hint hz hw hz hw) c

/-- Scaling both slots of the index form multiplies it by the square of the
scalar, even without integrability or coefficient-symmetry assumptions. -/
theorem indexForm_smul (R : ℝ → F →L[ℝ] F) (a b : ℝ) (y v : ℝ → F) (c : ℝ) :
    indexForm R a b (c • y) (c • v) (c • y) (c • v)
      = c ^ 2 * indexForm R a b y v y v := by
  rw [indexForm_smul_left, indexForm_smul_right]
  ring

/-- A zero self-index and nonzero cross term admit a negative perturbation. -/
theorem exists_indexForm_neg {R : ℝ → F →L[ℝ] F} {a b : ℝ} {y v z w : ℝ → F}
    (hR : ∀ t ∈ uIcc a b, LinearMap.IsSymmetric (R t).toLinearMap)
    (hyy : IntervalIntegrable (indexIntegrand R y v y v) volume a b)
    (hyz : IntervalIntegrable (indexIntegrand R y v z w) volume a b)
    (hzz : IntervalIntegrable (indexIntegrand R z w z w) volume a b)
    (hself : indexForm R a b y v y v = 0)
    (hcross : indexForm R a b y v z w ≠ 0) :
    ∃ c : ℝ,
      indexForm R a b (y + c • z) (v + c • w) (y + c • z) (v + c • w) < 0 := by
  by_contra! h
  have hpoly (c : ℝ) : 0 ≤ indexForm R a b z w z w * (c * c) +
      (2 * indexForm R a b y v z w) * c + 0 := by
    have hc := h c
    rw [indexForm_add_smul hR hyy hyz hzz, hself] at hc
    nlinarith only [hc]
  have hd := discrim_le_zero hpoly
  simp only [discrim, mul_zero, sub_zero] at hd
  exact hcross (by nlinarith)

/-- Green's identity for an integrable index density. Only the derivatives of the velocity
and the test field enter the boundary pairing. -/
theorem indexForm_eq_sub {R : ℝ → F →L[ℝ] F} {a b : ℝ} {y v z w : ℝ → F}
    (hab : a ≤ b)
    (hv : ∀ t ∈ Icc a b, HasDerivWithinAt v (-(R t) (y t)) (Icc a b) t)
    (hz : ∀ t ∈ Icc a b, HasDerivWithinAt z (w t) (Icc a b) t)
    (hint : IntervalIntegrable (indexIntegrand R y v z w) volume a b) :
    indexForm R a b y v z w = ⟪v b, z b⟫ - ⟪v a, z a⟫ := by
  have hvc : ContinuousOn v (Icc a b) := fun t ht ↦ (hv t ht).continuousWithinAt
  have hzc : ContinuousOn z (Icc a b) := fun t ht ↦ (hz t ht).continuousWithinAt
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab (hvc.inner hzc) ?_ hint
  intro t ht
  have hm : Icc a b ∈ nhds t := Icc_mem_nhds ht.1 ht.2
  have hd := ((hv t (Ioo_subset_Icc_self ht)).hasDerivAt hm).inner ℝ
    ((hz t (Ioo_subset_Icc_self ht)).hasDerivAt hm)
  convert hd.hasDerivWithinAt using 1
  simp only [indexIntegrand, inner_neg_left]
  ring

/-- Continuous coefficient, position and test velocity imply the integrability needed in
Green's identity. No derivative of the position is required. -/
theorem indexForm_eq_sub_of_continuousOn {R : ℝ → F →L[ℝ] F} {a b : ℝ}
    {y v z w : ℝ → F} (hab : a ≤ b) (hR : ContinuousOn R (Icc a b))
    (hy : ContinuousOn y (Icc a b))
    (hv : ∀ t ∈ Icc a b, HasDerivWithinAt v (-(R t) (y t)) (Icc a b) t)
    (hz : ∀ t ∈ Icc a b, HasDerivWithinAt z (w t) (Icc a b) t)
    (hw : ContinuousOn w (Icc a b)) :
    indexForm R a b y v z w = ⟪v b, z b⟫ - ⟪v a, z a⟫ := by
  apply indexForm_eq_sub hab hv hz
  apply intervalIntegrable_indexIntegrand <;> rw [uIcc_of_le hab]
  exacts [hR, hy, fun t ht ↦ (hv t ht).continuousWithinAt,
    fun t ht ↦ (hz t ht).continuousWithinAt, hw]

/-- A Jacobi field that vanishes at both endpoints has zero self-index. -/
theorem indexForm_self_eq_zero {R : ℝ → F →L[ℝ] F} {a b : ℝ} {y v : ℝ → F}
    (hab : a ≤ b) (hR : ContinuousOn R (Icc a b))
    (hy : ∀ t ∈ Icc a b, HasDerivWithinAt y (v t) (Icc a b) t)
    (hv : ∀ t ∈ Icc a b, HasDerivWithinAt v (-(R t) (y t)) (Icc a b) t)
    (hya : y a = 0) (hyb : y b = 0) : indexForm R a b y v y v = 0 := by
  rw [indexForm_eq_sub_of_continuousOn hab hR
    (fun t ht ↦ (hy t ht).continuousWithinAt) hv hy
    (fun t ht ↦ (hv t ht).continuousWithinAt), hya, hyb]
  simp

end TauCeti.Jacobi
