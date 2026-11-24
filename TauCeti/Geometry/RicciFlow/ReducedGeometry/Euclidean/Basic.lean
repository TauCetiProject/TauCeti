/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Reduced geometry of the static Euclidean metric

For a curve in a real normed space, the kinetic part of Perelman's backward action is
`∫₀ᵗ √s ‖γ'(s)‖² ds`. We minimize this actual integral over continuous curves that are
differentiable at positive interior times and have finite action. No derivative at time zero
is required. The square-root segments attain the minimum, which is `‖q - p‖² / (2 √t)`.
Dividing by `2 √t` therefore gives the Euclidean reduced length `‖q - p‖² / (4 t)`.

The action estimate and minimizer work in every real normed space. For an inner-product space,
this is the backward action of its static standard Riemannian metric: scalar curvature is zero
and squared speed is the squared norm of the ordinary derivative.

The normalization follows J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*
(2007), Definitions 6.1–6.2. Related formalizations appear in
https://github.com/frenzymath/lean-eval-submissions and
https://github.com/frenzymath/PoincareConjecture.
-/

public noncomputable section

open MeasureTheory Set Real
open scoped Topology

namespace TauCeti.ReducedGeometry

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A segment with affine dependence on square-root time. It may have singular velocity at zero. -/
def sqrtSegment (p q : E) (t s : ℝ) : E :=
  p + (√s / √t) • (q - p)

/-- Evaluation of the square-root segment at an arbitrary parameter. -/
theorem sqrtSegment_apply (p q : E) (t s : ℝ) :
    sqrtSegment p q t s = p + (√s / √t) • (q - p) := by rfl

/-- A square-root segment is the constant initial path when its terminal time is nonpositive. -/
@[simp] theorem sqrtSegment_of_nonpos (p q : E) {t : ℝ} (ht : t ≤ 0) :
    sqrtSegment p q t = fun _ ↦ p := by
  funext s
  simp [sqrtSegment, sqrt_eq_zero_of_nonpos ht]

/-- The square-root segment starts at its prescribed initial point. -/
@[simp] theorem sqrtSegment_zero (p q : E) (t : ℝ) : sqrtSegment p q t 0 = p := by
  simp [sqrtSegment]

/-- At a positive terminal time the square-root segment reaches its prescribed endpoint. -/
@[simp] theorem sqrtSegment_self (p q : E) {t : ℝ} (ht : 0 < t) :
    sqrtSegment p q t t = q := by
  simp [sqrtSegment, div_self ((sqrt_pos.mpr ht).ne')]

end Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The backward kinetic action, equal to Perelman's action for the static Euclidean metric. -/
def euclideanLAction (γ : ℝ → E) (t : ℝ) : ℝ :=
  ∫ s in 0..t, √s * ‖deriv γ s‖ ^ 2

/-- The integral formula for the Euclidean backward action. -/
theorem euclideanLAction_eq_integral (γ : ℝ → E) (t : ℝ) :
    euclideanLAction γ t = ∫ s in 0..t, √s * ‖deriv γ s‖ ^ 2 := by rfl

/-- A path with finite backward kinetic action. The two included endpoints require continuity;
ordinary differentiability is required only on the open parameter interval. -/
def IsEuclideanLPath (γ : ℝ → E) (t : ℝ) : Prop :=
  ContinuousOn γ (Icc 0 t) ∧ DifferentiableOn ℝ γ (Ioo 0 t) ∧
    IntervalIntegrable (fun s ↦ √s * ‖deriv γ s‖ ^ 2) volume 0 t

/-- Admissibility is closed-interval continuity, interior differentiability and finite action. -/
theorem isEuclideanLPath_iff (γ : ℝ → E) (t : ℝ) :
    IsEuclideanLPath γ t ↔ ContinuousOn γ (Icc 0 t) ∧
      DifferentiableOn ℝ γ (Ioo 0 t) ∧
      IntervalIntegrable (fun s ↦ √s * ‖deriv γ s‖ ^ 2) volume 0 t := by rfl

/-- The reduced length defined by the infimum over actual endpoint paths and their actions. -/
def euclideanReducedLength (p q : E) (t : ℝ) : ℝ :=
  sInf {l | ∃ γ : ℝ → E, IsEuclideanLPath γ t ∧ γ 0 = p ∧ γ t = q ∧
    l = euclideanLAction γ t / (2 * √t)}

/-- The defining infimum of normalized actions over admissible endpoint paths. -/
theorem euclideanReducedLength_def (p q : E) (t : ℝ) :
    euclideanReducedLength p q t =
      sInf {l | ∃ γ : ℝ → E, IsEuclideanLPath γ t ∧ γ 0 = p ∧ γ t = q ∧
        l = euclideanLAction γ t / (2 * √t)} := by rfl

/-- The totalized backward action vanishes on a nonpositive time interval. -/
@[simp] theorem euclideanLAction_of_nonpos (γ : ℝ → E) {t : ℝ} (ht : t ≤ 0) :
    euclideanLAction γ t = 0 := by
  rw [euclideanLAction, intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)),
    intervalIntegral.integral_zero]
  intro s hs
  rw [uIcc_of_ge ht] at hs
  simp only [sqrt_eq_zero_of_nonpos hs.2, zero_mul]

/-- The backward kinetic action is nonnegative, including its totalized nonpositive times. -/
theorem euclideanLAction_nonneg (γ : ℝ → E) (t : ℝ) : 0 ≤ euclideanLAction γ t := by
  rcases le_total t 0 with ht | ht
  · rw [euclideanLAction_of_nonpos γ ht]
  · exact intervalIntegral.integral_nonneg ht fun _ _ ↦
      mul_nonneg (sqrt_nonneg _) (sq_nonneg _)

/-- Integrated Young's inequality bounds displacement by the backward action and the explicit
integral of the reciprocal square root. -/
theorem two_mul_norm_sub_le_euclideanLAction_add {γ : ℝ → E} {t : ℝ}
    (hγ : IsEuclideanLPath γ t) (ht : 0 ≤ t) (c : ℝ) :
    2 * c * ‖γ t - γ 0‖ ≤ euclideanLAction γ t + 2 * c ^ 2 * √t := by
  rcases (isEuclideanLPath_iff γ t).mp hγ with ⟨hcont, hdiff, hint⟩
  rcases le_or_gt 0 c with hc | hc
  swap
  · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) (norm_nonneg _)).trans
      (add_nonneg (euclideanLAction_nonneg γ t) (by positivity))
  have hi : IntervalIntegrable (fun s : ℝ ↦ s ^ (-(1 / 2 : ℝ))) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hmajor := norm_sub_le_integral_of_norm_deriv_le_of_le ht
    (hcont.const_smul (2 * c))
    (hdiff.const_smul (2 * c))
    (B := fun s ↦ √s * ‖deriv γ s‖ ^ 2 + c ^ 2 * s ^ (-(1 / 2 : ℝ)))
    (Filter.Eventually.of_forall fun s hs ↦ by
      have hsqrt := sqrt_pos.mpr hs.1
      have hd := ((hdiff s hs).differentiableAt (isOpen_Ioo.mem_nhds hs)).hasDerivAt
      -- The displacement lemma uses the pointwise action of the constant scalar function.
      -- `rw` needs the definitionally equal scalar action on functions for the derivative law.
      change ‖deriv ((2 * c) • γ) s‖ ≤ _
      rw [(hd.const_smul (2 * c)).deriv, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ 2 * c)]
      rw [Real.rpow_neg hs.1.le, ← sqrt_eq_rpow]
      apply (mul_le_mul_iff_right₀ hsqrt).mp
      have hinv : √s * (c ^ 2 * (√s)⁻¹) = c ^ 2 := by field_simp
      rw [mul_add, hinv]
      nlinarith [sq_nonneg (√s * ‖deriv γ s‖ - c)])
    (hint.add (hi.const_mul _))
  have hpow : (∫ s in (0 : ℝ)..t, s ^ (-(1 / 2 : ℝ))) = 2 * √t := by
    rw [integral_rpow (Or.inl (by norm_num))]
    norm_num only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num,
      Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), sub_zero]
    rw [← sqrt_eq_rpow]
    ring
  dsimp only [Pi.smul_apply] at hmajor
  rw [← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 2 * c),
    intervalIntegral.integral_add hint (hi.const_mul _),
    intervalIntegral.integral_const_mul, hpow] at hmajor
  simpa only [euclideanLAction, mul_assoc, mul_left_comm, mul_comm] using hmajor

/-- Every admissible curve has at least the action of a square-root segment. -/
theorem norm_sub_sq_div_le_euclideanLAction {γ : ℝ → E} {t : ℝ}
    (hγ : IsEuclideanLPath γ t) :
    ‖γ t - γ 0‖ ^ 2 / (2 * √t) ≤ euclideanLAction γ t := by
  rcases le_or_gt t 0 with ht | ht
  · rw [euclideanLAction_of_nonpos γ ht, sqrt_eq_zero_of_nonpos ht]
    simp
  have hsqrt := sqrt_pos.mpr ht
  have h := two_mul_norm_sub_le_euclideanLAction_add hγ ht.le
    (‖γ t - γ 0‖ / (2 * √t))
  field_simp at h ⊢
  nlinarith

/-- The velocity of a square-root segment away from zero. -/
theorem hasDerivAt_sqrtSegment (p q : E) (t : ℝ) {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (sqrtSegment p q t) ((1 / (2 * √s) / √t) • (q - p)) s :=
  (((Real.hasDerivAt_sqrt hs).div_const _).smul_const _).const_add _

/-- The action density of a square-root segment is an explicit reciprocal-square-root weight. -/
theorem sqrtSegment_actionDensity (p q : E) {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    √s * ‖deriv (sqrtSegment p q t) s‖ ^ 2 =
      (‖q - p‖ ^ 2 / (4 * t)) * s ^ (-(1 / 2 : ℝ)) := by
  rcases le_or_gt s 0 with hs | hs
  · rw [sqrt_eq_zero_of_nonpos hs, zero_mul, Real.rpow_neg_eq_inv_rpow,
      ← sqrt_eq_rpow, sqrt_eq_zero_of_nonpos (inv_nonpos.mpr hs), mul_zero]
  rcases ht.eq_or_lt with rfl | ht
  · rw [sqrtSegment_of_nonpos p q le_rfl]
    simp
  rw [(hasDerivAt_sqrtSegment p q t hs.ne').deriv, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * √s) / √t),
    Real.rpow_neg hs.le, ← sqrt_eq_rpow]
  have ht0 := (sqrt_pos.mpr ht).ne'
  have hs0 := (sqrt_pos.mpr hs).ne'
  field_simp
  nlinarith [Real.sq_sqrt ht.le, Real.sq_sqrt hs.le]

/-- Square-root segments belong to the full class of finite-action competitors. -/
theorem isEuclideanLPath_sqrtSegment (p q : E) (t : ℝ) :
    IsEuclideanLPath (sqrtSegment p q t) t := by
  rw [isEuclideanLPath_iff]
  rcases le_or_gt t 0 with ht | ht
  · rw [sqrtSegment_of_nonpos p q ht]
    exact ⟨continuousOn_const, differentiableOn_const p, by simp⟩
  refine ⟨((continuous_const.add ((continuous_sqrt.div_const _).smul continuous_const)) :
    Continuous (sqrtSegment p q t)).continuousOn, fun s hs ↦ ?_, ?_⟩
  · exact (hasDerivAt_sqrtSegment p q t hs.1.ne').differentiableAt.differentiableWithinAt
  · apply ((intervalIntegral.intervalIntegrable_rpow'
      (a := 0) (b := t) (r := -(1 / 2 : ℝ)) (by norm_num)).const_mul
        (‖q - p‖ ^ 2 / (4 * t))).congr_uIoo
    intro s _
    exact (sqrtSegment_actionDensity p q ht.le s).symm

/-- A square-root segment has exactly the optimal backward action. -/
@[simp] theorem euclideanLAction_sqrtSegment (p q : E) (t : ℝ) :
    euclideanLAction (sqrtSegment p q t) t = ‖q - p‖ ^ 2 / (2 * √t) := by
  rcases le_or_gt t 0 with ht | ht
  · rw [euclideanLAction_of_nonpos _ ht, sqrt_eq_zero_of_nonpos ht]
    simp
  rw [euclideanLAction, intervalIntegral.integral_congr_Ioo_of_le ht.le
    (fun s _ ↦ sqrtSegment_actionDensity p q ht.le s),
    intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by norm_num))]
  norm_num only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num,
    Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), sub_zero]
  rw [← sqrt_eq_rpow]
  have _hsqrt := sqrt_pos.mpr ht
  field_simp
  nlinarith [Real.sq_sqrt ht.le]

/-- The totalized reduced length is zero at time zero. When the endpoints differ, the set of
competitors is empty and the real infimum has its default value zero. -/
@[simp] theorem euclideanReducedLength_zero (p q : E) :
    euclideanReducedLength p q 0 = 0 := by
  rw [euclideanReducedLength_def]
  set S := {l | ∃ γ : ℝ → E, IsEuclideanLPath γ 0 ∧ γ 0 = p ∧ γ 0 = q ∧
    l = euclideanLAction γ 0 / (2 * √0)}
  have hsub : S ⊆ {0} := by
    rintro l ⟨γ, _, _, _, rfl⟩
    simp [euclideanLAction]
  rcases S.eq_empty_or_nonempty with hS | ⟨l, hl⟩
  · simp [hS]
  · have hl0 : l = 0 := hsub hl
    have hS : S = {0} := subset_antisymm hsub (singleton_subset_iff.mpr (hl0 ▸ hl))
    simp [hS]

/-- The Euclidean reduced length is squared displacement divided by four times backward time. -/
theorem euclideanReducedLength_eq (p q : E) {t : ℝ} (ht : 0 ≤ t) :
    euclideanReducedLength p q t = ‖q - p‖ ^ 2 / (4 * t) := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  have hbound : ∀ l ∈ {l | ∃ γ : ℝ → E, IsEuclideanLPath γ t ∧ γ 0 = p ∧ γ t = q ∧
      l = euclideanLAction γ t / (2 * √t)}, ‖q - p‖ ^ 2 / (4 * t) ≤ l := by
    rintro l ⟨γ, hγ, h0, htq, rfl⟩
    have h := norm_sub_sq_div_le_euclideanLAction hγ
    rw [h0, htq] at h
    apply (le_div_iff₀ (by positivity : 0 < 2 * √t)).mpr
    convert h using 1
    field_simp
    nlinarith [Real.sq_sqrt ht.le]
  have hmem : ‖q - p‖ ^ 2 / (4 * t) ∈
      {l | ∃ γ : ℝ → E, IsEuclideanLPath γ t ∧ γ 0 = p ∧ γ t = q ∧
        l = euclideanLAction γ t / (2 * √t)} := by
    refine ⟨sqrtSegment p q t, isEuclideanLPath_sqrtSegment p q t,
      sqrtSegment_zero p q t, sqrtSegment_self p q ht, ?_⟩
    rw [euclideanLAction_sqrtSegment p q t]
    field_simp
    nlinarith [Real.sq_sqrt ht.le]
  exact le_antisymm (csInf_le ⟨_, hbound⟩ hmem) (le_csInf ⟨_, hmem⟩ hbound)

end TauCeti.ReducedGeometry
