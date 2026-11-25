/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.DefiningFunction.Basic
public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Inclusion
public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Boundary defining functions of the closed ball and the interval

This file computes boundary defining functions (`TauCeti.IsBoundaryDefiningFunctionOn`) on the
two model manifolds with boundary.

* On the closed unit ball of a real inner product space `E` of dimension `n + 1`,
  `ρ = 1 - ‖x‖²` is a global boundary defining function
  (`TauCeti.isBoundaryDefiningFunctionOn_closedBall`), whose differential sends the radial vector
  `x` to `-2 ‖x‖²`, so to `-2` on the sphere
  (`TauCeti.mvfderiv_closedBallDefiningFunction_radial`). For every `a` with `‖a‖ ≤ 1`,
  `(2 + ⟪a, x⟫) ρ` is another one, with ratio `2 + ⟪a, x⟫ ∈ [1, 3]`
  (`TauCeti.isBoundaryDefiningFunctionOn_closedBall_mul`); `ρ²` is not one, since its
  differential vanishes on the sphere, and `-ρ` is not one, since it is negative inside.
* On `[0, 1]`, `ρ(x) = x (1 - x)` is a global boundary defining function
  (`TauCeti.isBoundaryDefiningFunctionOn_unitInterval`), whose differential sends the unit tangent
  vector `1` to `1 - 2 x` (`TauCeti.mvfderiv_unitIntervalDefiningFunction_one`), so to `1` at `0`
  and to `-1` at `1`.
-/

public section

noncomputable section

open Set Metric Module
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

/-! ### The closed unit ball -/

section ClosedBall

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = n + 1)]

/-- The boundary defining function `1 - ‖x‖²` of the closed unit ball. -/
def closedBallDefiningFunction (x : closedBall (0 : E) 1) : ℝ := 1 - ‖(x : E)‖ ^ 2

private theorem contDiff_one_sub_norm_sq {k : ℕ∞ω} :
    ContDiff ℝ k (fun y : E ↦ 1 - ‖y‖ ^ 2) :=
  contDiff_const.sub (contDiff_norm_sq ℝ)

/-- The differential of `1 - ‖x‖²` on the closed ball sends the radial vector `x`, read as a
tangent vector through the inclusion, to `-2 ‖x‖²`. -/
theorem mvfderiv_closedBallDefiningFunction_radial (x : closedBall (0 : E) 1) :
    mvfderiv (𝓡∂ (n + 1)) closedBallDefiningFunction x
        ((subtypeValClosedBallTangentEquiv (n := n + 1) x).symm (x : E)) =
      -2 * ‖(x : E)‖ ^ 2 := by
  have hg : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) (fun y : E ↦ 1 - ‖y‖ ^ 2) (x : E) :=
    (contDiff_one_sub_norm_sq (k := 1)).contMDiff.mdifferentiableAt one_ne_zero
  have hι : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ, E) (Subtype.val : closedBall (0 : E) 1 → E) x :=
    (contMDiff_subtypeVal_closedBall (n := n + 1) (k := 1)).mdifferentiableAt one_ne_zero
  have hcomp : closedBallDefiningFunction (E := E) =
      (fun y : E ↦ 1 - ‖y‖ ^ 2) ∘ (Subtype.val : closedBall (0 : E) 1 → E) := rfl
  have hv : mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, E) (Subtype.val : closedBall (0 : E) 1 → E) x
      ((subtypeValClosedBallTangentEquiv (n := n + 1) x).symm (x : E)) = (x : E) := by
    have he := ContinuousLinearMap.ext_iff.1
      (subtypeValClosedBallTangentEquiv_toContinuousLinearMap (n := n + 1) x)
      ((subtypeValClosedBallTangentEquiv (n := n + 1) x).symm (x : E))
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at he
    exact he.symm
  rw [hcomp, mvfderiv_comp_apply x hg hι, hv, mvfderiv_eq_fderiv,
    fderiv_const_sub, fderiv_norm_sq_apply]
  change (-(2 • innerSL ℝ (x : E)) : E →L[ℝ] ℝ) (x : E) = -2 * ‖(x : E)‖ ^ 2
  rw [neg_apply, smul_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq, two_smul]
  ring

/-- **`1 - ‖x‖²` is a global boundary defining function of the closed unit ball.** -/
theorem isBoundaryDefiningFunctionOn_closedBall :
    IsBoundaryDefiningFunctionOn n (closedBallDefiningFunction (E := E)) univ where
  isOpen := isOpen_univ
  contMDiffOn := (contDiff_one_sub_norm_sq.contMDiff.comp
    (contMDiff_subtypeVal_closedBall (n := n + 1))).contMDiffOn
  pos x _ hx := by
    have h := (isInteriorPoint_closedBall_iff (n := n + 1)).1 hx
    have h0 := norm_nonneg (x : E)
    change 0 < 1 - ‖(x : E)‖ ^ 2
    nlinarith
  eq_zero x _ hx := by
    change 1 - ‖(x : E)‖ ^ 2 = 0
    simp [(isBoundaryPoint_closedBall_iff (n := n + 1)).1 hx]
  mvfderiv_ne_zero x _ hx h0 := by
    have h := mvfderiv_closedBallDefiningFunction_radial (n := n) x
    rw [h0, (isBoundaryPoint_closedBall_iff (n := n + 1)).1 hx] at h
    simp at h

/-- For every `a` with `‖a‖ ≤ 1`, the product `(2 + ⟪a, x⟫)(1 - ‖x‖²)` is another global boundary
defining function of the closed unit ball, with ratio `2 + ⟪a, x⟫ ∈ [1, 3]` to `1 - ‖x‖²`. -/
theorem isBoundaryDefiningFunctionOn_closedBall_mul {a : E} (ha : ‖a‖ ≤ 1) :
    IsBoundaryDefiningFunctionOn n
      (fun x : closedBall (0 : E) 1 ↦ (2 + ⟪a, (x : E)⟫) * closedBallDefiningFunction x) univ := by
  refine (isBoundaryDefiningFunctionOn_closedBall (n := n)).mul_left ?_ fun x _ ↦ ?_
  · exact ((contDiff_const.add (contDiff_const.inner ℝ contDiff_id)).contMDiff.comp
      (contMDiff_subtypeVal_closedBall (n := n + 1))).contMDiffOn
  · have h := abs_real_inner_le_norm a (x : E)
    have hx := mem_closedBall_zero_iff.1 x.property
    have : ‖a‖ * ‖(x : E)‖ ≤ 1 := by nlinarith [norm_nonneg a, norm_nonneg (x : E)]
    rw [abs_le] at h
    linarith

/-- The ratio `2 + ⟪a, x⟫` lies in `[1, 3]` on the closed unit ball when `‖a‖ ≤ 1`. -/
theorem two_add_inner_mem_Icc {a : E} (ha : ‖a‖ ≤ 1) (x : closedBall (0 : E) 1) :
    2 + ⟪a, (x : E)⟫ ∈ Icc (1 : ℝ) 3 := by
  have h := abs_real_inner_le_norm a (x : E)
  have hx := mem_closedBall_zero_iff.1 x.property
  have : ‖a‖ * ‖(x : E)‖ ≤ 1 := by nlinarith [norm_nonneg a, norm_nonneg (x : E)]
  rw [abs_le] at h
  constructor <;> linarith

/-- The square `(1 - ‖x‖²)²` is not a boundary defining function of the closed unit ball: its
differential vanishes on the boundary sphere. -/
theorem not_isBoundaryDefiningFunctionOn_closedBall_sq :
    ¬IsBoundaryDefiningFunctionOn n
      (fun x : closedBall (0 : E) 1 ↦ closedBallDefiningFunction x * closedBallDefiningFunction x)
      univ := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    rw [Fact.out (p := finrank ℝ E = n + 1)]
    exact Nat.succ_pos n)
  obtain ⟨y, hy⟩ := exists_norm_eq E zero_le_one
  exact (isBoundaryDefiningFunctionOn_closedBall (n := n)).not_mul_self (mem_univ ⟨y, by simp [hy]⟩)
    ((isBoundaryPoint_closedBall_iff (n := n + 1)).2 hy)

/-- The negative `-(1 - ‖x‖²)` is not a boundary defining function of the closed unit ball: it is
negative inside. -/
theorem not_isBoundaryDefiningFunctionOn_closedBall_neg :
    ¬IsBoundaryDefiningFunctionOn n
      (fun x : closedBall (0 : E) 1 ↦ -closedBallDefiningFunction x) univ :=
  (isBoundaryDefiningFunctionOn_closedBall (n := n)).not_neg (mem_univ ⟨0, by simp⟩)
    ((isInteriorPoint_closedBall_iff (n := n + 1)).2 (by simp))

end ClosedBall

/-! ### The unit interval -/

section UnitInterval

open Fact.Manifold

/-- The interval charts of `[0, 1]`, with the model dimension written as the successor `0 + 1`
used by the boundary constructions. -/
@[reducible] local instance instChartedSpaceUnitIntervalZeroAddOne :
    ChartedSpace (EuclideanHalfSpace (0 + 1)) (Icc (0 : ℝ) 1) :=
  instIccChartedSpace 0 1

/-- The interval `[0, 1]` is an analytic manifold for the charts
`instChartedSpaceUnitIntervalZeroAddOne`. -/
local instance instIsManifoldUnitIntervalZeroAddOne {k : ℕ∞ω} :
    IsManifold (𝓡∂ (0 + 1)) k (Icc (0 : ℝ) 1) :=
  instIsManifoldIcc 0 1

/-- The boundary defining function `x (1 - x)` of `[0, 1]`. -/
def unitIntervalDefiningFunction (x : Icc (0 : ℝ) 1) : ℝ := (x : ℝ) * (1 - x)

private theorem contDiff_mul_one_sub {k : ℕ∞ω} : ContDiff ℝ k (fun r : ℝ ↦ r * (1 - r)) := by
  fun_prop

/-- The differential of `x (1 - x)` sends the unit tangent vector `1` of `[0, 1]`, the image of
`1 ∈ ℝ`, to `1 - 2 x`. -/
theorem mvfderiv_unitIntervalDefiningFunction_one (x : Icc (0 : ℝ) 1) :
    mvfderiv (𝓡∂ (0 + 1)) unitIntervalDefiningFunction x (1 : TangentSpace (𝓡∂ 1) x) =
      1 - 2 * (x : ℝ) := by
  have hg : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ) (fun r : ℝ ↦ r * (1 - r)) (x : ℝ) :=
    (contDiff_mul_one_sub (k := 1)).contMDiff.mdifferentiableAt one_ne_zero
  have hι : MDifferentiableAt (𝓡∂ (0 + 1)) 𝓘(ℝ) (Subtype.val : Icc (0 : ℝ) 1 → ℝ) x :=
    (contMDiff_subtypeVal_Icc (n := 1)).mdifferentiableAt one_ne_zero
  have hcomp : unitIntervalDefiningFunction =
      (fun r : ℝ ↦ r * (1 - r)) ∘ (Subtype.val : Icc (0 : ℝ) 1 → ℝ) := rfl
  rw [hcomp, mvfderiv_comp_apply x hg hι, mfderiv_subtypeVal_Icc_one, mvfderiv_eq_fderiv]
  have hd : HasDerivAt (fun r : ℝ ↦ r * (1 - r)) (1 * (1 - (x : ℝ)) + (x : ℝ) * (0 - 1))
      (x : ℝ) := (hasDerivAt_id _).mul ((hasDerivAt_const _ _).sub (hasDerivAt_id _))
  rw [hd.hasFDerivAt.fderiv]
  change ContinuousLinearMap.toSpanSingleton ℝ (1 * (1 - (x : ℝ)) + (x : ℝ) * (0 - 1)) (1 : ℝ) =
    1 - 2 * (x : ℝ)
  rw [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  ring

/-- **`x (1 - x)` is a global boundary defining function of `[0, 1]`.** -/
theorem isBoundaryDefiningFunctionOn_unitInterval :
    IsBoundaryDefiningFunctionOn 0 unitIntervalDefiningFunction univ where
  isOpen := isOpen_univ
  contMDiffOn := (contDiff_mul_one_sub.contMDiff.comp contMDiff_subtypeVal_Icc).contMDiffOn
  pos x _ hx := by
    have hb : x ∉ ({⊥, ⊤} : Set (Icc (0 : ℝ) 1)) := fun h ↦
      (ModelWithCorners.disjoint_interior_boundary (I := 𝓡∂ (0 + 1))).ne_of_mem hx
        ((Set.ext_iff.1 boundary_Icc x).2 h) rfl
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hb
    have h0 : (0 : ℝ) < x := lt_of_le_of_ne x.property.1 fun h ↦ hb.1 (Subtype.ext h.symm)
    have h1 : (x : ℝ) < 1 := lt_of_le_of_ne x.property.2 fun h ↦ hb.2 (Subtype.ext h)
    exact mul_pos h0 (by linarith)
  eq_zero x _ hx := by
    rcases (Set.ext_iff.1 boundary_Icc x).1 hx with h | h
    · simp [unitIntervalDefiningFunction, h]
    · rw [mem_singleton_iff] at h
      simp [unitIntervalDefiningFunction, h]
  mvfderiv_ne_zero x _ hx h0 := by
    have h := mvfderiv_unitIntervalDefiningFunction_one x
    rw [h0] at h
    rcases (Set.ext_iff.1 boundary_Icc x).1 hx with hb | hb
    · rw [hb] at h
      norm_num at h
    · rw [mem_singleton_iff] at hb
      rw [hb] at h
      norm_num at h

end UnitInterval

end TauCeti
