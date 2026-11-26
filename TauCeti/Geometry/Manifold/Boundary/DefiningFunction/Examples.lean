/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.DefiningFunction.Basic
public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Inclusion
public import TauCeti.Geometry.Manifold.Instances.Icc.Boundary
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Boundary defining functions of the closed ball and of closed intervals

This file computes boundary defining functions (`TauCeti.IsBoundaryDefiningFunctionOn`) on the
two model manifolds with boundary.

* On the closed unit ball of a real inner product space `E` of dimension `n + 1`,
  `ρ = 1 - ‖x‖²` is a global boundary defining function
  (`TauCeti.isBoundaryDefiningFunctionOn_closedBall`), whose differential sends the tangent vector
  `v` to `-2 ⟪x, v⟫` (`TauCeti.mvfderiv_closedBallDefiningFunction_symm_apply`); in particular it
  sends the radial vector `x` to `-2` on the sphere. For every `a` with `‖a‖ ≤ 1`,
  `(2 + ⟪a, x⟫) ρ` is another one (`TauCeti.isBoundaryDefiningFunctionOn_closedBall_mul`), with
  ratio `2 + ⟪a, x⟫ ∈ [1, 3]` (`TauCeti.two_add_inner_mem_Icc`); `ρ²` is not one, since its
  differential vanishes on the sphere, and `-ρ` is not one, since it is negative inside.
* On `[a, b]` with `a < b`, `ρ(x) = (x - a) (b - x)` is a global boundary defining function
  (`TauCeti.isBoundaryDefiningFunctionOn_interval`), whose differential sends the unit tangent
  vector `1` to `a + b - 2 x` (`TauCeti.mvfderiv_intervalDefiningFunction_one`), so to `b - a` at
  `a` and to `a - b` at `b`. On `[0, 1]` this is `ρ(x) = x (1 - x)`, with differential `±1` at
  the ends.
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

omit [InnerProductSpace ℝ E] in
@[simp]
theorem closedBallDefiningFunction_apply (x : closedBall (0 : E) 1) :
    closedBallDefiningFunction x = 1 - ‖(x : E)‖ ^ 2 :=
  (rfl)

private theorem contDiff_one_sub_norm_sq {k : ℕ∞ω} :
    ContDiff ℝ k (fun y : E ↦ 1 - ‖y‖ ^ 2) :=
  contDiff_const.sub (contDiff_norm_sq ℝ)

/-- The differential of `1 - ‖x‖²` on the closed ball sends a vector `v`, read as a tangent
vector through the inclusion, to `-2 ⟪x, v⟫`. -/
theorem mvfderiv_closedBallDefiningFunction_symm_apply (x : closedBall (0 : E) 1) (v : E) :
    mvfderiv (𝓡∂ (n + 1)) closedBallDefiningFunction x
        ((subtypeValClosedBallTangentEquiv (n := n + 1) x).symm v) =
      -2 * ⟪(x : E), v⟫ := by
  have hg : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) (fun y : E ↦ 1 - ‖y‖ ^ 2) (x : E) :=
    (contDiff_one_sub_norm_sq (k := 1)).contMDiff.mdifferentiableAt one_ne_zero
  have hι : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ, E) (Subtype.val : closedBall (0 : E) 1 → E) x :=
    (contMDiff_subtypeVal_closedBall (n := n + 1) (k := 1)).mdifferentiableAt one_ne_zero
  have hcomp : closedBallDefiningFunction (E := E) =
      (fun y : E ↦ 1 - ‖y‖ ^ 2) ∘ (Subtype.val : closedBall (0 : E) 1 → E) := rfl
  rw [hcomp, mvfderiv_comp_apply x hg hι, mfderiv_subtypeVal_closedBall_symm_apply,
    mvfderiv_eq_fderiv, fderiv_const_sub, fderiv_norm_sq_apply]
  -- The tangent vector `x` lives in `TangentSpace 𝓘(ℝ, E) x`, which is `E` by definition;
  -- re-type it so that the evaluation lemmas of `E →L[ℝ] ℝ` apply.
  change (-(2 • innerSL ℝ (x : E)) : E →L[ℝ] ℝ) v = -2 * ⟪(x : E), v⟫
  simp

/-- **`1 - ‖x‖²` is a global boundary defining function of the closed unit ball.** -/
theorem isBoundaryDefiningFunctionOn_closedBall :
    IsBoundaryDefiningFunctionOn n (closedBallDefiningFunction (E := E)) univ where
  isOpen := isOpen_univ
  contMDiffOn := (contDiff_one_sub_norm_sq.contMDiff.comp
    (contMDiff_subtypeVal_closedBall (n := n + 1))).contMDiffOn
  pos x _ hx := by
    have h := (isInteriorPoint_closedBall_iff (n := n + 1)).1 hx
    have h0 := norm_nonneg (x : E)
    rw [closedBallDefiningFunction_apply]
    nlinarith
  eq_zero x _ hx := by
    simp [(isBoundaryPoint_closedBall_iff (n := n + 1)).1 hx]
  mvfderiv_ne_zero x _ hx h0 := by
    have h := mvfderiv_closedBallDefiningFunction_symm_apply (n := n) x x
    rw [h0, real_inner_self_eq_norm_sq, (isBoundaryPoint_closedBall_iff (n := n + 1)).1 hx] at h
    simp at h

/-- The ratio `2 + ⟪a, x⟫` lies in `[1, 3]` on the closed unit ball when `‖a‖ ≤ 1`. -/
theorem two_add_inner_mem_Icc {a : E} (ha : ‖a‖ ≤ 1) (x : closedBall (0 : E) 1) :
    2 + ⟪a, (x : E)⟫ ∈ Icc (1 : ℝ) 3 := by
  have h := abs_real_inner_le_norm a (x : E)
  have hx := mem_closedBall_zero_iff.1 x.property
  have : ‖a‖ * ‖(x : E)‖ ≤ 1 := by nlinarith [norm_nonneg a, norm_nonneg (x : E)]
  rw [abs_le] at h
  constructor <;> linarith

/-- For every `a` with `‖a‖ ≤ 1`, the product `(2 + ⟪a, x⟫)(1 - ‖x‖²)` is another global boundary
defining function of the closed unit ball; its ratio to `1 - ‖x‖²` lies in `[1, 3]` by
`two_add_inner_mem_Icc`. -/
theorem isBoundaryDefiningFunctionOn_closedBall_mul {a : E} (ha : ‖a‖ ≤ 1) :
    IsBoundaryDefiningFunctionOn n
      (fun x : closedBall (0 : E) 1 ↦ (2 + ⟪a, (x : E)⟫) * closedBallDefiningFunction x) univ := by
  refine (isBoundaryDefiningFunctionOn_closedBall (n := n)).mul_left ?_ fun x _ ↦ ?_
  · exact ((contDiff_const.add (contDiff_const.inner ℝ contDiff_id)).contMDiff.comp
      (contMDiff_subtypeVal_closedBall (n := n + 1))).contMDiffOn
  · exact one_pos.trans_le (two_add_inner_mem_Icc ha x).1

/-- The square `(1 - ‖x‖²)²` is not a boundary defining function of the closed unit ball: its
differential vanishes on the boundary sphere. -/
theorem not_isBoundaryDefiningFunctionOn_closedBall_mul_self :
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

/-! ### The closed interval -/

section Interval

/-- The boundary defining function `(x - a) (b - x)` of `[a, b]`. -/
def intervalDefiningFunction (a b : ℝ) (x : Icc a b) : ℝ := ((x : ℝ) - a) * (b - x)

@[simp]
theorem intervalDefiningFunction_apply (a b : ℝ) (x : Icc a b) :
    intervalDefiningFunction a b x = ((x : ℝ) - a) * (b - x) :=
  (rfl)

variable {a b : ℝ}

private theorem contDiff_sub_mul_sub {k : ℕ∞ω} :
    ContDiff ℝ k (fun r : ℝ ↦ (r - a) * (b - r)) := by
  fun_prop

variable [Fact (a < b)]

/-- The differential of `(x - a) (b - x)` sends the unit tangent vector `1` of `[a, b]`, the image
of `1 ∈ ℝ`, to `a + b - 2 x`. -/
theorem mvfderiv_intervalDefiningFunction_one (x : Icc a b) :
    -- Mathlib's unit tangent vector of `[a, b]` is only provided at the model `𝓡∂ 1`, which is
    -- `𝓡∂ (0 + 1)` by definition.
    mvfderiv (𝓡∂ (0 + 1)) (intervalDefiningFunction a b) x (1 : TangentSpace (𝓡∂ 1) x) =
      a + b - 2 * (x : ℝ) := by
  have hg : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ) (fun r : ℝ ↦ (r - a) * (b - r)) (x : ℝ) :=
    (contDiff_sub_mul_sub (k := 1)).contMDiff.mdifferentiableAt one_ne_zero
  have hι : MDifferentiableAt (𝓡∂ (0 + 1)) 𝓘(ℝ) (Subtype.val : Icc a b → ℝ) x :=
    (contMDiff_subtypeVal_Icc (n := 1)).mdifferentiableAt one_ne_zero
  have hcomp : intervalDefiningFunction a b =
      (fun r : ℝ ↦ (r - a) * (b - r)) ∘ (Subtype.val : Icc a b → ℝ) := rfl
  -- `mfderiv_subtypeVal_Icc_one` is stated at `𝓡∂ 1`; it applies at `𝓡∂ (0 + 1)` because the two
  -- models, and their interval charts, agree by definition.
  rw [hcomp, mvfderiv_comp_apply x hg hι, mfderiv_subtypeVal_Icc_one, mvfderiv_eq_fderiv]
  have hd : HasDerivAt (fun r : ℝ ↦ (r - a) * (b - r)) (1 * (b - (x : ℝ)) + ((x : ℝ) - a) * (0 - 1))
      (x : ℝ) :=
    ((hasDerivAt_id _).sub_const a).mul ((hasDerivAt_const _ _).sub (hasDerivAt_id _))
  -- `mvfderiv_eq_fderiv` composes with the identification `TangentSpace 𝓘(ℝ) x = ℝ`, which is
  -- the identity by definition; drop it to read the differential as the derivative.
  change fderiv ℝ (fun r : ℝ ↦ (r - a) * (b - r)) (x : ℝ) 1 = a + b - 2 * (x : ℝ)
  rw [fderiv_apply_one_eq_deriv, hd.deriv]
  ring

/-- **`(x - a) (b - x)` is a global boundary defining function of `[a, b]`.** For `a = 0` and
`b = 1` this is `x (1 - x)` on `[0, 1]`. -/
theorem isBoundaryDefiningFunctionOn_interval :
    IsBoundaryDefiningFunctionOn 0 (intervalDefiningFunction a b) univ where
  -- The boundary and interior facts `hx` below are at the model `𝓡∂ (0 + 1)` with the charts
  -- `instChartedSpaceIccZeroAddOne`. `Icc_isBoundaryPoint_iff` and `Icc_isInteriorPoint_iff` are
  -- stated at Mathlib's `𝓡∂ 1` and its interval charts, and apply here because these models and
  -- charts agree by definition.
  isOpen := isOpen_univ
  contMDiffOn := (contDiff_sub_mul_sub.contMDiff.comp contMDiff_subtypeVal_Icc).contMDiffOn
  pos x _ hx := by
    obtain ⟨ha, hb⟩ := (Icc_isInteriorPoint_iff x).1 hx
    rw [intervalDefiningFunction_apply]
    exact mul_pos (by linarith) (by linarith)
  eq_zero x _ hx := by
    rcases (Icc_isBoundaryPoint_iff x).1 hx with h | h <;> simp [h]
  mvfderiv_ne_zero x _ hx h0 := by
    have hab : a < b := Fact.out
    have h := mvfderiv_intervalDefiningFunction_one x
    rw [h0] at h
    rcases (Icc_isBoundaryPoint_iff x).1 hx with hx | hx <;> rw [hx] at h <;> norm_num at h <;>
      linarith

end Interval

end TauCeti
