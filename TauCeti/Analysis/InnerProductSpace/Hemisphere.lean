/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Closed hemispheres of a unit sphere

For a unit vector `p` of a real inner product space `E`, the closed hemisphere
`{x ∈ S | 0 ≤ ⟪x, p⟫}` of the unit sphere `S` of `E` is homeomorphic to the closed unit ball of
the hyperplane `(ℝ ∙ p)ᗮ`. The homeomorphism removes the component of `x` along `p`; its inverse
lifts a point `y` of the ball to `y + √(1 - ‖y‖²) • p`.

The closed hemispheres around `p` and `-p` cover the sphere and meet in the equator, the unit
sphere of `(ℝ ∙ p)ᗮ`, included in `S` by `TauCeti.equatorInclusion p`. Closed hemispheres are the
discs out of which the sphere is built in the inductive computations of the homology of the
complement of an embedded sphere.

## Main definitions

* `TauCeti.hemisphereHomeomorph p`: the closed hemisphere around `p` is homeomorphic to the closed
  unit ball of `(ℝ ∙ p)ᗮ`.
* `TauCeti.equatorInclusion p`: the inclusion of the equator, the unit sphere of `(ℝ ∙ p)ᗮ`, into
  the unit sphere of `E`.

## Main results

* `TauCeti.coe_hemisphereHomeomorph_apply` and `TauCeti.coe_hemisphereHomeomorph_symm_apply`:
  the formulas for the homeomorphism and its inverse.
* `TauCeti.range_equatorInclusion`: the equator is the intersection of the closed hemispheres
  around `p` and `-p`.
-/

public section

noncomputable section

open Metric Set
open scoped RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p : sphere (0 : E) 1)

/-- Removing from a point of the unit sphere its component along a unit vector `p` gives a vector
orthogonal to `p` of norm at most one. -/
private lemma sub_inner_smul_mem_closedBall (x : sphere (0 : E) 1) :
    (x : E) - ⟪(x : E), (p : E)⟫ • (p : E) ∈ (ℝ ∙ (p : E))ᗮ ∧
      ‖(x : E) - ⟪(x : E), (p : E)⟫ • (p : E)‖ ^ 2 = 1 - ⟪(x : E), (p : E)⟫ ^ 2 := by
  have hp : ⟪(p : E), (p : E)⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p, one_pow]
  have hx : ‖(x : E)‖ = 1 := norm_eq_of_mem_sphere x
  refine ⟨Submodule.mem_orthogonal_singleton_iff_inner_right.2 ?_, ?_⟩
  · rw [inner_sub_right, real_inner_smul_right, hp, real_inner_comm, mul_one, sub_self]
  · rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      norm_eq_of_mem_sphere p, hx]
    ring

/-- Lifting a point `y` of the closed unit ball of `(ℝ ∙ p)ᗮ` by `√(1 - ‖y‖²)` in the direction
of `p` lands on the unit sphere, with inner product `√(1 - ‖y‖²)` against `p`. -/
private lemma add_sqrt_smul_mem_sphere (y : closedBall (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    ‖((y : (ℝ ∙ (p : E))ᗮ) : E) + √(1 - ‖(y : (ℝ ∙ (p : E))ᗮ)‖ ^ 2) • (p : E)‖ = 1 ∧
      ⟪((y : (ℝ ∙ (p : E))ᗮ) : E) + √(1 - ‖(y : (ℝ ∙ (p : E))ᗮ)‖ ^ 2) • (p : E), (p : E)⟫ =
        √(1 - ‖(y : (ℝ ∙ (p : E))ᗮ)‖ ^ 2) := by
  have hp : ⟪(p : E), (p : E)⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p, one_pow]
  have hyp : ⟪((y : (ℝ ∙ (p : E))ᗮ) : E), (p : E)⟫ = 0 := by
    rw [real_inner_comm]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (y : (ℝ ∙ (p : E))ᗮ).2
  have hy : ‖(y : (ℝ ∙ (p : E))ᗮ)‖ ^ 2 ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (mem_closedBall_zero_iff.1 y.2)
  refine ⟨?_, by rw [inner_add_left, real_inner_smul_left, hyp, hp, zero_add, mul_one]⟩
  rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, norm_add_sq_real,
    real_inner_smul_right, hyp, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by linarith),
    norm_eq_of_mem_sphere p, Submodule.norm_coe]
  ring

/-- **The closed hemisphere around `p` is a disc.** For a point `p` of the unit sphere of a real
inner product space `E`, the closed hemisphere `{x | 0 ≤ ⟪x, p⟫}` of the unit sphere is
homeomorphic to the closed unit ball of the orthogonal complement `(ℝ ∙ p)ᗮ`. The homeomorphism
sends `x` to `x - ⟪x, p⟫ • p` (`TauCeti.coe_hemisphereHomeomorph_apply`), and its inverse sends `y`
to `y + √(1 - ‖y‖²) • p` (`TauCeti.coe_hemisphereHomeomorph_symm_apply`). -/
def hemisphereHomeomorph :
    {x : sphere (0 : E) 1 // 0 ≤ ⟪(x : E), (p : E)⟫} ≃ₜ closedBall (0 : (ℝ ∙ (p : E))ᗮ) 1 where
  toFun x := ⟨⟨_, (sub_inner_smul_mem_closedBall p x).1⟩, mem_closedBall_zero_iff.2 <|
    (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 <| by
      simp only [← Submodule.norm_coe, (sub_inner_smul_mem_closedBall p x).2]
      linarith [sq_nonneg ⟪((x : sphere (0 : E) 1) : E), (p : E)⟫]⟩
  invFun y := ⟨⟨_, mem_sphere_zero_iff_norm.2 (add_sqrt_smul_mem_sphere p y).1⟩,
    (add_sqrt_smul_mem_sphere p y).2.symm ▸ Real.sqrt_nonneg _⟩
  left_inv x := by
    obtain ⟨⟨x, hx⟩, hxp⟩ := x
    refine Subtype.ext (Subtype.ext ?_)
    have h := (sub_inner_smul_mem_closedBall p ⟨x, hx⟩).2
    simp only [← Submodule.norm_coe, h, sub_sub_cancel, Real.sqrt_sq hxp, sub_add_cancel]
  right_inv y := by
    refine Subtype.ext (Subtype.ext ?_)
    simp only [(add_sqrt_smul_mem_sphere p y).2, add_sub_cancel_right]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- `TauCeti.hemisphereHomeomorph p` removes the component along `p`. -/
@[simp]
theorem coe_hemisphereHomeomorph_apply (x : {x : sphere (0 : E) 1 // 0 ≤ ⟪(x : E), (p : E)⟫}) :
    ((hemisphereHomeomorph p x : (ℝ ∙ (p : E))ᗮ) : E) =
      ((x : sphere (0 : E) 1) : E) - ⟪((x : sphere (0 : E) 1) : E), (p : E)⟫ • (p : E) :=
  (rfl)

/-- The inverse of `TauCeti.hemisphereHomeomorph p` lifts a point `y` of the closed unit ball of
`(ℝ ∙ p)ᗮ` to `y + √(1 - ‖y‖²) • p`. -/
@[simp]
theorem coe_hemisphereHomeomorph_symm_apply (y : closedBall (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    (((hemisphereHomeomorph p).symm y : sphere (0 : E) 1) : E) =
      ((y : (ℝ ∙ (p : E))ᗮ) : E) + √(1 - ‖(y : (ℝ ∙ (p : E))ᗮ)‖ ^ 2) • (p : E) :=
  (rfl)

/-- The inclusion of the equator, the unit sphere of `(ℝ ∙ p)ᗮ`, into the unit sphere of `E`. -/
def equatorInclusion : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 → sphere (0 : E) 1 :=
  fun y ↦ ⟨((y : (ℝ ∙ (p : E))ᗮ) : E), mem_sphere_zero_iff_norm.2
    ((Submodule.norm_coe _).trans (norm_eq_of_mem_sphere y))⟩

/-- `TauCeti.equatorInclusion p` is the inclusion of `(ℝ ∙ p)ᗮ` into `E`. -/
@[simp]
theorem coe_equatorInclusion_apply (y : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    (equatorInclusion p y : E) = ((y : (ℝ ∙ (p : E))ᗮ) : E) :=
  (rfl)

/-- The inclusion of the equator is continuous. -/
theorem continuous_equatorInclusion : Continuous (equatorInclusion p) := by
  unfold equatorInclusion
  fun_prop

/-- The inclusion of the equator is injective. -/
theorem injective_equatorInclusion : Function.Injective (equatorInclusion p) := fun _ _ hyy' ↦
  Subtype.ext (Subtype.ext (congrArg (fun z : sphere (0 : E) 1 ↦ (z : E)) hyy'))

/-- The equator is the set of points of the sphere orthogonal to `p`, the intersection of the two
closed hemispheres around `p` and `-p`. -/
theorem range_equatorInclusion :
    range (equatorInclusion p) = {x : sphere (0 : E) 1 | 0 ≤ ⟪(x : E), (p : E)⟫} ∩
      {x : sphere (0 : E) 1 | 0 ≤ ⟪(x : E), ((-p : sphere (0 : E) 1) : E)⟫} := by
  refine Set.ext fun x ↦ ?_
  simp only [mem_inter_iff, mem_ofPred_eq, coe_neg_sphere, inner_neg_right, neg_nonneg,
    ← le_antisymm_iff, eq_comm (a := (0 : ℝ))]
  constructor
  · rintro ⟨y, rfl⟩
    rw [real_inner_comm]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (y : (ℝ ∙ (p : E))ᗮ).2
  · intro hx
    refine ⟨⟨⟨x, Submodule.mem_orthogonal_singleton_iff_inner_right.2 ?_⟩,
      mem_sphere_zero_iff_norm.2 (norm_eq_of_mem_sphere x)⟩, rfl⟩
    rwa [real_inner_comm]

end TauCeti
