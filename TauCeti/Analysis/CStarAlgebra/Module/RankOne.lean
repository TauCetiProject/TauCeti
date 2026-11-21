/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Action
public import TauCeti.Analysis.CStarAlgebra.Module.AdjointPair

/-!
# Rank-one operators on Hilbert C⋆-modules

`CStarModule.rankOne A x y` is the bounded module map sending `z` to
`inner A y z • x`. For a right Hilbert B-module, take `A = Bᵐᵒᵖ`; this is
then the usual operator `θ_(x,y) z = x ⟨y,z⟩_B`.

These operators generate the module-compact operators. They need not have
finite-dimensional complex range, nor be compact as Banach-space operators.
We prove their adjoint-pair identity, composition formulas, the norm bound,
and the exact diagonal norm `‖θ_(x,x)‖ = ‖x‖²`. No completeness or unitality
is required.

## References

* I. Raeburn and D. P. Williams, *Morita Equivalence and Continuous-Trace
  C⋆-Algebras*, Chapter 2, Definition 2.24.
* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1.
-/

public section

variable {A E F G : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul A G] [CStarModule A G]

namespace CStarModule

/-- The module rank-one operator `z ↦ inner A y z • x`. With `A = Bᵐᵒᵖ`,
this is the usual right-module operator `z ↦ x ⟨y,z⟩_B`. -/
noncomputable def rankOne (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [SMul A E] [CStarModule A E] [SMul A F] [CStarModule A F]
    (x : F) (y : E) : E →L[ℂ] F := by
  letI := distribSMul A F
  letI := isScalarTower A F
  refine LinearMap.mkContinuous
    { toFun := fun z ↦ inner A y z • x
      map_add' := fun z w ↦ by simp [CStarModule.add_smul]
      map_smul' := fun c z ↦ by simp [smul_assoc] }
    (‖x‖ * ‖y‖) ?_
  intro z
  calc
    ‖inner A y z • x‖ ≤ ‖inner A y z‖ * ‖x‖ := CStarModule.norm_smul_le _ _
    _ ≤ (‖y‖ * ‖z‖) * ‖x‖ := by gcongr; exact norm_inner_le E
    _ = (‖x‖ * ‖y‖) * ‖z‖ := by ring

@[simp]
lemma rankOne_apply (x : F) (y z : E) : rankOne A x y z = inner A y z • x := (rfl)

/-- Rank-one operators commute with the coefficient action, including for nonunital A. -/
lemma rankOne_smul_coeff (x : F) (y z : E) (a : A) :
    rankOne A x y (a • z) = a • rankOne A x y z := by
  let := semigroupAction A F
  simp [mul_smul]

@[simp]
lemma rankOne_zero_left (y : E) : rankOne A (0 : F) y = 0 := by
  let := distribSMul A F
  ext z
  simp

@[simp]
lemma rankOne_zero_right (x : F) : rankOne A x (0 : E) = 0 := by
  let := smulWithZero A F
  ext z
  simp

/-- Rank-one operators are additive in their range vector. -/
@[simp]
lemma rankOne_add_left (x u : F) (y : E) :
    rankOne A (x + u) y = rankOne A x y + rankOne A u y := by
  let := distribSMul A F
  ext z
  simp [smul_add]

/-- Rank-one operators are additive in their inner-product vector. -/
@[simp]
lemma rankOne_add_right (x : F) (y v : E) :
    rankOne A x (y + v) = rankOne A x y + rankOne A x v := by
  ext z
  simp [CStarModule.add_smul]

/-- Rank-one operators are complex-linear in their range vector. -/
@[simp]
lemma rankOne_smul_left (c : ℂ) (x : F) (y : E) :
    rankOne A (c • x) y = c • rankOne A x y := by
  let := smulCommClass A F
  ext z
  simp [smul_comm c]

/-- Rank-one operators are conjugate-linear in their inner-product vector. -/
@[simp]
lemma rankOne_smul_right (c : ℂ) (x : F) (y : E) :
    rankOne A x (c • y) = star c • rankOne A x y := by
  let := isScalarTower A F
  ext z
  simp [smul_assoc]

/-- Moving a coefficient between the two vectors requires its adjoint. -/
lemma rankOne_smul_coeff_left (a : A) (x : F) (y : E) :
    rankOne A (a • x) y = rankOne A x (star a • y) := by
  let := semigroupAction A F
  ext z
  simp [mul_smul]

/-- The operator norm of a module rank-one map is at most the product of the vector norms. -/
lemma norm_rankOne_le (x : F) (y : E) : ‖rankOne A x y‖ ≤ ‖x‖ * ‖y‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- Interchanging the two vectors gives the module adjoint. -/
lemma inner_left_rankOne_apply (x : F) (y z : E) (w : F) :
    inner A (rankOne A x y z) w = inner A z (rankOne A y x w) := by
  simp

/-- The rank-one maps associated to `(x,y)` and `(y,x)` form an adjoint pair. -/
lemma isAdjointPair_rankOne (x : F) (y : E) :
    LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip (rankOne A x y) (rankOne A y x) :=
  isAdjointPair_inner_iff.mpr (inner_left_rankOne_apply x y)

/-- Composing module rank-one maps again gives a module rank-one map. -/
lemma rankOne_comp_rankOne (x : G) (y u : F) (v : E) :
    (rankOne A x y).comp (rankOne A u v) = rankOne A (inner A y u • x) v := by
  let := semigroupAction A G
  ext z
  simp [mul_smul]

end CStarModule

namespace ContinuousLinearMap

open CStarModule

/-- Postcomposition by a bounded module map acts on the range vector. -/
lemma comp_rankOne_cstarModule (T : F →L[ℂ] G) (hT : ∀ (a : A) z, T (a • z) = a • T z)
    (x : F) (y : E) :
    T.comp (rankOne A x y) = rankOne A (T x) y := by
  ext z
  simp [hT]

/-- Precomposition by an adjointable map acts by its adjoint on the second vector.
The adjoint can be supplied as a function. -/
lemma rankOne_comp_cstarModule (T : E →L[ℂ] F) (S : F → E)
    (h : LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) (x : G) (y : F) :
    (rankOne A x y).comp T = rankOne A x (S y) := by
  ext z
  simp [← h.symm_cstarModule.inner_eq_cstarModule]

end ContinuousLinearMap

namespace CStarModule

/-- Diagonal rank-one operators have nonnegative quadratic forms. -/
lemma inner_rankOne_self_nonneg (x z : E) : 0 ≤ inner A z (rankOne A x x z) := by
  simpa using mul_star_self_nonneg (inner A x z)

/-- The exact norm of a diagonal module rank-one operator. Unlike the scalar case,
the off-diagonal norm need not equal the product of the vector norms. -/
@[simp]
lemma norm_rankOne_self (x : E) : ‖rankOne A x x‖ = ‖x‖ ^ 2 := by
  apply le_antisymm ((norm_rankOne_le x x).trans_eq (sq _).symm)
  by_cases hx : x = 0
  · simp [hx]
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h : (‖x‖ ^ 2) ^ 2 ≤ ‖x‖ ^ 2 * ‖rankOne A x x‖ := calc
    (‖x‖ ^ 2) ^ 2 = ‖inner A x (rankOne A x x x)‖ := by
      rw [rankOne_apply, inner_op_smul_right,
        (inner_self_nonneg (A := A) (x := x)).isSelfAdjoint.norm_mul_self, ← norm_sq_eq A]
    _ ≤ ‖x‖ * ‖rankOne A x x x‖ := norm_inner_le E
    _ ≤ ‖x‖ * (‖rankOne A x x‖ * ‖x‖) := by
      gcongr
      exact (rankOne A x x).le_opNorm x
    _ = ‖x‖ ^ 2 * ‖rankOne A x x‖ := by ring
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hx')).mp (by simpa only [sq] using h)

/-- A diagonal module rank-one map vanishes exactly when its vector does. -/
@[simp]
lemma rankOne_self_eq_zero {x : E} : rankOne A x x = 0 ↔ x = 0 := by
  rw [← norm_eq_zero, norm_rankOne_self, sq_eq_zero_iff, norm_eq_zero]

end CStarModule
