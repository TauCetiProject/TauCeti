/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Stiefel
public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Frame
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic

/-!
# The unit tangent bundle of the round two-sphere is `SO(3)`

The Stiefel manifold `TauCeti.stiefel (EuclideanSpace ℝ (Fin 3)) 2` of orthonormal pairs `(x, v)`
of `ℝ³` is the unit tangent bundle `UT(S²)` of the round unit sphere: `x` is a point of `S²`, and
`v` is a unit vector in its tangent plane `x^⊥` for the round metric, the restriction of the
Euclidean inner product (`TauCeti.mem_stiefel_two_iff_mem_range_mvfderiv`).

Sending `(x, v)` to the oriented orthonormal frame `(x, v, x ⨯₃ v)`, read as the rotation with
these columns (`TauCeti.Matrix.SpecialOrthogonalGroup.ofFrame`), is a homeomorphism
`TauCeti.stiefelTwoHomeomorphSpecialOrthogonalGroup : UT(S²) ≃ₜ SO(3)`. Its inverse reads off the
first two columns of a rotation, so the base point projection `(x, v) ↦ x` becomes `A ↦ A e₀`, and
the standard frame `(e₀, e₁)` corresponds to the identity. Rotating frames by `g ∈ SO(3)` becomes
left multiplication by `g`
(`TauCeti.stiefelTwoHomeomorphSpecialOrthogonalGroup_symm_mul_apply`), so the homeomorphism is
equivariant and `SO(3)` acts simply transitively on unit tangent vectors of the round sphere.

## Main declarations

* `TauCeti.stiefelTwoHomeomorphSpecialOrthogonalGroup`: the homeomorphism `UT(S²) ≃ₜ SO(3)`.
* `TauCeti.stiefelTwoHomeomorphSpecialOrthogonalGroup_symm_one`: the identity is the standard
  frame.
* `TauCeti.stiefelTwoHomeomorphSpecialOrthogonalGroup_symm_mul_apply`: equivariance.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, Chapter 5 (Stiefel manifolds).
-/

public section

open Matrix WithLp TauCeti.Matrix.SpecialOrthogonalGroup

namespace TauCeti

noncomputable section

/-- **The unit tangent bundle of the round two-sphere is `SO(3)`.** An orthonormal pair `(x, v)`
of `ℝ³`, a unit tangent vector `v` of the round sphere at `x`, goes to the rotation whose columns
are the oriented orthonormal frame `(x, v, x ⨯₃ v)`. The inverse sends a rotation to its first two
columns. -/
def stiefelTwoHomeomorphSpecialOrthogonalGroup :
    stiefel (EuclideanSpace ℝ (Fin 3)) 2 ≃ₜ specialOrthogonalGroup (Fin 3) ℝ where
  toFun v := ⟨ofFrame (ofLp (v.1 0)) (ofLp (v.1 1)),
    ofFrame_mem_iff.2 (mem_stiefel_two_euclideanSpace_iff.1 v.2)⟩
  invFun A := ⟨![toLp 2 ((A : Matrix (Fin 3) (Fin 3) ℝ).col 0),
      toLp 2 ((A : Matrix (Fin 3) (Fin 3) ℝ).col 1)],
    by
      have h := col_dotProduct_col_of_mem_orthogonalGroup A.2.1
      exact mem_stiefel_two_euclideanSpace_iff.2
        ⟨by simpa using h 0 0, by simpa using h 1 1, by simpa using h 0 1⟩⟩
  left_inv v := by
    ext1
    funext i
    fin_cases i <;> simp
  right_inv A := Subtype.ext (ofFrame_col_zero_col_one A.2)
  continuous_toFun := by
    have hv (i : Fin 2) : Continuous fun v : stiefel (EuclideanSpace ℝ (Fin 3)) 2 ↦ ofLp (v.1 i) :=
      (PiLp.continuous_ofLp 2 _).comp ((continuous_apply i).comp continuous_subtype_val)
    exact (continuous_ofFrame.comp ((hv 0).prodMk (hv 1))).subtype_mk _
  continuous_invFun := by
    have hA (j : Fin 3) : Continuous fun A : specialOrthogonalGroup (Fin 3) ℝ ↦
        toLp 2 ((A : Matrix (Fin 3) (Fin 3) ℝ).col j) :=
      (PiLp.continuous_toLp 2 _).comp ((continuous_apply j).comp
        (continuous_id.matrix_transpose.comp continuous_subtype_val))
    refine Continuous.subtype_mk (continuous_pi fun i ↦ ?_) _
    fin_cases i
    · exact hA 0
    · exact hA 1

/-- A unit tangent vector `v` at `x` goes to the rotation with columns `x`, `v` and `x ⨯₃ v`. -/
@[simp]
theorem coe_stiefelTwoHomeomorphSpecialOrthogonalGroup_apply
    (v : stiefel (EuclideanSpace ℝ (Fin 3)) 2) :
    (stiefelTwoHomeomorphSpecialOrthogonalGroup v : Matrix (Fin 3) (Fin 3) ℝ) =
      ofFrame (ofLp (v.1 0)) (ofLp (v.1 1)) :=
  (rfl)

/-- A rotation goes to the unit tangent vector given by its second column, at the point given by
its first column. -/
@[simp]
theorem coe_stiefelTwoHomeomorphSpecialOrthogonalGroup_symm_apply
    (A : specialOrthogonalGroup (Fin 3) ℝ) :
    (stiefelTwoHomeomorphSpecialOrthogonalGroup.symm A : Fin 2 → EuclideanSpace ℝ (Fin 3)) =
      ![toLp 2 ((A : Matrix (Fin 3) (Fin 3) ℝ).col 0),
        toLp 2 ((A : Matrix (Fin 3) (Fin 3) ℝ).col 1)] :=
  (rfl)

/-- The identity rotation corresponds to the standard frame `(e₀, e₁)`, the unit tangent vector
`e₁` at the point `e₀` of the sphere. -/
theorem stiefelTwoHomeomorphSpecialOrthogonalGroup_symm_one :
    (stiefelTwoHomeomorphSpecialOrthogonalGroup.symm 1 : Fin 2 → EuclideanSpace ℝ (Fin 3)) =
      ![EuclideanSpace.single 0 1, EuclideanSpace.single 1 1] := by
  simp only [coe_stiefelTwoHomeomorphSpecialOrthogonalGroup_symm_apply, OneMemClass.coe_one,
    ← mulVec_single_one, one_mulVec, PiLp.toLp_single]

/-- **The homeomorphism is equivariant**: the frame of `g * A` is the frame of `A` rotated by
`g`. -/
theorem stiefelTwoHomeomorphSpecialOrthogonalGroup_symm_mul_apply
    (g A : specialOrthogonalGroup (Fin 3) ℝ) (i : Fin 2) :
    (stiefelTwoHomeomorphSpecialOrthogonalGroup.symm (g * A) : Fin 2 → EuclideanSpace ℝ (Fin 3))
        i =
      toLp 2 ((g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
        ofLp ((stiefelTwoHomeomorphSpecialOrthogonalGroup.symm A :
          Fin 2 → EuclideanSpace ℝ (Fin 3)) i)) := by
  fin_cases i <;> simp [col_mul_eq_mulVec_col]

end

end TauCeti
