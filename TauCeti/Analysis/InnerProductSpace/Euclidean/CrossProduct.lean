/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.SkewAdjoint
public import Mathlib.Analysis.InnerProductSpace.Orientation
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.CrossProduct
public import TauCeti.Algebra.Lie.Orthogonal.CrossProduct
public import TauCeti.Algebra.Lie.SkewAdjoint
public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.Gram.Basic

/-!
# The cross product of Euclidean three-space

For the standard orientation of `ℝ³ = EuclideanSpace ℝ (Fin 3)`, given by its standard basis, the
oriented volume form is the triple product `vol(u, v, w) = u ⬝ (v × w)`
(`EuclideanSpace.volumeForm_basisFun_orientation_three`). This expresses volume forms built from an
orientation of `ℝ³`, such as the area form of the unit sphere, through Mathlib's cross product.

The cross product also describes the infinitesimal rotations of `ℝ³`. The endomorphism
`v ↦ u ⨯₃ v` (`TauCeti.euclideanCrossProduct u`) is skew-adjoint,
`⟪u ⨯₃ v, w⟫ = -⟪v, u ⨯₃ w⟫` (`TauCeti.inner_euclideanCrossProduct_apply_left`), and every
skew-adjoint endomorphism of `ℝ³` is of this form for a unique axis `u`, read off its coordinates.
This is the **hat map**, a linear isomorphism `TauCeti.euclideanSoThreeEquiv` from `ℝ³` onto the
orthogonal Lie algebra `so(3) = skewAdjointLieSubalgebra (innerₗ ℝ³)`. It carries the cross
product to the commutator, `⁅û, v̂⁆ = (u ⨯₃ v)^` (`TauCeti.lie_euclideanSoThreeEquiv`). The matrix
version, onto the skew-symmetric matrices `LieAlgebra.Orthogonal.so (Fin 3) R`, is
`TauCeti.soThreeEquiv`; the version here is its transport along the standard basis of `ℝ³`
(`TauCeti.skewAdjointLieEquivOfBasis`, the standard basis being orthonormal), and acts on the
inner product space `ℝ³`, as the Lie algebra of its orthogonal group does
(`TauCeti.orthogonalLieAlgebraEquiv`).

## Main declarations

* `EuclideanSpace.volumeForm_basisFun_orientation_three`: the volume form is the triple product.
* `TauCeti.euclideanCrossProduct`: the infinitesimal rotation `v ↦ u ⨯₃ v`, linear in `u`.
* `TauCeti.euclideanSoThreeEquiv`: the hat map `ℝ³ ≃ₗ[ℝ] so(3)`.
* `TauCeti.lie_euclideanSoThreeEquiv`: the hat map carries the cross product to the commutator.
-/

public section

open Matrix WithLp

/-- The volume form of the standard orientation of `ℝ³` is the triple product:
`vol(u, v, w) = u ⬝ (v × w)`. -/
theorem EuclideanSpace.volumeForm_basisFun_orientation_three
    (u v w : EuclideanSpace ℝ (Fin 3)) :
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.volumeForm ![u, v, w] =
      ofLp u ⬝ᵥ ofLp v ⨯₃ ofLp w := by
  rw [Orientation.volumeForm_robust _ (EuclideanSpace.basisFun (Fin 3) ℝ) rfl,
    Module.Basis.det_apply, triple_product_eq_det, ← det_transpose]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Module.Basis.toMatrix_apply]

/-! ### The hat map of `ℝ³` -/

namespace TauCeti

open scoped InnerProductSpace

/-- The **infinitesimal rotations** of Euclidean three-space: the axis `u` gives the endomorphism
`v ↦ u ⨯₃ v`, linearly in `u`. -/
noncomputable def euclideanCrossProduct :
    EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] Module.End ℝ (EuclideanSpace ℝ (Fin 3)) :=
  LinearMap.mk₂ ℝ (fun u v ↦ toLp 2 (ofLp u ⨯₃ ofLp v))
    (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp)

/-- The infinitesimal rotation about `u` sends `v` to `u ⨯₃ v`. -/
@[simp]
theorem euclideanCrossProduct_apply (u v : EuclideanSpace ℝ (Fin 3)) :
    euclideanCrossProduct u v = toLp 2 (ofLp u ⨯₃ ofLp v) :=
  (rfl)

/-- The infinitesimal rotations are skew-adjoint: `⟪u ⨯₃ v, w⟫ = -⟪v, u ⨯₃ w⟫`. -/
theorem inner_euclideanCrossProduct_apply_left (u v w : EuclideanSpace ℝ (Fin 3)) :
    ⟪euclideanCrossProduct u v, w⟫_ℝ = -⟪v, euclideanCrossProduct u w⟫_ℝ := by
  simp only [euclideanCrossProduct_apply, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [dotProduct_comm _ (ofLp v), ← cross_anticomm (ofLp w), dotProduct_neg, neg_neg]
  exact (triple_product_permutation _ _ _).symm

/-- The infinitesimal rotation about `u` lies in the orthogonal Lie algebra `so(3)` of the
skew-adjoint endomorphisms of Euclidean three-space. -/
theorem euclideanCrossProduct_mem_skewAdjointLieSubalgebra (u : EuclideanSpace ℝ (Fin 3)) :
    euclideanCrossProduct u ∈ skewAdjointLieSubalgebra (innerₗ (EuclideanSpace ℝ (Fin 3))) :=
  mem_skewAdjointLieSubalgebra_innerₗ_iff.2 (inner_euclideanCrossProduct_apply_left u)

/-- The **hat map** of Euclidean three-space: the linear isomorphism from `ℝ³` onto the orthogonal
Lie algebra `so(3)` of skew-adjoint endomorphisms sending the axis `u` to the infinitesimal
rotation `v ↦ u ⨯₃ v`. It is the matrix hat map `TauCeti.soThreeEquiv` transported along the
standard basis by `TauCeti.skewAdjointLieEquivOfBasis`. -/
noncomputable def euclideanSoThreeEquiv :
    EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ]
      skewAdjointLieSubalgebra (innerₗ (EuclideanSpace ℝ (Fin 3))) :=
  (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).trans ((soThreeEquiv ℝ).trans
    (skewAdjointLieEquivOfBasis (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis _
      (LinearMap.BilinForm.toMatrix_innerₗ_orthonormalBasis _)).toLinearEquiv)

/-- The hat map sends the axis `u` to the infinitesimal rotation `v ↦ u ⨯₃ v`. -/
@[simp]
theorem coe_euclideanSoThreeEquiv_apply (u v : EuclideanSpace ℝ (Fin 3)) :
    (euclideanSoThreeEquiv u : Module.End ℝ (EuclideanSpace ℝ (Fin 3))) v =
      toLp 2 (ofLp u ⨯₃ ofLp v) := by
  refine (LinearMap.congr_fun (coe_skewAdjointLieEquivOfBasis_apply _ _ _
    (soThreeEquiv ℝ (ofLp u))) v).trans ?_
  rw [Matrix.toLinAlgEquiv_apply]
  ext i
  simp [← crossProductMatrix_mulVec, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- The inverse of the hat map reads the axis of `A` off the coordinates of `A e₁`, `A e₂` and
`A e₀`. -/
theorem euclideanSoThreeEquiv_symm_apply
    (A : skewAdjointLieSubalgebra (innerₗ (EuclideanSpace ℝ (Fin 3)))) :
    euclideanSoThreeEquiv.symm A = toLp 2
      ![(A : Module.End ℝ (EuclideanSpace ℝ (Fin 3))) (EuclideanSpace.single 1 1) 2,
        (A : Module.End ℝ (EuclideanSpace ℝ (Fin 3))) (EuclideanSpace.single 2 1) 0,
        (A : Module.End ℝ (EuclideanSpace ℝ (Fin 3))) (EuclideanSpace.single 0 1) 1] := by
  obtain ⟨u, rfl⟩ := euclideanSoThreeEquiv.surjective A
  ext i
  fin_cases i <;> simp [cross_apply]

/-- **The hat map carries the cross product to the commutator**: `⁅û, v̂⁆ = (u ⨯₃ v)^`. This is
the matrix identity `TauCeti.lie_soThreeEquiv` transported along the standard basis. -/
@[simp]
theorem lie_euclideanSoThreeEquiv (u v : EuclideanSpace ℝ (Fin 3)) :
    ⁅euclideanSoThreeEquiv u, euclideanSoThreeEquiv v⁆ =
      euclideanSoThreeEquiv (toLp 2 (ofLp u ⨯₃ ofLp v)) :=
  ((skewAdjointLieEquivOfBasis (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis _
    (LinearMap.BilinForm.toMatrix_innerₗ_orthonormalBasis _)).map_lie _ _).symm.trans
    (congrArg _ (lie_soThreeEquiv (ofLp u) (ofLp v)))

end TauCeti
