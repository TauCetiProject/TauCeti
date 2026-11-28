/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.CategoryTheory.Endomorphism
public import TauCeti.Algebra.AlgebraicGroup.ConstantMultiplication.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Functor
public import TauCeti.Algebra.Category.LieAlgCat.Basic
import Mathlib.Algebra.Lie.NonUnitalNonAssocAlgebra

/-!
# The automorphism group scheme of a finite free Lie algebra

Let `b` be a finite basis of a Lie algebra `L` over a commutative ring `R`.
The group scheme of invertible matrices preserving the bracket has coordinate Hopf algebra
`TauCeti.LieAutomorphism.coordinateHopfAlgebra b`. For every commutative `R`-algebra `A`,
its points are the `A`-linear Lie automorphisms of `A ⊗[R] L`. The representing Hopf algebra
uses the existing equations for a group preserving a bilinear multiplication.

* `TauCeti.LieAutomorphism.preserves_toMatrix_iff` identifies the matrix equations with the
  condition of preserving the bracket after extension of scalars.
* `TauCeti.LieAutomorphism.pointsEquiv` gives the Lie equivalence attached to each point.
  `TauCeti.LieAutomorphism.pointsEquiv_mapPoints` gives naturality under coefficient change.
* `TauCeti.LieAutomorphism.pointsMulEquiv` packages this identification as a group isomorphism.

## References

* J. S. Milne, *Algebraic Groups* (2017), §24, on automorphism group schemes of algebras.
-/

public section

open scoped TensorProduct
open CategoryTheory

universe u v w

namespace TauCeti.LieAutomorphism

noncomputable section

variable {R : Type u} [CommRing R] {L : Type v} [LieRing L] [LieAlgebra R L]
variable {n : ℕ} (b : Module.Basis (Fin n) R L)

/-- The matrices of left bracket with the basis vectors. -/
def bracketMatrix (i : Fin n) : Matrix (Fin n) (Fin n) R :=
  LinearMap.toMatrix b b (LieAlgebra.ad R L (b i))

variable (A : Type w) [CommRing A] [Algebra R A]

/-- Left bracket with a scalar-extended basis vector has the scalar-extended structure matrix. -/
theorem toMatrix_ad_baseChange (i : Fin n) :
    LinearMap.toMatrix (b.baseChange A) (b.baseChange A)
      (LieAlgebra.ad A (A ⊗[R] L) ((b.baseChange A) i)) =
        (bracketMatrix b i).map (algebraMap R A) := by
  ext j k
  simp [bracketMatrix, LinearMap.toMatrix_apply, Algebra.smul_def]

/-- Preserving the structure matrices is equivalent to preserving the Lie bracket. -/
theorem preserves_toMatrix_iff (f : (A ⊗[R] L) →ₗ[A] (A ⊗[R] L)) :
    ConstantMultiplication.Preserves R n (bracketMatrix b)
        (LinearMap.toMatrix (b.baseChange A) (b.baseChange A) f) ↔
      ∀ x y, f ⁅x, y⁆ = ⁅f x, f y⁆ :=
  @ConstantMultiplication.preserves_toMatrix_iff R _ n (bracketMatrix b) A _ _
    (CommutatorRing (A ⊗[R] L)) _ _ (LieAlgebra.isScalarTower A (A ⊗[R] L))
    (LieAlgebra.smulCommClass A (A ⊗[R] L)) (b.baseChange A) (toMatrix_ad_baseChange b A) f

private def matrixLinearEquiv :
    Matrix.GeneralLinearGroup (Fin n) A ≃* ((A ⊗[R] L) ≃ₗ[A] (A ⊗[R] L)) :=
  (Matrix.GeneralLinearGroup.toLin' (b.baseChange A)).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv A _)

private theorem toMatrix_matrixLinearEquiv (g : Matrix.GeneralLinearGroup (Fin n) A) :
    LinearMap.toMatrix (b.baseChange A) (b.baseChange A)
      (matrixLinearEquiv b A g).toLinearMap = g.val := by
  rw [← LinearMap.toMatrix_toLin (b.baseChange A) (b.baseChange A) g.val]
  congr 1

private theorem mem_iff (g : Matrix.GeneralLinearGroup (Fin n) A) :
    g ∈ GeneralLinear.hopfIdealPointsSubgroup n
        (ConstantMultiplication.definingHopfIdeal R n (bracketMatrix b)) A ↔
    ∀ x y, matrixLinearEquiv b A g ⁅x, y⁆ =
      ⁅matrixLinearEquiv b A g x, matrixLinearEquiv b A g y⁆ := by
  rw [ConstantMultiplication.mem_hopfIdealPointsSubgroup_iff]
  have h := preserves_toMatrix_iff b A (matrixLinearEquiv b A g).toLinearMap
  rw [toMatrix_matrixLinearEquiv] at h
  exact h

private def subgroupEquiv :
    GeneralLinear.hopfIdealPointsSubgroup n
      (ConstantMultiplication.definingHopfIdeal R n (bracketMatrix b)) A ≃
      ((A ⊗[R] L) ≃ₗ⁅A⁆ (A ⊗[R] L)) where
  toFun g := { matrixLinearEquiv b A g.val with map_lie' := (mem_iff b A g.val).mp g.property _ _ }
  invFun e := ⟨(matrixLinearEquiv b A).symm e.toLinearEquiv, by
    rw [mem_iff, MulEquiv.apply_symm_apply]
    exact fun x y => e.map_lie x y⟩
  left_inv g := Subtype.ext ((matrixLinearEquiv b A).symm_apply_apply g.val)
  right_inv e := LieEquiv.ext fun x =>
    DFunLike.congr_fun ((matrixLinearEquiv b A).apply_symm_apply e.toLinearEquiv) x

/-- Coordinate Hopf algebra of the subgroup of the general linear group preserving the bracket. -/
abbrev coordinateHopfAlgebra : _root_.CommHopfAlgCat.{u} R :=
  ConstantMultiplication.coordinateHopfAlgebra R n (bracketMatrix b)

/-- Points are precisely Lie equivalences of the scalar-extended Lie algebra. -/
def pointsEquiv (S : CommAlgCat.{w} R) :
    HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra b) S ≃
      ((S ⊗[R] L) ≃ₗ⁅S⁆ (S ⊗[R] L)) :=
  (GeneralLinear.hopfIdealPointsSubgroupMulEquiv n _ S).toEquiv.trans (subgroupEquiv b S)

/-- The matrix of the associated Lie automorphism is the ambient general-linear point. -/
theorem toMatrix_pointsEquiv (S : CommAlgCat.{w} R)
    (q : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra b) S) :
    LinearMap.toMatrix (b.baseChange S) (b.baseChange S)
        (pointsEquiv b S q).toLinearEquiv.toLinearMap =
      (GeneralLinear.hopfIdealPointsSubgroupMulEquiv n _ S q).val.val :=
  toMatrix_matrixLinearEquiv b S _

private theorem pointsEquiv_apply (S : CommAlgCat.{w} R)
    (q : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra b) S) (x : S ⊗[R] L) :
    pointsEquiv b S q x =
      matrixLinearEquiv b S (GeneralLinear.hopfIdealPointsSubgroupMulEquiv n _ S q).val x :=
  rfl

/-- Multiplication of points corresponds to composition of Lie automorphisms. -/
theorem pointsEquiv_mul (S : CommAlgCat.{w} R)
    (q p : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra b) S) (x : S ⊗[R] L) :
    pointsEquiv b S (q * p) x = pointsEquiv b S q (pointsEquiv b S p x) := by
  rw [pointsEquiv_apply b S (q * p) x, pointsEquiv_apply b S q _, pointsEquiv_apply b S p x]
  rw [map_mul, Subgroup.coe_mul, map_mul, mul_apply_eq_comp]

private theorem toMatrix_pointsEquiv_mapPoints {S T : CommAlgCat.{w} R} (φ : S ⟶ T)
    (q : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra b) S) :
    LinearMap.toMatrix (b.baseChange T) (b.baseChange T)
      (pointsEquiv b T (HopfAlgebra.mapPoints φ q)).toLinearEquiv.toLinearMap =
      (LinearMap.toMatrix (b.baseChange S) (b.baseChange S)
        (pointsEquiv b S q).toLinearEquiv.toLinearMap).map φ.hom := by
  rw [toMatrix_pointsEquiv, toMatrix_pointsEquiv,
    GeneralLinear.hopfIdealPointsSubgroupMulEquiv_mapPoints,
    GeneralLinear.coe_mapHopfIdealPointsSubgroup]
  ext i j
  exact Matrix.GeneralLinearGroup.map_apply _ i j _

private abbrev changeScalars {S T : CommAlgCat.{w} R} (φ : S ⟶ T) :=
  LieAlgebra.ExtendScalars.map φ.hom (LieHom.id : L →ₗ⁅R⁆ L)

private theorem repr_changeScalars {S T : CommAlgCat.{w} R} (φ : S ⟶ T)
    (x : S ⊗[R] L) (i : Fin n) :
    (b.baseChange T).repr (changeScalars (L := L) φ x) i =
      φ ((b.baseChange S).repr x i) := by
  refine x.inductionOn ?_ ?_
  · intro a z
    simp [changeScalars, Algebra.smul_def]
  · intro y z hy hz
    simp [hy, hz]

/-- Coefficient change intertwines the two Lie automorphisms on every tensor. -/
theorem pointsEquiv_mapPoints {S T : CommAlgCat.{w} R} (φ : S ⟶ T)
    (q : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra b) S) (x : S ⊗[R] L) :
    pointsEquiv b T (HopfAlgebra.mapPoints φ q)
        (LieAlgebra.ExtendScalars.map φ.hom (LieHom.id : L →ₗ⁅R⁆ L) x) =
      LieAlgebra.ExtendScalars.map φ.hom (LieHom.id : L →ₗ⁅R⁆ L) (pointsEquiv b S q x) := by
  apply (b.baseChange T).repr.injective
  ext i
  have h₁ := congrFun (LinearMap.toMatrix_mulVec_repr (b.baseChange S) (b.baseChange S)
    (pointsEquiv b S q).toLinearEquiv.toLinearMap x) i
  have h₂ := congrFun (LinearMap.toMatrix_mulVec_repr (b.baseChange T) (b.baseChange T)
    (pointsEquiv b T (HopfAlgebra.mapPoints φ q)).toLinearEquiv.toLinearMap
      (changeScalars (L := L) φ x)) i
  rw [toMatrix_pointsEquiv_mapPoints] at h₂
  simp only [LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv] at h₁ h₂
  rw [repr_changeScalars, ← h₁, ← h₂]
  simp [Matrix.mulVec, dotProduct, repr_changeScalars]

/-- A group isomorphism to automorphisms of the Lie algebra object. -/
def pointsMulEquiv (S : CommAlgCat.{w} R) :
    HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra b) S ≃*
      CategoryTheory.Aut (LieAlgCat.of S (S ⊗[R] L)) where
  toFun q := .of (pointsEquiv b S q).toLieAlgCatIso
  invFun e := (pointsEquiv b S).symm e.asIso.toLieEquiv
  left_inv q := by simp
  right_inv e := by
    apply CategoryTheory.Aut.ext
    change ((pointsEquiv b S) ((pointsEquiv b S).symm e.asIso.toLieEquiv)).toLieAlgCatIso = _
    rw [Equiv.apply_symm_apply]
    exact CategoryTheory.Iso.toLieEquiv_toLieAlgCatIso e.asIso
  map_mul' q p := by
    apply CategoryTheory.Aut.ext
    apply CategoryTheory.Iso.ext
    apply LieAlgCat.hom_ext
    apply LieHom.ext
    intro x
    simpa only [Aut.mul_asIso, Iso.trans_hom, LieAlgCat.hom_comp, LieEquiv.toLieAlgCatIso_hom_hom,
      LieHom.comp_apply, LieEquiv.coe_toLieHom] using pointsEquiv_mul b S q p x

/-- Forgetting the categorical packaging recovers the Lie equivalence on points. -/
@[simp]
theorem pointsMulEquiv_toLieEquiv (S : CommAlgCat.{w} R)
    (q : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra b) S) :
    (pointsMulEquiv b S q).asIso.toLieEquiv = pointsEquiv b S q := by
  change (pointsEquiv b S q).toLieAlgCatIso.toLieEquiv = _
  exact LieEquiv.toLieAlgCatIso_toLieEquiv _

end

end TauCeti.LieAutomorphism
