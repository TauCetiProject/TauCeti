/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.Basic
public import TauCeti.Algebra.AlgebraicGroup.ConstantMultiplication.Tangent
public import TauCeti.LinearAlgebra.Matrix.Derivation

/-!
# The Lie algebra of the projective general linear group

The tangent Lie algebra of `PGLₙ`, represented as the automorphism group of the matrix
algebra, acts on that algebra by associative derivations. Every such derivation is inner.
Thus its image in the endomorphism algebra is exactly the space of commutators with matrices,
without a restriction on the characteristic or on the rank. Coefficients may lie in any
commutative algebra over the base ring.

The construction uses the closed-subgroup tangent equivalence and the tangent-matrix
identification for `GL`. The linearized multiplication relations characterize its image.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10, tangent spaces of automorphism groups.
* N. Jacobson, *Basic Algebra II*, inner derivations of matrix algebras.
-/

public section

open Matrix

namespace TauCeti.ProjectiveGeneralLinear

universe u v

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

variable (n : ℕ) {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]

/-- The tangent action of the projective general linear group on its matrix algebra.
It is the differential of its defining inclusion into `GL_{n²}`, expressed in the
matrix-unit basis. -/
def tangentEnd :
    Derivation R (coordinateHopfAlgebra n R)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra n R) B) →ₗ⁅B⁆
        Module.End B (Matrix (Fin n) (Fin n) B) :=
  ((Matrix.toLinAlgEquiv (matrixUnitBasis n B)).toLieEquiv.toLieHom).comp
    ((GeneralLinear.tangentLieEquivMatrix (R := R) (B := B) (n * n)).toLieHom.comp
      (HopfIdeal.quotientLieHom (B := B) (definingHopfIdeal n R)))

/-- The tangent action is the endomorphism represented by the ambient tangent matrix. -/
@[simp]
theorem tangentEnd_apply
    (d : Derivation R (coordinateHopfAlgebra n R)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra n R) B)) :
    tangentEnd n d = Matrix.toLinAlgEquiv (matrixUnitBasis n B)
      (GeneralLinear.tangentMatrix (n * n)
        (HopfIdeal.quotientLieHom (definingHopfIdeal n R) d)) := by
  simp [tangentEnd, GeneralLinear.tangentLieEquivMatrix_apply]

/-- The action of the tangent Lie algebra on the matrix algebra is faithful. -/
theorem tangentEnd_injective : Function.Injective (tangentEnd (R := R) (B := B) n) :=
  (Matrix.toLinAlgEquiv (matrixUnitBasis n B)).injective.comp
    ((GeneralLinear.tangentLieEquivMatrix (R := R) (B := B) (n * n)).injective.comp
      (HopfIdeal.quotientLieHom_injective (B := B) (definingHopfIdeal n R)))

/-- A linear endomorphism of the matrix algebra comes from a tangent vector of `PGLₙ`
exactly when it satisfies the associative Leibniz rule. -/
theorem mem_range_tangentEnd_iff_leibniz
    (f : Module.End B (Matrix (Fin n) (Fin n) B)) :
    f ∈ Set.range (tangentEnd (R := R) n) ↔
      ∀ x y, f (x * y) = f x * y + x * f y := by
  let e := GeneralLinear.tangentLieEquivMatrix (R := R) (B := B) (n * n)
  let X := LinearMap.toMatrix (matrixUnitBasis n B) (matrixUnitBasis n B) f
  have hX : e (e.symm X) = X := e.apply_symm_apply X
  have hf : Matrix.toLinAlgEquiv (matrixUnitBasis n B) X = f := by
    exact (Matrix.toLinAlgEquiv (matrixUnitBasis n B)).apply_symm_apply f
  have hmem : e.symm X ∈ (definingHopfIdeal n R).lieSubalgebra (B := B) ↔
      ∀ x y, f (x * y) = f x * y + x * f y := by
    rw [ConstantMultiplication.mem_lieSubalgebra_definingHopfIdeal_iff]
    rw [← GeneralLinear.tangentLieEquivMatrix_apply, hX]
    exact ConstantMultiplication.toMatrix_leibniz_iff (R := R)
      (structureMatrix n R) (matrixUnitBasis n B)
      (toMatrix_mulLeft_matrixUnitBasis n B R) f
  rw [← hmem]
  constructor
  · rintro ⟨d, hd⟩
    have hmatrix : e (HopfIdeal.quotientLieHom (definingHopfIdeal n R) d) = X := by
      apply (Matrix.toLinAlgEquiv (matrixUnitBasis n B)).injective
      rw [hf]
      exact hd
    rw [← hmatrix, e.symm_apply_apply]
    rw [← HopfIdeal.quotientLieEquiv_apply_coe]
    exact ((definingHopfIdeal n R).quotientLieEquiv d).property
  · intro hd
    let q := (definingHopfIdeal n R).quotientLieEquiv (B := B)
    let d := q.symm ⟨e.symm X, hd⟩
    have hqd := congrArg Subtype.val (q.apply_symm_apply ⟨e.symm X, hd⟩)
    rw [HopfIdeal.quotientLieEquiv_apply_coe] at hqd
    refine ⟨d, ?_⟩
    rw [tangentEnd_apply, ← GeneralLinear.tangentLieEquivMatrix_apply, hqd, hX, hf]

/-- The tangent Lie algebra of `PGLₙ` consists exactly of inner associative derivations
of the matrix algebra. This includes ranks zero and one and every characteristic. -/
theorem mem_range_tangentEnd_iff
    (f : Module.End B (Matrix (Fin n) (Fin n) B)) :
    f ∈ Set.range (tangentEnd (R := R) n) ↔
      ∃ X : Matrix (Fin n) (Fin n) B,
        f = LinearMap.mulLeft B X - LinearMap.mulRight B X := by
  rw [mem_range_tangentEnd_iff_leibniz]
  constructor
  · exact LinearMap.exists_matrix_eq_mulLeft_sub_mulRight_of_leibniz f
  · rintro ⟨X, rfl⟩ x y
    simp only [LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    noncomm_ring

end

end TauCeti.ProjectiveGeneralLinear
