/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.StdBasis
public import TauCeti.Algebra.AlgebraicGroup.ConstantMultiplication.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Functor

/-!
# The projective general linear group scheme as automorphisms of a matrix algebra

For a commutative ring `R` and a natural number `n`, this file constructs the affine group scheme
`PGLₙ` over `R` as the automorphism group scheme of the matrix algebra `Mₙ`: the closed subgroup
scheme of `GL_{n²}` of invertible linear maps of `Mₙ` that are multiplicative. Over every
commutative `R`-algebra `A` its points are exactly the `A`-algebra automorphisms of `Mₙ(A)`.

Concretely, `Mₙ(R)` is free on the matrix units, numbered by `Fin (n * n)` through
`finProdFinEquiv`. The structure matrices of `Mₙ(R)` in this basis are the left multiplication
matrices of the matrix units, and `TauCeti.ConstantMultiplication` provides the Hopf ideal of
`O(GL_{n²})` cutting out the matrices preserving that multiplication. A bijective multiplicative
linear map of a unital algebra automatically preserves the identity, so these matrices are
exactly the matrices of algebra automorphisms.

This is the representing object for the projective general linear group: the conjugation
homomorphism `GLₙ → PGLₙ`, its kernel and its surjectivity on field-valued points are in
`TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.Conjugation`. The pointwise quotient
`A ↦ GLₙ(A) / Z(GLₙ(A))` of `TauCeti.GeneralLinear.pglPointsFunctor` maps injectively into the
points of `PGLₙ` by conjugation (`Matrix.ProjGenLinGroup.innerAut_injective`), and bijectively
over a field.

## Main declarations

* `TauCeti.ProjectiveGeneralLinear.matrixUnitBasis`: the basis of matrix units of `Mₙ(S)`,
  indexed by `Fin (n * n)`.
* `TauCeti.ProjectiveGeneralLinear.structureMatrix`: the structure matrices of `Mₙ(R)` in that
  basis.
* `TauCeti.ProjectiveGeneralLinear.definingHopfIdeal`,
  `TauCeti.ProjectiveGeneralLinear.coordinateHopfAlgebra` and
  `TauCeti.ProjectiveGeneralLinear.groupScheme`: the closed subgroup scheme `PGLₙ` of `GL_{n²}`.
* `TauCeti.ProjectiveGeneralLinear.autToGeneralLinear`: the matrix of an algebra automorphism of
  `Mₙ(A)` in the matrix-unit basis.
* `TauCeti.ProjectiveGeneralLinear.hopfIdealPointsSubgroup_definingHopfIdeal`: the matrix points
  of `PGLₙ` are exactly the matrices of algebra automorphisms.
* `TauCeti.ProjectiveGeneralLinear.pointsMulEquiv`: the points of `PGLₙ` with values in `A` are
  the group of `A`-algebra automorphisms of `Mₙ(A)`.

## References

* J. S. Milne, *Algebraic Groups* (2017), where `PGLₙ` is identified with the automorphism group
  functor of the matrix algebra `Mₙ`.
* W. C. Waterhouse, *Introduction to Affine Group Schemes* (1979), Chapter 1, for closed
  subgroups of `GLₙ` cut out by polynomial identities.
-/

public section

open CategoryTheory Matrix WithConv

namespace TauCeti.ProjectiveGeneralLinear

universe u v w

noncomputable section

section MatrixUnits

variable (n : ℕ) (S : Type v) [CommRing S]

/-- The basis of `Matrix (Fin n) (Fin n) S` by matrix units, indexed by `Fin (n * n)` through
`finProdFinEquiv`: the `k`th basis vector is `Matrix.single i j 1` for
`(i, j) = finProdFinEquiv.symm k`. -/
def matrixUnitBasis : Module.Basis (Fin (n * n)) S (Matrix (Fin n) (Fin n) S) :=
  (Matrix.stdBasis S (Fin n) (Fin n)).reindex finProdFinEquiv

/-- The `k`th matrix unit. -/
@[simp]
theorem matrixUnitBasis_apply (k : Fin (n * n)) :
    matrixUnitBasis n S k =
      Matrix.single (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 1 := by
  rw [matrixUnitBasis, Module.Basis.reindex_apply, Matrix.stdBasis_eq_single]

/-- The `k`th coordinate of a matrix in the matrix-unit basis is its entry at
`finProdFinEquiv.symm k`. -/
@[simp]
theorem matrixUnitBasis_repr_apply (x : Matrix (Fin n) (Fin n) S) (k : Fin (n * n)) :
    (matrixUnitBasis n S).repr x k =
      x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := by
  simp [matrixUnitBasis, Matrix.stdBasis]

variable (R : Type u) [CommRing R]

/-- The structure matrices of the matrix algebra `Mₙ(R)`: the `k`th one is the matrix, in the
matrix-unit basis, of left multiplication by the `k`th matrix unit. -/
def structureMatrix (k : Fin (n * n)) : Matrix (Fin (n * n)) (Fin (n * n)) R :=
  Algebra.leftMulMatrix (matrixUnitBasis n R) (matrixUnitBasis n R k)

/-- The structure matrices are defined over the base: read in any commutative `R`-algebra `S`,
they are the structure matrices of `Mₙ(S)`. -/
theorem toMatrix_mulLeft_matrixUnitBasis [Algebra R S] (k : Fin (n * n)) :
    LinearMap.toMatrix (matrixUnitBasis n S) (matrixUnitBasis n S)
        (LinearMap.mulLeft S (matrixUnitBasis n S k)) =
      (structureMatrix n R k).map (algebraMap R S) := by
  ext a c
  rw [Matrix.map_apply, structureMatrix, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
    LinearMap.toMatrix_apply]
  simp only [LinearMap.mulLeft_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply',
    matrixUnitBasis_apply, matrixUnitBasis_repr_apply]
  simp [Matrix.mul_apply, Matrix.single_apply, apply_ite (algebraMap R S)]

end MatrixUnits

section Scheme

variable (n : ℕ) (R : Type u) [CommRing R]

/-- The Hopf ideal of `O(GL_{n²})` cutting out the invertible linear maps of `Mₙ` that are
multiplicative. -/
abbrev definingHopfIdeal : HopfIdeal R (GeneralLinear.coordinateHopfAlgebra R (n * n)) :=
  ConstantMultiplication.definingHopfIdeal R (n * n) (structureMatrix n R)

/-- The coordinate Hopf algebra of `PGLₙ`, the automorphism group scheme of `Mₙ`. -/
abbrev coordinateHopfAlgebra : _root_.CommHopfAlgCat.{u} R :=
  ConstantMultiplication.coordinateHopfAlgebra R (n * n) (structureMatrix n R)

/-- The projective general linear group scheme `PGLₙ` over `R`, as the automorphism group scheme
of the matrix algebra `Mₙ`, a closed subgroup scheme of `GL_{n²}`. -/
abbrev groupScheme :=
  ConstantMultiplication.groupScheme R (n * n) (structureMatrix n R)

end Scheme

section Points

variable (n : ℕ) {R : Type u} [CommRing R] (A : Type w) [CommRing A] [Algebra R A]

/-- The matrix, in the matrix-unit basis, of an `A`-algebra automorphism of `Mₙ(A)`, as a
homomorphism into `GL_{n²}(A)`. -/
def autToGeneralLinear :
    (Matrix (Fin n) (Fin n) A ≃ₐ[A] Matrix (Fin n) (Fin n) A) →*
      Matrix.GeneralLinearGroup (Fin (n * n)) A :=
  (Units.map (LinearMap.toMatrixAlgEquiv (matrixUnitBasis n A)).toRingEquiv.toMonoidHom).comp
    ((Units.map (AlgEquiv.toLinearMapHom A _)).comp toUnits.toMonoidHom)

variable {A}

/-- The underlying matrix of `autToGeneralLinear n A e` is the matrix of `e` in the matrix-unit
basis. -/
@[simp]
theorem coe_autToGeneralLinear (e : Matrix (Fin n) (Fin n) A ≃ₐ[A] Matrix (Fin n) (Fin n) A) :
    (autToGeneralLinear n A e : Matrix (Fin (n * n)) (Fin (n * n)) A) =
      LinearMap.toMatrix (matrixUnitBasis n A) (matrixUnitBasis n A) e.toLinearMap := by
  ext i j
  simp [autToGeneralLinear, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]

/-- An algebra automorphism of `Mₙ(A)` is determined by its matrix. -/
theorem autToGeneralLinear_injective : Function.Injective (autToGeneralLinear n A) := by
  intro e₁ e₂ h
  have h' := congrArg (fun g : Matrix.GeneralLinearGroup (Fin (n * n)) A =>
    (g : Matrix (Fin (n * n)) (Fin (n * n)) A)) h
  simp only [coe_autToGeneralLinear, (LinearMap.toMatrix _ _).injective.eq_iff] at h'
  exact AlgEquiv.ext fun x => LinearMap.congr_fun h' x

variable (R) in
/-- The matrix in the matrix-unit basis of a linear endomorphism of `Mₙ(A)` preserves the
multiplication exactly when the endomorphism is multiplicative. -/
theorem preserves_toMatrix_iff (f : Matrix (Fin n) (Fin n) A →ₗ[A] Matrix (Fin n) (Fin n) A) :
    ConstantMultiplication.Preserves R (n * n) (structureMatrix n R)
        (LinearMap.toMatrix (matrixUnitBasis n A) (matrixUnitBasis n A) f) ↔
      ∀ x y, f (x * y) = f x * f y :=
  ConstantMultiplication.preserves_toMatrix_iff R (n * n) (structureMatrix n R)
    (matrixUnitBasis n A) (toMatrix_mulLeft_matrixUnitBasis n A R) f

variable (R) in
/-- **An invertible matrix preserves the multiplication of `Mₙ(A)` exactly when it is the matrix
of an algebra automorphism.** Multiplicativity and bijectivity force the identity to be
preserved. -/
theorem preserves_iff_mem_range_autToGeneralLinear
    (g : Matrix.GeneralLinearGroup (Fin (n * n)) A) :
    ConstantMultiplication.Preserves R (n * n) (structureMatrix n R)
        (g : Matrix (Fin (n * n)) (Fin (n * n)) A) ↔
      g ∈ (autToGeneralLinear n A).range := by
  constructor
  · intro hg
    let f := Matrix.toLin (matrixUnitBasis n A) (matrixUnitBasis n A)
      (g : Matrix (Fin (n * n)) (Fin (n * n)) A)
    have hf : ∀ x y, f (x * y) = f x * f y := by
      rw [← preserves_toMatrix_iff n R, LinearMap.toMatrix_toLin]
      exact hg
    let g' := Matrix.toLin (matrixUnitBasis n A) (matrixUnitBasis n A)
      (↑g⁻¹ : Matrix (Fin (n * n)) (Fin (n * n)) A)
    let l : Matrix (Fin n) (Fin n) A ≃ₗ[A] Matrix (Fin n) (Fin n) A :=
      LinearEquiv.ofLinearMap f g'
        (by simp [f, g', ← Matrix.toLin_mul])
        (by simp [f, g', ← Matrix.toLin_mul])
    -- `l` is `f`, so it is multiplicative; being surjective, it then fixes the identity.
    have hmul : ∀ x y, l (x * y) = l x * l y := hf
    have hone : l 1 = 1 := by
      have h := hmul 1 (l.symm 1)
      rw [one_mul, l.apply_symm_apply, mul_one] at h
      exact h.symm
    refine ⟨AlgEquiv.ofLinearEquiv l hone hmul, Units.ext ?_⟩
    have hl : (l : Matrix (Fin n) (Fin n) A →ₗ[A] Matrix (Fin n) (Fin n) A) = f :=
      LinearMap.ext fun x => by simp [l]
    rw [coe_autToGeneralLinear, ← AlgEquiv.toLinearEquiv_toLinearMap,
      AlgEquiv.toLinearEquiv_ofLinearEquiv, hl, LinearMap.toMatrix_toLin]
  · rintro ⟨e, rfl⟩
    rw [coe_autToGeneralLinear, preserves_toMatrix_iff n R]
    exact fun x y => map_mul e x y

variable (R) in
/-- **The matrix points of `PGLₙ` are the matrices of algebra automorphisms**: the subgroup of
`GL_{n²}(A)` cut out by the defining Hopf ideal is the image of the automorphism group of
`Mₙ(A)`. -/
theorem hopfIdealPointsSubgroup_definingHopfIdeal (A : Type w) [CommRing A] [Algebra R A] :
    GeneralLinear.hopfIdealPointsSubgroup (n * n) (definingHopfIdeal n R) A =
      (autToGeneralLinear n A).range := by
  ext g
  have h := ConstantMultiplication.mem_definingPointsSubgroup_iff R (n * n) (structureMatrix n R)
    ((GeneralLinear.pointsMulEquiv (n * n)).symm g)
  rw [MulEquiv.apply_symm_apply, CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at h
  rw [← preserves_iff_mem_range_autToGeneralLinear n R,
    GeneralLinear.mem_hopfIdealPointsSubgroup_iff]
  exact h

variable (R) in
/-- **The points of `PGLₙ` are the automorphisms of the matrix algebra**: for every commutative
`R`-algebra `A`, the group of `A`-points of `PGLₙ` is the group of `A`-algebra automorphisms of
`Mₙ(A)`. -/
def pointsMulEquiv (A : CommAlgCat.{w} R) :
    HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra n R) A ≃*
      (Matrix (Fin n) (Fin n) A ≃ₐ[A] Matrix (Fin n) (Fin n) A) :=
  (GeneralLinear.hopfIdealPointsSubgroupMulEquiv (n * n) (definingHopfIdeal n R) A).trans
    ((MulEquiv.subgroupCongr (hopfIdealPointsSubgroup_definingHopfIdeal n R A)).trans
      (MonoidHom.ofInjective (autToGeneralLinear_injective n (A := A))).symm)

/-- The automorphism attached to a point of `PGLₙ` has, as its matrix, the invertible matrix of
the underlying point of `GL_{n²}`. Together with `autToGeneralLinear_injective` this determines
`pointsMulEquiv`. -/
@[simp]
theorem autToGeneralLinear_pointsMulEquiv (A : CommAlgCat.{w} R)
    (q : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra n R) A) :
    autToGeneralLinear n A (pointsMulEquiv n R A q) =
      GeneralLinear.pointsMulEquiv (n * n)
        (CommHopfAlgCat.quotientPointsHom _ (definingHopfIdeal n R) A q) := by
  rw [pointsMulEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MonoidHom.apply_ofInjective_symm, MulEquiv.subgroupCongr_apply,
    GeneralLinear.coe_hopfIdealPointsSubgroupMulEquiv_apply]

end Points

end

end TauCeti.ProjectiveGeneralLinear
