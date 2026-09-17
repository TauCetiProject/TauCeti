/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.RepresentationTheory.GrothendieckGroup.CartanMatrix

/-!
# Unimodularity of the Cartan matrix

Let `R` be an Artinian ring with finite exhaustive families of indecomposable projectives and
simple modules, indexed so that their classes give the projective and simple bases. If every
finitely generated `R`-module admits a finite resolution by finitely generated projectives, the
Cartan map is an isomorphism. Consequently its matrix in these bases is invertible over `ℤ`, and
its determinant is `1` or `-1`.

The inverse matrix records the projective-basis coordinates of the alternating projective
resolution class of each simple-basis vector. Thus the finite-resolution hypothesis appears
exactly where the inverse is constructed; no unimodularity statement is made for arbitrary
Artinian rings.

## Main definitions

* `TauCeti.inverseCartanMatrix`: the matrix of the inverse Cartan map in the simple and projective
  bases.

## Main results

* `TauCeti.cartanMatrix_mul_inverseCartanMatrix` and
  `TauCeti.inverseCartanMatrix_mul_cartanMatrix`: the two inverse identities.
* `TauCeti.isUnit_cartanMatrix`: the Cartan matrix is invertible over `ℤ`.
* `TauCeti.cartanMatrix_det_eq_one_or_neg_one`: its determinant is `1` or `-1`.

## References

* Ibrahim Assem, Daniel Simson and Andrzej Skowroński, *Elements of the Representation Theory of
  Associative Algebras I*, Chapter III, Section 3.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.ObjectProperty

universe u v

variable {R : Type u} [Ring R] [IsArtinianRing R]
variable {I : Type v} [Fintype I] [DecidableEq I]
variable (P : I → (finiteProjectiveModules R).FullSubcategory)
variable (S : I → FGModuleCat.{u} R) [∀ i, IsSimpleModule R (S i)]
variable (hind : ∀ i, IsIndecomposableModule R (P i).obj)
variable (hPnoniso : Pairwise fun i j ↦ IsEmpty (↑(P i).obj ≃ₗ[R] ↑(P j).obj))
variable (hPexhaustive : IsExhaustiveIndecomposableProjectiveFamily P)
variable (hSnoniso : Pairwise fun i j ↦ IsEmpty ((S i : Type u) ≃ₗ[R] S j))
variable (hSexhaustive : IsExhaustiveSimpleFamily S)

private theorem cartanMatrix_eq_toMatrix_cartanEquiv
    (h : ModuleCat.isFG R ≤
      (ExactStructure.abelian (ModuleCat.{u} R)).admitsFiniteResolution
        (finiteProjectiveModules R)) :
    cartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive =
      LinearMap.toMatrix
        (indecomposableProjectiveClassBasis P hind hPnoniso hPexhaustive)
        (simpleClassBasis S hSnoniso hSexhaustive)
        (cartanEquiv R h).toIntLinearEquiv := by
  ext i j
  simp [LinearMap.toMatrix_apply, cartanMap_of R (P j).2]

/-- The matrix of the inverse Cartan map in the simple-class basis on the source and the
indecomposable-projective basis on the target. Its columns are the projective coordinates of the
alternating finite-resolution classes of the selected simples. -/
noncomputable def inverseCartanMatrix
    (h : ModuleCat.isFG R ≤
      (ExactStructure.abelian (ModuleCat.{u} R)).admitsFiniteResolution
        (finiteProjectiveModules R)) :
    Matrix I I ℤ :=
  LinearMap.toMatrix
    (simpleClassBasis S hSnoniso hSexhaustive)
    (indecomposableProjectiveClassBasis P hind hPnoniso hPexhaustive)
    (cartanInverse R h).toIntLinearMap

/-- The `(i, j)` entry of the inverse Cartan matrix is the `i`th projective-basis coordinate of the
inverse Cartan map applied to the `j`th simple-basis vector. -/
theorem inverseCartanMatrix_apply
    (h : ModuleCat.isFG R ≤
      (ExactStructure.abelian (ModuleCat.{u} R)).admitsFiniteResolution
        (finiteProjectiveModules R)) (i j : I) :
    inverseCartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive h i j =
      (indecomposableProjectiveClassBasis P hind hPnoniso hPexhaustive).repr
        (cartanInverse R h (simpleClassBasis S hSnoniso hSexhaustive j)) i :=
  LinearMap.toMatrix_apply _ _ _ i j

/-- The inverse Cartan matrix is a right inverse of the Cartan matrix. -/
@[simp]
theorem cartanMatrix_mul_inverseCartanMatrix
    (h : ModuleCat.isFG R ≤
      (ExactStructure.abelian (ModuleCat.{u} R)).admitsFiniteResolution
        (finiteProjectiveModules R)) :
    cartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive *
      inverseCartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive h = 1 := by
  let bP := indecomposableProjectiveClassBasis P hind hPnoniso hPexhaustive
  let bS := simpleClassBasis S hSnoniso hSexhaustive
  rw [cartanMatrix_eq_toMatrix_cartanEquiv P S hind hPnoniso hPexhaustive hSnoniso
    hSexhaustive h, inverseCartanMatrix, ← LinearMap.toMatrix_comp]
  have hcomp : (cartanEquiv R h).toIntLinearEquiv.toLinearMap.comp
      (cartanInverse R h).toIntLinearMap = LinearMap.id := by
    ext x
    simpa only [LinearMap.comp_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
      AddEquiv.coe_toIntLinearEquiv, AddMonoidHom.coe_toIntLinearMap,
      ← cartanEquiv_symm_apply] using (cartanEquiv R h).apply_symm_apply x
  rw [hcomp, LinearMap.toMatrix_id]

/-- The inverse Cartan matrix is a left inverse of the Cartan matrix. -/
@[simp]
theorem inverseCartanMatrix_mul_cartanMatrix
    (h : ModuleCat.isFG R ≤
      (ExactStructure.abelian (ModuleCat.{u} R)).admitsFiniteResolution
        (finiteProjectiveModules R)) :
    inverseCartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive h *
      cartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive = 1 :=
  mul_eq_one_comm.mp
    (cartanMatrix_mul_inverseCartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive h)

/-- Under the finite-projective-resolution hypothesis, the Cartan matrix is invertible over
`ℤ`. -/
theorem isUnit_cartanMatrix
    (h : ModuleCat.isFG R ≤
      (ExactStructure.abelian (ModuleCat.{u} R)).admitsFiniteResolution
        (finiteProjectiveModules R)) :
    IsUnit (cartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive) :=
  .of_mul_eq_one
    (inverseCartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive h)
    (cartanMatrix_mul_inverseCartanMatrix P S hind hPnoniso hPexhaustive hSnoniso
      hSexhaustive h)

/-- Under the finite-projective-resolution hypothesis, the determinant of the Cartan matrix is a
unit in `ℤ`. -/
theorem isUnit_det_cartanMatrix
    (h : ModuleCat.isFG R ≤
      (ExactStructure.abelian (ModuleCat.{u} R)).admitsFiniteResolution
        (finiteProjectiveModules R)) :
    IsUnit (cartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive).det :=
  Matrix.isUnit_iff_isUnit_det _ |>.mp
    (isUnit_cartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive h)

/-- **Cartan-matrix unimodularity.** If every finitely generated module admits a finite resolution
by finitely generated projectives, the Cartan determinant is `1` or `-1`. No positivity of its
sign is asserted. -/
theorem cartanMatrix_det_eq_one_or_neg_one
    (h : ModuleCat.isFG R ≤
      (ExactStructure.abelian (ModuleCat.{u} R)).admitsFiniteResolution
        (finiteProjectiveModules R)) :
    (cartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive).det = 1 ∨
      (cartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive).det = -1 :=
  Int.isUnit_iff.mp
    (isUnit_det_cartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive h)

end TauCeti
