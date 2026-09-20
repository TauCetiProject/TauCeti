/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Coordinate
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.FromMatrix

/-!
# Coordinate morphisms out of `GLₙ` determined by a multiplicative matrix

A square matrix `Y` over a commutative Hopf algebra `S` is **multiplicative** when

```text
Y.map Δ = (Y ⊗ 1) (1 ⊗ Y),   Y.map ε = 1,
```

that is, when each entry comultiplies as `Δ Yᵢⱼ = ∑ₖ Yᵢₖ ⊗ Yₖⱼ` and counits to the corresponding
entry of the identity matrix. The generic matrix satisfies these identities, and transporting it
along a bialgebra morphism preserves them. Conversely, a multiplicative matrix determines a
morphism
of commutative Hopf algebras

```text
O(GLₙ) →ₐc[R] S
```

carrying the generic matrix to `Y`. Contravariantly, a multiplicative matrix over the coordinate
Hopf algebra of an affine group scheme `G` is the same thing as a homomorphism `G → GLₙ`, hence the
same thing as an `n`-dimensional representation of `G`; the conditions say that the matrix is
multiplicative and unital on points, functorially in the value algebra.

The determinant of a multiplicative matrix is automatically invertible — it is a group-like
element of
`S` — so no separate hypothesis is needed to land in `GLₙ` rather than in the matrix monoid.

The matrix-to-comodule construction lives in
`TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.FromMatrix`. This file applies it to obtain
the coordinate morphism. The coordinate algebra of `GLₙ` inverts the determinant, and the entries
of the inverse matrix are received through the antipode, so the target is required to be a Hopf
algebra.

## Main declarations

* `TauCeti.GeneralLinear.coordinateBialgHomOfMultiplicative`: the coordinate morphism of a
  multiplicative matrix, with its evaluation lemmas on the generic entries and their antipodes.
* `TauCeti.GeneralLinear.coordinateBialgHomOfMultiplicative_map_genericMatrix`: reconstructing a
  coordinate morphism from its transported generic matrix returns the original morphism.
* `TauCeti.GeneralLinear.map_comul_map_genericMatrix` and
  `TauCeti.GeneralLinear.map_counit_map_genericMatrix`: the image of the generic matrix under a
  morphism of commutative bialgebras is multiplicative.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes* (1979), §3.2, where representations of
  an affine group scheme are matched with comodules through their matrix coefficients.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.8.

The standard comodule `TauCeti.GeneralLinear.standardComodule` is obtained by specializing this
construction to the generic matrix.
-/

public section

open Module WithConv
open scoped TensorProduct

namespace TauCeti.GeneralLinear

universe u v

variable (R : Type u) (n : ℕ)


/-! ### The generic matrix transported along a coordinate morphism -/

section Transport

variable [CommRing R] {S : Type v} [Semiring S] [Bialgebra R S] {R n}
variable (φ : coordinateHopfAlgebra R n →ₐc[R] S)

/-- **The comultiplication condition for the generic matrix transported along a morphism of
commutative bialgebras.** The image of the generic matrix under any such morphism is
multiplicative, since the generic matrix is and the morphism respects comultiplication. -/
@[simp] theorem map_comul_map_genericMatrix :
    (genericMatrix R n).map ((Bialgebra.comulAlgHom R S) ∘ φ) =
      ((genericMatrix R n).map φ).map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        ((genericMatrix R n).map φ).map (Algebra.TensorProduct.includeRight (R := R)) :=
  Matrix.map_map.symm.trans
    (Comodule.map_comul_map R (genericMatrix R n) φ (map_comul_genericMatrix R n))

/-- **The counit condition for the generic matrix transported along a morphism of commutative
bialgebras.** -/
@[simp] theorem map_counit_map_genericMatrix :
    (genericMatrix R n).map ((Bialgebra.counitAlgHom R S) ∘ φ) = 1 :=
  Matrix.map_map.symm.trans
    (Comodule.map_counit_map R (genericMatrix R n) φ (map_counit_genericMatrix R n))

end Transport

/-! ### The coordinate morphism of a multiplicative matrix

The coordinate algebra of `GLₙ` inverts the determinant, so a morphism out of it needs the
antipode of `S` to receive the entries of the inverse matrix; this part asks for a Hopf
algebra. -/

section CoordinateMorphism

variable [CommRing R]
variable {S : Type v} [CommRing S] [HopfAlgebra R S]
variable (Y : Matrix (Fin n) (Fin n) S)
variable (hcomul : Y.map (Bialgebra.comulAlgHom R S) =
    Y.map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
      Y.map (Algebra.TensorProduct.includeRight (R := R)))
variable (hcounit : Y.map (Bialgebra.counitAlgHom R S) = 1)

include hcomul hcounit in
/-- **The coordinate morphism of a multiplicative matrix**: the morphism of commutative Hopf
algebras out of the coordinate algebra of `GL n` sending the generic matrix to `Y`. -/
noncomputable def coordinateBialgHomOfMultiplicative :
    coordinateHopfAlgebra R n →ₐc[R] S := by
  letI : Comodule R S (Fin n → R) := Comodule.matrixComodule R Y hcomul
    (Comodule.counit_basisFun_of_map_counit R Y hcounit)
  exact Comodule.coordinateBialgHom (Pi.basisFun R (Fin n))

include hcomul hcounit in
/-- The coordinate morphism of a multiplicative matrix sends a generic matrix entry to the
corresponding entry of the matrix. -/
@[simp]
theorem coordinateBialgHomOfMultiplicative_X (i j : Fin n) :
    coordinateBialgHomOfMultiplicative R n Y hcomul hcounit
        (coordinateHopfAlgebraAlgEquiv R n
          (coordinateRingMap R n (MvPolynomial.X (i, j)))) = Y i j := by
  let : Comodule R S (Fin n → R) := Comodule.matrixComodule R Y hcomul
    (Comodule.counit_basisFun_of_map_counit R Y hcounit)
  unfold coordinateBialgHomOfMultiplicative
  refine Eq.trans (Comodule.coordinateBialgHom_X (H := S) (Pi.basisFun R (Fin n)) i j) ?_
  exact congrFun (congrFun (Comodule.coefficientMatrix_matrixComodule R Y hcomul
    (Comodule.counit_basisFun_of_map_counit R Y hcounit)) i) j

include hcomul hcounit in
/-- The coordinate morphism of a multiplicative matrix sends an inverse generic-matrix entry to the
antipode of the corresponding matrix entry. -/
@[simp]
theorem coordinateBialgHomOfMultiplicative_antipode_X (i j : Fin n) :
    coordinateBialgHomOfMultiplicative R n Y hcomul hcounit
        (coordinateHopfAlgebraAlgEquiv R n ((localizedGenericMatrix R n)⁻¹ i j)) =
      HopfAlgebra.antipode R (Y i j) := by
  let : Comodule R S (Fin n → R) := Comodule.matrixComodule R Y hcomul
    (Comodule.counit_basisFun_of_map_counit R Y hcounit)
  unfold coordinateBialgHomOfMultiplicative
  refine Eq.trans (Comodule.coordinateBialgHom_antipode_X
    (H := S) (Pi.basisFun R (Fin n)) i j) ?_
  exact congrArg (HopfAlgebra.antipode R)
    (congrFun (congrFun (Comodule.coefficientMatrix_matrixComodule R Y hcomul
      (Comodule.counit_basisFun_of_map_counit R Y hcounit)) i) j)

include hcomul hcounit in
/-- The coordinate morphism of a multiplicative matrix carries the generic matrix to that matrix. -/
@[simp]
theorem map_genericMatrix_coordinateBialgHomOfMultiplicative :
    (genericMatrix R n).map (coordinateBialgHomOfMultiplicative R n Y hcomul hcounit) = Y := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.map_apply, genericMatrix_apply, coordinateBialgHomOfMultiplicative_X]

/-- Reconstructing a bialgebra morphism from its image of the generic matrix returns the original
morphism. -/
@[simp]
theorem coordinateBialgHomOfMultiplicative_map_genericMatrix
    (φ : coordinateHopfAlgebra R n →ₐc[R] S) :
    coordinateBialgHomOfMultiplicative R n ((genericMatrix R n).map φ)
        (Matrix.map_map.trans (map_comul_map_genericMatrix φ))
        (Matrix.map_map.trans (map_counit_map_genericMatrix φ)) = φ := by
  apply coordinateHopfAlgebra_bialgHom_ext
  intro i j
  rw [coordinateBialgHomOfMultiplicative_X, Matrix.map_apply, genericMatrix_apply]

end CoordinateMorphism

end TauCeti.GeneralLinear
