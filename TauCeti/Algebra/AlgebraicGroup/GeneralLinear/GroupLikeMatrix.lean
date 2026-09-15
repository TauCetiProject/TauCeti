/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Coordinate

/-!
# Coordinate morphisms out of `GLₙ` determined by a grouplike matrix

A square matrix `Y` over a commutative Hopf algebra `S` is **grouplike** when

```text
Y.map Δ = (Y ⊗ 1) (1 ⊗ Y),   Y.map ε = 1,
```

that is, when each entry comultiplies as `Δ Yᵢⱼ = ∑ₖ Yᵢₖ ⊗ Yₖⱼ` and counits to the corresponding
entry of the identity matrix. These are exactly the conditions making the columns of `Y` a
coaction of `S` on the free module `Rⁿ`, so a grouplike matrix determines a morphism of
commutative Hopf algebras

```text
O(GLₙ) →ₐc[R] S
```

carrying the generic matrix to `Y`. Contravariantly, a grouplike matrix over the coordinate Hopf
algebra of an affine group scheme `G` is the same thing as a homomorphism `G → GLₙ`, hence the
same thing as an `n`-dimensional representation of `G`; the conditions say that the matrix is
multiplicative and unital on points, functorially in the value algebra.

The determinant of a grouplike matrix is automatically invertible — it is a grouplike element of
`S` — so no separate hypothesis is needed to land in `GLₙ` rather than in the matrix monoid.

The comodule uses only the comultiplication and the counit of `S`, so it is built over a
bialgebra. The coordinate morphism needs more: the coordinate algebra of `GLₙ` inverts the
determinant, and the entries of the inverse matrix are received through the antipode, so that
half of the file asks for a Hopf algebra.

The construction is the comodule of the matrix followed by
`TauCeti.Comodule.coordinateBialgHom`, the coordinate morphism of a comodule with a basis. The
generic matrix of `GLₙ` is the case `S = O(GLₙ)` and `Y = X`, where the resulting morphism is the
identity.

## Main declarations

* `TauCeti.GeneralLinear.matrixCoact` and `TauCeti.GeneralLinear.matrixComodule`: the candidate
  coaction on column vectors given by the columns of a matrix, and the comodule it defines when the
  matrix is grouplike, with `TauCeti.GeneralLinear.coact_matrixComodule` unfolding the latter's
  coaction and `TauCeti.GeneralLinear.coefficientMatrix_matrixComodule` computing its coefficient
  matrix.
* `TauCeti.GeneralLinear.coordinateBialgHomOfGroupLike`: the coordinate morphism of a grouplike
  matrix, with `TauCeti.GeneralLinear.coordinateBialgHomOfGroupLike_X` and
  `TauCeti.GeneralLinear.map_genericMatrix_coordinateBialgHomOfGroupLike` identifying its value on
  the generic matrix.
* `TauCeti.GeneralLinear.comul_apply_of_map_comul` and
  `TauCeti.GeneralLinear.counit_apply_of_map_counit`: the entrywise form of the two conditions.
* `TauCeti.GeneralLinear.map_genericMatrix_map_comul` and
  `TauCeti.GeneralLinear.map_genericMatrix_map_counit`: the image of the generic matrix under a
  morphism of commutative bialgebras is grouplike.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes* (1979), §3.2, where representations of
  an affine group scheme are matched with comodules through their matrix coefficients.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.8.

The comodule construction follows the template of
`TauCeti.GeneralLinear.standardComodule`, which is the case of the generic matrix.
-/

public section

open Module WithConv
open scoped TensorProduct

namespace TauCeti.GeneralLinear

universe u v

variable (R : Type u) [CommRing R] (n : ℕ)

/-! ### The comodule of a grouplike matrix

Only the comultiplication and counit of `S` are used here, so this part asks for a bialgebra. -/

section Coaction

variable {S : Type v} [CommRing S] [Bialgebra R S]
variable (Y : Matrix (Fin n) (Fin n) S)

/-- The candidate coaction on column vectors determined by a square matrix over a commutative
bialgebra: the `j`th basis vector goes to the `j`th column of the matrix. This is a linear map for
an arbitrary matrix; the coassociativity and counit laws that make it a coaction come from the
grouplike hypotheses of `TauCeti.GeneralLinear.matrixComodule`. -/
noncomputable def matrixCoact :
    (Fin n → R) →ₗ[R] (Fin n → R) ⊗[R] S :=
  (Pi.basisFun R (Fin n)).constr R fun j ↦
    ∑ i, (Pi.single i (1 : R) : Fin n → R) ⊗ₜ[R] Y i j

/-- The candidate coaction of a matrix takes a basis vector to the corresponding column. -/
@[simp]
theorem matrixCoact_basisFun (j : Fin n) :
    matrixCoact R n Y (Pi.single j 1) =
      ∑ i, (Pi.single i (1 : R) : Fin n → R) ⊗ₜ[R] Y i j := by
  rw [matrixCoact, ← Pi.basisFun_apply, Basis.constr_basis]

variable (hcomul : Y.map (Bialgebra.comulAlgHom R S) =
    Y.map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
      Y.map (Algebra.TensorProduct.includeRight (R := R)))
variable (hcounit : Y.map (Bialgebra.counitAlgHom R S) = 1)

include hcomul in
/-- The entrywise form of the comultiplication condition on a grouplike matrix. -/
theorem comul_apply_of_map_comul (i j : Fin n) :
    Coalgebra.comul (R := R) (Y i j) = ∑ k, Y i k ⊗ₜ[R] Y k j := by
  have h := congrFun (congrFun hcomul i) j
  rw [Matrix.map_apply, Bialgebra.comulAlgHom_apply, Matrix.mul_apply] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.map_apply, Matrix.map_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, mul_one]

include hcounit in
/-- The entrywise form of the counit condition on a grouplike matrix. -/
theorem counit_apply_of_map_counit (i j : Fin n) :
    Coalgebra.counit (R := R) (Y i j) = if i = j then 1 else 0 := by
  have h := congrFun (congrFun hcounit i) j
  rw [Matrix.map_apply, Bialgebra.counitAlgHom_apply, Matrix.one_apply] at h
  exact h

include hcomul hcounit in
/-- **A grouplike matrix makes the column space a comodule.** -/
@[instance_reducible]
noncomputable def matrixComodule : Comodule R S (Fin n → R) where
  coact := matrixCoact R n Y
  coassoc := by
    apply (Pi.basisFun R (Fin n)).ext
    intro j
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [Pi.basisFun_apply, matrixCoact_basisFun]
    simp only [map_sum, LinearMap.rTensor_tmul, matrixCoact_basisFun,
      TensorProduct.sum_tmul, LinearEquiv.coe_coe, TensorProduct.assoc_tmul,
      LinearMap.lTensor_tmul, comul_apply_of_map_comul R n Y hcomul,
      TensorProduct.tmul_sum]
    rw [Finset.sum_comm]
  lTensor_counit_comp_coact := by
    apply (Pi.basisFun R (Fin n)).ext
    intro j
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [Pi.basisFun_apply, matrixCoact_basisFun]
    simp only [map_sum, LinearMap.lTensor_tmul, counit_apply_of_map_counit R n Y hcounit]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · simp

include hcomul hcounit in
/-- The coaction of the comodule of a grouplike matrix is that matrix's coaction. This is the
unfolding lemma through which the comodule's matrix coefficients are computed. -/
theorem coact_matrixComodule :
    letI : Comodule R S (Fin n → R) := matrixComodule R n Y hcomul hcounit
    Comodule.coact (R := R) (C := S) (M := Fin n → R) = matrixCoact R n Y :=
  (rfl)

include hcomul hcounit in
/-- The coefficient matrix of the comodule of a grouplike matrix is that matrix. -/
@[simp]
theorem coefficientMatrix_matrixComodule :
    letI : Comodule R S (Fin n → R) := matrixComodule R n Y hcomul hcounit
    Comodule.coefficientMatrix (C := S) (Pi.basisFun R (Fin n)) = Y := by
  let : Comodule R S (Fin n → R) := matrixComodule R n Y hcomul hcounit
  refine Matrix.ext fun i j => ?_
  rw [Comodule.coefficientMatrix_apply, Comodule.matrixCoefficient_def,
    coact_matrixComodule R n Y hcomul hcounit, Pi.basisFun_apply, matrixCoact_basisFun]
  simp [Pi.single_apply]

/-! ### The generic matrix transported along a coordinate morphism -/

section Transport

variable {R n}
variable (φ : coordinateHopfAlgebra R n →ₐc[R] S)

/-- **The comultiplication condition for the generic matrix transported along a morphism of
commutative Hopf algebras.** The image of the generic matrix under any such morphism is
grouplike, since the generic matrix is and the morphism respects comultiplication. -/
theorem map_genericMatrix_map_comul :
    ((genericMatrix R n).map φ).map (Bialgebra.comulAlgHom R S) =
      ((genericMatrix R n).map φ).map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        ((genericMatrix R n).map φ).map (Algebra.TensorProduct.includeRight (R := R)) := by
  have hcomul : (Bialgebra.comulAlgHom R S : S → S ⊗[R] S) ∘ (φ : _ → S) =
      (Algebra.TensorProduct.map φ.toAlgHom φ.toAlgHom : _ → S ⊗[R] S) ∘
        (Bialgebra.comulAlgHom R (coordinateHopfAlgebra R n) : _ → _) :=
    funext fun x => (CoalgHomClass.map_comp_comul_apply φ x).symm
  rw [Matrix.map_map, hcomul, ← Matrix.map_map, map_comul_genericMatrix,
    Matrix.map_mul, Matrix.map_map, Matrix.map_map, Matrix.map_map, Matrix.map_map]
  refine congrArg₂ (· * ·) (congrArg _ (funext fun x => ?_)) (congrArg _ (funext fun x => ?_))
  · exact congrFun (congrArg (fun f : coordinateHopfAlgebra R n →ₐ[R] S ⊗[R] S => (f : _ → _))
      (Algebra.TensorProduct.map_comp_includeLeft (S := R) (φ.toAlgHom) (φ.toAlgHom))) x
  · exact congrFun (congrArg (fun f : coordinateHopfAlgebra R n →ₐ[R] S ⊗[R] S => (f : _ → _))
      (Algebra.TensorProduct.map_comp_includeRight (φ.toAlgHom) (φ.toAlgHom))) x

/-- **The counit condition for the generic matrix transported along a morphism of commutative
bialgebras.** -/
theorem map_genericMatrix_map_counit :
    ((genericMatrix R n).map φ).map (Bialgebra.counitAlgHom R S) = 1 := by
  have hcounit : (Bialgebra.counitAlgHom R S : S → R) ∘ (φ : _ → S) =
      (Bialgebra.counitAlgHom R (coordinateHopfAlgebra R n) : _ → R) :=
    funext fun x => CoalgHomClass.counit_comp_apply φ x
  rw [Matrix.map_map, hcounit, map_counit_genericMatrix]

end Transport

end Coaction

/-! ### The coordinate morphism of a grouplike matrix

The coordinate algebra of `GLₙ` inverts the determinant, so a morphism out of it needs the
antipode of `S` to receive the entries of the inverse matrix; this part asks for a Hopf
algebra. -/

section CoordinateMorphism

variable {S : Type v} [CommRing S] [HopfAlgebra R S]
variable (Y : Matrix (Fin n) (Fin n) S)
variable (hcomul : Y.map (Bialgebra.comulAlgHom R S) =
    Y.map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
      Y.map (Algebra.TensorProduct.includeRight (R := R)))
variable (hcounit : Y.map (Bialgebra.counitAlgHom R S) = 1)

include hcomul hcounit in
/-- **The coordinate morphism of a grouplike matrix**: the morphism of commutative Hopf algebras
out of the coordinate algebra of `GL n` sending the generic matrix to `Y`. -/
noncomputable def coordinateBialgHomOfGroupLike :
    coordinateHopfAlgebra R n →ₐc[R] S := by
  letI : Comodule R S (Fin n → R) := matrixComodule R n Y hcomul hcounit
  exact Comodule.coordinateBialgHom (Pi.basisFun R (Fin n))

include hcomul hcounit in
/-- The coordinate morphism of a grouplike matrix sends a generic matrix entry to the
corresponding entry of the matrix. -/
@[simp]
theorem coordinateBialgHomOfGroupLike_X (i j : Fin n) :
    coordinateBialgHomOfGroupLike R n Y hcomul hcounit
        (coordinateHopfAlgebraAlgEquiv R n
          (coordinateRingMap R n (MvPolynomial.X (i, j)))) = Y i j := by
  let : Comodule R S (Fin n → R) := matrixComodule R n Y hcomul hcounit
  refine Eq.trans (Comodule.coordinateBialgHom_X (H := S) (Pi.basisFun R (Fin n)) i j) ?_
  exact congrFun (congrFun (coefficientMatrix_matrixComodule R n Y hcomul hcounit) i) j

include hcomul hcounit in
/-- The coordinate morphism of a grouplike matrix carries the generic matrix to that matrix. -/
@[simp]
theorem map_genericMatrix_coordinateBialgHomOfGroupLike :
    (genericMatrix R n).map (coordinateBialgHomOfGroupLike R n Y hcomul hcounit) = Y := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.map_apply, genericMatrix_apply, coordinateBialgHomOfGroupLike_X]

end CoordinateMorphism

end TauCeti.GeneralLinear
