/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Matrix
public import Mathlib.RingTheory.Bialgebra.Hom

/-!
# A comodule reconstructed from a multiplicative matrix

A square matrix whose entries satisfy the matrix comultiplication and counit identities defines a
coaction on a finite free module. Its coefficient matrix is the original matrix, so this reverses
the coefficient-matrix construction.

## Main declarations

* `TauCeti.Comodule.matrixCoact`: the candidate coaction given by the matrix columns.
* `TauCeti.Comodule.matrixComodule`: the resulting comodule for a multiplicative matrix.
* `TauCeti.Comodule.coefficientMatrix_matrixComodule`: its coefficient matrix is the input.
-/

public section

open Module WithConv
open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w

variable (R : Type u) {ι : Type*} [Fintype ι]

/-! ### The comodule of a multiplicative matrix

Only the comultiplication and counit of `S` are used here, so this part asks for a bialgebra. -/

section CandidateCoaction

variable [CommSemiring R] {S : Type v} [AddCommMonoid S] [Module R S]
variable (Y : Matrix ι ι S)

/-- The candidate coaction on column vectors determined by a square matrix over an `R`-module: the
`j`th basis vector goes to the `j`th column of the matrix. This is a linear map for an arbitrary
matrix; the coassociativity and counit laws that make it a coaction come from the multiplicativity
hypotheses of `TauCeti.Comodule.matrixComodule`. -/
noncomputable def matrixCoact :
    (ι → R) →ₗ[R] (ι → R) ⊗[R] S := by
  classical
  exact (Pi.basisFun R ι).constr R fun j ↦
    ∑ i, (Pi.basisFun R ι) i ⊗ₜ[R] Y i j

/-- The candidate coaction of a matrix takes a basis vector to the corresponding column. -/
@[simp]
theorem matrixCoact_apply_basisFun (j : ι) :
    matrixCoact R Y ((Pi.basisFun R ι) j) =
      ∑ i, (Pi.basisFun R ι) i ⊗ₜ[R] Y i j := by
  rw [matrixCoact, Basis.constr_basis]

end CandidateCoaction

section Coaction

variable [CommSemiring R] {S : Type v} [Semiring S] [Bialgebra R S]
variable (Y : Matrix ι ι S)

/-- The matrix comultiplication condition is equivalent to its entrywise form. -/
theorem map_comul_iff :
    Y.map (Bialgebra.comulAlgHom R S) =
        Y.map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
          Y.map (Algebra.TensorProduct.includeRight (R := R)) ↔
      ∀ i j, Coalgebra.comul (R := R) (Y i j) = ∑ k, Y i k ⊗ₜ[R] Y k j := by
  constructor
  · intro h i j
    have hij := congrFun (congrFun h i) j
    rw [Matrix.map_apply, Bialgebra.comulAlgHom_apply, Matrix.mul_apply] at hij
    rw [hij]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.map_apply, Matrix.map_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one]
  · intro h
    ext i j
    simpa [Matrix.mul_apply] using h i j

omit [Fintype ι] in
/-- The matrix counit condition is equivalent to its entrywise form. -/
theorem map_counit_iff [DecidableEq ι] :
    Y.map (Bialgebra.counitAlgHom R S) = 1 ↔
      ∀ i j, Coalgebra.counit (R := R) (Y i j) = if i = j then 1 else 0 := by
  constructor
  · intro h i j
    have hij := congrFun (congrFun h i) j
    rw [Matrix.map_apply, Bialgebra.counitAlgHom_apply, Matrix.one_apply] at hij
    exact hij
  · intro h
    ext i j
    rw [Matrix.map_apply, Bialgebra.counitAlgHom_apply, Matrix.one_apply]
    exact h i j

section Map

variable {T : Type w} [Semiring T] [Bialgebra R T]
variable (f : S →ₐc[R] T)

/-- A morphism of bialgebras carries the matrix comultiplication condition to the entrywise image
of the matrix. -/
theorem map_comul_map
    (hcomul : Y.map (Bialgebra.comulAlgHom R S) =
      Y.map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        Y.map (Algebra.TensorProduct.includeRight (R := R))) :
    (Y.map f).map (Bialgebra.comulAlgHom R T) =
      (Y.map f).map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        (Y.map f).map (Algebra.TensorProduct.includeRight (R := R)) := by
  rw [map_comul_iff]
  intro i j
  have hentry := (map_comul_iff R Y).mp hcomul i j
  calc
    Coalgebra.comul (R := R) ((Y.map f) i j) =
        Algebra.TensorProduct.map f.toAlgHom f.toAlgHom
          (Coalgebra.comul (R := R) (Y i j)) := by
      rw [Matrix.map_apply]
      exact (CoalgHomClass.map_comp_comul_apply f _).symm
    _ = Algebra.TensorProduct.map f.toAlgHom f.toAlgHom
          (∑ k, Y i k ⊗ₜ[R] Y k j) := by rw [hentry]
    _ = ∑ k, (Y.map f) i k ⊗ₜ[R] (Y.map f) k j := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Algebra.TensorProduct.map_tmul, Matrix.map_apply, BialgHom.coe_toAlgHom]

omit [Fintype ι] in
/-- A morphism of bialgebras carries the matrix counit condition to the entrywise image of the
matrix. -/
theorem map_counit_map [DecidableEq ι]
    (hcounit : Y.map (Bialgebra.counitAlgHom R S) = 1) :
    (Y.map f).map (Bialgebra.counitAlgHom R T) = 1 := by
  rw [map_counit_iff]
  intro i j
  rw [Matrix.map_apply, CoalgHomClass.counit_comp_apply]
  exact (map_counit_iff R Y).mp hcounit i j

end Map

omit [Fintype ι] in
/-- The matrix counit identity gives the basis-coordinate form needed to construct a comodule.
This form does not expose a decidable-equality requirement on the reconstructed comodule. -/
theorem counit_basisFun_of_map_counit [Finite ι] [DecidableEq ι]
    (hcounit : Y.map (Bialgebra.counitAlgHom R S) = 1) :
    ∀ i j, Coalgebra.counit (R := R) (Y i j) =
      (Pi.basisFun R ι).repr ((Pi.basisFun R ι) j) i := by
  intro i j
  rw [(map_counit_iff R Y).mp hcounit, Basis.repr_self_apply]
  simp only [eq_comm]

variable (hcomul : Y.map (Bialgebra.comulAlgHom R S) =
    Y.map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
      Y.map (Algebra.TensorProduct.includeRight (R := R)))
variable (hcounit : ∀ i j, Coalgebra.counit (R := R) (Y i j) =
  (Pi.basisFun R ι).repr ((Pi.basisFun R ι) j) i)

include hcomul hcounit in
/-- **A multiplicative matrix makes the column space a comodule.** -/
@[instance_reducible]
noncomputable def matrixComodule : TauCeti.Comodule R S (ι → R) where
  coact := matrixCoact R Y
  coassoc := by
    classical
    apply (Pi.basisFun R ι).ext
    intro j
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [matrixCoact_apply_basisFun]
    simp only [map_sum, LinearMap.rTensor_tmul, matrixCoact_apply_basisFun,
      TensorProduct.sum_tmul, LinearEquiv.coe_coe, TensorProduct.assoc_tmul,
      LinearMap.lTensor_tmul, (map_comul_iff R Y).mp hcomul,
      TensorProduct.tmul_sum]
    rw [Finset.sum_comm]
  lTensor_counit_comp_coact := by
    classical
    apply (Pi.basisFun R ι).ext
    intro j
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [matrixCoact_apply_basisFun]
    simp only [map_sum, LinearMap.lTensor_tmul, hcounit, Pi.basisFun_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · simp

include hcomul hcounit in
/-- The coaction of the comodule of a multiplicative matrix is that matrix's coaction. This is the
unfolding lemma through which the comodule's matrix coefficients are computed. -/
@[simp]
theorem matrixComodule_coact :
    letI : TauCeti.Comodule R S (ι → R) := matrixComodule R Y hcomul hcounit
    TauCeti.Comodule.coact (R := R) (C := S) (M := ι → R) = matrixCoact R Y :=
  (rfl)

include hcomul hcounit in
/-- The coefficient matrix of the comodule of a multiplicative matrix is that matrix. -/
@[simp]
theorem coefficientMatrix_matrixComodule :
    letI : TauCeti.Comodule R S (ι → R) := matrixComodule R Y hcomul hcounit
    TauCeti.Comodule.coefficientMatrix (C := S) (Pi.basisFun R ι) = Y := by
  classical
  let : TauCeti.Comodule R S (ι → R) := matrixComodule R Y hcomul hcounit
  refine Matrix.ext fun i j => ?_
  rw [Comodule.coefficientMatrix_apply, Comodule.matrixCoefficient_def,
    matrixComodule_coact R Y hcomul hcounit,
    matrixCoact_apply_basisFun]
  simp [Pi.basisFun_apply, Pi.single_apply]

end Coaction


end TauCeti.Comodule
