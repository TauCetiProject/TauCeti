/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Matrix.IntegralCast
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.CoordinateLattice
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.CubeZeroMatrix
public import TauCeti.Algebra.Lie.UniversalEnveloping.MatrixRepresentation

/-!
# Kostant root subgroups of cube-zero integral matrix families

Let `E : I → Matrix n n ℤ` satisfy `E i ^ 3 = 0` and `E i * E i = 2 • D i` for
`D : I → Matrix n n ℤ`. Coercing `E` into `Matrix n n ℚ` via `TauCeti.matrixIntCastLieHom ℚ` gives
root vectors acting nilpotently on `n → ℚ` whose Kostant `ℤ`-form preserves
`TauCeti.coordinateLattice n`. This file packages the resulting Kostant root subgroups in the
standard coordinate basis as homomorphisms `Multiplicative R →* Matrix.GeneralLinearGroup n R` over
any commutative ring `R`, proves their `1 + u • Eᵢ + u² • Dᵢ` matrix expansion, and gives an
entry-unit injectivity criterion.

## Main definitions and results

* `TauCeti.UniversalEnvelopingAlgebra.integralMatrixRootSubgroup` and
  `integralMatrixRootSubgroup_apply`: the Kostant root-subgroup homomorphism
  `Multiplicative R →* Matrix.GeneralLinearGroup n R` on `coordinateLattice n`.
* `TauCeti.UniversalEnvelopingAlgebra.pow_three_representation_matrix_eq_zero`,
  `isNilpotent_representation_matrix`, and `kostantForm_integralMatrix_mem_coordinateLattice`.
* `TauCeti.UniversalEnvelopingAlgebra.coe_integralMatrixRootSubgroup`,
  `coe_integralMatrixRootSubgroup_of_eq_zero`, and
  `integralMatrixRootSubgroup_eq_iff_of_entry_unit`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, §2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open scoped Matrix
open TauCeti (coordinateLattice coordinateLatticeBasis matrixIntCastLieHom)
open TauCeti.AdditiveGroup (gaPointsMulEquiv)
open Multiplicative (ofAdd toAdd)
open _root_.UniversalEnvelopingAlgebra (ι)

namespace TauCeti.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra
attribute [local instance] TauCeti.moduleNNRat

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An integral matrix that cubes to zero acts with vanishing cube on `n → ℚ`. -/
theorem pow_three_representation_matrix_eq_zero {X : Matrix n n ℤ} (hcube : X ^ 3 = 0) :
    representation ℚ (Matrix n n ℚ) (n → ℚ) (ι ℚ (matrixIntCastLieHom ℚ X)) ^ 3 = 0 := by
  rw [representation_matrix_ι, ← map_pow, pow_three, ← TauCeti.matrixIntCastLieHom_mul,
    ← TauCeti.matrixIntCastLieHom_mul, ← pow_three, hcube, map_zero, map_zero]

/-- An integral matrix that cubes to zero acts nilpotently on `n → ℚ`. -/
theorem isNilpotent_representation_matrix {X : Matrix n n ℤ} (hcube : X ^ 3 = 0) :
    IsNilpotent (representation ℚ (Matrix n n ℚ) (n → ℚ) (ι ℚ (matrixIntCastLieHom ℚ X))) :=
  ⟨3, pow_three_representation_matrix_eq_zero hcube⟩

/-- The standard coordinate lattice is preserved by the Kostant `ℤ`-form of any family of cube-zero
integral matrices whose squares are even integral matrices. -/
theorem kostantForm_integralMatrix_mem_coordinateLattice {I : Type*}
    (E D : I → Matrix n n ℤ) (hsq : ∀ i, E i * E i = 2 • D i) (hcube : ∀ i, E i ^ 3 = 0) :
    ∀ u ∈ kostantForm (fun i => matrixIntCastLieHom ℚ (E i)) Empty.elim,
      ∀ v ∈ (coordinateLattice n).toAddSubgroup,
        representation ℚ (Matrix n n ℚ) (n → ℚ) u v ∈ (coordinateLattice n).toAddSubgroup := by
  intro u hu v hv
  refine kostantForm_apply_mem_coordinateLattice_of_pow_eq_zero
    (fun i => matrixIntCastLieHom ℚ (E i)) Empty.elim (representation ℚ (Matrix n n ℚ) (n → ℚ))
    (wt := fun _ => Empty.elim) 3 (fun i => pow_three_representation_matrix_eq_zero (hcube i))
    (fun i m hm w hw => ?_) (fun a => (isCartanWeightVector_iff Empty.elim _).mpr Empty.rec) hu hv
  have hm' : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  rcases hm' with rfl | rfl | rfl
  · simpa using hw
  · rw [Associative.dividedPower_one, representation_ι_apply, Matrix.lie_apply]
    exact Matrix.intCastLieHom_mulVec_mem_coordinateLattice (E i) hw
  · rw [dividedPower_two_representation_matrix_apply
      (by rw [← TauCeti.matrixIntCastLieHom_mul, hsq i, map_nsmul])]
    exact Matrix.intCastLieHom_mulVec_mem_coordinateLattice (D i) hw

/-- **The Kostant root subgroup of a cube-zero integral matrix family** in the standard coordinate
basis over `R`. -/
noncomputable def integralMatrixRootSubgroup {I : Type*}
    (E D : I → Matrix n n ℤ) (hsq : ∀ i, E i * E i = 2 • D i) (hcube : ∀ i, E i ^ 3 = 0)
    (R : Type*) [CommRing R] (i : I) : Multiplicative R →* _root_.Matrix.GeneralLinearGroup n R :=
  (kostantRootSubgroupMatrix (fun k => matrixIntCastLieHom ℚ (E k)) Empty.elim
    (representation ℚ (Matrix n n ℚ) (n → ℚ)) (coordinateLattice n).toAddSubgroup
    (kostantForm_integralMatrix_mem_coordinateLattice E D hsq hcube) i
    (isNilpotent_representation_matrix (hcube i)) (coordinateLatticeBasis n)).comp
    (gaPointsMulEquiv (R := ℤ) (A := R)).symm.toMonoidHom

/-- Evaluating `integralMatrixRootSubgroup` applies `kostantRootSubgroupMatrix` in the standard
coordinate basis to the corresponding `𝔾ₐ`-point. -/
theorem integralMatrixRootSubgroup_apply {I : Type*}
    (E D : I → Matrix n n ℤ) (hsq : ∀ i, E i * E i = 2 • D i) (hcube : ∀ i, E i ^ 3 = 0)
    (R : Type*) [CommRing R] (i : I) (u : Multiplicative R) :
    integralMatrixRootSubgroup E D hsq hcube R i u =
      kostantRootSubgroupMatrix (fun k => matrixIntCastLieHom ℚ (E k)) Empty.elim
        (representation ℚ (Matrix n n ℚ) (n → ℚ)) (coordinateLattice n).toAddSubgroup
        (kostantForm_integralMatrix_mem_coordinateLattice E D hsq hcube) i
        (isNilpotent_representation_matrix (hcube i)) (coordinateLatticeBasis n)
        ((gaPointsMulEquiv (R := ℤ) (A := R)).symm u) := by rfl

/-- The matrix of `integralMatrixRootSubgroup` at `u` is `1 + u • Eᵢ + u² • Dᵢ`. -/
@[simp] theorem coe_integralMatrixRootSubgroup {I : Type*}
    (E D : I → Matrix n n ℤ) (hsq : ∀ i, E i * E i = 2 • D i) (hcube : ∀ i, E i ^ 3 = 0)
    (R : Type*) [CommRing R] (i : I) (u : Multiplicative R) :
    ((integralMatrixRootSubgroup E D hsq hcube R i u : _root_.Matrix.GeneralLinearGroup n R) :
        Matrix n n R) =
      1 + toAdd u • (E i).map (Int.cast : ℤ → R) + toAdd u ^ 2 • (D i).map (Int.cast : ℤ → R) := by
  have hact₁ : ∀ s, representation ℚ (Matrix n n ℚ) (n → ℚ) (ι ℚ (matrixIntCastLieHom ℚ (E i)))
        ((coordinateLatticeBasis n s : coordinateLattice n) : n → ℚ) =
      ∑ r, E i r s • ((coordinateLatticeBasis n r : coordinateLattice n) : n → ℚ) := fun s => by
    simpa only [representation_ι_apply, Matrix.lie_apply, TauCeti.matrixIntCastLieHom_eq_map,
      Int.coe_castRingHom] using Matrix.intCast_mulVec_coordinateLatticeBasis_eq_sum (E i) s
  have hact₂ : ∀ s, Associative.dividedPower 2
        (representation ℚ (Matrix n n ℚ) (n → ℚ) (ι ℚ (matrixIntCastLieHom ℚ (E i))))
        ((coordinateLatticeBasis n s : coordinateLattice n) : n → ℚ) =
      ∑ r, D i r s • ((coordinateLatticeBasis n r : coordinateLattice n) : n → ℚ) := fun s => by
    rw [dividedPower_two_representation_matrix_apply
      (by rw [← TauCeti.matrixIntCastLieHom_mul, hsq i, map_nsmul])]
    simpa only [TauCeti.matrixIntCastLieHom_eq_map, Int.coe_castRingHom] using
      Matrix.intCast_mulVec_coordinateLatticeBasis_eq_sum (D i) s
  simpa only [integralMatrixRootSubgroup_apply, MulEquiv.apply_symm_apply] using
    kostantRootSubgroupMatrix_eq_one_add_smul_add_smul (fun k => matrixIntCastLieHom ℚ (E k))
      Empty.elim (representation ℚ (Matrix n n ℚ) (n → ℚ)) (coordinateLattice n).toAddSubgroup
      (kostantForm_integralMatrix_mem_coordinateLattice E D hsq hcube) i
      (isNilpotent_representation_matrix (hcube i)) (coordinateLatticeBasis n) (E i) (D i)
      (nilpotencyClass_le_of_pow_eq_zero (pow_three_representation_matrix_eq_zero (hcube i)))
      hact₁ hact₂ ((gaPointsMulEquiv (R := ℤ) (A := R)).symm u)

/-- When the divided-square matrix `D i` vanishes, `integralMatrixRootSubgroup` is `1 + u • Eᵢ`. -/
theorem coe_integralMatrixRootSubgroup_of_eq_zero {I : Type*}
    (E D : I → Matrix n n ℤ) (hsq : ∀ i, E i * E i = 2 • D i) (hcube : ∀ i, E i ^ 3 = 0)
    (R : Type*) [CommRing R] {i : I} (hD : D i = 0) (u : Multiplicative R) :
    ((integralMatrixRootSubgroup E D hsq hcube R i u : _root_.Matrix.GeneralLinearGroup n R) :
        Matrix n n R) = 1 + toAdd u • (E i).map (Int.cast : ℤ → R) := by
  rw [coe_integralMatrixRootSubgroup, hD, Matrix.map_zero _ Int.cast_zero, smul_zero, add_zero]

/-- An off-diagonal entry `±1` where the divided square vanishes makes the root-subgroup
parametrization injective over every commutative ring. -/
theorem integralMatrixRootSubgroup_eq_iff_of_entry_unit {I : Type*}
    (E D : I → Matrix n n ℤ) (hsq : ∀ i, E i * E i = 2 • D i) (hcube : ∀ i, E i ^ 3 = 0)
    {R : Type*} [CommRing R] {i : I} {r s : n} (hrs : r ≠ s)
    (hE : E i r s = 1 ∨ E i r s = -1) (hD : D i r s = 0) (u v : R) :
    integralMatrixRootSubgroup E D hsq hcube R i (ofAdd u) =
      integralMatrixRootSubgroup E D hsq hcube R i (ofAdd v) ↔ u = v := by
  refine ⟨fun h => ?_, fun h => congrArg _ (congrArg ofAdd h)⟩
  have hentry := congrArg (fun g : _root_.Matrix.GeneralLinearGroup n R => (g : Matrix n n R) r s) h
  simp only [coe_integralMatrixRootSubgroup, toAdd_ofAdd, Matrix.add_apply, Matrix.one_apply_ne hrs,
    Matrix.smul_apply, Matrix.map_apply, hD, Int.cast_zero, smul_eq_mul, mul_zero, zero_add,
    add_zero] at hentry
  rcases hE with h1 | hm1
  · simpa [h1] using hentry
  · exact neg_inj.mp (by simpa [hm1] using hentry)

end TauCeti.UniversalEnvelopingAlgebra
