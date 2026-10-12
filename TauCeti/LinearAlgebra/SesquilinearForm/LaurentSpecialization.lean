/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import TauCeti.Algebra.Polynomial.Laurent.Specialization

/-!
# Specializing q-sesquilinear forms at a unit

Let `R` be a commutative ring.  For a unit `ε` of `R` and a module `N` over `R[q,q⁻¹]`, the
specialization `N_ε = TauCeti.LaurentSpecialization ε N` is the base change of `N` along
evaluation at `q = ε`; on it `q` acts as `ε`.

A sesquilinear form `b : N₁ × N₂ → R[q,q⁻¹]`, antilinear in its first argument for the involution
`q ↦ q⁻¹` (`LaurentPolynomial.invert`) and linear in its second, specializes to an `R`-bilinear
form on `N₁_ε₁ × N₂_ε₂` with values `laurentEval ε₂ (b x y)` whenever `ε₁⁻¹ = ε₂`: evaluating
`invert p` at `ε₂` is evaluating `p` at `ε₂⁻¹`.  Taking `ε₁ = ε₂ = ε` needs `ε⁻¹ = ε`; over
`R = ℤ` this is automatic, the two units being `q = 1` and `q = -1`.  This is how the q-Euler form
of a graded category specializes.

Specialization does not preserve nondegeneracy: over a nontrivial coefficient ring, the Laurent
matrix with rows `(1, q)` and `(q, 1)` has determinant `1 - q²`, which is a non-zero-divisor,
while its value at any `ε` with `ε⁻¹ = ε` has determinant zero.

The concrete matrix `!![1, 1; 1, q]` over `ℤ[q,q⁻¹]` gives an explicit example at `q = 1`: its
determinant is `q - 1`, while the specialization has nonzero kernel vector `(1, -1)`.

## Main definitions

* `LinearMap.laurentSpecialize`: the specialization of a q-sesquilinear form.

## Main results

* `LinearMap.laurentSpecialize_mk_mk`: the specialized form is evaluation of the original one.
* `TauCeti.exists_nondegenerate_and_not_nondegenerate_map_laurentEval`: nondegeneracy of a
  Laurent-polynomial matrix need not survive evaluation at `q = ±1`.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* **185** (2022), Sections 1.2 and 3.1, on the specialization of
  the q-Euler form and the warning that it may become degenerate.
-/

public section

open LaurentPolynomial

namespace LinearMap

open TauCeti TauCeti.LaurentSpecialization

variable {R : Type*} [CommRing R] {ε₁ ε₂ : Rˣ}
variable {N₁ N₂ : Type*} [AddCommGroup N₁] [Module R[T;T⁻¹] N₁] [Module R N₁]
  [IsScalarTower R R[T;T⁻¹] N₁] [AddCommGroup N₂] [Module R[T;T⁻¹] N₂] [Module R N₂]
  [IsScalarTower R R[T;T⁻¹] N₂]

/-- A q-sesquilinear form evaluated at `q = ε₂`, as an `R`-bilinear form on the unspecialized
modules. -/
private noncomputable def laurentEvalForm
    (b : N₁ →ₛₗ[(invert (R := R)).toRingEquiv.toRingHom] N₂ →ₗ[R[T;T⁻¹]] R[T;T⁻¹]) :
    N₁ →ₗ[R] N₂ →ₗ[R] R :=
  LinearMap.mk₂ R (fun x y => laurentEval ε₂ (b x y))
    (fun x₁ x₂ y => by rw [LinearMap.map_add₂, map_add])
    (fun r x y => by
      rw [← algebraMap_smul (A := R[T;T⁻¹]) r x, LinearMap.map_smulₛₗ₂, smul_eq_mul, map_mul]
      simp)
    (fun x y₁ y₂ => by rw [map_add, map_add])
    (fun r x y => by
      rw [← algebraMap_smul (A := R[T;T⁻¹]) r y, map_smul, smul_eq_mul, map_mul]
      simp)

/-- The evaluated form takes the values of `b` evaluated at `ε₂`. -/
private theorem laurentEvalForm_apply
    (b : N₁ →ₛₗ[(invert (R := R)).toRingEquiv.toRingHom] N₂ →ₗ[R[T;T⁻¹]] R[T;T⁻¹])
    (x : N₁) (y : N₂) :
    laurentEvalForm (ε₂ := ε₂) b x y = laurentEval ε₂ (b x y) :=
  LinearMap.mk₂_apply ..

/-- **The specialization of a q-sesquilinear form**, at `q = ε₁` in the first argument and at
`q = ε₂` in the second, for units with `ε₁⁻¹ = ε₂`.  The form `b` is antilinear in its first
argument for `q ↦ q⁻¹` and linear in its second; its specialization is the `R`-bilinear form on
the specialized modules whose values are the values of `b` evaluated at `ε₂`.  Taking
`ε₁ = ε₂ = ε` specializes both arguments at a unit with `ε⁻¹ = ε`; over `ℤ` this holds for both
units, `q = 1` and `q = -1`. -/
noncomputable def laurentSpecialize
    (b : N₁ →ₛₗ[(invert (R := R)).toRingEquiv.toRingHom] N₂ →ₗ[R[T;T⁻¹]] R[T;T⁻¹])
    (hε : ε₁⁻¹ = ε₂) :
    LaurentSpecialization ε₁ N₁ →ₗ[R] LaurentSpecialization ε₂ N₂ →ₗ[R] R :=
  (LaurentSpecialization.lift ε₂
    (LaurentSpecialization.lift ε₁ (laurentEvalForm (ε₂ := ε₂) b) (fun x => by
      ext y
      rw [laurentEvalForm_apply, LinearMap.map_smulₛₗ₂]
      simpa [laurentEvalForm_apply, ← hε, smul_eq_mul] using
        mul_comm (laurentEval ε₂ (b x y)) (ε₁ : R))).flip
    (fun y => by
      apply LaurentSpecialization.hom_ext ε₁
      intro x
      simp only [LinearMap.flip_apply, LinearMap.smul_apply, lift_mk, laurentEvalForm_apply]
      rw [map_smul, smul_eq_mul, map_mul, laurentEval_T_one]
      rfl)).flip

/-- **The specialized form is the evaluated form**: on specialized elements its value is the value
of the Laurent form evaluated at `ε₂`. -/
@[simp]
theorem laurentSpecialize_mk_mk
    (b : N₁ →ₛₗ[(invert (R := R)).toRingEquiv.toRingHom] N₂ →ₗ[R[T;T⁻¹]] R[T;T⁻¹])
    (hε : ε₁⁻¹ = ε₂) (x : N₁) (y : N₂) :
    b.laurentSpecialize hε (LaurentSpecialization.mk ε₁ x) (LaurentSpecialization.mk ε₂ y) =
      laurentEval ε₂ (b x y) := by
  simp [laurentSpecialize, LinearMap.flip_apply, laurentEvalForm_apply]

end LinearMap

namespace TauCeti

open scoped Polynomial

/-- **Specialization need not preserve nondegeneracy.**  Over a nontrivial commutative ring `R`,
some two-by-two Laurent-polynomial matrix is nondegenerate while its value at every unit `ε` with
`ε⁻¹ = ε` is degenerate; over `ℤ` these are both specializations `q = 1` and `q = -1`.  The
witness has rows `(1, q)` and `(q, 1)`, with determinant `1 - q²`, a non-zero-divisor. -/
theorem exists_nondegenerate_and_not_nondegenerate_map_laurentEval (R : Type*) [CommRing R]
    [Nontrivial R] :
    ∃ M : Matrix (Fin 2) (Fin 2) R[T;T⁻¹], M.Nondegenerate ∧
      ∀ ε : Rˣ, ε⁻¹ = ε → ¬ (M.map (laurentEval ε)).Nondegenerate := by
  refine ⟨!![1, T 1; T 1, 1], .of_det_mem_nonZeroDivisors ?_, fun ε hε hM => ?_⟩
  · have hmonic : (Polynomial.X ^ 2 - Polynomial.C 1 : R[X]).Monic :=
      Polynomial.monic_X_pow_sub_C 1 two_ne_zero
    have hmem := IsLocalization.map_nonZeroDivisors_le (Submonoid.powers (Polynomial.X : R[X]))
      R[T;T⁻¹] (Submonoid.mem_map_of_mem _ hmonic.mem_nonZeroDivisors)
    rw [algebraMap_eq_toLaurent] at hmem
    have hdet : Matrix.det !![(1 : R[T;T⁻¹]), T 1; T 1, 1] =
        Polynomial.toLaurent (Polynomial.X ^ 2 - Polynomial.C 1 : R[X]) * -1 := by
      simp [Matrix.det_fin_two_of, sq, ← T_add]
    rw [hdet]
    exact mul_mem hmem isUnit_one.neg.mem_nonZeroDivisors
  · have hεε : (ε : R) * ε = 1 := by
      simpa [hε] using Units.inv_mul ε
    have h := hM.separatingRight.eq_zero_of_mulVec_eq_zero (v := ![(ε : R), -1]) (by
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hεε])
    simpa using congrFun h 1

end TauCeti

namespace TauCeti

open LaurentPolynomial Matrix

noncomputable section

/-- A Laurent-polynomial matrix with nonzero determinant that becomes degenerate at `q = 1`. -/
def specializationDegeneracyMatrix : Matrix (Fin 2) (Fin 2) (LaurentPolynomial ℤ) :=
  !![1, 1; 1, T 1]

/-- The determinant of the specialization example is `q - 1`. -/
@[simp]
theorem det_specializationDegeneracyMatrix :
    specializationDegeneracyMatrix.det = T 1 - 1 := by
  simp [specializationDegeneracyMatrix, Matrix.det_fin_two_of]

/-- The determinant of the Laurent-polynomial matrix is nonzero before specialization. -/
theorem det_specializationDegeneracyMatrix_ne_zero :
    specializationDegeneracyMatrix.det ≠ 0 := by
  rw [det_specializationDegeneracyMatrix]
  intro h
  have hc := congrArg (fun p : LaurentPolynomial ℤ => p.coeff 1) h
  have hconst : (1 : LaurentPolynomial ℤ).coeff 1 = 0 := by
    rw [← LaurentPolynomial.T_zero (R := ℤ), LaurentPolynomial.T_apply]
    norm_num
  simp [hconst] at hc

/-- The matrix after evaluation at `q = 1`, with entries in `ℤ`. -/
def specializationDegeneracyMatrixAtOne : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 1; 1, 1]

/-- The specialized matrix is obtained by evaluating every entry of the Laurent matrix at `1`. -/
theorem specializationDegeneracyMatrixAtOne_eq_map :
    specializationDegeneracyMatrixAtOne =
      specializationDegeneracyMatrix.map (laurentEval (R := ℤ) (1 : ℤˣ)).toRingHom := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [specializationDegeneracyMatrixAtOne, specializationDegeneracyMatrix, laurentEval_T]

/-- The specialized matrix has zero determinant. -/
@[simp]
theorem det_specializationDegeneracyMatrixAtOne :
    specializationDegeneracyMatrixAtOne.det = 0 := by
  simp [specializationDegeneracyMatrixAtOne, Matrix.det_fin_two_of]

/-- A nonzero kernel vector for the Laurent matrix specialized at `q = 1`. -/
def specializationDegeneracyKernelVector : Fin 2 → ℤ :=
  ![1, -1]

/-- The vector `(1, -1)` witnesses degeneracy of the matrix at `q = 1`. -/
theorem specializationDegeneracyMatrixAtOne_mulVec_eq_zero :
    specializationDegeneracyMatrixAtOne *ᵥ specializationDegeneracyKernelVector = 0 := by
  ext i
  fin_cases i <;>
    simp [specializationDegeneracyMatrixAtOne, specializationDegeneracyKernelVector, Matrix.mulVec]

/-- The specialization kernel vector is nonzero. -/
theorem specializationDegeneracyKernelVector_ne_zero :
    specializationDegeneracyKernelVector ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [specializationDegeneracyKernelVector] at h0

end

end TauCeti
