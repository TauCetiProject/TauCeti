/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import TauCeti.Algebra.Algebra.Frobenius.Basic
public import TauCeti.Algebra.Algebra.Frobenius.Graded
public import TauCeti.Algebra.DualNumber.Grading
public import TauCeti.Algebra.DualNumber.Trace

/-!
# Frobenius algebra structure on the dual numbers

This file instantiates the trace-reconstructed Frobenius coalgebra, handle element, and
even-supported grading theory on the dual numbers `R[ε]` over a commutative semiring `R`.

## Main results

* `TauCeti.bilinForm_toMatrix_compr₂_mul_smul_sndHom`,
  `TauCeti.bilinForm_toMatrix_dualNumberTracePairing`,
  `TauCeti.det_bilinForm_toMatrix_compr₂_mul_smul_sndHom`: `c • TrivSqZeroExt.sndHom R R` has
  pairing matrix `!![0, c; c, 0]` (determinant `-c ^ 2`).
* `TauCeti.isPerfPair_compr₂_mul_smul_sndHom_iff`,
  `TauCeti.isFrobeniusFunctional_smul_sndHom_iff`,
  `TauCeti.isFrobeniusFunctional_two_smul_sndHom_int`,
  `TauCeti.not_isPerfPair_compr₂_mul_two_smul_sndHom_int`: unit vs regularity criteria and the
  explicit `2 • sndHom` separation over `ℤ`.
* `TauCeti.traceDualBasis_sndHom_dualNumberBasis`, `TauCeti.frobeniusCoalgebra_sndHom_comul_one`,
  `TauCeti.frobeniusCoalgebra_sndHom_comul_eps`, `TauCeti.handleElement_frobeniusCoalgebra_sndHom`,
  `TauCeti.sndHom_handleElement_frobeniusCoalgebra_sndHom`,
  `TauCeti.handleElement_frobeniusCoalgebra_sndHom_sq`: trace-reconstructed coproduct and handle
  identities.
* `TauCeti.isHomogeneous_frobeniusCoalgebra_sndHom_comul`,
  `TauCeti.handleElement_frobeniusCoalgebra_sndHom_mem_grade`: degree compatibility of the
  reconstructed comultiplication and handle element with `TauCeti.dualNumberIntegerGrade`.

## References

* J. Kock, *Frobenius Algebras and 2D Topological Quantum Field Theories*, Chapter 2.
* Goertz–Marino–Wedrich, *Monoidal 2-categories from foam evaluation*, arXiv:2602.11120v1,
  Example 2.9.
-/

public section

open scoped DualNumber Matrix TensorProduct

namespace TauCeti

section Pairing

variable (R : Type*) [CommSemiring R]

/-- The matrix of the scaled trace pairing `(x, y) ↦ c * (x * y).snd` in the basis `(1, ε)` is
`!![0, c; c, 0]`. -/
theorem bilinForm_toMatrix_compr₂_mul_smul_sndHom (c : R) :
    LinearMap.BilinForm.toMatrix (dualNumberBasis R)
        ((LinearMap.mul R R[ε]).compr₂ (c • TrivSqZeroExt.sndHom R R)) =
      !![0, c; c, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.BilinForm.toMatrix_apply]

/-- The matrix of `TauCeti.dualNumberTracePairing R` in the basis `(1, ε)` is `!![0, 1; 1, 0]`. -/
theorem bilinForm_toMatrix_dualNumberTracePairing :
    LinearMap.BilinForm.toMatrix (dualNumberBasis R) (dualNumberTracePairing R) =
      !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.BilinForm.toMatrix_apply]

/-- The scaled trace pairing `(x, y) ↦ c * (x * y).snd` on `R[ε]` is perfect if and only if
`c` is a unit in `R`. -/
theorem isPerfPair_compr₂_mul_smul_sndHom_iff (c : R) :
    ((LinearMap.mul R R[ε]).compr₂ (c • TrivSqZeroExt.sndHom R R)).IsPerfPair ↔
      IsUnit c := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h.bijective_left.surjective (TrivSqZeroExt.sndHom R R)
    have hε := LinearMap.congr_fun hx (DualNumber.eps : R[ε])
    exact isUnit_iff_exists_inv.mpr ⟨x.fst, by simpa using hε⟩
  · rintro ⟨u, rfl⟩
    have hcomp :
        (LinearMap.mul R R[ε]).compr₂ ((u : R) • TrivSqZeroExt.sndHom R R) =
          ((LinearMap.mul R R[ε]).compr₂ (TrivSqZeroExt.sndHom R R)).compl₁₂
            (LinearEquiv.smulOfUnit (R := R) (M := R[ε]) u).toLinearMap
            (LinearEquiv.refl R R[ε]).toLinearMap := by
      ext x y
      simp [LinearEquiv.smulOfUnit, Units.smul_def, smul_eq_mul]
    rw [hcomp]
    exact LinearMap.IsPerfPair.compl₁₂
      (p := (LinearMap.mul R R[ε]).compr₂ (TrivSqZeroExt.sndHom R R))
      (LinearEquiv.smulOfUnit u) (LinearEquiv.refl R R[ε])

/-- Over a commutative semiring `R`, the scaled trace `c • TrivSqZeroExt.sndHom R R` is a
Frobenius functional if and only if multiplication by `c` has trivial kernel. -/
theorem isFrobeniusFunctional_smul_sndHom_iff_mul_eq_zero (c : R) :
    (c • TrivSqZeroExt.sndHom R R).IsFrobeniusFunctional ↔ ∀ r : R, c * r = 0 → r = 0 := by
  rw [LinearMap.isFrobeniusFunctional_iff]
  constructor
  · intro h r hr
    have h0 : TrivSqZeroExt.inl r = (0 : R[ε]) := h.1 (TrivSqZeroExt.inl r) fun b ↦ by
      simp [smul_eq_mul, ← mul_assoc, hr]
    simpa using congrArg TrivSqZeroExt.fst h0
  · intro hc
    have hleft : ∀ a : R[ε], (∀ b : R[ε], (c • TrivSqZeroExt.sndHom R R) (a * b) = 0) → a = 0 := by
      intro a ha
      have hε := ha (DualNumber.eps : R[ε])
      have h1 := ha (1 : R[ε])
      exact TrivSqZeroExt.ext (hc a.fst (by simpa using hε)) (hc a.snd (by simpa using h1))
    exact ⟨hleft, fun b hb ↦ hleft b fun a ↦ by rw [mul_comm]; exact hb a⟩

end Pairing

section CommRingPairing

variable (R : Type*) [CommRing R]

/-- Over a commutative ring `R`, the pairing matrix of `c • TrivSqZeroExt.sndHom R R` in the basis
`(1, ε)` has determinant `-(c ^ 2)`. -/
theorem det_bilinForm_toMatrix_compr₂_mul_smul_sndHom (c : R) :
    (LinearMap.BilinForm.toMatrix (dualNumberBasis R)
        ((LinearMap.mul R R[ε]).compr₂ (c • TrivSqZeroExt.sndHom R R))).det = -(c ^ 2) := by
  rw [bilinForm_toMatrix_compr₂_mul_smul_sndHom, Matrix.det_fin_two]
  simp [sq]

/-- Over a commutative ring `R`, `c • TrivSqZeroExt.sndHom R R` is a Frobenius functional if and
only if `c` is regular. -/
theorem isFrobeniusFunctional_smul_sndHom_iff (c : R) :
    (c • TrivSqZeroExt.sndHom R R).IsFrobeniusFunctional ↔ IsRegular c := by
  rw [isFrobeniusFunctional_smul_sndHom_iff_mul_eq_zero, Commute.isRegular_iff (Commute.all c),
    isLeftRegular_iff_right_eq_zero_of_mul]

/-- Over `ℤ`, the pairing matrix of `2 • TrivSqZeroExt.sndHom ℤ ℤ` in `(1, ε)` has
determinant `-4`. -/
theorem det_bilinForm_toMatrix_two_smul_sndHom_int :
    (LinearMap.BilinForm.toMatrix (dualNumberBasis ℤ)
        ((LinearMap.mul ℤ ℤ[ε]).compr₂ ((2 : ℤ) • TrivSqZeroExt.sndHom ℤ ℤ))).det = -4 := by
  rw [det_bilinForm_toMatrix_compr₂_mul_smul_sndHom]
  norm_num

/-- Over `ℤ`, `2 • TrivSqZeroExt.sndHom ℤ ℤ` is a Frobenius functional (nondegenerate). -/
theorem isFrobeniusFunctional_two_smul_sndHom_int :
    ((2 : ℤ) • TrivSqZeroExt.sndHom ℤ ℤ).IsFrobeniusFunctional :=
  (isFrobeniusFunctional_smul_sndHom_iff ℤ 2).mpr
    ⟨mul_right_injective₀ (by decide), mul_left_injective₀ (by decide)⟩

/-- Over `ℤ`, the trace pairing of `2 • TrivSqZeroExt.sndHom ℤ ℤ` is not perfect, showing
that nondegeneracy does not imply perfectness over a general commutative ring. -/
theorem not_isPerfPair_compr₂_mul_two_smul_sndHom_int :
    ¬((LinearMap.mul ℤ ℤ[ε]).compr₂ ((2 : ℤ) • TrivSqZeroExt.sndHom ℤ ℤ)).IsPerfPair := by
  rw [isPerfPair_compr₂_mul_smul_sndHom_iff, Int.isUnit_iff]
  decide

end CommRingPairing

section CoalgebraAndHandle

variable (R : Type*) [CommSemiring R]

/-- The trace-dual basis of `(1, ε)` with respect to `TrivSqZeroExt.sndHom R R` is `(ε, 1)`. -/
@[simp]
theorem traceDualBasis_sndHom_dualNumberBasis (i : Fin 2) :
    LinearMap.traceDualBasis (TrivSqZeroExt.sndHom R R) (dualNumberBasis R) i =
      dualNumberBasis R i.rev := by
  apply ((LinearMap.mul R R[ε]).compr₂ (TrivSqZeroExt.sndHom R R)).toPerfPair.injective
  refine dualNumber_linearMap_ext ?_ ?_ <;>
    simp only [LinearMap.toPerfPair_apply, LinearMap.compr₂_apply, LinearMap.mul_apply_apply,
      LinearMap.traceDualBasis_mul] <;>
    fin_cases i <;> simp

/-- The trace-reconstructed comultiplication on `R[ε]` sends `1` to `1 ⊗ ε + ε ⊗ 1`. -/
@[simp]
theorem frobeniusCoalgebra_sndHom_comul_one :
    (TrivSqZeroExt.sndHom R R).frobeniusCoalgebra.comul (1 : R[ε]) =
      (1 : R[ε]) ⊗ₜ[R] DualNumber.eps + DualNumber.eps ⊗ₜ[R] (1 : R[ε]) := by
  rw [LinearMap.frobeniusCoalgebra_comul_eq_sum (TrivSqZeroExt.sndHom R R) (dualNumberBasis R) 1]
  simp [Fin.sum_univ_two]

/-- The trace-reconstructed comultiplication on `R[ε]` sends `ε` to `ε ⊗ ε`. -/
@[simp]
theorem frobeniusCoalgebra_sndHom_comul_eps :
    (TrivSqZeroExt.sndHom R R).frobeniusCoalgebra.comul (DualNumber.eps : R[ε]) =
      DualNumber.eps ⊗ₜ[R] DualNumber.eps := by
  rw [LinearMap.frobeniusCoalgebra_comul_eq_sum (TrivSqZeroExt.sndHom R R) (dualNumberBasis R)
    DualNumber.eps]
  simp [Fin.sum_univ_two]

/-- The handle element of the trace-reconstructed Frobenius algebra `R[ε]` is `2 * ε`. -/
@[simp]
theorem handleElement_frobeniusCoalgebra_sndHom :
    letI := (TrivSqZeroExt.sndHom R R).frobeniusCoalgebra
    TauCeti.Coalgebra.handleElement R R[ε] = 2 * DualNumber.eps := by
  let := (TrivSqZeroExt.sndHom R R).frobeniusCoalgebra
  rw [LinearMap.handleElement_frobeniusCoalgebra_eq_sum (TrivSqZeroExt.sndHom R R)
    (dualNumberBasis R)]
  simp [Fin.sum_univ_two, two_mul]

/-- The canonical trace evaluates the handle element of `R[ε]` to `2`. -/
theorem sndHom_handleElement_frobeniusCoalgebra_sndHom :
    letI := (TrivSqZeroExt.sndHom R R).frobeniusCoalgebra
    TrivSqZeroExt.sndHom R R (TauCeti.Coalgebra.handleElement R R[ε]) = 2 := by
  let := (TrivSqZeroExt.sndHom R R).frobeniusCoalgebra
  simp [two_mul, one_add_one_eq_two]

/-- The handle element of the trace-reconstructed Frobenius algebra `R[ε]` squares to zero. -/
theorem handleElement_frobeniusCoalgebra_sndHom_sq :
    letI := (TrivSqZeroExt.sndHom R R).frobeniusCoalgebra
    TauCeti.Coalgebra.handleElement R R[ε] ^ 2 = 0 := by
  let := (TrivSqZeroExt.sndHom R R).frobeniusCoalgebra
  simp [sq, mul_assoc, mul_left_comm]

end CoalgebraAndHandle

section Graded

variable (R : Type*) [CommSemiring R]

/-- With `deg ε = 2`, the trace-reconstructed comultiplication on `R[ε]` is homogeneous of degree
`2`. -/
theorem isHomogeneous_frobeniusCoalgebra_sndHom_comul :
    letI := dualNumberIntegerGradedAlgebra R
    TauCeti.LinearMap.IsHomogeneous (TrivSqZeroExt.sndHom R R).frobeniusCoalgebra.comul
      (dualNumberIntegerGrade R)
      ((InternalGrading.ofDecomposition (dualNumberIntegerGrade R)).tensorProduct
        (InternalGrading.ofDecomposition (dualNumberIntegerGrade R))).piece 2 := by
  let := dualNumberIntegerGradedAlgebra R
  exact LinearMap.isHomogeneous_frobeniusCoalgebra_comul (dualNumberIntegerGrade R)
    (TrivSqZeroExt.sndHom R R) (isHomogeneous_sndHom_dualNumberIntegerGrade R)

/-- With `deg ε = 2`, the handle element of `R[ε]` lies in degree `2`. -/
theorem handleElement_frobeniusCoalgebra_sndHom_mem_grade :
    letI := (TrivSqZeroExt.sndHom R R).frobeniusCoalgebra
    TauCeti.Coalgebra.handleElement R R[ε] ∈ dualNumberIntegerGrade R 2 := by
  let := (TrivSqZeroExt.sndHom R R).frobeniusCoalgebra
  rw [handleElement_frobeniusCoalgebra_sndHom, two_mul]
  exact (dualNumberIntegerGrade R 2).add_mem
    (eps_mem_dualNumberIntegerGrade_two R) (eps_mem_dualNumberIntegerGrade_two R)

end Graded

end TauCeti
