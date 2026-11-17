/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Frobenius.Basic
public import TauCeti.Algebra.Algebra.Frobenius.Graded
public import TauCeti.Algebra.DualNumber.Grading
public import TauCeti.Algebra.DualNumber.Trace
public import TauCeti.LinearAlgebra.PerfectPairing.Basis
import Mathlib.LinearAlgebra.Determinant

/-!
# Frobenius algebra reconstruction and grading on the dual numbers

For any commutative semiring `R`, the infinitesimal coordinate `TrivSqZeroExt.sndHom R R` on
`DualNumber R` defines the perfect Frobenius trace pairing `TauCeti.dualNumberTracePairing R`.
This file records the trace-reconstructed Frobenius coalgebra, Gram matrices, handle element,
scaled-trace criteria, and graded Frobenius properties on `DualNumber R`:

* In the basis `(1, ε)`, the Gram matrix of `dualNumberTracePairing R` is `!![0, 1; 1, 0]`, the
  trace-dual basis is `(ε, 1)`, the reconstructed coproduct satisfies
  `Δ 1 = 1 ⊗ ε + ε ⊗ 1` and `Δ ε = ε ⊗ ε`, and the handle element `h = m (Δ 1)` satisfies
  `h = 2 • ε`, `sndHom h = 2`, and `h ^ 2 = 0`.
* Scaling `sndHom` by `c : R` gives Gram matrix `!![0, c; c, 0]` of determinant `-(c ^ 2)`. Over a
  commutative semiring, `c • sndHom R R` is a Frobenius functional (hence symmetric) if and only if
  left multiplication by `c` has trivial kernel, whereas over a commutative ring its multiplication
  pairing is perfect if and only if `IsUnit c` (see
  `TauCeti.Examples.Algebra.DualNumber.Frobenius` for the `2 • sndHom ℤ ℤ` counterexample).
* With the standard integer grading `dualNumberIntegerGrade R` (`deg 1 = 0`, `deg ε = 2`), the
  reconstructed coproduct `Δ` has degree `2` and the handle element lies in degree `2`.

## Main definitions and results

* `TauCeti.toMatrix₂_dualNumberTracePairing`, `TauCeti.traceDualBasis_sndHom_zero`,
  `TauCeti.traceDualBasis_sndHom_one`, `TauCeti.frobeniusCoalgebra_sndHom_comul_one`,
  `TauCeti.frobeniusCoalgebra_sndHom_comul_eps`, `TauCeti.frobeniusCoalgebra_sndHom_handle`:
  Gram matrix, trace-dual basis, reconstructed coproduct, and handle element.
* `TauCeti.isFrobeniusFunctional_smul_sndHom_iff`,
  `TauCeti.isSymmetricFrobeniusFunctional_smul_sndHom`,
  `TauCeti.isPerfPair_compr₂_mul_smul_sndHom_iff`: nondegeneracy vs perfectness of scaled traces.
* `TauCeti.isHomogeneous_frobeniusCoalgebra_sndHom_comul`,
  `TauCeti.frobeniusCoalgebra_sndHom_handle_mem_dualNumberIntegerGrade_two`: degree-`2` homogeneity
  of the reconstructed coproduct and handle element.
-/

public section

noncomputable section

open TensorProduct DualNumber TrivSqZeroExt Matrix

namespace TauCeti

section CommSemiring

variable (R : Type*) [CommSemiring R]

/-- In the basis `(1, ε)`, the Gram matrix of `dualNumberTracePairing R` is `!![0, 1; 1, 0]`. -/
theorem toMatrix₂_dualNumberTracePairing :
    LinearMap.toMatrix₂ (dualNumberBasis R) (dualNumberBasis R) (dualNumberTracePairing R) =
      !![(0 : R), 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix₂_apply]

/-- In the basis `(1, ε)`, the Gram matrix of `c • sndHom R R` is `!![0, c; c, 0]`. -/
theorem toMatrix₂_compr₂_mul_smul_sndHom (c : R) :
    LinearMap.toMatrix₂ (dualNumberBasis R) (dualNumberBasis R)
      ((LinearMap.mul R (DualNumber R)).compr₂ (c • sndHom R R)) = !![(0 : R), c; c, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix₂_apply]

/-- The scaled coordinate `c • sndHom R R` is a Frobenius functional on `DualNumber R` if and only
if left multiplication by `c` on `R` has trivial kernel. -/
theorem isFrobeniusFunctional_smul_sndHom_iff {c : R} :
    (c • sndHom R R).IsFrobeniusFunctional ↔ ∀ x : R, c * x = 0 → x = 0 := by
  rw [LinearMap.isFrobeniusFunctional_iff]
  refine ⟨fun ⟨hleft, _⟩ x hcx ↦ ?_, fun hc ↦ ?_⟩
  · have ha : inr x = (0 : DualNumber R) := hleft (inr x) fun b ↦ by
      simp [smul_eq_mul, ← mul_assoc, hcx]
    simpa using congrArg TrivSqZeroExt.snd ha
  · have hleft (a : DualNumber R) (ha : ∀ b, (c • sndHom R R) (a * b) = 0) : a = 0 := by
      have hsnd : a.snd = 0 := hc a.snd (by simpa [smul_eq_mul] using ha 1)
      have hfst : a.fst = 0 := hc a.fst (by simpa [smul_eq_mul] using ha eps)
      exact TrivSqZeroExt.ext hfst hsnd
    exact ⟨hleft, fun b hb ↦ hleft b fun a ↦ by simpa [mul_comm] using hb a⟩

/-- If left multiplication by `c : R` is torsion-free, then `c • sndHom R R` is a symmetric
Frobenius functional on `DualNumber R`. -/
theorem isSymmetricFrobeniusFunctional_smul_sndHom {c : R} (hc : ∀ x : R, c * x = 0 → x = 0) :
    (c • sndHom R R).IsSymmetricFrobeniusFunctional :=
  ((isFrobeniusFunctional_smul_sndHom_iff R).mpr hc).isSymmetric

/-- The first vector of the `sndHom`-dual basis of `(1, ε)` is `ε`. -/
@[simp] theorem traceDualBasis_sndHom_zero :
    (sndHom R R).traceDualBasis (dualNumberBasis R) 0 = (eps : DualNumber R) := by
  apply ((LinearMap.mul R (DualNumber R)).compr₂ (sndHom R R)).toPerfPair.injective
  refine (dualNumberBasis R).ext fun j ↦ ?_
  simp only [LinearMap.toLinearMap_toPerfPair, LinearMap.compr₂_apply, LinearMap.mul_apply_apply,
    LinearMap.traceDualBasis_mul]
  fin_cases j <;> simp

/-- The second vector of the `sndHom`-dual basis of `(1, ε)` is `1`. -/
@[simp] theorem traceDualBasis_sndHom_one :
    (sndHom R R).traceDualBasis (dualNumberBasis R) 1 = (1 : DualNumber R) := by
  apply ((LinearMap.mul R (DualNumber R)).compr₂ (sndHom R R)).toPerfPair.injective
  refine (dualNumberBasis R).ext fun j ↦ ?_
  simp only [LinearMap.toLinearMap_toPerfPair, LinearMap.compr₂_apply, LinearMap.mul_apply_apply,
    LinearMap.traceDualBasis_mul]
  fin_cases j <;> simp

/-- The coproduct on `1` reconstructed from `sndHom R R` is `1 ⊗ ε + ε ⊗ 1`. -/
@[simp] theorem frobeniusCoalgebra_sndHom_comul_one :
    ((sndHom R R).frobeniusCoalgebra).comul (1 : DualNumber R) =
      (1 : DualNumber R) ⊗ₜ[R] eps + eps ⊗ₜ[R] 1 := by
  rw [LinearMap.frobeniusCoalgebra_comul_one_eq_sum (sndHom R R) (dualNumberBasis R),
    Fin.sum_univ_two]
  simp

/-- The coproduct on `ε` reconstructed from `sndHom R R` is `ε ⊗ ε`. -/
@[simp] theorem frobeniusCoalgebra_sndHom_comul_eps :
    ((sndHom R R).frobeniusCoalgebra).comul (eps : DualNumber R) =
      (eps : DualNumber R) ⊗ₜ[R] eps := by
  rw [LinearMap.frobeniusCoalgebra_comul_eq_sum (sndHom R R) (dualNumberBasis R),
    Fin.sum_univ_two]
  simp

/-- The handle element of `(sndHom R R).frobeniusCoalgebra` is `2 • ε`. -/
@[simp] theorem frobeniusCoalgebra_sndHom_handle :
    (letI := (sndHom R R).frobeniusCoalgebra; TauCeti.Coalgebra.handle R (DualNumber R)) =
      (2 : R) • (eps : DualNumber R) := by
  rw [LinearMap.frobeniusCoalgebra_handle_eq_sum (sndHom R R) (dualNumberBasis R),
    Fin.sum_univ_two, two_smul]
  simp

/-- Evaluating `sndHom R R` on the handle element gives `2`. -/
theorem sndHom_frobeniusCoalgebra_handle :
    sndHom R R (letI := (sndHom R R).frobeniusCoalgebra;
      TauCeti.Coalgebra.handle R (DualNumber R)) = 2 := by
  simp

/-- The handle element of `(sndHom R R).frobeniusCoalgebra` squares to `0`. -/
theorem frobeniusCoalgebra_sndHom_handle_sq :
    (letI := (sndHom R R).frobeniusCoalgebra; TauCeti.Coalgebra.handle R (DualNumber R)) ^ 2 =
      0 := by
  simp [sq, smul_mul_smul_comm]

/-- The reconstructed Frobenius coproduct on `DualNumber R` is homogeneous of degree `2`. -/
theorem isHomogeneous_frobeniusCoalgebra_sndHom_comul :
    LinearMap.IsHomogeneous ((sndHom R R).frobeniusCoalgebra).comul
      (dualNumberIntegerGrade R)
      ((dualNumberInternalGrading R).tensorProduct (dualNumberInternalGrading R)).piece 2 := by
  simpa using LinearMap.isHomogeneous_frobeniusCoalgebra_comul (dualNumberInternalGrading R)
    (sndHom R R) (by simpa using isHomogeneous_sndHom R)

/-- The reconstructed handle element on `DualNumber R` lies in integer degree `2`. -/
theorem frobeniusCoalgebra_sndHom_handle_mem_dualNumberIntegerGrade_two :
    (letI := (sndHom R R).frobeniusCoalgebra; TauCeti.Coalgebra.handle R (DualNumber R)) ∈
      dualNumberIntegerGrade R 2 := by
  simpa using LinearMap.frobeniusCoalgebra_handle_mem_piece (dualNumberInternalGrading R)
    (sndHom R R) (by simpa using isHomogeneous_sndHom R)

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

/-- Over a commutative ring, the Gram determinant of `c • sndHom R R` in `(1, ε)` is `-(c ^ 2)`. -/
theorem det_toMatrix₂_compr₂_mul_smul_sndHom (c : R) :
    (LinearMap.toMatrix₂ (dualNumberBasis R) (dualNumberBasis R)
      ((LinearMap.mul R (DualNumber R)).compr₂ (c • sndHom R R))).det = -(c ^ 2) := by
  rw [toMatrix₂_compr₂_mul_smul_sndHom, det_fin_two_of]
  ring

/-- Over a commutative ring, the multiplication pairing of `c • sndHom R R` on `DualNumber R` is
perfect if and only if `c` is a unit. -/
theorem isPerfPair_compr₂_mul_smul_sndHom_iff (c : R) :
    ((LinearMap.mul R (DualNumber R)).compr₂ (c • sndHom R R)).IsPerfPair ↔ IsUnit c := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hdet := (dualNumberBasis R).isUnit_det_of_isPerfPair (dualNumberBasis R) _ h
    rw [det_toMatrix₂_compr₂_mul_smul_sndHom, IsUnit.neg_iff, sq, IsUnit.mul_iff, and_self] at hdet
    exact hdet
  · refine (dualNumberBasis R).isPerfPair_of_isUnit_det (dualNumberBasis R) _ ?_
    rw [det_toMatrix₂_compr₂_mul_smul_sndHom, IsUnit.neg_iff]
    exact h.pow 2

end CommRing

end TauCeti

end
