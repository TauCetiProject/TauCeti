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
scaled-trace counterexample over `ℤ`, and even-supported degree-`2` grading on `DualNumber R`:

* In the basis `(1, ε)`, the Gram matrix of `dualNumberTracePairing R` is `!![0, 1; 1, 0]`, the
  trace-dual basis is `(ε, 1)`, the reconstructed coproduct satisfies
  `Δ 1 = 1 ⊗ ε + ε ⊗ 1` and `Δ ε = ε ⊗ ε`, and the handle element `h = m (Δ 1)` satisfies
  `h = 2 • ε`, `sndHom h = 2`, and `h ^ 2 = 0`.
* Scaling `sndHom` by `c : R` gives Gram matrix `!![0, c; c, 0]` of determinant `-(c ^ 2)`. Over a
  commutative ring, the scaled pairing is perfect if and only if `IsUnit c`, whereas every
  non-zero-divisor `c` defines a symmetric Frobenius functional. In particular, `2 • sndHom ℤ ℤ` on
  `DualNumber ℤ` has Gram determinant `-4` and is a nondegenerate symmetric Frobenius functional
  whose multiplication pairing is not perfect.
* With the standard integer grading `dualNumberIntegerGrade R` (`deg 1 = 0`, `deg ε = 2`), the
  grading is supported in even degrees, `sndHom` has degree `-2`, the reconstructed coproduct `Δ`
  has degree `2`, and the handle element lies in degree `2`.

## Main definitions and results

* `TauCeti.dualNumberModuleFree`, `TauCeti.isPerfPair_compr₂_mul_sndHom`: free-module and unfolded
  perfect-pairing instances on `DualNumber R`.
* `TauCeti.toMatrix₂_dualNumberTracePairing`, `TauCeti.traceDualBasis_sndHom_zero`,
  `TauCeti.traceDualBasis_sndHom_one`, `TauCeti.frobeniusCoalgebra_sndHom_comul_one`,
  `TauCeti.frobeniusCoalgebra_sndHom_comul_eps`, `TauCeti.frobeniusCoalgebra_sndHom_handle`:
  Gram matrix, trace-dual basis, reconstructed coproduct, and handle element.
* `TauCeti.isPerfPair_compr₂_mul_smul_sndHom_iff`,
  `TauCeti.isSymmetricFrobeniusFunctional_two_smul_sndHom_int`,
  `TauCeti.not_isPerfPair_compr₂_mul_two_smul_sndHom_int`: perfectness vs nondegeneracy of scaled
  traces.
* `TauCeti.dualNumberInternalGrading`, `TauCeti.parityGrading_dualNumberIntegerGrade_one`,
  `TauCeti.isHomogeneous_sndHom`, `TauCeti.isHomogeneous_frobeniusCoalgebra_sndHom_comul`:
  even-supported degree-`2` grading and homogeneity of `sndHom` and `Δ`.
-/

public section

noncomputable section

open TensorProduct DualNumber TrivSqZeroExt Matrix

namespace TauCeti

section CommSemiring

variable (R : Type*) [CommSemiring R]

/-- The dual numbers are a free `R`-module of rank two on the basis `1, ε`. -/
instance dualNumberModuleFree : Module.Free R (DualNumber R) :=
  Module.Free.of_basis (dualNumberBasis R)

/-- The multiplication pairing of `sndHom R R` equals `dualNumberTracePairing R`. -/
theorem compr₂_mul_sndHom_eq_dualNumberTracePairing :
    (LinearMap.mul R (DualNumber R)).compr₂ (sndHom R R) = dualNumberTracePairing R := by
  ext x y
  simp

/-- Unfolded perfect-pairing instance for `(LinearMap.mul R (DualNumber R)).compr₂ (sndHom R R)`. -/
instance isPerfPair_compr₂_mul_sndHom :
    ((LinearMap.mul R (DualNumber R)).compr₂ (sndHom R R)).IsPerfPair := by
  rw [compr₂_mul_sndHom_eq_dualNumberTracePairing]
  infer_instance

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

/-- If left multiplication by `c : R` is torsion-free, then `c • sndHom R R` is a symmetric
Frobenius functional on `DualNumber R`. -/
theorem isSymmetricFrobeniusFunctional_smul_sndHom {c : R} (hc : ∀ x : R, c * x = 0 → x = 0) :
    (c • sndHom R R).IsSymmetricFrobeniusFunctional where
  isFrobeniusFunctional := by
    rw [LinearMap.isFrobeniusFunctional_iff]
    have hleft (a : DualNumber R) (ha : ∀ b, (c • sndHom R R) (a * b) = 0) : a = 0 := by
      have hsnd : a.snd = 0 := hc a.snd (by simpa [smul_eq_mul] using ha 1)
      have hfst : a.fst = 0 := hc a.fst (by simpa [smul_eq_mul] using ha eps)
      exact TrivSqZeroExt.ext hfst hsnd
    exact ⟨hleft, fun b hb ↦ hleft b fun a ↦ by simpa [mul_comm] using hb a⟩
  apply_mul_comm a b := by simp [mul_comm]

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
theorem frobeniusCoalgebra_sndHom_handle :
    (letI := (sndHom R R).frobeniusCoalgebra; Coalgebra.handle R (DualNumber R)) =
      (2 : R) • (eps : DualNumber R) := by
  rw [LinearMap.frobeniusCoalgebra_handle_eq_sum (sndHom R R) (dualNumberBasis R),
    Fin.sum_univ_two, two_smul]
  simp

/-- Evaluating `sndHom R R` on the handle element gives `2`. -/
theorem sndHom_frobeniusCoalgebra_handle :
    sndHom R R (letI := (sndHom R R).frobeniusCoalgebra;
      Coalgebra.handle R (DualNumber R)) = 2 := by
  rw [frobeniusCoalgebra_sndHom_handle]
  simp

/-- The handle element of `(sndHom R R).frobeniusCoalgebra` squares to `0`. -/
@[simp] theorem frobeniusCoalgebra_sndHom_handle_sq :
    (letI := (sndHom R R).frobeniusCoalgebra; Coalgebra.handle R (DualNumber R)) ^ 2 = 0 := by
  rw [frobeniusCoalgebra_sndHom_handle, sq, smul_mul_smul_comm, eps_mul_eps, smul_zero]

/-! ### Even-supported degree-two grading -/

/-- The standard degree-two integer grading on `DualNumber R` packaged as an `InternalGrading`. -/
def dualNumberInternalGrading : InternalGrading R (DualNumber R) ℤ where
  piece := dualNumberIntegerGrade R
  isInternal :=
    letI := dualNumberIntegerGradedAlgebra R
    DirectSum.Decomposition.isInternal _

@[simp] theorem dualNumberInternalGrading_piece :
    (dualNumberInternalGrading R).piece = dualNumberIntegerGrade R := (rfl)

/-- Graded-monoid instance on `(dualNumberInternalGrading R).piece`. -/
instance instGradedMonoidDualNumberInternalGrading :
    SetLike.GradedMonoid (dualNumberInternalGrading R).piece :=
  letI := dualNumberIntegerGradedAlgebra R
  inferInstanceAs (SetLike.GradedMonoid (dualNumberIntegerGrade R))

/-- The degree-two integer grading on `DualNumber R` is supported in even degrees. -/
theorem parityGrading_dualNumberIntegerGrade_one :
    parityGrading (dualNumberIntegerGrade R) 1 = ⊥ := by
  rw [parityGrading_one_eq_bot_iff]
  intro k
  by_cases hk : 2 * k + 1 < 0
  · exact dualNumberIntegerGrade_eq_bot_of_neg R hk
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, 2 * k + 1 = n := Int.eq_ofNat_of_zero_le (by omega)
    rw [hn, dualNumberIntegerGrade_ofNat]
    exact dualNumberGrade_eq_bot R (by omega) (by omega)

/-- With `deg 1 = 0` and `deg ε = 2`, the trace `sndHom R R` is homogeneous of degree `-2`. -/
theorem isHomogeneous_sndHom :
    LinearMap.IsHomogeneous (sndHom R R) (dualNumberIntegerGrade R) (trivialGrading R R) (-2) := by
  rw [← dualNumberInternalGrading_piece,
    (dualNumberInternalGrading R).isHomogeneous_trivialGrading_iff_mem_dualPiece,
    InternalGrading.mem_dualPiece_iff]
  intro q x hx hq
  by_cases hqneg : q < 0
  · rw [dualNumberInternalGrading_piece, dualNumberIntegerGrade_eq_bot_of_neg R hqneg,
      Submodule.mem_bot] at hx
    simp [hx]
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = n := Int.eq_ofNat_of_zero_le (by omega)
    rw [dualNumberInternalGrading_piece, dualNumberIntegerGrade_ofNat] at hx
    rcases eq_or_ne n 0 with rfl | hn0
    · exact (mem_dualNumberGrade_zero R).mp hx
    · have hn2 : n ≠ 2 := by omega
      rw [dualNumberGrade_eq_bot R hn0 hn2, Submodule.mem_bot] at hx
      simp [hx]

/-- The reconstructed Frobenius coproduct on `DualNumber R` is homogeneous of degree `2`. -/
theorem isHomogeneous_frobeniusCoalgebra_sndHom_comul :
    LinearMap.IsHomogeneous ((sndHom R R).frobeniusCoalgebra).comul
      (dualNumberIntegerGrade R)
      ((dualNumberInternalGrading R).tensorProduct (dualNumberInternalGrading R)).piece 2 :=
  LinearMap.isHomogeneous_frobeniusCoalgebra_comul (dualNumberInternalGrading R) (sndHom R R)
    (isHomogeneous_sndHom R)

/-- The reconstructed handle element on `DualNumber R` lies in integer degree `2`. -/
theorem frobeniusCoalgebra_sndHom_handle_mem_dualNumberIntegerGrade_two :
    (letI := (sndHom R R).frobeniusCoalgebra; Coalgebra.handle R (DualNumber R)) ∈
      dualNumberIntegerGrade R 2 :=
  LinearMap.frobeniusCoalgebra_handle_mem_piece (dualNumberInternalGrading R) (sndHom R R)
    (isHomogeneous_sndHom R)

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

/-- On `DualNumber ℤ`, the Gram matrix of `(2 : ℤ) • sndHom ℤ ℤ` in `(1, ε)` has determinant
`-4`. -/
theorem det_toMatrix₂_compr₂_mul_two_smul_sndHom_int :
    (LinearMap.toMatrix₂ (dualNumberBasis ℤ) (dualNumberBasis ℤ)
      ((LinearMap.mul ℤ (DualNumber ℤ)).compr₂ ((2 : ℤ) • sndHom ℤ ℤ))).det = -4 := by
  rw [det_toMatrix₂_compr₂_mul_smul_sndHom]
  norm_num

/-- On `DualNumber ℤ`, `(2 : ℤ) • sndHom ℤ ℤ` is a symmetric Frobenius functional. -/
theorem isSymmetricFrobeniusFunctional_two_smul_sndHom_int :
    ((2 : ℤ) • sndHom ℤ ℤ).IsSymmetricFrobeniusFunctional :=
  isSymmetricFrobeniusFunctional_smul_sndHom ℤ fun _ hx ↦ by omega

/-- On `DualNumber ℤ`, the nondegenerate pairing induced by `(2 : ℤ) • sndHom ℤ ℤ` is not
perfect. -/
theorem not_isPerfPair_compr₂_mul_two_smul_sndHom_int :
    ¬ ((LinearMap.mul ℤ (DualNumber ℤ)).compr₂ ((2 : ℤ) • sndHom ℤ ℤ)).IsPerfPair := by
  rw [isPerfPair_compr₂_mul_smul_sndHom_iff, Int.isUnit_iff]
  omega

end CommRing

end TauCeti

end
