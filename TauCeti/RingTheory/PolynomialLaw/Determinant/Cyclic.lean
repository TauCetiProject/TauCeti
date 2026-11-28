/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Determinant
import TauCeti.LinearAlgebra.TensorProduct.Basic
import TauCeti.RingTheory.TensorProduct.Maps

/-!
# Cyclic invariance of characteristic coefficients

`TauCeti.Determinant.charpoly_mul_comm` extends `Matrix.charpoly_mul_comm` to Chenevier
determinants. It uses `TauCeti.Determinant.charpoly_monic` to cancel the determinant of a generic
scalar translate of one factor. The theorems `TauCeti.Determinant.charCoeff_mul_comm` and
`TauCeti.Determinant.trace_mul_comm` give the corresponding coefficient and trace identities.
-/

public section

namespace TauCeti.Determinant

open TensorProduct Polynomial

variable {A : Type*} [CommRing A] {R : Type*} [Semiring R] [Algebra A R] {d : ℕ}
  (D : Determinant A R d)

/-- The determinant of `X + x` is monic after extension to any commutative coefficient semiring. -/
theorem monic_rid_toFun_X_tmul_one_add_one_tmul (S : Type*) [CommSemiring S] [Algebra A S] (x : R) :
    (Algebra.TensorProduct.rid A A S[X]
      (D.toLaw.toFun S[X] ((X : S[X]) ⊗ₜ (1 : R) + 1 ⊗ₜ x))).Monic := by
  let φ : A[X] →ₐ[A] S[X] := mapAlgHom (Algebra.ofId A S)
  have hφ : φ.toLinearMap.rTensor R
      ((X : A[X]) ⊗ₜ (1 : R) - 1 ⊗ₜ ((-1 : A) • x)) =
      (X : S[X]) ⊗ₜ (1 : R) + 1 ⊗ₜ x := by
    rw [← smul_tmul, neg_one_smul, neg_tmul, sub_neg_eq_add]
    simp only [map_add, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, φ, coe_mapAlgHom,
      map_X, Polynomial.map_one]
  have hr (z : A[X] ⊗[A] A) :
      Algebra.TensorProduct.rid A A S[X] (φ.toLinearMap.rTensor A z) =
        φ (Algebra.TensorProduct.rid A A A[X] z) :=
    LinearMap.rid_rTensor_apply φ.toLinearMap z
  rw [← hφ, ← PolynomialLaw.isCompat_apply, hr, ← PolynomialLaw.toFun'_eq_toFun, ← charpoly_def]
  simp only [φ, coe_mapAlgHom]
  exact (D.charpoly_monic _).map _

/-- The characteristic polynomial of a product is invariant under exchanging its two factors.
This is the characteristic-polynomial form of
[Chenevier, Lemma 1.12(i)](https://arxiv.org/abs/0809.0415). -/
theorem charpoly_mul_comm (x y : R) : D.charpoly (x * y) = D.charpoly (y * x) := by
  -- Use the outer variable to make the determinant of the left factor cancellable.
  let u : A[X][X] ⊗[A] R := X ⊗ₜ 1 + 1 ⊗ₜ x
  let v : A[X][X] ⊗[A] R := (-1) ⊗ₜ y
  let t : A[X][X] ⊗[A] R := C X ⊗ₜ 1
  let e := Algebra.TensorProduct.rid A A A[X][X]
  let F := fun z : A[X][X] ⊗[A] R ↦ e (D.toLaw.toFun A[X][X] z)
  have hF (a b : A[X][X] ⊗[A] R) : F (a * b) = F a * F b := by
    simp only [F, D.isMultiplicative.toFun_mul, _root_.map_mul]
  have htu : Commute u t :=
    ((Commute.all _ _).tmul (Commute.refl _)).add_left
      ((Commute.one_left _).tmul (Commute.one_right _))
  have hprod : u * (t + v * u) = (t + u * v) * u := by
    rw [mul_add u t, add_mul t (u * v), htu.eq, mul_assoc]
  have h := congrArg F hprod
  rw [hF, hF, mul_comm (F (t + u * v))] at h
  have hu : (F u).Monic := D.monic_rid_toFun_X_tmul_one_add_one_tmul A[X] x
  have hcancel := e.injective (hu.isRegular.left h)
  -- Set the outer variable to zero, preserving the characteristic-polynomial variable.
  let ψ : A[X][X] →ₐ[A] A[X] := (aeval (0 : A[X])).restrictScalars A
  set g := Algebra.TensorProduct.map ψ (AlgHom.id A R) with hg
  have hg_tmul (p : A[X][X]) (z : R) : g (p ⊗ₜ z) = aeval (0 : A[X]) p ⊗ₜ z := by
    simp only [hg, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ψ,
      AlgHom.restrictScalars_apply]
  have gt : g t = (X : A[X]) ⊗ₜ (1 : R) := by
    simp only [t, hg_tmul, aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
  have gu : g u = (1 : A[X]) ⊗ₜ x := by
    simp only [u, map_add, hg_tmul, aeval_X, zero_tmul, _root_.map_one, zero_add]
  have gv : g v = (-1 : A[X]) ⊗ₜ y := by
    simp only [v, hg_tmul, _root_.map_neg, _root_.map_one]
  have hspec := congrArg (ψ.toLinearMap.rTensor A) hcancel
  rw [PolynomialLaw.isCompat_apply, PolynomialLaw.isCompat_apply] at hspec
  simp only [AlgHom.rTensor_toLinearMap_apply, ← hg, map_add, _root_.map_mul, gt, gu, gv] at hspec
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at hspec
  simp only [neg_tmul, ← sub_eq_add_neg] at hspec
  simpa only [charpoly_def, PolynomialLaw.toFun'_eq_toFun] using
    congrArg (Algebra.TensorProduct.rid A A A[X]) hspec.symm

/-- Each characteristic coefficient of a product is invariant under cyclic rotation. -/
theorem charCoeff_mul_comm (i : ℕ) (x y : R) : D.charCoeff i (x * y) = D.charCoeff i (y * x) := by
  by_cases hi : i ≤ d
  · have h := congrArg (fun p : A[X] ↦ p.coeff (d - i)) (D.charpoly_mul_comm x y)
    simp only [coeff_charpoly, ite_eq_left (Nat.sub_le d i), Nat.sub_sub_self hi] at h
    exact ((isUnit_neg_one : IsUnit (-1 : A)).pow i).mul_left_cancel h
  · simp only [D.charCoeff_eq_zero (Nat.lt_of_not_ge hi)]

/-- The trace of a determinant is central. -/
theorem trace_mul_comm (x y : R) : D.trace (x * y) = D.trace (y * x) := by
  simp only [trace_apply, D.charCoeff_mul_comm]

end TauCeti.Determinant
