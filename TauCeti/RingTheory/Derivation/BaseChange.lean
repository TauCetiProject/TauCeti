/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Scalar extension of derivations

An `R`-derivation of a commutative `R`-algebra `A` extends to an `S`-derivation of `S ⊗[R] A`
by differentiating the second factor. The extension is linear in the derivation and is uniquely
determined by its values on `1 ⊗ a`. This is the scalar-extension step for comparing traces of
differentials after a coefficient extension.
-/

public section

open TensorProduct

namespace Derivation

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  {S : Type*} [CommSemiring S] [Algebra R S]

variable (S) in
/-- Extend a derivation by differentiating the second factor of a tensor product. -/
noncomputable def baseChange (D : Derivation R A A) :
    Derivation S (S ⊗[R] A) (S ⊗[R] A) where
  __ := D.toLinearMap.baseChange S
  map_one_eq_zero' := by
    rw [Algebra.TensorProduct.one_def, LinearMap.baseChange_tmul]
    simp only [coeFn_coe, map_one_eq_zero, tmul_zero]
  leibniz' a b := by
    induction a using TensorProduct.inductionOn with
    | add a a' ha ha' =>
      simp only [add_mul, map_add, ha, ha', add_smul, smul_add,
        add_comm, add_left_comm, add_assoc]
    | tmul s a =>
      induction b using TensorProduct.inductionOn with
      | add b b' hb hb' =>
        simp only [mul_add, map_add, hb, hb', smul_add, add_smul,
          add_comm, add_left_comm, add_assoc]
      | tmul s' b =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.baseChange_tmul]
        simp only [coeFn_coe, leibniz, smul_eq_mul, tmul_add,
          Algebra.TensorProduct.tmul_mul_tmul,
          mul_comm s s']

/-- The extended derivation differentiates the right tensor factor. -/
@[simp]
theorem baseChange_tmul (D : Derivation R A A) (s : S) (a : A) :
    D.baseChange S (s ⊗ₜ[R] a) = s ⊗ₜ[R] D a := by
  rfl

/-- The underlying linear map is the ordinary scalar extension. -/
@[simp]
theorem baseChange_toLinearMap (D : Derivation R A A) :
    (D.baseChange S).toLinearMap = D.toLinearMap.baseChange S := by
  rfl

/-- An `S`-derivation of `S ⊗[R] A` is determined by its values on the right factor. -/
@[ext]
theorem baseChange_ext {M : Type*} [AddCommMonoid M] [Module S M]
    [Module (S ⊗[R] A) M] {D E : Derivation S (S ⊗[R] A) M}
    (h : ∀ a : A, D (1 ⊗ₜ[R] a) = E (1 ⊗ₜ[R] a)) : D = E := by
  apply Derivation.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s a =>
    have ht : s ⊗ₜ[R] a = s • ((1 : S) ⊗ₜ[R] a) := by rw [smul_tmul', smul_eq_mul, mul_one]
    rw [ht, map_smul, map_smul, h]

/-- Extending the zero derivation gives zero. -/
@[simp]
theorem baseChange_zero : (0 : Derivation R A A).baseChange S = 0 := by
  apply baseChange_ext
  intro a
  simp

/-- Scalar extension preserves addition of derivations. -/
@[simp]
theorem baseChange_add (D E : Derivation R A A) :
    (D + E).baseChange S = D.baseChange S + E.baseChange S := by
  apply baseChange_ext
  intro a
  simp [tmul_add]

/-- Extending an `A`-multiple of a derivation multiplies the extension by `1 ⊗ a`. -/
@[simp]
theorem baseChange_smul (a : A) (D : Derivation R A A) :
    (a • D).baseChange S = ((1 : S) ⊗ₜ[R] a) • D.baseChange S := by
  apply baseChange_ext
  intro b
  simp [Algebra.TensorProduct.tmul_mul_tmul, smul_eq_mul]

section Ring

variable {R A S : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [CommRing S] [Algebra R S]

/-- Scalar extension preserves negation of derivations. -/
@[simp]
theorem baseChange_neg (D : Derivation R A A) :
    (-D).baseChange S = -D.baseChange S := by
  apply baseChange_ext
  intro a
  simp [tmul_neg]

/-- Scalar extension preserves subtraction of derivations. -/
@[simp]
theorem baseChange_sub (D E : Derivation R A A) :
    (D - E).baseChange S = D.baseChange S - E.baseChange S := by
  simp [sub_eq_add_neg]

end Ring

end Derivation
