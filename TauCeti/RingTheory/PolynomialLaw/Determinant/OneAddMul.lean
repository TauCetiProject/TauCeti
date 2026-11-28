/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Determinant.Basic

/-!
# `D(1 + r r') = D(1 + r' r)`

For a determinant `D` on an `A`-algebra `R` and `r, r' ∈ R`, `D(1 + r r') = D(1 + r' r)`, the
analogue of Mathlib's `Matrix.det_one_add_mul_comm`.

The proof avoids inverting `r`. After scalar extension to `A[X]`, the element `u = X + r` satisfies
`u (1 + r' u) = (1 + u r') u`, so multiplicativity gives `D(u) D(1 + r' u) = D(1 + u r') D(u)`.
Here `D(u)` is the characteristic polynomial of `(-1) • r`, monic, hence a non-zero-divisor of
`A[X]`, so `D(1 + r' u) = D(1 + u r')` in `A[X]`. Evaluating at `X = 0`, which the law commutes
with, gives the claim.

## Main declarations

* `TauCeti.Determinant.map_one_add_mul_comm`: `D(1 + r r') = D(1 + r' r)`.

## References

* [G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, Lemma 1.12(i)](https://arxiv.org/abs/0809.0415)
-/

public section

noncomputable section

universe u

open TensorProduct Polynomial

namespace TauCeti

namespace Determinant

variable {A : Type u} [CommRing A] {R : Type*} [Semiring R] [Algebra A R] {d : ℕ}
  (D : Determinant A R d)

/-- **`D(1 + r r') = D(1 + r' r)`** for a determinant `D` and any `r, r' ∈ R`. -/
theorem map_one_add_mul_comm (r r' : R) : D (1 + r * r') = D (1 + r' * r) := by
  set u : A[X] ⊗[A] R := X ⊗ₜ 1 + 1 ⊗ₜ r
  set v : A[X] ⊗[A] R := 1 ⊗ₜ r'
  let F : A[X] ⊗[A] R → A[X] := fun z ↦ Algebra.TensorProduct.rid A A A[X] (D.toLaw.toFun A[X] z)
  have hF (z w : A[X] ⊗[A] R) : F (z * w) = F z * F w := by
    simp only [F, D.isMultiplicative.toFun_mul, _root_.map_mul]
  have hcomm : u * (1 + v * u) = (1 + u * v) * u := by
    simp only [mul_add, add_mul, mul_one, one_mul, mul_assoc]
  have hcancel : F (1 + v * u) = F (1 + u * v) := by
    have h := congrArg F hcomm
    rw [hF, hF, mul_comm (F (1 + u * v))] at h
    have hu : F u = D.charpoly ((-1 : A) • r) := by
      rw [charpoly_def, PolynomialLaw.toFun'_eq_toFun, ← smul_tmul, neg_one_smul,
        neg_tmul, sub_neg_eq_add]
    exact (hu ▸ D.charpoly_monic _).isRegular.left h
  have h1 : LinearMap.rTensor R (aeval (0 : A)).toLinearMap (1 + v * u) = 1 ⊗ₜ (1 + r' * r) := by
    simp [u, v, Algebra.TensorProduct.one_def, mul_add, tmul_add]
  have h2 : LinearMap.rTensor R (aeval (0 : A)).toLinearMap (1 + u * v) = 1 ⊗ₜ (1 + r * r') := by
    simp [u, v, Algebra.TensorProduct.one_def, add_mul, tmul_add]
  rw [D.apply_eq_rid_toFun_of_rTensor_eq _ h2, D.apply_eq_rid_toFun_of_rTensor_eq _ h1]
  exact congrArg (aeval (0 : A)) hcancel.symm

end Determinant

end TauCeti
