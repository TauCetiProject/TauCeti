/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Determinant

/-!
# `D(1 + r r') = D(1 + r' r)`

For a determinant `D` on an `A`-algebra `R` and `r, r' ∈ R`, `D(1 + r r') = D(1 + r' r)`, the
analogue of Mathlib's `Matrix.det_one_add_mul_comm`.

The proof avoids inverting `r`. After scalar extension to `A[X]`, the element `u = X + r` satisfies
`u (1 + r' u) = (1 + u r') u`, so multiplicativity gives `D(u) D(1 + r' u) = D(1 + u r') D(u)`.
Here `D(u) = ∑ᵢ Λᵢ(r) X^(d - i)` is monic, hence a non-zero-divisor of `A[X]`, so
`D(1 + r' u) = D(1 + u r')` in `A[X]`. Evaluating at `X = 0`, which the law commutes with, gives
the claim.

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

/-- After scalar extension to `A[X]`, `D(X ⊗ 1 + 1 ⊗ r)` is monic. -/
theorem monic_rid_toFun_X_tmul_one_add_one_tmul (r : R) :
    (Algebra.TensorProduct.rid A A A[X] (D.toLaw.toFun A[X] (X ⊗ₜ 1 + 1 ⊗ₜ r))).Monic := by
  rw [add_comm]
  refine monic_of_natDegree_le_of_coeff_eq_one d ?_ ?_
  · rw [rid_toFun_one_tmul_add_X_tmul_one]
    exact natDegree_sum_le_of_forall_le _ _ fun i _ ↦
      (natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le d i)
  · simpa [charCoeff_zero] using D.coeff_rid_toFun_one_tmul_add_X_tmul_one (Nat.zero_le d) r

/-- Evaluating at `X = 0` after the law at `A[X]` is the law at `A`: reading off values in `A`
through `rid` and `lid` commutes with the evaluation. -/
private theorem lid_rTensor_aeval_zero (z : A[X] ⊗[A] A) :
    TensorProduct.lid A A (LinearMap.rTensor A (aeval (0 : A)).toLinearMap z) =
      aeval (0 : A) (Algebra.TensorProduct.rid A A A[X] z) := by
  induction z using TensorProduct.inductionOn with
  | tmul p a => simp [mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

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
    exact (D.monic_rid_toFun_X_tmul_one_add_one_tmul r).isRegular.left h
  -- evaluate at `X = 0`
  have heval (z : A[X] ⊗[A] R) (x : R)
      (hz : LinearMap.rTensor R (aeval (0 : A)).toLinearMap z = 1 ⊗ₜ x) :
      D x = aeval (0 : A) (F z) := by
    rw [apply_eq_lid_toFun, ← hz, ← PolynomialLaw.isCompat_apply, lid_rTensor_aeval_zero]
  have h1 : LinearMap.rTensor R (aeval (0 : A)).toLinearMap (1 + v * u) = 1 ⊗ₜ (1 + r' * r) := by
    simp [u, v, Algebra.TensorProduct.one_def, mul_add, tmul_add]
  have h2 : LinearMap.rTensor R (aeval (0 : A)).toLinearMap (1 + u * v) = 1 ⊗ₜ (1 + r * r') := by
    simp [u, v, Algebra.TensorProduct.one_def, add_mul, tmul_add]
  rw [heval _ _ h2, heval _ _ h1, hcancel]

end Determinant

end TauCeti
