/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Derivation.Basic
public import TauCeti.Algebra.Lie.Loop.HahnModule
public import TauCeti.RingTheory.LaurentSeries.HahnModuleDerivative

/-!
# The derivative of the formal loop algebra

Let `L` be a Lie algebra over a commutative ring `R`. The formal loop algebra `L((t))` is
`HahnModule ℤ R L` with the coefficient convolution bracket. Its derivative
`D = HahnModule.derivative R`, the coefficientwise derivative `d/dt`, is a derivation of this Lie
algebra:

`D ⁅x, y⁆ = ⁅D x, y⁆ + ⁅x, D y⁆`.

On the polynomial loops `t ^ n ⊗ x`, embedded by `LieAlgebra.LoopAlgebra.toHahnModule`, the
derivative is `D (t ^ n ⊗ x) = t ^ (n - 1) ⊗ n x`. This is the mode formula behind Mathlib's
residue pairing `LieAlgebra.LoopAlgebra.residuePairing`, read as `(f, g) ↦ Res Φ(f, D g) dt` for a
bilinear form `Φ` on `L`.

## Main definitions

* `HahnModule.lieDerivation R L`: the derivative of `L((t))` as a Lie derivation.

## Main results

* `HahnModule.derivative_lie`: the Leibniz rule `D ⁅x, y⁆ = ⁅D x, y⁆ + ⁅x, D y⁆`.
* `LieAlgebra.LoopAlgebra.derivative_toHahnModule_single_tmul`: the derivative of a polynomial
  loop `t ^ n ⊗ x` is the image of `t ^ (n - 1) ⊗ n x`.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.2.
-/

public section

noncomputable section

open Finset HahnSeries

namespace HahnModule

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/- The Euler operator `t D` multiplies the coefficient of `t ^ n` by `n`; on the coefficient
`∑_{i + j = n} ⁅x_i, y_j⁆` of a bracket it splits `n = i + j`. Dividing by `t`, which is compatible
with the bracket because `L((t))` is a Lie algebra over `R⸨X⸩`, recovers the rule for `D`. -/

/-- The Euler operator `t D` is a derivation of the convolution bracket. -/
private theorem single_one_smul_derivative_lie (x y : HahnModule ℤ R L) :
    single (1 : ℤ) (1 : R) • derivative R ⁅x, y⁆ =
      ⁅single (1 : ℤ) (1 : R) • derivative R x, y⁆ +
        ⁅x, single (1 : ℤ) (1 : R) • derivative R y⁆ := by
  ext n
  have hx : ((of R).symm (single (1 : ℤ) (1 : R) • derivative R x)).support ⊆
      ((of R).symm x).support := fun i hi ↦ by
    rw [mem_support, coeff_single_one_smul_derivative] at hi
    exact right_ne_zero_of_smul hi
  have hy : ((of R).symm (single (1 : ℤ) (1 : R) • derivative R y)).support ⊆
      ((of R).symm y).support := fun j hj ↦ by
    rw [mem_support, coeff_single_one_smul_derivative] at hj
    exact right_ne_zero_of_smul hj
  rw [of_symm_add, coeff_add, coeff_single_one_smul_derivative, coeff_lie,
    coeff_lie_left' ((of R).symm x).isPWO_support hx,
    coeff_lie_right' ((of R).symm y).isPWO_support hy, smul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun ij hij ↦ ?_
  obtain ⟨-, -, hn⟩ := mem_antidiagonal.1 hij
  rw [coeff_single_one_smul_derivative, coeff_single_one_smul_derivative, zsmul_lie, lie_zsmul,
    ← hn, add_zsmul]

/-- **The Leibniz rule** for the derivative of the formal loop algebra:
`D ⁅x, y⁆ = ⁅D x, y⁆ + ⁅x, D y⁆`. -/
theorem derivative_lie (x y : HahnModule ℤ R L) :
    derivative R ⁅x, y⁆ = ⁅derivative R x, y⁆ + ⁅x, derivative R y⁆ := by
  rw [← single_neg_smul_single_smul 1 (derivative R ⁅x, y⁆), single_one_smul_derivative_lie,
    smul_add, ← smul_lie, ← lie_smul, single_neg_smul_single_smul, single_neg_smul_single_smul]

variable (R L) in
/-- The derivative `d/dt` of the formal loop algebra `L((t))`, as a derivation of its Lie
bracket. -/
def lieDerivation : LieDerivation R (HahnModule ℤ R L) (HahnModule ℤ R L) where
  __ := derivative R
  leibniz' x y := by
    simp only [derivative_lie]
    rw [← lie_skew y, sub_eq_add_neg, neg_neg, add_comm]

/-- The Lie derivation of the formal loop algebra is its coefficientwise derivative. -/
@[simp]
theorem lieDerivation_apply (x : HahnModule ℤ R L) :
    lieDerivation R L x = derivative R x :=
  (rfl)

end HahnModule

namespace LieAlgebra.LoopAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The derivative of the polynomial loop `t ^ n ⊗ x` in the formal loop algebra is the image of
the polynomial loop `t ^ (n - 1) ⊗ n x`. -/
theorem derivative_toHahnModule_single_tmul (n : ℤ) (x : L) :
    HahnModule.derivative R (toHahnModule R ℤ L (AddMonoidAlgebra.single n 1 ⊗ₜ[R] x)) =
      toHahnModule R ℤ L (AddMonoidAlgebra.single (n - 1) 1 ⊗ₜ[R] (n • x)) := by
  rw [toHahnModule_single_tmul, toHahnModule_single_tmul, HahnModule.derivative_single]

end LieAlgebra.LoopAlgebra
