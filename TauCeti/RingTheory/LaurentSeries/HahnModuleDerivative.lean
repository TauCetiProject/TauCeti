/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Derivative
public import TauCeti.RingTheory.LaurentSeries.Lattice

/-!
# The derivative of module-valued Laurent series

For a module `V` over a ring `R`, the `V`-valued Laurent series `V((t))` are modelled by
`HahnModule ℤ R V`, which carries the convolution action of the scalar Laurent series `R⸨X⸩`.
This file transports Mathlib's coefficientwise derivative `LaurentSeries.derivative` on
`LaurentSeries V` through the coefficient-preserving comparison `HahnModule.of`, giving the
`R`-linear map `D = d/dt` on `V((t))` with `D (v t ^ n) = n v t ^ (n - 1)`.

The main result is the Leibniz rule `D (f • x) = D f • x + f • D x` for the action of `f : R⸨X⸩`
on `x : V((t))`, over any ring `R`. The Leibniz rule for the convolution bracket of
Lie-algebra-valued Laurent series is `HahnModule.derivative_lie`.

The derivative maps the lattice `U_a(V) = t ^ a V⟦t⟧` into `U_(a - 1)(V)`, the estimate that makes
it continuous for the topology these lattices define, and it commutes with coefficientwise linear
maps.

## Main definitions

* `HahnModule.derivative R`: the derivative `D` of `V`-valued Laurent series.

## Main results

* `HahnModule.coeff_derivative`: the coefficient of `t ^ n` in `D x` is `n + 1` times the
  coefficient of `t ^ (n + 1)` in `x`.
* `HahnModule.derivative_single`: `D (v t ^ n) = n v t ^ (n - 1)`.
* `HahnModule.derivative_smul`: the Leibniz rule `D (f • x) = D f • x + f • D x`.
* `HahnModule.derivative_mem_lattice`: `D` maps `U_a(V)` into `U_(a - 1)(V)`.
* `HahnModule.derivative_map`: `D` commutes with coefficientwise linear maps.
-/

public section

noncomputable section

open Finset HahnSeries
open scoped LaurentSeries

namespace HahnModule

section Module

variable (R : Type*) {V : Type*} [Semiring R] [AddCommGroup V] [Module R V]

/-- The derivative `d/dt` of `V`-valued Laurent series `HahnModule ℤ R V`: Mathlib's
`LaurentSeries.derivative` on `LaurentSeries V`, read through the coefficient-preserving
comparison `HahnModule.of`. -/
def derivative : HahnModule ℤ R V →ₗ[R] HahnModule ℤ R V :=
  (ofLinearEquiv R).toLinearMap ∘ₗ LaurentSeries.derivative R ∘ₗ
    (ofLinearEquiv R).symm.toLinearMap

variable {R}

/-- Reading `D x` through `HahnModule.of` gives the derivative of `V`-valued Laurent series. -/
@[simp]
theorem of_symm_derivative (x : HahnModule ℤ R V) :
    (of R).symm (derivative R x) = LaurentSeries.derivative R ((of R).symm x) := by
  simp [derivative]

/-- The derivative of the module-valued series attached to `f` is attached to the derivative of
`f`. -/
theorem derivative_of (f : LaurentSeries V) :
    derivative R (of R f) = of R (LaurentSeries.derivative R f) := by
  simp [derivative]

/-- The coefficient of `t ^ n` in `D x` is `n + 1` times the coefficient of `t ^ (n + 1)` in
`x`. -/
theorem coeff_derivative (x : HahnModule ℤ R V) (n : ℤ) :
    ((of R).symm (derivative R x)).coeff n = (n + 1) • ((of R).symm x).coeff (n + 1) := by
  rw [of_symm_derivative, LaurentSeries.coeff_derivative]

/-- The coefficient of `t ^ (n - 1)` in `D x` is `n` times the coefficient of `t ^ n` in `x`. -/
theorem coeff_derivative_sub_one (x : HahnModule ℤ R V) (n : ℤ) :
    ((of R).symm (derivative R x)).coeff (n - 1) = n • ((of R).symm x).coeff n := by
  rw [of_symm_derivative, LaurentSeries.coeff_derivative_sub_one]

/-- The derivative of a monomial: `D (v t ^ n) = n v t ^ (n - 1)`. -/
@[simp]
theorem derivative_single (n : ℤ) (v : V) :
    derivative R (of R (single n v)) = of R (single (n - 1) (n • v)) := by
  rw [derivative_of, LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_single,
    Ring.choose_one_right, Nat.cast_one]

/-- The derivative maps the lattice `U_a(V) = t ^ a V⟦t⟧` into `U_(a - 1)(V)`. -/
theorem derivative_mem_lattice {a : ℤ} {x : HahnModule ℤ R V}
    (hx : x ∈ TauCeti.HahnModule.lattice R V a) :
    derivative R x ∈ TauCeti.HahnModule.lattice R V (a - 1) := by
  rw [TauCeti.HahnModule.mem_lattice_iff] at hx ⊢
  intro n hn
  rw [coeff_derivative, hx (n + 1) (by omega), smul_zero]

/-- The derivative commutes with applying a linear map to the coefficients. -/
theorem derivative_map {W : Type*} [AddCommGroup W] [Module R W] (g : V →ₗ[R] W)
    (x : HahnModule ℤ R V) :
    derivative R (of R (((of R).symm x).map g)) =
      of R (((of R).symm (derivative R x)).map g) := by
  rw [derivative_of, LaurentSeries.derivative_map, of_symm_derivative]

end Module

section Leibniz

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

/-- The Euler operator `t D` multiplies the coefficient of `t ^ n` by `n`. -/
theorem coeff_single_one_smul_derivative (x : HahnModule ℤ R V) (n : ℤ) :
    ((of R).symm (single (1 : ℤ) (1 : R) • derivative R x)).coeff n =
      n • ((of R).symm x).coeff n := by
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = (1 : ℤ) +ᵥ m := ⟨n - 1, by rw [vadd_eq_add, add_sub_cancel]⟩
  rw [coeff_single_smul_vadd, one_smul, coeff_derivative, vadd_eq_add, add_comm]

/- The Leibniz rules pass through the Euler operator `t D`, which multiplies the coefficient of
`t ^ n` by `n`: on the convolution `f • x` this gives `n = i + j` on each pair of exponents
`(i, j)` with `i + j = n`, and dividing by `t` recovers `D`. -/

/-- The Euler operator `t D` satisfies the Leibniz rule for the action of scalar Laurent series. -/
private theorem single_one_smul_derivative_smul (f : R⸨X⸩) (x : HahnModule ℤ R V) :
    single (1 : ℤ) (1 : R) • derivative R (f • x) =
      (single (1 : ℤ) (1 : R) * LaurentSeries.derivative R f) • x +
        f • (single (1 : ℤ) (1 : R) • derivative R x) := by
  ext n
  have hf : (single (1 : ℤ) (1 : R) * LaurentSeries.derivative R f).support ⊆ f.support :=
    fun i hi ↦ by
      rw [mem_support, LaurentSeries.coeff_single_one_mul_derivative] at hi
      exact right_ne_zero_of_smul hi
  have hx : ((of R).symm (single (1 : ℤ) (1 : R) • derivative R x)).support ⊆
      ((of R).symm x).support := fun j hj ↦ by
    rw [mem_support, coeff_single_one_smul_derivative] at hj
    exact right_ne_zero_of_smul hj
  rw [of_symm_add, coeff_add, coeff_single_one_smul_derivative, coeff_smul,
    coeff_smul_left f.isPWO_support hf, coeff_smul_right ((of R).symm x).isPWO_support hx,
    smul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun ij hij ↦ ?_
  obtain ⟨-, -, hn⟩ := (mem_vaddAntidiagonal _ _).1 hij
  rw [LaurentSeries.coeff_single_one_mul_derivative, coeff_single_one_smul_derivative, smul_assoc,
    smul_comm (f.coeff ij.1), ← hn, vadd_eq_add, add_zsmul]

/-- **The Leibniz rule** for the action of scalar Laurent series on module-valued Laurent series:
`D (f • x) = D f • x + f • D x`. -/
theorem derivative_smul (f : R⸨X⸩) (x : HahnModule ℤ R V) :
    derivative R (f • x) = LaurentSeries.derivative R f • x + f • derivative R x := by
  -- `t ^ (-1)` commutes with `f`, so it can be moved past `f` to cancel `t` in `f • t D x`.
  have hc : single (-1 : ℤ) (1 : R) * f = f * single (-1) 1 := by
    ext n
    rw [coeff_single_mul, coeff_mul_single, one_mul, mul_one]
  rw [← single_neg_smul_single_smul 1 (derivative R (f • x)), single_one_smul_derivative_smul,
    smul_add, ← mul_smul, ← mul_assoc, single_mul_single, neg_add_cancel, one_mul, single_zero_one,
    one_mul, ← mul_smul, hc, mul_smul, single_neg_smul_single_smul]

end Leibniz

end HahnModule
