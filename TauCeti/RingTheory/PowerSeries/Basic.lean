/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.RingTheory.MvPowerSeries.Basic

/-!
# Complements on power series

Mathlib's `PowerSeries.constantCoeff` is the constant coefficient `S⟦X⟧ → S` as a ring
homomorphism. This file records it as a homomorphism of `A`-algebras for any commutative semiring
`A` over which `S` is an algebra: evaluation at `X = 0`. It also records how a change of
coefficients `map f` acts on the constant coefficient, how multiplication splits into constant
and positive-degree terms, and univariate bridges for `MvPowerSeries.liftOfSurjective` and
coefficientwise membership.

## Main definitions

* `PowerSeries.constantCoeffAlgHom A`: the constant coefficient `S⟦X⟧ →ₐ[A] S`.

## Main results

* `PowerSeries.constantCoeffAlgHom_comp_toAlgHom`: evaluation at `X = 0` is a retraction of the
  inclusion of constants.
* `PowerSeries.constantCoeff_map`: a change of coefficients `map f` acts on the constant
  coefficient by `f`, as `MvPowerSeries.constantCoeff_map` does for multivariate power series.
* `PowerSeries.map_liftOfSurjective`: mapping `MvPowerSeries.liftOfSurjective hπ f` back along
  `π` recovers `f` as a univariate power series.
* `PowerSeries.mvCoeff_mem_of_coeff_mem`: converts univariate coefficient membership
  `∀ n, coeff n f ∈ I` to multivariate coefficient membership `∀ d, MvPowerSeries.coeff d f ∈ I`.
* `PowerSeries.coeff_mul_of_ne_zero`: for `k ≠ 0`, the `Xᵏ`-coefficient of `f * g` is
  `f₀ * gₖ + fₖ * g₀ + Σ_{0 < i < k} fᵢ * g_{k - i}`.
* `Polynomial.coeff_coe_eq_zero_of_degree_lt`: a polynomial of degree less than `s`, viewed as a
  power series, has zero coefficients from `s` on.
-/

public section

open scoped PowerSeries

namespace PowerSeries

section ConstantCoeff

variable (A : Type*) {S : Type*} [CommSemiring A] [Semiring S] [Algebra A S]

/-- The constant coefficient `S⟦X⟧ → S`, that is, evaluation at `X = 0`, as a homomorphism of
`A`-algebras. -/
noncomputable def constantCoeffAlgHom : S⟦X⟧ →ₐ[A] S where
  toRingHom := constantCoeff
  commutes' a := by rw [RingHom.toFun_eq_coe, algebraMap_apply, constantCoeff_C]

variable {A}

@[simp]
theorem constantCoeffAlgHom_apply (f : S⟦X⟧) : constantCoeffAlgHom A f = constantCoeff f := (rfl)

/-- As a ring homomorphism, `PowerSeries.constantCoeffAlgHom` is `PowerSeries.constantCoeff`. -/
@[simp]
theorem constantCoeffAlgHom_toRingHom :
    (constantCoeffAlgHom A (S := S) : S⟦X⟧ →+* S) = constantCoeff :=
  (rfl)

/-- Evaluation at `X = 0` is a retraction of the inclusion of constants. -/
@[simp]
theorem constantCoeffAlgHom_comp_toAlgHom {S : Type*} [CommSemiring S] [Algebra A S] :
    (constantCoeffAlgHom A).comp (IsScalarTower.toAlgHom A S S⟦X⟧) = AlgHom.id A S :=
  AlgHom.ext fun s ↦ by simp

end ConstantCoeff

section Map

variable {R S : Type*} [Semiring R] [Semiring S]

/-- A change of coefficients `map f` acts on the constant coefficient by `f`. -/
@[simp]
theorem constantCoeff_map (f : R →+* S) (φ : R⟦X⟧) :
    constantCoeff (map f φ) = f (constantCoeff φ) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply]

/-- Mapping `MvPowerSeries.liftOfSurjective hπ f` back along `π` recovers `f` as a univariate
power series. -/
@[simp]
theorem map_liftOfSurjective {π : R →+* S} (hπ : Function.Surjective π) (f : S⟦X⟧) :
    map π (MvPowerSeries.liftOfSurjective hπ f) = f :=
  ext fun n ↦ by
    rw [coeff_map, coeff_def (s := Finsupp.single () n) Finsupp.single_eq_same,
      MvPowerSeries.coeff_liftOfSurjective, Function.surjInv_eq hπ,
      ← coeff_def (s := Finsupp.single () n) Finsupp.single_eq_same]

end Map

section Coeff

variable {R : Type*} [Semiring R]

/-- If every univariate coefficient of `f : R⟦X⟧` lies in `I`, then so does every multivariate
coefficient `MvPowerSeries.coeff d f` (`d : Unit →₀ ℕ`). -/
theorem mvCoeff_mem_of_coeff_mem {C : Type*} [SetLike C R] {I : C} {f : R⟦X⟧}
    (hf : ∀ n, coeff n f ∈ I) (d : Unit →₀ ℕ) : MvPowerSeries.coeff d f ∈ I := by
  rw [← coeff_def (s := d) rfl]
  exact hf (d ())

/-- For `k ≠ 0`, the `Xᵏ`-coefficient of `f * g` splits into the two end terms `f₀ * gₖ` and
`fₖ * g₀` and the terms `fᵢ * g_{k - i}` with `0 < i < k`. -/
theorem coeff_mul_of_ne_zero (f g : R⟦X⟧) {k : ℕ} (hk : k ≠ 0) :
    coeff k (f * g) = constantCoeff f * coeff k g + coeff k f * constantCoeff g +
      ∑ i ∈ Finset.Ioo 0 k, coeff i f * coeff (k - i) g := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_eq_add_Ico _ (Nat.pos_of_ne_zero hk), ← Finset.Ico_add_one_left_eq_Ioo]
  simp [add_right_comm]

end Coeff

end PowerSeries

namespace Polynomial

variable {R : Type*} [Semiring R]

/-- A polynomial of degree less than `s`, viewed as a power series, has zero coefficients from
`s` on. -/
theorem coeff_coe_eq_zero_of_degree_lt {s : ℕ} {p : Polynomial R} {m : ℕ} (hp : p.degree < s)
    (hm : s ≤ m) : (p : PowerSeries R).coeff m = 0 := by
  rw [coeff_coe]
  exact coeff_eq_zero_of_degree_lt (hp.trans_le (by exact_mod_cast hm))

end Polynomial
