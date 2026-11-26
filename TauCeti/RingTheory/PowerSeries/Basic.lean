/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Complements on power series

Mathlib's `PowerSeries.constantCoeff` is the constant coefficient `S⟦X⟧ → S` as a ring
homomorphism. This file records it as a homomorphism of `A`-algebras for any commutative semiring
`A` over which `S` is an algebra: evaluation at `X = 0`. It also records how a change of
coefficients `map f` acts on the constant coefficient.

## Main definitions

* `PowerSeries.constantCoeffAlgHom A`: the constant coefficient `S⟦X⟧ →ₐ[A] S`.

## Main results

* `PowerSeries.constantCoeffAlgHom_comp_toAlgHom`: evaluation at `X = 0` is a retraction of the
  inclusion of constants.
* `PowerSeries.constantCoeff_map`: a change of coefficients `map f` acts on the constant
  coefficient by `f`, as `MvPowerSeries.constantCoeff_map` does for multivariate power series.
* `PowerSeries.mk_mul_one_sub_X_eq`: if `b d + a (d + 1) = a d + c (d + 1)` for all integers `d`
  and `a`, `b` vanish at `d₀ - 1`, then the series of `a`, `b`, `c` from degree `d₀` satisfy
  `(1 - X) H_a = H_c - X H_b`.
* `PowerSeries.coeff_mul_of_ne_zero`: for `k ≠ 0`, the `Xᵏ`-coefficient of `f * g` is
  `f₀ * gₖ + fₖ * g₀ + Σ_{0 < i < k} fᵢ * g_{k - i}`.
* `PowerSeries.coeff_succ_mul_eq_add_sum`: the `Xⁿ⁺¹`-coefficient of `f * g` is
  `f₀ * gₙ₊₁ + Σ_{j ≤ n} fₙ₊₁₋ⱼ * gⱼ`.
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

end Map

section OneSubX

variable {R : Type*} [CommRing R]

/-- If `b d + a (d + 1) = a d + c (d + 1)` for every integer `d`, and `a` and `b` vanish at
`d₀ - 1`, then the series of `a`, `b` and `c` starting in degree `d₀` satisfy
`(1 - X) H_a = H_c - X H_b`. This is the identity of Hilbert series obtained from exact sequences
`0 → K_d → M_d → M_{d+1} → C_{d+1} → 0`. -/
theorem mk_mul_one_sub_X_eq {a b c : ℤ → R} {d₀ : ℤ}
    (h : ∀ d, b d + a (d + 1) = a d + c (d + 1)) (ha : a (d₀ - 1) = 0) (hb : b (d₀ - 1) = 0) :
    mk (fun n : ℕ ↦ a (d₀ + n)) * (1 - X) =
      mk (fun n : ℕ ↦ c (d₀ + n)) - X * mk (fun n : ℕ ↦ b (d₀ + n)) := by
  ext n
  rw [mul_sub, mul_one, map_sub, map_sub]
  rcases n with _ | n
  · have h₀ := h (d₀ - 1)
    rw [sub_add_cancel, ha, hb] at h₀
    simp only [coeff_zero_mul_X, coeff_zero_X_mul, coeff_mk, Nat.cast_zero, add_zero]
    linear_combination h₀
  · have hn := h (d₀ + n)
    simp only [coeff_succ_mul_X, coeff_succ_X_mul, coeff_mk, Nat.cast_succ, ← add_assoc]
    linear_combination hn

end OneSubX

section Coeff

variable {R : Type*} [Semiring R]

/-- For `k ≠ 0`, the `Xᵏ`-coefficient of `f * g` splits into the two end terms `f₀ * gₖ` and
`fₖ * g₀` and the terms `fᵢ * g_{k - i}` with `0 < i < k`. -/
theorem coeff_mul_of_ne_zero (f g : R⟦X⟧) {k : ℕ} (hk : k ≠ 0) :
    coeff k (f * g) = constantCoeff f * coeff k g + coeff k f * constantCoeff g +
      ∑ i ∈ Finset.Ioo 0 k, coeff i f * coeff (k - i) g := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_eq_add_Ico _ (Nat.pos_of_ne_zero hk), ← Finset.Ico_add_one_left_eq_Ioo]
  simp [add_right_comm]

/-- The `Xⁿ⁺¹`-coefficient of `f * g`, with the term `f₀ * gₙ₊₁` of the constant coefficient of
`f` split off: it is `f₀ * gₙ₊₁ + Σ_{j ≤ n} fₙ₊₁₋ⱼ * gⱼ`. -/
theorem coeff_succ_mul_eq_add_sum (f g : R⟦X⟧) (n : ℕ) :
    coeff (n + 1) (f * g) = coeff 0 f * coeff (n + 1) g +
      ∑ j ∈ Finset.range (n + 1), coeff (n + 1 - j) f * coeff j g := by
  rw [coeff_mul, ← Finset.Nat.sum_antidiagonal_swap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ coeff j f * coeff i g),
    Finset.sum_range_succ, Nat.sub_self, add_comm]

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
