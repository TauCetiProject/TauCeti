/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Topology.Algebra.Polynomial
import TauCeti.Analysis.Polynomial.Order
import TauCeti.Analysis.SpecialFunctions.Complex.Exp.Limits
import TauCeti.RingTheory.PowerSeries.Derivative
import TauCeti.RingTheory.PowerSeries.Trunc

/-!
# Formal solutions at an irregular singularity of rank one

Consider `w'' + f(z) w' + g(z) w = 0` near `z = ∞`, where `f(z) = ∑ fₛ z⁻ˢ` and
`g(z) = ∑ gₛ z⁻ˢ` converge for `|z| > a` (the setting of DLMF §2.7(ii)). When `f₀`, `g₀` and `g₁`
are not all zero, infinity is then an irregular singularity of rank one, and the equation has
formal solutions (DLMF 2.7.8)

`exp(κ z) z^μ ∑ aₛ z⁻ˢ`,

where `κ` is a root of the characteristic equation `κ² + f₀ κ + g₀ = 0` (2.7.9),
`μ = -(κ f₁ + g₁) / (f₀ + 2κ)` (2.7.10), and the coefficients are determined by `a₀ = 1` and the
recursion (2.7.11)

`(f₀ + 2κ) s aₛ = (s - μ) (s - 1 - μ) aₛ₋₁ + ∑_{k=1}^{s} (κ fₖ₊₁ + gₖ₊₁ - (s - k - μ) fₖ) aₛ₋ₖ`.

This requires the two characteristic roots to be distinct, `f₀ + 2κ ≠ 0`. The actual solutions
with these asymptotic expansions are obtained, for convergent `f` and `g`, from the truncations by
solving a Volterra integral equation for the error, with the residual of the truncation as the
forcing term (Olver, Chapter 7, §2).

This file proves the formal part and the residual estimate. The formal part uses only the
coefficient sequences, recorded as formal power series `F` and `G` in the variable `X = z⁻¹`, and
holds over any commutative ring, respectively any field of characteristic zero for the
normalized coefficients. The residual estimate needs only the finite asymptotic expansions
`f(z) = ∑_{k ≤ N} fₖ z⁻ᵏ + O(z^{-N-1})` and likewise for `g`, and only along the region where the
residual is wanted.

Solutions are written in the logarithmic coordinate `z = exp ζ`. There `z^μ = exp(μ ζ)` needs no
choice of branch, the truncations are entire functions of `ζ`, and `w(e^ζ) = W(ζ)` turns the
equation into `W'' + (e^ζ f(e^ζ) - 1) W' + e^{2ζ} g(e^ζ) W = 0`. The residual estimates hold along
any filter `l ≤ comap re atTop`, that is as `Re ζ → +∞` in a region chosen by `l`, provided the
expansions of `f` and `g` hold along `l` after the substitution `z = e^ζ`. For `l = comap re atTop`
this asks for expansions as `z → ∞` in all directions and gives estimates uniform in `Im ζ`; for
a log strip `Re ζ → +∞` with `Im ζ` bounded, which is `z → ∞` in a sector, expansions in that
sector suffice. Expansions as `z → ∞` in all directions give the hypotheses along every such `l`
by composition with `Complex.tendsto_exp_comap_re_atTop`.

## Main definitions

* `TauCeti.rankOneOperator F G κ μ`: the linear operator
  `A ↦ X² (θ - μ) (θ - μ + 1) A - X (2κ + F) (θ - μ) A + (κ² + κ F + G) A`, with `θ = X d/dX`,
  obtained by substituting `exp(κ z) z^μ A(z⁻¹)` into the equation.
* `TauCeti.rankOneCoeff F G κ μ`: the candidate coefficient sequence of DLMF 2.7.11, normalized
  by `a₀ = 1`.
* `TauCeti.rankOneFormalSolutionTrunc κ μ a N`: the truncation
  `exp(κ e^ζ + μ ζ) ∑_{s<N} aₛ e^{-sζ}`.

## Main results

* `TauCeti.coeff_zero_rankOneOperator`, `TauCeti.coeff_one_rankOneOperator`,
  `TauCeti.coeff_add_two_rankOneOperator`: the coefficients of the formal operator, which give
  2.7.9, 2.7.10 and 2.7.11.
* `TauCeti.mul_rankOneCoeff`: the recursion 2.7.11, and `TauCeti.eq_rankOneCoeff_of_forall_mul_eq`:
  for `f₀ + 2κ ≠ 0` it determines the sequence from `a₀ = 1`.
* `TauCeti.rankOneOperator_mk_rankOneCoeff`: under 2.7.9 and 2.7.10 with distinct roots, the
  series with the coefficients of 2.7.11 is a formal solution.
* `TauCeti.eq_rankOneCoeff_of_rankOneOperator_eq_zero`: for fixed `κ` and `μ` with
  `f₀ + 2κ ≠ 0`, that is a simple root `κ`, it is the only formal solution with `a₀ = 1`.
* `TauCeti.hasDerivAt_rankOneFormalSolutionTrunc`,
  `TauCeti.hasDerivAt_deriv_rankOneFormalSolutionTrunc`: the first two derivatives of the
  truncation.
* `TauCeti.isBigO_rankOneFormalSolutionTrunc_residual_sub`: for arbitrary coefficients, the
  residual of the truncation after `N` terms is, up to `O(exp(κ e^ζ + (μ + 1 - N) ζ))`, given by
  the first `N + 1` coefficients of the formal operator applied to the `N`-term truncation of the
  series.
* `TauCeti.isBigO_rankOneFormalSolutionTrunc_residual`,
  `TauCeti.isBigO_rankOneFormalSolutionTrunc_rankOneCoeff_residual`: for a formal solution the
  residual of the truncation after `N` terms is `O(exp(κ e^ζ + (μ + 1 - N) ζ))` as `Re ζ → +∞`,
  that is `O(e^{κ z} z^{μ - N - 1})` in the original variable.

## Implementation notes

The truncation is `exp(κ e^ζ + μ ζ) p(e^{-ζ})` for the polynomial `p` of the first `N`
coefficients, and `d/dζ` acts on `p(e^{-ζ})` as `-θ`. Multiplied by `e^{-2ζ}`, the residual is
therefore `exp(κ e^ζ + μ ζ)` times the formal operator, applied to `p` and evaluated at `e^{-ζ}`,
up to the errors in the expansions of `f` and `g`.

## References

* NIST Digital Library of Mathematical Functions, §2.7(ii), equations (2.7.7)–(2.7.11),
  <https://dlmf.nist.gov/2.7.ii>.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted
  A K Peters, 1997. Chapter 7, §§1–2.
-/

public section

open Bornology Filter Finset Asymptotics PowerSeries
open scoped Topology Complex

namespace TauCeti

/-! ### The formal operator -/

section Formal

variable {R : Type*} [CommRing R]

/-- The operator obtained by substituting a formal solution `exp(κ z) z^μ ∑ aₛ z⁻ˢ` into
`w'' + f(z) w' + g(z) w = 0`, where `f(z) = ∑ fₛ z⁻ˢ` and `g(z) = ∑ gₛ z⁻ˢ` are the formal series
`F` and `G` in the variable `X = z⁻¹`. With `θ = X d/dX`, it is

`A ↦ X² (θ - μ) (θ - μ + 1) A - X (2κ + F) (θ - μ) A + (κ² + κ F + G) A`,

which is `z^{-μ} exp(-κ z)` times the left-hand side of the equation evaluated at
`exp(κ z) z^μ A(z⁻¹)`. The formal series is a formal solution when this operator vanishes. The
operator is linear in `A`, so linear combinations of formal solutions are formal solutions. -/
noncomputable def rankOneOperator (F G : R⟦X⟧) (κ μ : R) : R⟦X⟧ →ₗ[R] R⟦X⟧ where
  toFun A := X ^ 2 * (X * d⁄dX (X * d⁄dX A - C μ * A) - C (μ - 1) * (X * d⁄dX A - C μ * A)) -
    X * (C (2 * κ) + F) * (X * d⁄dX A - C μ * A) + (C (κ ^ 2) + C κ * F + G) * A
  map_add' A B := by
    simp only [map_add, map_sub, Derivation.leibniz, smul_eq_mul]
    ring
  map_smul' c A := by
    simp only [Derivation.map_smul, mul_smul_comm, ← smul_sub, ← smul_add, RingHom.id_apply]

theorem rankOneOperator_apply (F G : R⟦X⟧) (κ μ : R) (A : R⟦X⟧) :
    rankOneOperator F G κ μ A =
      X ^ 2 * (X * d⁄dX (X * d⁄dX A - C μ * A) - C (μ - 1) * (X * d⁄dX A - C μ * A)) -
        X * (C (2 * κ) + F) * (X * d⁄dX A - C μ * A) + (C (κ ^ 2) + C κ * F + G) * A := by
  rw [rankOneOperator, LinearMap.coe_mk, AddHom.coe_mk]

/-- If `Xⁿ ∣ A`, the operator applied to `A` agrees with `(κ² + κ F + G) A` modulo `Xⁿ⁺¹`: the
coefficient of `Xᵐ` in the operator depends on `aₘ` only through `(κ² + κ f₀ + g₀) aₘ`. -/
private lemma X_pow_succ_dvd_rankOneOperator_sub (F G : R⟦X⟧) (κ μ : R) {n : ℕ} {A : R⟦X⟧}
    (hA : X ^ n ∣ A) :
    X ^ (n + 1) ∣ rankOneOperator F G κ μ A - (C (κ ^ 2) + C κ * F + G) * A := by
  have h₁ := X_pow_dvd_X_mul_derivative_sub_C_mul hA μ
  have h₂ := X_pow_dvd_X_mul_derivative_sub_C_mul h₁ (μ - 1)
  rw [rankOneOperator_apply, add_sub_cancel_right]
  refine dvd_sub ?_ ?_
  · have h : (X : R⟦X⟧) ^ (n + 1) ∣ X ^ 2 * X ^ n := by
      rw [← pow_add]; exact pow_dvd_pow X (by omega)
    exact h.trans (mul_dvd_mul_left _ h₂)
  · rw [pow_succ', mul_assoc]
    exact mul_dvd_mul_left X (dvd_mul_of_dvd_right h₁ _)

/-- The coefficient of `Xⁿ⁺¹` in a product, with the term of the constant coefficient of the
first factor split off. -/
private lemma coeff_succ_mul_eq_add_sum (F A : R⟦X⟧) (n : ℕ) :
    coeff (n + 1) (F * A) =
      coeff 0 F * coeff (n + 1) A + ∑ j ∈ range (n + 1), coeff (n + 1 - j) F * coeff j A := by
  rw [mul_comm, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ,
    Nat.sub_self, add_comm]
  simp only [mul_comm (coeff _ A)]

/-- The constant coefficient of the operator is `(κ² + κ f₀ + g₀) a₀`: it vanishes for `a₀ ≠ 0`
exactly when `κ` is a root of the characteristic equation `κ² + f₀ κ + g₀ = 0` (DLMF 2.7.9). -/
theorem coeff_zero_rankOneOperator (F G : R⟦X⟧) (κ μ : R) (A : R⟦X⟧) :
    coeff 0 (rankOneOperator F G κ μ A) =
      (κ ^ 2 + κ * coeff 0 F + coeff 0 G) * coeff 0 A := by
  simp [rankOneOperator_apply, coeff_zero_eq_constantCoeff]

/-- The coefficient of `X` in the operator. When `κ² + κ f₀ + g₀ = 0` it is
`(μ (f₀ + 2κ) + κ f₁ + g₁) a₀`, so for `a₀ ≠ 0` and a simple root `κ`, `f₀ + 2κ ≠ 0`, it vanishes
exactly when `μ` is given by DLMF 2.7.10. -/
theorem coeff_one_rankOneOperator (F G : R⟦X⟧) (κ μ : R) (A : R⟦X⟧) :
    coeff 1 (rankOneOperator F G κ μ A) =
      (μ * (coeff 0 F + 2 * κ) + κ * coeff 1 F + coeff 1 G) * coeff 0 A +
        (κ ^ 2 + κ * coeff 0 F + coeff 0 G) * coeff 1 A := by
  simp [rankOneOperator_apply, pow_two, mul_assoc, coeff_succ_X_mul, coeff_one_mul,
    coeff_zero_eq_constantCoeff_apply]
  ring

/-- The coefficient of `Xˢ⁺²` in the operator. The terms in `aₛ₊₂` and `aₛ₊₁` are displayed
separately; when `κ² + κ f₀ + g₀ = 0` and `μ (f₀ + 2κ) + κ f₁ + g₁ = 0` they combine to
`-(s + 1) (f₀ + 2κ) aₛ₊₁`, which gives the recursion of DLMF 2.7.11. -/
theorem coeff_add_two_rankOneOperator (F G : R⟦X⟧) (κ μ : R) (A : R⟦X⟧) (s : ℕ) :
    coeff (s + 2) (rankOneOperator F G κ μ A) =
      (κ ^ 2 + κ * coeff 0 F + coeff 0 G) * coeff (s + 2) A +
        ((κ * coeff 1 F + coeff 1 G) - (coeff 0 F + 2 * κ) * (s + 1 - μ)) * coeff (s + 1) A +
        (s + 1 - μ) * (s - μ) * coeff s A +
        ∑ j ∈ range (s + 1), (κ * coeff (s + 2 - j) F + coeff (s + 2 - j) G -
          (j - μ) * coeff (s + 1 - j) F) * coeff j A := by
  have h₂ : s + 2 = s + 1 + 1 := rfl
  have h₁ : s + 1 + 1 - (s + 1) = 1 := by omega
  -- split off the constant factors, then the endpoint terms of the convolutions
  rw [rankOneOperator_apply, map_add, map_sub, coeff_X_pow_mul, h₂, mul_assoc, coeff_succ_X_mul,
    add_mul, add_mul, add_mul, mul_assoc (C κ), map_add, map_add, map_add, coeff_C_mul,
    coeff_C_mul, coeff_C_mul, coeff_succ_mul_eq_add_sum, coeff_succ_mul_eq_add_sum,
    coeff_succ_mul_eq_add_sum, sum_range_succ (n := s + 1), sum_range_succ (n := s + 1), h₁]
  simp only [coeff_X_mul_derivative_sub_C_mul]
  have hsum : κ * ∑ j ∈ range (s + 1), coeff (s + 1 + 1 - j) F * coeff j A +
      ∑ j ∈ range (s + 1), coeff (s + 1 + 1 - j) G * coeff j A -
      ∑ j ∈ range (s + 1), coeff (s + 1 - j) F * ((j - μ) * coeff j A) =
      ∑ j ∈ range (s + 1), (κ * coeff (s + 1 + 1 - j) F + coeff (s + 1 + 1 - j) G -
        (j - μ) * coeff (s + 1 - j) F) * coeff j A := by
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun j _ ↦ by ring
  push_cast
  linear_combination hsum

end Formal

/-! ### The coefficients of the formal solutions -/

section Coefficients

variable {K : Type*} [Field K]

/-- The candidate coefficients `aₛ` of a formal solution `exp(κ z) z^μ ∑ aₛ z⁻ˢ` of
`w'' + f(z) w' + g(z) w = 0`, where `f(z) = ∑ fₛ z⁻ˢ` and `g(z) = ∑ gₛ z⁻ˢ` are the formal series
`F` and `G`, normalized by `a₀ = 1` and defined by solving the recursion of DLMF 2.7.11,

`(f₀ + 2κ) s aₛ = (s - μ) (s - 1 - μ) aₛ₋₁ + ∑_{k=1}^{s} (κ fₖ₊₁ + gₖ₊₁ - (s - k - μ) fₖ) aₛ₋ₖ`,

for `aₛ`. The sequence is defined for all parameters. When `f₀ + 2κ ≠ 0` it satisfies this
recursion (`TauCeti.mul_rankOneCoeff`); for a root `κ` of the characteristic equation
`κ² + f₀ κ + g₀ = 0` this says that `κ` differs from the other root `-f₀ - κ`. It gives a formal
solution when moreover `κ` is a root of the characteristic equation and `μ` is given by
DLMF 2.7.10 (`TauCeti.rankOneOperator_mk_rankOneCoeff`). -/
noncomputable def rankOneCoeff (F G : K⟦X⟧) (κ μ : K) : ℕ → K
  | 0 => 1
  | s + 1 => ((coeff 0 F + 2 * κ) * (s + 1))⁻¹ *
      ((s + 1 - μ) * (s - μ) * rankOneCoeff F G κ μ s +
        ∑ j : Fin (s + 1), (κ * coeff (s + 2 - j) F + coeff (s + 2 - j) G -
          (j - μ) * coeff (s + 1 - j) F) * rankOneCoeff F G κ μ j)

@[simp]
theorem rankOneCoeff_zero (F G : K⟦X⟧) (κ μ : K) : rankOneCoeff F G κ μ 0 = 1 := by
  rw [rankOneCoeff]

theorem rankOneCoeff_succ (F G : K⟦X⟧) (κ μ : K) (s : ℕ) :
    rankOneCoeff F G κ μ (s + 1) = ((coeff 0 F + 2 * κ) * (s + 1))⁻¹ *
      ((s + 1 - μ) * (s - μ) * rankOneCoeff F G κ μ s +
        ∑ j ∈ range (s + 1), (κ * coeff (s + 2 - j) F + coeff (s + 2 - j) G -
          (j - μ) * coeff (s + 1 - j) F) * rankOneCoeff F G κ μ j) := by
  rw [rankOneCoeff, Fin.sum_univ_eq_sum_range (fun j ↦ (κ * coeff (s + 2 - j) F +
    coeff (s + 2 - j) G - (j - μ) * coeff (s + 1 - j) F) * rankOneCoeff F G κ μ j)]

/-- The sum of the recursion of DLMF 2.7.11, indexed by the earlier coefficient. -/
private lemma sum_Icc_eq_sum_range (F G : K⟦X⟧) (κ μ : K) (a : ℕ → K) (s : ℕ) :
    ∑ k ∈ Icc 1 (s + 1), (κ * coeff (k + 1) F + coeff (k + 1) G -
        (s + 1 - k - μ) * coeff k F) * a (s + 1 - k) =
      ∑ j ∈ range (s + 1), (κ * coeff (s + 2 - j) F + coeff (s + 2 - j) G -
        (j - μ) * coeff (s + 1 - j) F) * a j := by
  rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, ← sum_range_reflect]
  refine sum_congr (by simp) fun k hk ↦ ?_
  have hk := mem_range.1 hk
  have e₁ : 1 + (s + 1 + 1 - 1 - 1 - k) = s + 1 - k := by omega
  have e₂ : s + 2 - k = s + 1 - k + 1 := by omega
  have e₃ : s + 1 - (s + 1 - k) = k := by omega
  rw [e₁, e₂, e₃, Nat.cast_sub (by omega : k ≤ s + 1)]
  push_cast
  ring

variable [CharZero K]

/-- The recursion of `TauCeti.rankOneCoeff` with the sum indexed by the earlier coefficient. -/
private lemma mul_rankOneCoeff_succ {F G : K⟦X⟧} {κ : K} (hne : coeff 0 F + 2 * κ ≠ 0) (μ : K)
    (s : ℕ) : (coeff 0 F + 2 * κ) * (s + 1) * rankOneCoeff F G κ μ (s + 1) =
      (s + 1 - μ) * (s - μ) * rankOneCoeff F G κ μ s +
        ∑ j ∈ range (s + 1), (κ * coeff (s + 2 - j) F + coeff (s + 2 - j) G -
          (j - μ) * coeff (s + 1 - j) F) * rankOneCoeff F G κ μ j := by
  rw [rankOneCoeff_succ, ← mul_assoc,
    mul_inv_cancel₀ (mul_ne_zero hne (Nat.cast_add_one_ne_zero s)), one_mul]

/-- When `f₀ + 2κ ≠ 0`, the coefficients `TauCeti.rankOneCoeff` satisfy the recursion DLMF 2.7.11,
`(f₀ + 2κ) s aₛ = (s - μ) (s - 1 - μ) aₛ₋₁ + ∑_{k=1}^{s} (κ fₖ₊₁ + gₖ₊₁ - (s - k - μ) fₖ) aₛ₋ₖ`,
here at `s + 1` for `s ≥ 0`. -/
theorem mul_rankOneCoeff {F G : K⟦X⟧} {κ : K} (hne : coeff 0 F + 2 * κ ≠ 0) (μ : K) (s : ℕ) :
    (coeff 0 F + 2 * κ) * (s + 1) * rankOneCoeff F G κ μ (s + 1) =
      (s + 1 - μ) * (s - μ) * rankOneCoeff F G κ μ s +
        ∑ k ∈ Icc 1 (s + 1), (κ * coeff (k + 1) F + coeff (k + 1) G -
          (s + 1 - k - μ) * coeff k F) * rankOneCoeff F G κ μ (s + 1 - k) := by
  rw [mul_rankOneCoeff_succ hne, sum_Icc_eq_sum_range]

/-- When `f₀ + 2κ ≠ 0`, the recursion of DLMF 2.7.11 and `a₀ = 1` determine the sequence: any
solution `a` is `TauCeti.rankOneCoeff`. -/
theorem eq_rankOneCoeff_of_forall_mul_eq {F G : K⟦X⟧} {κ μ : K} {a : ℕ → K} (ha₀ : a 0 = 1)
    (hne : coeff 0 F + 2 * κ ≠ 0)
    (ha : ∀ s : ℕ, (coeff 0 F + 2 * κ) * (s + 1) * a (s + 1) =
      (s + 1 - μ) * (s - μ) * a s + ∑ k ∈ Icc 1 (s + 1), (κ * coeff (k + 1) F + coeff (k + 1) G -
        (s + 1 - k - μ) * coeff k F) * a (s + 1 - k)) :
    a = rankOneCoeff F G κ μ := by
  funext s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    rcases s with _ | s
    · rw [ha₀, rankOneCoeff_zero]
    have h := ha s
    rw [sum_Icc_eq_sum_range,
      sum_congr rfl fun j hj ↦ by rw [ih j (by have := mem_range.1 hj; omega)], ih s (by omega),
      ← mul_rankOneCoeff_succ hne] at h
    exact mul_left_cancel₀ (mul_ne_zero hne (Nat.cast_add_one_ne_zero s)) h

/-- **Formal solutions at an irregular singularity of rank one** (DLMF 2.7.8–2.7.11). If `κ` is a
root of the characteristic equation `κ² + f₀ κ + g₀ = 0` (2.7.9) different from the other root,
that is `f₀ + 2κ ≠ 0`, and `μ (f₀ + 2κ) = -(κ f₁ + g₁)` (2.7.10), then the series
`exp(κ z) z^μ ∑ aₛ z⁻ˢ` with the coefficients `TauCeti.rankOneCoeff` of 2.7.11 is a formal solution
of `w'' + f(z) w' + g(z) w = 0`. -/
theorem rankOneOperator_mk_rankOneCoeff {F G : K⟦X⟧} {κ μ : K}
    (hκ : κ ^ 2 + κ * coeff 0 F + coeff 0 G = 0) (hne : coeff 0 F + 2 * κ ≠ 0)
    (hμ : μ * (coeff 0 F + 2 * κ) + κ * coeff 1 F + coeff 1 G = 0) :
    rankOneOperator F G κ μ (mk (rankOneCoeff F G κ μ)) = 0 := by
  ext n
  rw [map_zero]
  rcases n with _ | _ | s
  · rw [coeff_zero_rankOneOperator, hκ, zero_mul]
  · rw [coeff_one_rankOneOperator, hκ, hμ, zero_mul, zero_mul, add_zero]
  · rw [coeff_add_two_rankOneOperator, hκ, zero_mul, zero_add]
    simp only [coeff_mk]
    linear_combination rankOneCoeff F G κ μ (s + 1) * hμ - mul_rankOneCoeff_succ (G := G) hne μ s

/-- The normalized formal solution is unique: for fixed `κ` and `μ` with `f₀ + 2κ ≠ 0`, if
`exp(κ z) z^μ ∑ bₛ z⁻ˢ` is a formal solution with `b₀ = 1`, then `bₛ` are the coefficients
`TauCeti.rankOneCoeff` of DLMF 2.7.11. The conditions 2.7.9 and 2.7.10 on `κ` and `μ` are then the
constant and linear coefficients of the equation `rankOneOperator F G κ μ (mk b) = 0`. -/
theorem eq_rankOneCoeff_of_rankOneOperator_eq_zero {F G : K⟦X⟧} {κ μ : K} {b : ℕ → K}
    (hb : rankOneOperator F G κ μ (mk b) = 0) (hb₀ : b 0 = 1) (hne : coeff 0 F + 2 * κ ≠ 0) :
    b = rankOneCoeff F G κ μ := by
  have h₀ := coeff_zero_rankOneOperator F G κ μ (mk b)
  have h₁ := coeff_one_rankOneOperator F G κ μ (mk b)
  rw [hb, map_zero, coeff_mk, hb₀, mul_one] at h₀
  rw [hb, map_zero, coeff_mk, coeff_mk, hb₀, mul_one, ← h₀, zero_mul, add_zero] at h₁
  refine eq_rankOneCoeff_of_forall_mul_eq hb₀ hne fun s ↦ ?_
  have h := coeff_add_two_rankOneOperator F G κ μ (mk b) s
  rw [hb, map_zero, ← h₀, zero_mul, zero_add] at h
  simp only [coeff_mk] at h
  rw [sum_Icc_eq_sum_range]
  linear_combination h - b (s + 1) * h₁

end Coefficients

/-! ### Truncated formal solutions in logarithmic coordinates -/

/-- The truncation after `N` terms of the formal solution `exp(κ z) z^μ ∑ aₛ z⁻ˢ` of
`w'' + f(z) w' + g(z) w = 0` at an irregular singularity of rank one at infinity, written in the
logarithmic coordinate `z = exp ζ`: `exp(κ e^ζ + μ ζ) ∑_{s<N} aₛ e^{-sζ}`. In this coordinate the
power `z^μ = exp(μ ζ)` needs no choice of branch, and the function is entire. The coefficients `a`
are arbitrary; they are those of a formal solution for `a = TauCeti.rankOneCoeff F G κ μ`. -/
noncomputable def rankOneFormalSolutionTrunc (κ μ : ℂ) (a : ℕ → ℂ) (N : ℕ) (ζ : ℂ) : ℂ :=
  cexp (κ * cexp ζ + μ * ζ) * ∑ s ∈ range N, a s * cexp (-(s * ζ))

theorem rankOneFormalSolutionTrunc_def (κ μ : ℂ) (a : ℕ → ℂ) (N : ℕ) (ζ : ℂ) :
    rankOneFormalSolutionTrunc κ μ a N ζ =
      cexp (κ * cexp ζ + μ * ζ) * ∑ s ∈ range N, a s * cexp (-(s * ζ)) := by
  rw [rankOneFormalSolutionTrunc]

@[simp]
theorem rankOneFormalSolutionTrunc_zero (κ μ : ℂ) (a : ℕ → ℂ) :
    rankOneFormalSolutionTrunc κ μ a 0 = 0 := by
  ext ζ
  simp [rankOneFormalSolutionTrunc]

/-- The truncation after `N + 1` terms adds the term `a_N exp(κ e^ζ + (μ - N) ζ)`. -/
theorem rankOneFormalSolutionTrunc_succ (κ μ : ℂ) (a : ℕ → ℂ) (N : ℕ) (ζ : ℂ) :
    rankOneFormalSolutionTrunc κ μ a (N + 1) ζ =
      rankOneFormalSolutionTrunc κ μ a N ζ + a N * cexp (κ * cexp ζ + (μ - N) * ζ) := by
  rw [rankOneFormalSolutionTrunc, rankOneFormalSolutionTrunc, sum_range_succ, mul_add,
    mul_left_comm, ← Complex.exp_add]
  ring_nf

section Analytic

/-- `ζ ↦ p(e^{-ζ})` has derivative `-(θ p)(e^{-ζ})`, with `θ = X d/dX`. -/
private lemma hasDerivAt_eval_exp_neg (p : Polynomial ℂ) (ζ : ℂ) :
    HasDerivAt (fun ζ ↦ p.eval (cexp (-ζ)))
      (-(Polynomial.X * Polynomial.derivative p).eval (cexp (-ζ))) ζ := by
  have h := (p.hasDerivAt (cexp (-ζ))).comp ζ ((hasDerivAt_neg ζ).cexp)
  refine h.congr_deriv ?_
  rw [Polynomial.eval_mul, Polynomial.eval_X]
  ring

/-- The function `exp(κ e^ζ + μ ζ) p(e^{-ζ})` for a polynomial `p`. -/
private noncomputable def expEval (κ μ : ℂ) (p : Polynomial ℂ) (ζ : ℂ) : ℂ :=
  cexp (κ * cexp ζ + μ * ζ) * p.eval (cexp (-ζ))

private lemma rankOneFormalSolutionTrunc_eq_expEval (κ μ : ℂ) (a : ℕ → ℂ) (N : ℕ) :
    rankOneFormalSolutionTrunc κ μ a N = expEval κ μ (trunc N (mk a)) := by
  ext ζ
  rw [rankOneFormalSolutionTrunc, expEval, eval_trunc]
  congr 1
  refine sum_congr rfl fun s _ ↦ ?_
  rw [coeff_mk, ← Complex.exp_natCast_mul, mul_neg]

private lemma hasDerivAt_cexp_mul_cexp_add (κ μ ζ : ℂ) :
    HasDerivAt (fun ζ ↦ cexp (κ * cexp ζ + μ * ζ))
      (cexp (κ * cexp ζ + μ * ζ) * (κ * cexp ζ + μ)) ζ := by
  have h := (((Complex.hasDerivAt_exp ζ).const_mul κ).add ((hasDerivAt_id ζ).const_mul μ)).cexp
  simpa using h

/-- The first derivative of `exp(κ e^ζ + μ ζ) p(e^{-ζ})`. -/
private lemma hasDerivAt_expEval (κ μ : ℂ) (p : Polynomial ℂ) (ζ : ℂ) :
    HasDerivAt (expEval κ μ p) (cexp (κ * cexp ζ + μ * ζ) *
      ((κ * cexp ζ + μ) * p.eval (cexp (-ζ)) -
        (Polynomial.X * Polynomial.derivative p).eval (cexp (-ζ)))) ζ :=
  ((hasDerivAt_cexp_mul_cexp_add κ μ ζ).mul (hasDerivAt_eval_exp_neg p ζ)).congr_deriv (by ring)

/-- The second derivative of `exp(κ e^ζ + μ ζ) p(e^{-ζ})`. -/
private lemma hasDerivAt_deriv_expEval (κ μ : ℂ) (p : Polynomial ℂ) (ζ : ℂ) :
    HasDerivAt (deriv (expEval κ μ p)) (cexp (κ * cexp ζ + μ * ζ) *
      (((κ * cexp ζ + μ) ^ 2 + κ * cexp ζ) * p.eval (cexp (-ζ)) -
        2 * (κ * cexp ζ + μ) * (Polynomial.X * Polynomial.derivative p).eval (cexp (-ζ)) +
        (Polynomial.X * Polynomial.derivative (Polynomial.X * Polynomial.derivative p)).eval
          (cexp (-ζ)))) ζ := by
  have hd : deriv (expEval κ μ p) = fun ζ ↦ cexp (κ * cexp ζ + μ * ζ) *
      ((κ * cexp ζ + μ) * p.eval (cexp (-ζ)) -
        (Polynomial.X * Polynomial.derivative p).eval (cexp (-ζ))) :=
    funext fun ζ ↦ (hasDerivAt_expEval κ μ p ζ).deriv
  rw [hd]
  exact ((hasDerivAt_cexp_mul_cexp_add κ μ ζ).mul
    (((((Complex.hasDerivAt_exp ζ).const_mul κ).add_const μ).mul
      (hasDerivAt_eval_exp_neg p ζ)).sub
        (hasDerivAt_eval_exp_neg (Polynomial.X * Polynomial.derivative p) ζ))).congr_deriv
    (by simp only [Pi.mul_apply, Pi.sub_apply]; ring)

/-- The value at `e^{-ζ}` of the truncation of `θ^j A`, for `θ = X d/dX` and `A = ∑ aₛ Xˢ`, is
`∑_{s<N} sʲ aₛ e^{-sζ}`. -/
private lemma eval_trunc_X_mul_derivative_mk (j : ℕ) (a : ℕ → ℂ) (N : ℕ) (ζ : ℂ) :
    (trunc N ((fun A ↦ X * d⁄dX A)^[j] (mk a))).eval (cexp (-ζ)) =
      ∑ s ∈ range N, (s : ℂ) ^ j * a s * cexp (-(s * ζ)) := by
  rw [eval_trunc]
  refine sum_congr rfl fun s _ ↦ ?_
  rw [← Complex.exp_natCast_mul, mul_neg]
  congr 1
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', coeff_X_mul_derivative, ih, pow_succ]; ring

/-- The derivative of the truncated formal solution: `d/dζ` multiplies the term
`aₛ exp(κ e^ζ + (μ - s) ζ)` by `κ e^ζ + μ - s`. -/
theorem hasDerivAt_rankOneFormalSolutionTrunc (κ μ : ℂ) (a : ℕ → ℂ) (N : ℕ) (ζ : ℂ) :
    HasDerivAt (rankOneFormalSolutionTrunc κ μ a N) (cexp (κ * cexp ζ + μ * ζ) *
      ∑ s ∈ range N, (κ * cexp ζ + μ - s) * a s * cexp (-(s * ζ))) ζ := by
  rw [rankOneFormalSolutionTrunc_eq_expEval]
  refine (hasDerivAt_expEval κ μ _ ζ).congr_deriv ?_
  have h₀ := eval_trunc_X_mul_derivative_mk 0 a N ζ
  have h₁ := eval_trunc_X_mul_derivative_mk 1 a N ζ
  simp only [Function.iterate_zero_apply, Function.iterate_one] at h₀ h₁
  rw [X_mul_derivative_trunc, h₀, h₁, mul_sum, ← sum_sub_distrib]
  congr 1
  exact sum_congr rfl fun s _ ↦ by ring

/-- The second derivative of the truncated formal solution: it multiplies the term
`aₛ exp(κ e^ζ + (μ - s) ζ)` by `(κ e^ζ + μ - s)² + κ e^ζ`. -/
theorem hasDerivAt_deriv_rankOneFormalSolutionTrunc (κ μ : ℂ) (a : ℕ → ℂ) (N : ℕ) (ζ : ℂ) :
    HasDerivAt (deriv (rankOneFormalSolutionTrunc κ μ a N)) (cexp (κ * cexp ζ + μ * ζ) *
      ∑ s ∈ range N, ((κ * cexp ζ + μ - s) ^ 2 + κ * cexp ζ) * a s * cexp (-(s * ζ))) ζ := by
  rw [rankOneFormalSolutionTrunc_eq_expEval]
  refine (hasDerivAt_deriv_expEval κ μ _ ζ).congr_deriv ?_
  have h₀ := eval_trunc_X_mul_derivative_mk 0 a N ζ
  have h₁ := eval_trunc_X_mul_derivative_mk 1 a N ζ
  have h₂ := eval_trunc_X_mul_derivative_mk 2 a N ζ
  simp only [Function.iterate_zero_apply, Function.iterate_succ_apply'] at h₀ h₁ h₂
  rw [X_mul_derivative_trunc, X_mul_derivative_trunc, h₀, h₁, h₂, mul_sum, mul_sum,
    ← sum_sub_distrib, ← sum_add_distrib]
  congr 1
  exact sum_congr rfl fun s _ ↦ by ring

/-- The truncated formal solution is entire. -/
theorem differentiable_rankOneFormalSolutionTrunc (κ μ : ℂ) (a : ℕ → ℂ) (N : ℕ) :
    Differentiable ℂ (rankOneFormalSolutionTrunc κ μ a N) :=
  fun ζ ↦ (hasDerivAt_rankOneFormalSolutionTrunc κ μ a N ζ).differentiableAt

/-- The operator `TauCeti.rankOneOperator` on polynomials `F`, `G`, `p`. -/
private noncomputable def residualPoly (κ μ : ℂ) (F G p : Polynomial ℂ) : Polynomial ℂ :=
  Polynomial.X ^ 2 *
      (Polynomial.X * Polynomial.derivative (Polynomial.X * Polynomial.derivative p) -
        Polynomial.C μ * (Polynomial.X * Polynomial.derivative p) -
        Polynomial.C (μ - 1) * (Polynomial.X * Polynomial.derivative p - Polynomial.C μ * p)) -
    Polynomial.X * (Polynomial.C (2 * κ) + F) *
      (Polynomial.X * Polynomial.derivative p - Polynomial.C μ * p) +
    (Polynomial.C (κ ^ 2) + Polynomial.C κ * F + G) * p

private lemma coe_residualPoly (κ μ : ℂ) (F G p : Polynomial ℂ) :
    ((residualPoly κ μ F G p : Polynomial ℂ) : ℂ⟦X⟧) =
      rankOneOperator (F : ℂ⟦X⟧) (G : ℂ⟦X⟧) κ μ (p : ℂ⟦X⟧) := by
  simp only [residualPoly, rankOneOperator_apply, Polynomial.coe_add, Polynomial.coe_sub,
    Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_C, ← derivative_coe,
    map_sub, ← smul_eq_C_mul, Derivation.map_smul]
  simp only [smul_eq_C_mul]
  ring

/-- The residual of `exp(κ e^ζ + μ ζ) p(e^{-ζ})` in
`W'' + (e^ζ f(e^ζ) - 1) W' + e^{2ζ} g(e^ζ) W = 0` is `exp(κ e^ζ + (μ + 2) ζ)` times the polynomial
operator, with `f`, `g` replaced by polynomials `Fp`, `Gp`, evaluated at `e^{-ζ}`, plus the
errors from replacing `f` and `g`. -/
private lemma residual_expEval_eq (f g : ℂ → ℂ) (κ μ : ℂ) (p Fp Gp : Polynomial ℂ) (ζ : ℂ) :
    deriv (deriv (expEval κ μ p)) ζ + (cexp ζ * f (cexp ζ) - 1) * deriv (expEval κ μ p) ζ +
        cexp (2 * ζ) * g (cexp ζ) * expEval κ μ p ζ =
      cexp (κ * cexp ζ + (μ + 2) * ζ) * ((residualPoly κ μ Fp Gp p).eval (cexp (-ζ)) -
        (Polynomial.X.eval (cexp (-ζ)) * (f (cexp ζ) - Fp.eval (cexp (-ζ)))) *
          (Polynomial.X * Polynomial.derivative p - Polynomial.C μ * p).eval (cexp (-ζ)) +
        (κ * (f (cexp ζ) - Fp.eval (cexp (-ζ))) + (g (cexp ζ) - Gp.eval (cexp (-ζ)))) *
          p.eval (cexp (-ζ))) := by
  have hE : cexp (κ * cexp ζ + (μ + 2) * ζ) = cexp (κ * cexp ζ + μ * ζ) * cexp ζ ^ 2 := by
    rw [← Complex.exp_natCast_mul, ← Complex.exp_add]; push_cast; ring_nf
  have h2 : cexp (2 * ζ) = cexp ζ ^ 2 := by rw [← Complex.exp_natCast_mul]; norm_num
  rw [(hasDerivAt_deriv_expEval κ μ p ζ).deriv, (hasDerivAt_expEval κ μ p ζ).deriv, expEval, hE,
    h2]
  simp only [residualPoly, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  generalize p.eval (cexp (-ζ)) = P
  generalize (Polynomial.derivative p).eval (cexp (-ζ)) = DP
  generalize (Polynomial.derivative (Polynomial.X * Polynomial.derivative p)).eval (cexp (-ζ)) = DDP
  rw [Complex.exp_neg]
  field_simp
  ring

/-- Replacing `F` and `G` by series congruent to them modulo `Xⁿ` changes the operator only
modulo `Xⁿ`. -/
private lemma X_pow_dvd_rankOneOperator_sub_rankOneOperator {n : ℕ} {F G F' G' : ℂ⟦X⟧}
    (hF : X ^ n ∣ F - F') (hG : X ^ n ∣ G - G') (κ μ : ℂ) (A : ℂ⟦X⟧) :
    X ^ n ∣ rankOneOperator F G κ μ A - rankOneOperator F' G' κ μ A := by
  have h : rankOneOperator F G κ μ A - rankOneOperator F' G' κ μ A =
      (F - F') * (-(X * (X * d⁄dX A - C μ * A)) + C κ * A) + (G - G') * A := by
    simp only [rankOneOperator_apply]; ring
  rw [h]
  exact dvd_add (dvd_mul_of_dvd_left hF _) (dvd_mul_of_dvd_left hG _)

/-- The polynomial operator with `F`, `G` truncated below degree `N + 1` agrees with the
operator applied to `p` below degree `N + 1`. -/
private lemma X_pow_dvd_residualPoly_sub_trunc (F G : ℂ⟦X⟧) (κ μ : ℂ) (p : Polynomial ℂ)
    (N : ℕ) : Polynomial.X ^ (N + 1) ∣ residualPoly κ μ (trunc (N + 1) F) (trunc (N + 1) G) p -
      trunc (N + 1) (rankOneOperator F G κ μ p) := by
  refine Polynomial.X_pow_dvd_iff.2 fun d hd ↦ ?_
  have h := X_pow_dvd_iff.1 (X_pow_dvd_rankOneOperator_sub_rankOneOperator
    (X_pow_dvd_sub_trunc (N + 1) F) (X_pow_dvd_sub_trunc (N + 1) G) κ μ p) d hd
  rw [map_sub, ← coe_residualPoly, Polynomial.coeff_coe, sub_eq_zero] at h
  rw [Polynomial.coeff_sub, coeff_trunc, ite_eq_left_of_eq_true _ _ (eq_true hd), h, sub_self]

/-- **The residual of a truncated formal solution.** Let `l ≤ comap re atTop`, so that `Re ζ → +∞`
along `l`, and let `f(e^ζ) = ∑_{k ≤ N} fₖ e^{-kζ} + O(e^{-(N+1)ζ})` and likewise for `g` along `l`,
with `fₖ`, `gₖ` the coefficients of `F` and `G`. For `l = comap re atTop` this is the expansion
`f(z) = ∑_{k ≤ N} fₖ z⁻ᵏ + O(z^{-N-1})` as `z → ∞` in all directions; for a log strip it is the
expansion in a sector. In the logarithmic coordinate `z = e^ζ` the equation
`w'' + f(z) w' + g(z) w = 0` reads `W'' + (e^ζ f(e^ζ) - 1) W' + e^{2ζ} g(e^ζ) W = 0`. For
arbitrary coefficients `aₛ`, the residual of the truncation `exp(κ e^ζ + μ ζ) ∑_{s<N} aₛ e^{-sζ}`
in this equation is `exp(κ e^ζ + (μ + 2) ζ) ∑_{m ≤ N} cₘ e^{-mζ}` up to an error
`O(exp(κ e^ζ + (μ + 1 - N) ζ))` along `l`, where `cₘ` are the first `N + 1` coefficients of the
formal operator `TauCeti.rankOneOperator` applied to the `N`-term truncation of `∑ aₛ Xˢ`. -/
theorem isBigO_rankOneFormalSolutionTrunc_residual_sub {f g : ℂ → ℂ} {F G : ℂ⟦X⟧} (κ μ : ℂ)
    (a : ℕ → ℂ) {N : ℕ} {l : Filter ℂ} (hl : l ≤ comap Complex.re atTop)
    (hf : (fun ζ ↦ f (cexp ζ) - ∑ k ∈ range (N + 1), coeff k F * (cexp ζ)⁻¹ ^ k) =O[l]
      fun ζ ↦ (cexp ζ)⁻¹ ^ (N + 1))
    (hg : (fun ζ ↦ g (cexp ζ) - ∑ k ∈ range (N + 1), coeff k G * (cexp ζ)⁻¹ ^ k) =O[l]
      fun ζ ↦ (cexp ζ)⁻¹ ^ (N + 1)) :
    (fun ζ ↦ deriv (deriv (rankOneFormalSolutionTrunc κ μ a N)) ζ +
        (cexp ζ * f (cexp ζ) - 1) * deriv (rankOneFormalSolutionTrunc κ μ a N) ζ +
        cexp (2 * ζ) * g (cexp ζ) * rankOneFormalSolutionTrunc κ μ a N ζ -
        cexp (κ * cexp ζ + (μ + 2) * ζ) * ∑ m ∈ range (N + 1),
          coeff m (rankOneOperator F G κ μ (trunc N (mk a))) * cexp (-(m * ζ)))
      =O[l] fun ζ ↦ cexp (κ * cexp ζ + (μ + 1 - N) * ζ) := by
  set p := trunc N (mk a)
  have hw := Complex.tendsto_exp_neg_comap_re_atTop.mono_left hl
  have hO (q : Polynomial ℂ) : (fun ζ ↦ q.eval (cexp (-ζ))) =O[l] fun _ ↦ (1 : ℂ) :=
    ((q.continuous.tendsto 0).comp hw).isBigO_one ℂ
  have hR (ζ : ℂ) : (trunc (N + 1) (rankOneOperator F G κ μ (p : ℂ⟦X⟧))).eval (cexp (-ζ)) =
      ∑ m ∈ range (N + 1), coeff m (rankOneOperator F G κ μ p) * cexp (-(m * ζ)) := by
    rw [eval_trunc]
    exact sum_congr rfl fun m _ ↦ by rw [← Complex.exp_natCast_mul, mul_neg]
  -- each term of the remainder is `O(e^{-(N + 1) ζ})`
  have hTR : (fun ζ ↦ (residualPoly κ μ (trunc (N + 1) F) (trunc (N + 1) G) p -
      trunc (N + 1) (rankOneOperator F G κ μ p)).eval (cexp (-ζ))) =O[l]
        fun ζ ↦ cexp (-ζ) ^ (N + 1) :=
    (Polynomial.isBigO_eval_of_X_pow_dvd
      (X_pow_dvd_residualPoly_sub_trunc F G κ μ p N)).comp_tendsto hw
  have hf' : (fun ζ ↦ f (cexp ζ) - (trunc (N + 1) F).eval (cexp (-ζ))) =O[l]
      fun ζ ↦ cexp (-ζ) ^ (N + 1) := by simpa only [eval_trunc, Complex.exp_neg] using hf
  have hg' : (fun ζ ↦ g (cexp ζ) - (trunc (N + 1) G).eval (cexp (-ζ))) =O[l]
      fun ζ ↦ cexp (-ζ) ^ (N + 1) := by simpa only [eval_trunc, Complex.exp_neg] using hg
  have hbound := (hTR.sub
    ((((hO Polynomial.X).mul hf').mul
      (hO (Polynomial.X * Polynomial.derivative p - Polynomial.C μ * p))).congr_right
        fun ζ ↦ by ring)).add
    (((hf'.const_mul_left κ).add hg').mul (hO p) |>.congr_right fun ζ ↦ by ring)
  rw [rankOneFormalSolutionTrunc_eq_expEval]
  refine (((isBigO_refl (fun ζ ↦ cexp (κ * cexp ζ + (μ + 2) * ζ)) _).mul hbound).congr
    (fun ζ ↦ ?_) fun ζ ↦ ?_)
  · rw [residual_expEval_eq f g κ μ p (trunc (N + 1) F) (trunc (N + 1) G), ← hR,
      Polynomial.eval_sub]
    ring
  rw [← Complex.exp_natCast_mul, ← Complex.exp_add]
  push_cast
  ring_nf

/-- If `κ² + κ f₀ + g₀ ≠ 0`, the first `N + 1` coefficients of the operator can only vanish when
`a₀ = ⋯ = a_N = 0`. -/
private lemma X_pow_dvd_of_coeff_rankOneOperator_eq_zero {F G : ℂ⟦X⟧} {κ μ : ℂ} {A : ℂ⟦X⟧}
    {N : ℕ} (hψ : κ ^ 2 + κ * coeff 0 F + coeff 0 G ≠ 0)
    (hres : ∀ m ≤ N, coeff m (rankOneOperator F G κ μ A) = 0) : X ^ (N + 1) ∣ A := by
  suffices h : ∀ m ≤ N + 1, X ^ m ∣ A from h _ le_rfl
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨R, hR⟩ := ih (by omega)
    have h := X_pow_dvd_iff.1 (X_pow_succ_dvd_rankOneOperator_sub F G κ μ ⟨R, hR⟩) m (by omega)
    have hX : ∀ Q : ℂ⟦X⟧, coeff m (X ^ m * Q) = constantCoeff Q := fun Q ↦ by
      simpa using coeff_X_pow_mul Q m 0
    rw [map_sub, hres m (by omega), zero_sub, neg_eq_zero, hR, mul_left_comm, hX,
      map_mul] at h
    have hR₀ : constantCoeff R = 0 := by
      refine (mul_eq_zero.1 h).resolve_left fun h' ↦ hψ ?_
      simpa [coeff_zero_eq_constantCoeff_apply] using h'
    rw [hR, pow_succ]
    exact mul_dvd_mul_left _ (X_dvd_iff.2 hR₀)

/-- If the first `N + 1` coefficients of the operator applied to `A` vanish, so do those of the
operator applied to the truncation of `A` below degree `N`. -/
private lemma coeff_rankOneOperator_trunc_eq_zero {F G : ℂ⟦X⟧} {κ μ : ℂ} {A : ℂ⟦X⟧} {N : ℕ}
    (hres : ∀ m ≤ N, coeff m (rankOneOperator F G κ μ A) = 0) {m : ℕ} (hm : m ≤ N) :
    coeff m (rankOneOperator F G κ μ (trunc N A)) = 0 := by
  by_cases hψ : κ ^ 2 + κ * coeff 0 F + coeff 0 G = 0
  · -- the operator is linear, and `A - trunc N A` is divisible by `X ^ N`
    have hdiv := X_pow_dvd_sub_trunc N A
    have hΨ : X ∣ C (κ ^ 2) + C κ * F + G :=
      X_dvd_iff.2 (by simpa [coeff_zero_eq_constantCoeff_apply] using hψ)
    have hsub := dvd_add (X_pow_succ_dvd_rankOneOperator_sub F G κ μ hdiv)
      (pow_succ' (X : ℂ⟦X⟧) N ▸ mul_dvd_mul hΨ hdiv)
    rw [sub_add_cancel, map_sub] at hsub
    have h := X_pow_dvd_iff.1 hsub m (by omega)
    rwa [map_sub, hres m hm, zero_sub, neg_eq_zero] at h
  · -- otherwise the truncation vanishes
    have hA := X_pow_dvd_of_coeff_rankOneOperator_eq_zero hψ hres
    have h : trunc N A = 0 := trunc_eq_zero_iff_le_order.2 <| nat_le_order_iff.2 fun d hd ↦
      X_pow_dvd_iff.1 hA d (by omega)
    rw [h, Polynomial.coe_zero, map_zero, map_zero]

/-- **The residual of a truncated formal solution**, sharp form. Let `l ≤ comap re atTop` and let
`f(e^ζ) = ∑_{k ≤ N} fₖ e^{-kζ} + O(e^{-(N+1)ζ})` and likewise for `g` along `l`, as in
`TauCeti.isBigO_rankOneFormalSolutionTrunc_residual_sub`. If the coefficients `aₛ` make the first
`N + 1` coefficients of the formal operator vanish, as those of a formal solution do, then the
truncation `exp(κ e^ζ + μ ζ) ∑_{s<N} aₛ e^{-sζ}` solves
`W'' + (e^ζ f(e^ζ) - 1) W' + e^{2ζ} g(e^ζ) W = 0` up to `O(exp(κ e^ζ + (μ + 1 - N) ζ))` along `l`.
In the variable `z = e^ζ` this is a residual `O(e^{κ z} z^{μ - N - 1})` of the original
equation. -/
theorem isBigO_rankOneFormalSolutionTrunc_residual {f g : ℂ → ℂ} {F G : ℂ⟦X⟧} {κ μ : ℂ}
    {a : ℕ → ℂ} {N : ℕ} {l : Filter ℂ} (hl : l ≤ comap Complex.re atTop)
    (hres : ∀ m ≤ N, coeff m (rankOneOperator F G κ μ (mk a)) = 0)
    (hf : (fun ζ ↦ f (cexp ζ) - ∑ k ∈ range (N + 1), coeff k F * (cexp ζ)⁻¹ ^ k) =O[l]
      fun ζ ↦ (cexp ζ)⁻¹ ^ (N + 1))
    (hg : (fun ζ ↦ g (cexp ζ) - ∑ k ∈ range (N + 1), coeff k G * (cexp ζ)⁻¹ ^ k) =O[l]
      fun ζ ↦ (cexp ζ)⁻¹ ^ (N + 1)) :
    (fun ζ ↦ deriv (deriv (rankOneFormalSolutionTrunc κ μ a N)) ζ +
        (cexp ζ * f (cexp ζ) - 1) * deriv (rankOneFormalSolutionTrunc κ μ a N) ζ +
        cexp (2 * ζ) * g (cexp ζ) * rankOneFormalSolutionTrunc κ μ a N ζ)
      =O[l] fun ζ ↦ cexp (κ * cexp ζ + (μ + 1 - N) * ζ) := by
  have h := isBigO_rankOneFormalSolutionTrunc_residual_sub κ μ a hl hf hg
  have hsum : ∀ ζ : ℂ, ∑ m ∈ range (N + 1),
      coeff m (rankOneOperator F G κ μ (trunc N (mk a))) * cexp (-(m * ζ)) = 0 := fun ζ ↦
    sum_eq_zero fun m hm ↦ by
      rw [coeff_rankOneOperator_trunc_eq_zero hres (Nat.lt_succ_iff.1 (mem_range.1 hm)), zero_mul]
  simpa only [hsum, mul_zero, sub_zero] using h

/-- The truncations of the normalized formal solution of DLMF 2.7.8, with the coefficients
`TauCeti.rankOneCoeff` of 2.7.11, solve the equation in logarithmic coordinates
`W'' + (e^ζ f(e^ζ) - 1) W' + e^{2ζ} g(e^ζ) W = 0` up to `O(exp(κ e^ζ + (μ + 1 - N) ζ))` along any
`l ≤ comap re atTop`, whenever `f(e^ζ)` and `g(e^ζ)` have the expansions `∑ fₖ e^{-kζ}` and
`∑ gₖ e^{-kζ}` to order `N` along `l`, `κ` is a simple root of `κ² + f₀ κ + g₀ = 0` and
`μ (f₀ + 2κ) = -(κ f₁ + g₁)`. -/
theorem isBigO_rankOneFormalSolutionTrunc_rankOneCoeff_residual {f g : ℂ → ℂ} {F G : ℂ⟦X⟧}
    {κ μ : ℂ} {N : ℕ} {l : Filter ℂ} (hl : l ≤ comap Complex.re atTop)
    (hκ : κ ^ 2 + κ * coeff 0 F + coeff 0 G = 0)
    (hne : coeff 0 F + 2 * κ ≠ 0) (hμ : μ * (coeff 0 F + 2 * κ) + κ * coeff 1 F + coeff 1 G = 0)
    (hf : (fun ζ ↦ f (cexp ζ) - ∑ k ∈ range (N + 1), coeff k F * (cexp ζ)⁻¹ ^ k) =O[l]
      fun ζ ↦ (cexp ζ)⁻¹ ^ (N + 1))
    (hg : (fun ζ ↦ g (cexp ζ) - ∑ k ∈ range (N + 1), coeff k G * (cexp ζ)⁻¹ ^ k) =O[l]
      fun ζ ↦ (cexp ζ)⁻¹ ^ (N + 1)) :
    (fun ζ ↦ deriv (deriv (rankOneFormalSolutionTrunc κ μ (rankOneCoeff F G κ μ) N)) ζ +
        (cexp ζ * f (cexp ζ) - 1) *
          deriv (rankOneFormalSolutionTrunc κ μ (rankOneCoeff F G κ μ) N) ζ +
        cexp (2 * ζ) * g (cexp ζ) * rankOneFormalSolutionTrunc κ μ (rankOneCoeff F G κ μ) N ζ)
      =O[l] fun ζ ↦ cexp (κ * cexp ζ + (μ + 1 - N) * ζ) :=
  isBigO_rankOneFormalSolutionTrunc_residual hl
    (fun m _ ↦ by rw [rankOneOperator_mk_rankOneCoeff hκ hne hμ, map_zero]) hf hg

end Analytic

/-! ### Checks -/

-- Expansions as `z → ∞` in all directions give the hypotheses along `comap re atTop` by
-- composition with `exp`, so the residual estimates hold uniformly in `Im ζ`.
example {f g : ℂ → ℂ} {F G : ℂ⟦X⟧} {κ μ : ℂ} {N : ℕ}
    (hκ : κ ^ 2 + κ * coeff 0 F + coeff 0 G = 0) (hne : coeff 0 F + 2 * κ ≠ 0)
    (hμ : μ * (coeff 0 F + 2 * κ) + κ * coeff 1 F + coeff 1 G = 0)
    (hf : (fun z ↦ f z - ∑ k ∈ range (N + 1), coeff k F * z⁻¹ ^ k) =O[cobounded ℂ]
      fun z ↦ z⁻¹ ^ (N + 1))
    (hg : (fun z ↦ g z - ∑ k ∈ range (N + 1), coeff k G * z⁻¹ ^ k) =O[cobounded ℂ]
      fun z ↦ z⁻¹ ^ (N + 1)) :
    (fun ζ ↦ deriv (deriv (rankOneFormalSolutionTrunc κ μ (rankOneCoeff F G κ μ) N)) ζ +
        (cexp ζ * f (cexp ζ) - 1) *
          deriv (rankOneFormalSolutionTrunc κ μ (rankOneCoeff F G κ μ) N) ζ +
        cexp (2 * ζ) * g (cexp ζ) * rankOneFormalSolutionTrunc κ μ (rankOneCoeff F G κ μ) N ζ)
      =O[comap Complex.re atTop] fun ζ ↦ cexp (κ * cexp ζ + (μ + 1 - N) * ζ) :=
  isBigO_rankOneFormalSolutionTrunc_rankOneCoeff_residual le_rfl hκ hne hμ
    (hf.comp_tendsto Complex.tendsto_exp_comap_re_atTop)
    (hg.comp_tendsto Complex.tendsto_exp_comap_re_atTop)

-- For `f(z) = -1 + 2z⁻²` and `g(z) = -z⁻² - 2z⁻³ + z⁻⁴` the characteristic roots are `0` and `1`,
-- both with `μ = 0`, and the solutions are `exp(1/z)` and `exp(z + 1/z)`; both normalized formal
-- series are the convergent nonterminating series `∑ z⁻ˢ/s!`.
example {κ : ℂ} (hκ : κ = 0 ∨ κ = 1) :
    rankOneCoeff (-1 + 2 * X ^ 2) (-X ^ 2 - 2 * X ^ 3 + X ^ 4) κ 0 =
      fun s ↦ ((s.factorial : ℂ))⁻¹ := by
  have hexp : (mk fun s ↦ ((s.factorial : ℂ))⁻¹) = PowerSeries.exp ℂ := by
    ext n
    simp [coeff_exp]
  have hE : d⁄dX (mk fun s ↦ ((s.factorial : ℂ))⁻¹) = mk fun s ↦ ((s.factorial : ℂ))⁻¹ := by
    rw [hexp, derivative_exp]
  have hne : coeff 0 (-1 + 2 * X ^ 2 : ℂ⟦X⟧) + 2 * κ ≠ 0 := by
    rcases hκ with rfl | rfl <;> norm_num [coeff_X_pow]
  refine (eq_rankOneCoeff_of_rankOneOperator_eq_zero ?_ (by simp) hne).symm
  simp only [rankOneOperator_apply, map_sub, map_mul, Derivation.leibniz, derivative_X,
    smul_eq_mul, hE]
  rcases hκ with rfl | rfl <;> simp [map_ofNat] <;> ring

end TauCeti
