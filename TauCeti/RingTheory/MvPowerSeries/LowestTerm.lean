/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Lowest terms of multivariate power series for a weight

For a weight `w : σ → ℕ` on the variables, a power series `f` has *lowest term* `c * X ^ m` if,
in every exponent `d` of weight at most that of `m`, the coefficient of `f` is that of the monomial
`c * X ^ m`. So `f` agrees with `c * X ^ m` up to weight `m.weight w`; the coefficient `c = 0` is
allowed. Lowest terms multiply: the lowest term of a product is the product of the lowest terms.

This is the bookkeeping by which the least valuations of coefficients of products of copies of a
series are computed: a product of factors whose lowest terms are known has a known coefficient in
the weight of the product of these terms.

## Main definitions and results

* `MvPowerSeries.IsLowestTerm w f m c`: `c * X ^ m` is the lowest term of `f` for the weight `w`.
* `MvPowerSeries.IsLowestTerm.coeff_eq`: the coefficient of `f` at `m` is `c`.
* `MvPowerSeries.IsLowestTerm.mul`, `MvPowerSeries.IsLowestTerm.prod`,
  `MvPowerSeries.IsLowestTerm.pow`: lowest terms of products and powers.

## References

* The definition and the rules for products are adapted from `New.IsLowestTerm`,
  `New.IsLowestTerm.mul`, `New.IsLowestTerm.prod` and `New.IsLowestTerm.pow` in
  `src/New/Derivatives/Sharpness/LeastValuation.lean` of
  <https://github.com/leanprover-community/riemann-hypothesis/tree/3ad0b4b58709>. There the
  coefficients form a commutative ring; here a commutative semiring suffices.
-/

public section

namespace MvPowerSeries

open Finset

variable {σ R : Type*} [CommSemiring R]

/-- `c * X ^ m` is the lowest term of `f` for the weight `w`: in every exponent of weight at most
that of `m`, the coefficient of `f` is that of the monomial `c * X ^ m` (here `c = 0` is
allowed). -/
def IsLowestTerm (w : σ → ℕ) (f : MvPowerSeries σ R) (m : σ →₀ ℕ) (c : R) : Prop :=
  ∀ d : σ →₀ ℕ, d.weight w ≤ m.weight w → coeff d f = coeff d (monomial m c)

theorem isLowestTerm_iff {w : σ → ℕ} {f : MvPowerSeries σ R} {m : σ →₀ ℕ} {c : R} :
    IsLowestTerm w f m c ↔
      ∀ d : σ →₀ ℕ, d.weight w ≤ m.weight w → coeff d f = coeff d (monomial m c) :=
  Iff.rfl

namespace IsLowestTerm

variable {w : σ → ℕ} {f g : MvPowerSeries σ R} {m m' : σ →₀ ℕ} {c c' : R}

/-- The coefficient of `f` at the exponent of its lowest term is the coefficient of that term. -/
theorem coeff_eq (hf : IsLowestTerm w f m c) : coeff m f = c := by
  simpa using hf m le_rfl

/-- Below the weight of its lowest term, `f` has only zero coefficients, apart from the
exponent `m` itself. -/
theorem coeff_eq_zero (hf : IsLowestTerm w f m c) {d : σ →₀ ℕ} (hd : d.weight w ≤ m.weight w)
    (hdm : d ≠ m) : coeff d f = 0 := by
  rw [hf d hd, coeff_monomial_ne hdm]

/-- A monomial is its own lowest term. -/
theorem monomial (w : σ → ℕ) (m : σ →₀ ℕ) (c : R) :
    IsLowestTerm w (MvPowerSeries.monomial m c) m c :=
  fun _ _ ↦ rfl

/-- The lowest term of `1` is `1 * X ^ 0`, for every weight. -/
theorem one (w : σ → ℕ) : IsLowestTerm w (1 : MvPowerSeries σ R) 0 1 := by
  simpa using monomial (R := R) w 0 1

/-- **Lowest terms multiply.** If `f` has lowest term `c * X ^ m` and `g` has lowest term
`c' * X ^ m'`, then `f * g` has lowest term `(c * c') * X ^ (m + m')`. -/
theorem mul (hf : IsLowestTerm w f m c) (hg : IsLowestTerm w g m' c') :
    IsLowestTerm w (f * g) (m + m') (c * c') := by
  classical
  intro e he
  -- Compare the two products at `e` term by term, over the splittings `x + y = e`.
  rw [← monomial_mul_monomial, coeff_mul, coeff_mul]
  refine sum_congr rfl fun ⟨x, y⟩ hxy ↦ ?_
  obtain rfl : x + y = e := mem_antidiagonal.1 hxy
  rw [map_add, map_add] at he
  by_cases hx : x.weight w ≤ m.weight w
  · by_cases hy : y.weight w ≤ m'.weight w
    · rw [hf x hx, hg y hy]
    · -- `y` is heavier than `m'`, so `x` is lighter than `m`, and both first factors vanish.
      rw [hf x hx, coeff_monomial_ne (fun h ↦ by subst h; omega), zero_mul, zero_mul]
  · -- `x` is heavier than `m`, so `y` is lighter than `m'`, and both second factors vanish.
    rw [hg y (by omega), coeff_monomial_ne (fun h ↦ by subst h; omega), mul_zero, mul_zero]

/-- If each factor `f i` has lowest term `c i * X ^ m i`, then their product has lowest term
`(∏ c i) * X ^ (∑ m i)`. -/
theorem prod {ι : Type*} {s : Finset ι} {f : ι → MvPowerSeries σ R} {m : ι → σ →₀ ℕ}
    {c : ι → R} (hf : ∀ i ∈ s, IsLowestTerm w (f i) (m i) (c i)) :
    IsLowestTerm w (∏ i ∈ s, f i) (∑ i ∈ s, m i) (∏ i ∈ s, c i) := by
  induction s using cons_induction with
  | empty => simpa using one w
  | cons i s hi ih =>
    simp only [prod_cons, sum_cons]
    exact (hf i (mem_cons_self i s)).mul (ih fun j hj ↦ hf j (mem_cons_of_mem hj))

/-- If `f` has lowest term `c * X ^ m`, then `f ^ k` has lowest term `c ^ k * X ^ (k • m)`. -/
theorem pow (hf : IsLowestTerm w f m c) (k : ℕ) : IsLowestTerm w (f ^ k) (k • m) (c ^ k) := by
  simpa using prod (s := range k) fun _ _ ↦ hf

end IsLowestTerm

end MvPowerSeries
