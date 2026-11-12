/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.PeriodPolynomial.CuspForm
public import TauCeti.NumberTheory.ModularForms.LFunction.Period
import TauCeti.Data.Fin.Rev

/-!
# The coefficients of a period polynomial are critical `L`-values

Let `f` be a cusp form of weight `k = w + 2` on `SL(2, ℤ)`. Expanding `(X - τY)ʷ` in its period
polynomial `r_f(X, Y) = ∫₀^{i∞} f(τ) (X - τY)ʷ dτ` writes `r_f` in terms of the periods
`rₙ(f) = ∫₀^{i∞} f(τ) τⁿ dτ = iⁿ⁺¹ Λ(f, n + 1)` (`TauCeti.cuspIntegral_mul_pow_zero_infty`):

`r_f(X, Y) = ∑_{n=0}^{w} (-1)ⁿ (w choose n) iⁿ⁺¹ Λ(f, n + 1) Xʷ⁻ⁿ Yⁿ`.

So the coefficients of `r_f` are, up to nonzero constants, the values of `L(f, s)` at the
critical integers `s = 1, …, w + 1`. The parity involution `P(X, Y) ↦ P(-X, Y)` multiplies the
monomial `Xʲ Yʷ⁻ʲ` by `(-1)ʲ`, so the even period polynomial `r_f^+` collects the critical values
`L(f, n + 1)` with `w - n` even and the odd period polynomial `r_f^-` those with `w - n` odd. In
particular `r_f^+` vanishes exactly when all the critical values `L(f, n + 1)` with `w - n` even
vanish, and similarly for `r_f^-`. So a single nonzero value `L(f, w + 1)` makes `r_f^+` nonzero,
and, for `w ≠ 0`, a single nonzero value `L(f, w)` makes `r_f^-` nonzero. This is the route to the
nonvanishing of the even and odd period polynomials of a Hecke eigenform: once the weight is large
enough, both points `w` and `w + 1` lie in the half-plane where the `L`-function of an eigenform
is an absolutely convergent Euler product.

## Main results

* `TauCeti.periodPolynomial_eq_sum`: `r_f` in the monomial basis, with the completed `L`-values
  `Λ(f, n + 1)` as coefficients.
* `TauCeti.binaryFormMonomialBasis_repr_periodPolynomial`: the coordinates of `r_f` in the
  monomial basis.
* `TauCeti.evenPeriodPolynomial_eq_zero_iff`, `TauCeti.oddPeriodPolynomial_eq_zero_iff`: `r_f^+`
  (respectively `r_f^-`) vanishes if and only if `L(f, n + 1) = 0` for every `n ≤ w` with `w - n`
  even (respectively odd).
* `TauCeti.evenPeriodPolynomial_ne_zero`, `TauCeti.oddPeriodPolynomial_ne_zero`: `r_f^+ ≠ 0` if
  `L(f, w + 1) ≠ 0`, and `r_f^- ≠ 0` if `w ≠ 0` and `L(f, w) ≠ 0`.

## References

* Y. I. Manin, *Periods of parabolic forms and p-adic Hecke series*, Mat. Sb. **92** (1973),
  378–401, §1.
* W. Kohnen and D. Zagier, *Modular forms with rational periods*, in *Modular Forms*
  (R. A. Rankin, ed.), Ellis Horwood, 1984, 197–249, §1.1.
-/

public section

open Complex MvPolynomial MulOpposite TauCeti.ModularSymbols
open scoped MatrixGroups

namespace TauCeti

variable {k : ℤ} {w : ℕ}

/-- **The period polynomial in the monomial basis.** The coefficient of `Xʲ Yʷ⁻ʲ` in the period
polynomial of a cusp form `f` of weight `k = w + 2` on `SL(2, ℤ)` is
`(-1)ʷ⁻ʲ (w choose j) iʷ⁻ʲ⁺¹ Λ(f, w - j + 1)`. -/
theorem periodPolynomial_eq_sum (hk : k = w + 2) (f : CuspForm 𝒮ℒ k) :
    (periodPolynomial hk f : homogeneousSubmodule (Fin 2) ℂ w) = ∑ j : Fin (w + 1),
      ((-1) ^ (w - j : ℕ) * (w.choose j : ℂ) * I ^ (w - j + 1 : ℕ) *
        ModularForm.Λ (by omega) f ((w - j : ℕ) + 1)) • binaryFormMonomialBasis ℂ w j := by
  rw [coe_periodPolynomial_eq_binaryFormDual hk f
    (F := CuspForm.mcast rfl f (MonoidHom.range_eq_map _).symm) (rfl), binaryFormDual_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  -- the period functional at `Xʷ⁻ʲ Yʲ` is the period `∫₀^{i∞} f(τ) τʷ⁻ʲ dτ`
  have h : periodIntegrand (CuspForm.mcast rfl f (MonoidHom.range_eq_map _).symm)
      (binaryFormMonomialBasis ℂ w (Fin.rev j)) = fun τ ↦ f τ * (τ : ℂ) ^ (w - j : ℕ) := by
    ext τ
    simp only [periodIntegrand_apply, coe_binaryFormMonomialBasis, Fin.val_rev]
    rw [show w + 1 - ((j : ℕ) + 1) = w - j by omega, Nat.sub_sub_self (by omega)]
    -- `CuspForm.mcast` does not change the underlying function, so `congr` closes that factor
    congr 1
    simp
  rw [LinearMap.comp_apply, periodMap_symbol, h, cuspIntegral_mul_pow_zero_infty (by omega)]
  ring_nf

/-- The coordinates of the period polynomial `r_f` in the monomial basis `Xʲ Yʷ⁻ʲ`. -/
theorem binaryFormMonomialBasis_repr_periodPolynomial (hk : k = w + 2) (f : CuspForm 𝒮ℒ k)
    (j : Fin (w + 1)) :
    (binaryFormMonomialBasis ℂ w).repr (periodPolynomial hk f) j =
      (-1) ^ (w - j : ℕ) * (w.choose j : ℂ) * I ^ (w - j + 1 : ℕ) *
        ModularForm.Λ (by omega) f ((w - j : ℕ) + 1) := by
  rw [periodPolynomial_eq_sum, Module.Basis.repr_sum_self]

/-- A coordinate of `r_f` in the monomial basis vanishes exactly when the corresponding critical
value of the `L`-function vanishes. -/
private theorem binaryFormMonomialBasis_repr_periodPolynomial_eq_zero_iff (hk : k = w + 2)
    (f : CuspForm 𝒮ℒ k) (j : Fin (w + 1)) :
    (binaryFormMonomialBasis ℂ w).repr (periodPolynomial hk f) j = 0 ↔
      ModularForm.L (by omega) f ((w - j : ℕ) + 1) = 0 := by
  rw [binaryFormMonomialBasis_repr_periodPolynomial, mul_eq_zero, or_iff_right,
    ModularForm.Λ_natCast_add_one_eq_zero_iff]
  have hj : (j : ℕ) ≤ w := Nat.lt_succ_iff.1 j.2
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
    (Nat.cast_ne_zero.2 (Nat.choose_pos hj).ne')) (pow_ne_zero _ I_ne_zero)

/-- **The even period polynomial vanishes exactly when the critical `L`-values `L(f, n + 1)`
with `w - n` even vanish.** -/
theorem evenPeriodPolynomial_eq_zero_iff (hk : k = w + 2) (f : CuspForm 𝒮ℒ k) :
    evenPeriodPolynomial hk f = 0 ↔
      ∀ n ≤ w, Even (w - n) → ModularForm.L (by omega) f (n + 1) = 0 := by
  rw [← Submodule.coe_eq_zero, ← LinearEquiv.map_eq_zero_iff (binaryFormMonomialBasis ℂ w).repr,
    Finsupp.ext_iff, ← Fin.forall_imp_sub_iff_forall_le]
  refine forall_congr' fun j ↦ ?_
  rw [Finsupp.zero_apply, binaryFormMonomialBasis_repr_evenPeriodPolynomial]
  split_ifs with hj
  · simp [hj, binaryFormMonomialBasis_repr_periodPolynomial_eq_zero_iff]
  · simp [hj]

/-- **The odd period polynomial vanishes exactly when the critical `L`-values `L(f, n + 1)`
with `w - n` odd vanish.** -/
theorem oddPeriodPolynomial_eq_zero_iff (hk : k = w + 2) (f : CuspForm 𝒮ℒ k) :
    oddPeriodPolynomial hk f = 0 ↔
      ∀ n ≤ w, Odd (w - n) → ModularForm.L (by omega) f (n + 1) = 0 := by
  rw [← Submodule.coe_eq_zero, ← LinearEquiv.map_eq_zero_iff (binaryFormMonomialBasis ℂ w).repr,
    Finsupp.ext_iff, ← Fin.forall_imp_sub_iff_forall_le]
  refine forall_congr' fun j ↦ ?_
  rw [Finsupp.zero_apply, binaryFormMonomialBasis_repr_oddPeriodPolynomial]
  split_ifs with hj
  · simp [hj]
  · simp [Nat.not_even_iff_odd.1 hj, binaryFormMonomialBasis_repr_periodPolynomial_eq_zero_iff]

/-- **A nonzero critical value makes the even period polynomial nonzero**: if `L(f, w + 1) ≠ 0`,
then `r_f^+ ≠ 0`. -/
theorem evenPeriodPolynomial_ne_zero (hk : k = w + 2) (f : CuspForm 𝒮ℒ k)
    (hL : ModularForm.L (by omega) f (w + 1) ≠ 0) : evenPeriodPolynomial hk f ≠ 0 :=
  fun h ↦ hL ((evenPeriodPolynomial_eq_zero_iff hk f).1 h w le_rfl (by simp))

/-- **A nonzero critical value makes the odd period polynomial nonzero**: if `w ≠ 0` and
`L(f, w) ≠ 0`, then `r_f^- ≠ 0`. -/
theorem oddPeriodPolynomial_ne_zero (hk : k = w + 2) (f : CuspForm 𝒮ℒ k) (hw : w ≠ 0)
    (hL : ModularForm.L (by omega) f w ≠ 0) : oddPeriodPolynomial hk f ≠ 0 := by
  refine fun h ↦ hL ?_
  have := (oddPeriodPolynomial_eq_zero_iff hk f).1 h (w - 1) (Nat.sub_le w 1)
    (by rw [Nat.sub_sub_self (Nat.one_le_iff_ne_zero.2 hw)]; exact odd_one)
  rwa [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hw), Nat.cast_one, sub_add_cancel] at this

end TauCeti
