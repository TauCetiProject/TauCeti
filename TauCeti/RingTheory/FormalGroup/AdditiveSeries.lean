/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.RingTheory.PowerSeries.Substitution

import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Basic
import TauCeti.RingTheory.MvPowerSeries.Basic
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# Additive power series

A power series `h(X)` over a commutative ring `R` is *additive* if `h(X + Y) = h(X) + h(Y)` in
`R⟦X, Y⟧`, that is, if it is an endomorphism of the additive formal group law `X + Y`. Writing
`h = ∑ cₙ Xⁿ`, the coefficient of `XⁱYʲ` in `h(X + Y)` is `(i + j).choose i * c_{i+j}`, so `h` is
additive exactly when `c₀ = 0` and `n.choose i * cₙ = 0` for all `0 < i < n`.

For instance, over a `ℚ`-algebra the additive series are the multiples `c₁ X`. If `p = 0` in `R`
for a prime `p`, the binomial coefficients `n.choose i`, `0 < i < n`, of `n ≥ 1` are all
divisible by `p` exactly when `n` is a power of `p`, and an integer prime to `p` is a unit in `R`.
So in that case `h` is additive exactly when its coefficients vanish away from the powers of `p`:

  `h = ∑_{k ≥ 0} b_k X^(p ^ k)`, `b_k = c_{p ^ k}`.

This coefficient description needs no other hypothesis on `R`: it may be the zero ring or have
nilpotents. If `R` is moreover Hausdorff, the displayed sum is a convergent sum for the
coefficientwise topology, and the additive series are exactly the sums of this form.

For `p = 2` this describes the freedom in the strict logarithm `g(X) = X + ⋯` of a commutative
formal group law `F` with `[2]_F = 0`, which satisfies `g(F(X, Y)) = g(X) + g(Y)`: composing `g`
with an additive series `h` with `c₁ = 1` gives another one, `h(g(F(X, Y))) = h(g(X)) + h(g(Y))`
by `PowerSeries.subst_add_of_subst_X_add_X_eq_add`.

## Main results

* `PowerSeries.coeff_subst_X_add_X`: the coefficient of `XⁱYʲ` in `h(X + Y)` is
  `(i + j).choose i * c_{i+j}`.
* `PowerSeries.subst_X_add_X_eq_add_iff`: `h(X + Y) = h(X) + h(Y)` exactly when `c₀ = 0` and
  `n.choose i * cₙ = 0` for `0 < i < n`.
* `PowerSeries.subst_add_of_subst_X_add_X_eq_add`: an additive series satisfies
  `h(a + b) = h(a) + h(b)` for all power series `a, b` that can be substituted.
* `PowerSeries.subst_X_add_X_eq_add_iff_of_natCast_eq_zero`: if `p = 0` in `R` for a prime `p`,
  `h` is additive exactly when `cₙ = 0` unless `n` is a power of `p`.
* `PowerSeries.WithPiTopology.subst_X_add_X_eq_add_iff_exists_hasSum`: if `p = 0` in `R` and `R` is
  Hausdorff, `h` is additive exactly when `h = ∑_k b_k X^(p ^ k)` for some `b : ℕ → R`.

## References

* M. Hazewinkel, *Formal Groups and Applications*, I §1.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1.
-/

public section

open Finsupp

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- The coefficient of `XⁱYʲ` in `h(X + Y)` is `(i + j).choose i` times the coefficient of
`X^(i + j)` in `h`. -/
theorem coeff_subst_X_add_X (h : R⟦X⟧) (i j : ℕ) :
    MvPowerSeries.coeff (single 0 i + single 1 j)
        (h.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) =
      (i + j).choose i * coeff (i + j) h := by
  rw [coeff_subst (HasSubst.of_constantCoeff_zero (by simp)), finsum_eq_single _ (i + j)]
  · simp [MvPowerSeries.coeff_X_add_X_pow, mul_comm]
  · intro n hn
    simp [MvPowerSeries.coeff_X_add_X_pow, Ne.symm hn]

/-- **The additive power series.** A power series `h` satisfies `h(X + Y) = h(X) + h(Y)` exactly
when its constant coefficient vanishes and `n.choose i` kills its coefficient of `Xⁿ` for every
`0 < i < n`. -/
theorem subst_X_add_X_eq_add_iff (h : R⟦X⟧) :
    h.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) =
        h.subst (MvPowerSeries.X 0) + h.subst (MvPowerSeries.X 1) ↔
      constantCoeff h = 0 ∧ ∀ n i, 0 < i → i < n → (n.choose i : R) * coeff n h = 0 := by
  -- Compare the coefficients of `XⁱYʲ`: `(i + j).choose i * c_{i+j} = [j = 0] cᵢ + [i = 0] cⱼ`.
  have key (i j : ℕ) : MvPowerSeries.coeff (single 0 i + single 1 j)
      (h.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) =
        MvPowerSeries.coeff (single 0 i + single 1 j)
          (h.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) + h.subst (MvPowerSeries.X 1)) ↔
      (i + j).choose i * coeff (i + j) h =
        (if j = 0 then coeff i h else 0) + if i = 0 then coeff j h else 0 := by
    rw [map_add, coeff_subst_X_add_X, coeff_subst_single, coeff_subst_single]
    simp
  refine ⟨fun hh => ⟨?_, fun n i hi hin => ?_⟩, fun ⟨h₀, hn⟩ => ?_⟩
  · -- At `i = j = 0`: `c₀ = c₀ + c₀`.
    have := (key 0 0).1 (congrArg _ hh)
    simpa using this
  · -- At `i, j ≠ 0`, with `i + j = n`.
    have := (key i (n - i)).1 (congrArg _ hh)
    simpa [Nat.add_sub_cancel' hin.le, hi.ne', Nat.sub_ne_zero_of_lt hin] using this
  · ext e
    obtain ⟨i, j, rfl⟩ : ∃ i j, e = single 0 i + single 1 j :=
      ⟨e 0, e 1, by ext k; fin_cases k <;> simp⟩
    refine (key i j).2 ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp [coeff_zero_eq_constantCoeff_apply, h₀]
      · simp [hj.ne']
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp [hi.ne']
      · simpa [hi.ne', hj.ne'] using hn _ i hi (by omega)

/-- An additive power series `h` satisfies `h(a + b) = h(a) + h(b)` for all power series `a, b`
in any number of variables that can be substituted into `h`. -/
theorem subst_add_of_subst_X_add_X_eq_add {h : R⟦X⟧}
    (hh : h.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) =
      h.subst (MvPowerSeries.X 0) + h.subst (MvPowerSeries.X 1))
    {σ : Type*} {a b : MvPowerSeries σ R} (ha : HasSubst a) (hb : HasSubst b) :
    h.subst (a + b) = h.subst a + h.subst b := by
  have hab : MvPowerSeries.HasSubst ![a, b] := MvPowerSeries.hasSubst_finTwo ha hb
  have := MvPowerSeries.powerSeriesSubst_subst_finTwo_eq_add
    (HasSubst.of_constantCoeff_zero (by simp)) hh ha hb
  rwa [MvPowerSeries.subst_add hab, MvPowerSeries.subst_X hab, MvPowerSeries.subst_X hab] at this

/-- **The additive power series when `p = 0`.** If `p = 0` in `R` for a prime `p`, a power series
`h` satisfies `h(X + Y) = h(X) + h(Y)` exactly when its coefficient of `Xⁿ` vanishes for every `n`
that is not a power of `p`; that is, `h = ∑_k b_k X^(p ^ k)`. -/
theorem subst_X_add_X_eq_add_iff_of_natCast_eq_zero {p : ℕ} (hp : p.Prime) (hpR : (p : R) = 0)
    (h : R⟦X⟧) :
    h.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) =
        h.subst (MvPowerSeries.X 0) + h.subst (MvPowerSeries.X 1) ↔
      ∀ n, (∀ k, n ≠ p ^ k) → coeff n h = 0 := by
  rw [subst_X_add_X_eq_add_iff]
  refine ⟨fun ⟨h₀, hh⟩ n hn => ?_, fun hh => ⟨?_, fun n i hi hin => ?_⟩⟩
  · rcases eq_or_ne n 0 with rfl | hn0
    · simpa using h₀
    obtain ⟨i, hi, hin, hpi⟩ := hp.exists_not_dvd_choose hn0 hn
    -- Bézout: `n.choose i * a + p * b = 1` in `ℤ`, and `p = 0` in `R`, so `n.choose i` is a unit.
    have hcop : Nat.Coprime (n.choose i) p := (hp.coprime_iff_not_dvd.2 hpi).symm
    have hu : IsUnit (n.choose i : R) := by
      refine IsUnit.of_mul_eq_one ((n.choose i).gcdA p : R) ?_
      have := congrArg (Int.cast : ℤ → R) (Nat.gcd_eq_gcd_ab (n.choose i) p)
      rw [hcop.gcd_eq_one] at this
      simpa [hpR] using this.symm
    exact hu.mul_right_eq_zero.1 (hh n i hi hin)
  · simpa using hh 0 fun k => (pow_ne_zero k hp.ne_zero).symm
  · -- If `n = p ^ k` then `p ∣ n.choose i` for `0 < i < n`; otherwise the coefficient vanishes.
    by_cases hn : ∀ k, n ≠ p ^ k
    · rw [hh n hn, mul_zero]
    push Not at hn
    obtain ⟨k, rfl⟩ := hn
    obtain ⟨m, hm⟩ := hp.dvd_choose_pow hi.ne' hin.ne
    rw [hm, Nat.cast_mul, hpR, zero_mul, zero_mul]

namespace WithPiTopology

open scoped PowerSeries.WithPiTopology

variable [TopologicalSpace R]

/-- If `p = 0` in `R` for a prime `p`, an additive power series `h` is the sum
`∑_k c_{p ^ k} X^(p ^ k)` of its monomials in the degrees `p ^ k`. -/
theorem hasSum_monomial_prime_pow {p : ℕ} (hp : p.Prime) (hpR : (p : R) = 0) {h : R⟦X⟧}
    (hh : h.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) =
      h.subst (MvPowerSeries.X 0) + h.subst (MvPowerSeries.X 1)) :
    HasSum (fun k => monomial (p ^ k) (coeff (p ^ k) h)) h := by
  have hh' := (subst_X_add_X_eq_add_iff_of_natCast_eq_zero hp hpR h).1 hh
  refine (Function.Injective.hasSum_iff (f := fun n => monomial n (coeff n h))
    (Nat.pow_right_injective hp.two_le) fun n hn => ?_).2 (hasSum_of_monomials_self h)
  rw [hh' n fun k hk => hn ⟨k, hk.symm⟩, map_zero]

/-- **The additive power series when `p = 0`, as sums.** If `p = 0` in `R` for a prime `p` and
`R` is Hausdorff, a power series `h` satisfies `h(X + Y) = h(X) + h(Y)` exactly when
`h = ∑_k b_k X^(p ^ k)` for some coefficients `b : ℕ → R`, the sum converging coefficientwise. -/
theorem subst_X_add_X_eq_add_iff_exists_hasSum [T2Space R] {p : ℕ} (hp : p.Prime)
    (hpR : (p : R) = 0) (h : R⟦X⟧) :
    h.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) =
        h.subst (MvPowerSeries.X 0) + h.subst (MvPowerSeries.X 1) ↔
      ∃ b : ℕ → R, HasSum (fun k => monomial (p ^ k) (b k)) h := by
  refine ⟨fun hh => ⟨_, hasSum_monomial_prime_pow hp hpR hh⟩, fun ⟨b, hb⟩ => ?_⟩
  rw [subst_X_add_X_eq_add_iff_of_natCast_eq_zero hp hpR]
  intro n hn
  -- Every term of the sum has zero coefficient of `Xⁿ`.
  have := hb.map (coeff n) (continuous_coeff R n)
  refine this.unique ?_
  convert hasSum_zero with k
  simp [coeff_monomial, hn k]

end WithPiTopology

end PowerSeries
