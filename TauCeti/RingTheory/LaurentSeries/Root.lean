/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.GroupTheory.Divisible
public import TauCeti.RingTheory.LaurentSeries.Ramified

import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.PowerSeries.Trunc
import TauCeti.RingTheory.PowerSeries.Hensel

/-!
# Roots of expanded formal Laurent series

Let `R` be a commutative semiring of exponential characteristic `d`. Expanding a formal Laurent
series `f ∈ R⸨X⸩` by `X ↦ X ^ d` and applying Frobenius `r ↦ r ^ d` to its coefficients produces
`f ^ (d : ℕ)`, extending `Polynomial.map_frobenius_expand` and `PowerSeries.map_frobenius_expand`
to poles of arbitrary order.

Over a field `K` whose unit group `Kˣ` is `ℕ`-rootable (for instance any algebraically closed field,
in any characteristic), every expanded Laurent series `expand K d f` has a `d`-th root in `K⸨X⸩`.
By factoring `d` into primes and composing expansions (`LaurentSeries.expand_expand`), this reduces
to prime degree `p`:

* when `p ≠ 0` in `K`, writing `f = X ^ (ord f) * u` with `u ∈ K⟦X⟧ˣ` and extracting a `p`-th root
  of `u` via Hensel's lemma (`PowerSeries.exists_pow_eq_of_constantCoeff_eq_pow`);
* when `p = 0` in `K`, `K` has characteristic `p` and Frobenius on `K` is surjective by rootability
  of `Kˣ`, so applying the inverse of Frobenius to the coefficients of `f` gives a `p`-th root of
  `expand K p f`.

## Main results

* `LaurentSeries.mapRingHom_frobenius_expand`: over a commutative semiring of exponential
  characteristic `d`, applying `frobenius R d` to the coefficients of `expand R d f` gives
  `f ^ (d : ℕ)`.
* `LaurentSeries.exists_pow_eq_expand_of_surjective_frobenius`: over a commutative semiring of
  exponential characteristic `d` with surjective Frobenius, every `expand R d f` is a `d`-th power.
* `LaurentSeries.exists_pow_eq_expand_of_exists_pow_constantCoeff`: over a field `K` with
  `(d : K) ≠ 0`, `expand K d f` has a `d`-th root whenever `constantCoeff f.powerSeriesPart` is a
  `d`-th power in `K`.
* `LaurentSeries.exists_pow_eq_expand`: over a field `K` with `[RootableBy Kˣ ℕ]`, every expanded
  Laurent series `expand K d f` is a `d`-th power in `K⸨X⸩`.
-/

public section

open HahnSeries
open scoped LaurentSeries Polynomial PowerSeries

namespace LaurentSeries

section Frobenius

variable {R : Type*} [CommSemiring R]

/-- On power series coerced to `R⸨X⸩`, applying `frobenius R d` to the coefficients of
`expand R d f` gives `f ^ (d : ℕ)`. -/
private theorem mapRingHom_frobenius_expand_coe (d : ℕ+) [ExpChar R d] (f : R⟦X⟧) :
    mapRingHom (frobenius R d) (expand R d (f : R⸨X⸩)) = (f : R⸨X⸩) ^ (d : ℕ) := by
  rw [← (ofPowerSeries ℤ R).map_pow]
  ext k
  rw [coeff_mapRingHom]
  by_cases hk : k < 0
  · rw [PowerSeries.coeff_coe, ite_eq_left hk]
    by_cases hd : (d : ℤ) ∣ k
    · obtain ⟨j, rfl⟩ := hd
      have hj : j < 0 := by
        have : (0 : ℤ) < d := by exact_mod_cast d.pos
        nlinarith
      rw [coeff_expand_mul, PowerSeries.coeff_coe, ite_eq_left hj, map_zero]
    · rw [coeff_expand_of_not_dvd d _ hd, map_zero]
  · lift k to ℕ using not_lt.mp hk
    rw [PowerSeries.coeff_coe, ite_eq_right hk, Int.natAbs_natCast]
    have hpow : PowerSeries.coeff k (f ^ (d : ℕ)) =
        ((Polynomial.map (frobenius R d)
          (Polynomial.expand R d (f.trunc (k + 1)))).coeff k) := by
      have htrunc : PowerSeries.coeff k (f ^ (d : ℕ)) =
          PowerSeries.coeff k ((f.trunc (k + 1) : R⟦X⟧) ^ (d : ℕ)) := by
        simpa only [PowerSeries.coeff_trunc, ite_eq_left k.lt_succ_self] using
          congrArg (fun p : R[X] ↦ p.coeff k) (f.trunc_trunc_pow (k + 1) d).symm
      rw [htrunc, ← Polynomial.coe_pow, Polynomial.coeff_coe, ← Polynomial.map_frobenius_expand]
    rw [hpow, Polynomial.coeff_map]
    by_cases hd : (d : ℕ) ∣ k
    · obtain ⟨j, rfl⟩ := hd
      have hj : j < d * j + 1 := Nat.lt_succ_of_le (Nat.le_mul_of_pos_left j d.pos)
      have hj0 : ¬ ((j : ℤ) < 0) := by omega
      rw [Nat.cast_mul, coeff_expand_mul, PowerSeries.coeff_coe, ite_eq_right hj0,
        Int.natAbs_natCast, Polynomial.coeff_expand_mul' d.pos, PowerSeries.coeff_trunc,
        ite_eq_left hj]
    · have hd' : ¬ ((d : ℤ) ∣ (k : ℤ)) := by exact_mod_cast hd
      rw [coeff_expand_of_not_dvd d _ hd', Polynomial.coeff_expand d.pos, ite_eq_right hd,
        map_zero]

/-- Over a commutative semiring `R` of exponential characteristic `d`, applying `frobenius R d` to
the coefficients of `expand R d f` produces `f ^ (d : ℕ)`. -/
theorem mapRingHom_frobenius_expand (d : ℕ+) [ExpChar R d] (f : R⸨X⸩) :
    mapRingHom (frobenius R d) (expand R d f) = f ^ (d : ℕ) := by
  conv_lhs => rw [← single_order_mul_powerSeriesPart f]
  conv_rhs => rw [← single_order_mul_powerSeriesPart f]
  have hsingle : mapRingHom (frobenius R d) (single ((d : ℤ) * f.order) (1 : R)) =
      single ((d : ℤ) * f.order) 1 := by
    ext k
    by_cases hk : k = (d : ℤ) * f.order <;> simp [hk]
  rw [map_mul, map_mul, expand_single, hsingle, mapRingHom_frobenius_expand_coe, mul_pow,
    single_pow, one_pow, nsmul_eq_mul]

/-- Over a commutative semiring `R` of exponential characteristic `d` with surjective Frobenius,
every expanded Laurent series `expand R d f` is a `d`-th power in `R⸨X⸩`. -/
theorem exists_pow_eq_expand_of_surjective_frobenius (d : ℕ+) [ExpChar R d]
    (hfrob : Function.Surjective (frobenius R d)) (f : R⸨X⸩) :
    ∃ g : R⸨X⸩, g ^ (d : ℕ) = expand R d f := by
  classical
  let ψ : R → R := fun r ↦ if r = 0 then 0 else Classical.choose (hfrob r)
  have hψ : ∀ r : R, frobenius R d (ψ r) = r := fun r ↦ by
    by_cases hr : r = 0
    · simp [ψ, hr]
    · simp [ψ, hr, Classical.choose_spec (hfrob r)]
  let g : R⸨X⸩ :=
    { coeff := fun k ↦ ψ (f.coeff k)
      isPWO_support' := f.isPWO_support'.mono fun k hk ↦
        Function.mem_support.mpr fun h0 ↦ Function.mem_support.mp hk (by simp [ψ, h0]) }
  refine ⟨g, ?_⟩
  rw [← mapRingHom_frobenius_expand d g]
  ext k
  by_cases hd : (d : ℤ) ∣ k
  · obtain ⟨j, rfl⟩ := hd
    simp [coeff_mapRingHom, coeff_expand_mul, g, hψ]
  · simp [coeff_mapRingHom, coeff_expand_of_not_dvd d _ hd]

end Frobenius

section Root

variable {K : Type*} [Field K]

/-- Over a field `K` with `(d : K) ≠ 0`, an expanded Laurent series `expand K d f` has a `d`-th root
in `K⸨X⸩` whenever `constantCoeff f.powerSeriesPart` is a `d`-th power in `K`. -/
theorem exists_pow_eq_expand_of_exists_pow_constantCoeff {d : ℕ+} (hd : ((d : ℕ) : K) ≠ 0)
    {f : K⸨X⸩} (hc : ∃ c : K, c ^ (d : ℕ) = PowerSeries.constantCoeff f.powerSeriesPart) :
    ∃ g : K⸨X⸩, g ^ (d : ℕ) = expand K d f := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact ⟨0, by simp [zero_pow d.ne_zero]⟩
  obtain ⟨c, hc⟩ := hc
  have hu : IsUnit f.powerSeriesPart := TauCeti.LaurentSeries.isUnit_powerSeriesPart hf
  have hc0 : c ≠ 0 := fun h0 ↦
    (PowerSeries.isUnit_iff_constantCoeff.mp hu).ne_zero (by rw [← hc, h0, zero_pow d.ne_zero])
  obtain ⟨v, hv, -⟩ := PowerSeries.exists_pow_eq_of_constantCoeff_eq_pow hd hc0 hc.symm
  refine ⟨single f.order 1 * expand K d (v : K⸨X⸩), ?_⟩
  rw [mul_pow, single_pow, one_pow, ← map_pow, ← PowerSeries.coe_pow, hv, nsmul_eq_mul]
  conv_rhs => rw [← single_order_mul_powerSeriesPart f]
  rw [map_mul, expand_single]

/-- Over a field `K` whose unit group `Kˣ` is `ℕ`-rootable, every expanded Laurent series
`expand K d f` has a `d`-th root in `K⸨X⸩`, in arbitrary characteristic. -/
theorem exists_pow_eq_expand [RootableBy Kˣ ℕ] (d : ℕ+) (f : K⸨X⸩) :
    ∃ g : K⸨X⸩, g ^ (d : ℕ) = expand K d f := by
  induction hd : (d : ℕ) using Nat.strong_induction_on generalizing d f with
  | ind n ih =>
    subst hd
    by_cases hd1 : d = 1
    · subst hd1
      exact ⟨f, by simp⟩
    · obtain ⟨p, hp, hpd⟩ := PNat.exists_prime_and_dvd hd1
      let m := d.divExact p
      have hdm : p * m = d := PNat.mul_div_exact hpd
      have hm_lt : (m : ℕ) < d := by
        have hp1 : 1 < (p : ℕ) := hp.one_lt
        have hm0 : 0 < (m : ℕ) := m.pos
        have : (p : ℕ) * m = d := congrArg PNat.val hdm
        nlinarith
      obtain ⟨h, hh⟩ := ih m hm_lt m f rfl
      have hprime : ∃ g : K⸨X⸩, g ^ (p : ℕ) = expand K p h := by
        by_cases hp0 : ((p : ℕ) : K) = 0
        · have : CharP K p := (CharP.charP_iff_prime_eq_zero hp).mpr hp0
          have : ExpChar K p := .prime hp
          refine exists_pow_eq_expand_of_surjective_frobenius p (fun a ↦ ?_) h
          rcases eq_or_ne a 0 with rfl | ha
          · exact ⟨0, map_zero _⟩
          · obtain ⟨c, hc⟩ := RootableBy.surjective_pow Kˣ ℕ p.ne_zero (Units.mk0 a ha)
            exact ⟨c, congrArg Units.val hc⟩
        · refine exists_pow_eq_expand_of_exists_pow_constantCoeff hp0 ?_
          rcases eq_or_ne (PowerSeries.constantCoeff h.powerSeriesPart) 0 with hc0 | hc0
          · exact ⟨0, by rw [hc0, zero_pow p.ne_zero]⟩
          · obtain ⟨c, hc⟩ := RootableBy.surjective_pow Kˣ ℕ p.ne_zero (Units.mk0 _ hc0)
            exact ⟨c, congrArg Units.val hc⟩
      obtain ⟨g, hg⟩ := hprime
      refine ⟨g, ?_⟩
      rw [← hdm, PNat.mul_coe, pow_mul, hg, ← map_pow, hh, expand_expand]

end Root

end LaurentSeries
