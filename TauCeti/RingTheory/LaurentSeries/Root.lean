/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.GroupTheory.Divisible
public import TauCeti.RingTheory.LaurentSeries.Ramified

import TauCeti.RingTheory.PowerSeries.Hensel

/-!
# Roots of expanded formal Laurent series

Over a field `K` whose unit group `Kˣ` is `ℕ`-rootable (for instance any algebraically closed field,
in any characteristic), every expanded Laurent series `expand K d f` has a `d`-th root in `K⸨X⸩`.
By factoring `d` into primes and composing expansions (`LaurentSeries.expand_expand`), this reduces
to prime degree `p`:

* when `p ≠ 0` in `K`, writing `f = X ^ (ord f) * u` with `u ∈ K⟦X⟧ˣ` and extracting a `p`-th root
  of `u` via Hensel's lemma (`PowerSeries.exists_pow_eq_of_constantCoeff_eq_pow`);
* when `p = 0` in `K`, `K` has characteristic `p` and Frobenius on `K` is surjective by rootability
  of `Kˣ`, so applying the inverse of Frobenius to the coefficients of `f` gives a `p`-th root of
  `expand K p f` via `LaurentSeries.mapRingHom_frobenius_expand`.

## Main results

* `LaurentSeries.exists_pow_eq_expand_of_surjective_frobenius`: over a commutative semiring of
  exponential characteristic `d` with surjective Frobenius, every `expand R d f` is a `d`-th power.
* `LaurentSeries.exists_pow_eq_expand_of_exists_pow_eq_constantCoeff_powerSeriesPart`: over a field
  `K` with `(d : K) ≠ 0`, `expand K d f` has a `d`-th root whenever
  `constantCoeff f.powerSeriesPart` is a `d`-th power in `K`.
* `LaurentSeries.exists_pow_eq_expand`: over a field `K` with `[RootableBy Kˣ ℕ]`, every expanded
  Laurent series `expand K d f` is a `d`-th power in `K⸨X⸩`.
-/

public section

open HahnSeries
open scoped LaurentSeries Polynomial PowerSeries

namespace LaurentSeries

section Frobenius

variable {R : Type*} [CommSemiring R]

/-- Over a commutative semiring `R` of exponential characteristic `d` with surjective Frobenius,
every expanded Laurent series `expand R d f` is a `d`-th power in `R⸨X⸩`. -/
theorem exists_pow_eq_expand_of_surjective_frobenius (d : ℕ+) [ExpChar R d]
    (hfrob : Function.Surjective (frobenius R d)) (f : R⸨X⸩) :
    ∃ g : R⸨X⸩, g ^ (d : ℕ) = expand R d f := by
  obtain ⟨g, rfl⟩ := (HahnSeries.mem_map_rangeS (f := frobenius R d)).mpr fun k ↦ hfrob (f.coeff k)
  refine ⟨g, ?_⟩
  rw [← mapRingHom_frobenius_expand d g]
  ext k
  by_cases hd : (d : ℤ) ∣ k
  · obtain ⟨j, rfl⟩ := hd
    simp [coeff_mapRingHom, coeff_expand_mul]
  · simp [coeff_mapRingHom, coeff_expand_of_not_dvd d _ hd]

end Frobenius

section Root

variable {K : Type*} [Field K]

/-- Over a field `K` with `(d : K) ≠ 0`, an expanded Laurent series `expand K d f` has a `d`-th root
in `K⸨X⸩` whenever `constantCoeff f.powerSeriesPart` is a `d`-th power in `K`. -/
theorem exists_pow_eq_expand_of_exists_pow_eq_constantCoeff_powerSeriesPart {d : ℕ+}
    (hd : ((d : ℕ) : K) ≠ 0)
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
        · refine exists_pow_eq_expand_of_exists_pow_eq_constantCoeff_powerSeriesPart hp0 ?_
          rcases eq_or_ne (PowerSeries.constantCoeff h.powerSeriesPart) 0 with hc0 | hc0
          · exact ⟨0, by rw [hc0, zero_pow p.ne_zero]⟩
          · obtain ⟨c, hc⟩ := RootableBy.surjective_pow Kˣ ℕ p.ne_zero (Units.mk0 _ hc0)
            exact ⟨c, congrArg Units.val hc⟩
      obtain ⟨g, hg⟩ := hprime
      refine ⟨g, ?_⟩
      rw [← hdm, PNat.mul_coe, pow_mul, hg, ← map_pow, hh, expand_expand]

end Root

end LaurentSeries
