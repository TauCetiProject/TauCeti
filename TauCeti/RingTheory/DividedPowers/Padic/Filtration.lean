/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DividedPowers.Nilpotent
public import TauCeti.RingTheory.DividedPowers.Padic.Basic

import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Divided power filtrations and PD-nilpotence on `ℤ_[p]` and `ZMod (p ^ e)`

This file establishes the divided power filtration behavior and complete PD-nilpotence
classification of the canonical divided power structure `PadicInt.dividedPowers p` on
`(p) ⊂ ℤ_[p]` and of its quotient `ZMod.dividedPowers p e` on `(p) ⊂ ZMod (p ^ e)`: exact
filtration steps for `p = 2`, sufficient containment and vanishing bounds for odd primes `p`, and
a complete classification of PD-nilpotence.

* Over `ℤ_[p]`, `(p)` is never PD-nilpotent (`PadicInt.not_isPDNilpotent_dividedPowers`), since
  `ℤ_[p]` is an integral domain.
* For an odd prime `p`, `(p - 1) * e ≤ (p - 2) * n` is a sufficient condition for
  `(PadicInt.dividedPowers p).pdFiltration n ≤ Ideal.span {(p : ℤ_[p]) ^ e}` (in particular,
  `F^(2e) ≤ (p ^ e)`). Hence `(ZMod.dividedPowers p e).pdFiltration n = ⊥` for `n` large enough,
  so `ZMod.dividedPowers p e` is PD-nilpotent.
* For `p = 2`, `γ₂(2) = 2 ∈ F² \ I²` and `(PadicInt.dividedPowers 2).dpow (2 ^ a) 2` is `2` times
  a unit for every `a : ℕ`, so the divided power filtration on `(2) ⊂ ℤ_[2]` is constant from
  degree `1` onward: `Fⁿ = (2)` for every `n ≠ 0`. Pushing forward to `ZMod (2 ^ e)` gives
  `Fⁿ = (2)` for all `n ≠ 0`, which vanishes only when `e ≤ 1`.
* Combining both cases yields the complete classification
  `(ZMod.dividedPowers p e).IsPDNilpotent ↔ p ≠ 2 ∨ e ≤ 1`.
* In particular, on `(2) ⊂ ZMod (2 ^ 2)` (`ℤ/4ℤ`), we have `(2) ^ 2 = 0`:
  `DividedPowers.OfSquareZero.dividedPowers` is PD-nilpotent (`F² = ⊥`), whereas
  `ZMod.dividedPowers 2 2` satisfies `γ₂(2) = 2` and is not PD-nilpotent, proving both that
  `IsNilpotent I` does not imply `IsPDNilpotent` and that `(2) ⊂ ZMod 4` carries two distinct
  divided power structures.

## Main results

* `PadicInt.pdFiltration_le_span_pow`: `(p - 1) * e ≤ (p - 2) * n → Fⁿ ≤ (p ^ e)`.
* `PadicInt.pdFiltration_two_mul_le_span_pow`: for odd `p`, `F^(2e) ≤ (p ^ e)`.
* `PadicInt.pdFiltration_two_eq`: for `p = 2` and `n ≠ 0`, `Fⁿ = (2)`.
* `PadicInt.span_two_sq_lt_pdFiltration_two`: `(2) ^ 2 < F²` in `ℤ_[2]`.
* `PadicInt.not_isPDNilpotent_dividedPowers`: `¬ (dividedPowers p).IsPDNilpotent`.
* `ZMod.pdFiltration_dividedPowers` and `ZMod.pdFiltration_dividedPowers_eq_bot_iff`: quotient
  filtration characterization.
* `ZMod.isPDNilpotent_dividedPowers_iff`:
  `(ZMod.dividedPowers p e).IsPDNilpotent ↔ p ≠ 2 ∨ e ≤ 1`.
* `ZMod.dividedPowers_two_two_ne_ofSquareZero`: the two divided power structures on `(2) ⊂ ZMod 4`
  are distinct.

## References

* [Stacks Project, Section 60.6 (Tag 07HQ)](https://stacks.math.columbia.edu/tag/07HQ).
* Stacks Project, Divided Power Algebra, Section 23.3 (Remark 23.3.6) and
  Section 23.5 (Lemma 23.5.3).
* P. Berthelot and A. Ogus, *Notes on crystalline cohomology*, Princeton Univ. Press, 1978, §3.
-/

public section

namespace PadicInt

section GeneralPrime

variable (p : ℕ) [hp : Fact p.Prime]

/-- Sufficient condition for containment of a divided power filtration step of `(p) ⊂ ℤ_[p]` in
`(p ^ e)`: whenever `(p - 1) * e ≤ (p - 2) * n`,
`(dividedPowers p).pdFiltration n ≤ Ideal.span {(p : ℤ_[p]) ^ e}`. -/
theorem pdFiltration_le_span_pow {n e : ℕ} (h : (p - 1) * e ≤ (p - 2) * n) :
    (dividedPowers p).pdFiltration n ≤ Ideal.span {(p : ℤ_[p]) ^ e} := by
  rw [(dividedPowers p).pdFiltration_le_iff_of_eq_span_singleton rfl]
  intro m hm
  rw [mem_span_pow_iff_le_valuation _ (dpow_p_ne_zero p m)]
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.out.one_lt
  have hleg := sub_one_mul_valuation_dpow_p p m
  have hmul : (p - 2) * n ≤ (p - 2) * m := Nat.mul_le_mul_left (p - 2) hm
  have hineq : (p - 1) * e ≤ (p - 1) * ((dividedPowers p).dpow m (p : ℤ_[p])).valuation := by
    omega
  exact Nat.le_of_mul_le_mul_left hineq hp1

/-- For an odd prime `p`, the divided power filtration on `(p) ⊂ ℤ_[p]` satisfies
`F^(2e) ≤ (p ^ e)` for every `e : ℕ`. -/
theorem pdFiltration_two_mul_le_span_pow (hp2 : p ≠ 2) (e : ℕ) :
    (dividedPowers p).pdFiltration (2 * e) ≤ Ideal.span {(p : ℤ_[p]) ^ e} := by
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le
    omega
  exact pdFiltration_le_span_pow p
    ((Nat.mul_le_mul_right e (by omega)).trans_eq (Nat.mul_assoc _ _ _))

/-- The canonical divided power ideal `(p) ⊂ ℤ_[p]` is not PD-nilpotent for any prime `p`. -/
@[simp]
theorem not_isPDNilpotent_dividedPowers : ¬ (dividedPowers p).IsPDNilpotent := by
  rw [DividedPowers.isPDNilpotent_iff_eq_bot, Ideal.span_singleton_eq_bot]
  exact NeZero.ne _

end GeneralPrime

section PrimeTwo

/-- For `p = 2` and every `n ≠ 0`, the `n`-th divided power filtration step of `(2) ⊂ ℤ_[2]`
equals `(2)` itself. -/
@[simp]
theorem pdFiltration_two_eq {n : ℕ} (hn : n ≠ 0) :
    (dividedPowers 2).pdFiltration n = Ideal.span {(2 : ℤ_[2])} := by
  refine le_antisymm ?_ ?_
  · simpa only [Nat.cast_ofNat] using (dividedPowers 2).pdFiltration_le_self hn
  · obtain ⟨u, hu⟩ := exists_unit_mul_two_eq_dpow_two_pow n
    have h2_mem : (2 : ℤ_[2]) ∈ Ideal.span {((2 : ℕ) : ℤ_[2])} := by
      rw [Ideal.mem_span_singleton, Nat.cast_ofNat]
    have hmem : (dividedPowers 2).dpow (2 ^ n) (2 : ℤ_[2]) ∈ (dividedPowers 2).pdFiltration n :=
      (dividedPowers 2).dpow_mem_pdFiltration_of_le Nat.lt_two_pow_self.le h2_mem
    rw [← Ideal.span_singleton_mul_left_unit u.isUnit (2 : ℤ_[2]), ← hu]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hmem

/-- In `ℤ_[2]`, `2` lies in every step of the divided power filtration of `(2)`. -/
theorem two_mem_pdFiltration_two (n : ℕ) :
    (2 : ℤ_[2]) ∈ (dividedPowers 2).pdFiltration n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [pdFiltration_two_eq hn]
    exact Ideal.subset_span (Set.mem_singleton _)

/-- Strict containment `(2) ^ 2 < F²((2))` in `ℤ_[2]`. -/
theorem span_two_sq_lt_pdFiltration_two :
    (Ideal.span {(2 : ℤ_[2])}) ^ 2 < (dividedPowers 2).pdFiltration 2 := by
  have hle : (Ideal.span {(2 : ℤ_[2])}) ^ 2 ≤ (dividedPowers 2).pdFiltration 2 := by
    simpa only [Nat.cast_ofNat] using (dividedPowers 2).pow_le_pdFiltration 2
  refine lt_of_le_of_ne hle fun h ↦ p_notMem_span_p_sq (p := 2) ?_
  simpa only [Nat.cast_ofNat, h] using two_mem_pdFiltration_two 2

end PrimeTwo

end PadicInt

namespace ZMod

section Filtration

variable (p : ℕ) [hp : Fact p.Prime] (e : ℕ)

/-- The divided power filtration of `ZMod.dividedPowers p e` is the image under `toZModPow e` of
the divided power filtration of `PadicInt.dividedPowers p`. -/
theorem pdFiltration_dividedPowers (n : ℕ) :
    (ZMod.dividedPowers p e).pdFiltration n =
      ((PadicInt.dividedPowers p).pdFiltration n).map (PadicInt.toZModPow e) :=
  ((toZModPow_isDPMorphism p e).map_pdFiltration_eq (PadicInt.map_toZModPow_span_p p e) n).symm

/-- Vanishing of the `n`-th divided power filtration step in `ZMod (p ^ e)` is equivalent to
containment of the `n`-th filtration step in `Ideal.span {(p : ℤ_[p]) ^ e}`. -/
theorem pdFiltration_dividedPowers_eq_bot_iff (n : ℕ) :
    (ZMod.dividedPowers p e).pdFiltration n = ⊥ ↔
      (PadicInt.dividedPowers p).pdFiltration n ≤ Ideal.span {(p : ℤ_[p]) ^ e} := by
  rw [pdFiltration_dividedPowers p e n, Ideal.map_eq_bot_iff_le_ker (PadicInt.toZModPow e),
    PadicInt.ker_toZModPow e]

/-- Whenever `(p - 1) * e ≤ (p - 2) * n`, the `n`-th divided power filtration step of
`ZMod.dividedPowers p e` vanishes. -/
theorem pdFiltration_dividedPowers_eq_bot {n : ℕ} (h : (p - 1) * e ≤ (p - 2) * n) :
    (ZMod.dividedPowers p e).pdFiltration n = ⊥ :=
  (pdFiltration_dividedPowers_eq_bot_iff p e n).mpr (PadicInt.pdFiltration_le_span_pow p h)

end Filtration

section PrimeTwoAndClassification

/-- For every `e : ℕ` and `n ≠ 0`, the `n`-th divided power filtration step of
`ZMod.dividedPowers 2 e` equals `Ideal.span {(2 : ZMod (2 ^ e))}`. -/
@[simp]
theorem pdFiltration_dividedPowers_two {e n : ℕ} (hn : n ≠ 0) :
    (ZMod.dividedPowers 2 e).pdFiltration n = Ideal.span {(2 : ZMod (2 ^ e))} := by
  rw [pdFiltration_dividedPowers 2 e n, PadicInt.pdFiltration_two_eq hn]
  simpa only [Nat.cast_ofNat] using PadicInt.map_toZModPow_span_p 2 e

/-- Complete classification of PD-nilpotence for the canonical divided power structure on
`(p) ⊂ ZMod (p ^ e)`: it is PD-nilpotent if and only if `p` is odd (`p ≠ 2`) or `e ≤ 1`. -/
@[simp]
theorem isPDNilpotent_dividedPowers_iff (p : ℕ) [hp : Fact p.Prime] (e : ℕ) :
    (ZMod.dividedPowers p e).IsPDNilpotent ↔ p ≠ 2 ∨ e ≤ 1 := by
  constructor
  · intro h
    by_contra! hneg
    rcases hneg with ⟨rfl, he⟩
    obtain ⟨n, hn, hbot⟩ := (ZMod.dividedPowers 2 e).isPDNilpotent_iff.mp h
    rw [pdFiltration_dividedPowers_two hn.ne', Ideal.span_singleton_eq_bot] at hbot
    have hdvd : 2 ^ e ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (2 ^ e)).mp (by simpa using hbot)
    exact Nat.not_pos_pow_dvd (by decide : 1 < 2) he hdvd
  · rintro (hp2 | he)
    · exact (ZMod.dividedPowers p e).isPDNilpotent_iff_exists_eq_bot.mpr
        ⟨2 * e, (pdFiltration_dividedPowers_eq_bot_iff p e (2 * e)).mpr
          (PadicInt.pdFiltration_two_mul_le_span_pow p hp2 e)⟩
    · refine (ZMod.dividedPowers p e).isPDNilpotent_of_eq_bot ?_
      rw [Ideal.span_singleton_eq_bot, ZMod.natCast_eq_zero_iff]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with rfl | rfl <;> simp

/-- For every `e ≥ 2`, the canonical `2`-adic divided power structure on `(2) ⊂ ZMod (2 ^ e)` is
not PD-nilpotent, even though `(2) ^ e = 0`. -/
theorem not_isPDNilpotent_dividedPowers_two {e : ℕ} (he : 2 ≤ e) :
    ¬ (ZMod.dividedPowers 2 e).IsPDNilpotent := by
  rw [isPDNilpotent_dividedPowers_iff 2 e]
  omega

/-- On the square-zero ideal `(2) ⊂ ZMod (2 ^ 2)` (`ℤ/4ℤ`), `ZMod.dividedPowers 2 2` (which is not
PD-nilpotent, with `γ₂(2) = 2`) differs from `DividedPowers.OfSquareZero.dividedPowers` (which is
PD-nilpotent, with `γ₂(2) = 0`). -/
theorem dividedPowers_two_two_ne_ofSquareZero
    [DecidablePred fun x : ZMod (2 ^ 2) ↦ x ∈ Ideal.span {((2 : ℕ) : ZMod (2 ^ 2))}] :
    ZMod.dividedPowers 2 2 ≠ DividedPowers.OfSquareZero.dividedPowers (by
      rw [Ideal.span_singleton_pow, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      simpa only [Nat.cast_ofNat] using ZMod.natCast_pow_eq_zero_of_le 2 (le_refl 2)) := by
  intro h
  have hnil : (ZMod.dividedPowers 2 2).IsPDNilpotent :=
    h ▸ DividedPowers.OfSquareZero.isPDNilpotent _
  exact not_isPDNilpotent_dividedPowers_two le_rfl hnil

end PrimeTwoAndClassification

end ZMod
