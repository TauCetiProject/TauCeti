/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.DividedPowers.Padic
public import TauCeti.Data.ZMod.Nilpotent
public import TauCeti.RingTheory.DividedPowers.Nilpotent

/-!
# Divided power filtrations and PD-nilpotence on `ℤ_[p]` and `ZMod (p ^ e)`

This file computes the `p`-adic valuations, divided power filtrations, and PD-nilpotence behavior
of the canonical divided power structure `PadicInt.dividedPowers p` on `(p) ⊂ ℤ_[p]` and of its
quotient `ZMod.dividedPowers p e` on `(p) ⊂ ZMod (p ^ e)`.

By Legendre's formula (`Nat.Prime.sub_one_mul_multiplicity_factorial`), for every prime `p` and
every `n : ℕ`, the `p`-adic valuation of `γₙ(p) = p ^ n / n!` satisfies
`(p - 1) * v_p(γₙ(p)) = (p - 2) * n + s_p(n)`, where `s_p(n)` is the sum of base-`p` digits of
`n`. This reveals a sharp dichotomy between `p = 2` and odd primes `p`:

* For any prime `p` and any `e : ℕ`, the kernel `Ideal.span {(p : ℤ_[p]) ^ e}` of
  `PadicInt.toZModPow e : ℤ_[p] →+* ZMod (p ^ e)` satisfies
  `IsSubDPIdeal (ker (toZModPow e) ⊓ (p))`, so `PadicInt.dividedPowers p` descends uniquely to a
  divided power structure `ZMod.dividedPowers p e` on `(p) ⊂ ZMod (p ^ e)`.
* Over `ℤ_[p]`, `(p)` is never PD-nilpotent (`PadicInt.not_isPDNilpotent_dividedPowers`), since
  `ℤ_[p]` is an integral domain.
* For an odd prime `p`, `(p - 1) * e ≤ (p - 2) * n` implies
  `(PadicInt.dividedPowers p).pdFiltration n ≤ Ideal.span {(p : ℤ_[p]) ^ e}` (in particular,
  `F^(2e) ≤ (p ^ e)`). Hence `(ZMod.dividedPowers p e).pdFiltration n = ⊥` for `n` large enough,
  so `ZMod.dividedPowers p e` is PD-nilpotent.
* For `p = 2`, `(PadicInt.dividedPowers 2).dpow (2 ^ a) 2` has `2`-adic valuation `1` for every
  `a : ℕ` (it is `2` times a unit in `ℤ_[2]`), and in particular `γ₂(2) = 2 ∈ F² \ I²`. Thus the
  divided power filtration on `(2) ⊂ ℤ_[2]` is constant from degree `1` onward:
  `Fⁿ = (2)` for every `n ≠ 0`. Pushing forward to `ZMod (2 ^ e)` gives `Fⁿ = (2)` for all `n ≠ 0`,
  which vanishes only when `e ≤ 1`.
* Combining both cases yields the complete classification
  `(ZMod.dividedPowers p e).IsPDNilpotent ↔ p ≠ 2 ∨ e ≤ 1`.
* In particular, on `(2) ⊂ ZMod (2 ^ 2)` (`ℤ/4ℤ`), we have `(2) ^ 2 = 0`:
  `DividedPowers.OfSquareZero.dividedPowers` is PD-nilpotent (`F² = ⊥`), whereas
  `ZMod.dividedPowers 2 2` satisfies `γ₂(2) = 2` and is not PD-nilpotent, proving both that
  `IsNilpotent I` does not imply `IsPDNilpotent` and that `(2) ⊂ ZMod 4` carries two distinct
  divided power structures.

## Main definitions

* `ZMod.dividedPowers`: the canonical divided power structure on `Ideal.span {(p : ZMod (p ^ e))}`
  induced from `PadicInt.dividedPowers p` along `PadicInt.toZModPow e`.

## Main results

* `PadicInt.valuation_dpow_p`: `((dividedPowers p).dpow n p).valuation = n - multiplicity p n!`.
* `PadicInt.sub_one_mul_valuation_dpow_p`: Legendre identity
  `(p - 1) * ((dividedPowers p).dpow n p).valuation = (p - 2) * n + (p.digits n).sum`.
* `PadicInt.isSubDPIdeal_span_pow`: `Ideal.span {(p : ℤ_[p]) ^ e}` is a sub-dp-ideal for `e ≠ 0`.
* `PadicInt.pdFiltration_le_span_pow`: `(p - 1) * e ≤ (p - 2) * n → Fⁿ ≤ (p ^ e)`.
* `PadicInt.valuation_dpow_two`: for `p = 2`, the `2`-adic valuation of `γₙ(2)` is the binary
  digit sum `(Nat.digits 2 n).sum`.
* `PadicInt.pdFiltration_two_eq`: for `p = 2` and `n ≠ 0`, `Fⁿ = (2)`.
* `PadicInt.span_two_sq_lt_pdFiltration_two`: `(2) ^ 2 < F²` in `ℤ_[2]`.
* `PadicInt.not_isPDNilpotent_dividedPowers`: `¬ (dividedPowers p).IsPDNilpotent`.
* `ZMod.isPDNilpotent_dividedPowers_iff`:
  `(ZMod.dividedPowers p e).IsPDNilpotent ↔ p ≠ 2 ∨ e ≤ 1`.
* `ZMod.dividedPowers_two_two_ne_ofSquareZero`: the two divided power structures on `(2) ⊂ ZMod 4`
  are distinct.

## References

* Mathlib's `PadicInt.dividedPowers` and `DividedPowers.Quotient.OfSurjective.dividedPowers` by
  A. Chambert-Loir and M. I. de Frutos-Fernández.
* [Stacks Project, Section 60.5 (Tag 07HL)](https://stacks.math.columbia.edu/tag/07HL),
  Definition 60.5.2 (Tag 07HM), and
  [Section 60.6 (Tag 07HQ)](https://stacks.math.columbia.edu/tag/07HQ).
* Stacks Project, Divided Power Algebra, Section 23.3 (Remark 23.3.6) and
  Section 23.5 (Lemma 23.5.3).
* P. Berthelot and A. Ogus, *Notes on crystalline cohomology*, Princeton Univ. Press, 1978, §3.
-/

public section

namespace PadicInt

section GeneralPrime

variable (p : ℕ) [hp : Fact p.Prime]

/-- Coercion of `(PadicInt.dividedPowers p).dpow n p` to `ℚ_[p]`. -/
theorem coe_dpow_p (n : ℕ) :
    (((dividedPowers p).dpow n (p : ℤ_[p])) : ℚ_[p]) =
      (n.factorial : ℚ_[p])⁻¹ * (p : ℚ_[p]) ^ n := by
  have hp_mem : (p : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p])} :=
    Ideal.subset_span (Set.mem_singleton _)
  rw [coe_dpow_eq p n (p : ℤ_[p])]
  simp [hp_mem, Ring.inverse_eq_inv']

/-- The divided power `(PadicInt.dividedPowers p).dpow n p` is nonzero for every `n : ℕ`. -/
theorem dpow_p_ne_zero (n : ℕ) : (dividedPowers p).dpow n (p : ℤ_[p]) ≠ 0 := by
  intro h
  have hcoe : (((dividedPowers p).dpow n (p : ℤ_[p])) : ℚ_[p]) = 0 := by
    rw [h, coe_zero]
  rw [coe_dpow_p p n] at hcoe
  have hfac : (n.factorial : ℚ_[p])⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
  have hpow : (p : ℚ_[p]) ^ n ≠ 0 :=
    pow_ne_zero n (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  exact mul_ne_zero hfac hpow hcoe

/-- The `p`-adic valuation of `γₙ(p) = p ^ n / n!` is `n - multiplicity p n.factorial`. -/
theorem valuation_dpow_p (n : ℕ) :
    ((dividedPowers p).dpow n (p : ℤ_[p])).valuation = n - multiplicity p n.factorial := by
  have hle : multiplicity p n.factorial ≤ n := multiplicity_factorial_le p n
  have hfac : (n.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hpow : (p : ℚ_[p]) ^ n ≠ 0 := pow_ne_zero n (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  apply Int.ofNat.inj
  rw [Int.ofNat_eq_natCast, ← valuation_coe, coe_dpow_p p n,
    Padic.valuation_mul (inv_ne_zero hfac) hpow, Padic.valuation_inv, Padic.valuation_natCast,
    Padic.valuation_pow, Padic.valuation_p, mul_one, Int.ofNat_eq_natCast, Nat.cast_sub hle]
  ring

/-- Membership of `γₙ(p)` in `(p ^ e) ⊂ ℤ_[p]` in terms of `multiplicity p n.factorial`. -/
theorem dpow_p_mem_span_pow_iff {n e : ℕ} :
    (dividedPowers p).dpow n (p : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ e} ↔
      e ≤ n - multiplicity p n.factorial := by
  rw [mem_span_pow_iff_le_valuation _ (dpow_p_ne_zero p n), valuation_dpow_p p n]

/-- Legendre's formula for the `p`-adic valuation of `γₙ(p)`:
`(p - 1) * v_p(γₙ(p)) = (p - 2) * n + s_p(n)`. -/
theorem sub_one_mul_valuation_dpow_p (n : ℕ) :
    (p - 1) * ((dividedPowers p).dpow n (p : ℤ_[p])).valuation =
      (p - 2) * n + (p.digits n).sum := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hleg := hp.out.sub_one_mul_multiplicity_factorial (n := n)
  have hdig : (p.digits n).sum ≤ n := Nat.digit_sum_le p n
  rw [valuation_dpow_p p n]
  have h1 : (p - 1) * (n - multiplicity p n.factorial) =
      (p - 1) * n - (p - 1) * multiplicity p n.factorial := Nat.mul_sub_left_distrib ..
  rw [h1, hleg]
  have h2 : (p - 1) * n = (p - 2) * n + n := by
    calc (p - 1) * n = (p - 2 + 1) * n := by congr 1; omega
      _ = (p - 2) * n + n := by ring
  omega

/-- For every `e : ℕ` and `n ≠ 0`, `γₙ(p ^ e)` belongs to `Ideal.span {(p : ℤ_[p]) ^ e}`. -/
theorem dpow_p_pow_mem_span_pow {e n : ℕ} (hn : n ≠ 0) :
    (dividedPowers p).dpow n ((p : ℤ_[p]) ^ e) ∈ Ideal.span {(p : ℤ_[p]) ^ e} := by
  rcases e with _ | e
  · simp [Ideal.span_singleton_one]
  · have hp_mem : (p : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p])} :=
      Ideal.subset_span (Set.mem_singleton _)
    have hdp : (dividedPowers p).dpow n ((p : ℤ_[p]) ^ (e + 1)) =
        ((p : ℤ_[p]) ^ e) ^ n * (dividedPowers p).dpow n (p : ℤ_[p]) := by
      rw [pow_succ, (dividedPowers p).dpow_mul hp_mem]
    rw [hdp]
    have hpow_ne : ((p : ℤ_[p]) ^ e) ^ n ≠ 0 :=
      pow_ne_zero _ (pow_ne_zero _ (NeZero.ne _))
    have hne : ((p : ℤ_[p]) ^ e) ^ n * (dividedPowers p).dpow n (p : ℤ_[p]) ≠ 0 :=
      mul_ne_zero hpow_ne (dpow_p_ne_zero p n)
    rw [mem_span_pow_iff_le_valuation _ hne,
      valuation_mul hpow_ne (dpow_p_ne_zero p n),
      valuation_pow, valuation_pow, valuation_p, mul_one, valuation_dpow_p p n]
    have hlt : multiplicity p n.factorial < n := multiplicity_factorial_lt_of_ne_zero p hn
    have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hmul : e ≤ n * e := Nat.le_mul_of_pos_left e h1
    omega

/-- For `e ≠ 0`, `Ideal.span {(p : ℤ_[p]) ^ e}` is a sub-dp-ideal of `PadicInt.dividedPowers p`. -/
theorem isSubDPIdeal_span_pow {e : ℕ} (he : e ≠ 0) :
    (dividedPowers p).IsSubDPIdeal (Ideal.span {(p : ℤ_[p]) ^ e}) := by
  have hsub : {(p : ℤ_[p]) ^ e} ⊆ (Ideal.span {(p : ℤ_[p])} : Set ℤ_[p]) := by
    rintro x rfl
    exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_singleton _)) e (Nat.pos_of_ne_zero he)
  exact (DividedPowers.span_isSubDPIdeal_iff (hI := dividedPowers p) hsub).mpr <| by
    rintro n hn _ rfl
    exact dpow_p_pow_mem_span_pow p hn

/-- The intersection `RingHom.ker (toZModPow e) ⊓ Ideal.span {(p : ℤ_[p])}` is a sub-dp-ideal of
`PadicInt.dividedPowers p` for every `e : ℕ`. -/
theorem isSubDPIdeal_ker_toZModPow_inf (e : ℕ) :
    (dividedPowers p).IsSubDPIdeal
      (RingHom.ker (toZModPow (p := p) e) ⊓ Ideal.span {(p : ℤ_[p])}) := by
  rw [ker_toZModPow e]
  rcases eq_or_ne e 0 with rfl | he
  · simp [Ideal.span_singleton_one, DividedPowers.IsSubDPIdeal.self]
  · have hle : Ideal.span {(p : ℤ_[p]) ^ e} ≤ Ideal.span {(p : ℤ_[p])} := by
      rw [Ideal.span_singleton_le_span_singleton]
      exact dvd_pow_self _ he
    rw [inf_of_le_left hle]
    exact isSubDPIdeal_span_pow p he

/-- Sharp `p`-adic bound on the divided power filtration of `(p) ⊂ ℤ_[p]`: whenever
`(p - 1) * e ≤ (p - 2) * n`, `(dividedPowers p).pdFiltration n ≤ Ideal.span {(p : ℤ_[p]) ^ e}`. -/
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

private theorem sub_one_mul_le_two_mul {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (e : ℕ) :
    (p - 1) * e ≤ (p - 2) * (2 * e) := by
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le
    omega
  have h1 : p - 1 ≤ (p - 2) * 2 := by omega
  calc (p - 1) * e ≤ ((p - 2) * 2) * e := Nat.mul_le_mul_right e h1
    _ = (p - 2) * (2 * e) := by ring

/-- For an odd prime `p`, the divided power filtration on `(p) ⊂ ℤ_[p]` satisfies
`F^(2e) ≤ (p ^ e)` for every `e : ℕ`. -/
theorem pdFiltration_two_mul_le_span_pow (hp2 : p ≠ 2) (e : ℕ) :
    (dividedPowers p).pdFiltration (2 * e) ≤ Ideal.span {(p : ℤ_[p]) ^ e} :=
  pdFiltration_le_span_pow p (sub_one_mul_le_two_mul hp2 e)

/-- The canonical divided power ideal `(p) ⊂ ℤ_[p]` is not PD-nilpotent for any prime `p`. -/
theorem not_isPDNilpotent_dividedPowers : ¬ (dividedPowers p).IsPDNilpotent := by
  rw [DividedPowers.isPDNilpotent_iff_eq_bot, Ideal.span_singleton_eq_bot]
  exact NeZero.ne _

end GeneralPrime

section PrimeTwo

/-- In `ℤ_[2]`, `γ₂(2) = 2`. -/
theorem dpow_two_two : (dividedPowers 2).dpow 2 (2 : ℤ_[2]) = 2 := by
  apply Subtype.coe_injective
  have h := coe_dpow_p 2 2
  norm_num at h
  exact h

/-- For `p = 2` and every `n : ℕ`, the `2`-adic valuation of `γₙ(2)` equals the sum of the binary
digits of `n`. -/
theorem valuation_dpow_two (n : ℕ) :
    ((dividedPowers 2).dpow n (2 : ℤ_[2])).valuation = (Nat.digits 2 n).sum := by
  simpa only [Nat.cast_ofNat, Nat.reduceSub, one_mul, zero_mul, zero_add] using
    sub_one_mul_valuation_dpow_p 2 n

/-- For every `a : ℕ`, the `2`-adic valuation of `γ_(2^a)(2)` in `ℤ_[2]` is `1`. -/
theorem valuation_dpow_two_pow (a : ℕ) :
    ((dividedPowers 2).dpow (2 ^ a) (2 : ℤ_[2])).valuation = 1 := by
  rw [valuation_dpow_two, ← mul_one (2 ^ a), Nat.digits_base_pow_mul (by decide) one_pos]
  simp

/-- For every `a : ℕ`, `γ_(2^a)(2)` in `ℤ_[2]` is `2` times a unit of `ℤ_[2]`. -/
theorem exists_unit_mul_two_eq_dpow_two_pow (a : ℕ) :
    ∃ u : ℤ_[2]ˣ, (dividedPowers 2).dpow (2 ^ a) (2 : ℤ_[2]) = (u : ℤ_[2]) * 2 := by
  have hne : (dividedPowers 2).dpow (2 ^ a) (2 : ℤ_[2]) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using dpow_p_ne_zero 2 (2 ^ a)
  refine ⟨unitCoeff hne, ?_⟩
  have hspec := unitCoeff_spec hne
  rw [valuation_dpow_two_pow a, pow_one] at hspec
  simpa only [Nat.cast_ofNat] using hspec

/-- For `p = 2` and every `n ≠ 0`, the `n`-th divided power filtration step of `(2) ⊂ ℤ_[2]`
equals `(2)` itself. -/
theorem pdFiltration_two_eq {n : ℕ} (hn : n ≠ 0) :
    (dividedPowers 2).pdFiltration n = Ideal.span {(2 : ℤ_[2])} := by
  refine le_antisymm ?_ ?_
  · simpa only [Nat.cast_ofNat] using (dividedPowers 2).pdFiltration_le_self hn
  · rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨u, hu⟩ := exists_unit_mul_two_eq_dpow_two_pow n
    have h2_mem : (2 : ℤ_[2]) ∈ Ideal.span {((2 : ℕ) : ℤ_[2])} := by
      rw [Ideal.mem_span_singleton, Nat.cast_ofNat]
    have hmem : (dividedPowers 2).dpow (2 ^ n) (2 : ℤ_[2]) ∈ (dividedPowers 2).pdFiltration n :=
      (dividedPowers 2).dpow_mem_pdFiltration_of_le Nat.lt_two_pow_self.le h2_mem
    have h2 : (2 : ℤ_[2]) = (u⁻¹ : ℤ_[2]ˣ) * (dividedPowers 2).dpow (2 ^ n) (2 : ℤ_[2]) := by
      rw [hu, ← mul_assoc, Units.inv_mul, one_mul]
    rw [h2]
    exact Ideal.mul_mem_left _ _ hmem

/-- In `ℤ_[2]`, `2` lies in every step of the divided power filtration of `(2)`. -/
theorem two_mem_pdFiltration_two (n : ℕ) :
    (2 : ℤ_[2]) ∈ (dividedPowers 2).pdFiltration n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [pdFiltration_two_eq hn]
    exact Ideal.subset_span (Set.mem_singleton _)

/-- In `ℤ_[2]`, `2` does not belong to `(2) ^ 2`. -/
theorem two_notMem_span_two_sq : (2 : ℤ_[2]) ∉ (Ideal.span {(2 : ℤ_[2])}) ^ 2 := by
  rw [Ideal.span_singleton_pow]
  intro h
  have hval := (mem_span_pow_iff_le_valuation (2 : ℤ_[2]) (NeZero.ne _) 2).mp <| by
    simpa only [Nat.cast_ofNat] using h
  have hvp : ((2 : ℤ_[2])).valuation = 1 := by
    simpa only [Nat.cast_ofNat] using valuation_p (p := 2)
  omega

/-- Strict containment `(2) ^ 2 < F²((2))` in `ℤ_[2]`. -/
theorem span_two_sq_lt_pdFiltration_two :
    (Ideal.span {(2 : ℤ_[2])}) ^ 2 < (dividedPowers 2).pdFiltration 2 := by
  have hle : (Ideal.span {(2 : ℤ_[2])}) ^ 2 ≤ (dividedPowers 2).pdFiltration 2 := by
    simpa only [Nat.cast_ofNat] using (dividedPowers 2).pow_le_pdFiltration 2
  exact lt_of_le_of_ne hle fun h ↦
    two_notMem_span_two_sq (h.symm ▸ two_mem_pdFiltration_two 2)

end PrimeTwo

end PadicInt

namespace ZMod

section Canonical

variable (p : ℕ) [hp : Fact p.Prime] (e : ℕ)

private theorem span_p_eq_map_toZModPow :
    Ideal.span {(p : ZMod (p ^ e))} =
      (Ideal.span {(p : ℤ_[p])}).map (PadicInt.toZModPow e) := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

/-- The canonical divided power structure on `Ideal.span {(p : ZMod (p ^ e))}` induced from
`PadicInt.dividedPowers p` along the quotient map `PadicInt.toZModPow e`. -/
noncomputable def dividedPowers : DividedPowers (Ideal.span {(p : ZMod (p ^ e))}) :=
  DividedPowers.Quotient.OfSurjective.dividedPowers (PadicInt.dividedPowers p)
    (ZMod.ringHom_surjective (PadicInt.toZModPow e))
    (span_p_eq_map_toZModPow p e)
    (PadicInt.isSubDPIdeal_ker_toZModPow_inf p e)

/-- The canonical quotient `PadicInt.toZModPow e : ℤ_[p] →+* ZMod (p ^ e)` is a divided power
morphism from `PadicInt.dividedPowers p` to `ZMod.dividedPowers p e`. -/
theorem toZModPow_isDPMorphism :
    (PadicInt.dividedPowers p).IsDPMorphism (ZMod.dividedPowers p e) (PadicInt.toZModPow e) :=
  DividedPowers.Quotient.OfSurjective.isDPMorphism (PadicInt.dividedPowers p)
    (ZMod.ringHom_surjective (PadicInt.toZModPow e))
    (span_p_eq_map_toZModPow p e)
    (PadicInt.isSubDPIdeal_ker_toZModPow_inf p e)

/-- Compatibility of `ZMod.dividedPowers p e` with `PadicInt.toZModPow e`. -/
theorem dividedPowers_dpow_toZModPow {n : ℕ} {x : ℤ_[p]} (hx : x ∈ Ideal.span {(p : ℤ_[p])}) :
    (ZMod.dividedPowers p e).dpow n (PadicInt.toZModPow e x) =
      PadicInt.toZModPow e ((PadicInt.dividedPowers p).dpow n x) :=
  (toZModPow_isDPMorphism p e).dpow_comp x hx

/-- `ZMod.dividedPowers p e` is the unique divided power structure on `(p) ⊂ ZMod (p ^ e)` making
`PadicInt.toZModPow e` a divided power morphism. -/
theorem dividedPowers_unique (hquot : DividedPowers (Ideal.span {(p : ZMod (p ^ e))}))
    (hm : (PadicInt.dividedPowers p).IsDPMorphism hquot (PadicInt.toZModPow e)) :
    hquot = ZMod.dividedPowers p e :=
  DividedPowers.Quotient.OfSurjective.dividedPowers_unique (PadicInt.dividedPowers p)
    (ZMod.ringHom_surjective (PadicInt.toZModPow e))
    (span_p_eq_map_toZModPow p e)
    (PadicInt.isSubDPIdeal_ker_toZModPow_inf p e) hquot hm

/-- The divided power filtration of `ZMod.dividedPowers p e` is the image under `toZModPow e` of
the divided power filtration of `PadicInt.dividedPowers p`. -/
theorem pdFiltration_dividedPowers (n : ℕ) :
    (ZMod.dividedPowers p e).pdFiltration n =
      ((PadicInt.dividedPowers p).pdFiltration n).map (PadicInt.toZModPow e) :=
  ((toZModPow_isDPMorphism p e).map_pdFiltration_eq (span_p_eq_map_toZModPow p e).symm n).symm

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

end Canonical

section PrimeTwoAndClassification

/-- For every `e : ℕ` and `n ≠ 0`, the `n`-th divided power filtration step of
`ZMod.dividedPowers 2 e` equals `Ideal.span {(2 : ZMod (2 ^ e))}`. -/
theorem pdFiltration_dividedPowers_two {e n : ℕ} (hn : n ≠ 0) :
    (ZMod.dividedPowers 2 e).pdFiltration n = Ideal.span {(2 : ZMod (2 ^ e))} := by
  rw [pdFiltration_dividedPowers 2 e n, PadicInt.pdFiltration_two_eq hn]
  simpa only [Nat.cast_ofNat] using (span_p_eq_map_toZModPow 2 e).symm

/-- In `ZMod (2 ^ e)`, `γ₂(2) = 2` for `ZMod.dividedPowers 2 e`. -/
theorem dividedPowers_two_dpow_two (e : ℕ) :
    (ZMod.dividedPowers 2 e).dpow 2 (2 : ZMod (2 ^ e)) = 2 := by
  have hp_mem : (2 : ℤ_[2]) ∈ Ideal.span {((2 : ℕ) : ℤ_[2])} := by
    rw [Ideal.mem_span_singleton, Nat.cast_ofNat]
  have h := dividedPowers_dpow_toZModPow 2 e (n := 2) hp_mem
  rw [map_ofNat, PadicInt.dpow_two_two, map_ofNat] at h
  exact h

/-- For every `e, a : ℕ`, `(ZMod.dividedPowers 2 e).dpow (2 ^ a) 2` is twice a unit in
`ZMod (2 ^ e)`. -/
theorem exists_unit_mul_two_eq_dpow_two_pow (e a : ℕ) :
    ∃ u : (ZMod (2 ^ e))ˣ,
      (ZMod.dividedPowers 2 e).dpow (2 ^ a) (2 : ZMod (2 ^ e)) = (u : ZMod (2 ^ e)) * 2 := by
  obtain ⟨u, hu⟩ := PadicInt.exists_unit_mul_two_eq_dpow_two_pow a
  refine ⟨Units.map (PadicInt.toZModPow (p := 2) e).toMonoidHom u, ?_⟩
  have hp_mem : (2 : ℤ_[2]) ∈ Ideal.span {((2 : ℕ) : ℤ_[2])} := by
    rw [Ideal.mem_span_singleton, Nat.cast_ofNat]
  have h := dividedPowers_dpow_toZModPow 2 e (n := 2 ^ a) hp_mem
  rw [map_ofNat, hu, map_mul, map_ofNat] at h
  simpa using h

/-- Complete classification of PD-nilpotence for the canonical divided power structure on
`(p) ⊂ ZMod (p ^ e)`: it is PD-nilpotent if and only if `p` is odd (`p ≠ 2`) or `e ≤ 1`. -/
theorem isPDNilpotent_dividedPowers_iff (p : ℕ) [hp : Fact p.Prime] (e : ℕ) :
    (ZMod.dividedPowers p e).IsPDNilpotent ↔ p ≠ 2 ∨ e ≤ 1 := by
  constructor
  · intro h
    by_contra! hneg
    rcases hneg with ⟨rfl, he⟩
    obtain ⟨n, hn, hbot⟩ := (ZMod.dividedPowers 2 e).isPDNilpotent_iff.mp h
    rw [pdFiltration_dividedPowers_two hn.ne', Ideal.span_singleton_eq_bot] at hbot
    have hdvd : 2 ^ e ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (2 ^ e)).mp (by simpa using hbot)
    have hle : 2 ^ e ≤ 2 := Nat.le_of_dvd (by decide) hdvd
    have h4 : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) he
    omega
  · rintro (hp2 | he)
    · exact (ZMod.dividedPowers p e).isPDNilpotent_iff_exists_eq_bot.mpr
        ⟨2 * e, pdFiltration_dividedPowers_eq_bot p e (PadicInt.sub_one_mul_le_two_mul hp2 e)⟩
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
    ZMod.dividedPowers 2 2 ≠ DividedPowers.OfSquareZero.dividedPowers (span_pow_eq_zero 2 2) := by
  intro h
  have hnil : (ZMod.dividedPowers 2 2).IsPDNilpotent :=
    h ▸ DividedPowers.OfSquareZero.isPDNilpotent (span_pow_eq_zero 2 2)
  exact not_isPDNilpotent_dividedPowers_two le_rfl hnil

end PrimeTwoAndClassification

end ZMod
