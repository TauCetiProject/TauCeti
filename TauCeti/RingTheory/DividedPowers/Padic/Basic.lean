/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DividedPowers.Padic
public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
public import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Canonical divided powers on `ZMod (p ^ e)` and `p`-adic valuations

This file develops the `p`-adic valuation and evaluation API for the canonical divided power
structure `PadicInt.dividedPowers p` on `(p) ⊂ ℤ_[p]` and constructs its quotient divided power
structure `ZMod.dividedPowers p e` on `(p) ⊂ ZMod (p ^ e)`.

* For every prime `p` and every `n : ℕ`, the `p`-adic valuation of `γₙ(p) = p ^ n / n!` is
  `n - multiplicity p n.factorial`, and by Legendre's formula
  `(p - 1) * v_p(γₙ(p)) = (p - 2) * n + s_p(n)`.
* For every prime `p` and every `e : ℕ`,
  `RingHom.ker (PadicInt.toZModPow e) ⊓ Ideal.span {(p : ℤ_[p])}` is a sub-PD-ideal of `(p)`
  with `PadicInt.dividedPowers p`, so `PadicInt.dividedPowers p` descends uniquely to a divided
  power structure `ZMod.dividedPowers p e` on `(p) ⊂ ZMod (p ^ e)`.
* For `p = 2`, `(PadicInt.dividedPowers 2).dpow (2 ^ a) 2` has `2`-adic valuation `1` (`2` times
  a unit in `ℤ_[2]`), and `γ₂(2) = 2` in both `ℤ_[2]` and `ZMod (2 ^ e)`.

See `TauCeti.RingTheory.DividedPowers.Padic.Filtration` for the divided power filtrations and
PD-nilpotence classification of `PadicInt.dividedPowers p` and `ZMod.dividedPowers p e`.

## Main definitions

* `ZMod.dividedPowers`: the canonical divided power structure on `Ideal.span {(p : ZMod (p ^ e))}`
  induced from `PadicInt.dividedPowers p` along `PadicInt.toZModPow e`.

## Main results

* `PadicInt.valuation_dpow_p`: `((dividedPowers p).dpow n p).valuation = n - multiplicity p n!`.
* `PadicInt.sub_one_mul_valuation_dpow_p`: Legendre identity
  `(p - 1) * ((dividedPowers p).dpow n p).valuation = (p - 2) * n + (p.digits n).sum`.
* `PadicInt.isSubDPIdeal_span_pow`: `Ideal.span {(p : ℤ_[p]) ^ e}` is a sub-dp-ideal for `e ≠ 0`.
* `PadicInt.isSubDPIdeal_ker_toZModPow_inf`:
  `RingHom.ker (toZModPow e) ⊓ Ideal.span {(p : ℤ_[p])}` is a sub-dp-ideal.
* `PadicInt.valuation_dpow_two`: for `p = 2`, the `2`-adic valuation of `γₙ(2)` is the binary
  digit sum `(Nat.digits 2 n).sum`.
* `ZMod.toZModPow_isDPMorphism`, `ZMod.dividedPowers_dpow_p`, and `ZMod.dividedPowers_unique`:
  compatibility, evaluation on `(p)`, and uniqueness of `ZMod.dividedPowers p e`.

## References

* Mathlib's `PadicInt.dividedPowers` and `DividedPowers.Quotient.OfSurjective.dividedPowers` by
  A. Chambert-Loir and M. I. de Frutos-Fernández.
* [Stacks Project, Section 60.5 (Tag 07HL)](https://stacks.math.columbia.edu/tag/07HL),
  Definition 60.5.2 (Tag 07HM).
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
@[simp]
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

/-- For `e ≠ 0`, `Ideal.span {(p : ℤ_[p]) ^ e}` is a sub-dp-ideal of `PadicInt.dividedPowers p`. -/
theorem isSubDPIdeal_span_pow {e : ℕ} (he : e ≠ 0) :
    (dividedPowers p).IsSubDPIdeal (Ideal.span {(p : ℤ_[p]) ^ e}) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
  have h := (DividedPowers.SubDPIdeal.prod (hI := dividedPowers p)
    (Ideal.span {(p : ℤ_[p]) ^ k})).toIsSubDPIdeal
  simpa [DividedPowers.SubDPIdeal.prod, smul_eq_mul, Ideal.span_singleton_mul_span_singleton,
    ← pow_succ'] using h

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

end GeneralPrime

section PrimeTwo

/-- In `ℤ_[2]`, `γ₂(2) = 2`. -/
@[simp]
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

end PrimeTwo

end PadicInt

namespace ZMod

section Canonical

variable (p : ℕ) [hp : Fact p.Prime] (e : ℕ)

/-- The canonical divided power structure on `Ideal.span {(p : ZMod (p ^ e))}` induced from
`PadicInt.dividedPowers p` along the quotient map `PadicInt.toZModPow e`. -/
noncomputable def dividedPowers : DividedPowers (Ideal.span {(p : ZMod (p ^ e))}) :=
  DividedPowers.Quotient.OfSurjective.dividedPowers (PadicInt.dividedPowers p)
    (ZMod.ringHom_surjective (PadicInt.toZModPow e))
    (PadicInt.map_toZModPow_span_p p e).symm
    (PadicInt.isSubDPIdeal_ker_toZModPow_inf p e)

/-- The canonical quotient `PadicInt.toZModPow e : ℤ_[p] →+* ZMod (p ^ e)` is a divided power
morphism from `PadicInt.dividedPowers p` to `ZMod.dividedPowers p e`. -/
theorem toZModPow_isDPMorphism :
    (PadicInt.dividedPowers p).IsDPMorphism (ZMod.dividedPowers p e) (PadicInt.toZModPow e) :=
  DividedPowers.Quotient.OfSurjective.isDPMorphism (PadicInt.dividedPowers p)
    (ZMod.ringHom_surjective (PadicInt.toZModPow e))
    (PadicInt.map_toZModPow_span_p p e).symm
    (PadicInt.isSubDPIdeal_ker_toZModPow_inf p e)

/-- Evaluation of `ZMod.dividedPowers p e` on the generator `(p : ZMod (p ^ e))`. -/
theorem dividedPowers_dpow_p (n : ℕ) :
    (ZMod.dividedPowers p e).dpow n (p : ZMod (p ^ e)) =
      PadicInt.toZModPow e ((PadicInt.dividedPowers p).dpow n (p : ℤ_[p])) := by
  have hx : (p : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p])} := Ideal.subset_span (Set.mem_singleton _)
  simpa only [map_natCast] using (toZModPow_isDPMorphism p e).dpow_comp _ hx

/-- `ZMod.dividedPowers p e` is the unique divided power structure on `(p) ⊂ ZMod (p ^ e)` making
`PadicInt.toZModPow e` a divided power morphism. -/
theorem dividedPowers_unique (hquot : DividedPowers (Ideal.span {(p : ZMod (p ^ e))}))
    (hm : (PadicInt.dividedPowers p).IsDPMorphism hquot (PadicInt.toZModPow e)) :
    hquot = ZMod.dividedPowers p e :=
  DividedPowers.Quotient.OfSurjective.dividedPowers_unique (PadicInt.dividedPowers p)
    (ZMod.ringHom_surjective (PadicInt.toZModPow e))
    (PadicInt.map_toZModPow_span_p p e).symm
    (PadicInt.isSubDPIdeal_ker_toZModPow_inf p e) hquot hm

end Canonical

section PrimeTwo

/-- In `ZMod (2 ^ e)`, `γ₂(2) = 2` for `ZMod.dividedPowers 2 e`. -/
@[simp]
theorem dividedPowers_two_dpow_two (e : ℕ) :
    (ZMod.dividedPowers 2 e).dpow 2 (2 : ZMod (2 ^ e)) = 2 := by
  have h := dividedPowers_dpow_p 2 e 2
  simpa only [Nat.cast_ofNat, PadicInt.dpow_two_two, map_ofNat] using h

/-- For every `e, a : ℕ`, `(ZMod.dividedPowers 2 e).dpow (2 ^ a) 2` is twice a unit in
`ZMod (2 ^ e)`. -/
theorem exists_unit_mul_two_eq_dpow_two_pow (e a : ℕ) :
    ∃ u : (ZMod (2 ^ e))ˣ,
      (ZMod.dividedPowers 2 e).dpow (2 ^ a) (2 : ZMod (2 ^ e)) = (u : ZMod (2 ^ e)) * 2 := by
  obtain ⟨u, hu⟩ := PadicInt.exists_unit_mul_two_eq_dpow_two_pow a
  refine ⟨Units.map (PadicInt.toZModPow (p := 2) e).toMonoidHom u, ?_⟩
  have h := dividedPowers_dpow_p 2 e (2 ^ a)
  simp only [Nat.cast_ofNat] at h
  rw [h, hu, map_mul, map_ofNat]
  rfl

end PrimeTwo

end ZMod
