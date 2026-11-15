/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.StickelbergerPhi.Primary
import TauCeti.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.RingTheory.Ideal.Quotient.Coprime

/-!
# The Eisenstein reciprocity law

Let `p` be an odd prime, `K = ℚ(ζ_p)` and `ζ` a primitive `p`-th root of unity, so that
`𝓞 K = ℤ[ζ]`. Write `(x / 𝔞)_p` for the `p`-th power residue symbol
`Ideal.powerResidueSymbolIdeal 𝔞 p (Ideal.Quotient.mk 𝔞 x)`, and `(x / y)_p` when `𝔞 = (y)`.

For a primary element `α` of `𝓞 K` (`TauCeti.IsEisensteinPrimary hζ.toInteger α`) and an integer
`a` not divisible by `p`, **Eisenstein's reciprocity law** states that

  `(α / a)_p = (a / α)_p`.

When `(a)` and `(α)` are not coprime in `𝓞 K`, both residue symbols vanish and the equality still
holds; when `α` is a primary unit or `a = ±1`, both sides are `1`.

The proof proceeds in three steps:

1. **Norm of an ideal** (`IsPrimitiveRoot.eisenstein_reciprocity_absNorm`): for any ideal `𝔅` of
   `𝓞 K` whose norm is prime to `p`, `(α / N 𝔅)_p = (N 𝔅 / α)_p`. When `(α)` and `(N 𝔅)` are
   coprime, `N((α))` and `N 𝔅` are coprime (`Ideal.absNorm_coprime_of_isCoprime_span_natCast`), so
   `(Φ((α)) / 𝔅)_p = (N 𝔅 / (α))_p` (`Ideal.powerResidueSymbolIdeal_stickelbergerPhi`) while
   `(α ^ γ / 𝔅)_p = (α / N 𝔅)_p` (`Ideal.powerResidueSymbolIdeal_stickelbergerProduct`). Since `α`
   is primary and `p` is odd, `Φ((α)) = ±α ^ γ`
   (`IsPrimitiveRoot.stickelbergerPhi_eq_or_eq_neg_stickelbergerProduct`) and `(-1 / 𝔅)_p = 1`.
2. **Rational primes** (`IsPrimitiveRoot.eisenstein_reciprocity_prime`): for a prime `q ≠ p` and a
   prime `P` of `𝓞 K` above `q`, `N P = q ^ f` where `f = f(P/q)` is the multiplicative order of
   `q` in `(ℤ/p)ˣ`, so `0 < f < p` and `gcd(f, p) = 1`. Specialising step 1 to `𝔅 = P` gives
   `(α / q)_p ^ f = (q / α)_p ^ f`, and raising `p`-th roots of unity to an exponent prime to `p`
   is injective.
3. **Multiplicative extension** (`IsPrimitiveRoot.eisenstein_reciprocity_natCast`,
   `IsPrimitiveRoot.eisenstein_reciprocity`): factor `|a|` into primes different from `p`, and
   handle the sign via `(-a) = (a)` on the ideal side and `(-1 / (α))_p = 1` on the numerator side.

For an arbitrary multiple `ζ ^ c * α` of a primary element `α`, evaluating `(ζ / a)_p` gives the
explicit Fermat-quotient factor `ζ ^ (c * ((|a| ^ (p - 1) - 1) / p))`, showing that the primary
normalisation cannot be omitted unless `|a| ^ (p - 1) ≡ 1 (mod p ^ 2)`.

## Main results

* `IsPrimitiveRoot.eisenstein_reciprocity_absNorm`: `(α / N 𝔅)_p = (N 𝔅 / α)_p` for primary `α`
  and `N 𝔅` prime to `p`.
* `IsPrimitiveRoot.eisenstein_reciprocity_prime`: `(α / q)_p = (q / α)_p` for primary `α` and a
  prime `q ≠ p`.
* `IsPrimitiveRoot.eisenstein_reciprocity_natCast`: `(α / n)_p = (n / α)_p` for primary `α` and
  `p ∤ n`.
* `IsPrimitiveRoot.eisenstein_reciprocity`: `(α / a)_p = (a / α)_p` for primary `α` and
  `(p : ℤ) ∤ a`.
* `IsPrimitiveRoot.powerResidueSymbolIdeal_span_intCast_toInteger`:
  `(ζ / a)_p = ζ ^ ((|a| ^ (p - 1) - 1) / p)` for `(p : ℤ) ∤ a`.
* `IsPrimitiveRoot.powerResidueSymbolIdeal_span_intCast_toInteger_pow_mul`:
  `((ζ ^ c * α) / a)_p = ζ ^ (c * ((|a| ^ (p - 1) - 1) / p)) * (a / (ζ ^ c * α))_p`.
* `IsPrimitiveRoot.powerResidueSymbolIdeal_span_intCast_toInteger_mul_eq_iff`: for `(α)` coprime to
  `(a)`, `((ζ * α) / a)_p = (a / (ζ * α))_p` if and only if `p ^ 2 ∣ |a| ^ (p - 1) - 1`.

## References

* G. Eisenstein, *Beweis des Reciprocitätssatzes für die cubischen Reste in der Theorie der aus
  dritten Wurzeln der Einheit zusammengesetzten complexen Zahlen*, J. Reine Angew. Math. 27 (1844),
  and *Nachtrag zum cubischen Reciprocitätssatze ...*, J. Reine Angew. Math. 39 (1850).
* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §4, Theorem 4.1 and (25).
* N. Xu, *Reciprocity Laws*, §6, Theorem 6.9 and Corollary 6.13.
* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 14, §2.
-/

public section

open NumberField Ideal UniqueFactorizationMonoid

namespace IsPrimitiveRoot

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

/-- **Eisenstein reciprocity at the norm of an ideal.** Let `p` be an odd prime, `α ∈ 𝓞 K` a
primary integer of `ℚ(ζ_p)`, and `𝔅` an ideal of `𝓞 K` whose norm is prime to `p`. Then
`(α / N 𝔅)_p = (N 𝔅 / α)_p`, the `p`-th power residue symbols at `(N 𝔅)` and `(α)`. -/
theorem eisenstein_reciprocity_absNorm (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {𝔅 : Ideal (𝓞 K)}
    (h𝔅 : (absNorm 𝔅).Coprime p) :
    powerResidueSymbolIdeal (span {(absNorm 𝔅 : 𝓞 K)}) p
        (Ideal.Quotient.mk (span {(absNorm 𝔅 : 𝓞 K)}) α) =
      powerResidueSymbolIdeal (span {α}) p
        (Ideal.Quotient.mk (span {α}) (absNorm 𝔅 : 𝓞 K)) := by
  by_cases hc : IsCoprime (span {α}) (span {(absNorm 𝔅 : 𝓞 K)})
  · have hp := (Fact.out : p.Prime)
    have hα𝔅 : (absNorm (span {α})).Coprime (absNorm 𝔅) :=
      absNorm_coprime_of_isCoprime_span_natCast hc
    rw [← powerResidueSymbolIdeal_stickelbergerProduct hp.two_le,
      ← powerResidueSymbolIdeal_stickelbergerPhi (span {α}) 𝔅 h𝔅 hα𝔅 hp.two_le]
    rcases hζ.stickelbergerPhi_eq_or_eq_neg_stickelbergerProduct hp2 hα with hΦ | hΦ
    · rw [hΦ]
    · rw [hΦ, map_neg, powerResidueSymbolIdeal_neg (hp.odd_of_ne_two hp2)]
  · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hc,
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr (mt IsCoprime.symm hc)]

/-- **Eisenstein reciprocity at a rational prime.** For an odd prime `p`, a primary element `α` of
`ℚ(ζ_p)` and a rational prime `q ≠ p`, `(α / q)_p = (q / α)_p`. -/
theorem eisenstein_reciprocity_prime (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) :
    powerResidueSymbolIdeal (span {(q : 𝓞 K)}) p (Ideal.Quotient.mk (span {(q : 𝓞 K)}) α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk (span {α}) (q : 𝓞 K)) := by
  by_cases hc : IsCoprime (span {α}) (span {(q : 𝓞 K)})
  · have hp := (Fact.out : p.Prime)
    have := Fact.mk hq
    have : (span {(q : ℤ)}).IsPrime :=
      (span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hq)
    obtain ⟨⟨P, _, _⟩⟩ := (inferInstance : Nonempty ((span {(q : ℤ)}).primesOver (𝓞 K)))
    set f := P.inertiaDeg ℤ with hf_def
    have hqp_cop : q.Coprime p := (Nat.coprime_primes hq hp).mpr hqp
    have hf_cop : f.Coprime p := by
      have hf_eq : f = orderOf (ZMod.unitOfCoprime q hqp_cop) := by
        rw [hf_def, IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd q K P
            (hq.coprime_iff_not_dvd.mp hqp_cop),
          ← orderOf_injective _ Units.coeHom_injective, Units.coeHom_apply, ZMod.coe_unitOfCoprime]
      have hf_lt : f < p := (hf_eq ▸ orderOf_le_card_univ).trans_lt
        (by rw [ZMod.card_units_eq_totient, Nat.totient_prime hp]; exact Nat.sub_lt hp.pos one_pos)
      exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (P.inertiaDeg_pos ℤ) hf_lt)).symm
    have hNP : absNorm P = q ^ f := (pow_inertiaDeg q P).symm
    have hPcop : (absNorm P).Coprime p := hNP ▸ hqp_cop.pow_left f
    have hpow := hζ.eisenstein_reciprocity_absNorm hp2 hα hPcop
    rw [hNP, Nat.cast_pow, ← span_singleton_pow, powerResidueSymbolIdeal_pow_right,
      map_pow, map_pow] at hpow
    have hx : powerResidueSymbolIdeal (span {(q : 𝓞 K)}) p
        (Ideal.Quotient.mk (span {(q : 𝓞 K)}) α) ^ p = 1 :=
      powerResidueSymbolIdeal_pow_eq_one
        (Ideal.Quotient.isUnit_mk_iff.mpr (isCoprime_iff_sup_eq.mp hc))
    have hy : powerResidueSymbolIdeal (span {α}) p
        (Ideal.Quotient.mk (span {α}) (q : 𝓞 K)) ^ p = 1 :=
      powerResidueSymbolIdeal_pow_eq_one
        (Ideal.Quotient.isUnit_mk_iff.mpr (isCoprime_iff_sup_eq.mp hc.symm))
    apply RingOfIntegers.coe_injective
    have hy0 : (powerResidueSymbolIdeal (span {α}) p
        (Ideal.Quotient.mk (span {α}) (q : 𝓞 K)) : K) ≠ 0 := by
      intro h0
      have h1 : (0 : K) ^ p = 1 := by
        rw [← h0, ← map_pow (algebraMap (𝓞 K) K), hy, map_one]
      exact zero_ne_one ((zero_pow hp.ne_zero).symm.trans h1)
    refine (div_eq_one_iff_eq hy0).mp ((pow_eq_one_iff_of_coprime hf_cop).mp ⟨?_, ?_⟩)
    · rw [div_pow, ← map_pow (algebraMap (𝓞 K) K), hpow, map_pow (algebraMap (𝓞 K) K),
        div_self (pow_ne_zero f hy0)]
    · rw [div_pow, ← map_pow (algebraMap (𝓞 K) K), ← map_pow (algebraMap (𝓞 K) K), hx, hy,
        map_one, div_self one_ne_zero]
  · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hc,
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr (mt IsCoprime.symm hc)]

/-- **The Eisenstein reciprocity law for natural numbers.** Let `p` be an odd prime, `α ∈ 𝓞 K` a
primary integer of `ℚ(ζ_p)`, and `n : ℕ` a natural number not divisible by `p`. Then
`(α / n)_p = (n / α)_p`. -/
theorem eisenstein_reciprocity_natCast (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {n : ℕ} (hn : ¬ p ∣ n) :
    powerResidueSymbolIdeal (span {(n : 𝓞 K)}) p (Ideal.Quotient.mk (span {(n : 𝓞 K)}) α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk (span {α}) (n : 𝓞 K)) := by
  induction n using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd (dvd_zero p) hn
  | h₂ n hu =>
    rw [Nat.isUnit_iff.mp hu, Nat.cast_one, span_singleton_one, powerResidueSymbolIdeal_top,
      map_one, MulChar.map_one]
  | h₃ m q hm0 hq ih =>
    have hq' : q.Prime := Nat.prime_iff.mpr hq
    have hqp : q ≠ p := fun h ↦ hn (h ▸ dvd_mul_right q m)
    have hmp : ¬ p ∣ m := fun h ↦ hn (h.mul_left q)
    have hq_ne : span {(q : 𝓞 K)} ≠ ⊥ :=
      span_singleton_eq_bot.not.mpr (Nat.cast_ne_zero.mpr hq'.ne_zero)
    have hm_ne : span {(m : 𝓞 K)} ≠ ⊥ :=
      span_singleton_eq_bot.not.mpr (Nat.cast_ne_zero.mpr hm0)
    rw [Nat.cast_mul, ← span_singleton_mul_span_singleton,
      powerResidueSymbolIdeal_mul_right hq_ne hm_ne,
      hζ.eisenstein_reciprocity_prime hp2 hα hq' hqp, ih hmp, map_mul, map_mul]

/-- **The Eisenstein reciprocity law.** Let `p` be an odd prime, `K = ℚ(ζ_p)` and `α ∈ 𝓞 K` a
primary cyclotomic integer (`TauCeti.IsEisensteinPrimary hζ.toInteger α`). For every rational
integer `a` not divisible by `p`,

  `(α / a)_p = (a / α)_p`,

the `p`-th power residue symbols at `(a)` and `(α)`. When `(a)` and `(α)` are not coprime, both
symbols vanish. -/
theorem eisenstein_reciprocity (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p (Ideal.Quotient.mk (span {(a : 𝓞 K)}) α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk (span {α}) (a : 𝓞 K)) := by
  have hn : ¬ p ∣ a.natAbs := fun h ↦ ha (Int.ofNat_dvd_left.mpr h)
  rcases Int.natAbs_eq a with h | h
  · rw [h, Int.cast_natCast]
    exact hζ.eisenstein_reciprocity_natCast hp2 hα hn
  · have hp := (Fact.out : p.Prime)
    rw [h, Int.cast_neg, Int.cast_natCast, span_singleton_neg, map_neg,
      powerResidueSymbolIdeal_neg (hp.odd_of_ne_two hp2)]
    exact hζ.eisenstein_reciprocity_natCast hp2 hα hn

/-! ### Non-primary multiples and the Fermat quotient of `a` -/

/-- **The `p`-th power residue symbol of `ζ` at a rational integer.** For `a ∈ ℤ` with `p ∤ a`,
`(ζ / a)_p = ζ ^ ((|a| ^ (p - 1) - 1) / p)`. -/
theorem powerResidueSymbolIdeal_span_intCast_toInteger {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p
        (Ideal.Quotient.mk (span {(a : 𝓞 K)}) hζ.toInteger) =
      hζ.toInteger ^ ((a.natAbs ^ (p - 1) - 1) / p) := by
  have hp := (Fact.out : p.Prime)
  have hN : absNorm (span {(a : 𝓞 K)}) = a.natAbs ^ (p - 1) := by
    rw [absNorm_span_intCast, RingOfIntegers.rank, IsCyclotomicExtension.Rat.finrank p K,
      Nat.totient_prime hp]
  have hcop : (absNorm (span {(a : 𝓞 K)})).Coprime p :=
    hN ▸ ((hp.coprime_iff_not_dvd.mpr fun h ↦ ha (Int.ofNat_dvd_left.mpr h)).symm).pow_left _
  rw [powerResidueSymbolIdeal_mk_of_pow_eq_one hcop hζ.toInteger_isPrimitiveRoot.pow_eq_one, hN]

/-- **Eisenstein reciprocity for an arbitrary `ζ`-power multiple of a primary element.** For primary
`α`, `c : ℕ` and `a ∈ ℤ` not divisible by `p`,
`((ζ ^ c * α) / a)_p = ζ ^ (c * ((|a| ^ (p - 1) - 1) / p)) * (a / (ζ ^ c * α))_p`. -/
theorem powerResidueSymbolIdeal_span_intCast_toInteger_pow_mul (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) (c : ℕ) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p
        (Ideal.Quotient.mk (span {(a : 𝓞 K)}) (hζ.toInteger ^ c * α)) =
      hζ.toInteger ^ (c * ((a.natAbs ^ (p - 1) - 1) / p)) *
        powerResidueSymbolIdeal (span {hζ.toInteger ^ c * α}) p
          (Ideal.Quotient.mk (span {hζ.toInteger ^ c * α}) (a : 𝓞 K)) := by
  have hp := (Fact.out : p.Prime)
  have hspan : span {hζ.toInteger ^ c * α} = span {α} :=
    span_singleton_eq_span_singleton.mpr
      (Associated.symm ⟨((hζ.toInteger_isPrimitiveRoot.isUnit hp.ne_zero).pow c).unit,
        by simp [mul_comm]⟩)
  have hcongr {𝔞 𝔟 : Ideal (𝓞 K)} (h : 𝔞 = 𝔟) :
      powerResidueSymbolIdeal 𝔞 p (Ideal.Quotient.mk 𝔞 (a : 𝓞 K)) =
        powerResidueSymbolIdeal 𝔟 p (Ideal.Quotient.mk 𝔟 (a : 𝓞 K)) := by
    subst h; rfl
  rw [map_mul, map_mul, map_pow, map_pow,
    hζ.powerResidueSymbolIdeal_span_intCast_toInteger ha, ← pow_mul, mul_comm _ c,
    hζ.eisenstein_reciprocity hp2 hα ha, hcongr hspan]

/-- **Failure of unshifted reciprocity without primary normalisation.** When `α` is primary and
`(α)` is coprime to `(a)` (`p ∤ a`), the unshifted identity `((ζ * α) / a)_p = (a / (ζ * α))_p`
holds if and only if `p ^ 2 ∣ |a| ^ (p - 1) - 1`. -/
theorem powerResidueSymbolIdeal_span_intCast_toInteger_mul_eq_iff (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a)
    (hc : IsCoprime (span {α}) (span {(a : 𝓞 K)})) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p
        (Ideal.Quotient.mk (span {(a : 𝓞 K)}) (hζ.toInteger * α)) =
      powerResidueSymbolIdeal (span {hζ.toInteger * α}) p
        (Ideal.Quotient.mk (span {hζ.toInteger * α}) (a : 𝓞 K)) ↔
      p ^ 2 ∣ a.natAbs ^ (p - 1) - 1 := by
  have hp := (Fact.out : p.Prime)
  have h1 := hζ.powerResidueSymbolIdeal_span_intCast_toInteger_pow_mul hp2 hα 1 ha
  rw [pow_one, one_mul] at h1
  rw [h1]
  have hspan : span {hζ.toInteger * α} = span {α} :=
    span_singleton_eq_span_singleton.mpr
      (Associated.symm ⟨(hζ.toInteger_isPrimitiveRoot.isUnit hp.ne_zero).unit, by simp [mul_comm]⟩)
  have hne : powerResidueSymbolIdeal (span {hζ.toInteger * α}) p
      (Ideal.Quotient.mk (span {hζ.toInteger * α}) (a : 𝓞 K)) ≠ 0 := by
    rw [Ne, powerResidueSymbolIdeal_mk_eq_zero_iff, hspan, not_not]
    exact hc.symm
  have hpdvd : p ∣ a.natAbs ^ (p - 1) - 1 := by
    have ha0 : (a.natAbs : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun h ↦ ha (Int.ofNat_dvd_left.mpr h)
    have hpow1 : a.natAbs ^ (p - 1) ≥ 1 :=
      Nat.one_le_pow _ _ (Nat.pos_of_ne_zero fun h0 ↦ ha (by simp [Int.natAbs_eq_zero.mp h0]))
    rw [← Nat.modEq_iff_dvd' hpow1, ← ZMod.natCast_eq_natCast_iff]
    simpa using (ZMod.pow_card_sub_one_eq_one ha0).symm
  rw [mul_eq_right₀ hne, hζ.toInteger_isPrimitiveRoot.pow_eq_one_iff_dvd, sq,
    Nat.dvd_div_iff_mul_dvd hpdvd]

end IsPrimitiveRoot

section Examples

open Ideal

private instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- At `p = 3` and `K = ℚ(ζ₃)`, the element `π = -1 - 3ζ` (of norm `7`) is Eisenstein-primary. -/
private theorem isEisensteinPrimary_neg_one_sub_three_mul {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    TauCeti.IsEisensteinPrimary hζ.toInteger ((-1 : 𝓞 K) - 3 * hζ.toInteger) := by
  refine TauCeti.isEisensteinPrimary_iff.mpr
    ⟨hζ.isCoprime_toInteger_sub_one_iff.mpr fun h ↦ ?_, -1, ?_⟩
  · have h3 : hζ.toInteger - 1 ∣ (3 : 𝓞 K) * hζ.toInteger :=
      hζ.toInteger_sub_one_dvd_prime'.mul_right _
    have h1 : hζ.toInteger - 1 ∣ (-1 : 𝓞 K) := by
      simpa [sub_eq_add_neg] using dvd_add h h3
    exact hζ.zeta_sub_one_prime'.not_isUnit (isUnit_of_dvd_unit h1 isUnit_neg_one)
  · have h3 := (hζ.toInteger_sub_one_sq_dvd_intCast_iff (by decide)).mpr (dvd_refl (3 : ℤ))
    convert h3.mul_right (-hζ.toInteger) using 1
    push_cast
    ring

/- For `p = 3`, `π = -1 - 3ζ` (primary of norm `7`) and `𝔅 = (2)` (`N 𝔅 = 4`), Eisenstein
reciprocity at the norm gives `(π / 4)_3 = (4 / π)_3`. -/
example {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3) {π : 𝓞 K} (hπ : π = -1 - 3 * hζ.toInteger) :
    powerResidueSymbolIdeal (span {(4 : 𝓞 K)}) 3 (Ideal.Quotient.mk _ π) =
      powerResidueSymbolIdeal (span {π}) 3 (Ideal.Quotient.mk _ (4 : 𝓞 K)) := by
  subst hπ
  have hN : absNorm (span {((2 : ℕ) : 𝓞 K)}) = 4 := by
    rw [absNorm_span_natCast, RingOfIntegers.rank, IsCyclotomicExtension.Rat.finrank 3 K]
    decide
  have h := hζ.eisenstein_reciprocity_absNorm (by decide)
    (isEisensteinPrimary_neg_one_sub_three_mul hζ)
    (𝔅 := span {((2 : ℕ) : 𝓞 K)}) (by rw [hN]; decide)
  rw [hN, Nat.cast_ofNat] at h
  exact h

/- For `p = 3`, `π = -1 - 3ζ` and `a = 2`, Eisenstein reciprocity gives `(π / 2)_3 = (2 / π)_3`,
the case of cubic reciprocity with one rational prime. -/
example {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3) {π : 𝓞 K} (hπ : π = -1 - 3 * hζ.toInteger) :
    powerResidueSymbolIdeal (span {(2 : 𝓞 K)}) 3 (Ideal.Quotient.mk _ π) =
      powerResidueSymbolIdeal (span {π}) 3 (Ideal.Quotient.mk _ (2 : 𝓞 K)) := by
  subst hπ
  have h := hζ.eisenstein_reciprocity_natCast (by decide)
    (isEisensteinPrimary_neg_one_sub_three_mul hζ) (n := 2) (by decide)
  rw [Nat.cast_ofNat] at h
  exact h

/- Replacing `1` (which is primary) by `ζ` at `p = 3`, `a = 2` breaks reciprocity because
`2 ^ 2 - 1 = 3` is not divisible by `3 ^ 2 = 9`. -/
example {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    powerResidueSymbolIdeal (span {(2 : 𝓞 K)}) 3 (Ideal.Quotient.mk _ hζ.toInteger) ≠
      powerResidueSymbolIdeal (span {hζ.toInteger}) 3 (Ideal.Quotient.mk _ (2 : 𝓞 K)) := by
  have hc : IsCoprime (span {(1 : 𝓞 K)}) (span {((2 : ℤ) : 𝓞 K)}) :=
    isCoprime_iff_sup_eq.mpr (by rw [span_singleton_one, top_sup_eq])
  have hiff := hζ.powerResidueSymbolIdeal_span_intCast_toInteger_mul_eq_iff (by decide)
    (TauCeti.isEisensteinPrimary_one (ζ := hζ.toInteger)) (a := 2) (by decide) hc
  rw [mul_one, Int.cast_ofNat] at hiff
  exact hiff.not.mpr (by decide)

end Examples
