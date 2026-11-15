/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.StickelbergerPhi.Primary
import TauCeti.RingTheory.Ideal.Norm.AbsNorm

/-!
# The Eisenstein reciprocity law

Let `p` be an odd prime and `K = ℚ(ζ_p)` the `p`-th cyclotomic field, with ring of integers
`𝓞 K = ℤ[ζ_p]`. An element `α ∈ 𝓞 K` is *primary* (`TauCeti.IsEisensteinPrimary`) if it is prime
to `ζ_p - 1` and congruent to a rational integer modulo `(ζ_p - 1) ^ 2`. **Eisenstein's reciprocity
law** states that for every primary `α ∈ 𝓞 K` and every rational integer `a ∈ ℤ` not divisible by
`p`,

  `(α / a)_p = (a / α)_p`,

where both `p`-th power residue symbols are read at the principal ideals `a 𝓞 K` and `α 𝓞 K` via
`Ideal.powerResidueSymbolIdeal`. When `a` and `α` are not coprime in `𝓞 K`, both symbols vanish;
when `α` is a unit or `a = ±1`, both sides are `1` (provided the other argument is coprime).

For a primary cyclotomic integer `α`, Stickelberger's relation with primary normalization gives
`Φ((α)) = ±α ^ γ` (`IsPrimitiveRoot.stickelbergerPhi_eq_or_eq_neg_stickelbergerProduct`), where
`α ^ γ` is `TauCeti.stickelbergerProduct p α`. Evaluating the `p`-th power residue symbol of both
sides at an ideal `𝔅` of `𝓞 K` whose norm is prime to `p` and to `N(α)` combines
`(Φ((α)) / 𝔅)_p = (N 𝔅 / α)_p` (`Ideal.powerResidueSymbolIdeal_stickelbergerPhi`) with
`(α ^ γ / 𝔅)_p = (α / N 𝔅)_p` (`Ideal.powerResidueSymbolIdeal_stickelbergerProduct`) to give
Eisenstein reciprocity at the norm of an ideal: `(α / N 𝔅)_p = (N 𝔅 / α)_p`. Specializing `𝔅` to
a prime of `𝓞 K` above a rational prime `q ≠ p`, whose residue degree divides `p - 1` and is
therefore coprime to `p`, yields `(α / q)_p = (q / α)_p`, and multiplicativity in `a` together
with invariance under negation for odd `p` gives `(α / a)_p = (a / α)_p`.

Shifting a primary element `α` by `ζ_p ^ c` leaves `(a / ζ_p ^ c α)_p` unchanged while multiplying
`(ζ_p ^ c α / a)_p` by the Fermat-quotient root of unity `ζ_p ^ (c · ((|a| ^ (p - 1) - 1) / p))`
(`IsPrimitiveRoot.eisenstein_reciprocity_toInteger_pow_mul`). In particular, for coprime `α` and
`a`, `(ζ_p α / a)_p = (a / ζ_p α)_p` holds if and only if `|a| ^ (p - 1) ≡ 1 (mod p ^ 2)`
(`IsPrimitiveRoot.eisenstein_reciprocity_toInteger_mul_iff`), so the primary hypothesis cannot be
dropped.

## Main results

* `IsPrimitiveRoot.eisenstein_reciprocity_absNorm`: `(α / N 𝔅)_p = (N 𝔅 / α)_p` for an odd prime
  `p`, a primary `α ∈ 𝓞 K`, and an ideal `𝔅` of `𝓞 K` whose norm is prime to `p`.
* `IsPrimitiveRoot.eisenstein_reciprocity_natCast`: `(α / n)_p = (n / α)_p` for `n : ℕ` with
  `¬ p ∣ n`.
* `IsPrimitiveRoot.eisenstein_reciprocity`: `(α / a)_p = (a / α)_p` for `a : ℤ` with
  `¬ (p : ℤ) ∣ a`.
* `IsPrimitiveRoot.powerResidueSymbolIdeal_span_intCast_mk_toInteger`: the supplementary formula
  `(ζ_p / a)_p = ζ_p ^ ((|a| ^ (p - 1) - 1) / p)` for `a : ℤ` prime to `p`.
* `IsPrimitiveRoot.powerResidueSymbolIdeal_span_intCast_mk_toInteger_eq_one_iff`: `(ζ_p / a)_p = 1`
  if and only if `|a| ^ (p - 1) ≡ 1 (mod p ^ 2)`.
* `IsPrimitiveRoot.eisenstein_reciprocity_toInteger_pow_mul`: the shifted reciprocity law for
  `ζ_p ^ c * α`.
* `IsPrimitiveRoot.eisenstein_reciprocity_toInteger_mul_iff`: for coprime `α` and `a`,
  `(ζ_p * α / a)_p = (a / ζ_p * α)_p` if and only if `|a| ^ (p - 1) ≡ 1 (mod p ^ 2)`.

## References

* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §4, Theorem 4.1 and (25).
* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 14, §2,
  Theorem 1.
* N. Xu, *Reciprocity Laws*, §6, Theorem 6.9 and Corollary 6.13.
-/

public section

open NumberField Ideal UniqueFactorizationMonoid

namespace IsPrimitiveRoot

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

/-- **Eisenstein reciprocity at the norm of an ideal.** Let `p` be an odd prime, `K = ℚ(ζ_p)`,
`α ∈ 𝓞 K` a primary cyclotomic integer, and `𝔅` an ideal of `𝓞 K` whose norm is prime to `p`.
Then `(α / N 𝔅)_p = (N 𝔅 / α)_p`, the `p`-th power residue symbols at the principal ideals
`(N 𝔅) 𝓞 K` and `α 𝓞 K`. If `α` and `N 𝔅` are not coprime in `𝓞 K`, both sides vanish. -/
theorem eisenstein_reciprocity_absNorm (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {𝔅 : Ideal (𝓞 K)}
    (h𝔅 : (absNorm 𝔅).Coprime p) :
    powerResidueSymbolIdeal (span {(absNorm 𝔅 : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (absNorm 𝔅 : 𝓞 K)) := by
  have hp : p.Prime := Fact.out
  by_cases hc : IsCoprime (span {α}) (span {(absNorm 𝔅 : 𝓞 K)})
  swap
  · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hc,
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr (mt IsCoprime.symm hc)]
  have hα𝔅 : (absNorm (span {α})).Coprime (absNorm 𝔅) :=
    absNorm_coprime_of_isCoprime_span_natCast hc
  rw [← powerResidueSymbolIdeal_stickelbergerProduct hp.two_le 𝔅 α,
    ← powerResidueSymbolIdeal_stickelbergerPhi (span {α}) 𝔅 h𝔅 hα𝔅 hp.two_le]
  rcases hζ.stickelbergerPhi_eq_or_eq_neg_stickelbergerProduct hp2 hα with hΦ | hΦ
  · rw [hΦ]
  · rw [hΦ, map_neg, powerResidueSymbolIdeal_neg (hp.odd_of_ne_two hp2)]

/-- Eisenstein reciprocity at a rational prime `q ≠ p`: `(α / q)_p = (q / α)_p`. -/
private theorem eisenstein_reciprocity_natCast_of_prime (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) :
    powerResidueSymbolIdeal (span {(q : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (q : 𝓞 K)) := by
  have hp : p.Prime := Fact.out
  by_cases hc : IsCoprime (span {α}) (span {(q : 𝓞 K)})
  swap
  · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hc,
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr (mt IsCoprime.symm hc)]
  -- Both residue classes are units, so both symbols are `p`-th roots of unity.
  have huL : IsUnit (Ideal.Quotient.mk (span {(q : 𝓞 K)}) α) := not_not.mp <|
    MulChar.apply_eq_zero_iff.not.mp
      fun h ↦ (powerResidueSymbolIdeal_mk_eq_zero_iff (n := p)).mp h hc
  have huR : IsUnit (Ideal.Quotient.mk (span {α}) (q : 𝓞 K)) := not_not.mp <|
    MulChar.apply_eq_zero_iff.not.mp
      fun h ↦ (powerResidueSymbolIdeal_mk_eq_zero_iff (n := p)).mp h hc.symm
  -- Pick a prime `P` of `𝓞 K` above `q`; its norm is `q ^ f` with `f = ord_p(q) ∣ p - 1`.
  have : Fact q.Prime := ⟨hq⟩
  have : (span {(q : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime q
  obtain ⟨⟨P, hP_prime, hP_over⟩⟩ :=
    (inferInstance : Nonempty ((span {(q : ℤ)}).primesOver (𝓞 K)))
  have hq₀ : span {(q : ℤ)} ≠ ⊥ := span_singleton_eq_bot.not.mpr (Nat.cast_ne_zero.mpr hq.ne_zero)
  have hP₀ : P ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hq₀ P
  have : P.IsMaximal := hP_prime.isMaximal hP₀
  have hq_cop : q.Coprime p := (Nat.coprime_primes hq hp).mpr hqp
  have hqp_dvd : ¬ q ∣ p := hq.coprime_iff_not_dvd.mp hq_cop
  have hqf : q ^ P.inertiaDeg ℤ = absNorm P := pow_inertiaDeg q P
  have hP_cop : (absNorm P).Coprime p := hqf ▸ hq_cop.pow_left _
  -- `P.inertiaDeg ℤ` divides `|(ZMod p)ˣ| = p - 1`, which is coprime to `p`.
  have hf_dvd : P.inertiaDeg ℤ ∣ p - 1 := by
    rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd q K P hqp_dvd,
      ← ZMod.coe_unitOfCoprime q hq_cop, orderOf_units, ← Nat.totient_prime hp,
      ← ZMod.card_units_eq_totient]
    exact orderOf_dvd_card
  have hpf : p.Coprime (P.inertiaDeg ℤ) :=
    ((Nat.coprime_self_sub_right hp.pos).mpr (Nat.coprime_one_right p)).coprime_dvd_right hf_dvd
  -- Raise both symbols to the `P.inertiaDeg ℤ`-th power and apply reciprocity at `N P`.
  have hspan : span {(q : 𝓞 K)} ^ P.inertiaDeg ℤ = span {(absNorm P : 𝓞 K)} := by
    rw [span_singleton_pow, ← Nat.cast_pow, hqf]
  have hf_eq :
      powerResidueSymbolIdeal (span {(q : 𝓞 K)}) p (Ideal.Quotient.mk _ α) ^ P.inertiaDeg ℤ =
        powerResidueSymbolIdeal (span {α}) p
          (Ideal.Quotient.mk _ (q : 𝓞 K)) ^ P.inertiaDeg ℤ := by
    rw [← powerResidueSymbolIdeal_pow_right, hspan,
      hζ.eisenstein_reciprocity_absNorm hp2 hα hP_cop, ← hqf, Nat.cast_pow, map_pow, map_pow]
  have hx : (powerResidueSymbolIdeal (span {(q : 𝓞 K)}) p (Ideal.Quotient.mk _ α) : K) ^ p = 1 :=
    mod_cast powerResidueSymbolIdeal_pow_eq_one huL
  have hy : (powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (q : 𝓞 K)) : K) ^ p = 1 :=
    mod_cast powerResidueSymbolIdeal_pow_eq_one huR
  have hxy :
      (powerResidueSymbolIdeal (span {(q : 𝓞 K)}) p
          (Ideal.Quotient.mk _ α) : K) ^ P.inertiaDeg ℤ =
        (powerResidueSymbolIdeal (span {α}) p
          (Ideal.Quotient.mk _ (q : 𝓞 K)) : K) ^ P.inertiaDeg ℤ :=
    mod_cast hf_eq
  have hy0 : (powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (q : 𝓞 K)) : K) ≠ 0 :=
    fun h ↦ one_ne_zero (by rw [← hy, h, zero_pow hp.ne_zero])
  apply RingOfIntegers.coe_injective
  refine (div_eq_one_iff_eq hy0).mp ((pow_eq_one_iff_of_coprime hpf).mp ⟨?_, ?_⟩)
  · rw [div_pow, hx, hy, div_one]
  · rw [div_pow, hxy, div_self (pow_ne_zero _ hy0)]

/-- **The Eisenstein reciprocity law for a natural number.** Let `p` be an odd prime, `K = ℚ(ζ_p)`,
`α ∈ 𝓞 K` a primary cyclotomic integer, and `n : ℕ` a natural number not divisible by `p`. Then
`(α / n)_p = (n / α)_p`. -/
theorem eisenstein_reciprocity_natCast (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {n : ℕ} (hn : ¬ p ∣ n) :
    powerResidueSymbolIdeal (span {(n : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (n : 𝓞 K)) := by
  induction n using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd (dvd_zero p) hn
  | h₂ n hnu =>
    rw [Nat.isUnit_iff.mp hnu, Nat.cast_one, span_singleton_one, powerResidueSymbolIdeal_top,
      map_one, MulChar.map_one]
  | h₃ b q hb₀ hq ih =>
    have hq' : q.Prime := Nat.prime_iff.mpr hq
    have hqp : q ≠ p := by
      rintro rfl
      exact hn (dvd_mul_right _ _)
    have hpb : ¬ p ∣ b := fun h ↦ hn (dvd_mul_of_dvd_right h _)
    have hq₀ : span {(q : 𝓞 K)} ≠ ⊥ :=
      span_singleton_eq_bot.not.mpr (Nat.cast_ne_zero.mpr hq.ne_zero)
    have hb₀' : span {(b : 𝓞 K)} ≠ ⊥ :=
      span_singleton_eq_bot.not.mpr (Nat.cast_ne_zero.mpr hb₀)
    have hmul : span {((q * b : ℕ) : 𝓞 K)} = span {(q : 𝓞 K)} * span {(b : 𝓞 K)} := by
      rw [Nat.cast_mul, span_singleton_mul_span_singleton]
    rw [hmul, powerResidueSymbolIdeal_mul_right hq₀ hb₀',
      hζ.eisenstein_reciprocity_natCast_of_prime hp2 hα hq' hqp, ih hpb, Nat.cast_mul, map_mul,
      map_mul]

/-- **The Eisenstein reciprocity law.** Let `p` be an odd prime, `K = ℚ(ζ_p)`, `α ∈ 𝓞 K` a primary
cyclotomic integer, and `a : ℤ` a rational integer not divisible by `p`. Then
`(α / a)_p = (a / α)_p`, the `p`-th power residue symbols at the principal ideals `a 𝓞 K` and
`α 𝓞 K`. The integer `a` may be negative, `±1`, or composite, and `α` may be a unit; if `a` and `α`
are not coprime in `𝓞 K`, both sides vanish. -/
theorem eisenstein_reciprocity (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (a : 𝓞 K)) := by
  have hp : p.Prime := Fact.out
  set n := a.natAbs
  have hn : ¬ p ∣ n := fun h ↦ ha (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h))
  rcases Int.natAbs_eq a with h | h
  · have ha_eq : (a : 𝓞 K) = (n : 𝓞 K) := by rw [h, Int.cast_natCast]
    rw [ha_eq]
    exact hζ.eisenstein_reciprocity_natCast hp2 hα hn
  · have ha_eq : (a : 𝓞 K) = -(n : 𝓞 K) := by rw [h, Int.cast_neg, Int.cast_natCast]
    have hspan : span {(a : 𝓞 K)} = span {(n : 𝓞 K)} := by rw [ha_eq, span_singleton_neg]
    rw [hspan, ha_eq, map_neg, powerResidueSymbolIdeal_neg (hp.odd_of_ne_two hp2)]
    exact hζ.eisenstein_reciprocity_natCast hp2 hα hn

/-- **The power residue symbol of `ζ_p` at a rational integer.** For a prime `p`, a primitive
`p`-th root of unity `ζ` in `K = ℚ(ζ_p)`, and `a : ℤ` not divisible by `p`,
`(ζ / a)_p = ζ ^ ((|a| ^ (p - 1) - 1) / p)`. -/
theorem powerResidueSymbolIdeal_span_intCast_mk_toInteger {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p (Ideal.Quotient.mk _ hζ.toInteger) =
      hζ.toInteger ^ ((a.natAbs ^ (p - 1) - 1) / p) := by
  have hp : p.Prime := Fact.out
  set n := a.natAbs
  have hn : ¬ p ∣ n := fun h ↦ ha (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h))
  have hspan : span {(a : 𝓞 K)} = span {(n : 𝓞 K)} := by
    rcases Int.natAbs_eq a with h | h
    · rw [h, Int.cast_natCast]
    · rw [h, Int.cast_neg, Int.cast_natCast, span_singleton_neg]
  have hnorm : absNorm (span {(n : 𝓞 K)}) = n ^ (p - 1) := by
    rw [absNorm_span_natCast, RingOfIntegers.rank,
      IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat hp.pos),
      Nat.totient_prime hp]
  have hcop : (absNorm (span {(n : 𝓞 K)})).Coprime p :=
    hnorm ▸ (hp.coprime_iff_not_dvd.mpr hn).symm.pow_left _
  rw [hspan, powerResidueSymbolIdeal_mk_of_pow_eq_one hcop hζ.toInteger_isPrimitiveRoot.pow_eq_one,
    hnorm]

/-- **Fermat-quotient criterion for `(ζ_p / a)_p = 1`.** For a prime `p`, a primitive `p`-th root
of unity `ζ` in `K = ℚ(ζ_p)`, and `a : ℤ` not divisible by `p`, `(ζ / a)_p = 1` if and only if
`|a| ^ (p - 1) ≡ 1 (mod p ^ 2)`. -/
theorem powerResidueSymbolIdeal_span_intCast_mk_toInteger_eq_one_iff {a : ℤ}
    (ha : ¬ (p : ℤ) ∣ a) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p (Ideal.Quotient.mk _ hζ.toInteger) = 1 ↔
      a.natAbs ^ (p - 1) ≡ 1 [MOD p ^ 2] := by
  have hp : p.Prime := Fact.out
  set n := a.natAbs
  have hn : ¬ p ∣ n := fun h ↦ ha (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h))
  have h1 : 1 ≤ n ^ (p - 1) :=
    Nat.one_le_pow _ _ (Nat.pos_of_ne_zero fun h ↦ hn (h ▸ dvd_zero p))
  have hp_dvd : p ∣ n ^ (p - 1) - 1 :=
    Nat.dvd_of_mod_eq_zero
      (Nat.pow_card_sub_one_sub_one_mod_card hp (hp.coprime_iff_not_dvd.mpr hn).symm)
  rw [hζ.powerResidueSymbolIdeal_span_intCast_mk_toInteger ha,
    hζ.toInteger_isPrimitiveRoot.pow_eq_one_iff_dvd, ← mul_dvd_mul_iff_left hp.ne_zero, ← sq,
    Nat.mul_div_cancel' hp_dvd, ← Nat.modEq_iff_dvd' h1]
  exact Nat.ModEq.comm

/-- **Eisenstein reciprocity for a root-of-unity multiple of a primary element.** For an odd prime
`p`, a primary `α ∈ 𝓞 K`, `c : ℕ`, and `a : ℤ` not divisible by `p`,
`(ζ ^ c * α / a)_p = ζ ^ (c * ((|a| ^ (p - 1) - 1) / p)) * (a / ζ ^ c * α)_p`. -/
theorem eisenstein_reciprocity_toInteger_pow_mul (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) (c : ℕ) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p (Ideal.Quotient.mk _ (hζ.toInteger ^ c * α)) =
      hζ.toInteger ^ (c * ((a.natAbs ^ (p - 1) - 1) / p)) *
        powerResidueSymbolIdeal (span {hζ.toInteger ^ c * α}) p
          (Ideal.Quotient.mk _ (a : 𝓞 K)) := by
  have hp : p.Prime := Fact.out
  have hunit : IsUnit (hζ.toInteger ^ c) := (hζ.toInteger_isPrimitiveRoot.isUnit hp.ne_zero).pow c
  have hspan : span {hζ.toInteger ^ c * α} = span {α} :=
    span_singleton_mul_left_unit hunit α
  rw [map_mul, map_pow, map_mul, map_pow,
    hζ.powerResidueSymbolIdeal_span_intCast_mk_toInteger ha, ← pow_mul, mul_comm _ c,
    hζ.eisenstein_reciprocity hp2 hα ha, hspan]

/-- **Obstruction to Eisenstein reciprocity for `ζ_p * α`.** For an odd prime `p`, a primary
`α ∈ 𝓞 K`, and `a : ℤ` not divisible by `p` and coprime to `α` in `𝓞 K`, the unshifted equality
`(ζ * α / a)_p = (a / ζ * α)_p` holds if and only if `|a| ^ (p - 1) ≡ 1 (mod p ^ 2)`. -/
theorem eisenstein_reciprocity_toInteger_mul_iff (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a)
    (hc : IsCoprime (span {α}) (span {(a : 𝓞 K)})) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p (Ideal.Quotient.mk _ (hζ.toInteger * α)) =
        powerResidueSymbolIdeal (span {hζ.toInteger * α}) p (Ideal.Quotient.mk _ (a : 𝓞 K)) ↔
      a.natAbs ^ (p - 1) ≡ 1 [MOD p ^ 2] := by
  have hp : p.Prime := Fact.out
  have hspan : span {hζ.toInteger * α} = span {α} :=
    span_singleton_mul_left_unit (hζ.toInteger_isPrimitiveRoot.isUnit hp.ne_zero) α
  have hs0 : powerResidueSymbolIdeal (span {hζ.toInteger * α}) p
      (Ideal.Quotient.mk _ (a : 𝓞 K)) ≠ 0 :=
    fun h ↦ powerResidueSymbolIdeal_mk_eq_zero_iff.mp h (hspan ▸ hc.symm)
  have hshift := hζ.eisenstein_reciprocity_toInteger_pow_mul hp2 hα 1 ha
  rw [pow_one, one_mul] at hshift
  rw [hshift, mul_eq_right₀ hs0,
    ← hζ.powerResidueSymbolIdeal_span_intCast_mk_toInteger ha,
    hζ.powerResidueSymbolIdeal_span_intCast_mk_toInteger_eq_one_iff ha]

end IsPrimitiveRoot

section Examples

variable {K : Type*} [Field K] {ζ : K}

/-- In `ℤ[ω]` (`ω` a primitive cube root of unity), `π = -1 - 3ω` of norm `7` is primary in the
sense of `TauCeti.IsEisensteinPrimary`. -/
private theorem isEisensteinPrimary_neg_one_sub_three_mul (hζ : IsPrimitiveRoot ζ 3) :
    TauCeti.IsEisensteinPrimary hζ.toInteger (-1 - 3 * hζ.toInteger) := by
  set ω := hζ.toInteger
  have hsum : 1 + ω + ω ^ 2 = 0 := by
    simpa [Finset.sum_range_succ, sq, add_assoc] using
      hζ.toInteger_isPrimitiveRoot.geom_sum_eq_zero (by lia : 1 < 3)
  rw [TauCeti.isEisensteinPrimary_iff]
  refine ⟨⟨-1, ω - 1, by linear_combination hsum⟩, -1, 1, ?_⟩
  push_cast
  linear_combination -hsum

variable [NumberField K] [IsCyclotomicExtension {3} ℚ K]

/- Eisenstein reciprocity at the norm of `(2)` in `ℤ[ω]`: for `π = -1 - 3ω`,
`(π / 4)_3 = (4 / π)_3`. -/
example (hζ : IsPrimitiveRoot ζ 3) :
    powerResidueSymbolIdeal (span {(absNorm (span {(2 : 𝓞 K)}) : 𝓞 K)}) 3
        (Ideal.Quotient.mk _ (-1 - 3 * hζ.toInteger)) =
      powerResidueSymbolIdeal (span {-1 - 3 * hζ.toInteger}) 3
        (Ideal.Quotient.mk _ (absNorm (span {(2 : 𝓞 K)}) : 𝓞 K)) := by
  refine hζ.eisenstein_reciprocity_absNorm (by lia) (isEisensteinPrimary_neg_one_sub_three_mul hζ)
    ?_
  rw [← Nat.cast_two, absNorm_span_natCast]
  exact (Nat.prime_two.coprime_iff_not_dvd.mpr (by lia)).pow_left _

/- Eisenstein reciprocity for `p = 3`, `π = -1 - 3ω`, and `a = 2`: `(π / 2)_3 = (2 / π)_3`. -/
example (hζ : IsPrimitiveRoot ζ 3) :
    powerResidueSymbolIdeal (span {((2 : ℤ) : 𝓞 K)}) 3
        (Ideal.Quotient.mk _ (-1 - 3 * hζ.toInteger)) =
      powerResidueSymbolIdeal (span {-1 - 3 * hζ.toInteger}) 3
        (Ideal.Quotient.mk _ ((2 : ℤ) : 𝓞 K)) :=
  hζ.eisenstein_reciprocity (by lia) (isEisensteinPrimary_neg_one_sub_three_mul hζ) (by lia)

/- Eisenstein reciprocity against the negative composite integer `a = -10` and at `a = -1`. -/
example (hζ : IsPrimitiveRoot ζ 3) :
    powerResidueSymbolIdeal (span {((-10 : ℤ) : 𝓞 K)}) 3
          (Ideal.Quotient.mk _ (-1 - 3 * hζ.toInteger)) =
        powerResidueSymbolIdeal (span {-1 - 3 * hζ.toInteger}) 3
          (Ideal.Quotient.mk _ ((-10 : ℤ) : 𝓞 K)) ∧
      powerResidueSymbolIdeal (span {((-1 : ℤ) : 𝓞 K)}) 3
          (Ideal.Quotient.mk _ (-1 - 3 * hζ.toInteger)) = 1 := by
  refine ⟨hζ.eisenstein_reciprocity (by lia) (isEisensteinPrimary_neg_one_sub_three_mul hζ)
    (by lia), ?_⟩
  rw [hζ.eisenstein_reciprocity (by lia) (isEisensteinPrimary_neg_one_sub_three_mul hζ) (by lia),
    Int.cast_neg, Int.cast_one, map_neg, map_one,
    powerResidueSymbolIdeal_neg (Nat.prime_three.odd_of_ne_two (by lia)), MulChar.map_one]

/- Negative control: the primary hypothesis cannot be dropped, even for a nonunit prime coprime to
`a`. For `x = ω * (-1 - 3ω)` of norm `7` and `a = 2 ≠ ±1`, `x` is a nonunit coprime to `3` and to
`2`, yet `(x / 2)_3 ≠ (2 / x)_3` since `2 ^ 2 = 4 ≢ 1 (mod 9)`. -/
example (hζ : IsPrimitiveRoot ζ 3) :
    let x : 𝓞 K := hζ.toInteger * (-1 - 3 * hζ.toInteger)
    ¬ IsUnit x ∧ IsCoprime (span {x}) (span {((2 : ℤ) : 𝓞 K)}) ∧
      powerResidueSymbolIdeal (span {((2 : ℤ) : 𝓞 K)}) 3 (Ideal.Quotient.mk _ x) ≠
        powerResidueSymbolIdeal (span {x}) 3 (Ideal.Quotient.mk _ ((2 : ℤ) : 𝓞 K)) := by
  intro x
  set ω := hζ.toInteger
  have hprim : IsPrimitiveRoot ω 3 := hζ.toInteger_isPrimitiveRoot
  have hsum : 1 + ω + ω ^ 2 = 0 := by
    simpa [Finset.sum_range_succ, sq, add_assoc] using hprim.geom_sum_eq_zero (by lia : 1 < 3)
  have hα := isEisensteinPrimary_neg_one_sub_three_mul hζ
  have hunit : IsUnit ω := hprim.isUnit (by lia)
  have hspan : span {x} = span {-1 - 3 * ω} :=
    span_singleton_mul_left_unit hunit (-1 - 3 * ω)
  have hω3 : ω ^ 3 = 1 := hprim.pow_eq_one
  have h7 : (-1 - 3 * ω) * (-1 - 3 * ω ^ 2) = (7 : 𝓞 K) := by
    linear_combination 3 * hsum + 9 * hω3
  -- Complex conjugation sends `-1 - 3ω` to `-1 - 3ω²`, so if `x` were a unit then `7` would be.
  have hx_nu : ¬ IsUnit x := by
    intro hux
    have huα : IsUnit (-1 - 3 * ω) := (IsUnit.mul_iff.mp hux).2
    let σ : Gal(K/ℚ) := (IsCyclotomicExtension.Rat.galEquivZMod 3 K).symm (-1)
    have hσω : σ • ω = ω ^ 2 := by
      have h := IsCyclotomicExtension.Rat.galEquivZMod_smul_of_pow_eq 3 K σ hω3
      rwa [MulEquiv.apply_symm_apply] at h
    have huα' : IsUnit (-1 - 3 * ω ^ 2) := by
      let f := MulSemiringAction.toRingHom Gal(K/ℚ) (𝓞 K) σ
      have h := huα.map f
      have hmap : f (-1 - 3 * ω) = -1 - 3 * ω ^ 2 := by
        rw [map_sub, map_neg, map_one, map_mul, map_ofNat, MulSemiringAction.toRingHom_apply, hσω]
      rwa [hmap] at h
    have hu7 : IsUnit ((7 : ℕ) : 𝓞 K) := by
      simpa [← h7] using huα.mul huα'
    have hn : absNorm (span {((7 : ℕ) : 𝓞 K)}) = 1 := by
      rw [span_singleton_eq_top.mpr hu7, absNorm_top]
    rw [absNorm_span_natCast, RingOfIntegers.rank,
      IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat (by lia : 0 < 3)),
      Nat.totient_prime Nat.prime_three] at hn
    lia
  have hcop' : IsCoprime (span {-1 - 3 * ω}) (span {((2 : ℤ) : 𝓞 K)}) := by
    rw [isCoprime_span_singleton_iff]
    exact ⟨1 + 3 * ω ^ 2, 4, by push_cast; linear_combination -3 * hsum - 9 * hω3⟩
  have hcop : IsCoprime (span {x}) (span {((2 : ℤ) : 𝓞 K)}) := hspan ▸ hcop'
  refine ⟨hx_nu, hcop, ?_⟩
  rw [Ne, hζ.eisenstein_reciprocity_toInteger_mul_iff (by lia) hα (by lia) hcop', Nat.ModEq]
  lia

end Examples
