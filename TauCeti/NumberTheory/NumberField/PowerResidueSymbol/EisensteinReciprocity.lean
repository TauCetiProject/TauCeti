/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.StickelbergerPhi.Primary
import Mathlib.RingTheory.Ideal.Int
import TauCeti.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.RingTheory.Ideal.Quotient.Coprime

/-!
# The Eisenstein reciprocity law

Let `p` be an odd prime, `K = ℚ(ζ_p)` the `p`-th cyclotomic field, and `ζ` a primitive `p`-th root
of unity, so that `𝓞 K = ℤ[ζ]`. Recall that `α ∈ 𝓞 K` is *primary* (`TauCeti.IsEisensteinPrimary`)
if it is coprime to `ζ - 1` and congruent to a rational integer modulo `(ζ - 1) ^ 2`. Write
`(x / 𝔞)_p` for the `p`-th power residue symbol `Ideal.powerResidueSymbolIdeal 𝔞 p` at an ideal `𝔞`
of `𝓞 K`.

**The Eisenstein reciprocity law** states that for every primary `α ∈ 𝓞 K` and every rational
integer `a` not divisible by `p`,

  `(α / a)_p = (a / α)_p`,

the two `p`-th power residue symbols being taken at the principal ideals `a 𝓞 K` and `α 𝓞 K`
(`IsPrimitiveRoot.eisenstein_reciprocity`). The integer `a` may be negative, composite, `±1`, or
non-coprime to `α` (in which case both symbols vanish); similarly `α` may be a primary unit.

Before passing to rational integers, the law holds at the absolute norm of any ideal `B` of `𝓞 K`
whose norm is prime to `p` (`IsPrimitiveRoot.eisenstein_reciprocity_absNorm`):

  `(α / N B)_p = (N B / α)_p`.

At a maximal ideal `P` coprime to `α`, the Gauss sum power `Φ((α))` satisfies both
`Φ((α)) = ±α ^ γ` (`IsPrimitiveRoot.stickelbergerPhi_eq_or_eq_neg_stickelbergerProduct`) and
`(Φ((α)) / P)_p = (N P / α)_p` (`Ideal.powerResidueSymbol_stickelbergerPhi`), while Galois
equivariance of the symbol and the conjugate-product identity for `N P` give
`(α ^ γ / P)_p = (α / N P)_p` (`Ideal.powerResidueSymbol_stickelbergerProduct`). At a rational
prime `q ≠ p`, choosing a prime `P` of `𝓞 K` above `q` of residue degree `f ∣ p - 1` yields
`(α / q)_p ^ f = (q / α)_p ^ f`, and since `p ∤ f` both `p`-th roots of unity agree. Multiplicative
extension and oddness of `p` then give all rational integers `a` prime to `p`.

Replacing a primary `α` by the non-primary associate `ζ ^ c * α` multiplies `(α / a)_p` by
`ζ ^ (c (|a| ^ (p - 1) - 1) / p)` while leaving `(a / α)_p` unchanged
(`IsPrimitiveRoot.powerResidueSymbolIdeal_span_intCast_mk_toInteger_pow_mul`). In particular, when
`α` and `a` are coprime, `ζ * α` satisfies reciprocity against `a` if and only if the Fermat
quotient vanishes modulo `p`, that is `|a| ^ (p - 1) ≡ 1 (mod p ^ 2)`
(`IsPrimitiveRoot.powerResidueSymbolIdeal_span_intCast_mk_toInteger_mul_eq_iff`).

## Main results

* `IsPrimitiveRoot.eisenstein_reciprocity_absNorm`: `(α / N B)_p = (N B / α)_p` for primary `α` and
  an ideal `B` of `𝓞 K` whose norm is prime to `p`.
* `IsPrimitiveRoot.eisenstein_reciprocity_natCast`: `(α / n)_p = (n / α)_p` for primary `α` and a
  natural number `n` not divisible by `p`.
* `IsPrimitiveRoot.eisenstein_reciprocity`: **the Eisenstein reciprocity law**
  `(α / a)_p = (a / α)_p` for primary `α` and an integer `a` not divisible by `p`.
* `IsPrimitiveRoot.powerResidueSymbolIdeal_span_natCast_mk_toInteger` and
  `IsPrimitiveRoot.powerResidueSymbolIdeal_span_intCast_mk_toInteger`:
  `(ζ / a)_p = ζ ^ ((|a| ^ (p - 1) - 1) / p)` for `p ∤ a`.
* `IsPrimitiveRoot.powerResidueSymbolIdeal_span_intCast_mk_toInteger_pow_mul`:
  `((ζ ^ c * α) / a)_p = ζ ^ (c (|a| ^ (p - 1) - 1) / p) · (a / (ζ ^ c * α))_p`.
* `IsPrimitiveRoot.powerResidueSymbolIdeal_span_intCast_mk_toInteger_mul_eq_iff`: for `α` coprime
  to `a`, `((ζ * α) / a)_p = (a / (ζ * α))_p ↔ |a| ^ (p - 1) ≡ 1 (mod p ^ 2)`.

## References

* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §4, Theorem 4.1 and (25).
* N. Xu, *Reciprocity Laws*, §6, Theorem 6.9 and Corollary 6.13.
* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 14, §2,
  Theorem 1.
-/

public section

open NumberField Ideal UniqueFactorizationMonoid

namespace IsPrimitiveRoot

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

/-- The `ℤ`-rank of `𝓞 K` for the `p`-th cyclotomic field `K = ℚ(ζ_p)` is `p - 1`. -/
private theorem finrank_ringOfIntegers_eq_sub_one : Module.finrank ℤ (𝓞 K) = p - 1 := by
  have hp : p.Prime := Fact.out
  rw [RingOfIntegers.rank, IsCyclotomicExtension.Rat.finrank p K, Nat.totient_prime hp]

omit [IsCyclotomicExtension {p} ℚ K] in
/-- Two `p`-th roots of unity (or elements equal to `0`) whose `f`-th powers agree for `f` not
divisible by `p` are equal. -/
private theorem eq_of_pow_eq_of_not_dvd {R : Type*} [Monoid R] {x y : R} (hx : x ^ p = 1)
    (hy : y ^ p = 1) {f : ℕ} (hpf : ¬ p ∣ f) (hxy : x ^ f = y ^ f) : x = y := by
  have hp : p.Prime := Fact.out
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  have hf0 : (f : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff f p).not.mpr hpf
  set k := ((f : ZMod p)⁻¹).val
  have hmod : f * k % p = 1 := by
    have hinv : ((f * k : ℕ) : ZMod p) = 1 := by
      rw [Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id', id, mul_inv_cancel₀ hf0]
    rw [← ZMod.val_natCast, hinv, ZMod.val_one]
  have hpow {z : R} (hz : z ^ p = 1) : z ^ (f * k) = z := by
    rw [← Nat.div_add_mod (f * k) p, pow_add, pow_mul, hz, one_pow, one_mul, hmod, pow_one]
  rw [← hpow hx, ← hpow hy, pow_mul, pow_mul, hxy]

/-- **The `p`-th power residue symbol of `ζ` at a natural number.** For `p ∤ n`, the symbol of `ζ`
at `n 𝓞 K` is `ζ ^ ((n ^ (p - 1) - 1) / p)`. -/
theorem powerResidueSymbolIdeal_span_natCast_mk_toInteger {n : ℕ} (hn : ¬ p ∣ n) :
    powerResidueSymbolIdeal (span {(n : 𝓞 K)}) p (Ideal.Quotient.mk _ hζ.toInteger) =
      hζ.toInteger ^ ((n ^ (p - 1) - 1) / p) := by
  have hp : p.Prime := Fact.out
  have hN : absNorm (span {(n : 𝓞 K)}) = n ^ (p - 1) := by
    rw [absNorm_span_natCast, finrank_ringOfIntegers_eq_sub_one (p := p)]
  have hcop : (absNorm (span {(n : 𝓞 K)})).Coprime p := by
    rw [hN]
    exact ((hp.coprime_iff_not_dvd.mpr hn).symm).pow_left _
  rw [powerResidueSymbolIdeal_mk_of_pow_eq_one hcop hζ.toInteger_isPrimitiveRoot.pow_eq_one, hN]

/-- **The `p`-th power residue symbol of `ζ` at a rational integer.** For `p ∤ a`, the symbol of
`ζ` at `a 𝓞 K` is `ζ ^ ((|a| ^ (p - 1) - 1) / p)`. -/
theorem powerResidueSymbolIdeal_span_intCast_mk_toInteger {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p (Ideal.Quotient.mk _ hζ.toInteger) =
      hζ.toInteger ^ ((a.natAbs ^ (p - 1) - 1) / p) := by
  have hna : ¬ p ∣ a.natAbs := by rwa [← Int.natCast_dvd]
  have hspan : span {(a : 𝓞 K)} = span {(a.natAbs : 𝓞 K)} := by
    rcases Int.natAbs_eq a with h | h
    · conv_lhs => rw [h, Int.cast_natCast]
    · conv_lhs => rw [h, Int.cast_neg, Int.cast_natCast, span_singleton_neg]
  rw [hspan, hζ.powerResidueSymbolIdeal_span_natCast_mk_toInteger hna]

/-- Eisenstein reciprocity at the norm of a maximal ideal `P` whose norm is prime to `p`:
`(α / N P)_p = (N P / α)_p`. -/
private theorem eisenstein_reciprocity_absNorm_of_isMaximal (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {P : Ideal (𝓞 K)} [P.IsMaximal]
    (hP : (absNorm P).Coprime p) :
    powerResidueSymbolIdeal (span {(absNorm P : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (absNorm P : 𝓞 K)) := by
  have hp : p.Prime := Fact.out
  by_cases hcop : IsCoprime (span {α}) (span {(absNorm P : 𝓞 K)})
  · have hNcop : (absNorm (span {α})).Coprime (absNorm P) :=
      absNorm_coprime_of_isCoprime_span_natCast hcop
    rw [← powerResidueSymbol_stickelbergerProduct hp.two_le P α,
      ← powerResidueSymbol_stickelbergerPhi (span {α}) P hP hNcop hp.two_le]
    rcases hζ.stickelbergerPhi_eq_or_eq_neg_stickelbergerProduct hp2 hα with hΦ | hΦ
    · rw [hΦ]
    · rw [hΦ, map_neg, ← powerResidueSymbolIdeal_of_isMaximal P,
        powerResidueSymbolIdeal_neg (hp.odd_of_ne_two hp2), powerResidueSymbolIdeal_of_isMaximal P]
  · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hcop,
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr (mt IsCoprime.symm hcop)]

/-- **Eisenstein reciprocity at the norm of an ideal.** Let `p` be an odd prime, `K = ℚ(ζ_p)`,
`α ∈ 𝓞 K` primary, and `B` an ideal of `𝓞 K` whose norm is prime to `p`. Then
`(α / N B)_p = (N B / α)_p`, the symbols being taken at the principal ideals `(N B) 𝓞 K` and
`α 𝓞 K`. -/
theorem eisenstein_reciprocity_absNorm (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {B : Ideal (𝓞 K)}
    (hB : (absNorm B).Coprime p) :
    powerResidueSymbolIdeal (span {(absNorm B : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (absNorm B : 𝓞 K)) := by
  have hp : p.Prime := Fact.out
  induction B using induction_on_prime with
  | h₁ =>
    rw [zero_eq_bot, absNorm_bot, Nat.coprime_zero_left] at hB
    exact absurd hB hp.ne_one
  | h₂ B hBu =>
    rw [isUnit_iff.mp hBu, absNorm_top, Nat.cast_one, span_singleton_one,
      powerResidueSymbolIdeal_top, map_one, MulChar.map_one]
  | h₃ B P hB₀ hP ih =>
    have : P.IsMaximal := (isPrime_of_prime hP).isMaximal hP.ne_zero
    rw [map_mul, Nat.coprime_mul_iff_left] at hB
    have hNP : span {(absNorm P : 𝓞 K)} ≠ ⊥ := by
      simpa [absNorm_eq_zero_iff] using hP.ne_zero
    have hNB : span {(absNorm B : 𝓞 K)} ≠ ⊥ := by
      simpa [absNorm_eq_zero_iff] using hB₀
    have hspan : span {(absNorm (P * B) : 𝓞 K)} =
        span {(absNorm P : 𝓞 K)} * span {(absNorm B : 𝓞 K)} := by
      rw [map_mul, Nat.cast_mul, span_singleton_mul_span_singleton]
    rw [hspan, powerResidueSymbolIdeal_mul_right hNP hNB, map_mul, Nat.cast_mul, map_mul, map_mul,
      hζ.eisenstein_reciprocity_absNorm_of_isMaximal hp2 hα hB.1, ih hB.2]

/-- Eisenstein reciprocity between a primary `α ∈ 𝓞 K` and a rational prime `q ≠ p`:
`(α / q)_p = (q / α)_p`. -/
private theorem eisenstein_reciprocity_natPrime (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {q : ℕ} (hq : q.Prime) (hqp : ¬ p ∣ q) :
    powerResidueSymbolIdeal (span {(q : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (q : 𝓞 K)) := by
  have hp : p.Prime := Fact.out
  by_cases hcop : IsCoprime (span {α}) (span {(q : 𝓞 K)})
  swap
  · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hcop,
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr (mt IsCoprime.symm hcop)]
  have : Fact q.Prime := ⟨hq⟩
  have : (span {(q : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime q
  obtain ⟨P, hPmax, hPover⟩ :=
    exists_maximal_ideal_liesOver_of_isIntegral (span {(q : ℤ)}) (S := 𝓞 K)
  set f := P.inertiaDeg ℤ
  have hqf : q ^ f = absNorm P := pow_inertiaDeg q P
  have hqcop : q.Coprime p := (hp.coprime_iff_not_dvd.mpr hqp).symm
  have hPcop : (absNorm P).Coprime p := hqf ▸ hqcop.pow_left f
  -- `f = orderOf (q : ZMod p)` divides `p - 1`, so `0 < f < p` and `p ∤ f`.
  have hqp' : ¬ q ∣ p := hq.coprime_iff_not_dvd.mp hqcop
  have hford : f = orderOf (q : ZMod p) :=
    IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd q K P hqp'
  have hdvd : f ∣ p - 1 := by
    rw [hford, ← ZMod.coe_unitOfCoprime q hqcop, orderOf_units, ← Nat.totient_prime hp,
      ← ZMod.card_units_eq_totient]
    exact orderOf_dvd_card
  have hf_lt : f < p :=
    (Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) hdvd).trans_lt (Nat.sub_lt hp.pos one_pos)
  have hpf : ¬ p ∣ f := Nat.not_dvd_of_pos_of_lt (inertiaDeg_pos P ℤ) hf_lt
  -- At `N P = q ^ f`, reciprocity gives `(α / q)_p ^ f = (q / α)_p ^ f`.
  have hrec := hζ.eisenstein_reciprocity_absNorm hp2 hα hPcop
  rw [← hqf, Nat.cast_pow, ← span_singleton_pow, powerResidueSymbolIdeal_pow_right, map_pow,
    map_pow] at hrec
  have hu₁ : IsUnit (Ideal.Quotient.mk (span {(q : 𝓞 K)}) α) :=
    Ideal.Quotient.isUnit_mk_iff.mpr (isCoprime_iff_sup_eq.mp hcop)
  have hu₂ : IsUnit (Ideal.Quotient.mk (span {α}) (q : 𝓞 K)) :=
    Ideal.Quotient.isUnit_mk_iff.mpr (isCoprime_iff_sup_eq.mp hcop.symm)
  exact eq_of_pow_eq_of_not_dvd (powerResidueSymbolIdeal_pow_eq_one hu₁)
    (powerResidueSymbolIdeal_pow_eq_one hu₂) hpf hrec

/-- **Eisenstein reciprocity for natural numbers.** Let `p` be an odd prime, `K = ℚ(ζ_p)`,
`α ∈ 𝓞 K` primary, and `n` a natural number not divisible by `p`. Then `(α / n)_p = (n / α)_p`,
the symbols being taken at the principal ideals `n 𝓞 K` and `α 𝓞 K`. -/
theorem eisenstein_reciprocity_natCast (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {n : ℕ} (hn : ¬ p ∣ n) :
    powerResidueSymbolIdeal (span {(n : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (n : 𝓞 K)) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    obtain rfl | hn0 := eq_or_ne n 0
    · exact absurd (dvd_zero p) hn
    obtain rfl | hn1 := eq_or_ne n 1
    · rw [Nat.cast_one, span_singleton_one, powerResidueSymbolIdeal_top, map_one, MulChar.map_one]
    obtain ⟨q, hq, m, rfl⟩ := Nat.exists_prime_and_dvd hn1
    have hm0 : m ≠ 0 := right_ne_zero_of_mul hn0
    have hmn : m < q * m := lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm0) hq.one_lt
    have hqp : ¬ p ∣ q := fun h ↦ hn (h.mul_right m)
    have hmp : ¬ p ∣ m := fun h ↦ hn (h.mul_left q)
    have hq_ne : span {(q : 𝓞 K)} ≠ ⊥ := by simpa using hq.ne_zero
    have hm_ne : span {(m : 𝓞 K)} ≠ ⊥ := by simpa using hm0
    have hspan : span {((q * m : ℕ) : 𝓞 K)} = span {(q : 𝓞 K)} * span {(m : 𝓞 K)} := by
      rw [Nat.cast_mul, span_singleton_mul_span_singleton]
    rw [hspan, powerResidueSymbolIdeal_mul_right hq_ne hm_ne, Nat.cast_mul, map_mul, map_mul,
      hζ.eisenstein_reciprocity_natPrime hp2 hα hq hqp, ih m hmn hmp]

/-- **The Eisenstein reciprocity law.** Let `p` be an odd prime, `K = ℚ(ζ_p)`, `α ∈ 𝓞 K` primary,
and `a` a rational integer not divisible by `p`. Then `(α / a)_p = (a / α)_p`, the `p`-th power
residue symbols being taken at the principal ideals `a 𝓞 K` and `α 𝓞 K`. The integer `a` may be
negative, composite, `±1`, or not coprime to `α` (in which case both sides vanish). -/
theorem eisenstein_reciprocity (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (a : 𝓞 K)) := by
  have hp : p.Prime := Fact.out
  have hna : ¬ p ∣ a.natAbs := by rwa [← Int.natCast_dvd]
  rcases Int.natAbs_eq a with h | h
  · rw [h, Int.cast_natCast]
    exact hζ.eisenstein_reciprocity_natCast hp2 hα hna
  · rw [h, Int.cast_neg, Int.cast_natCast, span_singleton_neg, map_neg,
      powerResidueSymbolIdeal_neg (hp.odd_of_ne_two hp2)]
    exact hζ.eisenstein_reciprocity_natCast hp2 hα hna

/-- **Eisenstein reciprocity for a `ζ`-power associate of a primary element.** Replacing a primary
`α` by `ζ ^ c * α` multiplies `(α / a)_p` by `ζ ^ (c (|a| ^ (p - 1) - 1) / p)` while leaving the
ideal `α 𝓞 K` and hence `(a / α)_p` unchanged. -/
theorem powerResidueSymbolIdeal_span_intCast_mk_toInteger_pow_mul (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) (c : ℕ) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p (Ideal.Quotient.mk _ (hζ.toInteger ^ c * α)) =
      hζ.toInteger ^ (c * ((a.natAbs ^ (p - 1) - 1) / p)) *
        powerResidueSymbolIdeal (span {hζ.toInteger ^ c * α}) p
          (Ideal.Quotient.mk _ (a : 𝓞 K)) := by
  have hp : p.Prime := Fact.out
  have hunit : IsUnit (hζ.toInteger ^ c) :=
    (hζ.toInteger_isPrimitiveRoot.isUnit hp.ne_zero).pow c
  rw [span_singleton_mul_left_unit hunit, map_mul, map_mul, map_pow, map_pow,
    hζ.powerResidueSymbolIdeal_span_intCast_mk_toInteger ha, ← pow_mul, mul_comm _ c,
    hζ.eisenstein_reciprocity hp2 hα ha]

/-- **When the non-primary associate `ζ * α` satisfies reciprocity against `a`.** For primary `α`
coprime to a rational integer `a` with `p ∤ a`, the equality `((ζ * α) / a)_p = (a / (ζ * α))_p`
holds if and only if `|a| ^ (p - 1) ≡ 1 (mod p ^ 2)`. -/
theorem powerResidueSymbolIdeal_span_intCast_mk_toInteger_mul_eq_iff (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a)
    (hcop : IsCoprime (span {α}) (span {(a : 𝓞 K)})) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p (Ideal.Quotient.mk _ (hζ.toInteger * α)) =
        powerResidueSymbolIdeal (span {hζ.toInteger * α}) p (Ideal.Quotient.mk _ (a : 𝓞 K)) ↔
      a.natAbs ^ (p - 1) ≡ 1 [MOD p ^ 2] := by
  have hp : p.Prime := Fact.out
  have hshift := hζ.powerResidueSymbolIdeal_span_intCast_mk_toInteger_pow_mul hp2 hα ha 1
  rw [pow_one, one_mul] at hshift
  have hunit : IsUnit hζ.toInteger := hζ.toInteger_isPrimitiveRoot.isUnit hp.ne_zero
  have hrhs_ne :
      powerResidueSymbolIdeal (span {hζ.toInteger * α}) p (Ideal.Quotient.mk _ (a : 𝓞 K)) ≠ 0 := by
    rw [span_singleton_mul_left_unit hunit, Ne, powerResidueSymbolIdeal_mk_eq_zero_iff, not_not]
    exact hcop.symm
  have ha0 : a.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr fun h ↦ ha (h ▸ dvd_zero _)
  have hN1 : 1 ≤ a.natAbs ^ (p - 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero ha0)
  have hna_cop : a.natAbs.Coprime p :=
    (hp.coprime_iff_not_dvd.mpr (by rwa [← Int.natCast_dvd])).symm
  have hfermat : p ∣ a.natAbs ^ (p - 1) - 1 := by
    have h := (Nat.ModEq.pow_totient hna_cop).symm
    rw [Nat.totient_prime hp] at h
    exact (Nat.modEq_iff_dvd' hN1).mp h
  obtain ⟨q, hq⟩ := hfermat
  rw [hshift, mul_left_eq_self₀, or_iff_left hrhs_ne,
    hζ.toInteger_isPrimitiveRoot.pow_eq_one_iff_dvd, Nat.ModEq.comm, Nat.modEq_iff_dvd' hN1, hq,
    Nat.mul_div_cancel_left q hp.pos, sq, mul_dvd_mul_iff_left hp.ne_zero]

end IsPrimitiveRoot

section Examples

open NumberField Ideal IsCyclotomicExtension.Rat

section Cubic

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
  {ζ : K} (hζ : IsPrimitiveRoot ζ 3)

/-- The element `π = -1 - 3ω` of `ℤ[ω]` (of norm `7`) is Eisenstein-primary. -/
private theorem isEisensteinPrimary_neg_one_sub_three_mul :
    TauCeti.IsEisensteinPrimary hζ.toInteger ((-1 : 𝓞 K) - 3 * hζ.toInteger) := by
  have hx : ¬ hζ.toInteger - 1 ∣ (-1 : 𝓞 K) - 3 * hζ.toInteger := by
    intro h
    have h4 : hζ.toInteger - 1 ∣ ((-4 : ℤ) : 𝓞 K) := by
      have hsub : ((-4 : ℤ) : 𝓞 K) = ((-1 : 𝓞 K) - 3 * hζ.toInteger) + 3 * (hζ.toInteger - 1) := by
        push_cast; ring
      rw [hsub]
      exact dvd_add h (dvd_mul_left _ _)
    exact absurd ((zeta_sub_one_dvd_intCast_iff' 3 hζ).mp h4) (by decide)
  have hab : (hζ.toInteger - 1) ^ 2 ∣
      ((-1 : 𝓞 K) - 3 * hζ.toInteger) - ((-4 : ℤ) + (-3 : ℤ) * (hζ.toInteger - 1)) := by
    refine ⟨0, ?_⟩
    push_cast; ring
  simpa using (hζ.isEisensteinPrimary_toInteger_pow_mul_iff (by decide) hx hab 0).mpr (by decide)

/-- The cubic residue symbol `((-1 - 3ω) / 2)_3` equals `ω ^ 2`. -/
private theorem powerResidueSymbolIdeal_two_neg_one_sub_three_mul :
    powerResidueSymbolIdeal (span {((2 : ℤ) : 𝓞 K)}) 3
        (Ideal.Quotient.mk _ ((-1 : 𝓞 K) - 3 * hζ.toInteger)) =
      hζ.toInteger ^ 2 := by
  let ω := hζ.toInteger
  have hsum : 1 + ω + ω ^ 2 = 0 := by
    simpa [Finset.sum_range_succ, pow_two] using
      hζ.toInteger_isPrimitiveRoot.geom_sum_eq_zero (by decide)
  have hmk : Ideal.Quotient.mk (span {((2 : ℤ) : 𝓞 K)}) ((-1 : 𝓞 K) - 3 * ω) =
      Ideal.Quotient.mk _ (ω ^ 2) := by
    rw [Ideal.Quotient.eq, mem_span_singleton]
    exact ⟨-ω, by linear_combination -hsum⟩
  have hN : absNorm (span {((2 : ℤ) : 𝓞 K)}) = 4 := by
    have h2 : ((2 : ℤ) : 𝓞 K) = ((2 : ℕ) : 𝓞 K) := by norm_num
    rw [h2, absNorm_span_natCast, IsPrimitiveRoot.finrank_ringOfIntegers_eq_sub_one (p := 3)]
    rfl
  have hω2 : (ω ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
  rw [hmk, powerResidueSymbolIdeal_mk_of_pow_eq_one (by rw [hN]; decide) hω2, hN]
  simp [ω]

/-- For `p = 3` and `α = -1 - 3ω` (primary of norm `7`), `a = 2`: both `(α / 2)_3` and `(2 / α)_3`
equal `ω ^ 2`. -/
example :
    powerResidueSymbolIdeal (span {((2 : ℤ) : 𝓞 K)}) 3
        (Ideal.Quotient.mk _ ((-1 : 𝓞 K) - 3 * hζ.toInteger)) = hζ.toInteger ^ 2 ∧
      powerResidueSymbolIdeal (span {(-1 : 𝓞 K) - 3 * hζ.toInteger}) 3
        (Ideal.Quotient.mk _ ((2 : ℤ) : 𝓞 K)) = hζ.toInteger ^ 2 := by
  have h2 := powerResidueSymbolIdeal_two_neg_one_sub_three_mul hζ
  refine ⟨h2, ?_⟩
  rw [← hζ.eisenstein_reciprocity (by decide) (isEisensteinPrimary_neg_one_sub_three_mul hζ)
    (by decide), h2]

/-- Eisenstein reciprocity at the norm `N((2)) = 4` of `B = 2 ℤ[ω]` for `α = -1 - 3ω`:
`(α / 4)_3 = (4 / α)_3 = ω`. -/
example :
    powerResidueSymbolIdeal (span {(absNorm (span {((2 : ℕ) : 𝓞 K)}) : 𝓞 K)}) 3
        (Ideal.Quotient.mk _ ((-1 : 𝓞 K) - 3 * hζ.toInteger)) = hζ.toInteger ∧
      powerResidueSymbolIdeal (span {(-1 : 𝓞 K) - 3 * hζ.toInteger}) 3
        (Ideal.Quotient.mk _ (absNorm (span {((2 : ℕ) : 𝓞 K)}) : 𝓞 K)) = hζ.toInteger := by
  have hN : absNorm (span {((2 : ℕ) : 𝓞 K)}) = 4 := by
    rw [absNorm_span_natCast, IsPrimitiveRoot.finrank_ringOfIntegers_eq_sub_one (p := 3)]
    rfl
  have hrec := hζ.eisenstein_reciprocity_absNorm (by decide)
    (isEisensteinPrimary_neg_one_sub_three_mul hζ) (B := span {((2 : ℕ) : 𝓞 K)})
    (by rw [hN]; decide)
  have hrhs : powerResidueSymbolIdeal (span {(-1 : 𝓞 K) - 3 * hζ.toInteger}) 3
      (Ideal.Quotient.mk _ (absNorm (span {((2 : ℕ) : 𝓞 K)}) : 𝓞 K)) = hζ.toInteger := by
    have h4 : ((4 : ℕ) : 𝓞 K) = ((2 : ℤ) : 𝓞 K) ^ 2 := by norm_num
    have hfour : 2 * 2 = 3 + 1 := rfl
    rw [hN, h4, map_pow, map_pow,
      ← hζ.eisenstein_reciprocity (by decide) (isEisensteinPrimary_neg_one_sub_three_mul hζ)
        (by decide),
      powerResidueSymbolIdeal_two_neg_one_sub_three_mul hζ, ← pow_mul, hfour, pow_add,
      hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_mul, pow_one]
  exact ⟨hrec.trans hrhs, hrhs⟩

/-- Negative control: the primary hypothesis cannot be dropped. For the non-primary associate
`ω * α` of `α = -1 - 3ω` and `a = 2`, `((ω * α) / 2)_3 = 1` whereas `(2 / (ω * α))_3 = ω ^ 2`,
so `((ω * α) / 2)_3 ≠ (2 / (ω * α))_3` (reflecting `2 ^ 2 = 4 ≢ 1 (mod 9)`). -/
example :
    powerResidueSymbolIdeal (span {((2 : ℤ) : 𝓞 K)}) 3
        (Ideal.Quotient.mk _ (hζ.toInteger * ((-1 : 𝓞 K) - 3 * hζ.toInteger))) = 1 ∧
      powerResidueSymbolIdeal (span {hζ.toInteger * ((-1 : 𝓞 K) - 3 * hζ.toInteger)}) 3
        (Ideal.Quotient.mk _ ((2 : ℤ) : 𝓞 K)) = hζ.toInteger ^ 2 ∧
      powerResidueSymbolIdeal (span {((2 : ℤ) : 𝓞 K)}) 3
        (Ideal.Quotient.mk _ (hζ.toInteger * ((-1 : 𝓞 K) - 3 * hζ.toInteger))) ≠
      powerResidueSymbolIdeal (span {hζ.toInteger * ((-1 : 𝓞 K) - 3 * hζ.toInteger)}) 3
        (Ideal.Quotient.mk _ ((2 : ℤ) : 𝓞 K)) := by
  set α := (-1 : 𝓞 K) - 3 * hζ.toInteger
  have hα := isEisensteinPrimary_neg_one_sub_three_mul hζ
  have h2 := powerResidueSymbolIdeal_two_neg_one_sub_three_mul hζ
  have hrhs : powerResidueSymbolIdeal (span {hζ.toInteger * α}) 3
      (Ideal.Quotient.mk _ ((2 : ℤ) : 𝓞 K)) = hζ.toInteger ^ 2 := by
    rw [span_singleton_mul_left_unit (hζ.toInteger_isPrimitiveRoot.isUnit (by decide)),
      ← hζ.eisenstein_reciprocity (by decide) hα (by decide), h2]
  have hlhs : powerResidueSymbolIdeal (span {((2 : ℤ) : 𝓞 K)}) 3
      (Ideal.Quotient.mk _ (hζ.toInteger * α)) = 1 := by
    have h := hζ.powerResidueSymbolIdeal_span_intCast_mk_toInteger_pow_mul (by decide) hα
      (a := 2) (by decide) 1
    rw [pow_one, hrhs] at h
    rw [h]
    norm_num
    rw [← pow_succ', hζ.toInteger_isPrimitiveRoot.pow_eq_one]
  refine ⟨hlhs, hrhs, ?_⟩
  rw [hlhs, hrhs]
  exact (hζ.toInteger_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by decide) (by decide)).symm

/-- Non-coprime edge case: `α = -1 - 3ω` divides `7 = (-1 - 3ω)(2 + 3ω)`, so at `a = 7` both
`(α / 7)_3` and `(7 / α)_3` vanish. -/
example :
    powerResidueSymbolIdeal (span {((7 : ℤ) : 𝓞 K)}) 3
        (Ideal.Quotient.mk _ ((-1 : 𝓞 K) - 3 * hζ.toInteger)) = 0 ∧
      powerResidueSymbolIdeal (span {(-1 : 𝓞 K) - 3 * hζ.toInteger}) 3
        (Ideal.Quotient.mk _ ((7 : ℤ) : 𝓞 K)) = 0 := by
  let ω := hζ.toInteger
  set α := (-1 : 𝓞 K) - 3 * ω
  have hsum : 1 + ω + ω ^ 2 = 0 := by
    simpa [Finset.sum_range_succ, pow_two] using
      hζ.toInteger_isPrimitiveRoot.geom_sum_eq_zero (by decide)
  have hdvd : α ∣ ((7 : ℤ) : 𝓞 K) := ⟨2 + 3 * ω, by push_cast [α]; linear_combination 9 * hsum⟩
  have htop : span {α} ≠ ⊤ := by
    intro htop
    have hrhs : powerResidueSymbolIdeal (span {α}) 3 (Ideal.Quotient.mk _ ((2 : ℤ) : 𝓞 K)) =
        ω ^ 2 := by
      rw [← hζ.eisenstein_reciprocity (by decide) (isEisensteinPrimary_neg_one_sub_three_mul hζ)
        (by decide), powerResidueSymbolIdeal_two_neg_one_sub_three_mul hζ]
    rw [htop, powerResidueSymbolIdeal_top] at hrhs
    exact hζ.toInteger_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by decide) (by decide) hrhs.symm
  have hncop : ¬ IsCoprime (span {α}) (span {((7 : ℤ) : 𝓞 K)}) := by
    rw [isCoprime_iff_sup_eq,
      sup_eq_left.mpr ((span_singleton_le_iff_mem _).mpr (mem_span_singleton.mpr hdvd))]
    exact htop
  exact ⟨powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hncop,
    powerResidueSymbolIdeal_mk_eq_zero_iff.mpr (mt IsCoprime.symm hncop)⟩

/-- At `a = -1`, both symbols in Eisenstein reciprocity equal `1`; against the negative composite
integer `a = -10`, both symbols agree. -/
example {α : 𝓞 K} (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) :
    powerResidueSymbolIdeal (span {((-1 : ℤ) : 𝓞 K)}) 3 (Ideal.Quotient.mk _ α) = 1 ∧
      powerResidueSymbolIdeal (span {α}) 3 (Ideal.Quotient.mk _ ((-1 : ℤ) : 𝓞 K)) = 1 ∧
      powerResidueSymbolIdeal (span {((-10 : ℤ) : 𝓞 K)}) 3 (Ideal.Quotient.mk _ α) =
        powerResidueSymbolIdeal (span {α}) 3 (Ideal.Quotient.mk _ ((-10 : ℤ) : 𝓞 K)) := by
  refine ⟨?_, ?_, hζ.eisenstein_reciprocity (by decide) hα (by decide)⟩
  · rw [Int.cast_neg, Int.cast_one, span_singleton_neg, span_singleton_one,
      powerResidueSymbolIdeal_top]
  · rw [Int.cast_neg, Int.cast_one, map_neg, map_one,
      powerResidueSymbolIdeal_neg (by decide : Odd 3), MulChar.map_one]

end Cubic

section Quintic

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K]
  {ζ : K} (hζ : IsPrimitiveRoot ζ 5)

/-- Quintic reciprocity in `K = ℚ(ζ₅)`: for the primary cyclotomic integer `α = ζ ^ 3 * (2 + ζ)`
(of norm `11`) and `a = 2`, reducing `α ≡ ζ ^ 4 (mod 2)` at the inert prime `2` (of norm `16`)
gives `(2 / α)_5 = (α / 2)_5 = ζ ^ 2 ≠ 1`. -/
example :
    TauCeti.IsEisensteinPrimary hζ.toInteger (hζ.toInteger ^ 3 * (2 + hζ.toInteger)) ∧
      powerResidueSymbolIdeal (span {hζ.toInteger ^ 3 * (2 + hζ.toInteger)}) 5
        (Ideal.Quotient.mk _ ((2 : ℤ) : 𝓞 K)) = hζ.toInteger ^ 2 ∧
      powerResidueSymbolIdeal (span {hζ.toInteger ^ 3 * (2 + hζ.toInteger)}) 5
        (Ideal.Quotient.mk _ ((2 : ℤ) : 𝓞 K)) ≠ 1 := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  let η := hζ.toInteger
  have hx : ¬ η - 1 ∣ 2 + η := by
    intro h
    have h3 : η - 1 ∣ ((3 : ℤ) : 𝓞 K) := by
      have hsub : ((3 : ℤ) : 𝓞 K) = (2 + η) - (η - 1) := by push_cast; ring
      rw [hsub]
      exact dvd_sub h dvd_rfl
    exact absurd ((zeta_sub_one_dvd_intCast_iff' 5 hζ).mp h3) (by decide)
  have hab : (η - 1) ^ 2 ∣ (2 + η) - ((3 : ℤ) + (1 : ℤ) * (η - 1)) :=
    ⟨0, by push_cast; ring⟩
  have hprim : TauCeti.IsEisensteinPrimary η (η ^ 3 * (2 + η)) :=
    (hζ.isEisensteinPrimary_toInteger_pow_mul_iff (by decide) hx hab 3).mpr (by decide)
  have hmk : Ideal.Quotient.mk (span {((2 : ℤ) : 𝓞 K)}) (η ^ 3 * (2 + η)) =
      Ideal.Quotient.mk _ (η ^ 4) := by
    rw [Ideal.Quotient.eq, mem_span_singleton]
    exact ⟨η ^ 3, by push_cast; ring⟩
  have hN : absNorm (span {((2 : ℤ) : 𝓞 K)}) = 16 := by
    have h2 : ((2 : ℤ) : 𝓞 K) = ((2 : ℕ) : 𝓞 K) := by norm_num
    rw [h2, absNorm_span_natCast, IsPrimitiveRoot.finrank_ringOfIntegers_eq_sub_one (p := 5)]
    rfl
  have hη4 : (η ^ 4) ^ 5 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
  have hval : powerResidueSymbolIdeal (span {η ^ 3 * (2 + η)}) 5
      (Ideal.Quotient.mk _ ((2 : ℤ) : 𝓞 K)) = η ^ 2 := by
    rw [← hζ.eisenstein_reciprocity (by decide) hprim (by decide), hmk,
      powerResidueSymbolIdeal_mk_of_pow_eq_one (by rw [hN]; decide) hη4, hN, ← pow_mul]
    have h12 : (4 * ((16 - 1) / 5) : ℕ) = 5 * 2 + 2 := rfl
    rw [h12, pow_add, pow_mul, hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow, one_mul]
  refine ⟨hprim, hval, ?_⟩
  rw [hval]
  exact hζ.toInteger_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by decide) (by decide)

end Quintic

end Examples
