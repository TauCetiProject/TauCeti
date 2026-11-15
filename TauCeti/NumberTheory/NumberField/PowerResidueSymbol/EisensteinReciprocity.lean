/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.StickelbergerPhi.Primary
import TauCeti.NumberTheory.NumberField.PrimeIdeal
import TauCeti.RingTheory.Ideal.Norm.AbsNorm

/-!
# The Eisenstein reciprocity law

Let `p` be an odd prime and `K = ℚ(ζ_p)` a `p`-th cyclotomic field over `ℚ`, with primitive `p`-th
root of unity `ζ`. An algebraic integer `α ∈ 𝓞 K` is primary (`TauCeti.IsEisensteinPrimary`) if it
is prime to `ζ - 1` and congruent to a rational integer modulo `(ζ - 1) ^ 2`. The **Eisenstein
reciprocity law** states that for every primary `α ∈ 𝓞 K` and every rational integer `a` not
divisible by `p`,

`(α / a)_p = (a / α)_p`,

where the `p`-th power residue symbols are taken at the principal ideals `a 𝓞 K` and `α 𝓞 K`
(`IsPrimitiveRoot.eisenstein_reciprocity`). Neither `α` nor `a` need be prime or positive, and if
`a 𝓞 K` and `α 𝓞 K` are not coprime then both symbols vanish.

The proof passes through Stickelberger's relation:

1. For any `m ≥ 2` in `ℚ(ζ_m)` and any ideal `𝔅` of `𝓞 K`, Galois equivariance of the power
   residue symbol identifies the symbol at `𝔅` of the Stickelberger product
   `α ^ γ = ∏_σ (σ⁻¹ α) ^ c(σ)` with `(α / N 𝔅)_m`, because `σ` raises every `m`-th root of unity
   to `c(σ)` and `∏_σ σ 𝔅 = (N 𝔅)` (`Ideal.powerResidueSymbolIdeal_stickelbergerProduct`).
2. When `m = p` is an odd prime and `α` is primary, Stickelberger's relation gives
   `Φ((α)) = ± α ^ γ` (`IsPrimitiveRoot.stickelbergerPhi_eq_or_eq_neg_stickelbergerProduct`), while
   `(Φ((α)) / 𝔅)_p = (N 𝔅 / α)_p` (`Ideal.powerResidueSymbolIdeal_stickelbergerPhi`) when `N 𝔅` is
   prime to `p` and to `N(α)`. Since `(-1 / 𝔅)_p = 1` for odd `p`, this gives reciprocity at the
   absolute norm of every ideal `𝔅` prime to `p`: `(α / N 𝔅)_p = (N 𝔅 / α)_p`
   (`IsPrimitiveRoot.eisenstein_reciprocity_absNorm`).
3. For a rational prime `q ≠ p`, picking a prime `P` of `𝓞 K` above `q` gives `N P = q ^ f`, where
   the residue degree `f` divides `[K : ℚ] = p - 1` and is therefore coprime to `p`. Reciprocity at
   `N P` gives `(α / q)_p ^ f = (q / α)_p ^ f`, and taking `p`-coprime roots of `p`-th roots of
   unity yields `(α / q)_p = (q / α)_p`. Multiplicativity in the ideal and in the numerator extends
   this to every natural number and then to every rational integer prime to `p`.

## Main results

* `IsPrimitiveRoot.eisenstein_reciprocity_absNorm`: `(α / N 𝔅)_p = (N 𝔅 / α)_p` for odd prime `p`,
  primary `α`, and `(N 𝔅).Coprime p`.
* `IsPrimitiveRoot.eisenstein_reciprocity_natCast`: `(α / n)_p = (n / α)_p` for natural `n` with
  `¬ p ∣ n`.
* `IsPrimitiveRoot.eisenstein_reciprocity`: **the Eisenstein reciprocity law**,
  `(α / a)_p = (a / α)_p` for `a : ℤ` with `¬ (p : ℤ) ∣ a`.
* `IsPrimitiveRoot.eisenstein_reciprocity_toInteger_pow_mul`:
  `(ζ ^ c α / a)_p = ζ ^ (c * ((|a| ^ (p - 1) - 1) / p)) * (a / ζ ^ c α)_p` for primary `α` and
  `a : ℤ` with `¬ (p : ℤ) ∣ a`.
* `IsPrimitiveRoot.eisenstein_reciprocity_toInteger_mul_iff`: for coprime primary `α` and `a` prime
  to `p`, unshifted reciprocity holds for `ζ α` if and only if `p ^ 2 ∣ |a| ^ (p - 1) - 1`.

## References

* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §4, Theorem 4.1 and (25).
* N. Xu, *Reciprocity Laws*, §6, Theorem 6.9 and Corollary 6.13.
* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 14, §2,
  Theorem 1.
-/

public section

open NumberField Ideal UniqueFactorizationMonoid

/-- An integer cast and its `natAbs` generate the same principal ideal in any commutative ring. -/
private theorem span_intCast_eq_span_natAbs {R : Type*} [CommRing R] (a : ℤ) :
    span {(a : R)} = span {(a.natAbs : R)} := by
  simpa only [Ideal.map_span, Set.image_singleton, Int.coe_castRingHom, Int.cast_natCast] using
    congrArg (Ideal.map (Int.castRingHom R)) (Int.span_natAbs a).symm

/-- Non-divisibility of `a : ℤ` by `(p : ℤ)` transfers to `a.natAbs`. -/
private theorem not_dvd_natAbs {p : ℕ} {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) : ¬ p ∣ a.natAbs :=
  mt (Int.dvd_natAbs.mp ∘ Int.natCast_dvd_natCast.mpr) ha

/-- Two elements of a commutative monoid with zero and no zero divisors, each either `0` or an
`n`-th root of unity, are equal when they have equal `f`-th powers for some `f ≠ 0` coprime to
`n`. -/
private theorem eq_of_pow_eq_of_eq_zero_or_pow_eq_one {M : Type*} [CommMonoidWithZero M]
    [NoZeroDivisors M] {x y : M} {f n : ℕ} (hf0 : f ≠ 0) (hfn : f.Coprime n)
    (hxy : x ^ f = y ^ f) (hx : x = 0 ∨ x ^ n = 1) (hy : y = 0 ∨ y ^ n = 1) : x = y := by
  rcases hx with rfl | hx
  · exact (eq_zero_of_pow_eq_zero (hxy.symm.trans (zero_pow hf0))).symm
  rcases hy with rfl | hy
  · exact eq_zero_of_pow_eq_zero (hxy.trans (zero_pow hf0))
  obtain rfl | hn := eq_or_ne n 0
  · simpa [(Nat.coprime_zero_right f).mp hfn] using hxy
  obtain ⟨u, rfl⟩ := IsUnit.of_pow_eq_one hx hn
  obtain ⟨v, rfl⟩ := IsUnit.of_pow_eq_one hy hn
  refine congrArg Units.val (div_eq_one.mp ((pow_eq_one_iff_of_coprime hfn).mp ⟨?_, ?_⟩))
  · rw [div_pow, div_eq_one, Units.ext_iff]; exact hxy
  · rw [div_pow, div_eq_one, Units.ext_iff]; exact hx.trans hy.symm

/-- Every value of the `n`-th power residue symbol at an ideal is either `0` or an `n`-th root of
unity. -/
private theorem powerResidueSymbolIdeal_eq_zero_or_pow_eq_one {K : Type*} [Field K] [NumberField K]
    {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity (𝓞 K) n] (𝔞 : Ideal (𝓞 K)) (x : 𝓞 K ⧸ 𝔞) :
    powerResidueSymbolIdeal 𝔞 n x = 0 ∨ powerResidueSymbolIdeal 𝔞 n x ^ n = 1 := by
  by_cases hx : IsUnit x
  · exact Or.inr (powerResidueSymbolIdeal_pow_eq_one hx)
  · exact Or.inl (MulChar.map_nonunit _ hx)

/-- In `K = ℚ(ζ_p)` for prime `p`, the residue degree of any prime ideal above a rational prime
divides `[K : ℚ] = p - 1`. -/
private theorem inertiaDeg_dvd_sub_one {p : ℕ} [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] (q : ℕ) [Fact q.Prime] (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (span {(q : ℤ)})] : P.inertiaDeg ℤ ∣ p - 1 := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {p} ℚ K
  have hcard := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (span {(q : ℤ)}) (𝓞 K) Gal(K/ℚ)
  rw [inertiaDegIn_eq_inertiaDeg (span {(q : ℤ)}) P Gal(K/ℚ), IsGalois.card_aut_eq_finrank,
    IsCyclotomicExtension.Rat.finrank p K, Nat.totient_prime Fact.out] at hcard
  exact dvd_of_mul_left_eq _ (by rw [← hcard, ← mul_assoc])

namespace IsPrimitiveRoot

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

/-- **Eisenstein reciprocity at the absolute norm of an ideal.** Let `p` be an odd prime, `α ∈ 𝓞 K`
a primary integer of `ℚ(ζ_p)`, and `𝔅` an ideal of `𝓞 K` whose absolute norm is prime to `p`. Then
`(α / N 𝔅)_p = (N 𝔅 / α)_p`. If `(α)` and `(N 𝔅)` are not coprime, both symbols vanish. -/
theorem eisenstein_reciprocity_absNorm (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {𝔅 : Ideal (𝓞 K)}
    (h𝔅 : (absNorm 𝔅).Coprime p) :
    powerResidueSymbolIdeal (span {(absNorm 𝔅 : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (absNorm 𝔅 : 𝓞 K)) := by
  have hp_two : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp_odd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  by_cases hcop : IsCoprime (span {α}) (span {(absNorm 𝔅 : 𝓞 K)})
  · have hN : (absNorm (span {α})).Coprime (absNorm 𝔅) :=
      absNorm_coprime_of_isCoprime_span_natCast hcop
    rw [← powerResidueSymbolIdeal_stickelbergerProduct hp_two 𝔅 α,
      ← powerResidueSymbolIdeal_stickelbergerPhi (span {α}) 𝔅 h𝔅 hN hp_two]
    rcases hζ.stickelbergerPhi_eq_or_eq_neg_stickelbergerProduct hp2 hα with hΦ | hΦ
    · rw [hΦ]
    · rw [hΦ, map_neg, powerResidueSymbolIdeal_neg hp_odd]
  · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hcop,
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr (mt IsCoprime.symm hcop)]

/-- Eisenstein reciprocity between a primary integer `α` and a rational prime `q ≠ p`. -/
private theorem eisenstein_reciprocity_prime (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {q : ℕ} (hq : q.Prime) (hqp : ¬ p ∣ q) :
    powerResidueSymbolIdeal (span {(q : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (q : 𝓞 K)) := by
  obtain ⟨P, hPprime, hP0, hPover⟩ := NumberField.exists_prime_ne_zero_liesOver (K := K) q hq
  have : Fact q.Prime := ⟨hq⟩
  have : P.IsMaximal := hPprime.isMaximal (by rwa [← zero_eq_bot])
  set f := P.inertiaDeg ℤ
  have hf0 : f ≠ 0 := (Ideal.inertiaDeg_pos P ℤ).ne'
  have hNP : absNorm P = q ^ f := (Ideal.pow_inertiaDeg q P).symm
  have hPcop : (absNorm P).Coprime p :=
    hNP ▸ (((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqp).symm).pow_left f
  -- Reciprocity at `N P = q ^ f` gives equality of the `f`-th powers of the two symbols.
  have hf_eq : powerResidueSymbolIdeal (span {(q : 𝓞 K)}) p (Ideal.Quotient.mk _ α) ^ f =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (q : 𝓞 K)) ^ f := by
    have h := hζ.eisenstein_reciprocity_absNorm hp2 hα hPcop
    rwa [hNP, Nat.cast_pow, ← span_singleton_pow, powerResidueSymbolIdeal_pow_right,
      map_pow, map_pow] at h
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hfp : f.Coprime p :=
    ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr fun hpf ↦ by
      have := Nat.le_of_dvd (Nat.sub_pos_of_lt hp1) (hpf.trans (inertiaDeg_dvd_sub_one K q P))
      omega).symm
  exact eq_of_pow_eq_of_eq_zero_or_pow_eq_one hf0 hfp hf_eq
    (powerResidueSymbolIdeal_eq_zero_or_pow_eq_one _ _)
    (powerResidueSymbolIdeal_eq_zero_or_pow_eq_one _ _)

/-- **Eisenstein reciprocity for natural numbers.** Let `p` be an odd prime, `α ∈ 𝓞 K` a primary
integer of `ℚ(ζ_p)`, and `n : ℕ` a natural number not divisible by `p`. Then
`(α / n)_p = (n / α)_p`. -/
theorem eisenstein_reciprocity_natCast (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {n : ℕ} (hn : ¬ p ∣ n) :
    powerResidueSymbolIdeal (span {(n : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (n : 𝓞 K)) := by
  induction n using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd (dvd_zero p) hn
  | h₂ n hu =>
    rw [Nat.isUnit_iff.mp hu, Nat.cast_one, span_singleton_one, powerResidueSymbolIdeal_top,
      map_one, MulChar.map_one]
  | h₃ a q ha hq ih =>
    have hq_prime : q.Prime := Nat.prime_iff.mpr hq
    have hqp : ¬ p ∣ q := fun h ↦ hn (dvd_mul_of_dvd_left h a)
    have hap : ¬ p ∣ a := fun h ↦ hn (dvd_mul_of_dvd_right h q)
    have hq_bot : (span {(q : 𝓞 K)} : Ideal (𝓞 K)) ≠ ⊥ :=
      mt span_singleton_eq_bot.mp (Nat.cast_ne_zero.mpr hq.ne_zero)
    have ha_bot : (span {(a : 𝓞 K)} : Ideal (𝓞 K)) ≠ ⊥ :=
      mt span_singleton_eq_bot.mp (Nat.cast_ne_zero.mpr ha)
    rw [Nat.cast_mul, ← span_singleton_mul_span_singleton,
      powerResidueSymbolIdeal_mul_right hq_bot ha_bot,
      hζ.eisenstein_reciprocity_prime hp2 hα hq_prime hqp, ih hap, map_mul, map_mul]

/-- **The Eisenstein reciprocity law.** Let `p` be an odd prime, let `K = ℚ(ζ_p)` be a `p`-th
cyclotomic field over `ℚ` with primitive `p`-th root of unity `ζ`, let `α ∈ 𝓞 K` be primary with
respect to `ζ`, and let `a : ℤ` be a rational integer not divisible by `p`. Then
`(α / a)_p = (a / α)_p`, where the `p`-th power residue symbols are taken at the principal ideals
`a 𝓞 K` and `α 𝓞 K`. Neither `α` nor `a` need be prime or positive; if `a 𝓞 K` and `α 𝓞 K` are not
coprime, both sides vanish. -/
theorem eisenstein_reciprocity (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (a : 𝓞 K)) := by
  rw [span_intCast_eq_span_natAbs, hζ.eisenstein_reciprocity_natCast hp2 hα (not_dvd_natAbs ha)]
  rcases Int.natAbs_eq a with h | h
  · nth_rw 2 [h]; rw [Int.cast_natCast]
  · nth_rw 2 [h]; rw [Int.cast_neg, Int.cast_natCast, map_neg,
      powerResidueSymbolIdeal_neg ((Fact.out : p.Prime).odd_of_ne_two hp2)]

/-- **Shifted Eisenstein reciprocity for `ζ ^ c * α`.** For an odd prime `p`, a primary integer
`α ∈ 𝓞 K`, `c : ℕ`, and `a : ℤ` with `¬ (p : ℤ) ∣ a`,
`(ζ ^ c α / a)_p = ζ ^ (c * ((|a| ^ (p - 1) - 1) / p)) * (a / ζ ^ c α)_p`: multiplying `α` by
`ζ ^ c` leaves the ideal `(ζ ^ c * α) = (α)` unchanged while multiplying the symbol at `a 𝓞 K` by
`(ζ / a)_p ^ c`. -/
theorem eisenstein_reciprocity_toInteger_pow_mul (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) (c : ℕ) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p (Ideal.Quotient.mk _ (hζ.toInteger ^ c * α)) =
      hζ.toInteger ^ (c * ((a.natAbs ^ (p - 1) - 1) / p)) *
        powerResidueSymbolIdeal (span {hζ.toInteger ^ c * α}) p
          (Ideal.Quotient.mk _ (a : 𝓞 K)) := by
  have hz : IsPrimitiveRoot hζ.toInteger p := hζ.toInteger_isPrimitiveRoot
  have hnorm : absNorm (span {(a : 𝓞 K)}) = a.natAbs ^ (p - 1) := by
    rw [span_intCast_eq_span_natAbs, absNorm_span_natCast, NumberField.RingOfIntegers.rank,
      IsCyclotomicExtension.Rat.finrank p K, Nat.totient_prime Fact.out]
  have hcop_p : (absNorm (span {(a : 𝓞 K)})).Coprime p :=
    hnorm ▸ (((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr (not_dvd_natAbs ha)).symm).pow_left _
  have hz_sym : powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p (Ideal.Quotient.mk _ hζ.toInteger) =
      hζ.toInteger ^ ((a.natAbs ^ (p - 1) - 1) / p) := by
    rw [powerResidueSymbolIdeal_mk_of_pow_eq_one hcop_p hz.pow_eq_one, hnorm]
  have hspan_unit : span {hζ.toInteger ^ c * α} = span {α} :=
    span_singleton_mul_left_unit ((hz.isUnit (Fact.out : p.Prime).ne_zero).pow c) α
  rw [map_mul, map_mul, map_pow, map_pow, hz_sym, ← pow_mul, mul_comm _ c,
    hζ.eisenstein_reciprocity hp2 hα ha, hspan_unit]

/-- **Obstruction to dropping primary normalization.** For an odd prime `p`, a primary `α ∈ 𝓞 K`,
and an integer `a` prime to `p` with `(α)` and `(a)` coprime, the non-primary associate `ζ * α`
satisfies unshifted reciprocity `(ζ α / a)_p = (a / ζ α)_p` if and only if the Fermat quotient of
`|a|` vanishes modulo `p`, that is, `p ^ 2 ∣ |a| ^ (p - 1) - 1`. -/
theorem eisenstein_reciprocity_toInteger_mul_iff (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a)
    (hcop : IsCoprime (span {α}) (span {(a : 𝓞 K)})) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p (Ideal.Quotient.mk _ (hζ.toInteger * α)) =
        powerResidueSymbolIdeal (span {hζ.toInteger * α}) p (Ideal.Quotient.mk _ (a : 𝓞 K)) ↔
      p ^ 2 ∣ a.natAbs ^ (p - 1) - 1 := by
  have hz : IsPrimitiveRoot hζ.toInteger p := hζ.toInteger_isPrimitiveRoot
  have hshift := hζ.eisenstein_reciprocity_toInteger_pow_mul hp2 hα 1 ha
  rw [pow_one, one_mul] at hshift
  have hspan_unit : span {hζ.toInteger * α} = span {α} :=
    span_singleton_mul_left_unit (hz.isUnit (Fact.out : p.Prime).ne_zero) α
  have hS0 : powerResidueSymbolIdeal (span {hζ.toInteger * α}) p
      (Ideal.Quotient.mk _ (a : 𝓞 K)) ≠ 0 := by
    rw [hspan_unit, ← hζ.eisenstein_reciprocity hp2 hα ha]
    exact fun h ↦ powerResidueSymbolIdeal_mk_eq_zero_iff.mp h hcop
  have hflt : p ∣ a.natAbs ^ (p - 1) - 1 :=
    Nat.dvd_of_mod_eq_zero (Nat.pow_card_sub_one_sub_one_mod_card Fact.out
      (((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr (not_dvd_natAbs ha)).symm))
  rw [hshift, mul_eq_right₀ hS0, hz.pow_eq_one_iff_dvd, Nat.dvd_div_iff_mul_dvd hflt, sq]

end IsPrimitiveRoot

section Examples

open Ideal IsCyclotomicExtension.Rat

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
  {ζ : K} (hζ : IsPrimitiveRoot ζ 3)

/-- In `ℤ[ζ_3]`, the element `-1 - 3 ζ_3` is primary with respect to `ζ_3`. -/
private theorem isEisensteinPrimary_neg_one_sub_three_mul :
    TauCeti.IsEisensteinPrimary hζ.toInteger (-1 - 3 * hζ.toInteger) := by
  rw [TauCeti.isEisensteinPrimary_iff, hζ.isCoprime_toInteger_sub_one_iff]
  have hdvd : (hζ.toInteger - 1) ^ 2 ∣
      (-1 - 3 * hζ.toInteger) - ((-4 : ℤ) : 𝓞 K) := by
    have hrew : (-1 - 3 * hζ.toInteger) - ((-4 : ℤ) : 𝓞 K) =
        ((0 : ℤ) : 𝓞 K) + ((-3 : ℤ) : 𝓞 K) * (hζ.toInteger - 1) := by
      push_cast
      ring
    rw [hrew, hζ.toInteger_sub_one_sq_dvd_intCast_add_intCast_mul_iff (by decide)]
    exact ⟨dvd_zero _, ⟨-1, rfl⟩⟩
  refine ⟨fun hdiv ↦ ?_, -4, hdvd⟩
  have h4 : hζ.toInteger - 1 ∣ ((-4 : ℤ) : 𝓞 K) := by
    have h1 := (dvd_pow_self _ two_ne_zero).trans hdvd
    simpa using dvd_sub hdiv h1
  have h34 : (3 : ℤ) ∣ -4 := (zeta_sub_one_dvd_intCast_iff' 3 hζ).mp h4
  omega

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
/-- In `ℤ[ζ_3]`, the primary element `-1 - 3 ζ_3` is coprime to `2`. -/
private theorem isCoprime_neg_one_sub_three_mul_two :
    IsCoprime (span {-1 - 3 * hζ.toInteger}) (span {((2 : ℤ) : 𝓞 K)}) := by
  set z := hζ.toInteger
  have hcyc : z ^ 2 + z + 1 = 0 := by
    simpa [Finset.sum_range_succ, sq, add_assoc, add_comm, add_left_comm] using
      hζ.toInteger_isPrimitiveRoot.geom_sum_eq_zero (by decide)
  rw [isCoprime_span_singleton_iff]
  refine ⟨-z, z + 2, ?_⟩
  calc (-z) * (-1 - 3 * z) + (z + 2) * ((2 : ℤ) : 𝓞 K)
      = 3 * (z ^ 2 + z + 1) + 1 := by push_cast; ring
    _ = 1 := by rw [hcyc, mul_zero, zero_add]

/- Reciprocity at the norm `N(2 𝓞 K) = 4` for the primary element `α = -1 - 3 ζ_3` in `ℤ[ζ_3]`. -/
example :
    powerResidueSymbolIdeal (span {(absNorm (span {((2 : ℕ) : 𝓞 K)}) : 𝓞 K)}) 3
        (Ideal.Quotient.mk _ (-1 - 3 * hζ.toInteger)) =
      powerResidueSymbolIdeal (span {-1 - 3 * hζ.toInteger}) 3
        (Ideal.Quotient.mk _ (absNorm (span {((2 : ℕ) : 𝓞 K)}) : 𝓞 K)) := by
  have hnorm : absNorm (span {((2 : ℕ) : 𝓞 K)}) = 4 := by
    rw [absNorm_span_natCast, NumberField.RingOfIntegers.rank,
      IsCyclotomicExtension.Rat.finrank 3 K]
    decide
  exact hζ.eisenstein_reciprocity_absNorm (by decide)
    (isEisensteinPrimary_neg_one_sub_three_mul hζ) (by rw [hnorm]; decide)

/- Eisenstein reciprocity for `p = 3`, `α = -1 - 3 ζ_3`, and `a = 2`, as well as against the
negative composite integer `a = -10`. -/
example :
    powerResidueSymbolIdeal (span {((2 : ℤ) : 𝓞 K)}) 3
        (Ideal.Quotient.mk _ (-1 - 3 * hζ.toInteger)) =
      powerResidueSymbolIdeal (span {-1 - 3 * hζ.toInteger}) 3
        (Ideal.Quotient.mk _ ((2 : ℤ) : 𝓞 K)) :=
  hζ.eisenstein_reciprocity (by decide) (isEisensteinPrimary_neg_one_sub_three_mul hζ) (by decide)

example :
    powerResidueSymbolIdeal (span {((-10 : ℤ) : 𝓞 K)}) 3
        (Ideal.Quotient.mk _ (-1 - 3 * hζ.toInteger)) =
      powerResidueSymbolIdeal (span {-1 - 3 * hζ.toInteger}) 3
        (Ideal.Quotient.mk _ ((-10 : ℤ) : 𝓞 K)) :=
  hζ.eisenstein_reciprocity (by decide) (isEisensteinPrimary_neg_one_sub_three_mul hζ) (by decide)

/- Negative control: multiplying the primary integer `α = -1 - 3 ζ_3` by `ζ_3` without
re-normalising destroys reciprocity at `a = 2` since `3 ^ 2 ∤ 2 ^ 2 - 1 = 3`, whereas at the cube
`a = 8` (`3 ^ 2 ∣ 8 ^ 2 - 1 = 63`) the Fermat-quotient factor vanishes. -/
example :
    powerResidueSymbolIdeal (span {((2 : ℤ) : 𝓞 K)}) 3
        (Ideal.Quotient.mk _ (hζ.toInteger * (-1 - 3 * hζ.toInteger))) ≠
      powerResidueSymbolIdeal (span {hζ.toInteger * (-1 - 3 * hζ.toInteger)}) 3
        (Ideal.Quotient.mk _ ((2 : ℤ) : 𝓞 K)) := by
  rw [Ne, hζ.eisenstein_reciprocity_toInteger_mul_iff (by decide)
    (isEisensteinPrimary_neg_one_sub_three_mul hζ) (by decide)
    (isCoprime_neg_one_sub_three_mul_two hζ)]
  decide

example :
    powerResidueSymbolIdeal (span {((8 : ℤ) : 𝓞 K)}) 3
        (Ideal.Quotient.mk _ (hζ.toInteger * (-1 - 3 * hζ.toInteger))) =
      powerResidueSymbolIdeal (span {hζ.toInteger * (-1 - 3 * hζ.toInteger)}) 3
        (Ideal.Quotient.mk _ ((8 : ℤ) : 𝓞 K)) := by
  have h8 : ((8 : ℤ) : 𝓞 K) = ((2 : ℤ) : 𝓞 K) ^ 3 := by norm_num
  have hcop8 : IsCoprime (span {-1 - 3 * hζ.toInteger}) (span {((8 : ℤ) : 𝓞 K)}) := by
    rw [h8, ← span_singleton_pow]
    exact (isCoprime_neg_one_sub_three_mul_two hζ).pow_right
  rw [hζ.eisenstein_reciprocity_toInteger_mul_iff (by decide)
    (isEisensteinPrimary_neg_one_sub_three_mul hζ) (by decide) hcop8]
  decide

end Examples
