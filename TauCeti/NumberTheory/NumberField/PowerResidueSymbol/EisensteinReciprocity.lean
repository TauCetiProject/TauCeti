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

Let `p` be an odd prime and let `K = ℚ(ζ_p)` be the `p`-th cyclotomic field, with primitive `p`-th
root of unity `ζ`. Recall that `α ∈ 𝓞 K` is *primary* (`TauCeti.IsEisensteinPrimary hζ.toInteger α`)
when `α` is coprime to `ζ - 1` and congruent to a rational integer modulo `(ζ - 1) ^ 2`. Every
element coprime to `p` has a unique primary associate `ζ ^ c * α` (`0 ≤ c < p`).

**Eisenstein's reciprocity law** states that for every primary `α ∈ 𝓞 K` and every rational integer
`a` not divisible by `p`,

  `(α / a)_p = (a / α)_p`,

where the `p`-th power residue symbols `Ideal.powerResidueSymbolIdeal` are taken at the principal
ideals `a 𝓞 K` and `α 𝓞 K`. More generally, for every ideal `𝔅` of `𝓞 K` whose absolute norm `N 𝔅`
is coprime to `p`,

  `(α / N 𝔅)_p = (N 𝔅 / α)_p`.

Neither `α` nor `a` is required to be a nonunit, positive, or prime, and no coprimality between `α`
and `a` (or `N 𝔅`) is assumed: when `α 𝓞 K` and `a 𝓞 K` share a prime factor, both residue classes
are nonunits and both symbols vanish.

## Proof outline

1. **At the norm of a maximal ideal `P` coprime to `p`:** When `N(α)` and `N P` share a prime
   factor, `(α)` and `(N P)` are not coprime (`Ideal.absNorm_coprime_of_isCoprime_span_natCast`) and
   both symbols are `0`. When `N(α)` is coprime to `N P`, the Gauss sum power `Φ((α))` satisfies
   `(Φ((α)) / P)_p = (N P / α)_p` (`Ideal.powerResidueSymbol_stickelbergerPhi`). Since `p` is odd
   and `α` is primary, Stickelberger's relation gives `Φ((α)) = ± α ^ γ`
   (`IsPrimitiveRoot.stickelbergerPhi_eq_or_eq_neg_stickelbergerProduct`), and `(-1 / P)_p = 1`, so
   `(Φ((α)) / P)_p = (α ^ γ / P)_p`. Galois equivariance of the power residue symbol identifies
   `(α ^ γ / P)_p` with `(α / N P)_p` (`Ideal.powerResidueSymbol_stickelbergerProduct`).
2. **At the norm of an arbitrary ideal `𝔅` coprime to `p`:** Multiplicativity in the ideal extends
   the identity from maximal ideals to `𝔅`.
3. **At a rational prime `q ≠ p`:** Choose a prime `Q` of `𝓞 K` above `q`. Its norm is
   `N Q = q ^ f`, where the residue degree `f` is the multiplicative order of `q` modulo `p`.
   Reciprocity at `N Q` gives `((α / q)_p) ^ f = ((q / α)_p) ^ f`. Because `f ∣ p - 1`, `f` is
   coprime to `p`; since nonzero values of the symbol are `p`-th roots of unity, raising to the
   `f`-th power is injective on `p`-th roots of unity and `(α / q)_p = (q / α)_p` follows.
4. **At an arbitrary integer `a` with `p ∤ a`:** Multiplicativity extends reciprocity from primes
   `q ≠ p` to natural numbers `n` with `p ∤ n`, and `(-1 / 𝔞)_p = 1` for odd `p` extends it to `ℤ`.

## Main results

* `IsPrimitiveRoot.eisenstein_reciprocity_absNorm`: `(α / N 𝔅)_p = (N 𝔅 / α)_p` for `p ≠ 2`, `α`
  primary, and `N 𝔅` coprime to `p`.
* `IsPrimitiveRoot.eisenstein_reciprocity_natCast`: `(α / n)_p = (n / α)_p` for `p ≠ 2`, `α`
  primary, and `n : ℕ` with `p ∤ n`.
* `IsPrimitiveRoot.eisenstein_reciprocity`: `(α / a)_p = (a / α)_p` for `p ≠ 2`, `α` primary, and
  `a : ℤ` with `p ∤ a`.

## References

* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §4, Theorem 4.1.
* N. Xu, *Reciprocity Laws*, §6, Theorem 6.9 and Corollary 6.13.
* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 14, §2,
  Theorem 1.
-/

public section

open NumberField Ideal UniqueFactorizationMonoid

namespace IsPrimitiveRoot

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

/-- Eisenstein reciprocity at the norm of a maximal ideal `P` coprime to `p`. -/
private theorem eisenstein_reciprocity_absNorm_of_isMaximal (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) (P : Ideal (𝓞 K)) [P.IsMaximal]
    (hP : (absNorm P).Coprime p) :
    powerResidueSymbolIdeal (span {(absNorm P : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (absNorm P : 𝓞 K)) := by
  have hp : p.Prime := Fact.out
  by_cases hcop : (absNorm (span {α})).Coprime (absNorm P)
  · have hΦP := powerResidueSymbol_stickelbergerPhi (span {α}) P hP hcop hp.two_le
    have hγP := powerResidueSymbol_stickelbergerProduct hp.two_le P α
    rw [← hΦP, ← hγP, ← powerResidueSymbolIdeal_of_isMaximal]
    rcases hζ.stickelbergerPhi_eq_or_eq_neg_stickelbergerProduct hp2 hα with hΦ | hΦ
    · rw [hΦ]
    · rw [hΦ, map_neg, powerResidueSymbolIdeal_neg (hp.odd_of_ne_two hp2)]
  · -- Non-coprime norms force `(α)` and `(N P)` to share a prime factor, so both symbols vanish.
    have hnc : ¬IsCoprime (span {α}) (span {(absNorm P : 𝓞 K)}) :=
      mt absNorm_coprime_of_isCoprime_span_natCast hcop
    rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr (mt IsCoprime.symm hnc),
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hnc]

/-- **Eisenstein reciprocity at the norm of an ideal.** Let `p` be an odd prime, `K = ℚ(ζ_p)`, and
`α ∈ 𝓞 K` primary. For every ideal `𝔅` of `𝓞 K` whose norm is coprime to `p`,
`(α / N 𝔅)_p = (N 𝔅 / α)_p`. -/
theorem eisenstein_reciprocity_absNorm (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {𝔅 : Ideal (𝓞 K)}
    (h𝔅 : (absNorm 𝔅).Coprime p) :
    powerResidueSymbolIdeal (span {(absNorm 𝔅 : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (absNorm 𝔅 : 𝓞 K)) := by
  induction 𝔅 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    rw [zero_eq_bot, absNorm_bot, Nat.coprime_zero_left] at h𝔅
    exact absurd h𝔅 (Fact.out : p.Prime).ne_one
  | h₂ 𝔅 h =>
    rw [isUnit_iff.mp h, absNorm_top, Nat.cast_one, span_singleton_one, powerResidueSymbolIdeal_top,
      map_one, MulChar.map_one]
  | h₃ 𝔅 P h𝔅₀ hP ih =>
    have _ : P.IsMaximal := (isPrime_of_prime hP).isMaximal hP.ne_zero
    rw [map_mul, Nat.coprime_mul_iff_left] at h𝔅
    have hNP : span {(absNorm P : 𝓞 K)} ≠ ⊥ := by
      simpa [span_singleton_eq_bot, absNorm_eq_zero_iff] using hP.ne_zero
    have hN𝔅 : span {(absNorm 𝔅 : 𝓞 K)} ≠ ⊥ := by
      simpa [span_singleton_eq_bot, absNorm_eq_zero_iff] using h𝔅₀
    rw [map_mul, Nat.cast_mul, ← span_singleton_mul_span_singleton,
      powerResidueSymbolIdeal_mul_right hNP hN𝔅, map_mul, map_mul,
      hζ.eisenstein_reciprocity_absNorm_of_isMaximal hp2 hα P h𝔅.1, ih h𝔅.2]

/-- Eisenstein reciprocity at a rational prime `q ≠ p`, deduced from reciprocity at the norm
`q ^ f` of a prime of `𝓞 K` above `q` via `gcd(f, p) = 1`. -/
private theorem eisenstein_reciprocity_natCast_prime (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {q : ℕ} (hq : q.Prime) (hqp : ¬ p ∣ q) :
    powerResidueSymbolIdeal (span {(q : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (q : 𝓞 K)) := by
  by_cases hcop : IsCoprime (span {α}) (span {(q : 𝓞 K)})
  swap
  · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr (mt IsCoprime.symm hcop),
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hcop]
  have hp : p.Prime := Fact.out
  have _ : Fact q.Prime := ⟨hq⟩
  obtain ⟨Q, _, hQ0, _⟩ := NumberField.exists_prime_ne_zero_liesOver (K := K) q hq
  have _ : Q.IsMaximal := ‹Q.IsPrime›.isMaximal (by rwa [zero_eq_bot] at hQ0)
  set f := Q.inertiaDeg ℤ
  have hNQ : q ^ f = absNorm Q := pow_inertiaDeg q Q
  have hQcop : (absNorm Q).Coprime p :=
    hNQ ▸ ((hp.coprime_iff_not_dvd.mpr hqp).symm.pow_left f)
  -- `f = ord_p(q)` divides `p - 1`, so `f` is positive and `< p`, hence coprime to `p`.
  have hqp' : ¬ q ∣ p := fun h ↦ hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp h ▸ dvd_rfl)
  have hf_dvd : f ∣ p - 1 := by
    rw [show f = orderOf (q : ZMod p) from
      IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd q K Q hqp']
    exact ZMod.orderOf_dvd_card_sub_one ((ZMod.natCast_eq_zero_iff q p).not.mpr hqp)
  have hf_cop : f.Coprime p :=
    (hp.coprime_iff_not_dvd.mpr <| Nat.not_dvd_of_pos_of_lt (inertiaDeg_pos Q ℤ) <|
      (Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) hf_dvd).trans_lt
        (Nat.sub_lt hp.pos zero_lt_one)).symm
  -- Reciprocity at `N Q = q ^ f` equates the `f`-th powers of the two `p`-th roots of unity.
  have hpow := hζ.eisenstein_reciprocity_absNorm hp2 hα hQcop
  rw [← hNQ, Nat.cast_pow, ← span_singleton_pow, powerResidueSymbolIdeal_pow_right, map_pow,
    map_pow] at hpow
  set x := powerResidueSymbolIdeal (span {(q : 𝓞 K)}) p (Ideal.Quotient.mk _ α)
  set y := powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (q : 𝓞 K))
  have hx1 : x ^ p = 1 := powerResidueSymbolIdeal_pow_eq_one <| not_not.mp <|
    mt MulChar.apply_eq_zero_iff.mpr ((powerResidueSymbolIdeal_mk_eq_zero_iff (n := p)).not.mpr
      (not_not.mpr hcop))
  have hy1 : y ^ p = 1 := powerResidueSymbolIdeal_pow_eq_one <| not_not.mp <|
    mt MulChar.apply_eq_zero_iff.mpr ((powerResidueSymbolIdeal_mk_eq_zero_iff (n := p)).not.mpr
      (not_not.mpr hcop.symm))
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hf_cop hp.ne_zero
  have hmod : f * k ≡ 1 [MOD p] := hk
  calc x = x ^ (f * k) := by simpa only [pow_one] using (pow_eq_pow_of_modEq hmod hx1).symm
    _ = y ^ (f * k) := by rw [pow_mul, pow_mul, hpow]
    _ = y := by simpa only [pow_one] using pow_eq_pow_of_modEq hmod hy1

/-- **Eisenstein reciprocity for natural numbers.** Let `p` be an odd prime, `K = ℚ(ζ_p)`, and
`α ∈ 𝓞 K` primary. For every natural number `n` not divisible by `p`, `(α / n)_p = (n / α)_p`. -/
theorem eisenstein_reciprocity_natCast (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {n : ℕ} (hn : ¬ p ∣ n) :
    powerResidueSymbolIdeal (span {(n : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (n : 𝓞 K)) := by
  induction n using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd (dvd_zero p) hn
  | h₂ n hu =>
    rw [Nat.isUnit_iff.mp hu, Nat.cast_one, span_singleton_one, powerResidueSymbolIdeal_top,
      map_one, MulChar.map_one]
  | h₃ n q hn0 hq ih =>
    have hq' : q.Prime := Nat.prime_iff.mpr hq
    have hqp : ¬ p ∣ q := fun h ↦ hn (h.trans (dvd_mul_right q n))
    have hnp : ¬ p ∣ n := fun h ↦ hn (h.trans (dvd_mul_left n q))
    have hq0 : span {(q : 𝓞 K)} ≠ ⊥ := by simpa [span_singleton_eq_bot] using hq'.ne_zero
    have hn0' : span {(n : 𝓞 K)} ≠ ⊥ := by simpa [span_singleton_eq_bot] using hn0
    rw [Nat.cast_mul, ← span_singleton_mul_span_singleton,
      powerResidueSymbolIdeal_mul_right hq0 hn0', map_mul, map_mul,
      hζ.eisenstein_reciprocity_natCast_prime hp2 hα hq' hqp, ih hnp]

/-- **The Eisenstein reciprocity law.** Let `p` be an odd prime, `K = ℚ(ζ_p)`, and `α ∈ 𝓞 K`
primary (`TauCeti.IsEisensteinPrimary hζ.toInteger α`). For every rational integer `a` not divisible
by `p`, `(α / a)_p = (a / α)_p`, where the `p`-th power residue symbols are taken at the principal
ideals `a 𝓞 K` and `α 𝓞 K`. -/
theorem eisenstein_reciprocity (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (a : 𝓞 K)) := by
  have hp_odd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hn : ¬ p ∣ a.natAbs := by rwa [← Int.natCast_dvd_natCast, Int.dvd_natAbs]
  rcases Int.natAbs_eq a with h | h <;> rw [h]
  · rw [Int.cast_natCast]
    exact hζ.eisenstein_reciprocity_natCast hp2 hα hn
  · rw [Int.cast_neg, Int.cast_natCast, span_singleton_neg, map_neg,
      powerResidueSymbolIdeal_neg hp_odd]
    exact hζ.eisenstein_reciprocity_natCast hp2 hα hn

end IsPrimitiveRoot

section Examples

open NumberField Ideal

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]

private theorem absNorm_span_two_three : absNorm (span {(2 : 𝓞 K)}) = 4 := by
  rw [← Nat.cast_ofNat, absNorm_span_natCast, RingOfIntegers.rank,
    IsCyclotomicExtension.finrank (n := 3) K
      (Polynomial.cyclotomic.irreducible_rat (by norm_num)),
    Nat.totient_prime Nat.prime_three]
  rfl

/- Explicit cubic evaluation via Eisenstein reciprocity: in `ℤ[ω]`, `α = -1 - 3ω` is primary (of
norm `7`) and congruent to `ω²` modulo `2` because `(-1 - 3ω) - ω² = -(1 + ω + ω²) - 2ω = -2ω`.
Since `N(2 ℤ[ω]) = 4`, `(2 / (-1 - 3ω))_3 = (-1 - 3ω / 2)_3 = (ω² / 2)_3 = (ω²)^((4 - 1) / 3) = ω²`,
certifying that `2` is a cubic nonresidue modulo `-1 - 3ω`. -/
example {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    powerResidueSymbolIdeal (span {-1 - 3 * hζ.toInteger}) 3 (Ideal.Quotient.mk _ (2 : 𝓞 K)) =
      hζ.toInteger ^ 2 := by
  set ω := hζ.toInteger
  have hα : TauCeti.IsEisensteinPrimary ω (-1 - 3 * ω) := by
    rw [TauCeti.isEisensteinPrimary_iff, hζ.isCoprime_toInteger_sub_one_iff]
    refine ⟨fun hdvd ↦ hζ.zeta_sub_one_prime'.not_isUnit ?_, -1, ?_⟩
    · have h3 : ω - 1 ∣ 3 * ω := hζ.toInteger_sub_one_dvd_prime'.mul_right ω
      exact isUnit_of_dvd_unit (by simpa using dvd_add hdvd h3) isUnit_one.neg
    · have hsq : (ω - 1) ^ 2 ∣ ((-3 : ℤ) : 𝓞 K) :=
        (hζ.toInteger_sub_one_sq_dvd_intCast_iff (by decide)).mpr ⟨-1, by ring⟩
      simpa [sub_eq_add_neg, add_assoc] using hsq.mul_right ω
  have hN2 : absNorm (span {(2 : 𝓞 K)}) = 4 := absNorm_span_two_three
  have hcyc : 1 + ω + ω ^ 2 = 0 := by
    have h := hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic (by decide : 0 < 3)
    rw [Polynomial.IsRoot.def, Polynomial.cyclotomic_three] at h
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one] at h
    linear_combination h
  have hmk : Ideal.Quotient.mk (span {(2 : 𝓞 K)}) (-1 - 3 * ω) = Ideal.Quotient.mk _ (ω ^ 2) := by
    rw [Ideal.Quotient.eq, mem_span_singleton]
    refine ⟨-ω, ?_⟩
    linear_combination -hcyc
  have hrec := hζ.eisenstein_reciprocity (by decide) hα (a := 2) (by decide)
  rw [Int.cast_ofNat] at hrec
  rw [← hrec, hmk,
    powerResidueSymbolIdeal_mk_of_pow_eq_one (by rw [hN2]; decide)
      (by rw [← pow_mul, mul_comm, pow_mul, hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]),
    hN2, show (4 - 1) / 3 = 1 by decide, pow_one]

/- Eisenstein reciprocity at the norm `N(2 ℤ[ω]) = 4` of an inert prime ideal. -/
example {ζ : K} (hζ : IsPrimitiveRoot ζ 3) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) :
    powerResidueSymbolIdeal (span {(4 : 𝓞 K)}) 3 (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) 3 (Ideal.Quotient.mk _ (4 : 𝓞 K)) := by
  have hN2 : absNorm (span {(2 : 𝓞 K)}) = 4 := absNorm_span_two_three
  have h := hζ.eisenstein_reciprocity_absNorm (by decide) hα
    (𝔅 := span {(2 : 𝓞 K)}) (by rw [hN2]; decide)
  rwa [hN2, Nat.cast_ofNat] at h

/- Negative composite integers (`a = -10`) and non-coprime pairs (`α = 2`, `a = 2`). -/
example {ζ : K} (hζ : IsPrimitiveRoot ζ 3) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) :
    powerResidueSymbolIdeal (span {((-10 : ℤ) : 𝓞 K)}) 3 (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) 3 (Ideal.Quotient.mk _ ((-10 : ℤ) : 𝓞 K)) ∧
    powerResidueSymbolIdeal (span {((2 : ℤ) : 𝓞 K)}) 3
      (Ideal.Quotient.mk _ ((2 : ℤ) : 𝓞 K)) = 0 := by
  refine ⟨hζ.eisenstein_reciprocity (by decide) hα (by decide),
    powerResidueSymbolIdeal_mk_eq_zero_iff.mpr fun h ↦ ?_⟩
  have h1 : IsUnit ((2 : ℤ) : 𝓞 K) := by
    rw [← span_singleton_eq_top, ← sup_idem (a := span {((2 : ℤ) : 𝓞 K)})]
    exact h.sup_eq
  have hN : absNorm (span {(2 : 𝓞 K)}) = 1 := by
    rw [← Int.cast_ofNat, span_singleton_eq_top.mpr h1, absNorm_top]
  have hN2 : absNorm (span {(2 : 𝓞 K)}) = 4 := absNorm_span_two_three
  omega

/- Sharpness of primary normalization: `ω` is coprime to `3` in `ℤ[ω]` but is not primary, and
`(ω / 2)_3 = ω ≠ 1 = (2 / ω)_3`. -/
example {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    powerResidueSymbolIdeal (span {((2 : ℤ) : 𝓞 K)}) 3 (Ideal.Quotient.mk _ hζ.toInteger) ≠
      powerResidueSymbolIdeal (span {hζ.toInteger}) 3 (Ideal.Quotient.mk _ ((2 : ℤ) : 𝓞 K)) := by
  have hN2 : absNorm (span {(2 : 𝓞 K)}) = 4 := absNorm_span_two_three
  have hunit : IsUnit hζ.toInteger := hζ.toInteger_isPrimitiveRoot.isUnit (by decide)
  rw [Int.cast_ofNat, span_singleton_eq_top.mpr hunit, powerResidueSymbolIdeal_top,
    powerResidueSymbolIdeal_mk_of_pow_eq_one (by rw [hN2]; decide)
      hζ.toInteger_isPrimitiveRoot.pow_eq_one,
    hN2, show (4 - 1) / 3 = 1 by decide, pow_one]
  exact hζ.toInteger_isPrimitiveRoot.ne_one (by decide)

end Examples
