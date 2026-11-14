/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.Cyclotomic
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.StickelbergerPhi.Primary
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Int.Basic
import TauCeti.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.RingTheory.Ideal.Quotient.Coprime

/-!
# The Eisenstein reciprocity law

Let `p` be an odd prime and `K = ℚ(ζ_p)` the `p`-th cyclotomic field, with ring of integers
`𝓞 K = ℤ[ζ_p]`. An integer `α ∈ 𝓞 K` is primary (`TauCeti.IsEisensteinPrimary`) if it is prime to
`ζ_p - 1` and congruent to a rational integer modulo `(ζ_p - 1) ^ 2`. **Eisenstein's reciprocity
law** asserts that, for every primary `α ∈ 𝓞 K` and every rational integer `a` not divisible by
`p`, the `p`-th power residue symbols at `(a)` and `(α)` agree:

  `(α / a)_p = (a / α)_p`.

No unit exclusion on `α`, no exclusion `a ≠ ±1`, and no coprimality assumption between `α` and `a`
are needed: when `(α)` and `(a)` share a prime factor, both power residue symbols vanish.

The proof proceeds in three steps from Stickelberger's relation for primary elements
(`IsPrimitiveRoot.stickelbergerPhi_eq_or_eq_neg_stickelbergerProduct`):
1. At a maximal ideal `P` of `𝓞 K` with norm prime to `p`, comparing `(Φ((α)) / P)_p = (N P / α)_p`
   (`Ideal.powerResidueSymbol_stickelbergerPhi`) with `(α ^ γ / P)_p = (α / N P)_p`
   (`Ideal.powerResidueSymbol_stickelbergerProduct`) across `Φ((α)) = ±α ^ γ` yields
   `(α / N P)_p = (N P / α)_p` since `(-1 / P)_p = 1` for odd `p`; multiplicativity extends this to
   every ideal `B` of norm prime to `p` (`IsPrimitiveRoot.eisenstein_reciprocity_absNorm`).
2. For a rational prime `q ≠ p` and a prime `Q` of `𝓞 K` above `q`, `N Q = q ^ f` with residue
   degree `f = ord_p(q) ≤ p - 1`, so `(α / q)_p ^ f = (q / α)_p ^ f` with `p ∤ f`; since both
   values are `p`-th roots of unity (or both zero when `(α)` and `(q)` are not coprime),
   `(α / q)_p = (q / α)_p`.
3. Multiplicativity in the rational argument and `(-1 / ·)_p = 1` give `(α / n)_p = (n / α)_p` for
   `p ∤ n` (`IsPrimitiveRoot.eisenstein_reciprocity_natCast`) and `(α / a)_p = (a / α)_p` for
   `(p : ℤ) ∤ a` (`IsPrimitiveRoot.eisenstein_reciprocity`).

We also record the exact defect when the primary normalization is dropped: replacing a primary `α`
by `ζ_p α` leaves `(a / ζ_p α)_p = (a / α)_p` unchanged while multiplying `(α / a)_p` by
`(ζ_p / a)_p = ζ_p ^ ((|a| ^ (p - 1) - 1) / p)`, so for `(α)` coprime to `(a)` reciprocity holds
for `ζ_p α` if and only if `|a| ^ (p - 1) ≡ 1 (mod p ^ 2)`. Finally, we evaluate the cubic case
`p = 3`, `α = -1 - 3 ζ_3` (primary of norm `7`) at `a = 2`, `N((2)) = 4`, and `a = ±1`, and check
that `(ζ_3 α / 2)_3 = 1 ≠ ζ_3 ^ 2 = (2 / ζ_3 α)_3`.

## Main results

* `IsPrimitiveRoot.eisenstein_reciprocity_absNorm`: `(α / N(B))_p = (N(B) / α)_p` for odd prime
  `p`, primary `α ∈ 𝓞 K`, and `B : Ideal (𝓞 K)` with `(absNorm B).Coprime p`.
* `IsPrimitiveRoot.eisenstein_reciprocity_natCast`: `(α / n)_p = (n / α)_p` for `¬ p ∣ n`.
* `IsPrimitiveRoot.eisenstein_reciprocity`: `(α / a)_p = (a / α)_p` for `¬ (p : ℤ) ∣ a`.
* `IsPrimitiveRoot.powerResidueSymbolIdeal_span_natCast_toInteger_mul` and
  `IsPrimitiveRoot.powerResidueSymbolIdeal_span_intCast_toInteger_mul`:
  `(ζ_p α / a)_p = ζ_p ^ ((|a| ^ (p - 1) - 1) / p) * (a / ζ_p α)_p`.
* `IsPrimitiveRoot.powerResidueSymbolIdeal_span_natCast_toInteger_mul_eq_iff` and
  `IsPrimitiveRoot.powerResidueSymbolIdeal_span_intCast_toInteger_mul_eq_iff`: for `(α)` coprime to
  `(a)`, `(ζ_p α / a)_p = (a / ζ_p α)_p ↔ |a| ^ (p - 1) ≡ 1 [MOD p ^ 2]`.
* `IsPrimitiveRoot.cubic_reciprocity_neg_one_sub_three_mul_two` and
  `IsPrimitiveRoot.cubic_nonprimary_toInteger_mul_neg_one_sub_three_mul_two_ne`: explicit cubic
  evaluations and non-primary counterexample at `p = 3`, `α = -1 - 3 ζ_3`, `a = 2`.

## References

* G. Eisenstein, *Beweis der allgemeinsten Reciprocitätsgesetze zwischen reellen und complexen
  Zahlen*, Monatsber. Königl. Preuß. Akad. Wiss. Berlin (1850), 189–198.
* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §4, Theorem 4.1 and (25).
* N. Xu, *Reciprocity Laws*, §6, Theorem 6.9 and Corollary 6.13.
* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, 2nd ed.,
  Chapter 14, §2, Theorem 1.
-/

public section

open NumberField Ideal UniqueFactorizationMonoid

namespace IsPrimitiveRoot

/-- Raising to an exponent not divisible by `p` is injective on elements of a monoid whose `p`-th
power is `1`. -/
private theorem eq_of_pow_eq_of_pow_prime_eq_one {M : Type*} [Monoid M] {p f : ℕ} (hp : p.Prime)
    (hpf : ¬ p ∣ f) {x y : M} (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : x ^ f = y ^ f) :
    x = y := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  have hf0 : (f : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff f p).not.mpr hpf
  set d := (f : ZMod p)⁻¹.val
  have hmod : f * d % p = 1 := by
    rw [← ZMod.val_natCast p (f * d), Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id', id,
      mul_inv_cancel₀ hf0, ZMod.val_one]
  have hpow (z : M) (hz : z ^ p = 1) : (z ^ f) ^ d = z := by
    rw [← pow_mul, ← Nat.div_add_mod (f * d) p, pow_add, pow_mul, hz, one_pow, one_mul, hmod,
      pow_one]
  rw [← hpow x hx, hxy, hpow y hy]

section PrimeExponent

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

/-- Eisenstein reciprocity at the norm of a maximal ideal prime to `p`. -/
private theorem eisenstein_reciprocity_absNorm_of_isMaximal (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) (P : Ideal (𝓞 K)) [P.IsMaximal]
    (hP : (absNorm P).Coprime p) :
    powerResidueSymbolIdeal (span {(absNorm P : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (absNorm P : 𝓞 K)) := by
  have hm : 2 ≤ p := hp.out.two_le
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  by_cases hcop : IsCoprime (span {α}) (span {(absNorm P : 𝓞 K)})
  · have hAP : (absNorm (span {α})).Coprime (absNorm P) :=
      isCoprime_span_natCast_iff.mp hcop
    rw [← powerResidueSymbol_stickelbergerPhi (span {α}) P hP hAP hm,
      ← powerResidueSymbol_stickelbergerProduct hm P hP α]
    rcases hζ.stickelbergerPhi_eq_or_eq_neg_stickelbergerProduct hp2 hα with hΦ | hΦ
    · rw [hΦ]
    · rw [hΦ, map_neg, ← powerResidueSymbolIdeal_of_isMaximal,
        powerResidueSymbolIdeal_neg hodd, powerResidueSymbolIdeal_of_isMaximal]
  · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hcop,
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr fun h ↦ hcop h.symm]

/-- **Eisenstein reciprocity at the norm of an ideal.** For an odd prime `p`, a primary integer
`α` of `ℚ(ζ_p)`, and an ideal `B` of `𝓞 K` whose norm is coprime to `p`,
`(α / N(B))_p = (N(B) / α)_p`. -/
theorem eisenstein_reciprocity_absNorm (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {B : Ideal (𝓞 K)}
    (hB : (absNorm B).Coprime p) :
    powerResidueSymbolIdeal (span {(absNorm B : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (absNorm B : 𝓞 K)) := by
  induction B using induction_on_prime with
  | h₁ =>
    rw [zero_eq_bot, absNorm_bot, Nat.coprime_zero_left] at hB
    exact absurd hB hp.out.ne_one
  | h₂ B hB' =>
    rw [isUnit_iff.mp hB', absNorm_top, Nat.cast_one, span_singleton_one,
      powerResidueSymbolIdeal_top, map_one, MulChar.map_one]
  | h₃ B P hB₀ hP ih =>
    have : P.IsMaximal := (isPrime_of_prime hP).isMaximal hP.ne_zero
    rw [map_mul, Nat.coprime_mul_iff_left] at hB
    have hNP : span {(absNorm P : 𝓞 K)} ≠ ⊥ := by simpa [absNorm_eq_zero_iff] using hP.ne_zero
    have hNB : span {(absNorm B : 𝓞 K)} ≠ ⊥ := by simpa [absNorm_eq_zero_iff] using hB₀
    rw [absNorm.map_mul, Nat.cast_mul, ← span_singleton_mul_span_singleton,
      powerResidueSymbolIdeal_mul_right hNP hNB,
      eisenstein_reciprocity_absNorm_of_isMaximal hζ hp2 hα P hB.1, ih hB.2, map_mul, map_mul]

/-- Eisenstein reciprocity between a primary integer `α` and a rational prime `q ≠ p`. -/
private theorem eisenstein_reciprocity_prime (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {q : ℕ} (hq : q.Prime) (hpq : ¬ p ∣ q) :
    powerResidueSymbolIdeal (span {(q : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (q : 𝓞 K)) := by
  have : Fact q.Prime := ⟨hq⟩
  have : (span {(q : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime q
  obtain ⟨Q, hQmax, hQlo⟩ :=
    exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) (span {(q : ℤ)})
  have hqp : q.Coprime p := (hp.out.coprime_iff_not_dvd.mpr hpq).symm
  have hNQ : q ^ inertiaDeg Q ℤ = absNorm Q := pow_inertiaDeg q Q
  have hQp : (absNorm Q).Coprime p := hNQ ▸ hqp.pow_left _
  have hflt : inertiaDeg Q ℤ < p := by
    rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd q K Q (hq.coprime_iff_not_dvd.mp hqp),
      ← ZMod.coe_unitOfCoprime q hqp, orderOf_units]
    exact (orderOf_le_card_univ (x := ZMod.unitOfCoprime q hqp)).trans_lt
      ((ZMod.card_units p).trans_lt (Nat.sub_lt hp.out.pos Nat.one_pos))
  have hfnd : ¬ p ∣ inertiaDeg Q ℤ := Nat.not_dvd_of_pos_of_lt (inertiaDeg_pos Q ℤ) hflt
  have hpow := eisenstein_reciprocity_absNorm_of_isMaximal hζ hp2 hα Q hQp
  rw [← hNQ, Nat.cast_pow, ← span_singleton_pow, powerResidueSymbolIdeal_pow_right,
    map_pow, map_pow] at hpow
  by_cases hcop : IsCoprime (span {α}) (span {(q : 𝓞 K)})
  · have hu₁ : IsUnit (Ideal.Quotient.mk (span {(q : 𝓞 K)}) α) :=
      Ideal.Quotient.isUnit_mk_iff.mpr (isCoprime_iff_sup_eq.mp hcop)
    have hu₂ : IsUnit (Ideal.Quotient.mk (span {α}) (q : 𝓞 K)) :=
      Ideal.Quotient.isUnit_mk_iff.mpr (isCoprime_iff_sup_eq.mp hcop.symm)
    exact eq_of_pow_eq_of_pow_prime_eq_one hp.out hfnd
      (powerResidueSymbolIdeal_pow_eq_one hu₁) (powerResidueSymbolIdeal_pow_eq_one hu₂) hpow
  · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hcop,
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr fun h ↦ hcop h.symm]

/-- **The Eisenstein reciprocity law for natural numbers.** For an odd prime `p`, a primary integer
`α` of `ℚ(ζ_p)`, and a natural number `n` not divisible by `p`, `(α / n)_p = (n / α)_p`. -/
theorem eisenstein_reciprocity_natCast (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {n : ℕ} (hn : ¬ p ∣ n) :
    powerResidueSymbolIdeal (span {(n : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (n : 𝓞 K)) := by
  induction n using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd (dvd_zero p) hn
  | h₂ n hn' =>
    rw [Nat.isUnit_iff.mp hn', Nat.cast_one, span_singleton_one, powerResidueSymbolIdeal_top,
      map_one, MulChar.map_one]
  | h₃ a q ha₀ hq ih =>
    have hq_prime : q.Prime := Nat.prime_iff.mpr hq
    have hpq : ¬ p ∣ q := fun hd ↦ hn (hd.trans (dvd_mul_right q a))
    have hpa : ¬ p ∣ a := fun hd ↦ hn (hd.trans (dvd_mul_left a q))
    have hq0 : span {(q : 𝓞 K)} ≠ ⊥ := by simpa using hq_prime.ne_zero
    have ha0 : span {(a : 𝓞 K)} ≠ ⊥ := by simpa using ha₀
    rw [Nat.cast_mul, ← span_singleton_mul_span_singleton,
      powerResidueSymbolIdeal_mul_right hq0 ha0,
      eisenstein_reciprocity_prime hζ hp2 hα hq_prime hpq, ih hpa, map_mul, map_mul]

/-- **The Eisenstein reciprocity law.** For an odd prime `p`, a primary integer `α` of `ℚ(ζ_p)`,
and a rational integer `a` not divisible by `p`, `(α / a)_p = (a / α)_p`. -/
theorem eisenstein_reciprocity (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (a : 𝓞 K)) := by
  have hn : ¬ p ∣ a.natAbs := by rwa [← Int.natCast_dvd]
  rcases Int.natAbs_eq a with h | h
  · rw [h, Int.cast_natCast]
    exact hζ.eisenstein_reciprocity_natCast hp2 hα hn
  · rw [h, Int.cast_neg, Int.cast_natCast, span_singleton_neg, map_neg,
      powerResidueSymbolIdeal_neg (hp.out.odd_of_ne_two hp2)]
    exact hζ.eisenstein_reciprocity_natCast hp2 hα hn

/-- At `a = 1`, both sides of Eisenstein reciprocity equal `1`. -/
theorem eisenstein_reciprocity_one (α : 𝓞 K) :
    powerResidueSymbolIdeal (span {(1 : 𝓞 K)}) p (Ideal.Quotient.mk _ α) = 1 ∧
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (1 : 𝓞 K)) = 1 := by
  rw [span_singleton_one, powerResidueSymbolIdeal_top, map_one, MulChar.map_one]
  exact ⟨rfl, rfl⟩

/-- At `a = -1` for odd `p`, both sides of Eisenstein reciprocity equal `1`. -/
theorem eisenstein_reciprocity_neg_one (hp2 : p ≠ 2) (α : 𝓞 K) :
    powerResidueSymbolIdeal (span {(-1 : 𝓞 K)}) p (Ideal.Quotient.mk _ α) = 1 ∧
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (-1 : 𝓞 K)) = 1 := by
  rw [span_singleton_neg, span_singleton_one, powerResidueSymbolIdeal_top, map_neg,
    powerResidueSymbolIdeal_neg (hp.out.odd_of_ne_two hp2), map_one, MulChar.map_one]
  exact ⟨rfl, rfl⟩

/-- **Non-primary defect at a natural number.** Replacing a primary integer `α` by `ζ α` leaves
`(n / ζ α)_p = (n / α)_p` unchanged while multiplying `(α / n)_p` by
`(ζ / n)_p = ζ ^ ((n ^ (p - 1) - 1) / p)`. -/
theorem powerResidueSymbolIdeal_span_natCast_toInteger_mul (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {n : ℕ} (hn : ¬ p ∣ n) :
    powerResidueSymbolIdeal (span {(n : 𝓞 K)}) p (Ideal.Quotient.mk _ (hζ.toInteger * α)) =
      hζ.toInteger ^ ((n ^ (p - 1) - 1) / p) *
        powerResidueSymbolIdeal (span {hζ.toInteger * α}) p (Ideal.Quotient.mk _ (n : 𝓞 K)) := by
  have hnp : n.Coprime p := (hp.out.coprime_iff_not_dvd.mpr hn).symm
  have hζp := hζ.toInteger_isPrimitiveRoot
  have hspan : span {hζ.toInteger * α} = span {α} :=
    span_singleton_mul_left_unit (hζp.isUnit hp.out.ne_zero) α
  rw [map_mul, map_mul,
    IsCyclotomicExtension.Rat.powerResidueSymbolIdeal_span_natCast_mk_of_pow_eq_one hnp
      hζp.pow_eq_one,
    Nat.totient_prime hp.out, hζ.eisenstein_reciprocity_natCast hp2 hα hn, hspan]

/-- **Non-primary defect at a rational integer.** Replacing a primary integer `α` by `ζ α`
multiplies the reciprocity relation at `a` by `ζ ^ ((|a| ^ (p - 1) - 1) / p)`. -/
theorem powerResidueSymbolIdeal_span_intCast_toInteger_mul (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p (Ideal.Quotient.mk _ (hζ.toInteger * α)) =
      hζ.toInteger ^ ((a.natAbs ^ (p - 1) - 1) / p) *
        powerResidueSymbolIdeal (span {hζ.toInteger * α}) p (Ideal.Quotient.mk _ (a : 𝓞 K)) := by
  have hap : IsCoprime a (p : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]
    exact (hp.out.coprime_iff_not_dvd.mpr (by rwa [← Int.natCast_dvd])).symm
  have hζp := hζ.toInteger_isPrimitiveRoot
  have hspan : span {hζ.toInteger * α} = span {α} :=
    span_singleton_mul_left_unit (hζp.isUnit hp.out.ne_zero) α
  rw [map_mul, map_mul,
    IsCyclotomicExtension.Rat.powerResidueSymbolIdeal_span_intCast_mk_of_pow_eq_one hap
      hζp.pow_eq_one,
    Nat.totient_prime hp.out, hζ.eisenstein_reciprocity hp2 hα ha, hspan]

/-- **Wieferich criterion for reciprocity on `ζ α` (natural-number form).** When `α` is primary,
`p ∤ n`, and `(α)` is coprime to `(n)`, the non-primary element `ζ α` satisfies
`(ζ α / n)_p = (n / ζ α)_p` if and only if `n ^ (p - 1) ≡ 1 [MOD p ^ 2]`. -/
theorem powerResidueSymbolIdeal_span_natCast_toInteger_mul_eq_iff (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {n : ℕ} (hn : ¬ p ∣ n)
    (hcop : IsCoprime (span {α}) (span {(n : 𝓞 K)})) :
    powerResidueSymbolIdeal (span {(n : 𝓞 K)}) p (Ideal.Quotient.mk _ (hζ.toInteger * α)) =
      powerResidueSymbolIdeal (span {hζ.toInteger * α}) p (Ideal.Quotient.mk _ (n : 𝓞 K)) ↔
      n ^ (p - 1) ≡ 1 [MOD p ^ 2] := by
  have hζp := hζ.toInteger_isPrimitiveRoot
  have hspan : span {hζ.toInteger * α} = span {α} :=
    span_singleton_mul_left_unit (hζp.isUnit hp.out.ne_zero) α
  have hz : powerResidueSymbolIdeal (span {hζ.toInteger * α}) p
      (Ideal.Quotient.mk _ (n : 𝓞 K)) ≠ 0 :=
    powerResidueSymbolIdeal_mk_eq_zero_iff.not.mpr (not_not.mpr (hspan ▸ hcop.symm))
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h0 ↦ hn (h0 ▸ dvd_zero p)
  have h1le : 1 ≤ n ^ (p - 1) := Nat.one_le_pow _ _ hn0
  have hnp : n.Coprime p := (hp.out.coprime_iff_not_dvd.mpr hn).symm
  have hdvd : p ∣ n ^ (p - 1) - 1 := by
    rw [← Nat.modEq_iff_dvd' h1le, Nat.ModEq.comm, ← Nat.totient_prime hp.out]
    exact Nat.ModEq.pow_totient hnp
  rw [hζ.powerResidueSymbolIdeal_span_natCast_toInteger_mul hp2 hα hn, mul_eq_right₀ hz,
    hζp.pow_eq_one_iff_dvd, Nat.dvd_div_iff_mul_dvd hdvd, ← sq, ← Nat.modEq_iff_dvd' h1le,
    Nat.ModEq.comm]

/-- **Wieferich criterion for reciprocity on `ζ α` (integer form).** When `α` is primary,
`(p : ℤ) ∤ a`, and `(α)` is coprime to `(a)`, the non-primary element `ζ α` satisfies
`(ζ α / a)_p = (a / ζ α)_p` if and only if `|a| ^ (p - 1) ≡ 1 [MOD p ^ 2]`. -/
theorem powerResidueSymbolIdeal_span_intCast_toInteger_mul_eq_iff (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a)
    (hcop : IsCoprime (span {α}) (span {(a : 𝓞 K)})) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p (Ideal.Quotient.mk _ (hζ.toInteger * α)) =
      powerResidueSymbolIdeal (span {hζ.toInteger * α}) p (Ideal.Quotient.mk _ (a : 𝓞 K)) ↔
      a.natAbs ^ (p - 1) ≡ 1 [MOD p ^ 2] := by
  have hn : ¬ p ∣ a.natAbs := by rwa [← Int.natCast_dvd]
  have hspan_a : span {(a : 𝓞 K)} = span {(a.natAbs : 𝓞 K)} := by
    rcases Int.natAbs_eq a with h | h
    · conv_lhs => rw [h, Int.cast_natCast]
    · conv_lhs => rw [h, Int.cast_neg, Int.cast_natCast, span_singleton_neg]
  have hrhs :
      powerResidueSymbolIdeal (span {hζ.toInteger * α}) p (Ideal.Quotient.mk _ (a : 𝓞 K)) =
        powerResidueSymbolIdeal (span {hζ.toInteger * α}) p
          (Ideal.Quotient.mk _ (a.natAbs : 𝓞 K)) := by
    rcases Int.natAbs_eq a with h | h
    · conv_lhs => rw [h, Int.cast_natCast]
    · conv_lhs =>
        rw [h, Int.cast_neg, Int.cast_natCast, map_neg,
          powerResidueSymbolIdeal_neg (hp.out.odd_of_ne_two hp2)]
  rw [hspan_a, hrhs]
  exact hζ.powerResidueSymbolIdeal_span_natCast_toInteger_mul_eq_iff hp2 hα hn (hspan_a ▸ hcop)

end PrimeExponent

section CubicExamples

variable {K : Type*} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)

/-- In the ring of integers of any field `K` containing a primitive cube root of unity `ζ_3`,
the element `-1 - 3 ζ_3` is primary with respect to `ζ_3`. -/
theorem isEisensteinPrimary_neg_one_sub_three_mul :
    TauCeti.IsEisensteinPrimary hζ.toInteger (-1 - 3 * hζ.toInteger) := by
  have hsum : 1 + hζ.toInteger + hζ.toInteger ^ 2 = 0 := by
    simpa [Finset.sum_range_succ, add_assoc] using
      hζ.toInteger_isPrimitiveRoot.geom_sum_eq_zero (by decide : 1 < 3)
  rw [TauCeti.isEisensteinPrimary_iff]
  refine ⟨⟨-1, hζ.toInteger - 1, ?_⟩, -1, 1, ?_⟩
  · linear_combination hsum
  · push_cast
    linear_combination -hsum

variable [NumberField K] [IsCyclotomicExtension {3} ℚ K]

/-- **Cubic reciprocity check at `a = 2`:** for `α = -1 - 3 ζ_3` in `ℤ[ζ_3]`, both
`(α / 2)_3` and `(2 / α)_3` equal `ζ_3 ^ 2`. -/
theorem cubic_reciprocity_neg_one_sub_three_mul_two :
    powerResidueSymbolIdeal (span {(2 : 𝓞 K)}) 3
        (Ideal.Quotient.mk _ (-1 - 3 * hζ.toInteger)) = hζ.toInteger ^ 2 ∧
      powerResidueSymbolIdeal (span {-1 - 3 * hζ.toInteger}) 3
        (Ideal.Quotient.mk _ (2 : 𝓞 K)) = hζ.toInteger ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hζp := hζ.toInteger_isPrimitiveRoot
  have hsum : 1 + hζ.toInteger + hζ.toInteger ^ 2 = 0 := by
    simpa [Finset.sum_range_succ, add_assoc] using hζp.geom_sum_eq_zero (by decide : 1 < 3)
  have hmod2 : Ideal.Quotient.mk (span {(2 : 𝓞 K)}) (-1 - 3 * hζ.toInteger) =
      Ideal.Quotient.mk (span {(2 : 𝓞 K)}) (hζ.toInteger ^ 2) := by
    rw [Ideal.Quotient.eq, mem_span_singleton]
    refine ⟨-hζ.toInteger, ?_⟩
    linear_combination -hsum
  have hval : powerResidueSymbolIdeal (span {(2 : 𝓞 K)}) 3
      (Ideal.Quotient.mk _ (-1 - 3 * hζ.toInteger)) = hζ.toInteger ^ 2 := by
    rw [hmod2, map_pow, map_pow, ← Nat.cast_two,
      IsCyclotomicExtension.Rat.powerResidueSymbolIdeal_span_natCast_mk_of_pow_eq_one
        (by decide : (2 : ℕ).Coprime 3) hζp.pow_eq_one,
      show (2 ^ Nat.totient 3 - 1) / 3 = 1 by decide, pow_one]
  have hrec : powerResidueSymbolIdeal (span {(2 : 𝓞 K)}) 3
      (Ideal.Quotient.mk _ (-1 - 3 * hζ.toInteger)) =
        powerResidueSymbolIdeal (span {-1 - 3 * hζ.toInteger}) 3
          (Ideal.Quotient.mk _ (2 : 𝓞 K)) := by
    simpa only [Nat.cast_ofNat] using hζ.eisenstein_reciprocity_natCast (n := 2) (by decide)
      hζ.isEisensteinPrimary_neg_one_sub_three_mul (by decide)
  exact ⟨hval, hrec.symm.trans hval⟩

/-- **Ideal-norm reciprocity check at `B = (2)` (`N(B) = 4`):** for `α = -1 - 3 ζ_3` in `ℤ[ζ_3]`,
both `(α / N((2)))_3` and `(N((2)) / α)_3` equal `ζ_3`. -/
theorem cubic_reciprocity_neg_one_sub_three_mul_absNorm_two :
    powerResidueSymbolIdeal (span {(absNorm (span {(2 : 𝓞 K)}) : 𝓞 K)}) 3
        (Ideal.Quotient.mk _ (-1 - 3 * hζ.toInteger)) = hζ.toInteger ∧
      powerResidueSymbolIdeal (span {-1 - 3 * hζ.toInteger}) 3
        (Ideal.Quotient.mk _ (absNorm (span {(2 : 𝓞 K)}) : 𝓞 K)) = hζ.toInteger := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hζp := hζ.toInteger_isPrimitiveRoot
  have hN : absNorm (span {(2 : 𝓞 K)}) = 4 := by
    rw [← Nat.cast_two, absNorm_span_natCast, RingOfIntegers.rank,
      IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat (by decide : 0 < 3))]
    decide
  have hB : (absNorm (span {(2 : 𝓞 K)})).Coprime 3 := by rw [hN]; decide
  obtain ⟨h2, -⟩ := hζ.cubic_reciprocity_neg_one_sub_three_mul_two
  have h4 : powerResidueSymbolIdeal (span {(absNorm (span {(2 : 𝓞 K)}) : 𝓞 K)}) 3
      (Ideal.Quotient.mk _ (-1 - 3 * hζ.toInteger)) = hζ.toInteger := by
    rw [hN, show ((4 : ℕ) : 𝓞 K) = (2 : 𝓞 K) ^ 2 by norm_num, ← span_singleton_pow,
      powerResidueSymbolIdeal_pow_right, h2, ← pow_mul,
      show 2 * 2 = 3 + 1 by rfl, pow_add, hζp.pow_eq_one, one_mul, pow_one]
  exact ⟨h4, (hζ.eisenstein_reciprocity_absNorm (by decide)
    hζ.isEisensteinPrimary_neg_one_sub_three_mul hB).symm.trans h4⟩

/-- **Non-primary negative control at `p = 3`, `a = 2`:** for `α = -1 - 3 ζ_3`, the non-primary
associate `ζ_3 α` violates reciprocity at `2`: `(ζ_3 α / 2)_3 = 1` whereas
`(2 / ζ_3 α)_3 = ζ_3 ^ 2`, and `1 ≠ ζ_3 ^ 2`. -/
theorem cubic_nonprimary_toInteger_mul_neg_one_sub_three_mul_two_ne :
    ¬ TauCeti.IsEisensteinPrimary hζ.toInteger (hζ.toInteger * (-1 - 3 * hζ.toInteger)) ∧
      powerResidueSymbolIdeal (span {(2 : 𝓞 K)}) 3
        (Ideal.Quotient.mk _ (hζ.toInteger * (-1 - 3 * hζ.toInteger))) ≠
      powerResidueSymbolIdeal (span {hζ.toInteger * (-1 - 3 * hζ.toInteger)}) 3
        (Ideal.Quotient.mk _ (2 : 𝓞 K)) := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hζp := hζ.toInteger_isPrimitiveRoot
  have hprim := hζ.isEisensteinPrimary_neg_one_sub_three_mul
  have hnot : ¬ TauCeti.IsEisensteinPrimary hζ.toInteger
      (hζ.toInteger * (-1 - 3 * hζ.toInteger)) := by
    simpa [pow_one] using (hζ.isEisensteinPrimary_toInteger_pow_mul_iff_eq_zero (by decide) hprim
      (i := 1) (by decide)).not.mpr one_ne_zero
  refine ⟨hnot, ?_⟩
  obtain ⟨_, h2⟩ := hζ.cubic_reciprocity_neg_one_sub_three_mul_two
  have hspan : span {hζ.toInteger * (-1 - 3 * hζ.toInteger)} = span {-1 - 3 * hζ.toInteger} :=
    span_singleton_mul_left_unit (hζp.isUnit (by decide)) _
  have hshift : powerResidueSymbolIdeal (span {(2 : 𝓞 K)}) 3
      (Ideal.Quotient.mk _ (hζ.toInteger * (-1 - 3 * hζ.toInteger))) =
        hζ.toInteger ^ ((2 ^ (3 - 1) - 1) / 3) *
          powerResidueSymbolIdeal (span {hζ.toInteger * (-1 - 3 * hζ.toInteger)}) 3
            (Ideal.Quotient.mk _ (2 : 𝓞 K)) := by
    simpa only [Nat.cast_ofNat] using hζ.powerResidueSymbolIdeal_span_natCast_toInteger_mul
      (n := 2) (by decide) hprim (by decide)
  rw [hshift, hspan, h2, show (2 ^ (3 - 1) - 1) / 3 = 1 by decide, pow_one, ← pow_succ',
    hζp.pow_eq_one]
  exact fun h12 ↦ absurd ((hζp.pow_eq_one_iff_dvd 2).mp h12.symm) (by decide)

end CubicExamples

end IsPrimitiveRoot

end
