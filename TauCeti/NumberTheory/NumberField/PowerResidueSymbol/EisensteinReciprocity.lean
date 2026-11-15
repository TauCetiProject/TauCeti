/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.EisensteinPrimary
public import TauCeti.NumberTheory.NumberField.Cyclotomic.RootsOfUnity
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.Ideal
import Mathlib.RingTheory.Ideal.Int
import TauCeti.Data.ZMod.Pow
import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.Cyclotomic
import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.StickelbergerPhi.Primary
import TauCeti.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.RingTheory.Ideal.Quotient.Coprime

/-!
# The Eisenstein reciprocity law

Let `p` be an odd prime, `K = ℚ(ζ_p)` the `p`-th cyclotomic field, and `ζ` a primitive `p`-th root
of unity in `K`, so that `𝓞 K = ℤ[ζ]` and `λ = ζ - 1` generates the unique prime above `p`. An
element `α ∈ 𝓞 K` is *primary* (`TauCeti.IsEisensteinPrimary hζ.toInteger α`) if it is coprime to
`λ` and congruent to a rational integer modulo `λ ^ 2`.

The **Eisenstein reciprocity law** states that for every primary `α ∈ 𝓞 K` and every rational
integer `a` not divisible by `p`,

  `(α / a)_p = (a / α)_p`,

where `(· / a)_p` and `(· / α)_p` are the `p`-th power residue symbols
(`Ideal.powerResidueSymbolIdeal`) at the principal ideals `a 𝓞 K` and `α 𝓞 K`. Neither `α` nor `a`
is required to be a nonunit, `a` may be negative or composite, and no coprimality between `α` and
`a` is assumed: when `α 𝓞 K` and `a 𝓞 K` are not coprime, both residue symbols vanish.

The proof has two arithmetic stages:

1. **Reciprocity at the norm of an ideal**
   (`TauCeti.IsEisensteinPrimary.eisenstein_reciprocity_absNorm`). For an ideal `𝔅` of `𝓞 K` with
   `(N 𝔅).Coprime p`, we show `(α / N 𝔅)_p = (N 𝔅 / α)_p`. When `α 𝓞 K` and `(N 𝔅) 𝓞 K` are not
   coprime both sides vanish; otherwise `N(α 𝓞 K)` is coprime to `N 𝔅`
   (`Ideal.absNorm_coprime_of_isCoprime_span_natCast`), and multiplicativity reduces to a maximal
   ideal `P` not above `p`. Stickelberger's relation for primary elements gives `Φ((α)) = ±α ^ γ`
   (`IsPrimitiveRoot.stickelbergerPhi_eq_or_eq_neg_stickelbergerProduct`). Since `p` is odd,
   `(-1 / P)_p = 1`, so Galois equivariance of the Stickelberger product
   (`Ideal.powerResidueSymbolIdeal_stickelbergerProduct`) and the Frobenius identity for `Φ((α))` at
   `P` (`Ideal.powerResidueSymbol_stickelbergerPhi`) equate `(α / N P)_p = (α ^ γ / P)_p =
   (Φ((α)) / P)_p = (N P / α)_p`.

2. **Descent to rational integers** (`TauCeti.IsEisensteinPrimary.eisenstein_reciprocity`).
   For a rational prime `q ≠ p`, any prime `P` of `𝓞 K` above `q` has `N P = q ^ f`, where the
   inertia degree `f` is the order of `q` in `(ℤ/pℤ)ˣ` and therefore divides `p - 1`. Step 1 at `P`
   gives `(α / q)_p ^ f = (q / α)_p ^ f`. Since both symbols are either simultaneously zero or
   `p`-th roots of unity and `f` is coprime to `p`, `(α / q)_p = (q / α)_p`. Multiplicativity in `a`
   and `(-1 / α)_p = 1` extend the equality to every `a ∈ ℤ` with `p ∤ a`.

For an arbitrary element `ζ ^ c * α` prime to `p` written in terms of its primary associate `α`,
combining reciprocity with the supplementary law for `ζ` at `a 𝓞 K`
(`IsPrimitiveRoot.powerResidueSymbolIdeal_span_intCast_toInteger`) yields
`(ζ ^ c * α / a)_p = ζ ^ (c · (|a| ^ (p - 1) - 1) / p) · (a / (ζ ^ c * α))_p`, governed by the
Fermat quotient of `|a|` base `p`
(`TauCeti.IsEisensteinPrimary.powerResidueSymbolIdeal_toInteger_pow_mul`).

## Main results

* `TauCeti.IsEisensteinPrimary.eisenstein_reciprocity_absNorm`: `(α / N 𝔅)_p = (N 𝔅 / α)_p` for
  odd prime `p`, primary `α`, and `(N 𝔅).Coprime p`.
* `TauCeti.IsEisensteinPrimary.eisenstein_reciprocity_natCast`: `(α / a)_p = (a / α)_p` for
  `a : ℕ` with `¬ p ∣ a`.
* `TauCeti.IsEisensteinPrimary.eisenstein_reciprocity`: the Eisenstein reciprocity law
  `(α / a)_p = (a / α)_p` for `a : ℤ` with `¬ (p : ℤ) ∣ a`.
* `TauCeti.IsEisensteinPrimary.powerResidueSymbolIdeal_toInteger_pow_mul`: the Fermat-quotient
  reciprocity formula for `ζ ^ c * α`.

## References

* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §4, Theorem 4.1 and (25).
* N. Xu, *Reciprocity Laws*, §6, Theorem 6.9 and Corollary 6.13.
* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 14, §2,
  Theorem 1.
-/

public section

open NumberField Ideal UniqueFactorizationMonoid

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K} {hζ : IsPrimitiveRoot ζ p} {α : 𝓞 K}

/-- **Eisenstein reciprocity at the norm of an ideal.** Let `p` be an odd prime, `K = ℚ(ζ_p)`, and
`α ∈ 𝓞 K` primary. For every ideal `𝔅` of `𝓞 K` whose norm is prime to `p`,
`(α / N 𝔅)_p = (N 𝔅 / α)_p`, the `p`-th power residue symbols at `(N 𝔅) 𝓞 K` and `α 𝓞 K`. -/
theorem IsEisensteinPrimary.eisenstein_reciprocity_absNorm
    (hα : IsEisensteinPrimary hζ.toInteger α) (hp2 : p ≠ 2) {𝔅 : Ideal (𝓞 K)}
    (h𝔅 : (absNorm 𝔅).Coprime p) :
    powerResidueSymbolIdeal (span {(absNorm 𝔅 : 𝓞 K)}) p
        (Ideal.Quotient.mk (span {(absNorm 𝔅 : 𝓞 K)}) α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk (span {α}) (absNorm 𝔅 : 𝓞 K)) := by
  have hp : p.Prime := Fact.out
  by_cases hcop : IsCoprime (span {α}) (span {(absNorm 𝔅 : 𝓞 K)})
  swap
  · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hcop,
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr (mt IsCoprime.symm hcop)]
  -- Coprimality of `(α)` and `(N 𝔅)` implies `(absNorm (span {α})).Coprime (absNorm 𝔅)`.
  have hα𝔅 : (absNorm (span {α})).Coprime (absNorm 𝔅) :=
    absNorm_coprime_of_isCoprime_span_natCast hcop
  clear hcop
  induction 𝔅 using induction_on_prime with
  | h₁ =>
    rw [zero_eq_bot, absNorm_bot, Nat.coprime_zero_left] at h𝔅
    exact absurd h𝔅 hp.ne_one
  | h₂ 𝔅 h =>
    rw [isUnit_iff.mp h, absNorm_top, Nat.cast_one, span_singleton_one,
      powerResidueSymbolIdeal_top, map_one, MulChar.map_one]
  | h₃ A P hA₀ hP ih =>
    have hP₀ : P ≠ ⊥ := hP.ne_zero
    have hA₀' : A ≠ ⊥ := hA₀
    have : P.IsMaximal := (isPrime_of_prime hP).isMaximal hP₀
    rw [map_mul, Nat.coprime_mul_iff_left] at h𝔅
    rw [map_mul, Nat.coprime_mul_iff_right] at hα𝔅
    have hNP : span {(absNorm P : 𝓞 K)} ≠ ⊥ := by simpa [absNorm_eq_zero_iff] using hP₀
    have hNA : span {(absNorm A : 𝓞 K)} ≠ ⊥ := by simpa [absNorm_eq_zero_iff] using hA₀'
    -- Stickelberger's relation at the maximal factor `P` gives `(α / N P)_p = (N P / α)_p`.
    have hP_rec : powerResidueSymbolIdeal (span {(absNorm P : 𝓞 K)}) p
        (Ideal.Quotient.mk (span {(absNorm P : 𝓞 K)}) α) =
          powerResidueSymbolIdeal (span {α}) p
            (Ideal.Quotient.mk (span {α}) (absNorm P : 𝓞 K)) := by
      rw [← powerResidueSymbolIdeal_stickelbergerProduct hp.two_le P α,
        ← powerResidueSymbol_stickelbergerPhi (span {α}) P h𝔅.1 hα𝔅.1 hp.two_le,
        ← powerResidueSymbolIdeal_of_isMaximal]
      rcases hζ.stickelbergerPhi_eq_or_eq_neg_stickelbergerProduct hp2 hα with hΦ | hΦ
      · rw [hΦ]
      · rw [hΦ, map_neg, powerResidueSymbolIdeal_neg (hp.odd_of_ne_two hp2)]
    rw [map_mul, Nat.cast_mul, ← span_singleton_mul_span_singleton,
      powerResidueSymbolIdeal_mul_right hNP hNA, map_mul, map_mul, hP_rec, ih h𝔅.2 hα𝔅.2]

/-- **The Eisenstein reciprocity law for natural numbers.** Let `p` be an odd prime, `K = ℚ(ζ_p)`,
and `α ∈ 𝓞 K` primary. For every natural number `a` with `¬ p ∣ a`,
`(α / a)_p = (a / α)_p`, the `p`-th power residue symbols at `a 𝓞 K` and `α 𝓞 K`. -/
theorem IsEisensteinPrimary.eisenstein_reciprocity_natCast
    (hα : IsEisensteinPrimary hζ.toInteger α) (hp2 : p ≠ 2) {a : ℕ} (ha : ¬ p ∣ a) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p (Ideal.Quotient.mk (span {(a : 𝓞 K)}) α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk (span {α}) (a : 𝓞 K)) := by
  have hp : p.Prime := Fact.out
  induction a using induction_on_prime with
  | h₁ => exact absurd (dvd_zero p) ha
  | h₂ a hu =>
    rw [Nat.isUnit_iff.mp hu, Nat.cast_one, span_singleton_one, powerResidueSymbolIdeal_top,
      map_one, MulChar.map_one]
  | h₃ b q hb₀ hq ih =>
    have hq_prime : q.Prime := Nat.prime_iff.mpr hq
    have hpq : ¬ p ∣ q := fun h ↦ ha (h.trans (dvd_mul_right q b))
    rw [Nat.cast_mul, ← span_singleton_mul_span_singleton,
      powerResidueSymbolIdeal_mul_right (by simpa using hq_prime.ne_zero) (by simpa using hb₀),
      map_mul, map_mul, ih fun h ↦ ha (h.trans (dvd_mul_left b q))]
    congr 1
    -- Pick a prime `P` of `𝓞 K` above `q`: `N P = q ^ f` with `f ∣ p - 1`, so `f.Coprime p`.
    have : Fact q.Prime := ⟨hq_prime⟩
    have : (span {(q : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime q
    obtain ⟨P, _, _⟩ := exists_maximal_ideal_liesOver_of_isIntegral (span {(q : ℤ)}) (S := 𝓞 K)
    have hqp : ¬ q ∣ p := fun h ↦ hpq ((Nat.prime_dvd_prime_iff_eq hq_prime hp).mp h ▸ dvd_rfl)
    set f := inertiaDeg P ℤ
    have hNP : q ^ f = absNorm P := pow_inertiaDeg q P
    have hPcop : (absNorm P).Coprime p := hNP ▸ ((hp.coprime_iff_not_dvd.mpr hpq).symm).pow_left f
    have hfcop : f.Coprime p := by
      have hf_ord : f = orderOf (q : ZMod p) :=
        IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd q K P hqp
      have hq_ne : (q : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff q p).not.mpr hpq
      exact ((Nat.coprime_self_sub_left hp.pos).mpr (Nat.coprime_one_left p)).coprime_dvd_left
        (hf_ord ▸ ZMod.orderOf_dvd_card_sub_one hq_ne)
    have hpow := hα.eisenstein_reciprocity_absNorm hp2 hPcop
    rw [← hNP, Nat.cast_pow, ← span_singleton_pow, powerResidueSymbolIdeal_pow_right, map_pow,
      map_pow] at hpow
    by_cases hcop : IsCoprime (span {α}) (span {(q : 𝓞 K)})
    swap
    · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hcop,
        powerResidueSymbolIdeal_mk_eq_zero_iff.mpr (mt IsCoprime.symm hcop)]
    have hpow1 {𝔞 : Ideal (𝓞 K)} {x : 𝓞 K} (hc : IsCoprime (span {x}) 𝔞) :
        (powerResidueSymbolIdeal 𝔞 p (Ideal.Quotient.mk 𝔞 x) ^ f) ^ (f⁻¹ : ZMod p).val =
          powerResidueSymbolIdeal 𝔞 p (Ideal.Quotient.mk 𝔞 x) := by
      rw [← pow_mul, pow_mul_val_inv (powerResidueSymbolIdeal_pow_eq_one
        (Ideal.Quotient.isUnit_mk_iff.mpr (isCoprime_iff_sup_eq.mp hc))) hfcop]
    rw [← hpow1 hcop, hpow, hpow1 hcop.symm]

/-- **The Eisenstein reciprocity law.** Let `p` be an odd prime, `K = ℚ(ζ_p)`, and `α ∈ 𝓞 K`
primary. For every rational integer `a` not divisible by `p`,
`(α / a)_p = (a / α)_p`, the `p`-th power residue symbols at `a 𝓞 K` and `α 𝓞 K`.
The integer `a` may be negative, `±1`, or composite, and `α` may be a unit or share factors with
`a`. -/
theorem IsEisensteinPrimary.eisenstein_reciprocity
    (hα : IsEisensteinPrimary hζ.toInteger α) (hp2 : p ≠ 2) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p (Ideal.Quotient.mk (span {(a : 𝓞 K)}) α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk (span {α}) (a : 𝓞 K)) := by
  have ha' : ¬ p ∣ a.natAbs := fun h ↦ ha (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h))
  rcases Int.natAbs_eq a with h | h
  · rw [h, Int.cast_natCast]
    exact hα.eisenstein_reciprocity_natCast hp2 ha'
  · rw [h, Int.cast_neg, Int.cast_natCast, span_singleton_neg, map_neg,
      powerResidueSymbolIdeal_neg ((Fact.out : p.Prime).odd_of_ne_two hp2)]
    exact hα.eisenstein_reciprocity_natCast hp2 ha'

/-- **Eisenstein reciprocity for a root-of-unity multiple of a primary element.**
For an odd prime `p`, primary `α ∈ 𝓞 K`, `a ∈ ℤ` not divisible by `p`, and `c : ℕ`,
`(ζ ^ c * α / a)_p = ζ ^ (c * ((|a| ^ (p - 1) - 1) / p)) * (a / (ζ ^ c * α))_p`. -/
theorem IsEisensteinPrimary.powerResidueSymbolIdeal_toInteger_pow_mul
    (hα : IsEisensteinPrimary hζ.toInteger α) (hp2 : p ≠ 2) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a)
    (c : ℕ) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p
        (Ideal.Quotient.mk (span {(a : 𝓞 K)}) (hζ.toInteger ^ c * α)) =
      hζ.toInteger ^ (c * ((a.natAbs ^ (p - 1) - 1) / p)) *
        powerResidueSymbolIdeal (span {hζ.toInteger ^ c * α}) p
          (Ideal.Quotient.mk (span {hζ.toInteger ^ c * α}) (a : 𝓞 K)) := by
  have hu : IsUnit (hζ.toInteger ^ c) :=
    (hζ.toInteger_isPrimitiveRoot.isUnit (Fact.out : p.Prime).ne_zero).pow c
  have hspan : span {hζ.toInteger ^ c * α} = span {α} := by
    rw [mul_comm, span_singleton_mul_right_unit hu]
  rw [hspan, map_mul, map_mul, map_pow, map_pow,
    hζ.powerResidueSymbolIdeal_span_intCast_toInteger ha, ← pow_mul, mul_comm _ c,
    hα.eisenstein_reciprocity hp2 ha]

end TauCeti

section Examples

open TauCeti

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]

/-- In `ℤ[ω]`, `-1 - 3ω` is Eisenstein primary (`-1 - 3ω = -4 - 3(ω - 1)`), so Eisenstein
reciprocity at the norm `4` of the inert ideal `2 ℤ[ω]` gives `(-1 - 3ω / 4)_3 = (4 / -1 - 3ω)_3`,
and at `2` (or `-10`) gives `(-1 - 3ω / 2)_3 = (2 / -1 - 3ω)_3` (and similarly at `-10`). -/
example {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    let π : 𝓞 K := (-1 : ℤ) - 3 * hζ.toInteger
    powerResidueSymbolIdeal (span {(absNorm (span {(2 : 𝓞 K)}) : 𝓞 K)}) 3
        (Ideal.Quotient.mk _ π) =
      powerResidueSymbolIdeal (span {π}) 3
        (Ideal.Quotient.mk _ (absNorm (span {(2 : 𝓞 K)}) : 𝓞 K)) ∧
    powerResidueSymbolIdeal (span {(2 : 𝓞 K)}) 3 (Ideal.Quotient.mk _ π) =
      powerResidueSymbolIdeal (span {π}) 3 (Ideal.Quotient.mk _ (2 : 𝓞 K)) ∧
    powerResidueSymbolIdeal (span {((-10 : ℤ) : 𝓞 K)}) 3 (Ideal.Quotient.mk _ π) =
      powerResidueSymbolIdeal (span {π}) 3 (Ideal.Quotient.mk _ ((-10 : ℤ) : 𝓞 K)) := by
  intro π
  have hπ : IsEisensteinPrimary hζ.toInteger π := by
    refine isEisensteinPrimary_iff.mpr
      ⟨hζ.isCoprime_toInteger_sub_one_iff.mpr fun hdvd ↦ ?_, -4, ?_⟩
    · have h4 : hζ.toInteger - 1 ∣ ((-4 : ℤ) : 𝓞 K) := by
        convert dvd_add hdvd (dvd_mul_left (hζ.toInteger - 1) (3 : 𝓞 K)) using 1
        simp only [π]
        push_cast
        ring
      exact (by decide : ¬ (3 : ℤ) ∣ -4)
        ((IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff' 3 hζ).mp h4)
    · have h3 : (hζ.toInteger - 1) ^ 2 ∣ ((0 : ℤ) : 𝓞 K) + (-3 : ℤ) * (hζ.toInteger - 1) :=
        (hζ.toInteger_sub_one_sq_dvd_intCast_add_intCast_mul_iff (by decide)).mpr ⟨dvd_zero _, -1,
          by norm_num⟩
      convert h3 using 1
      simp only [π]
      push_cast
      ring
  have h2 : (absNorm (span {(2 : 𝓞 K)})).Coprime 3 :=
    hζ.absNorm_span_singleton_coprime_of_isEisensteinPrimary
      (hζ.isEisensteinPrimary_ofNat_iff.mpr (by decide))
  have hrec2 := hπ.eisenstein_reciprocity_natCast (by decide) (a := 2) (by decide)
  rw [Nat.cast_ofNat] at hrec2
  exact ⟨hπ.eisenstein_reciprocity_absNorm (by decide) h2, hrec2,
    hπ.eisenstein_reciprocity (by decide) (a := -10) (by decide)⟩

/-- Primary normalization is essential: for `p = 3` and `a = 2`, the non-primary unit `ω` satisfies
`(ω / 2)_3 = ω ≠ 1 = (2 / ω)_3`. -/
example {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    powerResidueSymbolIdeal (span {(2 : 𝓞 K)}) 3 (Ideal.Quotient.mk _ hζ.toInteger) ≠
      powerResidueSymbolIdeal (span {hζ.toInteger}) 3 (Ideal.Quotient.mk _ (2 : 𝓞 K)) := by
  have hu : span {hζ.toInteger} = (⊤ : Ideal (𝓞 K)) :=
    span_singleton_eq_top.mpr (hζ.toInteger_isPrimitiveRoot.isUnit (by decide))
  have h2 := hζ.powerResidueSymbolIdeal_span_intCast_toInteger (a := 2) (by decide)
  rw [Int.cast_ofNat] at h2
  have h2' : powerResidueSymbolIdeal (span {(2 : 𝓞 K)}) 3 (Ideal.Quotient.mk _ hζ.toInteger) =
      hζ.toInteger := by simpa using h2
  rw [h2', hu, powerResidueSymbolIdeal_top]
  exact hζ.toInteger_isPrimitiveRoot.ne_one (by decide)

/-- At `a = -1`, both sides of Eisenstein reciprocity equal `1`. -/
example {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {L : Type*} [Field L] [NumberField L]
    [IsCyclotomicExtension {p} ℚ L] {ζ : L} {hζ : IsPrimitiveRoot ζ p} {α : 𝓞 L}
    (hα : IsEisensteinPrimary hζ.toInteger α) :
    powerResidueSymbolIdeal (span {((-1 : ℤ) : 𝓞 L)}) p (Ideal.Quotient.mk _ α) = 1 ∧
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ ((-1 : ℤ) : 𝓞 L)) = 1 := by
  have h1 : powerResidueSymbolIdeal (span {((-1 : ℤ) : 𝓞 L)}) p (Ideal.Quotient.mk _ α) = 1 := by
    rw [Int.cast_neg, Int.cast_one, span_singleton_neg, span_singleton_one,
      powerResidueSymbolIdeal_top]
  refine ⟨h1, ?_⟩
  have hnotdvd : ¬ (p : ℤ) ∣ -1 := fun h ↦ (Fact.out : p.Prime).ne_one
    (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h.neg_right)
  rw [← hα.eisenstein_reciprocity hp2 hnotdvd, h1]

end Examples

end
