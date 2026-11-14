/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.Primary
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.Ideal
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import TauCeti.NumberTheory.GaussSum.Basic
import TauCeti.NumberTheory.LegendreSymbol.Complex
import TauCeti.NumberTheory.LegendreSymbol.ZModChar
import TauCeti.NumberTheory.MulChar.Basic
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.GaussSum
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.RationalResidue
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.SupplementaryLaws
import TauCeti.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.RingTheory.Ideal.Quotient.Coprime
import TauCeti.RingTheory.IntegralClosure.Map

/-!
# The law of biquadratic (quartic) reciprocity

Let `K = ℚ(i)`, given as a number field with `IsCyclotomicExtension {4} ℚ K`, so that
`𝓞 K = ℤ[i]`, and write `(α / β)_4` for the quartic power residue symbol at the principal ideal
`β 𝓞 K` (`Ideal.powerResidueSymbolIdeal`). An element of `𝓞 K` is *primary* if it is congruent to
`1` modulo `(1 + i)³` (`TauCeti.IsPrimaryGaussian`). The law of biquadratic reciprocity states
that for primary elements `π₁` and `π₂` of `𝓞 K`,

`(π₂ / π₁)_4 = (π₁ / π₂)_4 · (-1) ^ (((N π₁ - 1) / 4) ((N π₂ - 1) / 4))`

(`TauCeti.IsPrimaryGaussian.quartic_reciprocity`), where `N α` is the absolute norm of `α 𝓞 K`. In
coordinates `π₁ = a + b i` and `π₂ = c + d i`, the norm congruence
`(N(a + b i) - 1) / 4 ≡ (a - 1) / 2 (mod 2)` rewrites the sign as
`(-1) ^ (((a - 1) / 2) ((c - 1) / 2))` (`TauCeti.IsPrimaryGaussian.quartic_reciprocity_add_mul`).
For coprime primary elements, the two symbols are negatives of one another when
`N π₁ ≡ N π₂ ≡ 5 (mod 8)` (`TauCeti.IsPrimaryGaussian.quartic_reciprocity_eq_neg_iff`) and are
equal when at least one norm is `1` modulo `8`
(`TauCeti.IsPrimaryGaussian.quartic_reciprocity_eq_iff`).

The proof proceeds in three stages:

1. **Rational integers against primary elements**
   (`TauCeti.IsPrimaryGaussian.quartic_reciprocity_intCast_mul_χ₄`,
   `TauCeti.IsPrimaryGaussian.quartic_reciprocity_intCast`,
   `TauCeti.IsPrimaryGaussian.quartic_reciprocity_natCast`): for a primary prime `π` of `𝓞 K` and
   an odd prime `q` not divisible by `π`, let `P = π 𝓞 K`, `χ = (· / P)_4`, and `g = g(χ, ψ)` in
   the algebraic integers of `ℂ`, where `g ^ 4 = π ^ 3 σ π` for complex conjugation `σ`
   (`Ideal.gaussSum_powerResidueSymbol_four_pow_four_eq_pow_three_mul`).
   * If `q ≡ 3 (mod 4)`, then `Q = q 𝓞 K` is prime of norm `q²` with Frobenius `x ^ q ≡ σ x`
     modulo `Q`; comparing `g ^ (q + 1)` computed from `g ^ 4 = π ^ 3 σ π` and from the Gauss-sum
     Frobenius congruence modulo a prime above `Q` gives `(-q / π)_4 = (π / q)_4`.
   * If `q ≡ 1 (mod 4)`, then `q = σ β · β` splits into conjugate primes `L = β 𝓞 K` and `σ L` of
     norm `q`; comparing `g ^ (q - 1)` modulo a prime above `L` with `g ^ 4 = π ^ 3 σ π` and
     applying Galois equivariance (`Ideal.map_powerResidueSymbol`) gives `(q / π)_4 = (π / q)_4`.
   Multiplicativity in both variables extends `((m χ₄(m)) / x)_4 = (x / m)_4` to every primary
   `x ∈ 𝓞 K` and every odd integer `m`.
2. **Primary elements with coprime coordinates**: if `π₁ = a + b i` and `π₂ = c + d i` are coprime
   primary elements with `gcd(a, b) = gcd(c, d) = 1` and `m = a c + b d`, the congruences
   `c π₁ ≡ m (mod π₂)` and `a π₂ ≡ m (mod π₁)`, together with `σ π₁ · π₂ ≡ (a d - b c) i (mod m)`,
   the triviality of the quartic symbol on coprime rational integers
   (`Ideal.powerResidueSymbolIdeal_intCast_four`), and the supplementary laws for `i` and `-1`,
   express `(π₂ / π₁)_4 (π₁ / π₂)_4⁻¹` as `(i / a)_4 (i / c)_4 (i / m)_4`.
3. **General primary elements**: writing `π₁ = m₁ π₁'` and `π₂ = m₂ π₂'` with
   `m₁ ≡ m₂ ≡ 1 (mod 4)` and `π₁', π₂'` primary of coprime coordinates reduces the general law to
   stages 1 and 2.

## Main results

* `TauCeti.IsPrimaryGaussian.quartic_reciprocity_intCast_mul_χ₄`:
  `((m χ₄(m)) / x)_4 = (x / m)_4` for primary `x` and odd `m : ℤ`.
* `TauCeti.IsPrimaryGaussian.quartic_reciprocity_intCast`:
  `(a / x)_4 = (x / a)_4` for primary `x` and `a ≡ 1 (mod 4)`.
* `TauCeti.IsPrimaryGaussian.quartic_reciprocity_natCast`:
  `((-1) ^ ((q - 1) / 2) * q / x)_4 = (x / q)_4` for primary `x` and odd `q : ℕ`.
* `TauCeti.IsPrimaryGaussian.quartic_reciprocity`: the law of biquadratic (quartic) reciprocity.
* `TauCeti.IsPrimaryGaussian.quartic_reciprocity_add_mul`: the coordinate form
  `(π₂ / π₁)_4 = (π₁ / π₂)_4 · (-1) ^ (((a - 1) / 2) ((c - 1) / 2))` for primary `π₁ = a + b i`
  and `π₂ = c + d i`.
* `TauCeti.IsPrimaryGaussian.quartic_reciprocity_of_absNorm_modEq_one`,
  `TauCeti.IsPrimaryGaussian.quartic_reciprocity_of_absNorm_modEq_five`: symmetry when one norm is
  `1 (mod 8)` and negation when both norms are `5 (mod 8)`.
* `TauCeti.IsPrimaryGaussian.quartic_reciprocity_eq_neg_iff`,
  `TauCeti.IsPrimaryGaussian.quartic_reciprocity_eq_iff`: exact norm criteria modulo `8` for
  coprime primary elements.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 9, §§8–9.
* N. Xu, *Reciprocity Laws*, §5, Theorem 5.8 and Propositions 5.11–5.13.
* M. C. Relyea, *On finite fields and higher reciprocity*, §4.1, Theorem 4.4 (where the product of
  the two symbols is written in place of their quotient).
-/

public section

open NumberField Ideal

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

/-! ### Rational primes and rational integers against primary elements -/

section RationalReciprocity

/-- An inert prime `q ≡ 3 (mod 4)` generates a maximal ideal in `𝓞 K = ℤ[i]`. -/
private theorem isMaximal_span_natCast_of_mod_four_eq_three {q : ℕ} (hq : q.Prime)
    (hq3 : q % 4 = 3) : (span {(q : 𝓞 K)}).IsMaximal :=
  ((span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr
    (prime_natCast_of_mod_four_eq_three hq hq3)).isMaximal (by simpa using hq.ne_zero)

/-- At an inert rational prime `q ≡ 3 (mod 4)`, the `q`-th power map on `𝓞 K ⧸ (q)` coincides with
complex conjugation `σ`, because `a ^ q ≡ a (mod q)` for `a : ℤ` and `i ^ q = i ^ 3 = σ i`. -/
private theorem mk_span_natCast_pow_eq_conj {σ : 𝓞 K →+* 𝓞 K}
    (hσ : ∀ x : 𝓞 K, x ^ 4 = 1 → σ x = x ^ 3) {q : ℕ} (hq : q.Prime) (hq3 : q % 4 = 3)
    (x : 𝓞 K) :
    (Ideal.Quotient.mk (span {(q : 𝓞 K)}) x) ^ q =
      Ideal.Quotient.mk (span {(q : 𝓞 K)}) (σ x) := by
  set Q : Ideal (𝓞 K) := span {(q : 𝓞 K)}
  have : Q.IsMaximal := isMaximal_span_natCast_of_mod_four_eq_three hq hq3
  have : Fact q.Prime := ⟨hq⟩
  have hq0 : (q : 𝓞 K ⧸ Q) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem]
    exact mem_span_singleton_self _
  have : CharP (𝓞 K ⧸ Q) q := (CharP.charP_iff_prime_eq_zero hq).mpr hq0
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
  obtain ⟨a, b, rfl⟩ := hζ.exists_intCast_add_intCast_mul_toInteger_eq (by decide) x
  have hint (c : ℤ) : (Ideal.Quotient.mk Q (c : 𝓞 K)) ^ q = Ideal.Quotient.mk Q (c : 𝓞 K) := by
    have hcast : Ideal.Quotient.mk Q (c : 𝓞 K) = ZMod.castHom dvd_rfl (𝓞 K ⧸ Q) c := by simp
    rw [hcast, ← map_pow, ZMod.pow_card]
  have hi : hζ.toInteger ^ q = σ hζ.toInteger := by
    have h4 := hζ.toInteger_isPrimitiveRoot.pow_eq_one
    rw [hσ _ h4, show q = 4 * (q / 4) + 3 by omega, pow_add, pow_mul, h4, one_pow, one_mul]
  rw [map_add, map_mul, add_pow_char, mul_pow, hint a, hint b, ← map_pow, hi, ← map_mul, ← map_add,
    map_add σ, map_mul σ, map_intCast σ, map_intCast σ]

/-- Evaluating `(π_I g) ^ (q + 1)` via the Gauss-sum Frobenius congruence at an inert prime
`q ≡ 3 (mod 4)` gives `(-q / P)_4 · N P` modulo `I`. -/
private theorem gaussSum_pow_succ_eq_at_inert {P : Ideal (𝓞 K)} [P.IsMaximal] [Fintype (𝓞 K ⧸ P)]
    (hP : (absNorm P).Coprime 4) {q : ℕ} (hq : q.Prime) (hq3 : q % 4 = 3)
    (hqP : Ideal.Quotient.mk P (q : 𝓞 K) ≠ 0) {R : Type*} [CommRing R] [IsDomain R]
    {f : 𝓞 K →+* R} (hf : Function.Injective f) {ψ : AddChar (𝓞 K ⧸ P) R} (hψ : ψ.IsPrimitive)
    (I : Ideal R) [CharP (R ⧸ I) q] :
    (Ideal.Quotient.mk I (gaussSum ((powerResidueSymbol P 4).ringHomComp f) ψ)) ^ (q + 1) =
      Ideal.Quotient.mk I
        (f (powerResidueSymbol P 4 (Ideal.Quotient.mk P (-(q : 𝓞 K))) * absNorm P)) := by
  let _ := Ideal.Quotient.field P
  have : Fact q.Prime := ⟨hq⟩
  let χ := (powerResidueSymbol P 4).ringHomComp f
  let πI := Ideal.Quotient.mk I
  let χ' := χ.ringHomComp πI
  let ψ' := πI.toMonoidHom.compAddChar ψ
  have hord : orderOf χ = 4 := by
    rw [MulChar.orderOf_ringHomComp hf, orderOf_powerResidueSymbol hP]
  have hχne : χ ≠ 1 := by rw [← orderOf_eq_one_iff.ne, hord]; decide
  have hχ4 : χ ^ 4 = 1 := hord ▸ pow_orderOf_eq_one χ
  have hχ'4 : χ' ^ 4 = 1 := by rw [MulChar.ringHomComp_pow, hχ4, MulChar.ringHomComp_one]
  have hχ'q : χ' ^ q = χ' ^ 3 := by
    rw [show q = 4 * (q / 4) + 3 by omega, pow_add, pow_mul, hχ'4, one_pow, one_mul]
  have hχ'inv : (χ' ^ 3)⁻¹ = χ' := inv_eq_of_mul_eq_one_right (by rw [← pow_succ, hχ'4])
  let uq : (𝓞 K ⧸ P)ˣ :=
    (by rwa [← map_natCast (Ideal.Quotient.mk P)] : (q : 𝓞 K ⧸ P) ≠ 0).isUnit.unit
  have huq : (uq : 𝓞 K ⧸ P) = q := IsUnit.unit_spec _
  have hg_map (φ : MulChar (𝓞 K ⧸ P) R) :
      gaussSum (φ.ringHomComp πI) ψ' = πI (gaussSum φ ψ) := by
    simp only [gaussSum, map_sum, map_mul, MulChar.ringHomComp_apply]; rfl
  have hfrob : (πI (gaussSum χ ψ)) ^ q = χ' uq * πI (gaussSum (χ ^ 3) ψ) := by
    rw [← hg_map χ, gaussSum_frob q χ' ψ', hχ'q, AddChar.pow_mulShift, ← huq,
      gaussSum_mulShift_eq, hχ'inv, MulChar.ringHomComp_pow, hg_map (χ ^ 3)]
  have hprod := gaussSum_mul_gaussSum_pow_orderOf_sub_one hχne hψ
  rw [hord, ← Nat.card_eq_fintype_card, ← absNorm_eq_natCard] at hprod
  calc (πI (gaussSum χ ψ)) ^ (q + 1)
      = χ' uq * (πI (gaussSum χ ψ) * πI (gaussSum (χ ^ 3) ψ)) := by rw [pow_succ, hfrob]; ring
    _ = χ' uq * πI (χ (-1) * absNorm P) := by rw [← map_mul, hprod]
    _ = πI (f (powerResidueSymbol P 4 (Ideal.Quotient.mk P (-(q : 𝓞 K))) * absNorm P)) := by
      rw [neg_eq_neg_one_mul (q : 𝓞 K)]
      simp only [χ', χ, huq, map_mul, map_neg, map_one, map_natCast, MulChar.ringHomComp_apply]
      ring

/-- Evaluating `((π ^ 3 σ π) ^ ((q + 1) / 4))` modulo an inert prime `Q = q 𝓞 K` with
`q ≡ 3 (mod 4)` gives `(π / Q)_4 · N(π 𝓞 K)` modulo `Q`. -/
private theorem mk_pow_three_mul_conj_pow_eq_at_inert {π : 𝓞 K} {σ : 𝓞 K →+* 𝓞 K}
    (hσ : ∀ x : 𝓞 K, x ^ 4 = 1 → σ x = x ^ 3) {q : ℕ} (hq : q.Prime) (hq3 : q % 4 = 3)
    (hcop : (absNorm (span {π})).Coprime q) {Q : Ideal (𝓞 K)} [Q.IsMaximal]
    (hQ : Q = span {(q : 𝓞 K)}) :
    Ideal.Quotient.mk Q ((π ^ 3 * σ π) ^ ((q + 1) / 4)) =
      Ideal.Quotient.mk Q (powerResidueSymbol Q 4 (Ideal.Quotient.mk Q π) *
        absNorm (span {π})) := by
  have hNQ : absNorm Q = q ^ 2 := hQ ▸ absNorm_span_natCast_four q
  have hQ4 : (absNorm Q).Coprime 4 := by
    rw [hNQ]
    exact Nat.Coprime.pow_left 2 (Nat.Coprime.pow_right 2
      (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr (by omega))))
  have hNP : (absNorm (span {π}) : 𝓞 K) = π * σ π := by
    rw [← Int.cast_natCast, RingOfIntegers.natCast_absNorm_span_singleton_of_four,
      intCast_norm_eq_mul_of_four hσ]
  have hπQ : Ideal.Quotient.mk Q π ≠ 0 := by
    intro h
    rw [Ideal.Quotient.eq_zero_iff_mem] at h
    exact natCast_notMem_of_coprime_absNorm ‹Q.IsMaximal›.ne_top
      (by rw [hNQ]; exact hcop.pow_right 2) (hNP ▸ Q.mul_mem_right (σ π) h)
  have hexp : (3 + q) * ((q + 1) / 4) = (absNorm Q - 1) / 4 + (q + 1) := by
    rw [hNQ]
    set m := (q + 1) / 4
    have hdiv : 4 * m = q + 1 := by omega
    have hsq : q ^ 2 - 1 = 4 * ((q - 1) * m) := by
      have h1 : (q - 1) * (4 * m) + 1 = q ^ 2 := by rw [hdiv]; zify [hq.one_lt.le]; ring
      exact Nat.sub_eq_of_eq_add (by linear_combination h1.symm)
    rw [hsq, Nat.mul_div_cancel_left _ (by decide : 0 < 4)]
    zify [hq.one_lt.le]
    linear_combination (1 : ℤ) * (by exact_mod_cast hdiv : (4 : ℤ) * m = q + 1)
  have hconj (x : 𝓞 K) : (Ideal.Quotient.mk Q x) ^ q = Ideal.Quotient.mk Q (σ x) := by
    subst hQ; exact mk_span_natCast_pow_eq_conj hσ hq hq3 x
  rw [map_pow, map_mul, map_pow, ← hconj π, ← pow_add, ← pow_mul, hexp, pow_add, pow_succ',
    hconj π, ← map_mul, ← hNP, ← mk_powerResidueSymbol hQ4 hπQ, map_mul]

/-- Quartic reciprocity between `P = π 𝓞 K` and `Q = q 𝓞 K` (`q ≡ 3 (mod 4)`) given an injective
homomorphism `f : 𝓞 K →+* R`, a primitive additive character `ψ`, and a prime `I` of `R` over
`Q`. -/
private theorem quartic_reciprocity_prime_inert_of_comap {π : 𝓞 K} (hπ : IsPrimaryGaussian π)
    {P : Ideal (𝓞 K)} [P.IsMaximal] (hP : P = span {π})
    {Q : Ideal (𝓞 K)} [hQmax : Q.IsMaximal] {q : ℕ} (hq : q.Prime) (hq3 : q % 4 = 3)
    (hQ : Q = span {(q : 𝓞 K)}) (hqP' : Ideal.Quotient.mk P (q : 𝓞 K) ≠ 0)
    (hcop : (absNorm P).Coprime q) {τ : 𝓞 K →+* 𝓞 K} (hσ : ∀ x : 𝓞 K, x ^ 4 = 1 → τ x = x ^ 3)
    {R : Type*} [CommRing R] [IsDomain R] {f : 𝓞 K →+* R} (hf : Function.Injective f)
    {ψ : AddChar (𝓞 K ⧸ P) R} (hψ : ψ.IsPrimitive) (I : Ideal R) [I.IsMaximal]
    (hIQ : comap f I = Q) :
    powerResidueSymbol P 4 (Ideal.Quotient.mk P (-(q : 𝓞 K))) =
      powerResidueSymbol Q 4 (Ideal.Quotient.mk Q π) := by
  let _ := Ideal.Quotient.field P
  let _ := Fintype.ofFinite (𝓞 K ⧸ P)
  have hP4 : (absNorm P).Coprime 4 := hP ▸ hπ.absNorm_span_singleton_coprime_four
  have hQ4 : (absNorm Q).Coprime 4 := hQ ▸ absNorm_span_natCast_four (K := K) q ▸
    Nat.Coprime.pow_left 2 (Nat.Coprime.pow_right 2
      (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr (by omega))))
  let ρ := quotientMap I f hIQ.ge
  have : CharP (𝓞 K ⧸ Q) q := (CharP.charP_iff_prime_eq_zero hq).mpr <| by
    rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem, hQ]
    exact mem_span_singleton_self _
  have : CharP (R ⧸ I) q := CharP.of_ringHom_of_ne_zero ρ q hq.ne_zero
  have h1 := gaussSum_pow_succ_eq_at_inert hP4 hq hq3 hqP' hf hψ I
  have hg4 := gaussSum_powerResidueSymbol_four_pow_four_eq_pow_three_mul (f := f) (σ := τ) hP hπ
    hσ hf hψ
  have hpow : (Ideal.Quotient.mk I (gaussSum ((powerResidueSymbol P 4).ringHomComp f) ψ)) ^
      (q + 1) = ρ (Ideal.Quotient.mk Q ((π ^ 3 * τ π) ^ ((q + 1) / 4))) := by
    rw [quotientMap_mk, map_pow, map_pow, ← hg4, map_pow, ← pow_mul,
      show 4 * ((q + 1) / 4) = q + 1 by omega]
  have hNP0 : Ideal.Quotient.mk Q (absNorm P : 𝓞 K) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact natCast_notMem_of_coprime_absNorm hQmax.ne_top
      (by rw [hQ, absNorm_span_natCast_four]; exact hcop.pow_right 2)
  have hmk : Ideal.Quotient.mk Q (powerResidueSymbol Q 4 (Ideal.Quotient.mk Q π) * absNorm P) =
      Ideal.Quotient.mk Q (powerResidueSymbol P 4 (Ideal.Quotient.mk P (-(q : 𝓞 K))) *
        absNorm P) := by
    have hρ : Function.Injective ρ := quotientMap_injective' hIQ.le
    apply hρ
    conv_lhs => rw [hP]
    rw [← mk_pow_three_mul_conj_pow_eq_at_inert (σ := τ) hσ hq hq3 (hP ▸ hcop) hQ, ← hpow, h1,
      quotientMap_mk]
  rw [map_mul, map_mul] at hmk
  have hπQ : Ideal.Quotient.mk Q π ≠ 0 := fun h ↦ hNP0 <| by
    rw [hP, ← Int.cast_natCast, RingOfIntegers.natCast_absNorm_span_singleton_of_four,
      intCast_norm_eq_mul_of_four (σ := τ) hσ, map_mul, h, zero_mul]
  exact eq_of_pow_eq_one_of_mk_eq hQmax.ne_top hQ4
    (powerResidueSymbol_pow_eq_one hP4 (by simpa using hqP'))
    (powerResidueSymbol_pow_eq_one hQ4 hπQ) (mul_right_cancel₀ hNP0 hmk.symm)

/-- Quartic reciprocity between a primary prime `π` and an inert rational prime `q ≡ 3 (mod 4)`
not in `π 𝓞 K`: `(-q / π)_4 = (π / q)_4`. -/
private theorem quartic_reciprocity_prime_inert {π : 𝓞 K} (hp : Prime π)
    (hπ : IsPrimaryGaussian π) {q : ℕ} (hq : q.Prime) (hq3 : q % 4 = 3)
    (hqP : (q : 𝓞 K) ∉ span {π}) :
    powerResidueSymbolIdeal (span {π}) 4 (Ideal.Quotient.mk _ (-(q : 𝓞 K))) =
      powerResidueSymbolIdeal (span {(q : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) := by
  set P : Ideal (𝓞 K) := span {π}
  set Q : Ideal (𝓞 K) := span {(q : 𝓞 K)}
  have : P.IsMaximal := ((span_singleton_prime hp.ne_zero).mpr hp).isMaximal
    (by simpa using hp.ne_zero)
  have : Q.IsMaximal := isMaximal_span_natCast_of_mod_four_eq_three hq hq3
  let _ := Ideal.Quotient.field P
  have hqP' : Ideal.Quotient.mk P (q : 𝓞 K) ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hcop : (absNorm P).Coprime q := absNorm_coprime_of_isCoprime_span_natCast
    (isCoprime_iff_sup_eq.mpr ((sup_comm _ _).trans (Ideal.Quotient.isUnit_mk_iff.mp hqP'.isUnit)))
  obtain ⟨σ₀, _, hσ⟩ := exists_gal_apply_eq_pow_three_of_four (K := K)
  let τ : 𝓞 K →+* 𝓞 K := (MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) σ₀ : 𝓞 K →+* 𝓞 K)
  let f : 𝓞 K →+* integralClosure ℤ ℂ :=
    (Classical.arbitrary (K →+* ℂ)).toIntAlgHom.mapIntegralClosure.toRingHom
  have hf : Function.Injective f := AlgHom.mapIntegralClosure_injective
    (f := (Classical.arbitrary (K →+* ℂ)).toIntAlgHom) (RingHom.injective _)
  obtain ⟨ψ, hψ⟩ := exists_primitive_addChar_integralClosure (𝓞 K ⧸ P)
  let _ := f.toAlgebra
  have : IsScalarTower ℤ (𝓞 K) (integralClosure ℤ ℂ) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  have : Algebra.IsIntegral (𝓞 K) (integralClosure ℤ ℂ) :=
    ⟨fun x ↦ (integralClosure.isIntegral x).tower_top⟩
  obtain ⟨I, _, hIQ⟩ := exists_ideal_over_maximal_of_isIntegral Q
    (((RingHom.injective_iff_ker_eq_bot _).mp hf).trans_le bot_le)
  rw [powerResidueSymbolIdeal_of_isMaximal, powerResidueSymbolIdeal_of_isMaximal]
  exact quartic_reciprocity_prime_inert_of_comap hπ rfl hq hq3 rfl hqP' hcop (τ := τ) hσ hf hψ I
    hIQ

/-- Evaluating `(π_I g) ^ (q - 1)` via the Gauss-sum Frobenius congruence at a split prime
`q ≡ 1 (mod 4)` gives `(q / P)_4 ^ 3` modulo `I`. -/
private theorem gaussSum_pow_pred_eq_at_split_factor {P : Ideal (𝓞 K)} [P.IsMaximal]
    [Fintype (𝓞 K ⧸ P)] (hP4 : (absNorm P).Coprime 4) {q : ℕ} (hq : q.Prime) (hq1 : q % 4 = 1)
    (hqP : Ideal.Quotient.mk P (q : 𝓞 K) ≠ 0) {R : Type*} [CommRing R] {f : 𝓞 K →+* R}
    {ψ : AddChar (𝓞 K ⧸ P) R} {I : Ideal R} [I.IsMaximal] [CharP (R ⧸ I) q]
    (hg0 : Ideal.Quotient.mk I (gaussSum ((powerResidueSymbol P 4).ringHomComp f) ψ) ≠ 0) :
    (Ideal.Quotient.mk I (gaussSum ((powerResidueSymbol P 4).ringHomComp f) ψ)) ^ (q - 1) =
      Ideal.Quotient.mk I (f (powerResidueSymbol P 4 (Ideal.Quotient.mk P (q : 𝓞 K)) ^ 3)) := by
  let _ := Ideal.Quotient.field P
  let _ := Ideal.Quotient.field I
  have : Fact q.Prime := ⟨hq⟩
  let χ := (powerResidueSymbol P 4).ringHomComp f
  let πI := Ideal.Quotient.mk I
  have hχq : χ.ringHomComp πI ^ q ^ 1 = χ.ringHomComp πI := by
    rw [pow_one, MulChar.ringHomComp_pow, MulChar.ringHomComp_pow,
      powerResidueSymbol_pow_eq_self ⟨(q - 1) / 4, by omega⟩ hq.pos]
  have hfrob := gaussSum_pow_char_pow hχq (πI.toMonoidHom.compAddChar ψ)
    (by rw [pow_one, ← map_natCast (Ideal.Quotient.mk P)]; exact hqP.isUnit)
  have hg_eq : gaussSum (χ.ringHomComp πI) (πI.toMonoidHom.compAddChar ψ) =
      πI (gaussSum χ ψ) := by
    simp only [gaussSum, map_sum, map_mul, MulChar.ringHomComp_apply]; rfl
  have hinv : (χ.ringHomComp πI)⁻¹ ((q : 𝓞 K ⧸ P) ^ 1) =
      πI (f (powerResidueSymbol P 4 (Ideal.Quotient.mk P (q : 𝓞 K)) ^ 3)) := by
    have h4 : powerResidueSymbol P 4 ^ 4 = 1 := by
      have h := pow_orderOf_eq_one (powerResidueSymbol P 4)
      rwa [orderOf_powerResidueSymbol hP4] at h
    have hinv_eq : (powerResidueSymbol P 4)⁻¹ = powerResidueSymbol P 4 ^ 3 :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_succ', h4])
    rw [pow_one, MulChar.ringHomComp_inv, MulChar.ringHomComp_inv, hinv_eq,
      MulChar.ringHomComp_apply, MulChar.ringHomComp_apply, MulChar.pow_apply' _ (by decide),
      map_natCast (Ideal.Quotient.mk P)]
  rw [hg_eq, pow_one, hinv, ← pow_sub_one_mul hq.ne_zero] at hfrob
  exact mul_right_cancel₀ hg0 hfrob

/-- `(q / P)_4 ^ 3 = (π ^ 3 σ π / L)_4` at a split prime factor `L` of `q ≡ 1 (mod 4)` given a
maximal ideal `I` of `R` lying over `L`. -/
private theorem powerResidueSymbol_pow_three_eq_at_split_factor_of_comap {π : 𝓞 K}
    (hπ : IsPrimaryGaussian π) {P : Ideal (𝓞 K)} [P.IsMaximal]
    (hP : P = span {π}) {σ : 𝓞 K →+* 𝓞 K} (hσ : ∀ x : 𝓞 K, x ^ 4 = 1 → σ x = x ^ 3)
    {q : ℕ} (hq : q.Prime) (hq1 : q % 4 = 1) (hqP : Ideal.Quotient.mk P (q : 𝓞 K) ≠ 0)
    (hcop : (absNorm P).Coprime q) (L : Ideal (𝓞 K)) [L.IsMaximal] (hNL : absNorm L = q)
    (hqL : (q : 𝓞 K) ∈ L) {R : Type*} [CommRing R] [IsDomain R] {f : 𝓞 K →+* R}
    (hf : Function.Injective f) {ψ : AddChar (𝓞 K ⧸ P) R} (hψ : ψ.IsPrimitive) (I : Ideal R)
    [I.IsMaximal] (hIL : comap f I = L) :
    powerResidueSymbol P 4 (Ideal.Quotient.mk P (q : 𝓞 K)) ^ 3 =
      powerResidueSymbol L 4 (Ideal.Quotient.mk L (π ^ 3 * σ π)) := by
  let _ := Ideal.Quotient.field P
  let _ := Fintype.ofFinite (𝓞 K ⧸ P)
  have hP4 : (absNorm P).Coprime 4 := hP ▸ hπ.absNorm_span_singleton_coprime_four
  have hL4 : (absNorm L).Coprime 4 :=
    hNL ▸ Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr (by omega)))
  let ρ := quotientMap I f hIL.ge
  have : CharP (𝓞 K ⧸ L) q := (CharP.charP_iff_prime_eq_zero hq).mpr <| by
    rwa [← map_natCast (Ideal.Quotient.mk L), Ideal.Quotient.eq_zero_iff_mem]
  have : CharP (R ⧸ I) q := CharP.of_ringHom_of_ne_zero ρ q hq.ne_zero
  let χ := (powerResidueSymbol P 4).ringHomComp f
  let πI := Ideal.Quotient.mk I
  let g := gaussSum χ ψ
  have hord : orderOf χ = 4 := by
    rw [MulChar.orderOf_ringHomComp hf, orderOf_powerResidueSymbol hP4]
  have hχne : χ ≠ 1 := by rw [← orderOf_eq_one_iff.ne, hord]; decide
  have hg0 : πI g ≠ 0 := fun h0 ↦ by
    have hcard := congrArg πI (gaussSum_mul_gaussSum_eq_card hχne hψ)
    rw [map_mul, h0, zero_mul, ← Nat.card_eq_fintype_card, ← absNorm_eq_natCard, eq_comm,
      ← map_natCast f, Ideal.Quotient.eq_zero_iff_mem, ← mem_comap, hIL] at hcard
    exact natCast_notMem_of_coprime_absNorm ‹L.IsMaximal›.ne_top (hNL ▸ hcop) hcard
  have hgq := gaussSum_pow_pred_eq_at_split_factor hP4 hq hq1 hqP hg0
  have hg4 := gaussSum_powerResidueSymbol_four_pow_four_eq_pow_three_mul (f := f) hP hπ hσ hf hψ
  have hpow : (πI g) ^ (q - 1) =
      ρ (Ideal.Quotient.mk L ((π ^ 3 * σ π) ^ ((absNorm L - 1) / 4))) := by
    rw [quotientMap_mk, map_pow, map_pow, ← hg4, map_pow, ← pow_mul, hNL,
      show 4 * ((q - 1) / 4) = q - 1 by omega]
  have hmemL : Ideal.Quotient.mk L (π ^ 3 * σ π) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, ← hIL, mem_comap, ← Ideal.Quotient.eq_zero_iff_mem,
      ← hg4, map_pow]
    exact pow_ne_zero 4 hg0
  have hmk : Ideal.Quotient.mk L (powerResidueSymbol P 4 (Ideal.Quotient.mk P (q : 𝓞 K)) ^ 3) =
      Ideal.Quotient.mk L (powerResidueSymbol L 4 (Ideal.Quotient.mk L (π ^ 3 * σ π))) := by
    have hρ : Function.Injective ρ := quotientMap_injective' hIL.le
    apply hρ
    rw [mk_powerResidueSymbol hL4 hmemL, ← map_pow (Ideal.Quotient.mk L), ← hpow, hgq,
      quotientMap_mk]
  exact eq_of_pow_eq_one_of_mk_eq ‹L.IsMaximal›.ne_top hL4
    (by rw [← pow_mul, mul_comm, pow_mul, powerResidueSymbol_pow_eq_one hP4 hqP, one_pow])
    (powerResidueSymbol_pow_eq_one hL4 hmemL) hmk

/-- At a split prime factor `L` of `q ≡ 1 (mod 4)` with `N L = q`, comparing `(π_I g) ^ (q - 1)`
from Frobenius with `g ^ 4 = π ^ 3 σ π` yields `(q / P)_4 ^ 3 = (π ^ 3 σ π / L)_4`. -/
private theorem powerResidueSymbol_pow_three_eq_at_split_factor {π : 𝓞 K}
    (hπ : IsPrimaryGaussian π) {P : Ideal (𝓞 K)} [P.IsMaximal] (hP : P = span {π})
    {σ : 𝓞 K →+* 𝓞 K} (hσ : ∀ x : 𝓞 K, x ^ 4 = 1 → σ x = x ^ 3) {q : ℕ} (hq : q.Prime)
    (hq1 : q % 4 = 1) (hqP : Ideal.Quotient.mk P (q : 𝓞 K) ≠ 0) (hcop : (absNorm P).Coprime q)
    (L : Ideal (𝓞 K)) [L.IsMaximal] (hNL : absNorm L = q) (hqL : (q : 𝓞 K) ∈ L) :
    powerResidueSymbol P 4 (Ideal.Quotient.mk P (q : 𝓞 K)) ^ 3 =
      powerResidueSymbol L 4 (Ideal.Quotient.mk L (π ^ 3 * σ π)) := by
  let _ := Ideal.Quotient.field P
  let f : 𝓞 K →+* integralClosure ℤ ℂ :=
    (Classical.arbitrary (K →+* ℂ)).toIntAlgHom.mapIntegralClosure.toRingHom
  have hf : Function.Injective f := AlgHom.mapIntegralClosure_injective
    (f := (Classical.arbitrary (K →+* ℂ)).toIntAlgHom) (RingHom.injective _)
  obtain ⟨ψ, hψ⟩ := exists_primitive_addChar_integralClosure (𝓞 K ⧸ P)
  let _ := f.toAlgebra
  have : IsScalarTower ℤ (𝓞 K) (integralClosure ℤ ℂ) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  have : Algebra.IsIntegral (𝓞 K) (integralClosure ℤ ℂ) :=
    ⟨fun x ↦ (integralClosure.isIntegral x).tower_top⟩
  obtain ⟨I, _, hIL⟩ := exists_ideal_over_maximal_of_isIntegral L
    (((RingHom.injective_iff_ker_eq_bot _).mp hf).trans_le bot_le)
  exact powerResidueSymbol_pow_three_eq_at_split_factor_of_comap hπ hP hσ hq hq1 hqP hcop L hNL
    hqL hf hψ I hIL

/-- At a split prime `q = τ β · β` with `L = β 𝓞 K` of norm `q`, Galois equivariance identifies
`(π ^ 3 τ π / L)_4` with `(π / q)_4 ^ 3` and shows that `π` is a unit modulo `q 𝓞 K`. -/
private theorem symbol_pow_three_mul_conj_at_split {π β : 𝓞 K} (hβ : β ≠ 0) {q : ℕ}
    (hqodd : Odd q) (hcop : (absNorm (span {π})).Coprime q) {τ : 𝓞 K ≃+* 𝓞 K}
    (hτ_inv : ∀ x, τ (τ x) = x) (hτ4 : ∀ x : 𝓞 K, x ^ 4 = 1 → τ x = x ^ 3)
    (hqβ : (q : 𝓞 K) = τ β * β) {L : Ideal (𝓞 K)} [L.IsMaximal] (hL : L = span {β})
    (hNL : absNorm L = q) :
    powerResidueSymbol L 4 (Ideal.Quotient.mk L (π ^ 3 * τ π)) =
        powerResidueSymbolIdeal (span {(q : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) ^ 3 ∧
      IsUnit (Ideal.Quotient.mk (span {(q : 𝓞 K)}) π) := by
  have : (L.map τ).IsMaximal := map_isMaximal_of_equiv τ
  have hL4 : (absNorm L).Coprime 4 :=
    hNL ▸ Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hqodd)
  have hNP : (absNorm (span {π}) : 𝓞 K) = π * τ π := by
    rw [← Int.cast_natCast, RingOfIntegers.natCast_absNorm_span_singleton_of_four,
      intCast_norm_eq_mul_of_four (σ := (τ : 𝓞 K →+* 𝓞 K)) hτ4]
    rfl
  have hτπL : Ideal.Quotient.mk L (τ π) ≠ 0 := fun h ↦
    natCast_notMem_of_coprime_absNorm ‹L.IsMaximal›.ne_top (hNL ▸ hcop)
      (hNP ▸ L.mul_mem_left π (Ideal.Quotient.eq_zero_iff_mem.mp h))
  have hgal := map_powerResidueSymbol (n := 4) L τ (τ π)
  rw [hτ_inv, hτ4 _ (powerResidueSymbol_pow_eq_one hL4 hτπL)] at hgal
  have hconj : powerResidueSymbol L 4 (Ideal.Quotient.mk L (τ π)) =
      powerResidueSymbol (L.map τ) 4 (Ideal.Quotient.mk (L.map τ) π) ^ 3 := by
    rw [← hgal, ← pow_mul]
    have h4 := powerResidueSymbol_pow_eq_one hL4 hτπL
    linear_combination -(powerResidueSymbol L 4 (Ideal.Quotient.mk L (τ π)) ^ 5 +
      powerResidueSymbol L 4 (Ideal.Quotient.mk L (τ π))) * h4
  have hspan : span {(q : 𝓞 K)} = L.map τ * L := by
    rw [hqβ, hL, ← span_singleton_mul_span_singleton, map_span, Set.image_singleton]
  have hmul : powerResidueSymbolIdeal (span {(q : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) =
      powerResidueSymbol (L.map τ) 4 (Ideal.Quotient.mk (L.map τ) π) *
        powerResidueSymbol L 4 (Ideal.Quotient.mk L π) := by
    rw [hspan, powerResidueSymbolIdeal_mul_right (Ring.ne_bot_of_isMaximal_of_not_isField ‹_›
      (RingOfIntegers.not_isField K)) (by simpa [hL] using hβ),
      powerResidueSymbolIdeal_of_isMaximal, powerResidueSymbolIdeal_of_isMaximal]
  refine ⟨by rw [map_mul, map_mul, map_pow, map_pow, hconj, mul_comm, ← mul_pow, ← hmul], ?_⟩
  rw [Ideal.Quotient.isUnit_mk_iff, sup_comm, ← isCoprime_iff_sup_eq, hspan,
    IsCoprime.mul_left_iff]
  refine ⟨?_, ?_⟩
  · rw [isCoprime_iff_sup_eq, sup_comm, ← Ideal.Quotient.isUnit_mk_iff]
    let _ := Ideal.Quotient.field (L.map τ)
    refine Ne.isUnit fun h0 ↦ ?_
    obtain ⟨y, hy, hyx⟩ := (mem_map_iff_of_surjective τ τ.surjective).mp
      (Ideal.Quotient.eq_zero_iff_mem.mp h0)
    exact hτπL (Ideal.Quotient.eq_zero_iff_mem.mpr ((by simpa [hτ_inv] using congrArg τ hyx) ▸ hy))
  · rw [isCoprime_iff_sup_eq, sup_comm, ← Ideal.Quotient.isUnit_mk_iff]
    let _ := Ideal.Quotient.field L
    exact Ne.isUnit fun h0 ↦ natCast_notMem_of_coprime_absNorm ‹L.IsMaximal›.ne_top (hNL ▸ hcop)
      (hNP ▸ L.mul_mem_right (τ π) (Ideal.Quotient.eq_zero_iff_mem.mp h0))

/-- Quartic reciprocity between a primary prime `π` and a split rational prime `q ≡ 1 (mod 4)`
not in `π 𝓞 K`: `(q / π)_4 = (π / q)_4`. -/
private theorem quartic_reciprocity_prime_split {π : 𝓞 K} (hp : Prime π)
    (hπ : IsPrimaryGaussian π) {q : ℕ} (hq : q.Prime) (hq1 : q % 4 = 1)
    (hqP : (q : 𝓞 K) ∉ span {π}) :
    powerResidueSymbolIdeal (span {π}) 4 (Ideal.Quotient.mk _ (q : 𝓞 K)) =
      powerResidueSymbolIdeal (span {(q : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) := by
  set P : Ideal (𝓞 K) := span {π}
  have : P.IsMaximal := ((span_singleton_prime hp.ne_zero).mpr hp).isMaximal
    (by simpa using hp.ne_zero)
  let _ := Ideal.Quotient.field P
  have hqP' : Ideal.Quotient.mk P (q : 𝓞 K) ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hcop : (absNorm P).Coprime q := absNorm_coprime_of_isCoprime_span_natCast
    (isCoprime_iff_sup_eq.mpr ((sup_comm _ _).trans (Ideal.Quotient.isUnit_mk_iff.mp hqP'.isUnit)))
  obtain ⟨σ₀, hσ₀, hτ⟩ := exists_gal_apply_eq_pow_three_of_four (K := K)
  let τ := MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) σ₀
  have hτ_inv (x : 𝓞 K) : τ (τ x) = x := by
    have hsq : σ₀ * σ₀ = 1 := (IsCyclotomicExtension.Rat.galEquivZMod 4 K).injective
      (by rw [map_mul, hσ₀, neg_mul_neg, one_mul, map_one])
    rw [MulSemiringAction.toRingEquiv_apply_apply, MulSemiringAction.toRingEquiv_apply_apply,
      ← mul_smul, hsq, one_smul]
  obtain ⟨β, hβ, hqβ, hNβ⟩ := exists_natCast_eq_mul_of_mod_four_ne_three
    (σ := (τ : 𝓞 K →+* 𝓞 K)) hτ hq (by omega)
  simp only [RingEquiv.coe_toRingHom] at hqβ
  set L : Ideal (𝓞 K) := span {β}
  have : L.IsMaximal :=
    (isPrime_of_irreducible_absNorm (hNβ ▸ hq)).isMaximal (by simpa [L] using hβ)
  have hqL : (q : 𝓞 K) ∈ L := hqβ ▸ mem_span_singleton.mpr ⟨τ β, mul_comm _ _⟩
  have h3 := powerResidueSymbol_pow_three_eq_at_split_factor hπ rfl (σ := (τ : 𝓞 K →+* 𝓞 K)) hτ
    hq hq1 hqP' hcop L hNβ hqL
  simp only [RingEquiv.coe_toRingHom] at h3
  obtain ⟨hsplit, hπq_unit⟩ := symbol_pow_three_mul_conj_at_split hβ
    (Nat.odd_iff.mpr (by omega)) hcop hτ_inv hτ hqβ rfl hNβ
  rw [hsplit, ← powerResidueSymbolIdeal_of_isMaximal] at h3
  have hA4 : powerResidueSymbolIdeal P 4 (Ideal.Quotient.mk P (q : 𝓞 K)) ^ 4 = 1 :=
    powerResidueSymbolIdeal_pow_eq_one hqP'.isUnit
  have hB4 : powerResidueSymbolIdeal (span {(q : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) ^ 4 = 1 :=
    powerResidueSymbolIdeal_pow_eq_one hπq_unit
  set A := powerResidueSymbolIdeal P 4 (Ideal.Quotient.mk P (q : 𝓞 K))
  set B := powerResidueSymbolIdeal (span {(q : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π)
  have hcube := congrArg (· ^ 3) h3
  linear_combination hcube - (A ^ 5 + A) * hA4 + (B ^ 5 + B) * hB4

/-- Quartic reciprocity between a primary prime `π` and an odd prime `q : ℕ`:
`((q χ₄(q)) / π)_4 = (π / q)_4`, including when `π ∣ q` (both sides vanish). -/
private theorem quartic_reciprocity_prime_nat {π : 𝓞 K} (hp : Prime π)
    (hπ : IsPrimaryGaussian π) {q : ℕ} (hq : q.Prime) (hqodd : Odd q) :
    powerResidueSymbolIdeal (span {π}) 4
        (Ideal.Quotient.mk _ (((q : ℤ) * ZMod.χ₄ q : ℤ) : 𝓞 K)) =
      powerResidueSymbolIdeal (span {(q : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) := by
  by_cases hqP : (q : 𝓞 K) ∈ span {π}
  · have hχ_mul : (ZMod.χ₄ q : 𝓞 K) * (ZMod.χ₄ q : 𝓞 K) = 1 := by
      exact_mod_cast ZMod.χ₄_natCast_mul_self hqodd
    have htop : span {(ZMod.χ₄ q : 𝓞 K)} = ⊤ :=
      span_singleton_eq_top.mpr (IsUnit.of_mul_eq_one _ hχ_mul)
    have hspan : span {(((q : ℤ) * ZMod.χ₄ q : ℤ) : 𝓞 K)} = span {(q : 𝓞 K)} := by
      rw [Int.cast_mul, Int.cast_natCast, ← span_singleton_mul_span_singleton, htop, mul_top]
    have hncop : ¬IsCoprime (span {π}) (span {(q : 𝓞 K)}) := by
      rw [isCoprime_iff_sup_eq, sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hqP)]
      exact ((span_singleton_prime hp.ne_zero).mpr hp).ne_top
    rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr (hspan ▸ mt IsCoprime.symm hncop),
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hncop]
  rcases (show q % 4 = 1 ∨ q % 4 = 3 by have := Nat.odd_iff.mp hqodd; omega) with hq1 | hq3
  · rw [ZMod.χ₄_nat_one_mod_four hq1, mul_one, Int.cast_natCast]
    exact quartic_reciprocity_prime_split hp hπ hq hq1 hqP
  · rw [ZMod.χ₄_nat_three_mod_four hq3, mul_neg_one, Int.cast_neg, Int.cast_natCast]
    exact quartic_reciprocity_prime_inert hp hπ hq hq3 hqP

/-- Quartic reciprocity between a primary prime `π` and any odd integer `m`:
`((m χ₄(m)) / π)_4 = (π / m)_4`. -/
private theorem quartic_reciprocity_prime_int {π : 𝓞 K} (hp : Prime π)
    (hπ : IsPrimaryGaussian π) {m : ℤ} (hm : Odd m) :
    powerResidueSymbolIdeal (span {π}) 4
        (Ideal.Quotient.mk _ ((m * ZMod.χ₄ m : ℤ) : 𝓞 K)) =
      powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) := by
  induction m using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact (Int.not_odd_zero hm).elim
  | h₂ m hunit =>
    have htop : span {(m : 𝓞 K)} = ⊤ :=
      span_singleton_eq_top.mpr (hunit.map (Int.castRingHom (𝓞 K)))
    rw [htop, powerResidueSymbolIdeal_top]
    rcases Int.isUnit_iff.mp hunit with rfl | rfl
    · rw [show ((1 : ℤ) * ZMod.χ₄ (1 : ℤ) : ℤ) = 1 by decide, Int.cast_one, map_one, map_one]
    · rw [show ((-1 : ℤ) * ZMod.χ₄ (-1 : ℤ) : ℤ) = 1 by decide, Int.cast_one, map_one, map_one]
  | h₃ m p hm0 hp_int ih =>
    obtain ⟨hpodd, hmodd⟩ := Int.odd_mul.mp hm
    have hmul : ((p * m) * ZMod.χ₄ (p * m : ℤ) : ℤ) =
        (p * ZMod.χ₄ (p : ℤ)) * (m * ZMod.χ₄ (m : ℤ)) := by
      rw [Int.cast_mul, map_mul]; ring
    have hq := Int.prime_iff_natAbs_prime.mp hp_int
    have hqodd : Odd p.natAbs := Int.natAbs_odd.mpr hpodd
    have hp_rec : powerResidueSymbolIdeal (span {π}) 4
        (Ideal.Quotient.mk _ ((p * ZMod.χ₄ (p : ℤ) : ℤ) : 𝓞 K)) =
        powerResidueSymbolIdeal (span {(p : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) := by
      rcases Int.natAbs_eq p with h | h
      · rw [h, Int.cast_natCast, Int.cast_natCast]
        exact quartic_reciprocity_prime_nat hp hπ hq hqodd
      · have hneg : ((-↑p.natAbs : ℤ) * ZMod.χ₄ (-↑p.natAbs : ℤ)) =
            (p.natAbs : ℤ) * ZMod.χ₄ (p.natAbs : ZMod 4) := by
          rw [Int.cast_neg, Int.cast_natCast, ZMod.χ₄_neg]; ring
        rw [h, hneg, Int.cast_neg, Int.cast_natCast, span_singleton_neg]
        exact quartic_reciprocity_prime_nat hp hπ hq hqodd
    rw [hmul, Int.cast_mul, map_mul, map_mul, hp_rec, ih hmodd, Int.cast_mul,
      ← span_singleton_mul_span_singleton,
      powerResidueSymbolIdeal_mul_right (by simpa using hp_int.ne_zero) (by simpa using hm0)]

/-- **Quartic reciprocity between a primary Gaussian integer and an odd rational integer.**
Let `K = ℚ(i)`, so that `𝓞 K = ℤ[i]`. For every primary element `x` of `𝓞 K` and every odd
integer `m`, `((m χ₄(m)) / x)_4 = (x / m)_4`, the quartic residue symbols being taken at the
ideals `x 𝓞 K` and `m 𝓞 K`. Both `x` and `m` may be composite or units, `m` may be negative, and
when `x` and `m` are not coprime both symbols vanish. -/
theorem IsPrimaryGaussian.quartic_reciprocity_intCast_mul_χ₄ {x : 𝓞 K}
    (hx : IsPrimaryGaussian x) {m : ℤ} (hm : Odd m) :
    powerResidueSymbolIdeal (span {x}) 4
        (Ideal.Quotient.mk _ ((m * ZMod.χ₄ m : ℤ) : 𝓞 K)) =
      powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 (Ideal.Quotient.mk _ x) := by
  obtain ⟨s, hs, rfl⟩ := hx.exists_multiset_prod_eq
  clear hx
  induction s using Multiset.induction_on with
  | empty =>
    rw [Multiset.prod_zero, span_singleton_one, powerResidueSymbolIdeal_top, map_one, map_one]
  | cons π s ih =>
    obtain ⟨hp, hπ⟩ := hs π (Multiset.mem_cons_self π s)
    have hs' : ∀ q ∈ s, Prime q ∧ IsPrimaryGaussian q :=
      fun q hq ↦ hs q (Multiset.mem_cons_of_mem hq)
    have hs0 : s.prod ≠ 0 :=
      fun h0 ↦ (hs' 0 (Multiset.prod_eq_zero_iff.mp h0)).1.ne_zero rfl
    rw [Multiset.prod_cons, ← span_singleton_mul_span_singleton,
      powerResidueSymbolIdeal_mul_right (by simpa using hp.ne_zero) (by simpa using hs0),
      quartic_reciprocity_prime_int hp hπ hm, ih hs', map_mul, map_mul]

/-- **Quartic reciprocity between a primary Gaussian integer and an integer `a ≡ 1 (mod 4)`.**
Let `K = ℚ(i)`, so that `𝓞 K = ℤ[i]`. For every primary element `x` of `𝓞 K` and every integer
`a ≡ 1 (mod 4)`, `(a / x)_4 = (x / a)_4`, the symbols being taken at `x 𝓞 K` and `a 𝓞 K`. Both `x`
and `a` may be composite or units, `a` may be negative, and when `x` and `a` are not coprime both
symbols vanish. -/
theorem IsPrimaryGaussian.quartic_reciprocity_intCast {x : 𝓞 K}
    (hx : IsPrimaryGaussian x) {a : ℤ} (ha : a ≡ 1 [ZMOD 4]) :
    powerResidueSymbolIdeal (span {x}) 4 (Ideal.Quotient.mk _ (a : 𝓞 K)) =
      powerResidueSymbolIdeal (span {(a : 𝓞 K)}) 4 (Ideal.Quotient.mk _ x) := by
  have hodd : Odd a := Int.odd_iff.mpr (by simp only [Int.ModEq] at ha; omega)
  have hχ : ZMod.χ₄ a = 1 := ZMod.χ₄_int_one_mod_four (by simp only [Int.ModEq] at ha; omega)
  simpa [hχ] using hx.quartic_reciprocity_intCast_mul_χ₄ hodd

/-- **Quartic reciprocity between a primary Gaussian integer and an odd natural number.**
Let `K = ℚ(i)`, so that `𝓞 K = ℤ[i]`. For every primary element `x` of `𝓞 K` and every odd
natural number `q`, `((-1) ^ ((q - 1) / 2) * q / x)_4 = (x / q)_4`, the symbols being taken at
`x 𝓞 K` and `q 𝓞 K`. In particular this holds when `q` is an odd prime and `x` is a primary prime;
when `x` and `q` are not coprime both symbols vanish. -/
theorem IsPrimaryGaussian.quartic_reciprocity_natCast {x : 𝓞 K}
    (hx : IsPrimaryGaussian x) {q : ℕ} (hq : Odd q) :
    powerResidueSymbolIdeal (span {x}) 4
        (Ideal.Quotient.mk _ ((-1) ^ ((q - 1) / 2) * (q : 𝓞 K))) =
      powerResidueSymbolIdeal (span {(q : 𝓞 K)}) 4 (Ideal.Quotient.mk _ x) := by
  have hq_int : Odd (q : ℤ) := by obtain ⟨k, rfl⟩ := hq; exact ⟨k, by push_cast; ring⟩
  have h := hx.quartic_reciprocity_intCast_mul_χ₄ hq_int
  have hχ : ZMod.χ₄ (q : ZMod 4) = (-1) ^ ((q - 1) / 2) := by
    rw [ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hq)]
    obtain ⟨k, rfl⟩ := hq
    congr 1
    omega
  rw [Int.cast_natCast, hχ, mul_comm, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast] at h
  exact h

end RationalReciprocity

/-! ### Primary elements with coprime coordinates -/

section CoprimeCoordinates

/-- A maximal ideal `𝔓` of `𝓞 K = ℤ[i]` not containing `2` cannot contain both
`(a - b i) (c + d i)` and `(a + b i) (c - d i)` when `gcd(a, b) = gcd(c, d) = 1` and `a + b i`,
`c + d i` generate coprime ideals. -/
private theorem not_mem_and_conj_mem_of_not_two_mem {ζ : K} (hζ : IsPrimitiveRoot ζ 4)
    {a b c d : ℤ} (hab : IsCoprime a b) (hcd : IsCoprime c d)
    (hcop : IsCoprime (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger})
      (span {(c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger}))
    {𝔓 : Ideal (𝓞 K)} (h𝔓 : 𝔓.IsMaximal) (h2_notMem : (2 : 𝓞 K) ∉ 𝔓)
    (hprod1 : ((a : 𝓞 K) - (b : 𝓞 K) * hζ.toInteger) *
      ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger) ∈ 𝔓)
    (hprod2 : ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger) *
      ((c : 𝓞 K) - (d : 𝓞 K) * hζ.toInteger) ∈ 𝔓) : False := by
  have hsq : hζ.toInteger ^ 2 = -1 := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  obtain ⟨u₁, v₁, huv₁⟩ := hab
  have h2π₁ : ((u₁ : 𝓞 K) - (v₁ : 𝓞 K) * hζ.toInteger) * ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger) +
      ((u₁ : 𝓞 K) + (v₁ : 𝓞 K) * hζ.toInteger) * ((a : 𝓞 K) - (b : 𝓞 K) * hζ.toInteger) = 2 := by
    have huv₁' : (u₁ : 𝓞 K) * a + (v₁ : 𝓞 K) * b = 1 := by exact_mod_cast huv₁
    linear_combination 2 * huv₁' - 2 * (v₁ : 𝓞 K) * b * hsq
  obtain ⟨u₂, v₂, huv₂⟩ := hcd
  have h2π₂ : ((u₂ : 𝓞 K) - (v₂ : 𝓞 K) * hζ.toInteger) * ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger) +
      ((u₂ : 𝓞 K) + (v₂ : 𝓞 K) * hζ.toInteger) * ((c : 𝓞 K) - (d : 𝓞 K) * hζ.toInteger) = 2 := by
    have huv₂' : (u₂ : 𝓞 K) * c + (v₂ : 𝓞 K) * d = 1 := by exact_mod_cast huv₂
    linear_combination 2 * huv₂' - 2 * (v₂ : 𝓞 K) * d * hsq
  obtain ⟨α, β, hαβ⟩ := (isCoprime_span_singleton_iff _ _).mp hcop
  obtain ⟨σ₀, _, hτ⟩ := exists_gal_apply_eq_pow_three_of_four (K := K)
  let τ := MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) σ₀
  have hτi : τ hζ.toInteger = -hζ.toInteger := by
    rw [hτ hζ.toInteger hζ.toInteger_isPrimitiveRoot.pow_eq_one]
    linear_combination hζ.toInteger * hsq
  have hαβ' : τ α * ((a : 𝓞 K) - (b : 𝓞 K) * hζ.toInteger) +
      τ β * ((c : 𝓞 K) - (d : 𝓞 K) * hζ.toInteger) = 1 := by
    have h := congrArg τ hαβ
    simpa [map_add, map_mul, map_intCast, hτi, sub_eq_add_neg, mul_neg] using h
  rcases h𝔓.isPrime.mem_or_mem hprod1 with h₁' | h₂ <;>
    rcases h𝔓.isPrime.mem_or_mem hprod2 with h₁ | h₂'
  · exact h2_notMem (h2π₁ ▸ 𝔓.add_mem (𝔓.mul_mem_left _ h₁) (𝔓.mul_mem_left _ h₁'))
  · exact h𝔓.ne_top ((eq_top_iff_one _).mpr
      (hαβ' ▸ 𝔓.add_mem (𝔓.mul_mem_left _ h₁') (𝔓.mul_mem_left _ h₂')))
  · exact h𝔓.ne_top ((eq_top_iff_one _).mpr
      (hαβ ▸ 𝔓.add_mem (𝔓.mul_mem_left _ h₁) (𝔓.mul_mem_left _ h₂)))
  · exact h2_notMem (h2π₂ ▸ 𝔓.add_mem (𝔓.mul_mem_left _ h₂) (𝔓.mul_mem_left _ h₂'))

/-- If `π₁ = a + b i` and `π₂ = c + d i` are coprime primary elements with
`gcd(a, b) = gcd(c, d) = 1`, then `n = a d - b c` and `m = a c + b d` are coprime integers. -/
private theorem isCoprime_sub_add_of_isCoprime_coords {ζ : K} (hζ : IsPrimitiveRoot ζ 4)
    {a b c d : ℤ} (hπ₁ : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger))
    (hπ₂ : IsPrimaryGaussian ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger)) (hab : IsCoprime a b)
    (hcd : IsCoprime c d)
    (hcop : IsCoprime (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger})
      (span {(c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger})) :
    IsCoprime (a * d - b * c) (a * c + b * d) := by
  have hsq : hζ.toInteger ^ 2 = -1 := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  have hmod₁ := (hζ.isPrimaryGaussian_add_mul_iff).mp hπ₁
  have hmod₂ := (hζ.isPrimaryGaussian_add_mul_iff).mp hπ₂
  have hm_odd : Odd (a * c + b * d) := Odd.add_even
    ((Int.odd_iff.mpr (by simp only [Int.ModEq] at hmod₁; omega)).mul
      (Int.odd_iff.mpr (by simp only [Int.ModEq] at hmod₂; omega)))
    ((Int.even_iff.mpr (by simp only [Int.ModEq] at hmod₁; omega)).mul_right d)
  by_contra hncop
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd (mt Int.isCoprime_iff_gcd_eq_one.mpr hncop)
  have hpm : (p : ℤ) ∣ a * c + b * d :=
    (Int.natCast_dvd_natCast.mpr hpg).trans (Int.gcd_dvd_right _ _)
  have hpn : (p : ℤ) ∣ a * d - b * c :=
    (Int.natCast_dvd_natCast.mpr hpg).trans (Int.gcd_dvd_left _ _)
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact Int.not_even_iff_odd.mpr hm_odd (even_iff_two_dvd.mpr hpm)
  have hptop : span {(p : 𝓞 K)} ≠ ⊤ := fun htop ↦ by
    have hN := congrArg absNorm htop
    rw [absNorm_span_natCast_four, absNorm_top] at hN
    nlinarith [hp.one_lt]
  obtain ⟨𝔓, h𝔓, hp𝔓⟩ := exists_le_maximal (span {(p : 𝓞 K)}) hptop
  have hp_mem : (p : 𝓞 K) ∈ 𝔓 := hp𝔓 (mem_span_singleton_self _)
  have h2_notMem : (2 : 𝓞 K) ∉ 𝔓 := fun h2 ↦ by
    obtain ⟨u, v, huv⟩ := (Nat.prime_two.coprime_iff_not_dvd.mpr fun h ↦
      hp2 (((Nat.dvd_prime hp).mp h).resolve_left (by decide)).symm).isCoprime.map
      (Int.castRingHom (𝓞 K))
    exact h𝔓.ne_top ((eq_top_iff_one _).mpr (huv ▸ 𝔓.add_mem (𝔓.mul_mem_left u (by simpa using h2))
      (𝔓.mul_mem_left v (by simpa using hp_mem))))
  have hm_mem : ((a * c + b * d : ℤ) : 𝓞 K) ∈ 𝔓 := by
    obtain ⟨k, hk⟩ := hpm; rw [hk]; simpa [Int.cast_mul] using 𝔓.mul_mem_right (k : 𝓞 K) hp_mem
  have hn_mem : ((a * d - b * c : ℤ) : 𝓞 K) ∈ 𝔓 := by
    obtain ⟨k, hk⟩ := hpn; rw [hk]; simpa [Int.cast_mul] using 𝔓.mul_mem_right (k : 𝓞 K) hp_mem
  refine not_mem_and_conj_mem_of_not_two_mem hζ hab hcd hcop h𝔓 h2_notMem ?_ ?_
  · have h : ((a : 𝓞 K) - (b : 𝓞 K) * hζ.toInteger) * ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger) =
        ((a * c + b * d : ℤ) : 𝓞 K) + ((a * d - b * c : ℤ) : 𝓞 K) * hζ.toInteger := by
      push_cast; linear_combination -(b : 𝓞 K) * d * hsq
    exact h ▸ 𝔓.add_mem hm_mem (𝔓.mul_mem_right hζ.toInteger hn_mem)
  · have h : ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger) * ((c : 𝓞 K) - (d : 𝓞 K) * hζ.toInteger) =
        ((a * c + b * d : ℤ) : 𝓞 K) - ((a * d - b * c : ℤ) : 𝓞 K) * hζ.toInteger := by
      push_cast; linear_combination -(b : 𝓞 K) * d * hsq
    exact h ▸ 𝔓.sub_mem hm_mem (𝔓.mul_mem_right hζ.toInteger hn_mem)

/-- From `c π₁ ≡ a c + b d (mod π₂)` and `π₂ ≡ d i (mod c)`, `(i / c)_4 · (π₁ / π₂)_4 =
(χ₄(a) / π₂)_4 · (π₂ / (a c + b d))_4` for primary `π₁ = a + b i` and `π₂ = c + d i` with
`gcd(c, d) = 1`. -/
private theorem symbol_toInteger_mul_symbol_eq_at_primary {ζ : K} (hζ : IsPrimitiveRoot ζ 4)
    {a b c d : ℤ} (hπ₁ : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger))
    (hπ₂ : IsPrimaryGaussian ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger)) (hcd : IsCoprime c d) :
    let m : ℤ := a * c + b * d
    powerResidueSymbolIdeal (span {(c : 𝓞 K)}) 4 (Ideal.Quotient.mk _ hζ.toInteger) *
        powerResidueSymbolIdeal (span {(c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger}) 4
          (Ideal.Quotient.mk _ ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) =
      powerResidueSymbolIdeal (span {(c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger}) 4
          (Ideal.Quotient.mk _ (ZMod.χ₄ a : 𝓞 K)) *
        powerResidueSymbolIdeal (span {((m : ℤ) : 𝓞 K)}) 4
          (Ideal.Quotient.mk _ ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger)) := by
  intro m
  set π₁ : 𝓞 K := (a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger
  set π₂ : 𝓞 K := (c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger
  have hsq : hζ.toInteger ^ 2 = -1 := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  have hmod₁ := (hζ.isPrimaryGaussian_add_mul_iff).mp hπ₁
  have hmod₂ := (hζ.isPrimaryGaussian_add_mul_iff).mp hπ₂
  have hc_odd : Odd c := Int.odd_iff.mpr (by simp only [Int.ModEq] at hmod₂; omega)
  have hm_odd : Odd m := Odd.add_even
    ((Int.odd_iff.mpr (by simp only [Int.ModEq] at hmod₁; omega)).mul hc_odd)
    ((Int.even_iff.mpr (by simp only [Int.ModEq] at hmod₁; omega)).mul_right d)
  have hχm : ZMod.χ₄ (m : ZMod 4) = ZMod.χ₄ (a : ZMod 4) * ZMod.χ₄ (c : ZMod 4) := by
    have hbd4 : (4 : ℤ) ∣ b * d := mul_dvd_mul
      (by simp only [Int.ModEq] at hmod₁; omega : (2 : ℤ) ∣ b)
      (by simp only [Int.ModEq] at hmod₂; omega : (2 : ℤ) ∣ d)
    obtain ⟨k, hk⟩ := hbd4
    rw [show (m : ZMod 4) = (a : ZMod 4) * (c : ZMod 4) by
      simp [m, hk, show (4 : ZMod 4) = 0 by decide], map_mul]
  have hχ_sq {w : ℤ} (hw : Odd w) : ZMod.χ₄ (w : ZMod 4) * ZMod.χ₄ (w : ZMod 4) = 1 := by
    rcases (show w % 4 = 1 ∨ w % 4 = 3 by have := Int.odd_iff.mp hw; omega) with h1 | h3
    · rw [ZMod.χ₄_int_one_mod_four h1]; rfl
    · rw [ZMod.χ₄_int_three_mod_four h3]; rfl
  have hmk_m : Ideal.Quotient.mk (span {π₂}) ((c : 𝓞 K) * π₁) =
      Ideal.Quotient.mk (span {π₂}) (m : 𝓞 K) := by
    rw [Ideal.Quotient.eq, mem_span_singleton]
    refine ⟨(b : 𝓞 K) * hζ.toInteger, ?_⟩
    simp only [π₁, π₂, m]; push_cast; linear_combination -(b : 𝓞 K) * d * hsq
  have hrel := congrArg (powerResidueSymbolIdeal (span {π₂}) 4) hmk_m
  have hc_eq : (c : 𝓞 K) = (ZMod.χ₄ c : 𝓞 K) * ((c * ZMod.χ₄ c : ℤ) : 𝓞 K) := by
    exact_mod_cast (by linear_combination -c * hχ_sq hc_odd : c = ZMod.χ₄ c * (c * ZMod.χ₄ c))
  have hm_eq : (m : 𝓞 K) =
      (ZMod.χ₄ a : 𝓞 K) * (ZMod.χ₄ c : 𝓞 K) * ((m * ZMod.χ₄ m : ℤ) : 𝓞 K) := by
    exact_mod_cast (by rw [← hχm]; linear_combination -m * hχ_sq hm_odd :
      m = ZMod.χ₄ a * ZMod.χ₄ c * (m * ZMod.χ₄ m))
  have hπ₂_c : Ideal.Quotient.mk (span {(c : 𝓞 K)}) π₂ =
      Ideal.Quotient.mk (span {(c : 𝓞 K)}) ((d : 𝓞 K) * hζ.toInteger) :=
    Ideal.Quotient.eq.mpr (mem_span_singleton.mpr ⟨1, by simp [π₂]⟩)
  have hdc : powerResidueSymbolIdeal (span {(c : 𝓞 K)}) 4 (Ideal.Quotient.mk _ (d : 𝓞 K)) = 1 := by
    simpa using powerResidueSymbolIdeal_intCast_four (K := K) hcd.symm
  rw [map_mul, map_mul, hc_eq, map_mul, map_mul, hπ₂.quartic_reciprocity_intCast_mul_χ₄ hc_odd,
    hπ₂_c, map_mul, map_mul, hdc, one_mul, hm_eq, map_mul, map_mul, map_mul, map_mul,
    hπ₂.quartic_reciprocity_intCast_mul_χ₄ hm_odd] at hrel
  have hχc_mul : (ZMod.χ₄ c : 𝓞 K) * (ZMod.χ₄ c : 𝓞 K) = 1 := by exact_mod_cast hχ_sq hc_odd
  have hu : IsUnit (Ideal.Quotient.mk (span {π₂}) (ZMod.χ₄ c : 𝓞 K)) :=
    (IsUnit.of_mul_eq_one _ hχc_mul).map _
  exact (IsUnit.of_pow_eq_one (n := 4) (powerResidueSymbolIdeal_pow_eq_one hu)
    (by decide)).mul_left_cancel (by linear_combination hrel)

/-- The product `(χ₄(a) / π₂)_4 · (χ₄(c) / π₁)_4` is `1` for primary `π₁ = a + b i` and
`π₂ = c + d i`: each factor is `(-1) ^ (((a - 1) / 2) ((c - 1) / 2))`. -/
private theorem symbol_χ₄_mul_symbol_χ₄_eq_one {ζ : K} (hζ : IsPrimitiveRoot ζ 4) {a b c d : ℤ}
    (hπ₁ : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger))
    (hπ₂ : IsPrimaryGaussian ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger)) :
    powerResidueSymbolIdeal (span {(c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ (ZMod.χ₄ a : 𝓞 K)) *
      powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ (ZMod.χ₄ c : 𝓞 K)) = 1 := by
  have hmod₁ := (hζ.isPrimaryGaussian_add_mul_iff).mp hπ₁
  have hmod₂ := (hζ.isPrimaryGaussian_add_mul_iff).mp hπ₂
  have h_eval {x y : ℤ} (hx : IsPrimaryGaussian ((x : 𝓞 K) + (y : 𝓞 K) * hζ.toInteger))
      {w : ℤ} (hw : w ≡ 1 [ZMOD 4] ∨ w ≡ 3 [ZMOD 4]) :
      ((powerResidueSymbolIdeal (span {(x : 𝓞 K) + (y : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ (ZMod.χ₄ w : 𝓞 K)) : 𝓞 K) : K) =
        (-1 : K) ^ (((w - 1) / 2) * ((x - 1) / 2)) := by
    rcases hw with hw1 | hw3
    · have h1 : ZMod.χ₄ w = 1 := ZMod.χ₄_int_one_mod_four (by simp only [Int.ModEq] at hw1; omega)
      have heven : Even ((w - 1) / 2 * ((x - 1) / 2)) :=
        Even.mul_right ⟨(w - 1) / 4, by simp only [Int.ModEq] at hw1; omega⟩ _
      rw [h1, Int.cast_one, map_one, map_one, heven.neg_one_zpow]
      rfl
    · have h3 : ZMod.χ₄ w = -1 :=
        ZMod.χ₄_int_three_mod_four (by simp only [Int.ModEq] at hw3; omega)
      rw [h3, Int.cast_neg, Int.cast_one, hx.powerResidueSymbolIdeal_mk_neg_one]
      refine zpow_eq_zpow_of_modEq (n := 2) (by norm_num) ?_
      obtain ⟨k, hk⟩ : ∃ k, w = 4 * k + 3 := ⟨w / 4, by simp only [Int.ModEq] at hw3; omega⟩
      rw [hk, show (4 * k + 3 - 1) / 2 = 2 * k + 1 by omega]
      exact Int.modEq_iff_dvd.mpr ⟨k * ((x - 1) / 2), by ring⟩
  have hK : ((powerResidueSymbolIdeal (span {(c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ (ZMod.χ₄ a : 𝓞 K)) : 𝓞 K) : K) *
      ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ (ZMod.χ₄ c : 𝓞 K)) : 𝓞 K) : K) = 1 := by
    rw [h_eval hπ₂ (hmod₁.imp And.left And.left), h_eval hπ₁ (hmod₂.imp And.left And.left),
      mul_comm ((c - 1) / 2), ← zpow_add₀ (by norm_num)]
    exact Even.neg_one_zpow ⟨_, rfl⟩
  ext
  simpa using hK

/-- For primary `π₁ = a + b i`, `π₂ = c + d i`, and `m = a c + b d`, the sum of
`(w χ₄(w) - 1) / 4` over `w ∈ {a, c, m}` is congruent modulo `2` to
`((N π₁ - 1) / 4) ((N π₂ - 1) / 4)`. -/
private theorem exp_sum_modEq_norm_mul_of_primary {ζ : K} (hζ : IsPrimitiveRoot ζ 4)
    {a b c d : ℤ} (hπ₁ : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger))
    (hπ₂ : IsPrimaryGaussian ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger)) :
    let π₁ : 𝓞 K := (a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger
    let π₂ : 𝓞 K := (c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger
    let m : ℤ := a * c + b * d
    (a * ZMod.χ₄ a - 1) / 4 + (c * ZMod.χ₄ c - 1) / 4 + (m * ZMod.χ₄ m - 1) / 4 ≡
      (((absNorm (span {π₁}) - 1) / 4 * ((absNorm (span {π₂}) - 1) / 4) : ℕ) : ℤ) [ZMOD 2] := by
  intro π₁ π₂ m
  have hmod₁ := (hζ.isPrimaryGaussian_add_mul_iff).mp hπ₁
  have hmod₂ := (hζ.isPrimaryGaussian_add_mul_iff).mp hπ₂
  have ha_odd : Odd a := Int.odd_iff.mpr (by simp only [Int.ModEq] at hmod₁; omega)
  have hc_odd : Odd c := Int.odd_iff.mpr (by simp only [Int.ModEq] at hmod₂; omega)
  obtain ⟨u, hu⟩ : ∃ u, a * ZMod.χ₄ a = 4 * u + 1 := by
    have := ZMod.int_mul_χ₄_modEq_one ha_odd; simp only [Int.ModEq] at this
    exact ⟨(a * ZMod.χ₄ a) / 4, by omega⟩
  obtain ⟨v, hv⟩ : ∃ v, c * ZMod.χ₄ c = 4 * v + 1 := by
    have := ZMod.int_mul_χ₄_modEq_one hc_odd; simp only [Int.ModEq] at this
    exact ⟨(c * ZMod.χ₄ c) / 4, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = 2 * b' := ⟨b / 2, by simp only [Int.ModEq] at hmod₁; omega⟩
  obtain ⟨d', rfl⟩ : ∃ d', d = 2 * d' := ⟨d / 2, by simp only [Int.ModEq] at hmod₂; omega⟩
  have hχm : ZMod.χ₄ (m : ZMod 4) = ZMod.χ₄ (a : ZMod 4) * ZMod.χ₄ (c : ZMod 4) := by
    rw [show (m : ZMod 4) = (a : ZMod 4) * (c : ZMod 4) by
      simp [m, show (2 * b' * (2 * d') : ℤ) = 4 * (b' * d') by ring,
        show (4 : ZMod 4) = 0 by decide], map_mul]
  have hm_val : (m * ZMod.χ₄ m - 1) / 4 = 4 * u * v + u + v + ZMod.χ₄ a * ZMod.χ₄ c * b' * d' := by
    have hmul : m * ZMod.χ₄ m - 1 = 4 * (4 * u * v + u + v + ZMod.χ₄ a * ZMod.χ₄ c * b' * d') := by
      rw [hχm]
      calc (a * c + 2 * b' * (2 * d')) * (ZMod.χ₄ a * ZMod.χ₄ c) - 1
          = (a * ZMod.χ₄ a) * (c * ZMod.χ₄ c) + 4 * (ZMod.χ₄ a * ZMod.χ₄ c * b' * d') - 1 := by ring
        _ = (4 * u + 1) * (4 * v + 1) + 4 * (ZMod.χ₄ a * ZMod.χ₄ c * b' * d') - 1 := by rw [hu, hv]
        _ = 4 * (4 * u * v + u + v + ZMod.χ₄ a * ZMod.χ₄ c * b' * d') := by ring
    rw [hmul, Int.mul_ediv_cancel_left _ (by decide : (4 : ℤ) ≠ 0)]
  have hb' : b' ≡ ((absNorm (span {π₁}) - 1) / 4 : ℕ) [ZMOD 2] :=
    (show b' ≡ (a - 1) / 2 [ZMOD 2] by simp only [Int.ModEq] at hmod₁ ⊢; omega).trans
      (hπ₁.norm_sub_one_div_four.symm.trans (by rw [hπ₁.natCast_absNorm_sub_one_div_four]))
  have hd' : d' ≡ ((absNorm (span {π₂}) - 1) / 4 : ℕ) [ZMOD 2] :=
    (show d' ≡ (c - 1) / 2 [ZMOD 2] by simp only [Int.ModEq] at hmod₂ ⊢; omega).trans
      (hπ₂.norm_sub_one_div_four.symm.trans (by rw [hπ₂.natCast_absNorm_sub_one_div_four]))
  have hχ_mod2 : ZMod.χ₄ a * ZMod.χ₄ c ≡ 1 [ZMOD 2] := by
    rcases (show a % 4 = 1 ∨ a % 4 = 3 by have := Int.odd_iff.mp ha_odd; omega) with ha1 | ha3 <;>
      rcases (show c % 4 = 1 ∨ c % 4 = 3 by have := Int.odd_iff.mp hc_odd; omega) with hc1 | hc3
    · rw [ZMod.χ₄_int_one_mod_four ha1, ZMod.χ₄_int_one_mod_four hc1]; decide
    · rw [ZMod.χ₄_int_one_mod_four ha1, ZMod.χ₄_int_three_mod_four hc3]; decide
    · rw [ZMod.χ₄_int_three_mod_four ha3, ZMod.χ₄_int_one_mod_four hc1]; decide
    · rw [ZMod.χ₄_int_three_mod_four ha3, ZMod.χ₄_int_three_mod_four hc3]; decide
  rw [hu, hv, hm_val, show (4 * u + 1 - 1) / 4 = u by omega,
    show (4 * v + 1 - 1) / 4 = v by omega]
  refine (Int.modEq_iff_dvd.mpr ⟨-(2 * u * v + u + v), by ring⟩ :
      u + v + (4 * u * v + u + v + ZMod.χ₄ a * ZMod.χ₄ c * b' * d') ≡
        ZMod.χ₄ a * ZMod.χ₄ c * b' * d' [ZMOD 2]).trans ?_
  rw [mul_assoc (ZMod.χ₄ a * ZMod.χ₄ c), Nat.cast_mul]
  simpa using hχ_mod2.mul (hb'.mul hd')

/-- For primary `π₁ = a + b i` and `π₂ = c + d i` and `m = a c + b d`, the product
`(i / a)_4 · (i / c)_4 · (i / m)_4` is `(-1) ^ (((N π₁ - 1) / 4) ((N π₂ - 1) / 4))`. -/
private theorem symbol_toInteger_mul_three_eq_sign {ζ : K} (hζ : IsPrimitiveRoot ζ 4)
    {a b c d : ℤ} (hπ₁ : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger))
    (hπ₂ : IsPrimaryGaussian ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger)) :
    let π₁ : 𝓞 K := (a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger
    let π₂ : 𝓞 K := (c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger
    let m : ℤ := a * c + b * d
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) 4 (Ideal.Quotient.mk _ hζ.toInteger) *
      powerResidueSymbolIdeal (span {(c : 𝓞 K)}) 4 (Ideal.Quotient.mk _ hζ.toInteger) *
      powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 (Ideal.Quotient.mk _ hζ.toInteger) =
      (-1) ^ (((absNorm (span {π₁}) - 1) / 4) * ((absNorm (span {π₂}) - 1) / 4)) := by
  intro π₁ π₂ m
  have hmod₁ := (hζ.isPrimaryGaussian_add_mul_iff).mp hπ₁
  have hmod₂ := (hζ.isPrimaryGaussian_add_mul_iff).mp hπ₂
  have ha_odd : Odd a := Int.odd_iff.mpr (by simp only [Int.ModEq] at hmod₁; omega)
  have hc_odd : Odd c := Int.odd_iff.mpr (by simp only [Int.ModEq] at hmod₂; omega)
  have hm_odd : Odd m := Odd.add_even (ha_odd.mul hc_odd)
    ((Int.even_iff.mpr (by simp only [Int.ModEq] at hmod₁; omega)).mul_right d)
  have h_odd_i {w : ℤ} (hw : Odd w) :
      ((powerResidueSymbolIdeal (span {(w : 𝓞 K)}) 4
        (Ideal.Quotient.mk _ hζ.toInteger) : 𝓞 K) : K) =
        (-1 : K) ^ ((w * ZMod.χ₄ w - 1) / 4) := by
    have hχu : IsUnit (ZMod.χ₄ w : 𝓞 K) := by
      rcases (show w % 4 = 1 ∨ w % 4 = 3 by have := Int.odd_iff.mp hw; omega) with h1 | h3
      · rw [ZMod.χ₄_int_one_mod_four h1, Int.cast_one]; exact isUnit_one
      · rw [ZMod.χ₄_int_three_mod_four h3, Int.cast_neg, Int.cast_one]; exact isUnit_one.neg
    have htop : span {(ZMod.χ₄ w : 𝓞 K)} = ⊤ := span_singleton_eq_top.mpr hχu
    have hspan : span {((w * ZMod.χ₄ w : ℤ) : 𝓞 K)} = span {(w : 𝓞 K)} := by
      rw [Int.cast_mul, ← span_singleton_mul_span_singleton, htop, mul_top]
    rw [← hspan,
      hζ.powerResidueSymbolIdeal_span_intCast_mk_toInteger (ZMod.int_mul_χ₄_modEq_one hw)]
  have hK : ((powerResidueSymbolIdeal (span {(a : 𝓞 K)}) 4
        (Ideal.Quotient.mk _ hζ.toInteger) : 𝓞 K) : K) *
      ((powerResidueSymbolIdeal (span {(c : 𝓞 K)}) 4
        (Ideal.Quotient.mk _ hζ.toInteger) : 𝓞 K) : K) *
      ((powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4
        (Ideal.Quotient.mk _ hζ.toInteger) : 𝓞 K) : K) =
      (-1 : K) ^ (((absNorm (span {π₁}) - 1) / 4) * ((absNorm (span {π₂}) - 1) / 4)) := by
    rw [h_odd_i ha_odd, h_odd_i hc_odd, h_odd_i hm_odd, ← zpow_add₀ (by norm_num),
      ← zpow_add₀ (by norm_num), ← zpow_natCast]
    exact zpow_eq_zpow_of_modEq (n := 2) (by norm_num)
      (exp_sum_modEq_norm_mul_of_primary hζ hπ₁ hπ₂)
  ext
  simpa using hK

/-- At `m = a c + b d`, Galois equivariance and `τ π₁ · π₂ ≡ (a d - b c) i (mod m)` give
`(π₁ / m)_4 ^ 3 = (τ π₁ / m)_4` and `(π₂ / m)_4 · (τ π₁ / m)_4 = (i / m)_4`. -/
private theorem symbol_pow_three_and_mul_at_add_mul {ζ : K} (hζ : IsPrimitiveRoot ζ 4)
    {a b c d : ℤ} (hπ₁ : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger))
    (hπ₂ : IsPrimaryGaussian ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger)) (hab : IsCoprime a b)
    (hcd : IsCoprime c d)
    (hcop : IsCoprime (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger})
      (span {(c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger}))
    {τ : 𝓞 K ≃+* 𝓞 K} (hτ : ∀ x : 𝓞 K, x ^ 4 = 1 → τ x = x ^ 3) :
    let π₁ : 𝓞 K := (a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger
    let π₂ : 𝓞 K := (c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger
    let m : ℤ := a * c + b * d
    powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π₁) ^ 3 =
        powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 (Ideal.Quotient.mk _ (τ π₁)) ∧
      powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π₂) *
          powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 (Ideal.Quotient.mk _ (τ π₁)) =
        powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 (Ideal.Quotient.mk _ hζ.toInteger) := by
  intro π₁ π₂ m
  have hsq : hζ.toInteger ^ 2 = -1 := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  have ha_π₁ : IsCoprime (span {(a : 𝓞 K)}) (span {π₁}) := by
    obtain ⟨u, v, huv⟩ := hab
    refine (isCoprime_span_singleton_iff _ _).mpr
      ⟨(u : 𝓞 K) + (v : 𝓞 K) * hζ.toInteger, -(v : 𝓞 K) * hζ.toInteger, ?_⟩
    have huv' : (u : 𝓞 K) * a + (v : 𝓞 K) * b = 1 := by exact_mod_cast huv
    simp only [π₁]
    linear_combination huv' - (v : 𝓞 K) * b * hsq
  have hπ₁m_cop : IsCoprime (span {π₁}) (span {(m : 𝓞 K)}) := by
    have hm_mod : (m : 𝓞 K) - (a : 𝓞 K) * π₂ = (-(d : 𝓞 K) * hζ.toInteger) * π₁ := by
      simp only [π₁, π₂, m]; push_cast; linear_combination (b : 𝓞 K) * d * hsq
    have hal : IsCoprime (span {π₁}) (span {(a : 𝓞 K) * π₂}) := by
      rw [← span_singleton_mul_span_singleton]; exact ha_π₁.symm.mul_right hcop
    obtain ⟨u, v, huv⟩ := (isCoprime_span_singleton_iff _ _).mp hal
    exact (isCoprime_span_singleton_iff _ _).mpr
      ⟨u - v * (-(d : 𝓞 K) * hζ.toInteger), v, by linear_combination huv + v * hm_mod⟩
  have hπ₁m4 : powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π₁) ^ 4 = 1 :=
    powerResidueSymbolIdeal_pow_eq_one
      (Ideal.Quotient.isUnit_mk_iff.mpr (isCoprime_iff_sup_eq.mp hπ₁m_cop))
  have hgal_m : powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π₁) ^ 3 =
      powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 (Ideal.Quotient.mk _ (τ π₁)) := by
    have h := map_powerResidueSymbolIdeal (n := 4) (span {(m : 𝓞 K)}) τ π₁
    rw [hτ _ hπ₁m4] at h
    exact h.trans (by rw [map_span, Set.image_singleton, map_intCast])
  have hτπ₁_π₂ : Ideal.Quotient.mk (span {(m : 𝓞 K)}) (τ π₁ * π₂) =
      Ideal.Quotient.mk (span {(m : 𝓞 K)}) (((a * d - b * c : ℤ) : 𝓞 K) * hζ.toInteger) := by
    have hτi : τ hζ.toInteger = -hζ.toInteger := by
      rw [hτ hζ.toInteger hζ.toInteger_isPrimitiveRoot.pow_eq_one]
      linear_combination hζ.toInteger * hsq
    rw [Ideal.Quotient.eq, mem_span_singleton]
    refine ⟨1, ?_⟩
    simp only [π₁, π₂, m, map_add, map_mul, map_intCast, hτi]
    push_cast
    linear_combination -(b : 𝓞 K) * d * hsq
  have hnm : powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4
      (Ideal.Quotient.mk _ ((a * d - b * c : ℤ) : 𝓞 K)) = 1 := by
    simpa [m] using powerResidueSymbolIdeal_intCast_four (K := K)
      (isCoprime_sub_add_of_isCoprime_coords hζ hπ₁ hπ₂ hab hcd hcop)
  refine ⟨hgal_m, ?_⟩
  rw [mul_comm, ← map_mul, ← map_mul, hτπ₁_π₂, map_mul, map_mul, hnm, one_mul]

/-- Quartic reciprocity for coprime primary elements `π₁ = a + b i` and `π₂ = c + d i` whose
integer coordinates satisfy `IsCoprime a b` and `IsCoprime c d`. -/
private theorem quartic_reciprocity_of_isCoprime_coords {ζ : K} (hζ : IsPrimitiveRoot ζ 4)
    {a b c d : ℤ} (hπ₁ : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger))
    (hπ₂ : IsPrimaryGaussian ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger)) (hab : IsCoprime a b)
    (hcd : IsCoprime c d)
    (hcop : IsCoprime (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger})
      (span {(c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger})) :
    let π₁ : 𝓞 K := (a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger
    let π₂ : 𝓞 K := (c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger
    powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) =
      powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) *
        (-1) ^ (((absNorm (span {π₁}) - 1) / 4) * ((absNorm (span {π₂}) - 1) / 4)) := by
  intro π₁ π₂
  set m : ℤ := a * c + b * d
  have eq1 := symbol_toInteger_mul_symbol_eq_at_primary hζ hπ₁ hπ₂ hcd
  have eq2 := symbol_toInteger_mul_symbol_eq_at_primary hζ hπ₂ hπ₁ hab
  dsimp only at eq1 eq2
  rw [show c * a + d * b = m by ring] at eq2
  obtain ⟨σ₀, _, hτ⟩ := exists_gal_apply_eq_pow_three_of_four (K := K)
  let τ := MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) σ₀
  obtain ⟨hgal_m, hprod_m⟩ :=
    symbol_pow_three_and_mul_at_add_mul hζ hπ₁ hπ₂ hab hcd hcop (τ := τ) hτ
  have hmod₁ := (hζ.isPrimaryGaussian_add_mul_iff).mp hπ₁
  have hmod₂ := (hζ.isPrimaryGaussian_add_mul_iff).mp hπ₂
  have ha_odd : Odd a := Int.odd_iff.mpr (by simp only [Int.ModEq] at hmod₁; omega)
  have hc_odd : Odd c := Int.odd_iff.mpr (by simp only [Int.ModEq] at hmod₂; omega)
  have hm_odd : Odd m := Odd.add_even (ha_odd.mul hc_odd)
    ((Int.even_iff.mpr (by simp only [Int.ModEq] at hmod₁; omega)).mul_right d)
  have hi_sq {w : ℤ} (hw : Odd w) :
      powerResidueSymbolIdeal (span {(w : 𝓞 K)}) 4 (Ideal.Quotient.mk _ hζ.toInteger) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one,
      powerResidueSymbolIdeal_span_intCast_mk_neg_one hw]
  have hχc_sq :
      powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ (ZMod.χ₄ c : 𝓞 K)) ^ 2 = 1 := by
    have h1 : (ZMod.χ₄ c : 𝓞 K) ^ 2 = 1 := by
      rcases (show c % 4 = 1 ∨ c % 4 = 3 by have := Int.odd_iff.mp hc_odd; omega) with h1 | h3 <;>
        [rw [ZMod.χ₄_int_one_mod_four h1]; rw [ZMod.χ₄_int_three_mod_four h3]] <;> norm_num
    rw [← map_pow, ← map_pow, h1, map_one, map_one]
  have hπ₂π₁4 : powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) ^ 4 = 1 :=
    powerResidueSymbolIdeal_pow_eq_one
      (Ideal.Quotient.isUnit_mk_iff.mpr (isCoprime_iff_sup_eq.mp hcop.symm))
  set s₁ := powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂)
  set s₂ := powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁)
  set ia := powerResidueSymbolIdeal (span {(a : 𝓞 K)}) 4 (Ideal.Quotient.mk _ hζ.toInteger)
  set ic := powerResidueSymbolIdeal (span {(c : 𝓞 K)}) 4 (Ideal.Quotient.mk _ hζ.toInteger)
  set im := powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 (Ideal.Quotient.mk _ hζ.toInteger)
  set χc₁ := powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ (ZMod.χ₄ c : 𝓞 K))
  set mτ₁ := powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 (Ideal.Quotient.mk _ (τ π₁))
  have eq2' : ia * s₁ ^ 3 = χc₁ * mτ₁ := by
    have hcube := congrArg (· ^ 3) eq2
    rw [mul_pow, mul_pow, hgal_m] at hcube
    linear_combination hcube - ia * s₁ ^ 3 * hi_sq ha_odd + χc₁ * mτ₁ * hχc_sq
  have hcomb : ic * ia * s₂ * s₁ ^ 3 = im := by
    calc ic * ia * s₂ * s₁ ^ 3
        = (ic * s₂) * (ia * s₁ ^ 3) := by ring
      _ = _ := by rw [eq1, eq2']
      _ = _ := by rw [mul_mul_mul_comm, symbol_χ₄_mul_symbol_χ₄_eq_one hζ hπ₁ hπ₂, hprod_m, one_mul]
  rw [← symbol_toInteger_mul_three_eq_sign hζ hπ₁ hπ₂]
  linear_combination -s₁ * im * hcomb + s₂ * ia * ic * im * hπ₂π₁4 - s₁ * hi_sq hm_odd

end CoprimeCoordinates

/-! ### The law of biquadratic (quartic) reciprocity -/

section GeneralReciprocity

/-- Every primary element `x` of `𝓞 K = ℤ[i]` decomposes as `m * (a + b i)` where `m ≡ 1 (mod 4)`
is an integer and `a + b i` is primary with `IsCoprime a b`. -/
private theorem exists_intCast_mul_isCoprime_coords {ζ : K} (hζ : IsPrimitiveRoot ζ 4) {x : 𝓞 K}
    (hx : IsPrimaryGaussian x) :
    ∃ (m a b : ℤ), m ≡ 1 [ZMOD 4] ∧ IsCoprime a b ∧
      IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger) ∧
      x = (m : 𝓞 K) * ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger) := by
  obtain ⟨a₀, b₀, rfl⟩ := hζ.exists_intCast_add_intCast_mul_toInteger_eq (by decide) x
  have hmod := (hζ.isPrimaryGaussian_add_mul_iff).mp hx
  have ha₀_odd : Odd a₀ := Int.odd_iff.mpr (by simp only [Int.ModEq] at hmod; omega)
  have ha₀_ne : a₀ ≠ 0 := by rintro rfl; exact Int.not_odd_zero ha₀_odd
  obtain ⟨a₁, b₁, hgcd, ha₀_eq, hb₀_eq⟩ :=
    Int.exists_gcd_one (Int.gcd_pos_of_ne_zero_left b₀ ha₀_ne)
  set g : ℤ := (Int.gcd a₀ b₀ : ℤ)
  have hg_odd : Odd g := by
    obtain ⟨k, hk⟩ := Int.gcd_dvd_left a₀ b₀
    rw [hk] at ha₀_odd
    exact (Int.odd_mul.mp ha₀_odd).1
  have hχg_sq : ZMod.χ₄ (g : ZMod 4) * ZMod.χ₄ (g : ZMod 4) = 1 := by
    rcases (show g % 4 = 1 ∨ g % 4 = 3 by have := Int.odd_iff.mp hg_odd; omega) with h1 | h3
    · rw [ZMod.χ₄_int_one_mod_four h1]; rfl
    · rw [ZMod.χ₄_int_three_mod_four h3]; rfl
  have hm : g * ZMod.χ₄ g ≡ 1 [ZMOD 4] := ZMod.int_mul_χ₄_modEq_one hg_odd
  have hcop : IsCoprime (a₁ * ZMod.χ₄ g) (b₁ * ZMod.χ₄ g) := by
    obtain ⟨u, v, huv⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hgcd
    exact ⟨u * ZMod.χ₄ g, v * ZMod.χ₄ g, by linear_combination huv + (u * a₁ + v * b₁) * hχg_sq⟩
  have hx_eq : (a₀ : 𝓞 K) + (b₀ : 𝓞 K) * hζ.toInteger =
      ((g * ZMod.χ₄ g : ℤ) : 𝓞 K) *
        (((a₁ * ZMod.χ₄ g : ℤ) : 𝓞 K) + ((b₁ * ZMod.χ₄ g : ℤ) : 𝓞 K) * hζ.toInteger) := by
    have ha' : a₀ = (g * ZMod.χ₄ g) * (a₁ * ZMod.χ₄ g) := by
      linear_combination ha₀_eq - a₁ * g * hχg_sq
    have hb' : b₀ = (g * ZMod.χ₄ g) * (b₁ * ZMod.χ₄ g) := by
      linear_combination hb₀_eq - b₁ * g * hχg_sq
    conv_lhs => rw [ha', hb']
    push_cast
    ring
  exact ⟨g * ZMod.χ₄ g, a₁ * ZMod.χ₄ g, b₁ * ZMod.χ₄ g, hm, hcop,
    (hx_eq ▸ hx).of_intCast_mul hm, hx_eq⟩

/-- Multiplying a primary element `y` by an odd integer `m` does not change the parity of
`(N(y 𝓞 K) - 1) / 4`, because `N(m 𝓞 K) = m² ≡ 1 (mod 8)`. -/
private theorem neg_one_pow_absNorm_intCast_mul {m : ℤ} (hm : Odd m) {y : 𝓞 K}
    (hy : IsPrimaryGaussian y) (k : ℕ) :
    (-1 : 𝓞 K) ^ (((absNorm (span {(m : 𝓞 K) * y}) - 1) / 4) * k) =
      (-1 : 𝓞 K) ^ (((absNorm (span {y}) - 1) / 4) * k) := by
  have hm_norm : absNorm (span {(m : 𝓞 K)}) = m.natAbs ^ 2 := by
    have hspan : span {(m : 𝓞 K)} = span {(m.natAbs : 𝓞 K)} := by
      rcases Int.natAbs_eq m with h | h <;> rw [h] <;> simp
    rw [hspan, absNorm_span_natCast_four]
  have hm8 : m.natAbs ^ 2 % 8 = 1 := by
    obtain ⟨t, ht⟩ := Int.natAbs_odd.mpr hm
    obtain ⟨r, hr⟩ := Nat.even_mul_succ_self t
    have hsq : m.natAbs ^ 2 = 8 * r + 1 := by rw [ht]; linear_combination 4 * hr
    omega
  have hy4 : absNorm (span {y}) % 4 = 1 := by
    simpa [Nat.ModEq] using absNorm_modEq_one hy.absNorm_span_singleton_coprime_four
  rw [← span_singleton_mul_span_singleton, map_mul, hm_norm]
  set q := m.natAbs ^ 2
  set N := absNorm (span {y})
  have hmod2 : ((q * N - 1) / 4) % 2 = ((N - 1) / 4) % 2 := by
    obtain ⟨a, ha⟩ : ∃ a, q = 8 * a + 1 := ⟨q / 8, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, N = 4 * b + 1 := ⟨N / 4, by omega⟩
    have h1 : ((8 * a + 1) * (4 * b + 1) - 1) / 4 = 2 * (4 * a * b + a) + b := by
      have hmul : (8 * a + 1) * (4 * b + 1) - 1 = 4 * (2 * (4 * a * b + a) + b) :=
        Nat.sub_eq_of_eq_add (by ring)
      rw [hmul, Nat.mul_div_cancel_left _ (by decide : 0 < 4)]
    rw [ha, hb, h1, show (4 * b + 1 - 1) / 4 = b by omega]
    omega
  rw [← Nat.mod_add_div (((q * N - 1) / 4) * k) 2,
    ← Nat.mod_add_div (((N - 1) / 4) * k) 2, Nat.mul_mod, hmod2, ← Nat.mul_mod]
  simp [pow_add, pow_mul]

/-- Expanding `(m₂ y / m₁ x)_4` via multiplicativity, integer triviality `(m₂ / m₁)_4 = 1`, and
rational reciprocity `(x / m₁)_4 = (m₁ / x)_4` when `m₁ ≡ 1 (mod 4)` and `IsCoprime m₂ m₁`. -/
private theorem symbol_intCast_mul_eq {m₁ m₂ : ℤ} (hm₁ : m₁ ≡ 1 [ZMOD 4])
    (hm₂₁ : IsCoprime m₂ m₁) {x y : 𝓞 K} (hx : IsPrimaryGaussian x) (hy : IsPrimaryGaussian y) :
    powerResidueSymbolIdeal (span {(m₁ : 𝓞 K) * x}) 4
        (Ideal.Quotient.mk _ ((m₂ : 𝓞 K) * y)) =
      powerResidueSymbolIdeal (span {y}) 4 (Ideal.Quotient.mk _ (m₁ : 𝓞 K)) *
        powerResidueSymbolIdeal (span {x}) 4 (Ideal.Quotient.mk _ (m₂ : 𝓞 K)) *
        powerResidueSymbolIdeal (span {x}) 4 (Ideal.Quotient.mk _ y) := by
  have hm₁_odd : Odd m₁ := Int.odd_iff.mpr (by simp only [Int.ModEq] at hm₁; omega)
  have hm₁0 : span {(m₁ : 𝓞 K)} ≠ ⊥ := by
    simpa using (by rintro rfl; exact Int.not_odd_zero hm₁_odd : m₁ ≠ 0)
  have hx0 : span {x} ≠ ⊥ := by simpa using (by rintro h; simpa [h] using hx.odd_norm : x ≠ 0)
  have hm₂₁_triv :
      powerResidueSymbolIdeal (span {(m₁ : 𝓞 K)}) 4 (Ideal.Quotient.mk _ (m₂ : 𝓞 K)) = 1 := by
    simpa using powerResidueSymbolIdeal_intCast_four (K := K) hm₂₁
  rw [← span_singleton_mul_span_singleton, powerResidueSymbolIdeal_mul_right hm₁0 hx0,
    map_mul, map_mul, hm₂₁_triv, one_mul, ← hy.quartic_reciprocity_intCast hm₁, map_mul,
    map_mul, mul_assoc]

/-- **The law of biquadratic (quartic) reciprocity.** Let `K = ℚ(i)`, so that `𝓞 K = ℤ[i]`, and
let `π₁` and `π₂` be primary elements of `𝓞 K`. Then
`(π₂ / π₁)_4 = (π₁ / π₂)_4 · (-1) ^ (((N π₁ - 1) / 4) ((N π₂ - 1) / 4))`,
where `(· / α)_4` is the quartic power residue symbol at the ideal `α 𝓞 K` and `N α` is the
absolute norm of `α 𝓞 K`. Neither primality nor coprimality is required: `π₁` and `π₂` may be
composite or equal to `1`, and when they are not coprime both symbols vanish. -/
theorem IsPrimaryGaussian.quartic_reciprocity {π₁ π₂ : 𝓞 K}
    (hπ₁ : IsPrimaryGaussian π₁) (hπ₂ : IsPrimaryGaussian π₂) :
    powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) =
      powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) *
        (-1) ^ (((absNorm (span {π₁}) - 1) / 4) * ((absNorm (span {π₂}) - 1) / 4)) := by
  by_cases hcop : IsCoprime (span {π₁}) (span {π₂})
  swap
  · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr (mt IsCoprime.symm hcop),
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hcop, zero_mul]
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
  obtain ⟨m₁, a, b, hm₁, hab, hπ₁', rfl⟩ := exists_intCast_mul_isCoprime_coords hζ hπ₁
  obtain ⟨m₂, c, d, hm₂, hcd, hπ₂', rfl⟩ := exists_intCast_mul_isCoprime_coords hζ hπ₂
  set π₁' : 𝓞 K := (a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger
  set π₂' : 𝓞 K := (c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger
  have hm₁_odd : Odd m₁ := Int.odd_iff.mpr (by simp only [Int.ModEq] at hm₁; omega)
  have hm₂_odd : Odd m₂ := Int.odd_iff.mpr (by simp only [Int.ModEq] at hm₂; omega)
  rw [← span_singleton_mul_span_singleton, ← span_singleton_mul_span_singleton] at hcop
  obtain ⟨⟨hm₁₂_id, _⟩, ⟨_, hcop'⟩⟩ :=
    (IsCoprime.mul_left_iff.mp hcop).imp IsCoprime.mul_right_iff.mp IsCoprime.mul_right_iff.mp
  have hm₂₁ : IsCoprime m₂ m₁ := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have hle : (⊤ : Ideal (𝓞 K)) ≤ span {(Int.gcd m₂ m₁ : 𝓞 K)} := by
      rw [← isCoprime_iff_sup_eq.mp hm₁₂_id]
      refine sup_le (span_singleton_le_span_singleton.mpr ?_)
        (span_singleton_le_span_singleton.mpr ?_)
      · obtain ⟨k, hk⟩ := Int.gcd_dvd_right m₂ m₁
        exact ⟨k, by exact_mod_cast hk⟩
      · obtain ⟨k, hk⟩ := Int.gcd_dvd_left m₂ m₁
        exact ⟨k, by exact_mod_cast hk⟩
    have hN := congrArg absNorm (top_unique hle)
    rw [absNorm_span_natCast_four, absNorm_top] at hN
    simpa using hN
  have hrec : powerResidueSymbolIdeal (span {π₁'}) 4 (Ideal.Quotient.mk _ π₂') =
      powerResidueSymbolIdeal (span {π₂'}) 4 (Ideal.Quotient.mk _ π₁') *
        (-1) ^ (((absNorm (span {π₁'}) - 1) / 4) * ((absNorm (span {π₂'}) - 1) / 4)) :=
    quartic_reciprocity_of_isCoprime_coords hζ hπ₁' hπ₂' hab hcd hcop'
  have hsign : (-1 : 𝓞 K) ^ (((absNorm (span {(m₁ : 𝓞 K) * π₁'}) - 1) / 4) *
        ((absNorm (span {(m₂ : 𝓞 K) * π₂'}) - 1) / 4)) =
      (-1 : 𝓞 K) ^ (((absNorm (span {π₁'}) - 1) / 4) * ((absNorm (span {π₂'}) - 1) / 4)) := by
    rw [neg_one_pow_absNorm_intCast_mul hm₁_odd hπ₁', mul_comm,
      neg_one_pow_absNorm_intCast_mul hm₂_odd hπ₂', mul_comm]
  rw [symbol_intCast_mul_eq hm₁ hm₂₁ hπ₁' hπ₂', symbol_intCast_mul_eq hm₂ hm₂₁.symm hπ₂' hπ₁',
    hrec, hsign]
  ring

/-- **Quartic reciprocity in coordinates.** Let `K = ℚ(i)`, let `i` be a primitive fourth root of
unity, and let `π₁ = a + b i` and `π₂ = c + d i` be primary elements of `𝓞 K = ℤ[i]`. Then
`(π₂ / π₁)_4 = (π₁ / π₂)_4 · (-1) ^ (((a - 1) / 2) ((c - 1) / 2))`, read in `K`. Neither
coprimality of `π₁` and `π₂` nor coprimality of `(a, b)` or `(c, d)` is required. -/
theorem IsPrimaryGaussian.quartic_reciprocity_add_mul {ζ : K} {hζ : IsPrimitiveRoot ζ 4}
    {a b c d : ℤ} (hπ₁ : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger))
    (hπ₂ : IsPrimaryGaussian ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger)) :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger)) : 𝓞 K) : K) =
      ((powerResidueSymbolIdeal (span {(c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger}) 4
          (Ideal.Quotient.mk _ ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) : 𝓞 K) : K) *
        (-1) ^ (((a - 1) / 2) * ((c - 1) / 2)) := by
  rw [hπ₁.quartic_reciprocity hπ₂]
  push_cast
  congr 1
  rw [← zpow_natCast, Nat.cast_mul, hπ₁.natCast_absNorm_sub_one_div_four,
    hπ₂.natCast_absNorm_sub_one_div_four]
  exact zpow_eq_zpow_of_modEq (n := 2) (by norm_num)
    (hπ₁.norm_sub_one_div_four.mul hπ₂.norm_sub_one_div_four)

/-- If the primary element `π₁` has ideal norm `N π₁ ≡ 1 (mod 8)`, then quartic reciprocity with
any primary element `π₂` has trivial sign: `(π₂ / π₁)_4 = (π₁ / π₂)_4`. -/
theorem IsPrimaryGaussian.quartic_reciprocity_of_absNorm_modEq_one {π₁ π₂ : 𝓞 K}
    (hπ₁ : IsPrimaryGaussian π₁) (hπ₂ : IsPrimaryGaussian π₂)
    (hN : absNorm (span {π₁}) ≡ 1 [MOD 8]) :
    powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) =
      powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) := by
  have heven : Even (((absNorm (span {π₁}) - 1) / 4) * ((absNorm (span {π₂}) - 1) / 4)) := by
    refine Even.mul_right ⟨(absNorm (span {π₁}) - 1) / 8, ?_⟩ _
    simp only [Nat.ModEq] at hN
    omega
  rw [hπ₁.quartic_reciprocity hπ₂, heven.neg_one_pow, mul_one]

/-- If the primary elements `π₁` and `π₂` both have ideal norm congruent to `5` modulo `8`, then
`(π₂ / π₁)_4 = -(π₁ / π₂)_4`. -/
theorem IsPrimaryGaussian.quartic_reciprocity_of_absNorm_modEq_five {π₁ π₂ : 𝓞 K}
    (hπ₁ : IsPrimaryGaussian π₁) (hπ₂ : IsPrimaryGaussian π₂)
    (hN₁ : absNorm (span {π₁}) ≡ 5 [MOD 8]) (hN₂ : absNorm (span {π₂}) ≡ 5 [MOD 8]) :
    powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) =
      -powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) := by
  have hodd : Odd (((absNorm (span {π₁}) - 1) / 4) * ((absNorm (span {π₂}) - 1) / 4)) := by
    refine Odd.mul ⟨(absNorm (span {π₁}) - 5) / 8, ?_⟩ ⟨(absNorm (span {π₂}) - 5) / 8, ?_⟩ <;>
      (simp only [Nat.ModEq] at hN₁ hN₂; omega)
  rw [hπ₁.quartic_reciprocity hπ₂, hodd.neg_one_pow, mul_neg_one]

/-- For coprime primary elements `π₁` and `π₂` of `𝓞 K = ℤ[i]`, `(π₂ / π₁)_4 = -(π₁ / π₂)_4` if and
only if `N π₁ ≡ 5 (mod 8)` and `N π₂ ≡ 5 (mod 8)`. -/
theorem IsPrimaryGaussian.quartic_reciprocity_eq_neg_iff {π₁ π₂ : 𝓞 K}
    (hπ₁ : IsPrimaryGaussian π₁) (hπ₂ : IsPrimaryGaussian π₂)
    (hcop : IsCoprime (span {π₁}) (span {π₂})) :
    powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) =
        -powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) ↔
      absNorm (span {π₁}) ≡ 5 [MOD 8] ∧ absNorm (span {π₂}) ≡ 5 [MOD 8] := by
  refine ⟨fun h ↦ ?_, fun ⟨h1, h2⟩ ↦ hπ₁.quartic_reciprocity_of_absNorm_modEq_five hπ₂ h1 h2⟩
  have h4 := powerResidueSymbolIdeal_pow_eq_one (n := 4)
    (Ideal.Quotient.isUnit_mk_iff.mpr (isCoprime_iff_sup_eq.mp hcop))
  have hunit : IsUnit (powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁)) :=
    IsUnit.of_pow_eq_one h4 (by decide)
  rw [hπ₁.quartic_reciprocity hπ₂] at h
  have hsgn : (-1 : 𝓞 K) ^ (((absNorm (span {π₁}) - 1) / 4) *
      ((absNorm (span {π₂}) - 1) / 4)) = -1 :=
    hunit.mul_left_cancel (by linear_combination h)
  have hodd : Odd (((absNorm (span {π₁}) - 1) / 4) * ((absNorm (span {π₂}) - 1) / 4)) := by
    by_contra he
    rw [(Nat.not_odd_iff_even.mp he).neg_one_pow] at hsgn
    exact absurd (congrArg (algebraMap (𝓞 K) K) hsgn) (by norm_num)
  obtain ⟨hodd₁, hodd₂⟩ := Nat.odd_mul.mp hodd
  have h₁4 := absNorm_modEq_one hπ₁.absNorm_span_singleton_coprime_four
  have h₂4 := absNorm_modEq_one hπ₂.absNorm_span_singleton_coprime_four
  simp only [Nat.ModEq] at h₁4 h₂4 ⊢
  rw [Nat.odd_iff] at hodd₁ hodd₂
  exact ⟨by omega, by omega⟩

/-- For coprime primary elements `π₁` and `π₂` of `𝓞 K = ℤ[i]`, `(π₂ / π₁)_4 = (π₁ / π₂)_4` if and
only if `N π₁ ≡ 1 (mod 8)` or `N π₂ ≡ 1 (mod 8)`. -/
theorem IsPrimaryGaussian.quartic_reciprocity_eq_iff {π₁ π₂ : 𝓞 K}
    (hπ₁ : IsPrimaryGaussian π₁) (hπ₂ : IsPrimaryGaussian π₂)
    (hcop : IsCoprime (span {π₁}) (span {π₂})) :
    powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) =
        powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) ↔
      absNorm (span {π₁}) ≡ 1 [MOD 8] ∨ absNorm (span {π₂}) ≡ 1 [MOD 8] := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.elim (hπ₁.quartic_reciprocity_of_absNorm_modEq_one hπ₂)
    fun h₂1 ↦ (hπ₂.quartic_reciprocity_of_absNorm_modEq_one hπ₁ h₂1).symm⟩
  by_contra! hne
  have h₁4 := absNorm_modEq_one hπ₁.absNorm_span_singleton_coprime_four
  have h₂4 := absNorm_modEq_one hπ₂.absNorm_span_singleton_coprime_four
  have h5 : absNorm (span {π₁}) ≡ 5 [MOD 8] ∧ absNorm (span {π₂}) ≡ 5 [MOD 8] := by
    simp only [Nat.ModEq] at h₁4 h₂4 hne ⊢
    exact ⟨by omega, by omega⟩
  have hneg := (hπ₁.quartic_reciprocity_eq_neg_iff hπ₂ hcop).mpr h5
  rw [h] at hneg
  have h4 := powerResidueSymbolIdeal_pow_eq_one (n := 4)
    (Ideal.Quotient.isUnit_mk_iff.mpr (isCoprime_iff_sup_eq.mp hcop))
  have hunit : IsUnit (powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁)) :=
    IsUnit.of_pow_eq_one h4 (by decide)
  have h1 : (1 : 𝓞 K) = -1 := hunit.mul_left_cancel (by linear_combination hneg)
  exact absurd (congrArg (algebraMap (𝓞 K) K) h1) (by norm_num)

end GeneralReciprocity

/-! ### Worked examples -/

section Examples

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 4)
include hζ

/- For the primary prime `π = -1 + 2i` (norm `5`) and the inert prime `q = 3` (primary associate
`-3`, norm `9 ≡ 1 (mod 8)`), `((-3) / (-1 + 2i))_4 = ((-1 + 2i) / 3)_4 = -i`. -/
example :
    let π : 𝓞 K := ((-1 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger
    powerResidueSymbolIdeal (span {π}) 4 (Ideal.Quotient.mk _ ((-3 : ℤ) : 𝓞 K)) =
      powerResidueSymbolIdeal (span {((3 : ℕ) : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) ∧
    powerResidueSymbolIdeal (span {((3 : ℕ) : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) =
      -hζ.toInteger := by
  intro π
  have hπ : IsPrimaryGaussian π := by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide
  refine ⟨by simpa using hπ.quartic_reciprocity_natCast (q := 3) (by decide), ?_⟩
  set Q : Ideal (𝓞 K) := span {((3 : ℕ) : 𝓞 K)}
  have : Q.IsMaximal := isMaximal_span_natCast_of_mod_four_eq_three Nat.prime_three rfl
  have hNQ : absNorm Q = 9 := by rw [absNorm_span_natCast_four]; norm_num
  have hQ4 : (absNorm Q).Coprime 4 := by rw [hNQ]; decide
  have hsq := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  have hπQ : Ideal.Quotient.mk Q π ≠ 0 := by
    intro h
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton,
      show ((3 : ℕ) : 𝓞 K) = ((3 : ℤ) : 𝓞 K) by simp,
      hζ.intCast_dvd_intCast_add_intCast_mul_toInteger_iff (by decide)] at h
    omega
  rw [powerResidueSymbolIdeal_of_isMaximal]
  refine (powerResidueSymbol_eq_iff hQ4 hπQ ?_).mpr ?_
  · rw [neg_pow, Even.neg_one_pow ⟨2, rfl⟩, one_mul, hζ.toInteger_isPrimitiveRoot.pow_eq_one]
  · rw [hNQ, show (9 - 1) / 4 = 2 by decide, ← map_pow, Ideal.Quotient.eq, mem_span_singleton]
    refine ⟨1 + hζ.toInteger, ?_⟩
    simp only [π]
    push_cast
    linear_combination (-4 : 𝓞 K) * hsq

/- For `q = 5 ≡ 1 (mod 4)` and the primary prime `3 + 2i` of norm `13`, the sign
`(-1) ^ ((5 - 1) / 2)` is `+1`, so `(5 / (3 + 2i))_4 = ((3 + 2i) / 5)_4`. -/
example :
    let π₂ : 𝓞 K := ((3 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger
    powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ ((5 : ℕ) : 𝓞 K)) =
      powerResidueSymbolIdeal (span {((5 : ℕ) : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π₂) := by
  intro π₂
  have hπ₂ : IsPrimaryGaussian π₂ := by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide
  simpa using hπ₂.quartic_reciprocity_natCast (q := 5) (by decide)

/- For the primary primes `π₁ = -1 + 2i` (norm `5 ≡ 5 (mod 8)`) and `π₂ = 3 + 2i` (norm
`13 ≡ 5 (mod 8)`), quartic reciprocity negates the symbol: `(π₂ / π₁)_4 = -(π₁ / π₂)_4`. -/
example :
    let π₁ : 𝓞 K := ((-1 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger
    let π₂ : 𝓞 K := ((3 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger
    powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) =
      -powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) := by
  intro π₁ π₂
  have hπ₁ : IsPrimaryGaussian π₁ := by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide
  have hπ₂ : IsPrimaryGaussian π₂ := by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide
  refine hπ₁.quartic_reciprocity_of_absNorm_modEq_five hπ₂ ?_ ?_
  · rw [absNorm_span_singleton, hζ.norm_intCast_add_intCast_mul_toInteger_of_four]; decide
  · rw [absNorm_span_singleton, hζ.norm_intCast_add_intCast_mul_toInteger_of_four]; decide

/- For `π₁ = -1 + 2i` (norm `5`) and `π₂ = -3` (norm `9 ≡ 1 (mod 8)`, non-coprime coordinates
`(-3, 0)`), the general theorem gives `((-3) / (-1 + 2i))_4 = ((-1 + 2i) / (-3))_4`. -/
example :
    let π₁ : 𝓞 K := ((-1 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger
    powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ ((-3 : ℤ) : 𝓞 K)) =
      powerResidueSymbolIdeal (span {((-3 : ℤ) : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π₁) := by
  intro π₁
  have hπ₁ : IsPrimaryGaussian π₁ := by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide
  have hπ₂ : IsPrimaryGaussian ((-3 : ℤ) : 𝓞 K) := isPrimaryGaussian_intCast_iff.mpr (by decide)
  refine (hπ₂.quartic_reciprocity_of_absNorm_modEq_one hπ₁ ?_).symm
  rw [Int.cast_neg, span_singleton_neg, show ((3 : ℤ) : 𝓞 K) = ((3 : ℕ) : 𝓞 K) by simp,
    absNorm_span_natCast_four]
  decide

end Examples

end TauCeti
