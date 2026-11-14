/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.Primary
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.StickelbergerPhi.Basic
import Mathlib.Algebra.CharP.Lemmas
import TauCeti.Algebra.GroupWithZero.Basic
import TauCeti.NumberTheory.GaussSum.Basic
import TauCeti.NumberTheory.LegendreSymbol.Complex
import TauCeti.NumberTheory.LegendreSymbol.ZModChar
import TauCeti.NumberTheory.MulChar.Basic
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.GaussSum
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.RationalResidue
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.SupplementaryLaws
import TauCeti.NumberTheory.NumberField.PrimeIdeal
import TauCeti.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.RingTheory.Ideal.Quotient.Coprime
import TauCeti.RingTheory.IntegralClosure.Map

/-!
# The law of biquadratic reciprocity

Let `K = ℚ(i)`, given as a number field with `IsCyclotomicExtension {4} ℚ K`, so that
`𝓞 K = ℤ[i]`, and write `(α / β)_4` for the quartic power residue symbol
`Ideal.powerResidueSymbolIdeal (Ideal.span {β}) 4 (Ideal.Quotient.mk _ α)` at the principal ideal
`β 𝓞 K`. An element of `ℤ[i]` of odd norm has a unique *primary* associate, congruent to `1`
modulo `(1 + i)³` (`TauCeti.IsPrimaryGaussian`). The law of biquadratic (quartic) reciprocity
states that for primary elements `π₁, π₂ ∈ 𝓞 K`,

`(π₂ / π₁)_4 = (π₁ / π₂)_4 · (-1) ^ (((N π₁ - 1) / 4) * ((N π₂ - 1) / 4))`

(`TauCeti.IsPrimaryGaussian.quartic_reciprocity`). When `π₁` and `π₂` are not coprime, both symbols
vanish, so no coprimality or nonunit hypothesis is required. In coordinates `π₁ = a + b i` and
`π₂ = c + d i`, the parity congruence `(N(a + b i) - 1) / 4 ≡ (a - 1) / 2 (mod 2)` rewrites the
sign as `(-1) ^ (((a - 1) / 2) * ((c - 1) / 2))`
(`TauCeti.IsPrimaryGaussian.quartic_reciprocity_add_mul`), and the sign is `-1` if and only if
both ideal norms are `5` modulo `8`.

## Proof outline

1. **Rational primes against primary primes**
   (`TauCeti.IsPrimaryGaussian.quartic_reciprocity_nat_prime`): for an odd prime `q` and a primary
   prime `π`, `((-1) ^ ((q - 1) / 2) * q / π)_4 = (π / q)_4`.
   * If `q ≡ 1 (mod 4)`, `q = σ(β) β` splits into conjugate primes of norm `q`. The Gauss sum
     power `Φ(π 𝓞 K) = g(χ_π⁻¹, ψ) ^ 4` equals `π σ(π) ^ 3` (`Ideal.stickelbergerPhi_four_eq`),
     and combining `(Φ(π 𝓞 K) / β 𝓞 K)_4 = (q / π)_4` (`Ideal.powerResidueSymbol_stickelbergerPhi`)
     with Galois equivariance under `σ` gives `(q / π)_4 = (π / q)_4`.
   * If `q ≡ 3 (mod 4)`, `q 𝓞 K` stays prime of norm `q²`, and Frobenius `x ↦ x ^ q` on
     `𝓞 K ⧸ q 𝓞 K` acts as complex conjugation `σ`. Comparing `g(χ_π, ψ) ^ (q + 1)` modulo a prime
     over `q` via the Frobenius congruence `g ^ q ≡ χ_π(q) g(χ_π⁻¹)` and via
     `g ^ 4 = π ^ 3 σ(π)` (`Ideal.gaussSum_powerResidueSymbol_four_pow_four_eq_pow_three_mul`)
     gives `(-q / π)_4 = (π / q)_4`.
2. **Rational integers against primary elements**
   (`TauCeti.IsPrimaryGaussian.quartic_reciprocity_intCast`): multiplicativity in both arguments
   and the twist `m * χ₄(m) ≡ 1 (mod 4)` extend step 1 to `(a / π)_4 = (π / a)_4` for every
   `a ≡ 1 (mod 4)` and every primary `π ∈ 𝓞 K`.
3. **Primary primes and general primary elements**
   (`TauCeti.IsPrimaryGaussian.quartic_reciprocity`): an inert primary prime is `-q ≡ 1 (mod 4)`,
   covered by step 2. For two coprime split primary primes `π₁ = a + b i` and `π₂ = c + d i`, the
   congruences `c π₁ ≡ a c + b d (mod π₂)`, `a π₂ ≡ a c + b d (mod π₁)`, and
   `σ(π₁) π₂ ≡ (a d - b c) i (mod a c + b d)` reduce `(π₂ / π₁)_4 (π₁ / π₂)_4⁻¹` to
   rational-denominator symbols and the supplementary laws for `i` and `-1`. Factoring general
   primary elements into primary primes (`TauCeti.IsPrimaryGaussian.exists_multiset_prod_eq`)
   completes the proof.

## Main results

* `Ideal.stickelbergerPhi_four_eq`: `Φ(π 𝓞 K) = π σ(π) ^ 3` for a primary prime `π` of `ℤ[i]` and
  complex conjugation `σ`.
* `TauCeti.IsPrimaryGaussian.quartic_reciprocity_nat_prime`:
  `((-1) ^ ((q - 1) / 2) * q / π)_4 = (π / q)_4` for a primary prime `π` and an odd prime `q`.
* `TauCeti.IsPrimaryGaussian.quartic_reciprocity_intCast`: `(a / π)_4 = (π / a)_4` for primary
  `π ∈ 𝓞 K` and `a : ℤ` with `a ≡ 1 (mod 4)`.
* `TauCeti.IsPrimaryGaussian.quartic_reciprocity`: the law of biquadratic reciprocity for primary
  Gaussian integers.
* `TauCeti.IsPrimaryGaussian.quartic_reciprocity_add_mul`: the coordinate form
  `(π₂ / π₁)_4 = (π₁ / π₂)_4 · (-1) ^ (((a - 1) / 2) * ((c - 1) / 2))`.
* `TauCeti.IsPrimaryGaussian.odd_absNorm_sub_one_div_four_iff`,
  `TauCeti.IsPrimaryGaussian.quartic_reciprocity_of_absNorm_modEq_one`,
  `TauCeti.IsPrimaryGaussian.quartic_reciprocity_of_absNorm_modEq_five`: the mod-`8` sign rules.

## References

* C. F. Gauss, *Theoria residuorum biquadraticorum, Commentatio secunda*.
* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 9, §§7–9.
* N. Xu, *Reciprocity Laws*, §5, Theorem 5.8 and Propositions 5.10–5.13.
* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §4, for the residue
  symbol of `Φ(P)` at a second prime.
-/

public section

open NumberField IsCyclotomicExtension.Rat

namespace Ideal

open TauCeti

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

/-- Two ring endomorphisms of `𝓞 K = ℤ[i]` that both cube every fourth root of unity agree on all
of `𝓞 K`, and their composite is the identity. -/
private theorem apply_eq_of_pow_three_of_four {σ₁ σ₂ : 𝓞 K →+* 𝓞 K}
    (h₁ : ∀ x : 𝓞 K, x ^ 4 = 1 → σ₁ x = x ^ 3) (h₂ : ∀ x : 𝓞 K, x ^ 4 = 1 → σ₂ x = x ^ 3)
    (x : 𝓞 K) : σ₁ x = σ₂ x ∧ σ₁ (σ₁ x) = x := by
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
  have h4 := hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hsq := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  obtain ⟨a, b, rfl⟩ := hζ.exists_intCast_add_intCast_mul_toInteger_eq (by decide) x
  have hi₁ : σ₁ hζ.toInteger = -hζ.toInteger := by
    rw [h₁ _ h4, pow_succ, hsq, neg_one_mul]
  have hi₂ : σ₂ hζ.toInteger = -hζ.toInteger := by
    rw [h₂ _ h4, pow_succ, hsq, neg_one_mul]
  exact ⟨by simp [hi₁, hi₂], by simp [hi₁]⟩

/-- **The Gauss sum power `Φ(P)` of a primary prime of `ℤ[i]`.** If `K = ℚ(i)`, `P = π 𝓞 K` is a
maximal ideal with `π` primary, and `σ` is a ring endomorphism of `𝓞 K` cubing the fourth roots of
unity (complex conjugation), then `Φ(P) = π σ(π) ^ 3`, where `Φ(P) = g(χ_P⁻¹, ψ) ^ 4` is the
fourth power of the Gauss sum of the inverse quartic residue character. -/
theorem stickelbergerPhi_four_eq {P : Ideal (𝓞 K)} [P.IsMaximal] {π : 𝓞 K}
    (hπ : P = span {π}) (hπ' : IsPrimaryGaussian π) {σ : 𝓞 K →+* 𝓞 K}
    (hσ : ∀ x : 𝓞 K, x ^ 4 = 1 → σ x = x ^ 3) :
    stickelbergerPhi P 4 = π * σ π ^ 3 := by
  let _ := Ideal.Quotient.field P
  let _ := Fintype.ofFinite (𝓞 K ⧸ P)
  obtain ⟨γ, _, hτ⟩ := exists_gal_apply_eq_pow_three_of_four (K := K)
  let τ : 𝓞 K ≃+* 𝓞 K := MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) γ
  have hτ' : ∀ x : 𝓞 K, x ^ 4 = 1 → (τ : 𝓞 K →+* 𝓞 K) x = x ^ 3 := hτ
  have hP : (absNorm P).Coprime 4 := hπ ▸ hπ'.absNorm_span_singleton_coprime_four
  let f : 𝓞 K →+* ℂ := (Classical.arbitrary (K →+* ℂ)).comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f :=
    (Classical.arbitrary (K →+* ℂ)).injective.comp (FaithfulSMul.algebraMap_injective _ _)
  have hψ := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (𝓞 K ⧸ P)
  -- `(χ⁻¹) ^ 3 = χ` since `χ ^ 4 = 1`, so `f (τ (Φ(P))) = g(χ, ψ) ^ 4 = f (π ^ 3 * τ π)`.
  have hχ : (powerResidueSymbol P 4)⁻¹ ^ 3 = powerResidueSymbol P 4 := by
    have h4 : powerResidueSymbol P 4 ^ 4 = 1 := by
      simpa only [orderOf_powerResidueSymbol hP] using pow_orderOf_eq_one (powerResidueSymbol P 4)
    calc (powerResidueSymbol P 4)⁻¹ ^ 3
        = (powerResidueSymbol P 4)⁻¹ ^ 3 * powerResidueSymbol P 4 ^ 4 := by rw [h4, mul_one]
      _ = powerResidueSymbol P 4 := by group
  have h₁ := apply_stickelbergerPhi_eq_gaussSum_pow P hP (by norm_num) τ hτ hf hψ
  rw [hχ, gaussSum_powerResidueSymbol_four_pow_four_eq_pow_three_mul hπ hπ' hτ' hf hψ] at h₁
  have h₂ := congrArg (τ : 𝓞 K →+* 𝓞 K) (hf h₁)
  have hinv := (apply_eq_of_pow_three_of_four hτ' hσ (stickelbergerPhi P 4)).2
  have hinvπ := apply_eq_of_pow_three_of_four hτ' hσ π
  simp only [RingEquiv.coe_toRingHom] at h₂ hinv hinvπ
  rw [hinv, map_mul, map_pow, hinvπ.2, hinvπ.1] at h₂
  rw [mul_comm]; exact h₂

end Ideal

namespace TauCeti

open Ideal

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

/-! ### Quartic reciprocity between a primary element and a rational integer -/

/-- A primary element has nonzero norm, so it is nonzero. -/
private theorem IsPrimaryGaussian.ne_zero {x : 𝓞 K} (hx : IsPrimaryGaussian x) : x ≠ 0 := by
  rintro rfl
  exact Int.not_odd_zero (by simpa using hx.odd_norm)

omit [IsCyclotomicExtension {4} ℚ K] in
/-- When `π` is prime and does not divide `x`, the principal ideals `(π)` and `(x)` are coprime. -/
private theorem isCoprime_span_of_prime_of_not_dvd {π x : 𝓞 K} (hp : Prime π) (h : ¬ π ∣ x) :
    IsCoprime (span {π}) (span {x}) := by
  have : (span {π}).IsMaximal :=
    ((span_singleton_prime hp.ne_zero).mpr hp).isMaximal (by simpa using hp.ne_zero)
  by_contra hncop
  rw [isCoprime_iff_sup_eq] at hncop
  have heq := IsMaximal.eq_of_le ‹_› hncop le_sup_left
  exact h (mem_span_singleton.mp
    (heq.symm ▸ (le_sup_right : span {x} ≤ _) (mem_span_singleton_self x)))

/-- The split case `q ≡ 1 (mod 4)` of `quartic_reciprocity_nat_prime`: `q = τ(β) β` factors into
conjugate primes of norm `q`, and `(Φ(π) / β)_4 = (q / π)_4` pairs with Galois equivariance. -/
private theorem quartic_reciprocity_nat_prime_split {π : 𝓞 K} (hπ : IsPrimaryGaussian π)
    (hp : Prime π) {q : ℕ} (hq : q.Prime) (hq1 : q % 4 = 1) (hndvd : ¬ π ∣ (q : 𝓞 K)) :
    powerResidueSymbolIdeal (span {π}) 4 (Ideal.Quotient.mk _ (q : 𝓞 K)) =
      powerResidueSymbolIdeal (span {(q : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) := by
  have : (span {π}).IsMaximal :=
    ((span_singleton_prime hp.ne_zero).mpr hp).isMaximal (by simpa using hp.ne_zero)
  obtain ⟨γ, _, hτ⟩ := exists_gal_apply_eq_pow_three_of_four (K := K)
  let τ : 𝓞 K ≃+* 𝓞 K := MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) γ
  have hτ' : ∀ x : 𝓞 K, x ^ 4 = 1 → (τ : 𝓞 K →+* 𝓞 K) x = x ^ 3 := hτ
  obtain ⟨β, hβ, hqβ, hNβ⟩ := exists_natCast_eq_mul_of_mod_four_ne_three hτ' hq (by omega)
  simp only [RingEquiv.coe_toRingHom] at hqβ
  let P' : Ideal (𝓞 K) := span {β}
  have : P'.IsMaximal := (isPrime_of_irreducible_absNorm (hNβ ▸ hq)).isMaximal
    (by simpa [P'] using hβ)
  have hP'4 : (absNorm P').Coprime 4 := by
    rw [hNβ]
    exact (Nat.odd_iff.mpr (by omega) : Odd q).coprime_two_right.pow_right 2
  have hPP' : (absNorm (span {π})).Coprime (absNorm P') := by
    rw [hNβ]
    exact absNorm_coprime_of_isCoprime_span_natCast (isCoprime_span_of_prime_of_not_dvd hp hndvd)
  have hinvπ : τ (τ π) = π := by
    simpa only [RingEquiv.coe_toRingHom] using (Ideal.apply_eq_of_pow_three_of_four hτ' hτ' π).2
  -- `(q / π)_4 = (Φ(π) / P')_4 = (π / P')_4 * (τ π / P')_4 ^ 3`.
  have hΦ := powerResidueSymbol_stickelbergerPhi (span {π}) P' hP'4 hPP' (by norm_num)
  rw [hNβ, stickelbergerPhi_four_eq rfl hπ hτ'] at hΦ
  simp only [RingEquiv.coe_toRingHom, map_mul, map_pow] at hΦ
  -- Conjugate `(τ π / P')_4`: `τ ((τ π / P')_4) = (π / τ P')_4`, and `τ` cubes fourth roots.
  have hu : IsUnit (Ideal.Quotient.mk P' (τ π)) := by
    rw [Ideal.Quotient.isUnit_mk_iff, ← isCoprime_iff_sup_eq]
    have hc : IsCoprime (span {τ π}) (span {(q : 𝓞 K)}) := by
      rw [isCoprime_span_singleton_iff, ← map_natCast τ]
      exact ((isCoprime_span_singleton_iff _ _).mp
        (isCoprime_span_of_prime_of_not_dvd hp hndvd)).map (τ : 𝓞 K →+* 𝓞 K)
    rw [hqβ, ← span_singleton_mul_span_singleton] at hc
    exact hc.of_mul_right_right
  have hmap := map_powerResidueSymbol P' (n := 4) τ (τ π)
  rw [hτ _ (powerResidueSymbol_pow_eq_one hP'4 hu.ne_zero), hinvπ] at hmap
  have hmapβ : P'.map τ = span {τ β} := by rw [map_span, Set.image_singleton]
  rw [← hΦ, hqβ, ← span_singleton_mul_span_singleton,
    powerResidueSymbolIdeal_mul_right (by simpa using τ.map_ne_zero_iff.mpr hβ) (by simpa using hβ),
    ← hmapβ, powerResidueSymbolIdeal_of_isMaximal, powerResidueSymbolIdeal_of_isMaximal, ← hmap,
    mul_comm]

/-- Modulo an inert prime `q ≡ 3 (mod 4)`, Frobenius `x ↦ x ^ q` acts as complex conjugation `τ`,
so `(π ^ 3 * τ π) ^ ((q + 1) / 4) ≡ N(π) * (π / q)_4 (mod q)`. -/
private theorem mk_pow_three_mul_conj_pow_inert {q : ℕ} (hq : q.Prime) (hq3 : q % 4 = 3)
    {τ : 𝓞 K →+* 𝓞 K} (hτ : ∀ x : 𝓞 K, x ^ 4 = 1 → τ x = x ^ 3) {π : 𝓞 K}
    [(span {(q : 𝓞 K)}).IsMaximal] [Fact q.Prime] [CharP (𝓞 K ⧸ span {(q : 𝓞 K)}) q]
    (hπq : Ideal.Quotient.mk (span {(q : 𝓞 K)}) π ≠ 0) :
    let P' := span {(q : 𝓞 K)}
    Ideal.Quotient.mk P' ((π ^ 3 * τ π) ^ ((q + 1) / 4)) =
      (absNorm (span {π}) : 𝓞 K ⧸ P') *
        Ideal.Quotient.mk P' (powerResidueSymbol P' 4 (Ideal.Quotient.mk P' π)) := by
  intro P'
  -- First show `τ π ≡ π ^ q (mod q)` in coordinates `π = a + b i`.
  have hfrob : Ideal.Quotient.mk P' (τ π) = Ideal.Quotient.mk P' π ^ q := by
    have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
    obtain ⟨a, b, rfl⟩ := hζ.exists_intCast_add_intCast_mul_toInteger_eq (by decide) π
    have hi4 := hζ.toInteger_isPrimitiveRoot.pow_eq_one
    have hisq := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
    have hτi : τ hζ.toInteger = -hζ.toInteger := by
      rw [hτ _ hi4, pow_succ, hisq, neg_one_mul]
    set j : 𝓞 K ⧸ P' := Ideal.Quotient.mk P' hζ.toInteger
    have hjq : j ^ q = -j := by
      obtain ⟨k, hk⟩ : ∃ k, q = 4 * k + 3 := ⟨q / 4, by omega⟩
      have hj4 : j ^ 4 = 1 := by rw [← map_pow, hi4, map_one]
      have hj2 : j ^ 2 = -1 := by rw [← map_pow, hisq, map_neg, map_one]
      rw [hk, pow_add, pow_mul, hj4, one_pow, one_mul, pow_succ, hj2, neg_one_mul]
    have hint (n : ℤ) : (n : 𝓞 K ⧸ P') ^ q = n := by
      rw [← map_intCast (ZMod.castHom dvd_rfl (𝓞 K ⧸ P')) n, ← map_pow, ZMod.pow_card]
    simp only [map_add, map_mul, map_intCast, hτi, map_neg]
    rw [add_pow_char, mul_pow, hint, hint, hjq, mul_neg]
  have hN' : absNorm P' = q ^ 2 := absNorm_span_natCast_four q
  have hcop4 : (absNorm P').Coprime 4 := by
    rw [hN']
    exact ((Nat.odd_iff.mpr (by omega) : Odd q).coprime_two_right.pow_left 2).pow_right 2
  have hexp : (3 + q) * ((q + 1) / 4) = (q + 1) + (absNorm P' - 1) / 4 := by
    rw [hN']
    obtain ⟨k, rfl⟩ : ∃ k, q = 4 * k + 3 := ⟨q / 4, by omega⟩
    have h1 : (4 * k + 3 + 1) / 4 = k + 1 := by omega
    have hsq : (4 * k + 3) ^ 2 - 1 = 4 * (4 * k ^ 2 + 6 * k + 2) :=
      Nat.sub_eq_of_eq_add (by ring)
    rw [h1, hsq, Nat.mul_div_cancel_left _ (by decide : 0 < 4)]
    ring
  have hnorm : Ideal.Quotient.mk P' π ^ (q + 1) = (absNorm (span {π}) : 𝓞 K ⧸ P') := by
    rw [pow_succ', ← hfrob, ← map_mul, ← intCast_norm_eq_mul_of_four hτ,
      ← RingOfIntegers.natCast_absNorm_span_singleton_of_four, Int.cast_natCast, map_natCast]
  rw [map_pow, map_mul, map_pow, hfrob, ← pow_add, ← pow_mul, hexp, pow_add, hnorm,
    ← mk_powerResidueSymbol hcop4 hπq]

/-- Frobenius evaluation of `g(χ_P, ψ) ^ (q + 1)` modulo an ideal `I` of characteristic
`q ≡ 3 (mod 4)` lying over `P' = q 𝓞 K`. -/
private theorem gaussSum_pow_inert_eq {P P' : Ideal (𝓞 K)} [P.IsMaximal]
    [Fintype (𝓞 K ⧸ P)] (hP : (absNorm P).Coprime 4) {q : ℕ} [Fact q.Prime] (hq3 : q % 4 = 3)
    (hqP : (q : 𝓞 K) ∉ P) {R : Type*} [CommRing R] [IsDomain R]
    {f : 𝓞 K →+* R} (hf : Function.Injective f) {ψ : AddChar (𝓞 K ⧸ P) R} (hψ : ψ.IsPrimitive)
    (I : Ideal R) [CharP (R ⧸ I) q] (hI : I.comap f = P') :
    let ρ := quotientMap I f hI.ge
    Ideal.Quotient.mk I (gaussSum ((powerResidueSymbol P 4).ringHomComp f) ψ) ^ (q + 1) =
      (absNorm P : R ⧸ I) *
        ρ (Ideal.Quotient.mk P' (powerResidueSymbol P 4 (Ideal.Quotient.mk P (-(q : 𝓞 K))))) := by
  intro ρ
  let _ := Ideal.Quotient.field P
  set πI := Ideal.Quotient.mk I
  set χ := (powerResidueSymbol P 4).ringHomComp f
  have hord : orderOf χ = 4 := by rw [MulChar.orderOf_ringHomComp hf, orderOf_powerResidueSymbol hP]
  have hχ1 : χ ≠ 1 := by rw [Ne, ← orderOf_eq_one_iff, hord]; decide
  have h4 : powerResidueSymbol P 4 ^ 4 = 1 := by
    simpa only [orderOf_powerResidueSymbol hP] using pow_orderOf_eq_one (powerResidueSymbol P 4)
  have hχ3 : powerResidueSymbol P 4 ^ 3 = (powerResidueSymbol P 4)⁻¹ := by
    calc powerResidueSymbol P 4 ^ 3
        = powerResidueSymbol P 4 ^ 4 * (powerResidueSymbol P 4)⁻¹ := by group
      _ = (powerResidueSymbol P 4)⁻¹ := by rw [h4, one_mul]
  have hχq : (χ.ringHomComp πI) ^ q = (χ⁻¹).ringHomComp πI := by
    obtain ⟨k, rfl⟩ : ∃ k, q = 4 * k + 3 := ⟨q / 4, by omega⟩
    rw [MulChar.ringHomComp_pow, MulChar.ringHomComp_pow, pow_add, pow_mul, h4, one_pow, one_mul,
      hχ3, MulChar.ringHomComp_inv]
  have huq : IsUnit (q : 𝓞 K ⧸ P) := by
    have hne : (q : 𝓞 K ⧸ P) ≠ 0 := by
      rw [← map_natCast (Ideal.Quotient.mk P), Ne, Ideal.Quotient.eq_zero_iff_mem]
      exact hqP
    exact hne.isUnit
  have hg : πI (gaussSum χ ψ) = gaussSum (χ.ringHomComp πI) (πI.toMonoidHom.compAddChar ψ) := by
    simp [gaussSum, MulChar.ringHomComp_apply]
  have hg' : πI (gaussSum (χ ^ 3) ψ) =
      gaussSum ((χ⁻¹).ringHomComp πI) (πI.toMonoidHom.compAddChar ψ) := by
    have h3 : χ ^ 3 = χ⁻¹ := by rw [MulChar.ringHomComp_pow, hχ3, MulChar.ringHomComp_inv]
    simp [h3, gaussSum, MulChar.ringHomComp_apply]
  -- `gbar ^ q = χ(q) * g(χ⁻¹, ψ)` by `gaussSum_frob` and `gaussSum_mulShift_eq`.
  have hfrob : πI (gaussSum χ ψ) ^ q =
      πI (f (powerResidueSymbol P 4 (q : 𝓞 K ⧸ P))) * πI (gaussSum (χ ^ 3) ψ) := by
    rw [hg, gaussSum_frob, hχq, AddChar.pow_mulShift, ← huq.unit_spec, gaussSum_mulShift_eq, ← hg']
    congr 1
    rw [← MulChar.ringHomComp_inv, inv_inv, MulChar.ringHomComp_apply, MulChar.ringHomComp_apply,
      huq.unit_spec]
  have hprod := congrArg πI (gaussSum_mul_gaussSum_pow_orderOf_sub_one hχ1 hψ)
  rw [hord, ← Nat.card_eq_fintype_card, ← absNorm_eq_natCard, map_mul, map_mul, map_natCast]
    at hprod
  simp only [Nat.reduceSub] at hprod
  have hmkf (z : 𝓞 K) : πI (f z) = ρ (Ideal.Quotient.mk P' z) := rfl
  rw [pow_succ', mul_comm _ (πI (gaussSum χ ψ) ^ q), hfrob, mul_assoc,
    mul_comm (πI (gaussSum (χ ^ 3) ψ)), hprod]
  simp only [χ, MulChar.ringHomComp_apply]
  rw [← mul_assoc, mul_comm _ (absNorm P : R ⧸ I)]
  congr 1
  rw [← map_mul, ← map_mul, ← map_mul, ← map_natCast (Ideal.Quotient.mk P),
    ← map_one (Ideal.Quotient.mk P), ← map_neg, ← map_mul, mul_neg_one, hmkf]

omit [IsCyclotomicExtension {4} ℚ K] in
/-- Every maximal ideal `P'` of `𝓞 K` lies under a prime ideal `I` of `integralClosure ℤ ℂ` via
an injective ring homomorphism `f : 𝓞 K →+* integralClosure ℤ ℂ`. -/
private theorem exists_prime_integralClosure_over_maximal (P' : Ideal (𝓞 K)) [P'.IsMaximal] :
    ∃ (f : 𝓞 K →+* integralClosure ℤ ℂ) (_ : Function.Injective f)
      (I : Ideal (integralClosure ℤ ℂ)), I.IsMaximal ∧ I.comap f = P' := by
  let f : 𝓞 K →+* integralClosure ℤ ℂ :=
    (Classical.arbitrary (K →+* ℂ)).toIntAlgHom.mapIntegralClosure.toRingHom
  have hf : Function.Injective f := AlgHom.mapIntegralClosure_injective
    (f := (Classical.arbitrary (K →+* ℂ)).toIntAlgHom) (RingHom.injective _)
  let _ := f.toAlgebra
  have : IsScalarTower ℤ (𝓞 K) (integralClosure ℤ ℂ) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  have : Algebra.IsIntegral (𝓞 K) (integralClosure ℤ ℂ) :=
    ⟨fun x ↦ (integralClosure.isIntegral x).tower_top⟩
  obtain ⟨I, hI, hIP'⟩ := exists_ideal_over_maximal_of_isIntegral P'
    (((RingHom.injective_iff_ker_eq_bot _).mp hf).trans_le bot_le)
  exact ⟨f, hf, I, hI, hIP'⟩

/-- The inert case `q ≡ 3 (mod 4)` of `quartic_reciprocity_nat_prime`: compare `g ^ (q + 1)` from
Frobenius with `(g ^ 4) ^ ((q + 1) / 4) = (π ^ 3 * τ π) ^ ((q + 1) / 4)` modulo a prime over `q`. -/
private theorem quartic_reciprocity_nat_prime_inert {π : 𝓞 K} (hπ : IsPrimaryGaussian π)
    (hp : Prime π) {q : ℕ} (hq : q.Prime) (hq3 : q % 4 = 3) (hndvd : ¬ π ∣ (q : 𝓞 K)) :
    powerResidueSymbolIdeal (span {π}) 4 (Ideal.Quotient.mk _ (-(q : 𝓞 K))) =
      powerResidueSymbolIdeal (span {(q : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) := by
  let P := span {π}
  let P' := span {(q : 𝓞 K)}
  have : P.IsMaximal :=
    ((span_singleton_prime hp.ne_zero).mpr hp).isMaximal (by simpa using hp.ne_zero)
  have : P'.IsMaximal :=
    ((span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr
      (prime_natCast_of_mod_four_eq_three hq hq3)).isMaximal (by simpa using hq.ne_zero)
  let _ := Ideal.Quotient.field P
  let _ := Fintype.ofFinite (𝓞 K ⧸ P)
  have := Fact.mk hq
  obtain ⟨γ, _, hτ⟩ := exists_gal_apply_eq_pow_three_of_four (K := K)
  let τ : 𝓞 K →+* 𝓞 K := (MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) γ : 𝓞 K →+* 𝓞 K)
  have hτ' : ∀ x : 𝓞 K, x ^ 4 = 1 → τ x = x ^ 3 := hτ
  obtain ⟨ψ, hψ⟩ := exists_primitive_addChar_integralClosure (𝓞 K ⧸ P)
  obtain ⟨f, hf, I, hI, hIP'⟩ := exists_prime_integralClosure_over_maximal P'
  let ρ := quotientMap I f hIP'.ge
  have : CharP (𝓞 K ⧸ P') q := (CharP.charP_iff_prime_eq_zero hq).mpr
    ((map_natCast (Ideal.Quotient.mk P') q).symm.trans
      (Ideal.Quotient.eq_zero_iff_mem.mpr (mem_span_singleton_self _)))
  have : CharP (integralClosure ℤ ℂ ⧸ I) q := CharP.of_ringHom_of_ne_zero ρ q hq.ne_zero
  have hP4 := hπ.absNorm_span_singleton_coprime_four
  have hP'4 : (absNorm P').Coprime 4 := (absNorm_span_natCast_four (K := K) q).symm ▸
    (((Nat.odd_iff.mpr (by omega) : Odd q).coprime_two_right.pow_left 2).pow_right 2)
  have hqP : (q : 𝓞 K) ∉ P := by rwa [mem_span_singleton]
  have hcop := isCoprime_span_of_prime_of_not_dvd hp hndvd
  have hπq : Ideal.Quotient.mk P' π ≠ 0 := fun h0 ↦ IsPrime.ne_top' (by
    have hle := (span_singleton_le_iff_mem _).mpr (Ideal.Quotient.eq_zero_iff_mem.mp h0)
    exact (sup_eq_right.mpr hle).symm.trans (isCoprime_iff_sup_eq.mp hcop))
  -- Compare the two evaluations of `gbar ^ (q + 1)` in the domain `R ⧸ I`.
  have h₁ := gaussSum_pow_inert_eq hP4 hq3 hqP hf hψ I hIP'
  have h₂ : Ideal.Quotient.mk I (gaussSum ((powerResidueSymbol P 4).ringHomComp f) ψ) ^ (q + 1) =
      (absNorm P : integralClosure ℤ ℂ ⧸ I) *
        ρ (Ideal.Quotient.mk P' (powerResidueSymbol P' 4 (Ideal.Quotient.mk P' π))) := by
    have hk : q + 1 = 4 * ((q + 1) / 4) := by omega
    have hmkf (z : 𝓞 K) : Ideal.Quotient.mk I (f z) = ρ (Ideal.Quotient.mk P' z) := rfl
    rw [hk, ← map_pow, pow_mul,
      gaussSum_powerResidueSymbol_four_pow_four_eq_pow_three_mul rfl hπ hτ' hf hψ, ← map_pow, hmkf,
      mk_pow_three_mul_conj_pow_inert hq hq3 hτ' hπq, map_mul, map_natCast]
  have hN0 : (absNorm P : integralClosure ℤ ℂ ⧸ I) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff _ q]
    exact hq.coprime_iff_not_dvd.mp (absNorm_coprime_of_isCoprime_span_natCast hcop).symm
  have hnq0 : Ideal.Quotient.mk P (-(q : 𝓞 K)) ≠ 0 := by
    rwa [map_neg, neg_ne_zero, Ne, Ideal.Quotient.eq_zero_iff_mem]
  rw [powerResidueSymbolIdeal_of_isMaximal, powerResidueSymbolIdeal_of_isMaximal]
  exact eq_of_pow_eq_one_of_mk_eq IsPrime.ne_top' hP'4
    (powerResidueSymbol_pow_eq_one hP4 hnq0) (powerResidueSymbol_pow_eq_one hP'4 hπq)
    (quotientMap_injective' hIP'.le (mul_left_cancel₀ hN0 (h₁.symm.trans h₂)))

/-- **Quartic reciprocity between a primary prime and an odd rational prime.** Let `K = ℚ(i)`, let
`π` be a primary prime of `𝓞 K = ℤ[i]`, and let `q` be an odd rational prime. Then
`((-1) ^ ((q - 1) / 2) * q / π)_4 = (π / q)_4`, the symbols being taken at the principal ideals
`π 𝓞 K` and `q 𝓞 K`. If `π` divides `q`, both symbols vanish. -/
theorem IsPrimaryGaussian.quartic_reciprocity_nat_prime {π : 𝓞 K} (hπ : IsPrimaryGaussian π)
    (hp : Prime π) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    powerResidueSymbolIdeal (span {π}) 4
        (Ideal.Quotient.mk _ ((-1) ^ ((q - 1) / 2) * (q : 𝓞 K))) =
      powerResidueSymbolIdeal (span {(q : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) := by
  by_cases hπq : π ∣ (q : 𝓞 K)
  · have h₁ : ¬ IsCoprime (span {(-1) ^ ((q - 1) / 2) * (q : 𝓞 K)}) (span {π}) := by
      rw [isCoprime_iff_sup_eq,
        sup_eq_right.mpr (span_singleton_le_span_singleton.mpr (dvd_mul_of_dvd_right hπq _))]
      exact ((span_singleton_prime hp.ne_zero).mpr hp).ne_top
    have h₂ : ¬ IsCoprime (span {π}) (span {(q : 𝓞 K)}) := by
      rw [isCoprime_iff_sup_eq, sup_eq_left.mpr (span_singleton_le_span_singleton.mpr hπq)]
      exact ((span_singleton_prime hp.ne_zero).mpr hp).ne_top
    rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr h₁,
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr h₂]
  have hmod : q % 4 = 1 ∨ q % 4 = 3 := by
    have := Nat.odd_iff.mp (hq.odd_of_ne_two hq2)
    omega
  rcases hmod with hq1 | hq3
  · have heven : Even ((q - 1) / 2) := ⟨q / 4, by omega⟩
    rw [heven.neg_one_pow, one_mul]
    exact quartic_reciprocity_nat_prime_split hπ hp hq hq1 hπq
  · have hodd' : Odd ((q - 1) / 2) := ⟨q / 4, by omega⟩
    rw [hodd'.neg_one_pow, neg_one_mul]
    exact quartic_reciprocity_nat_prime_inert hπ hp hq hq3 hπq

/-- Twisted rational-integer reciprocity at a primary prime `π`: for every odd integer `m`,
`((m * χ₄(m)) / π)_4 = (π / m)_4`. -/
private theorem quartic_reciprocity_mul_χ₄_prime {π : 𝓞 K} (hπ : IsPrimaryGaussian π)
    (hp : Prime π) {m : ℤ} (hm : Odd m) :
    powerResidueSymbolIdeal (span {π}) 4
        (Ideal.Quotient.mk _ (((m * ZMod.χ₄ m : ℤ) : 𝓞 K))) =
      powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) := by
  induction m using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact (Int.not_odd_zero hm).elim
  | h₂ m hu =>
    have hm' : span {(m : 𝓞 K)} = ⊤ := span_singleton_eq_top.mpr (hu.map (Int.castRingHom (𝓞 K)))
    rw [hm', powerResidueSymbolIdeal_top]
    rcases Int.isUnit_iff.mp hu with rfl | rfl
    · simp
    · have h1 : ((-1 : ℤ) * ZMod.χ₄ ((-1 : ℤ) : ZMod 4) : ℤ) = 1 := by decide
      rw [h1, Int.cast_one, map_one, map_one]
  | h₃ m p hm0 hp' ih =>
    obtain ⟨hpodd, hmodd⟩ := Int.odd_mul.mp hm
    have hpm : (p * m) * ZMod.χ₄ ((p * m : ℤ) : ZMod 4) =
        (p * ZMod.χ₄ p) * (m * ZMod.χ₄ m) := by rw [Int.cast_mul, map_mul]; ring
    have hpval : powerResidueSymbolIdeal (span {π}) 4
        (Ideal.Quotient.mk _ (((p * ZMod.χ₄ p : ℤ) : 𝓞 K))) =
        powerResidueSymbolIdeal (span {(p : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) := by
      obtain ⟨q, hpq⟩ : ∃ q : ℕ, p.natAbs = q ∧ (p = q ∨ p = -q) := ⟨p.natAbs, rfl, Int.natAbs_eq p⟩
      have hq : q.Prime := hpq.1 ▸ Int.prime_iff_natAbs_prime.mp hp'
      have hq2 : q ≠ 2 := by
        rintro rfl
        have := Int.odd_iff.mp hpodd
        rcases hpq.2 with rfl | rfl <;> omega
      have hmod : q % 4 = 1 ∨ q % 4 = 3 := by
        have := Nat.odd_iff.mp (hq.odd_of_ne_two hq2); omega
      have hsign : (q : ℤ) * ZMod.χ₄ ((q : ℤ) : ZMod 4) = (-1) ^ ((q - 1) / 2) * (q : ℤ) := by
        rcases hmod with hq1 | hq3
        · have he : Even ((q - 1) / 2) := ⟨q / 4, by omega⟩
          simp [ZMod.χ₄_nat_one_mod_four hq1, he.neg_one_pow]
        · have ho : Odd ((q - 1) / 2) := ⟨q / 4, by omega⟩
          simp [ZMod.χ₄_nat_three_mod_four hq3, ho.neg_one_pow]
      rcases hpq.2 with rfl | rfl
      · rw [hsign, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
        exact hπ.quartic_reciprocity_nat_prime hp hq hq2
      · have hneg : (-(q : ℤ)) * ZMod.χ₄ ((-(q : ℤ) : ℤ) : ZMod 4) =
            (q : ℤ) * ZMod.χ₄ ((q : ℤ) : ZMod 4) := by
          rw [Int.cast_neg, ZMod.χ₄_neg, neg_mul_neg]
        rw [hneg, hsign, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
          Int.cast_neg, Int.cast_natCast, span_singleton_neg]
        exact hπ.quartic_reciprocity_nat_prime hp hq hq2
    rw [hpm, Int.cast_mul, map_mul, map_mul, hpval, ih hmodd, Int.cast_mul,
      ← span_singleton_mul_span_singleton,
      powerResidueSymbolIdeal_mul_right (by simpa using hp'.ne_zero) (by simpa using hm0)]

/-- A multiset product of primary elements is primary. -/
private theorem IsPrimaryGaussian.multiset_prod {s : Multiset (𝓞 K)}
    (hs : ∀ q ∈ s, Prime q ∧ IsPrimaryGaussian q) : IsPrimaryGaussian s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons q t iht =>
    rw [Multiset.prod_cons]
    exact (hs q (Multiset.mem_cons_self q t)).2.mul
      (iht fun r hr ↦ hs r (Multiset.mem_cons_of_mem hr))

/-- **Quartic reciprocity between a primary element and a rational integer.** Let `K = ℚ(i)`, let
`π` be a primary element of `𝓞 K = ℤ[i]`, and let `a` be a rational integer with `a ≡ 1 (mod 4)`.
Then `(a / π)_4 = (π / a)_4`, the symbols being taken at the principal ideals `π 𝓞 K` and `a 𝓞 K`.
Here `π` may be composite or `1`, and `a` may be negative; if `a` and `π` are not coprime, both
symbols vanish. -/
theorem IsPrimaryGaussian.quartic_reciprocity_intCast {π : 𝓞 K} (hπ : IsPrimaryGaussian π)
    {a : ℤ} (ha : a ≡ 1 [ZMOD 4]) :
    powerResidueSymbolIdeal (span {π}) 4 (Ideal.Quotient.mk _ (a : 𝓞 K)) =
      powerResidueSymbolIdeal (span {(a : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) := by
  have haodd : Odd a := Int.odd_iff.mpr (by simp only [Int.ModEq] at ha; omega)
  obtain ⟨s, hs, rfl⟩ := hπ.exists_multiset_prod_eq
  clear hπ
  induction s using Multiset.induction_on with
  | empty =>
    rw [Multiset.prod_zero, span_singleton_one, powerResidueSymbolIdeal_top, map_one, map_one]
  | cons q s ih =>
    obtain ⟨hp, hq⟩ := hs q (Multiset.mem_cons_self q s)
    have hs' : ∀ r ∈ s, Prime r ∧ IsPrimaryGaussian r :=
      fun r hr ↦ hs r (Multiset.mem_cons_of_mem hr)
    have hsprod := IsPrimaryGaussian.multiset_prod hs'
    have hqa := quartic_reciprocity_mul_χ₄_prime hq hp haodd
    rw [ZMod.χ₄_int_one_mod_four ha, mul_one] at hqa
    rw [Multiset.prod_cons, ← span_singleton_mul_span_singleton,
      powerResidueSymbolIdeal_mul_right (by simpa using hp.ne_zero)
        (by simpa using hsprod.ne_zero),
      hqa, ih hs', map_mul, map_mul]

/-! ### The law of biquadratic reciprocity -/

/-- Reciprocity between an arbitrary odd rational integer `m` and a primary `ξ = x + y i`:
`(m / ξ)_4 = (-1) ^ (((m - 1) / 2) * ((x - 1) / 2)) * (ξ / m)_4`, read in `K`. -/
private theorem quartic_reciprocity_intCast_odd {ζ : K} {hζ : IsPrimitiveRoot ζ 4} {x y m : ℤ}
    (hξ : IsPrimaryGaussian ((x : 𝓞 K) + (y : 𝓞 K) * hζ.toInteger)) (hm : Odd m) :
    ((powerResidueSymbolIdeal (span {(x : 𝓞 K) + (y : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ (m : 𝓞 K)) : 𝓞 K) : K) =
      (-1) ^ (((m - 1) / 2) * ((x - 1) / 2)) *
        ((powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4
          (Ideal.Quotient.mk _ ((x : 𝓞 K) + (y : 𝓞 K) * hζ.toInteger)) : 𝓞 K) : K) := by
  have hcase : m % 4 = 1 ∨ m % 4 = 3 := by have := Int.odd_iff.mp hm; omega
  rcases hcase with h1 | h3
  · have hm' : m ≡ 1 [ZMOD 4] := h1
    have heven : Even ((m - 1) / 2) := ⟨m / 4, by omega⟩
    rw [hξ.quartic_reciprocity_intCast hm', (heven.mul_right _).neg_one_zpow, one_mul]
  · have hnm : -m ≡ 1 [ZMOD 4] := by simp only [Int.ModEq]; omega
    have hmod : (x - 1) / 2 ≡ ((m - 1) / 2) * ((x - 1) / 2) [ZMOD 2] := by
      obtain ⟨k, rfl⟩ : ∃ k, m = 4 * k + 3 := ⟨m / 4, by omega⟩
      have hdiv : (4 * k + 3 - 1) / 2 = 2 * k + 1 := by omega
      rw [hdiv]
      exact Int.modEq_iff_dvd.mpr ⟨k * ((x - 1) / 2), by ring⟩
    have hsplit : (m : 𝓞 K) = (-1) * ((-m : ℤ) : 𝓞 K) := by push_cast; ring
    conv_lhs => rw [hsplit]
    rw [map_mul, map_mul, RingOfIntegers.coe_eq_algebraMap, map_mul,
      ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap,
      hξ.powerResidueSymbolIdeal_mk_neg_one, hξ.quartic_reciprocity_intCast hnm,
      Int.cast_neg, span_singleton_neg, zpow_eq_zpow_of_modEq (neg_one_sq : (-1 : K) ^ 2 = 1) hmod]

/-- The supplementary law for `i` at an arbitrary odd rational integer `m`:
`(i / m)_4 = (-1) ^ ((m ^ 2 - 1) / 8)`, read in `K`. -/
private theorem powerResidueSymbolIdeal_span_intCast_mk_toInteger_odd {ζ : K}
    (hζ : IsPrimitiveRoot ζ 4) {m : ℤ} (hm : Odd m) :
    ((powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4
        (Ideal.Quotient.mk _ hζ.toInteger) : 𝓞 K) : K) = (-1) ^ ((m ^ 2 - 1) / 8) := by
  wlog hm1 : m ≡ 1 [ZMOD 4] generalizing m
  · have h := this hm.neg (by obtain ⟨k, rfl⟩ := hm; simp only [Int.ModEq] at hm1 ⊢; omega)
    rwa [Int.cast_neg, span_singleton_neg, neg_sq] at h
  rw [hζ.powerResidueSymbolIdeal_span_intCast_mk_toInteger hm1]
  refine zpow_eq_zpow_of_modEq (n := 2) (by norm_num) ?_
  obtain ⟨k, rfl⟩ : ∃ k, m = 4 * k + 1 := ⟨m / 4, by simp only [Int.ModEq] at hm1; omega⟩
  have h1 : (4 * k + 1 - 1) / 4 = k := by omega
  have h2 : (4 * k + 1) ^ 2 - 1 = 8 * (2 * k ^ 2 + k) := by ring
  rw [h1, h2, Int.mul_ediv_cancel_left _ (by norm_num)]
  exact Int.modEq_iff_dvd.mpr ⟨k ^ 2, by ring⟩

/-- The coordinates of a primary Gaussian integer `a + b i` satisfy `Odd a` and `Even b`. -/
private theorem odd_and_even_of_isPrimaryGaussian {ζ : K} (hζ : IsPrimitiveRoot ζ 4)
    {a b : ℤ} (h : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) :
    Odd a ∧ Even b := by
  rw [hζ.isPrimaryGaussian_add_mul_iff] at h
  simp only [Int.ModEq] at h
  exact ⟨Int.odd_iff.mpr (by omega), Int.even_iff.mpr (by omega)⟩

/-- For primary `π = a + b i` with `gcd(a, b) = 1`, `(a / π)_4 = (-1) ^ (((a - 1) / 2) ^ 2 +
(a ^ 2 - 1) / 8)`. -/
private theorem quartic_reciprocity_self_coord {ζ : K} {hζ : IsPrimitiveRoot ζ 4} {a b : ℤ}
    (hπ : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) (hab : IsCoprime a b) :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ (a : 𝓞 K)) : 𝓞 K) : K) =
      (-1) ^ (((a - 1) / 2) ^ 2 + (a ^ 2 - 1) / 8) := by
  have haodd : Odd a := (odd_and_even_of_isPrimaryGaussian hζ hπ).1
  have hmk : Ideal.Quotient.mk (span {(a : 𝓞 K)}) ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger) =
      Ideal.Quotient.mk (span {(a : 𝓞 K)}) ((b : 𝓞 K) * hζ.toInteger) := by
    rw [Ideal.Quotient.eq, add_sub_cancel_right]
    exact mem_span_singleton_self _
  rw [quartic_reciprocity_intCast_odd hπ haodd, ← sq, hmk, map_mul, map_mul,
    RingOfIntegers.coe_eq_algebraMap, map_mul, ← RingOfIntegers.coe_eq_algebraMap,
    ← RingOfIntegers.coe_eq_algebraMap, map_intCast (Ideal.Quotient.mk (span {(a : 𝓞 K)})),
    powerResidueSymbolIdeal_intCast_four hab.symm, RingOfIntegers.coe_eq_algebraMap, map_one,
    one_mul, powerResidueSymbolIdeal_span_intCast_mk_toInteger_odd hζ haodd,
    ← zpow_add₀ (by norm_num)]

/-- The mod-`2` congruence collecting the five sign exponents in Xu's reduction of biquadratic
reciprocity into `((a - 1) / 2) * ((c - 1) / 2)`. -/
private theorem quartic_reciprocity_exponent_modEq {ζ : K} {hζ : IsPrimitiveRoot ζ 4}
    {a b c d : ℤ}
    (hπ₁ : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger))
    (hπ₂ : IsPrimaryGaussian ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger)) :
    let e := a * c + b * d
    (((c - 1) / 2) ^ 2 + (c ^ 2 - 1) / 8) + (((a - 1) / 2) ^ 2 + (a ^ 2 - 1) / 8) +
        ((e - 1) / 2 * ((c - 1) / 2 + (a - 1) / 2) + (e ^ 2 - 1) / 8) ≡
      ((a - 1) / 2) * ((c - 1) / 2) [ZMOD 2] := by
  intro e
  rw [hζ.isPrimaryGaussian_add_mul_iff] at hπ₁ hπ₂
  simp only [Int.ModEq] at hπ₁ hπ₂
  have hdiv1 (k : ℤ) :
      ((4 * k + 1) - 1) / 2 = 2 * k ∧ ((4 * k + 1) ^ 2 - 1) / 8 = 2 * k ^ 2 + k := by
    have hsq : (4 * k + 1) ^ 2 - 1 = 8 * (2 * k ^ 2 + k) := by ring
    exact ⟨by omega, hsq ▸ Int.mul_ediv_cancel_left _ (by norm_num)⟩
  have hdiv3 (k : ℤ) :
      ((4 * k + 3) - 1) / 2 = 2 * k + 1 ∧ ((4 * k + 3) ^ 2 - 1) / 8 = 2 * k ^ 2 + 3 * k + 1 := by
    have hsq : (4 * k + 3) ^ 2 - 1 = 8 * (2 * k ^ 2 + 3 * k + 1) := by ring
    exact ⟨by omega, hsq ▸ Int.mul_ediv_cancel_left _ (by norm_num)⟩
  refine (ZMod.intCast_eq_intCast_iff _ _ 2).mp ?_
  rcases hπ₁ with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨k₁, rfl⟩ : ∃ k, a = 4 * k + 1 := ⟨a / 4, by omega⟩
    obtain ⟨l₁, rfl⟩ : ∃ l, b = 4 * l := ⟨b / 4, by omega⟩
    rcases hπ₂ with ⟨hc, hd⟩ | ⟨hc, hd⟩
    · obtain ⟨k₂, rfl⟩ : ∃ k, c = 4 * k + 1 := ⟨c / 4, by omega⟩
      obtain ⟨l₂, rfl⟩ : ∃ l, d = 4 * l := ⟨d / 4, by omega⟩
      have he : e = 4 * (4 * k₁ * k₂ + k₁ + k₂ + 4 * l₁ * l₂) + 1 := by dsimp [e]; ring
      rw [(hdiv1 k₁).1, (hdiv1 k₁).2, (hdiv1 k₂).1, (hdiv1 k₂).2, he, (hdiv1 _).1, (hdiv1 _).2]
      push_cast; generalize (k₁ : ZMod 2) = x₁, (k₂ : ZMod 2) = x₂, (l₁ : ZMod 2) = y₁,
        (l₂ : ZMod 2) = y₂; revert x₁ x₂ y₁ y₂; decide
    · obtain ⟨k₂, rfl⟩ : ∃ k, c = 4 * k + 3 := ⟨c / 4, by omega⟩
      obtain ⟨l₂, rfl⟩ : ∃ l, d = 4 * l + 2 := ⟨d / 4, by omega⟩
      have he : e = 4 * (4 * k₁ * k₂ + 3 * k₁ + k₂ + 4 * l₁ * l₂ + 2 * l₁) + 3 := by dsimp [e]; ring
      rw [(hdiv1 k₁).1, (hdiv1 k₁).2, (hdiv3 k₂).1, (hdiv3 k₂).2, he, (hdiv3 _).1, (hdiv3 _).2]
      push_cast; generalize (k₁ : ZMod 2) = x₁, (k₂ : ZMod 2) = x₂, (l₁ : ZMod 2) = y₁,
        (l₂ : ZMod 2) = y₂; revert x₁ x₂ y₁ y₂; decide
  · obtain ⟨k₁, rfl⟩ : ∃ k, a = 4 * k + 3 := ⟨a / 4, by omega⟩
    obtain ⟨l₁, rfl⟩ : ∃ l, b = 4 * l + 2 := ⟨b / 4, by omega⟩
    rcases hπ₂ with ⟨hc, hd⟩ | ⟨hc, hd⟩
    · obtain ⟨k₂, rfl⟩ : ∃ k, c = 4 * k + 1 := ⟨c / 4, by omega⟩
      obtain ⟨l₂, rfl⟩ : ∃ l, d = 4 * l := ⟨d / 4, by omega⟩
      have he : e = 4 * (4 * k₁ * k₂ + k₁ + 3 * k₂ + 4 * l₁ * l₂ + 2 * l₂) + 3 := by dsimp [e]; ring
      rw [(hdiv3 k₁).1, (hdiv3 k₁).2, (hdiv1 k₂).1, (hdiv1 k₂).2, he, (hdiv3 _).1, (hdiv3 _).2]
      push_cast; generalize (k₁ : ZMod 2) = x₁, (k₂ : ZMod 2) = x₂, (l₁ : ZMod 2) = y₁,
        (l₂ : ZMod 2) = y₂; revert x₁ x₂ y₁ y₂; decide
    · obtain ⟨k₂, rfl⟩ : ∃ k, c = 4 * k + 3 := ⟨c / 4, by omega⟩
      obtain ⟨l₂, rfl⟩ : ∃ l, d = 4 * l + 2 := ⟨d / 4, by omega⟩
      have he : e = 4 * (4 * k₁ * k₂ + 3 * k₁ + 3 * k₂ + 4 * l₁ * l₂ + 2 * l₁ + 2 * l₂ + 3) + 1 :=
        by dsimp [e]; ring
      rw [(hdiv3 k₁).1, (hdiv3 k₁).2, (hdiv3 k₂).1, (hdiv3 k₂).2, he, (hdiv1 _).1, (hdiv1 _).2]
      push_cast; generalize (k₁ : ZMod 2) = x₁, (k₂ : ZMod 2) = x₂, (l₁ : ZMod 2) = y₁,
        (l₂ : ZMod 2) = y₂; revert x₁ x₂ y₁ y₂; decide

/-- Since `a π₂ ≡ a c + b d (mod π₁)`, `(a c + b d / π₁)_4 = (a / π₁)_4 * (π₂ / π₁)_4`. -/
private theorem powerResidueSymbolIdeal_add_mul_coord_eq {ζ : K} {hζ : IsPrimitiveRoot ζ 4}
    {a b c d : ℤ}
    (hπ₁ : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) (hab : IsCoprime a b) :
    ((-1 : K) ^ (((a - 1) / 2) ^ 2 + (a ^ 2 - 1) / 8)) *
        ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
          (Ideal.Quotient.mk _ ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger)) : 𝓞 K) : K) =
      ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ (((a * c + b * d : ℤ) : 𝓞 K))) : 𝓞 K) : K) := by
  set π₁ : 𝓞 K := (a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger
  set π₂ : 𝓞 K := (c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger
  have hmk : Ideal.Quotient.mk (span {π₁}) ((a : 𝓞 K) * π₂) =
      Ideal.Quotient.mk (span {π₁}) (((a * c + b * d : ℤ) : 𝓞 K)) := by
    rw [Ideal.Quotient.eq, mem_span_singleton]
    refine ⟨(d : 𝓞 K) * hζ.toInteger, ?_⟩
    dsimp [π₁, π₂]; push_cast
    linear_combination (-(b * d : 𝓞 K)) * hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  rw [← quartic_reciprocity_self_coord hπ₁ hab, RingOfIntegers.coe_eq_algebraMap,
    RingOfIntegers.coe_eq_algebraMap, ← map_mul, ← map_mul, ← map_mul, hmk,
    ← RingOfIntegers.coe_eq_algebraMap]

/-- Modulo `e = a c + b d`, `τ(π₁) π₂ ≡ (a d - b c) i`, evaluating `(e / π₂)_4 * (e / τ π₁)_4`. -/
private theorem powerResidueSymbolIdeal_mul_conj_dot_eq {ζ : K} {hζ : IsPrimitiveRoot ζ 4}
    {a b c d : ℤ} {τ : 𝓞 K ≃+* 𝓞 K} (hτ : ∀ x : 𝓞 K, x ^ 4 = 1 → τ x = x ^ 3)
    (hπ₁ : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger))
    (hπ₂ : IsPrimaryGaussian ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger))
    (hef : IsCoprime (a * d - b * c) (a * c + b * d)) :
    let e := a * c + b * d
    ((powerResidueSymbolIdeal (span {(c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ (e : 𝓞 K)) : 𝓞 K) : K) *
      ((powerResidueSymbolIdeal (span {τ ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)}) 4
        (Ideal.Quotient.mk _ (e : 𝓞 K)) : 𝓞 K) : K) =
      (-1) ^ ((e - 1) / 2 * ((c - 1) / 2 + (a - 1) / 2) + (e ^ 2 - 1) / 8) := by
  intro e
  set i := hζ.toInteger
  set π₁ : 𝓞 K := (a : 𝓞 K) + (b : 𝓞 K) * i
  set π₂ : 𝓞 K := (c : 𝓞 K) + (d : 𝓞 K) * i
  have hisq : i ^ 2 = -1 := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  have heodd : Odd e :=
    ((odd_and_even_of_isPrimaryGaussian hζ hπ₁).1.mul
      (odd_and_even_of_isPrimaryGaussian hζ hπ₂).1).add_even
      ((odd_and_even_of_isPrimaryGaussian hζ hπ₁).2.mul_right d)
  have hτπ₁ : τ π₁ = (a : 𝓞 K) + ((-b : ℤ) : 𝓞 K) * i := by
    have hτi : τ i = -i := by
      rw [hτ _ hζ.toInteger_isPrimitiveRoot.pow_eq_one, pow_succ, hisq, neg_one_mul]
    simp [π₁, hτi]
  have hτπ₁' : IsPrimaryGaussian ((a : 𝓞 K) + ((-b : ℤ) : 𝓞 K) * i) :=
    hτπ₁ ▸ hπ₁.map τ.toRingHom
  have hmk : Ideal.Quotient.mk (span {(e : 𝓞 K)}) (τ π₁ * π₂) =
      Ideal.Quotient.mk (span {(e : 𝓞 K)}) (((a * d - b * c : ℤ) : 𝓞 K) * i) := by
    rw [hτπ₁, Ideal.Quotient.eq, mem_span_singleton]
    exact ⟨1, by dsimp [e, π₂]; push_cast; linear_combination (-(b * d : 𝓞 K)) * hisq⟩
  rw [hτπ₁, quartic_reciprocity_intCast_odd hπ₂ heodd, quartic_reciprocity_intCast_odd hτπ₁' heodd,
    ← hτπ₁, mul_mul_mul_comm, ← zpow_add₀ (by norm_num), ← mul_add,
    RingOfIntegers.coe_eq_algebraMap, ← map_mul, ← map_mul, ← map_mul, mul_comm _ (τ π₁), hmk,
    map_mul, map_mul, map_mul, ← RingOfIntegers.coe_eq_algebraMap,
    ← RingOfIntegers.coe_eq_algebraMap, map_intCast (Ideal.Quotient.mk (span {(e : 𝓞 K)})),
    powerResidueSymbolIdeal_intCast_four hef, RingOfIntegers.coe_eq_algebraMap, map_one, one_mul,
    powerResidueSymbolIdeal_span_intCast_mk_toInteger_odd hζ heodd, ← zpow_add₀ (by norm_num)]

/-- When `π₁ = a + b i` and `π₂ = c + d i` are coprime with `gcd(a, b) = 1`, `e = a c + b d` is a
unit modulo `π₁`, so `(e / τ π₁)_4 * (e / π₁)_4 = 1`. -/
private theorem powerResidueSymbolIdeal_conj_mul_dot_eq_one {ζ : K} {hζ : IsPrimitiveRoot ζ 4}
    {σ : Gal(K/ℚ)} (hσ : galEquivZMod 4 K σ = -1) {a b c d : ℤ} (hab : IsCoprime a b)
    (hcop : IsCoprime ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)
      ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger)) :
    let π₁ : 𝓞 K := (a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger
    let τ : 𝓞 K ≃+* 𝓞 K := MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) σ
    let e : ℤ := a * c + b * d
    ((powerResidueSymbolIdeal (span {τ π₁}) 4 (Ideal.Quotient.mk _ (e : 𝓞 K)) : 𝓞 K) : K) *
      ((powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ (e : 𝓞 K)) : 𝓞 K) : K) = 1 := by
  intro π₁ τ e
  let i := hζ.toInteger
  let π₂ : 𝓞 K := (c : 𝓞 K) + (d : 𝓞 K) * i
  have hisq : i ^ 2 = -1 := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  have haπ₁ : IsCoprime (a : 𝓞 K) π₁ := by
    obtain ⟨u, v, huv⟩ := hab
    have huv' : (u : 𝓞 K) * a + (v : 𝓞 K) * b = 1 := by exact_mod_cast huv
    exact ⟨(u : 𝓞 K) + (v : 𝓞 K) * i, -(v : 𝓞 K) * i,
      by dsimp [π₁, i]; linear_combination -(v * b : 𝓞 K) * hisq + huv'⟩
  have hueπ₁ : IsUnit (e : 𝓞 K ⧸ span {π₁}) := by
    rw [← map_intCast (Ideal.Quotient.mk (span {π₁})), Ideal.Quotient.isUnit_mk_iff,
      ← isCoprime_iff_sup_eq, isCoprime_span_singleton_iff]
    have hrel : (e : 𝓞 K) = (a : 𝓞 K) * π₂ + π₁ * (-(d : 𝓞 K) * i) := by
      dsimp [e, π₁, π₂, i]; push_cast; linear_combination (b * d : 𝓞 K) * hisq
    exact hrel ▸ (haπ₁.mul_left hcop.symm).add_mul_left_left _
  have h := powerResidueSymbolIdeal_map_intCast_mul_eq_one hσ (span {π₁}) hueπ₁
  rw [map_span, Set.image_singleton, ← map_intCast (Ideal.Quotient.mk (span {τ π₁})),
    ← map_intCast (Ideal.Quotient.mk (span {π₁}))] at h
  exact_mod_cast h

/-- Xu's congruence reduction for coprime primary `π₁ = a + b i` and `π₂ = c + d i` when
`gcd(a, b) = gcd(c, d) = gcd(a d - b c, a c + b d) = 1`. -/
private theorem quartic_reciprocity_of_isCoprime_det {ζ : K} {hζ : IsPrimitiveRoot ζ 4}
    {a b c d : ℤ}
    (hπ₁ : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger))
    (hπ₂ : IsPrimaryGaussian ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger))
    (hcop : IsCoprime ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)
      ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger))
    (hab : IsCoprime a b) (hcd : IsCoprime c d)
    (hef : IsCoprime (a * d - b * c) (a * c + b * d)) :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger)) : 𝓞 K) : K) =
      ((powerResidueSymbolIdeal (span {(c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) : 𝓞 K) : K) *
        (-1) ^ (((a - 1) / 2) * ((c - 1) / 2)) := by
  let π₁ : 𝓞 K := (a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger
  let π₂ : 𝓞 K := (c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger
  let e : ℤ := a * c + b * d
  obtain ⟨σ, hσ, hτ⟩ := exists_gal_apply_eq_pow_three_of_four (K := K)
  let τ : 𝓞 K ≃+* 𝓞 K := MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) σ
  have hconj := powerResidueSymbolIdeal_conj_mul_dot_eq_one hσ hab hcop
  let s₁ : K := (-1 : K) ^ (((c - 1) / 2) ^ 2 + (c ^ 2 - 1) / 8)
  let s₂ : K := (-1 : K) ^ (((a - 1) / 2) ^ 2 + (a ^ 2 - 1) / 8)
  let s₃ : K := (-1 : K) ^ ((e - 1) / 2 * ((c - 1) / 2 + (a - 1) / 2) + (e ^ 2 - 1) / 8)
  have hesymm : c * a + d * b = e := by dsimp [e]; ring
  have eq1 : s₁ * ((powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) : 𝓞 K) : K) =
      ((powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ (e : 𝓞 K)) : 𝓞 K) : K) := by
    rw [← hesymm]; exact powerResidueSymbolIdeal_add_mul_coord_eq hπ₂ hcd
  have eq2 : s₂ * ((powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) : 𝓞 K) : K) =
      ((powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ (e : 𝓞 K)) : 𝓞 K) : K) :=
    powerResidueSymbolIdeal_add_mul_coord_eq hπ₁ hab
  have eq3 : ((powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ (e : 𝓞 K)) : 𝓞 K) : K) *
      ((powerResidueSymbolIdeal (span {τ π₁}) 4 (Ideal.Quotient.mk _ (e : 𝓞 K)) : 𝓞 K) : K) =
      s₃ := powerResidueSymbolIdeal_mul_conj_dot_eq (τ := τ) hτ hπ₁ hπ₂ hef
  have hsq (k : ℤ) : ((-1 : K) ^ k) * ((-1 : K) ^ k) = 1 := by
    rw [← zpow_add₀ (by norm_num), ← two_mul, Even.neg_one_zpow ⟨k, two_mul k⟩]
  have hs : s₁ * s₂ * s₃ = (-1 : K) ^ (((a - 1) / 2) * ((c - 1) / 2)) := by
    rw [← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num),
      zpow_eq_zpow_of_modEq (neg_one_sq : (-1 : K) ^ 2 = 1)
        (quartic_reciprocity_exponent_modEq hπ₁ hπ₂)]
  have hE₁ : ((powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ (e : 𝓞 K)) : 𝓞 K) : K) =
      s₃ * (s₁ * ((powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) : 𝓞 K) : K)) := by
    calc ((powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ (e : 𝓞 K)) : 𝓞 K) : K)
        = (s₃ * s₃) * _ := by rw [hsq, one_mul]
      _ = s₃ * (((powerResidueSymbolIdeal (span {π₂}) 4
            (Ideal.Quotient.mk _ (e : 𝓞 K)) : 𝓞 K) : K) *
            (((powerResidueSymbolIdeal (span {τ π₁}) 4
              (Ideal.Quotient.mk _ (e : 𝓞 K)) : 𝓞 K) : K) *
            ((powerResidueSymbolIdeal (span {π₁}) 4
              (Ideal.Quotient.mk _ (e : 𝓞 K)) : 𝓞 K) : K))) :=
          by rw [mul_assoc s₃]; congr 1; rw [← eq3, mul_assoc]
      _ = s₃ * (s₁ * ((powerResidueSymbolIdeal (span {π₂}) 4
            (Ideal.Quotient.mk _ π₁) : 𝓞 K) : K)) := by rw [hconj, mul_one, ← eq1]
  calc ((powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) : 𝓞 K) : K)
      = s₂ * (s₂ * ((powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) : 𝓞 K) : K)) :=
        by rw [← mul_assoc, hsq, one_mul]
    _ = ((powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) : 𝓞 K) : K) *
          (s₁ * s₂ * s₃) := by rw [eq2, hE₁]; ring
    _ = ((powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) : 𝓞 K) : K) *
          (-1) ^ (((a - 1) / 2) * ((c - 1) / 2)) := by rw [hs]

/-- A Gaussian integer `x + y i` whose principal ideal has prime norm satisfies `gcd(x, y) = 1`. -/
private theorem isCoprime_of_prime_absNorm {ζ : K} (hζ : IsPrimitiveRoot ζ 4) {x y : ℤ}
    (hp : (absNorm (span {(x : 𝓞 K) + (y : 𝓞 K) * hζ.toInteger})).Prime) :
    IsCoprime x y := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra h1
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd h1
  have hrx : (r : ℤ) ∣ x := (Int.natCast_dvd_natCast.mpr hrd).trans (Int.gcd_dvd_left x y)
  have hry : (r : ℤ) ∣ y := (Int.natCast_dvd_natCast.mpr hrd).trans (Int.gcd_dvd_right x y)
  obtain ⟨u, rfl⟩ := hrx
  obtain ⟨v, rfl⟩ := hry
  have hr2 : r ^ 2 ∣ absNorm (span {((r * u : ℤ) : 𝓞 K) + ((r * v : ℤ) : 𝓞 K) * hζ.toInteger}) := by
    rw [← Int.natCast_dvd_natCast, RingOfIntegers.natCast_absNorm_span_singleton_of_four,
      hζ.norm_intCast_add_intCast_mul_toInteger_of_four, Nat.cast_pow]
    exact ⟨u ^ 2 + v ^ 2, by ring⟩
  have hrp : r = absNorm (span {((r * u : ℤ) : 𝓞 K) + ((r * v : ℤ) : 𝓞 K) * hζ.toInteger}) :=
    ((Nat.dvd_prime hp).mp ((dvd_pow_self r two_ne_zero).trans hr2)).resolve_left hr.ne_one
  have hle := Nat.le_of_dvd hp.pos hr2
  rw [← hrp] at hle
  nlinarith [hr.two_le]

omit [IsCyclotomicExtension {4} ℚ K] in
/-- If `a d - b c = 0` and the norm `r = a² + b² ≠ 0` divides `a c + b d`, then `a + b i` divides
`c + d i` in `𝓞 K`. -/
private theorem dvd_of_mul_sub_mul_eq_zero {ζ : K} (hζ : IsPrimitiveRoot ζ 4) {a b c d : ℤ}
    {r : ℕ} (hr0 : r ≠ 0) (hr : (r : ℤ) = a ^ 2 + b ^ 2) (hf0 : a * d - b * c = 0)
    (hdvd : (r : ℤ) ∣ a * c + b * d) :
    ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger) ∣ ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger) := by
  obtain ⟨v, hv⟩ := hdvd
  set π' : 𝓞 K := (a : 𝓞 K) - (b : 𝓞 K) * hζ.toInteger
  have hprod2 : π' * ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger) = (r : 𝓞 K) := by
    rw [← Int.cast_natCast, hr]; dsimp [π']; push_cast
    linear_combination -(b ^ 2 : 𝓞 K) * hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  have hπ'0 : π' ≠ 0 := fun h0 ↦ hr0 (Nat.cast_eq_zero.mp (by rw [← hprod2, h0, zero_mul]))
  have hprod1 : π' * ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger) = ((a * c + b * d : ℤ) : 𝓞 K) := by
    have hf0' : ((a * d - b * c : ℤ) : 𝓞 K) = 0 := by exact_mod_cast hf0
    dsimp [π']; push_cast at hf0' ⊢
    linear_combination (-(b * d : 𝓞 K)) * hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one +
      hζ.toInteger * hf0'
  refine ⟨v, mul_left_cancel₀ hπ'0 ?_⟩
  rw [hprod1, hv, Int.cast_mul, Int.cast_natCast, ← mul_assoc, hprod2]

/-- Coordinates of two coprime split primary primes satisfy `gcd(a, b) = gcd(c, d) =
gcd(a d - b c, a c + b d) = 1`, since `(a c + b d)² + (a d - b c)² = p₁ p₂`. -/
private theorem isCoprime_coords_of_prime_norm {ζ : K} (hζ : IsPrimitiveRoot ζ 4) {a b c d : ℤ}
    (hπ₁ : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger))
    (hπ₂ : IsPrimaryGaussian ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger))
    (hp₁ : (absNorm (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger})).Prime)
    (hp₂ : (absNorm (span {(c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger})).Prime)
    (hcop : IsCoprime ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)
      ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger)) :
    IsCoprime a b ∧ IsCoprime c d ∧ IsCoprime (a * d - b * c) (a * c + b * d) := by
  refine ⟨isCoprime_of_prime_absNorm hζ hp₁, isCoprime_of_prime_absNorm hζ hp₂, ?_⟩
  let e := a * c + b * d
  let f := a * d - b * c
  let p₁ := absNorm (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger})
  let p₂ := absNorm (span {(c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger})
  have hN₁ : (p₁ : ℤ) = a ^ 2 + b ^ 2 := by
    rw [RingOfIntegers.natCast_absNorm_span_singleton_of_four,
      hζ.norm_intCast_add_intCast_mul_toInteger_of_four]
  have hbrah : e ^ 2 + f ^ 2 = (p₁ : ℤ) * p₂ := by
    have hN₂ : (p₂ : ℤ) = c ^ 2 + d ^ 2 := by
      rw [RingOfIntegers.natCast_absNorm_span_singleton_of_four,
        hζ.norm_intCast_add_intCast_mul_toInteger_of_four]
    rw [hN₁, hN₂]; dsimp [e, f]; ring
  by_contra hnot
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (mt Int.isCoprime_iff_gcd_eq_one.mpr hnot)
  obtain ⟨u, hu⟩ : (r : ℤ) ∣ f := (Int.natCast_dvd_natCast.mpr hrd).trans (Int.gcd_dvd_left f e)
  obtain ⟨v, hv⟩ : (r : ℤ) ∣ e := (Int.natCast_dvd_natCast.mpr hrd).trans (Int.gcd_dvd_right f e)
  have hr2 : r ^ 2 ∣ p₁ * p₂ := by
    rw [← Int.natCast_dvd_natCast, Nat.cast_pow, Nat.cast_mul, ← hbrah, hu, hv]
    exact ⟨v ^ 2 + u ^ 2, by ring⟩
  have hrp : p₁ = r ∧ p₂ = r := by
    rcases hr.dvd_or_dvd ((dvd_pow_self r two_ne_zero).trans hr2) with h1 | h2
    · have hr1 : r = p₁ := ((Nat.dvd_prime hp₁).mp h1).resolve_left hr.ne_one
      rw [hr1, sq, Nat.mul_dvd_mul_iff_left hp₁.pos] at hr2
      exact ⟨hr1.symm, (((Nat.dvd_prime hp₂).mp hr2).resolve_left hp₁.ne_one).symm.trans hr1.symm⟩
    · have hr1 : r = p₂ := ((Nat.dvd_prime hp₂).mp h2).resolve_left hr.ne_one
      rw [hr1, sq, mul_comm p₁, Nat.mul_dvd_mul_iff_left hp₂.pos] at hr2
      exact ⟨(((Nat.dvd_prime hp₁).mp hr2).resolve_left hp₂.ne_one).symm.trans hr1.symm, hr1.symm⟩
  rw [hrp.1, hrp.2, hu, hv] at hbrah
  have huv1 : v ^ 2 + u ^ 2 = 1 :=
    mul_left_cancel₀ (pow_ne_zero 2 (Nat.cast_ne_zero.mpr hr.ne_zero)) (by linear_combination hbrah)
  have hf_even : Even f :=
    ((odd_and_even_of_isPrimaryGaussian hζ hπ₂).2.mul_left a).sub
      ((odd_and_even_of_isPrimaryGaussian hζ hπ₁).2.mul_right c)
  have hr_odd : Odd (r : ℤ) := by
    rw [← hrp.1, RingOfIntegers.natCast_absNorm_span_singleton_of_four]; exact hπ₁.odd_norm
  obtain ⟨w, rfl⟩ : Even u :=
    (Int.even_mul.mp (hu ▸ hf_even)).resolve_left (Int.not_even_iff_odd.mpr hr_odd)
  have hw0 : w = 0 := by nlinarith [sq_nonneg v, sq_nonneg w]
  have hf0 : f = 0 := by rw [hw0, add_zero, mul_zero] at hu; exact hu
  have hdvd := dvd_of_mul_sub_mul_eq_zero hζ hr.ne_zero (hrp.1 ▸ hN₁) hf0 ⟨v, hv⟩
  have huπ : IsUnit ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger) :=
    isCoprime_self.mp (hcop.of_isCoprime_of_dvd_right hdvd)
  rw [span_singleton_eq_top.mpr huπ, absNorm_top] at hp₁
  exact hp₁.ne_one rfl

/-- Classification of primary primes of `ℤ[i]`: either `N(π)` is prime (split prime), or `π = m`
for a rational integer `m ≡ 1 (mod 4)` with `N(π) = p ^ 2` for an odd prime `p` (inert prime). -/
private theorem isPrimaryGaussian_prime_cases {π : 𝓞 K} (hπ : IsPrimaryGaussian π) (hp : Prime π) :
    (absNorm (span {π})).Prime ∨
      ∃ (m : ℤ) (p : ℕ), m ≡ 1 [ZMOD 4] ∧ Odd p ∧ π = m ∧ absNorm (span {π}) = p ^ 2 := by
  have : (span {π}).IsMaximal :=
    ((span_singleton_prime hp.ne_zero).mpr hp).isMaximal (by simpa using hp.ne_zero)
  obtain ⟨p, n, hn0, hpP, hp', hN⟩ := exists_prime_and_absNorm_eq_pow (span {π})
  have hdvd : p ^ n ∣ p ^ 2 := by
    rw [← hN, ← absNorm_span_natCast_four (K := K) p]
    exact absNorm_dvd_absNorm_of_le ((span_singleton_le_iff_mem _).mpr hpP)
  have hn2 : n ≤ 2 := (Nat.pow_dvd_pow_iff_le_right hp'.one_lt).mp hdvd
  interval_cases n
  · exact Or.inl (by rwa [hN, pow_one])
  · right
    have hpodd : Odd p := by
      have h : Odd (absNorm (span {π})) := by
        rw [absNorm_span_singleton]
        exact Int.natAbs_odd.mpr hπ.odd_norm
      rw [hN, sq] at h
      exact Nat.Odd.of_mul_left h
    obtain ⟨u, hu⟩ : π ∣ (p : 𝓞 K) := mem_span_singleton.mp hpP
    have hu1 : (Algebra.norm ℤ u).natAbs = 1 := by
      have h1 := congrArg (fun z : 𝓞 K ↦ absNorm (span {z})) hu
      rw [absNorm_span_natCast_four, ← span_singleton_mul_span_singleton, map_mul, hN,
        absNorm_span_singleton] at h1
      exact (Nat.mul_eq_left (pow_ne_zero 2 hp'.ne_zero)).mp h1.symm
    have hu' : IsUnit u := by
      rw [← span_singleton_eq_top, ← absNorm_eq_one_iff, absNorm_span_singleton, hu1]
    have hpodd_int : Odd (p : ℤ) := by obtain ⟨k, rfl⟩ := hpodd; exact ⟨k, by push_cast; ring⟩
    set m : ℤ := p * ZMod.χ₄ p
    have hm1 : m ≡ 1 [ZMOD 4] := ZMod.int_mul_χ₄_modEq_one hpodd_int
    have hmod : p % 4 = 1 ∨ p % 4 = 3 := by have := Nat.odd_iff.mp hpodd; omega
    have hunit_m : ∃ v : (𝓞 K)ˣ, (m : 𝓞 K) = (v : 𝓞 K) * π := by
      rcases hmod with h1 | h3
      · refine ⟨hu'.unit, ?_⟩
        simp [m, ZMod.χ₄_nat_one_mod_four h1, hu, mul_comm]
      · refine ⟨-hu'.unit, ?_⟩
        simp [m, ZMod.χ₄_nat_three_mod_four h3, hu, mul_comm]
    obtain ⟨v, hv⟩ := hunit_m
    have hvm : IsPrimaryGaussian ((v : 𝓞 K) * π) := by
      rw [← hv]
      exact isPrimaryGaussian_intCast_iff.mpr hm1
    obtain ⟨w, -, huniq⟩ := existsUnique_unit_mul_isPrimaryGaussian hπ.odd_norm
    have hv1 : v = 1 := (huniq v hvm).trans (huniq 1 (by simpa using hπ)).symm
    rw [hv1, Units.val_one, one_mul] at hv
    exact ⟨m, p, hm1, hpodd, hv.symm, hN⟩

/-- Biquadratic reciprocity for two primary primes `π₁` and `π₂`. -/
private theorem quartic_reciprocity_prime {π₁ π₂ : 𝓞 K} (hπ₁ : IsPrimaryGaussian π₁)
    (hπ₂ : IsPrimaryGaussian π₂) (hp₁ : Prime π₁) (hp₂ : Prime π₂) :
    powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) =
      powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) *
        (-1) ^ ((absNorm (span {π₁}) - 1) / 4 * ((absNorm (span {π₂}) - 1) / 4)) := by
  by_cases hcop : IsCoprime (span {π₂}) (span {π₁})
  swap
  · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hcop,
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr (mt IsCoprime.symm hcop), zero_mul]
  rcases isPrimaryGaussian_prime_cases hπ₁ hp₁ with hN₁ | ⟨m, p, hm1, ⟨k, hk⟩, rfl, hN⟩
  · rcases isPrimaryGaussian_prime_cases hπ₂ hp₂ with hN₂ | ⟨m, p, hm1, ⟨k, hk⟩, rfl, hN⟩
    · have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
      obtain ⟨a, b, rfl⟩ := hζ.exists_intCast_add_intCast_mul_toInteger_eq (by decide) π₁
      obtain ⟨c, d, rfl⟩ := hζ.exists_intCast_add_intCast_mul_toInteger_eq (by decide) π₂
      have hcop' := (isCoprime_span_singleton_iff _ _).mp hcop.symm
      obtain ⟨hab, hcd, hef⟩ := isCoprime_coords_of_prime_norm hζ hπ₁ hπ₂ hN₁ hN₂ hcop'
      have hrec := quartic_reciprocity_of_isCoprime_det hπ₁ hπ₂ hcop' hab hcd hef
      have hmod : (((absNorm (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) - 1) / 4 *
          ((absNorm (span {(c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger}) - 1) / 4) : ℕ) : ℤ) ≡
          ((a - 1) / 2) * ((c - 1) / 2) [ZMOD 2] := by
        rw [Nat.cast_mul, hπ₁.natCast_absNorm_sub_one_div_four,
          hπ₂.natCast_absNorm_sub_one_div_four]
        exact hπ₁.norm_sub_one_div_four.mul hπ₂.norm_sub_one_div_four
      apply RingOfIntegers.coe_injective
      rw [map_mul, map_pow, map_neg, map_one, ← RingOfIntegers.coe_eq_algebraMap,
        ← RingOfIntegers.coe_eq_algebraMap, hrec, ← zpow_natCast,
        zpow_eq_zpow_of_modEq (neg_one_sq : (-1 : K) ^ 2 = 1) hmod]
    · have hsq : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := Nat.sub_eq_of_eq_add (by ring)
      have heven : Even ((absNorm (span {(m : 𝓞 K)}) - 1) / 4 *
          ((absNorm (span {π₁}) - 1) / 4)) := by
        rw [hN, hk, hsq, Nat.mul_div_cancel_left _ (by decide : 0 < 4)]
        exact (Nat.even_mul_succ_self k).mul_right _
      rw [mul_comm ((absNorm (span {π₁}) - 1) / 4), heven.neg_one_pow, mul_one,
        (hπ₁.quartic_reciprocity_intCast hm1).symm]
  · have hsq : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := Nat.sub_eq_of_eq_add (by ring)
    have heven : Even ((absNorm (span {(m : 𝓞 K)}) - 1) / 4 *
        ((absNorm (span {π₂}) - 1) / 4)) := by
      rw [hN, hk, hsq, Nat.mul_div_cancel_left _ (by decide : 0 < 4)]
      exact (Nat.even_mul_succ_self k).mul_right _
    rw [heven.neg_one_pow, mul_one, hπ₂.quartic_reciprocity_intCast hm1]

/-- For primary `x, y ∈ 𝓞 K`, `(N(x y) - 1) / 4` has the parity of
`(N(x) - 1) / 4 + (N(y) - 1) / 4`. -/
private theorem absNorm_mul_sub_one_div_four_even {x y : 𝓞 K} (hx : IsPrimaryGaussian x)
    (hy : IsPrimaryGaussian y) (z : ℕ) :
    ((-1 : 𝓞 K) ^ ((absNorm (span {x * y}) - 1) / 4 * z)) =
      (-1 : 𝓞 K) ^ ((absNorm (span {x}) - 1) / 4 * z) *
        (-1 : 𝓞 K) ^ ((absNorm (span {y}) - 1) / 4 * z) := by
  have hx1 : absNorm (span {x}) ≡ 1 [MOD 4] :=
    absNorm_modEq_one hx.absNorm_span_singleton_coprime_four
  have hy1 : absNorm (span {y}) ≡ 1 [MOD 4] :=
    absNorm_modEq_one hy.absNorm_span_singleton_coprime_four
  obtain ⟨u, hu⟩ : ∃ u, absNorm (span {x}) = 4 * u + 1 :=
    ⟨absNorm (span {x}) / 4, by simp only [Nat.ModEq] at hx1; omega⟩
  obtain ⟨v, hv⟩ : ∃ v, absNorm (span {y}) = 4 * v + 1 :=
    ⟨absNorm (span {y}) / 4, by simp only [Nat.ModEq] at hy1; omega⟩
  have h1 : 4 * u + 1 - 1 = 4 * u := by omega
  have h2 : 4 * v + 1 - 1 = 4 * v := by omega
  have h3 : (4 * u + 1) * (4 * v + 1) - 1 = 4 * (u + v + 2 * (2 * u * v)) :=
    Nat.sub_eq_of_eq_add (by ring)
  have hev : Even (2 * (2 * u * v) * z) := ⟨(2 * u * v) * z, by ring⟩
  rw [← span_singleton_mul_span_singleton, map_mul, hu, hv, h1, h2, h3,
    Nat.mul_div_cancel_left _ (by decide : 0 < 4),
    Nat.mul_div_cancel_left _ (by decide : 0 < 4),
    Nat.mul_div_cancel_left _ (by decide : 0 < 4),
    add_mul, add_mul, pow_add, pow_add, hev.neg_one_pow, mul_one]

/-- **The law of biquadratic (quartic) reciprocity.** Let `K = ℚ(i)`, so that `𝓞 K = ℤ[i]`, and
let `π₁` and `π₂` be primary elements of `𝓞 K`. Then
`(π₂ / π₁)_4 = (π₁ / π₂)_4 · (-1) ^ (((N π₁ - 1) / 4) * ((N π₂ - 1) / 4))`,
where the symbols are the quartic power residue symbols at the principal ideals `π₁ 𝓞 K` and
`π₂ 𝓞 K`, and `N` denotes the absolute ideal norm. Both `π₁` and `π₂` may be composite or `1`; if
they are not coprime, both symbols vanish. -/
theorem IsPrimaryGaussian.quartic_reciprocity {π₁ π₂ : 𝓞 K} (hπ₁ : IsPrimaryGaussian π₁)
    (hπ₂ : IsPrimaryGaussian π₂) :
    powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) =
      powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) *
        (-1) ^ ((absNorm (span {π₁}) - 1) / 4 * ((absNorm (span {π₂}) - 1) / 4)) := by
  have hstep_left {π' : 𝓞 K} (hπ' : IsPrimaryGaussian π') {ρ : 𝓞 K} (hρ : IsPrimaryGaussian ρ)
      (hpρ : Prime ρ) :
      powerResidueSymbolIdeal (span {π'}) 4 (Ideal.Quotient.mk _ ρ) =
        powerResidueSymbolIdeal (span {ρ}) 4 (Ideal.Quotient.mk _ π') *
          (-1) ^ ((absNorm (span {π'}) - 1) / 4 * ((absNorm (span {ρ}) - 1) / 4)) := by
    obtain ⟨s, hs, rfl⟩ := hπ'.exists_multiset_prod_eq
    clear hπ'
    induction s using Multiset.induction_on with
    | empty =>
      rw [Multiset.prod_zero, span_singleton_one, absNorm_top, powerResidueSymbolIdeal_top]
      simp
    | cons q s ih =>
      obtain ⟨hpq, hq⟩ := hs q (Multiset.mem_cons_self q s)
      have hs' := fun x hx ↦ hs x (Multiset.mem_cons_of_mem hx)
      have hs_prim := IsPrimaryGaussian.multiset_prod hs'
      rw [Multiset.prod_cons, absNorm_mul_sub_one_div_four_even hq hs_prim,
        ← span_singleton_mul_span_singleton,
        powerResidueSymbolIdeal_mul_right (by simpa using hpq.ne_zero)
          (by simpa using hs_prim.ne_zero),
        quartic_reciprocity_prime hq hρ hpq hpρ, ih hs', map_mul, map_mul]
      ring
  obtain ⟨t, ht, rfl⟩ := hπ₂.exists_multiset_prod_eq
  clear hπ₂
  induction t using Multiset.induction_on with
  | empty =>
    rw [Multiset.prod_zero, span_singleton_one, absNorm_top, powerResidueSymbolIdeal_top]
    simp
  | cons ρ t ih =>
    obtain ⟨hpρ, hρ⟩ := ht ρ (Multiset.mem_cons_self ρ t)
    have ht' := fun x hx ↦ ht x (Multiset.mem_cons_of_mem hx)
    have ht_prim := IsPrimaryGaussian.multiset_prod ht'
    have hsign := absNorm_mul_sub_one_div_four_even hρ ht_prim ((absNorm (span {π₁}) - 1) / 4)
    simp only [mul_comm _ ((absNorm (span {π₁}) - 1) / 4)] at hsign
    rw [Multiset.prod_cons, hsign, ← span_singleton_mul_span_singleton,
      powerResidueSymbolIdeal_mul_right (by simpa using hpρ.ne_zero)
        (by simpa using ht_prim.ne_zero),
      map_mul, map_mul, hstep_left hπ₁ hρ hpρ, ih ht']
    ring

/-- **Biquadratic reciprocity in coordinates.** Let `K = ℚ(i)` and let `π₁ = a + b i` and
`π₂ = c + d i` be primary elements of `𝓞 K = ℤ[i]`. Then
`(π₂ / π₁)_4 = (π₁ / π₂)_4 · (-1) ^ (((a - 1) / 2) * ((c - 1) / 2))`, read in `K`. Neither
`gcd(a, b) = 1` nor coprimality of `π₁` and `π₂` is required. -/
theorem IsPrimaryGaussian.quartic_reciprocity_add_mul {ζ : K} {hζ : IsPrimitiveRoot ζ 4}
    {a b c d : ℤ}
    (hπ₁ : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger))
    (hπ₂ : IsPrimaryGaussian ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger)) :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger)) : 𝓞 K) : K) =
      ((powerResidueSymbolIdeal (span {(c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) : 𝓞 K) : K) *
        (-1) ^ (((a - 1) / 2) * ((c - 1) / 2)) := by
  have hmod : (((absNorm (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) - 1) / 4 *
      ((absNorm (span {(c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger}) - 1) / 4) : ℕ) : ℤ) ≡
      ((a - 1) / 2) * ((c - 1) / 2) [ZMOD 2] := by
    rw [Nat.cast_mul, hπ₁.natCast_absNorm_sub_one_div_four,
      hπ₂.natCast_absNorm_sub_one_div_four]
    exact hπ₁.norm_sub_one_div_four.mul hπ₂.norm_sub_one_div_four
  rw [hπ₁.quartic_reciprocity hπ₂]
  push_cast
  rw [← zpow_natCast, zpow_eq_zpow_of_modEq (n := 2) (by norm_num) hmod]

/-! ### The mod-`8` sign rules -/

/-- For a primary Gaussian integer `x`, the exponent `(N(x 𝓞 K) - 1) / 4` is odd if and only if
`N(x 𝓞 K) ≡ 5 (mod 8)`. -/
theorem IsPrimaryGaussian.odd_absNorm_sub_one_div_four_iff {x : 𝓞 K} (hx : IsPrimaryGaussian x) :
    Odd ((absNorm (span {x}) - 1) / 4) ↔ absNorm (span {x}) ≡ 5 [MOD 8] := by
  have h1 : absNorm (span {x}) ≡ 1 [MOD 4] :=
    absNorm_modEq_one hx.absNorm_span_singleton_coprime_four
  simp only [Nat.odd_iff, Nat.ModEq] at h1 ⊢
  omega

/-- If `π₁` and `π₂` are primary and `N(π₁ 𝓞 K) ≡ 1 (mod 8)`, the sign in biquadratic reciprocity
is `+1`, so `(π₂ / π₁)_4 = (π₁ / π₂)_4`. -/
theorem IsPrimaryGaussian.quartic_reciprocity_of_absNorm_modEq_one {π₁ π₂ : 𝓞 K}
    (hπ₁ : IsPrimaryGaussian π₁) (hπ₂ : IsPrimaryGaussian π₂)
    (hN : absNorm (span {π₁}) ≡ 1 [MOD 8]) :
    powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) =
      powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) := by
  have heven : Even ((absNorm (span {π₁}) - 1) / 4) := by
    rw [← Nat.not_odd_iff_even, hπ₁.odd_absNorm_sub_one_div_four_iff]
    simp only [Nat.ModEq] at hN ⊢
    omega
  rw [hπ₁.quartic_reciprocity hπ₂, (heven.mul_right _).neg_one_pow, mul_one]

/-- If `π₁` and `π₂` are primary and `N(π₁ 𝓞 K) ≡ N(π₂ 𝓞 K) ≡ 5 (mod 8)`, the sign in biquadratic
reciprocity is `-1`, so `(π₂ / π₁)_4 = -(π₁ / π₂)_4`. -/
theorem IsPrimaryGaussian.quartic_reciprocity_of_absNorm_modEq_five {π₁ π₂ : 𝓞 K}
    (hπ₁ : IsPrimaryGaussian π₁) (hπ₂ : IsPrimaryGaussian π₂)
    (hN₁ : absNorm (span {π₁}) ≡ 5 [MOD 8]) (hN₂ : absNorm (span {π₂}) ≡ 5 [MOD 8]) :
    powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) =
      -powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) := by
  have hodd : Odd ((absNorm (span {π₁}) - 1) / 4 * ((absNorm (span {π₂}) - 1) / 4)) :=
    (hπ₁.odd_absNorm_sub_one_div_four_iff.mpr hN₁).mul
      (hπ₂.odd_absNorm_sub_one_div_four_iff.mpr hN₂)
  rw [hπ₁.quartic_reciprocity hπ₂, hodd.neg_one_pow, mul_neg_one]

section Examples

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 4)

/- The sign in biquadratic reciprocity is `-1` if and only if both primary elements have ideal
norm congruent to `5` modulo `8`. -/
example {π₁ π₂ : 𝓞 K} (hπ₁ : IsPrimaryGaussian π₁) (hπ₂ : IsPrimaryGaussian π₂) :
    ((-1 : 𝓞 K) ^ ((absNorm (span {π₁}) - 1) / 4 * ((absNorm (span {π₂}) - 1) / 4))) = -1 ↔
      absNorm (span {π₁}) ≡ 5 [MOD 8] ∧ absNorm (span {π₂}) ≡ 5 [MOD 8] := by
  have h2 : (1 : 𝓞 K) ≠ -1 := by
    intro h
    exact two_ne_zero (by linear_combination h : (2 : 𝓞 K) = 0)
  rw [← hπ₁.odd_absNorm_sub_one_div_four_iff, ← hπ₂.odd_absNorm_sub_one_div_four_iff,
    ← Nat.odd_mul]
  rcases Nat.even_or_odd ((absNorm (span {π₁}) - 1) / 4 * ((absNorm (span {π₂}) - 1) / 4)) with
    heven | hodd
  · rw [heven.neg_one_pow]
    exact ⟨fun h ↦ absurd h h2, fun h ↦ absurd h (Nat.not_odd_iff_even.mpr heven)⟩
  · rw [hodd.neg_one_pow]
    exact ⟨fun _ ↦ hodd, fun _ ↦ rfl⟩

include hζ

/- For the primary prime `π = 3 + 2i` of norm `13` and `q = 5 ≡ 1 (mod 4)`, the sign in
`quartic_reciprocity_nat_prime` is `+1`, so `(5 / (3 + 2i))_4 = ((3 + 2i) / 5)_4`. -/
example :
    powerResidueSymbolIdeal (span {((3 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ (5 : 𝓞 K)) =
      powerResidueSymbolIdeal (span {(5 : 𝓞 K)}) 4
        (Ideal.Quotient.mk _ (((3 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger)) := by
  have hπ : IsPrimaryGaussian (((3 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger) := by
    rw [hζ.isPrimaryGaussian_add_mul_iff]; decide
  have h := hπ.quartic_reciprocity_intCast (a := 5) (by decide)
  have h5 : ((5 : ℤ) : 𝓞 K) = 5 := Int.cast_ofNat 5
  rwa [h5] at h

/- For the primary elements `π₁ = -1 + 2i` (norm `5 ≡ 5 (mod 8)`) and `π₂ = 3 + 2i`
(norm `13 ≡ 5 (mod 8)`), `(a - 1) / 2 = -1` and `(c - 1) / 2 = 1`, so
`(π₂ / π₁)_4 = -(π₁ / π₂)_4`. -/
example :
    powerResidueSymbolIdeal (span {((-1 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ (((3 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger)) =
      -powerResidueSymbolIdeal (span {((3 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ (((-1 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger)) := by
  have hπ₁ : IsPrimaryGaussian (((-1 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger) := by
    rw [hζ.isPrimaryGaussian_add_mul_iff]; decide
  have hπ₂ : IsPrimaryGaussian (((3 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger) := by
    rw [hζ.isPrimaryGaussian_add_mul_iff]; decide
  refine hπ₁.quartic_reciprocity_of_absNorm_modEq_five hπ₂ ?_ ?_
  · rw [absNorm_span_singleton, hζ.norm_intCast_add_intCast_mul_toInteger_of_four]; decide
  · rw [absNorm_span_singleton, hζ.norm_intCast_add_intCast_mul_toInteger_of_four]; decide

/- For `π₁ = -1 + 2i` (norm `5`) and `π₂ = -3` (norm `9 ≡ 1 (mod 8)`), both `((-3) / π₁)_4` and
`(π₁ / 3)_4 = (π₁ / (-3))_4` equal `-i`, fixing the sign and quotient conventions. -/
example :
    let π₁ := ((-1 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger
    powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ ((-3 : ℤ) : 𝓞 K)) =
        -hζ.toInteger ∧
      powerResidueSymbolIdeal (span {(3 : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π₁) = -hζ.toInteger := by
  intro π₁
  have hπ₁ : IsPrimaryGaussian π₁ := by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide
  have hN : absNorm (span {π₁}) = 5 := by
    rw [absNorm_span_singleton, hζ.norm_intCast_add_intCast_mul_toInteger_of_four]; rfl
  have hprime : (span {π₁}).IsPrime :=
    isPrime_of_irreducible_absNorm (by rw [hN]; exact Nat.prime_five)
  have : (span {π₁}).IsMaximal :=
    hprime.isMaximal fun h ↦ by rw [h, absNorm_bot] at hN; exact absurd hN (by norm_num)
  have hisq := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  have hμ : (-hζ.toInteger) ^ 4 = 1 := by
    linear_combination hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hdvd : π₁ ∣ -hζ.toInteger - ((-3 : ℤ) : 𝓞 K) :=
    ⟨-(1 + hζ.toInteger), by dsimp [π₁]; push_cast; linear_combination (2 : 𝓞 K) * hisq⟩
  have hne : Ideal.Quotient.mk (span {π₁}) ((-3 : ℤ) : 𝓞 K) ≠ 0 := by
    intro h0
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton] at h0
    have hu : IsUnit π₁ := isUnit_of_dvd_unit (by simpa using dvd_add hdvd h0)
      (IsUnit.of_pow_eq_one hμ (by norm_num))
    rw [span_singleton_eq_top.mpr hu, absNorm_top] at hN
    exact absurd hN (by norm_num)
  have hlhs : powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ ((-3 : ℤ) : 𝓞 K)) =
      -hζ.toInteger := by
    rw [powerResidueSymbolIdeal_of_isMaximal,
      powerResidueSymbol_eq_iff (by rw [hN]; decide) hne hμ, hN, pow_one,
      Ideal.Quotient.eq, mem_span_singleton]
    exact hdvd
  refine ⟨hlhs, ?_⟩
  have hspan : span {(3 : 𝓞 K)} = span {((-3 : ℤ) : 𝓞 K)} := by
    rw [Int.cast_neg, Int.cast_ofNat, span_singleton_neg]
  rw [hspan, ← hπ₁.quartic_reciprocity_intCast (by decide), hlhs]

end Examples

end TauCeti
