/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.GaussSum
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.StickelbergerPhi
import Mathlib.NumberTheory.LegendreSymbol.Complex
import Mathlib.NumberTheory.SumTwoSquares
import TauCeti.NumberTheory.GaussSum.Basic
import TauCeti.NumberTheory.LegendreSymbol.Complex
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.RationalResidue
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.SupplementaryLaws
import TauCeti.NumberTheory.NumberField.PrimeIdeal
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Norm
import TauCeti.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.RingTheory.Ideal.Quotient.Coprime
import TauCeti.RingTheory.IntegralClosure.Map

/-!
# The law of biquadratic (quartic) reciprocity

Let `K = ℚ(i)`, given as a number field with `IsCyclotomicExtension {4} ℚ K`, so that
`𝓞 K = ℤ[i]`, and write `(α / β)_4` for the quartic power residue symbol
`Ideal.powerResidueSymbolIdeal (Ideal.span {β}) 4 (Ideal.Quotient.mk _ α)`. For primary elements
`π₁` and `π₂` of `ℤ[i]`, the law of biquadratic reciprocity relates `(π₂ / π₁)_4` and
`(π₁ / π₂)_4` up to a sign determined by their norms (or equivalently by their real parts):

`(π₂ / π₁)_4 = (π₁ / π₂)_4 · (-1) ^ (((N(π₂) - 1) / 4) * ((N(π₁) - 1) / 4))`.

If `π₁` and `π₂` are not coprime, both residue symbols vanish and the equality still holds.

The proof proceeds in three stages:

1. **Primary prime against an odd rational prime `q`**
   (`TauCeti.IsPrimaryGaussian.quartic_reciprocity_natCast_prime`):
   `(((-1) ^ ((q - 1) / 2) * q) / π)_4 = (π / q)_4`.
   When `q ≡ 1 (mod 4)`, `q = β (σ β)` splits in `ℤ[i]` and the identity follows by evaluating the
   Gauss sum power `Φ(π 𝓞 K) = π · (σ π) ^ 3` (`Ideal.stickelbergerPhi_four_eq`) modulo `β 𝓞 K`
   through `Ideal.powerResidueSymbol_stickelbergerPhi`. When `q ≡ 3 (mod 4)`, `Q = q 𝓞 K` is inert
   of norm `q²` and the `(q + 1)`-st power of the quartic Gauss sum modulo a prime of the algebraic
   integers over `Q` is computed in two ways: by the Frobenius congruence in characteristic `q` and
   from `g(χ, ψ) ^ 4 = π ^ 3 σ π`. Multiplicativity in both slots extends this to any primary `π`
   and odd rational integer `m` (`TauCeti.IsPrimaryGaussian.coe_quartic_reciprocity_intCast_of_odd`,
   and in coordinates `TauCeti.IsPrimaryGaussian.quartic_reciprocity_intCast_add_mul_of_odd`), and
   in particular gives `(a / π)_4 = (π / a)_4` for `a ≡ 1 (mod 4)`
   (`TauCeti.IsPrimaryGaussian.quartic_reciprocity_intCast`).
2. **Primary elements with coprime coordinates**: for primary `π₁ = a + b i` and `π₂ = c + d i`
   with `gcd(a, b) = gcd(c, d) = 1`, setting `m = a c + b d` eliminates `(π₂ / π₁)_4` and
   `(π₁ / π₂)_4` against `(m / π₂)_4`, `(m / σ π₁)_4`, `(c / π₂)_4`, and `(a / σ π₁)_4`, which
   reduce by odd-integer reciprocity and `(i / n)_4 = (-1) ^ ((n² - 1) / 8)` to a parity congruence
   on primary coordinates.
3. **General primary elements** (`TauCeti.IsPrimaryGaussian.quartic_reciprocity`): writing each
   primary element as `r · π₀` with `r ≡ 1 (mod 4)` in `ℤ` and `π₀` primary with coprime
   coordinates (`TauCeti.IsPrimaryGaussian.exists_intCast_mul_add_mul_isCoprime`), the rational
   factors cancel by `(r / π)_4 = (π / r)_4` and `(r / s)_4 = 1`.

Together with the supplementary laws for `i` and `-1` in
`TauCeti.NumberTheory.NumberField.Cyclotomic.Four.SupplementaryLaws` and the triviality of the
quartic residue symbol on coprime rational integers in
`TauCeti.NumberTheory.NumberField.Cyclotomic.Four.RationalResidue`, this evaluates the quartic
residue symbol on odd-norm elements of `ℤ[i]` and supplies the reciprocity input for the
supplementary law at the ramified prime `1 + i`.

## Main results

* `Ideal.stickelbergerPhi_four_eq`: `Φ(π 𝓞 K) = π · (σ π) ^ 3` for a primary prime `π` of `ℤ[i]`
  and complex conjugation `σ`.
* `TauCeti.IsPrimaryGaussian.quartic_reciprocity_natCast_prime`:
  `(((-1) ^ ((q - 1) / 2) * q) / π)_4 = (π / q)_4` for a primary prime `π` and an odd rational
  prime `q`.
* `TauCeti.IsPrimaryGaussian.coe_quartic_reciprocity_intCast_of_odd`,
  `TauCeti.IsPrimaryGaussian.quartic_reciprocity_intCast_add_mul_of_odd`:
  `(m / π)_4 = (π / m)_4 · (-1) ^ (((m - 1) / 2) * ((N(π) - 1) / 4))` for primary `π` and an odd
  rational integer `m`, with exponent `((m - 1) / 2) * ((c - 1) / 2)` when `π = c + d i`.
* `TauCeti.IsPrimaryGaussian.quartic_reciprocity_intCast`: `(a / π)_4 = (π / a)_4` for primary `π`
  and a rational integer `a ≡ 1 (mod 4)`.
* `TauCeti.IsPrimaryGaussian.quartic_reciprocity`: the law of biquadratic reciprocity in `𝓞 K`,
  with exponent `((N(π₂ 𝓞 K) - 1) / 4) * ((N(π₁ 𝓞 K) - 1) / 4)`.
* `TauCeti.IsPrimaryGaussian.coe_quartic_reciprocity`: the law of biquadratic reciprocity read in
  `K`, with integer norm exponent `((N(π₂) - 1) / 4) * ((N(π₁) - 1) / 4)`.
* `TauCeti.IsPrimaryGaussian.quartic_reciprocity_add_mul`: the coordinate form
  `(π₂ / π₁)_4 = (π₁ / π₂)_4 · (-1) ^ (((a - 1) / 2) * ((c - 1) / 2))` for primary `π₁ = a + b i`
  and `π₂ = c + d i`.

## References

* N. Xu, *Reciprocity Laws*, §5, Theorem 5.8 and Propositions 5.11–5.13.
* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 9, §§8–9.
* M. C. Relyea, *On finite fields and higher reciprocity*, §4.1, Theorem 4.4.
-/

public section

open NumberField

namespace Ideal

open TauCeti

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

/-- **The Gauss sum power `Φ(P)` of a primary prime of `ℤ[i]`.** If `K = ℚ(i)`, `P = π 𝓞 K` is a
maximal ideal with `π` primary, and `σ` is a ring endomorphism of `𝓞 K` cubing the fourth roots of
unity (that is, complex conjugation), then `Φ(P) = π · (σ π) ^ 3`. -/
theorem stickelbergerPhi_four_eq {P : Ideal (𝓞 K)} [P.IsMaximal] {π : 𝓞 K} (hπ : P = span {π})
    (hπ' : IsPrimaryGaussian π) {σ : 𝓞 K →+* 𝓞 K} (hσ : ∀ x : 𝓞 K, x ^ 4 = 1 → σ x = x ^ 3) :
    stickelbergerPhi P 4 = π * σ π ^ 3 := by
  let _ := Ideal.Quotient.field P
  let _ := Fintype.ofFinite (𝓞 K ⧸ P)
  have hP : (absNorm P).Coprime 4 := hπ ▸ hπ'.absNorm_span_singleton_coprime_four
  have hσ_inv : Function.LeftInverse σ σ := apply_apply_eq_self_of_four hσ
  let ι : K →+* ℂ := Classical.arbitrary _
  let f : 𝓞 K →+* ℂ := ι.comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f := ι.injective.comp RingOfIntegers.coe_injective
  have hfσ : Function.Injective (f.comp σ) := hf.comp hσ_inv.injective
  have hψ := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (𝓞 K ⧸ P)
  -- Conjugation inverts the quartic residue character, identifying `χ_P` with `σ ∘ (· / P)_4`.
  have hχ : (powerResidueSymbol P 4)⁻¹.ringHomComp f =
      (powerResidueSymbol P 4).ringHomComp (f.comp σ) := by
    refine MulChar.ext fun u ↦ ?_
    have hu4 := powerResidueSymbol_pow_eq_one hP u.ne_zero
    have h4 : powerResidueSymbol P 4 * powerResidueSymbol P 4 ^ 3 = 1 :=
      MulChar.ext fun v ↦ by
        rw [MulChar.mul_apply, MulChar.pow_apply_coe, ← pow_succ', MulChar.one_apply_coe,
          powerResidueSymbol_pow_eq_one hP v.ne_zero]
    have hinv : (powerResidueSymbol P 4)⁻¹ u = powerResidueSymbol P 4 u ^ 3 := by
      rw [inv_eq_of_mul_eq_one_right h4, MulChar.pow_apply_coe]
    simp only [MulChar.ringHomComp_apply, RingHom.comp_apply, hinv, hσ _ hu4]
  apply hf
  rw [stickelbergerPhi_prime P hP (by decide) hf hψ, hχ,
    gaussSum_powerResidueSymbol_four_pow_four_eq_pow_three_mul hπ hπ' hσ hfσ hψ,
    RingHom.comp_apply, map_mul, map_pow, hσ_inv π, mul_comm]

end Ideal

namespace TauCeti

open Ideal

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

/-! ### Reciprocity between a primary prime and an odd rational prime -/

/-- Quartic reciprocity between a primary prime `π` and a split rational prime `q ≡ 1 (mod 4)` not
divisible by `π`: `(q / π)_4 = (π / q)_4`. -/
private theorem quartic_reciprocity_natCast_prime_of_mod_four_eq_one {π : 𝓞 K}
    (hπ : IsPrimaryGaussian π) (hp : Prime π) {q : ℕ} (hq : q.Prime) (hq1 : q % 4 = 1)
    (hπq : ¬ π ∣ (q : 𝓞 K)) :
    powerResidueSymbolIdeal (span {π}) 4 (Ideal.Quotient.mk _ (q : 𝓞 K)) =
      powerResidueSymbolIdeal (span {(q : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) := by
  have : Fact q.Prime := ⟨hq⟩
  have hPmax : (span {π}).IsMaximal :=
    ((span_singleton_prime hp.ne_zero).mpr hp).isMaximal (by simpa using hp.ne_zero)
  -- Factor `q = x² + y² = β (τ β)` in `𝓞 K` using complex conjugation `τ`.
  obtain ⟨x, y, hxy⟩ := Nat.Prime.sq_add_sq (p := q) (by omega)
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
  obtain ⟨τ, hτ⟩ := exists_ringEquiv_apply_eq_pow_three_of_four (K := K)
  set β : 𝓞 K := x + y * hζ.toInteger
  have hnorm : Algebra.norm ℤ β = q := by
    have h := hζ.norm_intCast_add_intCast_mul_toInteger_of_four (x : ℤ) (y : ℤ)
    rw [Int.cast_natCast, Int.cast_natCast] at h
    rw [h, ← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_add, hxy]
  have hqβ : (q : 𝓞 K) = β * τ β := by
    simpa only [hnorm, Int.cast_natCast] using intCast_norm_eq_mul_of_four hτ β
  have hNβ : absNorm (span {β}) = q := by
    rw [absNorm_span_singleton, hnorm, Int.natAbs_natCast]
  have hβ0 : span {β} ≠ ⊥ := fun h ↦ hq.ne_zero (by rw [← hNβ, h, absNorm_bot])
  have hτβ0 : span {τ β} ≠ ⊥ := by
    rw [← Set.image_singleton, ← map_span]
    exact (map_eq_bot_iff_of_injective τ.injective).not.mpr hβ0
  have hLmax : (span {β}).IsMaximal :=
    (isPrime_of_irreducible_absNorm (hNβ ▸ hq)).isMaximal hβ0
  have hL4 : (absNorm (span {β})).Coprime 4 := by
    rw [hNβ, Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hq1]
    rfl
  have hPL : (absNorm (span {π})).Coprime (absNorm (span {β})) := by
    refine NumberField.coprime_absNorm_of_absNorm_ne finrank_four fun hN ↦ hπq ?_
    rw [← mem_span_singleton, hNβ.symm, ← hN]
    exact absNorm_mem (span {π})
  -- Apply `powerResidueSymbol_stickelbergerPhi` at `(P, L) = (π 𝓞 K, β 𝓞 K)`.
  have hstick := powerResidueSymbol_stickelbergerPhi (span {π}) (span {β}) hL4 hPL (by decide)
  rw [hNβ, stickelbergerPhi_four_eq rfl hπ (σ := (τ : 𝓞 K →+* 𝓞 K)) hτ, RingHom.coe_coe,
    map_mul, map_pow, map_mul, map_pow] at hstick
  have hττ : ∀ z : 𝓞 K, τ (τ z) = z := apply_apply_eq_self_of_four hτ
  have hmapL : (span {β}).map τ = span {τ β} := by rw [map_span, Set.image_singleton]
  have hconj : powerResidueSymbol (span {β}) 4 (Ideal.Quotient.mk _ (τ π)) ^ 3 =
      powerResidueSymbolIdeal (span {τ β}) 4 (Ideal.Quotient.mk _ π) := by
    by_cases h0 : Ideal.Quotient.mk (span {β}) (τ π) = 0
    · rw [h0, MulChar.map_zero, zero_pow (by decide)]
      have hmem : π ∈ span {τ β} := by
        obtain ⟨u, hu⟩ := mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0)
        exact mem_span_singleton.mpr ⟨τ u, by rw [← map_mul, ← hu, hττ]⟩
      have hncop : ¬ IsCoprime (span {π}) (span {τ β}) := by
        rw [isCoprime_iff_sup_eq,
          sup_eq_right.mpr (span_le.mpr (Set.singleton_subset_iff.mpr hmem)),
          span_singleton_eq_top]
        exact fun hu ↦ hLmax.ne_top (span_singleton_eq_top.mpr (hττ β ▸ hu.map τ))
      exact (powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hncop).symm
    · have hp1 := powerResidueSymbol_pow_eq_one hL4 h0
      rw [← hτ _ hp1, ← powerResidueSymbolIdeal_of_isMaximal, map_powerResidueSymbolIdeal, hmapL,
        hττ]
  rw [← hstick, hconj, ← powerResidueSymbolIdeal_of_isMaximal (span {β}), hqβ,
    ← span_singleton_mul_span_singleton, powerResidueSymbolIdeal_mul_right hβ0 hτβ0]

/-- Modulo an ideal `I` of characteristic `q ≡ 3 (mod 4)` prime to `N P`, the `(q + 1)`-st power of
the quartic Gauss sum `g(χ, ψ)` equals the image of `(-q / P)_4 * N P`. -/
private theorem gaussSum_pow_succ_of_mod_four_eq_three {P : Ideal (𝓞 K)} [P.IsMaximal]
    [Fintype (𝓞 K ⧸ P)] (hP4 : (absNorm P).Coprime 4) {q : ℕ} [Fact q.Prime] (hq3 : q % 4 = 3)
    (hqF : (q : 𝓞 K ⧸ P) ≠ 0) {R : Type*} [CommRing R] [IsDomain R] {f : 𝓞 K →+* R}
    (hf : Function.Injective f) {ψ : AddChar (𝓞 K ⧸ P) R} (hψ : ψ.IsPrimitive)
    (I : Ideal R) [CharP (R ⧸ I) q] :
    let χ := (powerResidueSymbol P 4).ringHomComp f
    (Ideal.Quotient.mk I (gaussSum χ ψ)) ^ (q + 1) =
      Ideal.Quotient.mk I (f (powerResidueSymbol P 4 (Ideal.Quotient.mk P (-(q : 𝓞 K))) *
        absNorm P)) := by
  intro χ
  have hq : q.Prime := Fact.out
  let _ := Ideal.Quotient.field P
  let πI := Ideal.Quotient.mk I
  let χS := χ.ringHomComp πI
  let ψS := πI.toMonoidHom.compAddChar ψ
  have hgS (η : MulChar (𝓞 K ⧸ P) R) : πI (gaussSum η ψ) = gaussSum (η.ringHomComp πI) ψS := by
    simp only [gaussSum, map_sum, map_mul, ψS, MulChar.ringHomComp_apply,
      MonoidHom.coe_compAddChar, Function.comp_apply, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass]
  have hχ4 : powerResidueSymbol P 4 ^ 4 = 1 := by
    simpa [orderOf_powerResidueSymbol hP4] using pow_orderOf_eq_one (powerResidueSymbol P 4)
  have hχSq : χS ^ q = χ⁻¹.ringHomComp πI := by
    have h4 : χS ^ 4 = 1 := by
      rw [MulChar.ringHomComp_pow, MulChar.ringHomComp_pow, hχ4,
        MulChar.ringHomComp_one, MulChar.ringHomComp_one]
    obtain ⟨k, hk⟩ : ∃ k, q = 4 * k + 3 := ⟨q / 4, by omega⟩
    rw [← MulChar.ringHomComp_inv, hk, pow_add, pow_mul, h4, one_pow, one_mul]
    exact (inv_eq_of_mul_eq_one_right (b := χS ^ 3) (by rw [← pow_succ', h4])).symm
  have hg_frob : πI (gaussSum χ ψ) ^ q = χS (q : 𝓞 K ⧸ P) * πI (gaussSum χ⁻¹ ψ) := by
    have hsum : gaussSum χS ψS ^ q = gaussSum (χS ^ q) (ψS ^ q) := by
      rw [gaussSum, gaussSum, sum_pow_char]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [mul_pow, ← MulChar.pow_apply' χS hq.ne_zero, ← pow_apply]
    rw [hgS χ, hsum, hχSq, AddChar.pow_mulShift, ← hqF.isUnit.unit_spec, gaussSum_mulShift_eq,
      ← hgS χ⁻¹, ← MulChar.ringHomComp_inv, inv_inv]
  have hχ_ne : χ ≠ 1 := by
    rw [MulChar.ringHomComp_ne_one_iff hf, Ne, ← orderOf_eq_one_iff, orderOf_powerResidueSymbol hP4]
    decide
  have hg_prod : gaussSum χ ψ * gaussSum χ⁻¹ ψ = χ (-1) * absNorm P := by
    have hneg1 : χ⁻¹ (-1) = χ (-1) := by
      have hχ_inv : χ⁻¹ = χ ^ 3 :=
        inv_eq_of_mul_eq_one_right
          (by rw [← pow_succ', MulChar.ringHomComp_pow, hχ4, MulChar.ringHomComp_one])
      rw [hχ_inv, MulChar.pow_apply' χ (by decide), pow_succ, ← map_pow, neg_one_sq, map_one,
        one_mul]
    rw [← mul_gaussSum_inv_eq_gaussSum χ⁻¹ ψ, hneg1, mul_left_comm,
      gaussSum_mul_gaussSum_eq_card hχ_ne hψ, ← Nat.card_eq_fintype_card, ← absNorm_eq_natCard]
  have hq_neg : χ (q : 𝓞 K ⧸ P) * (χ (-1) * absNorm P) =
      f (powerResidueSymbol P 4 (Ideal.Quotient.mk P (-(q : 𝓞 K))) * absNorm P) := by
    have hmk_q : (q : 𝓞 K ⧸ P) * (-1) = Ideal.Quotient.mk P (-(q : 𝓞 K)) := by simp
    simp only [χ, MulChar.ringHomComp_apply]
    rw [← mul_assoc, ← map_mul, ← map_mul, ← map_natCast f, ← map_mul, hmk_q]
  calc πI (gaussSum χ ψ) ^ (q + 1)
      = χS (q : 𝓞 K ⧸ P) * (πI (gaussSum χ ψ) * πI (gaussSum χ⁻¹ ψ)) := by
        rw [pow_succ, hg_frob]
        ring
    _ = πI (χ (q : 𝓞 K ⧸ P) * (χ (-1) * absNorm P)) := by
        simp only [χS, MulChar.ringHomComp_apply]
        rw [← map_mul, hg_prod, ← map_mul]
    _ = _ := by rw [hq_neg]

/-- Modulo an inert prime `Q = q 𝓞 K` with `q ≡ 3 (mod 4)` not dividing `π`, the `(q + 1) / 4`-th
power of `π ^ 3 * σ π` equals `(π / Q)_4 * N(π 𝓞 K)`. -/
private theorem mk_pow_three_mul_pow_of_mod_four_eq_three {π : 𝓞 K} {q : ℕ} (hq : q.Prime)
    (hq3 : q % 4 = 3) [(span {(q : 𝓞 K)}).IsMaximal]
    (hπQ : Ideal.Quotient.mk (span {(q : 𝓞 K)}) π ≠ 0)
    {σ : 𝓞 K →+* 𝓞 K} (hσ : ∀ x : 𝓞 K, x ^ 4 = 1 → σ x = x ^ 3) :
    (Ideal.Quotient.mk (span {(q : 𝓞 K)}) (π ^ 3 * σ π)) ^ ((q + 1) / 4) =
      Ideal.Quotient.mk (span {(q : 𝓞 K)})
        (powerResidueSymbol (span {(q : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π)) *
        (absNorm (span {π}) : 𝓞 K ⧸ span {(q : 𝓞 K)}) := by
  set Q := span {(q : 𝓞 K)}
  have hNQ : absNorm Q = q ^ 2 := absNorm_span_natCast_four q
  have hQ4 : (absNorm Q).Coprime 4 := by
    refine hNQ ▸ Nat.Coprime.pow_left 2 ?_
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hq3]
    rfl
  have hexp : (3 + q) * ((q + 1) / 4) = (q ^ 2 - 1) / 4 + (q + 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, q = 4 * k + 3 := ⟨q / 4, by omega⟩
    have h1 : (4 * k + 3 + 1) / 4 = k + 1 := by omega
    have hsq : (4 * k + 3) ^ 2 = 4 * (4 * k ^ 2 + 6 * k + 2) + 1 := by ring
    have h2 : ((4 * k + 3) ^ 2 - 1) / 4 = 4 * k ^ 2 + 6 * k + 2 := by rw [hsq]; omega
    rw [h1, h2]
    ring
  have hmk_frob : (Ideal.Quotient.mk Q π) ^ q = Ideal.Quotient.mk Q (σ π) :=
    mk_pow_eq_mk_apply_of_mod_four_eq_three hq hq3 hσ π
  have hNP : (absNorm (span {π}) : 𝓞 K ⧸ Q) =
      Ideal.Quotient.mk Q π * (Ideal.Quotient.mk Q π) ^ q := by
    rw [← map_natCast (Ideal.Quotient.mk Q), ← Int.cast_natCast,
      RingOfIntegers.natCast_absNorm_span_singleton_of_four, intCast_norm_eq_mul_of_four hσ,
      map_mul, hmk_frob]
  calc (Ideal.Quotient.mk Q (π ^ 3 * σ π)) ^ ((q + 1) / 4)
      = ((Ideal.Quotient.mk Q π) ^ (3 + q)) ^ ((q + 1) / 4) := by
        rw [map_mul, map_pow, ← hmk_frob, ← pow_add]
    _ = (Ideal.Quotient.mk Q π) ^ ((q ^ 2 - 1) / 4) *
          (Ideal.Quotient.mk Q π * (Ideal.Quotient.mk Q π) ^ q) := by
        rw [← pow_mul, hexp, pow_add, pow_succ' _ q]
    _ = _ := by rw [← hNQ, ← mk_powerResidueSymbol hQ4 hπQ, hNP]

/-- Comparing the Frobenius evaluation of `g(χ, ψ) ^ (q + 1)` in characteristic `q ≡ 3 (mod 4)`
with `(g(χ, ψ) ^ 4) ^ ((q + 1) / 4)` modulo a prime of `integralClosure ℤ ℂ` over `Q = q 𝓞 K`
equates `(-q / P)_4 · N P` and `(π ^ 3 σ π) ^ ((q + 1) / 4)` in `𝓞 K ⧸ Q`. -/
private theorem mk_powerResidueSymbol_neg_natCast_mul_absNorm_of_mod_four_eq_three
    {π : 𝓞 K} (hπ : IsPrimaryGaussian π) [(span {π}).IsMaximal]
    {q : ℕ} (hq : q.Prime) (hq3 : q % 4 = 3) [(span {(q : 𝓞 K)}).IsMaximal]
    (hqF : (q : 𝓞 K ⧸ span {π}) ≠ 0)
    {σ : 𝓞 K →+* 𝓞 K} (hσ : ∀ x : 𝓞 K, x ^ 4 = 1 → σ x = x ^ 3) :
    Ideal.Quotient.mk (span {(q : 𝓞 K)})
        (powerResidueSymbol (span {π}) 4 (Ideal.Quotient.mk _ (-(q : 𝓞 K)))) *
      (absNorm (span {π}) : 𝓞 K ⧸ span {(q : 𝓞 K)}) =
      (Ideal.Quotient.mk (span {(q : 𝓞 K)}) (π ^ 3 * σ π)) ^ ((q + 1) / 4) := by
  have : Fact q.Prime := ⟨hq⟩
  set P := span {π}
  set Q := span {(q : 𝓞 K)}
  let _ := Ideal.Quotient.field P
  let _ := Fintype.ofFinite (𝓞 K ⧸ P)
  have hP4 : (absNorm P).Coprime 4 := hπ.absNorm_span_singleton_coprime_four
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
  let ρ := quotientMap I f hIQ.ge
  have hρ : Function.Injective ρ := quotientMap_injective' hIQ.le
  have : CharP (integralClosure ℤ ℂ ⧸ I) q := CharP.of_ringHom_of_ne_zero ρ q hq.ne_zero
  have hρ_mk (x : 𝓞 K) : Ideal.Quotient.mk I (f x) = ρ (Ideal.Quotient.mk Q x) :=
    (quotientMap_mk (I := I) (f := f) (H := hIQ.ge)).symm
  have hq4 : 4 * ((q + 1) / 4) = q + 1 := by omega
  apply hρ
  calc ρ (Ideal.Quotient.mk Q (powerResidueSymbol P 4 (Ideal.Quotient.mk P (-(q : 𝓞 K)))) *
          (absNorm P : 𝓞 K ⧸ Q))
      = (Ideal.Quotient.mk I (gaussSum ((powerResidueSymbol P 4).ringHomComp f) ψ)) ^ (q + 1) := by
        rw [← map_natCast (Ideal.Quotient.mk Q), ← map_mul, ← hρ_mk,
          gaussSum_pow_succ_of_mod_four_eq_three hP4 hq3 hqF hf hψ I]
    _ = Ideal.Quotient.mk I (f ((π ^ 3 * σ π) ^ ((q + 1) / 4))) := by
        nth_rw 1 [← hq4]
        rw [pow_mul, ← map_pow,
          gaussSum_powerResidueSymbol_four_pow_four_eq_pow_three_mul rfl hπ hσ hf hψ,
          ← map_pow, ← map_pow]
    _ = _ := by rw [hρ_mk, map_pow, map_pow]

/-- Quartic reciprocity between a primary prime `π` and an inert rational prime `q ≡ 3 (mod 4)` not
divisible by `π`: `(-q / π)_4 = (π / q)_4`. -/
private theorem quartic_reciprocity_natCast_prime_of_mod_four_eq_three {π : 𝓞 K}
    (hπ : IsPrimaryGaussian π) (hp : Prime π) {q : ℕ} (hq : q.Prime) (hq3 : q % 4 = 3)
    (hπq : ¬ π ∣ (q : 𝓞 K)) :
    powerResidueSymbolIdeal (span {π}) 4 (Ideal.Quotient.mk _ (-(q : 𝓞 K))) =
      powerResidueSymbolIdeal (span {(q : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) := by
  set P := span {π}
  set Q := span {(q : 𝓞 K)}
  have hPmax : P.IsMaximal :=
    ((span_singleton_prime hp.ne_zero).mpr hp).isMaximal (by simpa using hp.ne_zero)
  have hQmax : Q.IsMaximal :=
    ((span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr
      (prime_natCast_of_mod_four_eq_three hq hq3)).isMaximal (by simpa using hq.ne_zero)
  let _ := Ideal.Quotient.field Q
  have hP4 : (absNorm P).Coprime 4 := hπ.absNorm_span_singleton_coprime_four
  have hNQ : absNorm Q = q ^ 2 := absNorm_span_natCast_four q
  have hQ4 : (absNorm Q).Coprime 4 := by
    refine hNQ ▸ Nat.Coprime.pow_left 2 ?_
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hq3]
    rfl
  have hPQ : (absNorm P).Coprime (absNorm Q) := by
    refine NumberField.coprime_absNorm_of_absNorm_ne finrank_four fun hN ↦ hπq ?_
    have hmem : (q : 𝓞 K) ^ 2 ∈ P := by simpa [hN, hNQ] using absNorm_mem P
    exact mem_span_singleton.mp (hPmax.isPrime.mem_of_pow_mem 2 hmem)
  have hNq : (absNorm P).Coprime q :=
    (Nat.coprime_pow_right_iff (by decide : 0 < 2) _ _).mp (hNQ ▸ hPQ)
  have hqF : (q : 𝓞 K ⧸ P) ≠ 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P), Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact natCast_notMem_of_coprime_absNorm IsPrime.ne_top' hNq.symm
  have hNPQ : (absNorm P : 𝓞 K ⧸ Q) ≠ 0 := by
    rw [← map_natCast (Ideal.Quotient.mk Q), Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact natCast_notMem_of_coprime_absNorm IsPrime.ne_top' hPQ
  obtain ⟨σ, hσ⟩ := exists_ringHom_apply_eq_pow_three_of_four (K := K)
  have hπQ : Ideal.Quotient.mk Q π ≠ 0 := fun h0 ↦ hNPQ <| by
    rw [← map_natCast (Ideal.Quotient.mk Q), ← Int.cast_natCast,
      RingOfIntegers.natCast_absNorm_span_singleton_of_four, intCast_norm_eq_mul_of_four hσ,
      map_mul, h0, zero_mul]
  have hmk_eq : Ideal.Quotient.mk Q (powerResidueSymbol P 4 (Ideal.Quotient.mk P (-(q : 𝓞 K)))) =
      Ideal.Quotient.mk Q (powerResidueSymbol Q 4 (Ideal.Quotient.mk Q π)) :=
    mul_right_cancel₀ hNPQ
      ((mk_powerResidueSymbol_neg_natCast_mul_absNorm_of_mod_four_eq_three hπ hq hq3 hqF hσ).trans
        (mk_pow_three_mul_pow_of_mod_four_eq_three hq hq3 hπQ hσ))
  have hnegq0 : Ideal.Quotient.mk P (-(q : 𝓞 K)) ≠ 0 := by
    rw [map_neg, map_natCast, neg_ne_zero]
    exact hqF
  rw [powerResidueSymbolIdeal_of_isMaximal, powerResidueSymbolIdeal_of_isMaximal]
  exact eq_of_pow_eq_one_of_mk_eq IsPrime.ne_top' hQ4 (powerResidueSymbol_pow_eq_one hP4 hnegq0)
    (powerResidueSymbol_pow_eq_one hQ4 hπQ) hmk_eq

/-- **Quartic reciprocity between a primary prime and an odd rational prime.** Let `K = ℚ(i)`, so
that `𝓞 K = ℤ[i]`, let `π` be a primary prime of `𝓞 K` (either split or inert), and let `q` be an
odd rational prime. Then `(((-1) ^ ((q - 1) / 2) * q) / π)_4 = (π / q)_4`, the symbols being taken
at the principal ideals `π 𝓞 K` and `q 𝓞 K`. If `π` divides `q`, both sides vanish. -/
theorem IsPrimaryGaussian.quartic_reciprocity_natCast_prime {π : 𝓞 K} (hπ : IsPrimaryGaussian π)
    (hp : Prime π) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    powerResidueSymbolIdeal (span {π}) 4
        (Ideal.Quotient.mk _ ((-1 : 𝓞 K) ^ ((q - 1) / 2) * q)) =
      powerResidueSymbolIdeal (span {(q : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) := by
  by_cases hπq : π ∣ (q : 𝓞 K)
  · have h1 : ¬ IsCoprime (span {(-1 : 𝓞 K) ^ ((q - 1) / 2) * q}) (span {π}) := by
      have hdvd : π ∣ (-1 : 𝓞 K) ^ ((q - 1) / 2) * q := dvd_mul_of_dvd_right hπq _
      rw [isCoprime_iff_sup_eq, sup_eq_right.mpr (span_singleton_le_span_singleton.mpr hdvd)]
      exact ((span_singleton_prime hp.ne_zero).mpr hp).ne_top
    have h2 : ¬ IsCoprime (span {π}) (span {(q : 𝓞 K)}) := by
      rw [isCoprime_iff_sup_eq, sup_eq_left.mpr (span_singleton_le_span_singleton.mpr hπq)]
      exact ((span_singleton_prime hp.ne_zero).mpr hp).ne_top
    rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr h1,
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr h2]
  have hodd : q % 2 = 1 := hq.eq_two_or_odd.resolve_left hq2
  rcases (by omega : q % 4 = 1 ∨ q % 4 = 3) with hq1 | hq3
  · have heven : Even ((q - 1) / 2) := ⟨(q - 1) / 4, by omega⟩
    rw [heven.neg_one_pow, one_mul]
    exact quartic_reciprocity_natCast_prime_of_mod_four_eq_one hπ hp hq hq1 hπq
  · have hodd' : Odd ((q - 1) / 2) := ⟨(q - 3) / 4, by omega⟩
    rw [hodd'.neg_one_pow, neg_one_mul]
    exact quartic_reciprocity_natCast_prime_of_mod_four_eq_three hπ hp hq hq3 hπq

/-! ### Reciprocity between a primary element and an odd rational integer -/

/-- For primary `π`, `(-1 / π)_4 = (-1) ^ ((N(π 𝓞 K) - 1) / 4)`, read in `K`. -/
private theorem coe_powerResidueSymbolIdeal_mk_neg_one {π : 𝓞 K} (hπ : IsPrimaryGaussian π) :
    ((powerResidueSymbolIdeal (span {π}) 4 (Ideal.Quotient.mk _ (-1)) : 𝓞 K) : K) =
      (-1) ^ (((absNorm (span {π}) - 1) / 4 : ℕ) : ℤ) := by
  rw [powerResidueSymbolIdeal_mk_of_pow_eq_one hπ.absNorm_span_singleton_coprime_four (by norm_num),
    zpow_natCast, RingOfIntegers.coe_eq_algebraMap, map_pow, map_neg, map_one]

/-- Reciprocity at a primary prime `π` against a signed odd integer prime `p : ℤ`, read in `K`. -/
private theorem coe_quartic_reciprocity_intCast_prime {π : 𝓞 K} (hπ : IsPrimaryGaussian π)
    (hp : Prime π) {p : ℤ} (hp_int : Prime p) (hp_odd : Odd p) :
    ((powerResidueSymbolIdeal (span {π}) 4 (Ideal.Quotient.mk _ (p : 𝓞 K)) : 𝓞 K) : K) =
      ((powerResidueSymbolIdeal (span {(p : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) : 𝓞 K) : K) *
        (-1) ^ (((p - 1) / 2) * (((absNorm (span {π}) - 1) / 4 : ℕ) : ℤ)) := by
  set N4 : ℤ := (((absNorm (span {π}) - 1) / 4 : ℕ) : ℤ)
  set q : ℕ := p.natAbs
  have hq : q.Prime := Int.prime_iff_natAbs_prime.mp hp_int
  have hq_odd : Odd q := Int.natAbs_odd.mpr hp_odd
  have hq2 : q ≠ 2 := fun h2 ↦ absurd (h2 ▸ hq_odd) (by decide)
  have hnat := hπ.quartic_reciprocity_natCast_prime hp hq hq2
  have hspan : span {(p : 𝓞 K)} = span {(q : 𝓞 K)} := by
    rcases Int.natAbs_eq p with hp_eq | hp_eq
    · rw [hp_eq, Int.cast_natCast]
    · rw [hp_eq, Int.cast_neg, Int.cast_natCast, span_singleton_neg]
  rw [hspan]
  have hq_mod : q % 4 = 1 ∨ q % 4 = 3 := by obtain ⟨k, hk⟩ := hq_odd; omega
  -- Check the two signs `p = ±q` and the two residue classes `q ≡ 1, 3 (mod 4)`.
  have hflip (x : 𝓞 K) (hx : (p : 𝓞 K) = (-1) * x) (ho : Odd ((p - 1) / 2)) :
      ((powerResidueSymbolIdeal (span {π}) 4 (Ideal.Quotient.mk _ (p : 𝓞 K)) : 𝓞 K) : K) =
        ((powerResidueSymbolIdeal (span {π}) 4 (Ideal.Quotient.mk _ x) : 𝓞 K) : K) *
          (-1) ^ (((p - 1) / 2) * N4) := by
    obtain ⟨t, ht⟩ := ho
    rw [hx, map_mul, map_mul, RingOfIntegers.coe_eq_algebraMap, map_mul,
      ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap,
      coe_powerResidueSymbolIdeal_mk_neg_one hπ, mul_comm]
    congr 1
    exact zpow_eq_zpow_of_modEq (n := 2) (by norm_num)
      (Int.modEq_iff_dvd.mpr ⟨t * N4, by rw [ht]; ring⟩)
  rcases Int.natAbs_eq p with hp_eq | hp_eq <;> rcases hq_mod with hq1 | hq3
  · have he : Even ((p - 1) / 2) := ⟨(q - 1) / 4, by omega⟩
    have hqe : Even ((q - 1) / 2) := ⟨(q - 1) / 4, by omega⟩
    rw [hqe.neg_one_pow, one_mul] at hnat
    rw [(he.mul_right N4).neg_one_zpow, mul_one, hp_eq, Int.cast_natCast, hnat]
  · have ho : Odd ((p - 1) / 2) := ⟨(q - 3) / 4, by omega⟩
    have hqo : Odd ((q - 1) / 2) := ⟨(q - 3) / 4, by omega⟩
    rw [hqo.neg_one_pow, neg_one_mul] at hnat
    rw [hflip (-(q : 𝓞 K)) (by rw [hp_eq, Int.cast_natCast]; ring) ho, hnat]
  · have ho : Odd ((p - 1) / 2) := ⟨-(((q : ℤ) - 1) / 4) - 1, by omega⟩
    have hqe : Even ((q - 1) / 2) := ⟨(q - 1) / 4, by omega⟩
    rw [hqe.neg_one_pow, one_mul] at hnat
    rw [hflip (q : 𝓞 K) (by rw [hp_eq, Int.cast_neg, Int.cast_natCast]; ring) ho, hnat]
  · have he : Even ((p - 1) / 2) := ⟨-(((q : ℤ) + 1) / 4), by omega⟩
    have hqo : Odd ((q - 1) / 2) := ⟨(q - 3) / 4, by omega⟩
    rw [hqo.neg_one_pow, neg_one_mul] at hnat
    rw [(he.mul_right N4).neg_one_zpow, mul_one, hp_eq, Int.cast_neg, Int.cast_natCast, hnat]

/-- Odd-integer quartic reciprocity at a primary prime `π`, read in `K`. -/
private theorem coe_quartic_reciprocity_intCast_of_prime_of_odd {π : 𝓞 K}
    (hπ : IsPrimaryGaussian π) (hp : Prime π) {m : ℤ} (hm : Odd m) :
    ((powerResidueSymbolIdeal (span {π}) 4 (Ideal.Quotient.mk _ (m : 𝓞 K)) : 𝓞 K) : K) =
      ((powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) : 𝓞 K) : K) *
        (-1) ^ (((m - 1) / 2) * (((absNorm (span {π}) - 1) / 4 : ℕ) : ℤ)) := by
  set N4 : ℤ := (((absNorm (span {π}) - 1) / 4 : ℕ) : ℤ)
  induction m using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd hm (by simp)
  | h₂ u hu =>
    have hu' : IsUnit (u : 𝓞 K) := RingOfIntegers.isUnit_intCast.mpr hu
    rw [span_singleton_eq_top.mpr hu', powerResidueSymbolIdeal_top]
    rcases Int.isUnit_iff.mp hu with rfl | rfl
    · simp
    · simp only [Int.cast_neg, Int.cast_one, RingOfIntegers.coe_eq_algebraMap, map_one, one_mul]
      rw [← RingOfIntegers.coe_eq_algebraMap, coe_powerResidueSymbolIdeal_mk_neg_one hπ,
        show (-1 - 1 : ℤ) / 2 = -1 by decide]
      exact zpow_eq_zpow_of_modEq (n := 2) (by norm_num)
        (Int.modEq_iff_dvd.mpr ⟨-N4, by ring⟩)
  | h₃ m' p hm'0 hp_int ih =>
    rw [Int.odd_mul] at hm
    obtain ⟨hp_odd, hm'_odd⟩ := hm
    have hp0 : span {(p : 𝓞 K)} ≠ ⊥ := by simpa using hp_int.ne_zero
    have hm'_span0 : span {(m' : 𝓞 K)} ≠ ⊥ := by simpa using hm'0
    rw [Int.cast_mul, map_mul, map_mul, ← span_singleton_mul_span_singleton,
      powerResidueSymbolIdeal_mul_right hp0 hm'_span0,
      RingOfIntegers.coe_eq_algebraMap, map_mul,
      ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap,
      RingOfIntegers.coe_eq_algebraMap (_ * _), map_mul,
      ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap,
      coe_quartic_reciprocity_intCast_prime hπ hp hp_int hp_odd, ih hm'_odd,
      mul_mul_mul_comm, ← zpow_add₀ (by norm_num), ← add_mul]
    congr 1
    refine zpow_eq_zpow_of_modEq (n := 2) (by norm_num) (Int.ModEq.mul_right N4 ?_)
    -- Inline `(p * m' - 1) / 2 ≡ (p - 1) / 2 + (m' - 1) / 2 (mod 2)` for odd `p, m'`.
    obtain ⟨u, rfl⟩ := hp_odd
    obtain ⟨v, rfl⟩ := hm'_odd
    have hxy : ((2 * u + 1) * (2 * v + 1) - 1) / 2 = 2 * (u * v) + u + v := by
      have h : (2 * u + 1) * (2 * v + 1) - 1 = 2 * (2 * (u * v) + u + v) := by ring
      rw [h, Int.mul_ediv_cancel_left _ (by decide)]
    have hu : (2 * u + 1 - 1) / 2 = u := by omega
    have hv : (2 * v + 1 - 1) / 2 = v := by omega
    rw [hxy, hu, hv]
    exact Int.modEq_iff_dvd.mpr ⟨u * v, by ring⟩

/-- For nonzero ideals `I` and `J` whose norms are prime to `4`, `(N(I J) - 1) / 4` has the parity
of `(N I - 1) / 4 + (N J - 1) / 4`. -/
private theorem neg_one_zpow_mul_absNorm_sub_one_div_four {F : Type*} [Field F] {I J : Ideal (𝓞 K)}
    (hI0 : I ≠ ⊥) (hJ0 : J ≠ ⊥) (hI4 : (absNorm I).Coprime 4) (hJ4 : (absNorm J).Coprime 4)
    (k : ℤ) :
    (-1 : F) ^ (k * (((absNorm (I * J) - 1) / 4 : ℕ) : ℤ)) =
      (-1 : F) ^ (k * (((absNorm I - 1) / 4 : ℕ) : ℤ)) *
        (-1 : F) ^ (k * (((absNorm J - 1) / 4 : ℕ) : ℤ)) := by
  have hI1 : 1 ≤ absNorm I := Nat.one_le_iff_ne_zero.mpr (absNorm_eq_zero_iff.not.mpr hI0)
  have hJ1 : 1 ≤ absNorm J := Nat.one_le_iff_ne_zero.mpr (absNorm_eq_zero_iff.not.mpr hJ0)
  obtain ⟨u, hu⟩ := (Nat.modEq_iff_dvd' hI1).mp (absNorm_modEq_one hI4).symm
  obtain ⟨v, hv⟩ := (Nat.modEq_iff_dvd' hJ1).mp (absNorm_modEq_one hJ4).symm
  have hIu : absNorm I = 4 * u + 1 := by omega
  have hJv : absNorm J = 4 * v + 1 := by omega
  have hmulN : (absNorm (I * J) - 1) / 4 = u + v + 4 * (u * v) := by
    have h : (4 * u + 1) * (4 * v + 1) = 4 * (u + v + 4 * (u * v)) + 1 := by ring
    rw [map_mul, hIu, hJv, h]
    omega
  have hu4 : (absNorm I - 1) / 4 = u := by omega
  have hv4 : (absNorm J - 1) / 4 = v := by omega
  have heven : Even (k * (4 * ((u : ℤ) * v))) := ⟨k * (2 * ((u : ℤ) * v)), by ring⟩
  rw [hmulN, hu4, hv4]
  push_cast
  rw [mul_add, mul_add, zpow_add₀ (by norm_num), zpow_add₀ (by norm_num), heven.neg_one_zpow,
    mul_one]

/-- **Quartic reciprocity between a primary element and an odd rational integer.** If `K = ℚ(i)`,
`π` is primary in `𝓞 K = ℤ[i]`, and `m` is an odd rational integer, then
`(m / π)_4 = (π / m)_4 · (-1) ^ (((m - 1) / 2) * ((N(π) - 1) / 4))`, read in `K` with
`N = Algebra.norm ℤ`. If `m` and `π` are not coprime, both sides vanish. -/
theorem IsPrimaryGaussian.coe_quartic_reciprocity_intCast_of_odd {π : 𝓞 K}
    (hπ : IsPrimaryGaussian π) {m : ℤ} (hm : Odd m) :
    ((powerResidueSymbolIdeal (span {π}) 4 (Ideal.Quotient.mk _ (m : 𝓞 K)) : 𝓞 K) : K) =
      ((powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) : 𝓞 K) : K) *
        (-1) ^ (((m - 1) / 2) * ((Algebra.norm ℤ π - 1) / 4)) := by
  have hgen : ∀ {x : 𝓞 K}, IsPrimaryGaussian x →
      ((powerResidueSymbolIdeal (span {x}) 4 (Ideal.Quotient.mk _ (m : 𝓞 K)) : 𝓞 K) : K) =
        ((powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 (Ideal.Quotient.mk _ x) : 𝓞 K) : K) *
          (-1) ^ (((m - 1) / 2) * (((absNorm (span {x}) - 1) / 4 : ℕ) : ℤ)) := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := hx.exists_multiset_prod_eq
    clear hx
    induction s using Multiset.induction_on with
    | empty =>
      rw [Multiset.prod_zero, span_singleton_one, absNorm_top, powerResidueSymbolIdeal_top]
      simp
    | cons p s ih =>
      have hp := hs p (Multiset.mem_cons_self p s)
      have hs' : ∀ q ∈ s, Prime q ∧ IsPrimaryGaussian q := fun q hq ↦
        hs q (Multiset.mem_cons_of_mem hq)
      have hs_prim : IsPrimaryGaussian s.prod := by
        clear hp hs ih
        induction s using Multiset.induction_on with
        | empty => simp
        | cons q t iht =>
          rw [Multiset.prod_cons]
          exact (hs' q (Multiset.mem_cons_self q t)).2.mul
            (iht fun r hr ↦ hs' r (Multiset.mem_cons_of_mem hr))
      have hp0 : span {p} ≠ ⊥ := by simpa using hp.1.ne_zero
      have hs0 : span {s.prod} ≠ ⊥ := by
        rw [Ne, span_singleton_eq_bot]
        exact fun h ↦ absurd (h ▸ hs_prim.odd_norm) (by simp)
      rw [Multiset.prod_cons, ← span_singleton_mul_span_singleton,
        powerResidueSymbolIdeal_mul_right hp0 hs0,
        RingOfIntegers.coe_eq_algebraMap, map_mul,
        ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap,
        coe_quartic_reciprocity_intCast_of_prime_of_odd hp.2 hp.1 hm, ih hs',
        map_mul, map_mul, RingOfIntegers.coe_eq_algebraMap (_ * _), map_mul,
        ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap,
        mul_mul_mul_comm,
        neg_one_zpow_mul_absNorm_sub_one_div_four hp0 hs0 hp.2.absNorm_span_singleton_coprime_four
          hs_prim.absNorm_span_singleton_coprime_four]
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
  obtain ⟨c, d, rfl⟩ := hζ.exists_intCast_add_intCast_mul_toInteger_eq (by decide) π
  rw [hgen hπ, hπ.natCast_absNorm_sub_one_div_four]

/-- **Quartic reciprocity in coordinates between a primary element and an odd rational integer.**
If `K = ℚ(i)`, `π = c + d i` is primary, and `m` is an odd rational integer, then
`(m / π)_4 = (π / m)_4 · (-1) ^ (((m - 1) / 2) * ((c - 1) / 2))`, read in `K`. -/
theorem IsPrimaryGaussian.quartic_reciprocity_intCast_add_mul_of_odd {ζ : K}
    {hζ : IsPrimitiveRoot ζ 4} {c d m : ℤ}
    (hπ : IsPrimaryGaussian ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger)) (hm : Odd m) :
    ((powerResidueSymbolIdeal (span {(c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ (m : 𝓞 K)) : 𝓞 K) : K) =
      ((powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4
        (Ideal.Quotient.mk _ ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger)) : 𝓞 K) : K) *
        (-1) ^ (((m - 1) / 2) * ((c - 1) / 2)) := by
  rw [hπ.coe_quartic_reciprocity_intCast_of_odd hm]
  congr 1
  exact zpow_eq_zpow_of_modEq (n := 2) (by norm_num)
    (Int.ModEq.mul_left _ hπ.norm_sub_one_div_four)

/-- **Quartic reciprocity between a primary element and a rational integer `a ≡ 1 (mod 4)`.** If
`K = ℚ(i)`, `π` is primary in `𝓞 K = ℤ[i]`, and `a ≡ 1 (mod 4)` is a rational integer (possibly
negative or composite), then `(a / π)_4 = (π / a)_4`. If `a` and `π` are not coprime, both sides
vanish. -/
theorem IsPrimaryGaussian.quartic_reciprocity_intCast {π : 𝓞 K} (hπ : IsPrimaryGaussian π)
    {a : ℤ} (ha : a ≡ 1 [ZMOD 4]) :
    powerResidueSymbolIdeal (span {π}) 4 (Ideal.Quotient.mk _ (a : 𝓞 K)) =
      powerResidueSymbolIdeal (span {(a : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) := by
  have hodd : Odd a := by rw [Int.odd_iff]; simp only [Int.ModEq] at ha; omega
  have heven : Even (((a - 1) / 2) * ((Algebra.norm ℤ π - 1) / 4)) := by
    obtain ⟨k, hk⟩ := ha.symm.dvd
    have ha2 : (a - 1) / 2 = 2 * k := by omega
    rw [ha2]
    exact ⟨k * ((Algebra.norm ℤ π - 1) / 4), by ring⟩
  apply RingOfIntegers.coe_injective
  rw [← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap,
    hπ.coe_quartic_reciprocity_intCast_of_odd hodd, heven.neg_one_zpow, mul_one]

/-! ### Primary elements with coprime coordinates -/

/-- For primary coordinates `(a, b)` and `(c, d)` and `m = a * c + b * d`, the combined sign
exponent from odd-integer reciprocity and `(i / ·)_4` is congruent modulo `2` to
`((a - 1) / 2) * ((c - 1) / 2)`. -/
private theorem sign_exponent_modEq {a b c d : ℤ}
    (hπ₁ : a ≡ 1 [ZMOD 4] ∧ b ≡ 0 [ZMOD 4] ∨ a ≡ 3 [ZMOD 4] ∧ b ≡ 2 [ZMOD 4])
    (hπ₂ : c ≡ 1 [ZMOD 4] ∧ d ≡ 0 [ZMOD 4] ∨ c ≡ 3 [ZMOD 4] ∧ d ≡ 2 [ZMOD 4]) :
    let m := a * c + b * d
    ((m ^ 2 - 1) / 8 + ((m - 1) / 2) * ((c - 1) / 2) + ((m - 1) / 2) * ((a - 1) / 2) +
      ((c ^ 2 - 1) / 8 + ((c - 1) / 2) * ((c - 1) / 2) +
        (a ^ 2 - 1) / 8 + ((a - 1) / 2) * ((a - 1) / 2))) ≡
      ((a - 1) / 2) * ((c - 1) / 2) [ZMOD 2] := by
  intro m
  simp only [Int.ModEq] at hπ₁ hπ₂
  obtain ⟨u, rfl⟩ : ∃ u, a = 2 * u + 1 := ⟨(a - 1) / 2, by omega⟩
  obtain ⟨β, rfl⟩ : ∃ β, b = 2 * β := ⟨b / 2, by omega⟩
  obtain ⟨v, rfl⟩ : ∃ v, c = 2 * v + 1 := ⟨(c - 1) / 2, by omega⟩
  obtain ⟨δ, rfl⟩ : ∃ δ, d = 2 * δ := ⟨d / 2, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, β = u + 2 * r := ⟨(β - u) / 2, by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, δ = v + 2 * s := ⟨(δ - v) / 2, by omega⟩
  have hoddsq (z : ℤ) : ((2 * z + 1) ^ 2 - 1) / 8 = z * (z + 1) / 2 := by
    have hsq : (2 * z + 1) ^ 2 - 1 = 4 * (z * (z + 1)) := by ring
    rw [hsq]
    omega
  set t : ℤ := u * v + u * s + v * r + 2 * r * s
  have hm_eq : m = 2 * (u + v + 4 * t) + 1 := by simp only [m, t]; ring
  have hw : (m - 1) / 2 = u + v + 4 * t := by omega
  have hu2 : (2 * u + 1 - 1) / 2 = u := by omega
  have hv2 : (2 * v + 1 - 1) / 2 = v := by omega
  rw [hw, hm_eq, hoddsq (u + v + 4 * t), hoddsq u, hoddsq v, hu2, hv2]
  have hsum : (u + v + 4 * t) * (u + v + 4 * t + 1) / 2 =
      (u + v) * (u + v + 1) / 2 + 2 * (t * (2 * (u + v) + 4 * t + 1)) := by
    have h : (u + v + 4 * t) * (u + v + 4 * t + 1) =
        (u + v) * (u + v + 1) + 2 * (2 * (t * (2 * (u + v) + 4 * t + 1))) := by ring
    rw [h, Int.add_mul_ediv_left _ _ (by decide)]
  have huv_tri : (u + v) * (u + v + 1) / 2 = u * (u + 1) / 2 + v * (v + 1) / 2 + u * v := by
    have hev (z : ℤ) : 2 ∣ z * (z + 1) := by
      rcases Int.even_or_odd z with ⟨x, rfl⟩ | ⟨x, rfl⟩
      · exact ⟨x * (x + x + 1), by ring⟩
      · exact ⟨(2 * x + 1) * (x + 1), by ring⟩
    obtain ⟨eu, heu⟩ := hev u
    obtain ⟨ev, hev⟩ := hev v
    have h : (u + v) * (u + v + 1) = 2 * (eu + ev + u * v) := by linear_combination heu + hev
    rw [h, heu, hev]
    omega
  rw [hsum, huv_tri]
  exact Int.modEq_iff_dvd.mpr
    ⟨-(u * (u + 1) / 2 + v * (v + 1) / 2 + t * (2 * (u + v) + 4 * t + 1) + u ^ 2 + u * v +
      v ^ 2 + 2 * t * (u + v)), by ring⟩

/-- For coprime primary elements `π₁ = a + b i` and `π₂ = c + d i` with coprime coordinates and
`m = a c + b d`, relates `(π₂ / π₁)_4` and `(π₁ / π₂)_4` to residue symbols with rational integer
numerators `m, c, a` and records `IsCoprime (a d - b c) m`. -/
private theorem mul_powerResidueSymbolIdeal_add_mul {ζ : K} {hζ : IsPrimitiveRoot ζ 4}
    {a b c d : ℤ} {τ : 𝓞 K ≃+* 𝓞 K} (hτ : ∀ z : 𝓞 K, z ^ 4 = 1 → τ z = z ^ 3)
    (hab : IsCoprime a b) (hcd : IsCoprime c d)
    (hcop : IsCoprime (span {(c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger})
      (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger})) :
    let i := hζ.toInteger
    let π₁ : 𝓞 K := (a : 𝓞 K) + (b : 𝓞 K) * i
    let π₂ : 𝓞 K := (c : 𝓞 K) + (d : 𝓞 K) * i
    let m : ℤ := a * c + b * d
    (powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ (m : 𝓞 K)) *
        powerResidueSymbolIdeal (span {τ π₁}) 4 (Ideal.Quotient.mk _ (m : 𝓞 K))) *
        powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) =
      (powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ (c : 𝓞 K)) *
        powerResidueSymbolIdeal (span {τ π₁}) 4 (Ideal.Quotient.mk _ (a : 𝓞 K))) *
        powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) ∧
      IsCoprime (a * d - b * c) m := by
  intro i π₁ π₂ m
  set k : ℤ := a * d - b * c
  have hsq : i ^ 2 = -1 := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  have hi_unit : IsUnit i := hζ.toInteger_isPrimitiveRoot.isUnit (by decide)
  have hτπ₁ : τ π₁ = (a : 𝓞 K) - (b : 𝓞 K) * i :=
    hζ.apply_intCast_add_intCast_mul_toInteger_of_four hτ a b
  have hid1 : (c : 𝓞 K) * π₁ - (m : 𝓞 K) = ((b : 𝓞 K) * i) * π₂ := by
    simp only [π₁, π₂, m]; push_cast; linear_combination (-(b : 𝓞 K) * d) * hsq
  have hid2 : (a : 𝓞 K) * π₂ - (m : 𝓞 K) = ((d : 𝓞 K) * i) * π₁ := by
    simp only [π₁, π₂, m]; push_cast; linear_combination (-(b : 𝓞 K) * d) * hsq
  have hid3 : τ π₁ * π₂ - (m : 𝓞 K) = (k : 𝓞 K) * i := by
    rw [hτπ₁]; simp only [π₂, m, k]; push_cast; linear_combination (-(b : 𝓞 K) * d) * hsq
  have heq1 : powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ (c : 𝓞 K)) *
      powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) =
      powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ (m : 𝓞 K)) := by
    have hmk : Ideal.Quotient.mk (span {π₂}) ((c : 𝓞 K) * π₁) =
        Ideal.Quotient.mk (span {π₂}) (m : 𝓞 K) :=
      Ideal.Quotient.eq.mpr (mem_span_singleton.mpr ⟨b * i, by linear_combination hid1⟩)
    rw [← map_mul, ← map_mul, hmk]
  have heq2 : powerResidueSymbolIdeal (span {τ π₁}) 4 (Ideal.Quotient.mk _ (m : 𝓞 K)) *
      powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) =
      powerResidueSymbolIdeal (span {τ π₁}) 4 (Ideal.Quotient.mk _ (a : 𝓞 K)) := by
    have heq2_raw : powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ (a : 𝓞 K)) *
        powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) =
        powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ (m : 𝓞 K)) := by
      have hmk : Ideal.Quotient.mk (span {π₁}) ((a : 𝓞 K) * π₂) =
          Ideal.Quotient.mk (span {π₁}) (m : 𝓞 K) :=
        Ideal.Quotient.eq.mpr (mem_span_singleton.mpr ⟨d * i, by linear_combination hid2⟩)
      rw [← map_mul, ← map_mul, hmk]
    have h4 : powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) ^ 4 = 1 :=
      powerResidueSymbolIdeal_pow_eq_one (n := 4)
        (Ideal.Quotient.isUnit_mk_iff.mpr (isCoprime_iff_sup_eq.mp hcop))
    have hmap : (span {π₁}).map τ = span {τ π₁} := by rw [map_span, Set.image_singleton]
    have hτ_int (z : ℤ) :
        τ (powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ (z : 𝓞 K))) =
          powerResidueSymbolIdeal (span {τ π₁}) 4 (Ideal.Quotient.mk _ (z : 𝓞 K)) := by
      rw [map_powerResidueSymbolIdeal, hmap, map_intCast τ]
    have hτ2 := congrArg τ heq2_raw
    rw [map_mul, hτ_int a, hτ _ h4, hτ_int m] at hτ2
    simpa only [mul_assoc, ← pow_succ, h4, mul_one] using
      (congrArg (· * powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂)) hτ2).symm
  refine ⟨?_, ?_⟩
  · calc (powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ (m : 𝓞 K)) *
          powerResidueSymbolIdeal (span {τ π₁}) 4 (Ideal.Quotient.mk _ (m : 𝓞 K))) *
          powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂)
        = (powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ (c : 𝓞 K)) *
            powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁)) *
            (powerResidueSymbolIdeal (span {τ π₁}) 4 (Ideal.Quotient.mk _ (m : 𝓞 K)) *
              powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂)) := by
          rw [heq1, mul_assoc]
      _ = _ := by rw [heq2]; ring
  · have hcπ₂ : IsCoprime (c : 𝓞 K) π₂ := by
      simpa [π₂] using ((isCoprime_mul_unit_right_right hi_unit (c : 𝓞 K) (d : 𝓞 K)).mpr
        hcd.intCast).mul_add_left_right 1
    have haπ₁ : IsCoprime (a : 𝓞 K) π₁ := by
      simpa [π₁] using ((isCoprime_mul_unit_right_right hi_unit (a : 𝓞 K) (b : 𝓞 K)).mpr
        hab.intCast).mul_add_left_right 1
    have hcop' : IsCoprime π₂ π₁ := (isCoprime_span_singleton_iff _ _).mp hcop
    have hmπ₂ : IsCoprime (m : 𝓞 K) π₂ := by
      obtain ⟨u, v, huv⟩ := hcπ₂.mul_left hcop'.symm
      exact ⟨u, v + u * ((b : 𝓞 K) * i), by linear_combination huv - u * hid1⟩
    have hmπ₁ : IsCoprime (m : 𝓞 K) π₁ := by
      obtain ⟨u, v, huv⟩ := haπ₁.mul_left hcop'
      exact ⟨u, v + u * ((d : 𝓞 K) * i), by linear_combination huv - u * hid2⟩
    have hmτπ₁ : IsCoprime (m : 𝓞 K) (τ π₁) := by
      simpa only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_intCast] using
        hmπ₁.map τ.toRingHom
    obtain ⟨u, v, huv⟩ := hmτπ₁.mul_right hmπ₂
    have hki : IsCoprime (m : 𝓞 K) ((k : 𝓞 K) * i) :=
      ⟨u + v, v, by linear_combination huv - v * hid3⟩
    exact (RingOfIntegers.isCoprime_intCast.mp
      ((isCoprime_mul_unit_right_right hi_unit _ _).mp hki)).symm

/-- For an odd integer `n`, `x` divisible by `n`, and `y` coprime to `n`,
`((x + y i) / n)_4 = (-1) ^ ((n² - 1) / 8)`, read in `K`. -/
private theorem coe_powerResidueSymbolIdeal_span_intCast_add_mul_of_dvd {ζ : K}
    (hζ : IsPrimitiveRoot ζ 4) {n x y : ℤ} (hn : Odd n) (hxn : n ∣ x) (hyn : IsCoprime y n) :
    ((powerResidueSymbolIdeal (span {(n : 𝓞 K)}) 4
        (Ideal.Quotient.mk _ ((x : 𝓞 K) + (y : 𝓞 K) * hζ.toInteger)) : 𝓞 K) : K) =
      (-1) ^ ((n ^ 2 - 1) / 8) := by
  obtain ⟨q, rfl⟩ := hxn
  have hmk : Ideal.Quotient.mk (span {(n : 𝓞 K)})
      (((n * q : ℤ) : 𝓞 K) + (y : 𝓞 K) * hζ.toInteger) =
      Ideal.Quotient.mk (span {(n : 𝓞 K)}) ((y : 𝓞 K) * hζ.toInteger) :=
    Ideal.Quotient.eq.mpr (mem_span_singleton.mpr ⟨q, by push_cast; ring⟩)
  rw [hmk, map_mul, map_mul, map_intCast, powerResidueSymbolIdeal_intCast_four hyn, one_mul]
  exact hζ.powerResidueSymbolIdeal_span_intCast_mk_toInteger_of_odd hn

/-- Cancels powers of `-1` in a field: if `(-1) ^ e₁ * x = (-1) ^ e₂ * y` and `e₁ + e₂ ≡ e (mod 2)`,
then `x = y * (-1) ^ e`. -/
private theorem eq_mul_neg_one_zpow_of_mul_eq {F : Type*} [Field F] {x y : F} {e₁ e₂ e : ℤ}
    (h : (-1 : F) ^ e₁ * x = (-1 : F) ^ e₂ * y) (he : e₁ + e₂ ≡ e [ZMOD 2]) :
    x = y * (-1) ^ e := by
  have hsq : (-1 : F) ^ e₁ * (-1 : F) ^ e₁ = 1 := by
    rw [← zpow_add₀ (by norm_num)]
    exact Even.neg_one_zpow ⟨e₁, by ring⟩
  calc x = ((-1 : F) ^ e₁ * (-1 : F) ^ e₁) * x := by rw [hsq, one_mul]
    _ = (-1 : F) ^ e₁ * ((-1 : F) ^ e₂ * y) := by rw [mul_assoc, h]
    _ = y * (-1) ^ (e₁ + e₂) := by rw [← mul_assoc, ← zpow_add₀ (by norm_num), mul_comm]
    _ = y * (-1) ^ e := by rw [zpow_eq_zpow_of_modEq (n := 2) (by norm_num) he]

/-- Quartic reciprocity for primary elements `π₁ = a + b i` and `π₂ = c + d i` whose coordinates
are coprime (`IsCoprime a b` and `IsCoprime c d`). -/
private theorem quartic_reciprocity_add_mul_of_isCoprime {ζ : K} {hζ : IsPrimitiveRoot ζ 4}
    {a b c d : ℤ} (hπ₁ : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger))
    (hπ₂ : IsPrimaryGaussian ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger))
    (hab : IsCoprime a b) (hcd : IsCoprime c d) :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger)) : 𝓞 K) : K) =
      ((powerResidueSymbolIdeal (span {(c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) : 𝓞 K) : K) *
        (-1) ^ (((a - 1) / 2) * ((c - 1) / 2)) := by
  set i := hζ.toInteger
  set π₁ : 𝓞 K := (a : 𝓞 K) + (b : 𝓞 K) * i
  set π₂ : 𝓞 K := (c : 𝓞 K) + (d : 𝓞 K) * i
  by_cases hcop : IsCoprime (span {π₂}) (span {π₁})
  swap
  · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hcop,
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr (mt IsCoprime.symm hcop)]
    simp
  have hsq : i ^ 2 = -1 := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  have hπ₁_coord := (hζ.isPrimaryGaussian_add_mul_iff (a := a) (b := b)).mp hπ₁
  have hπ₂_coord := (hζ.isPrimaryGaussian_add_mul_iff (a := c) (b := d)).mp hπ₂
  have ha_odd : Odd a := by rw [Int.odd_iff]; simp only [Int.ModEq] at hπ₁_coord; omega
  have hc_odd : Odd c := by rw [Int.odd_iff]; simp only [Int.ModEq] at hπ₂_coord; omega
  set m : ℤ := a * c + b * d
  set k : ℤ := a * d - b * c
  have hm_odd : Odd m := by
    obtain ⟨u, ha_eq⟩ := ha_odd
    obtain ⟨v, hc_eq⟩ := hc_odd
    obtain ⟨w, hb_eq⟩ : ∃ w, b = 2 * w := ⟨b / 2, by simp only [Int.ModEq] at hπ₁_coord; omega⟩
    exact ⟨2 * u * v + u + v + w * d, by simp only [m, ha_eq, hc_eq, hb_eq]; ring⟩
  obtain ⟨τ, hτ⟩ := exists_ringEquiv_apply_eq_pow_three_of_four (K := K)
  have hτπ₁ : τ π₁ = (a : 𝓞 K) + ((-b : ℤ) : 𝓞 K) * i := by
    rw [hζ.apply_intCast_add_intCast_mul_toInteger_of_four hτ a b]
    push_cast
    ring
  have hτπ₁_prim : IsPrimaryGaussian ((a : 𝓞 K) + ((-b : ℤ) : 𝓞 K) * i) :=
    hτπ₁ ▸ hπ₁.map τ.toRingHom
  obtain ⟨hmaster, hkm_cop⟩ := mul_powerResidueSymbolIdeal_add_mul hτ hab hcd hcop
  -- Evaluate the rational-denominator symbols `(π₂ / c)_4`, `(τ π₁ / a)_4`, and
  -- `((τ π₁ * π₂) / m)_4`.
  have hL_sym : ((powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π₂) : 𝓞 K) :
      K) * ((powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 (Ideal.Quotient.mk _ (τ π₁)) : 𝓞 K) :
      K) = (-1) ^ ((m ^ 2 - 1) / 8) := by
    have hprod : τ π₁ * π₂ = (m : 𝓞 K) + (k : 𝓞 K) * i := by
      rw [hτπ₁]; simp only [π₂, m, k]; push_cast; linear_combination (-(b : 𝓞 K) * d) * hsq
    rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap, ← map_mul,
      mul_comm, ← map_mul, ← map_mul, hprod, ← RingOfIntegers.coe_eq_algebraMap]
    exact coe_powerResidueSymbolIdeal_span_intCast_add_mul_of_dvd hζ hm_odd dvd_rfl hkm_cop
  have hc_sym : ((powerResidueSymbolIdeal (span {(c : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π₂) : 𝓞 K) :
      K) = (-1) ^ ((c ^ 2 - 1) / 8) :=
    coe_powerResidueSymbolIdeal_span_intCast_add_mul_of_dvd hζ hc_odd dvd_rfl hcd.symm
  have ha_sym : ((powerResidueSymbolIdeal (span {(a : 𝓞 K)}) 4 (Ideal.Quotient.mk _ (τ π₁)) :
      𝓞 K) : K) = (-1) ^ ((a ^ 2 - 1) / 8) := by
    rw [hτπ₁]
    exact coe_powerResidueSymbolIdeal_span_intCast_add_mul_of_dvd hζ ha_odd dvd_rfl
      hab.symm.neg_left
  -- Push `hmaster` to `K`, substitute odd-integer reciprocity, and cancel the `(-1)` powers.
  have hmasterK := congrArg (algebraMap (𝓞 K) K) hmaster
  simp only [map_mul, ← RingOfIntegers.coe_eq_algebraMap] at hmasterK
  rw [hπ₂.quartic_reciprocity_intCast_add_mul_of_odd hm_odd,
    hπ₂.quartic_reciprocity_intCast_add_mul_of_odd hc_odd, hτπ₁,
    hτπ₁_prim.quartic_reciprocity_intCast_add_mul_of_odd hm_odd,
    hτπ₁_prim.quartic_reciprocity_intCast_add_mul_of_odd ha_odd, ← hτπ₁] at hmasterK
  set eL : ℤ := (m ^ 2 - 1) / 8 + ((m - 1) / 2) * ((c - 1) / 2) + ((m - 1) / 2) * ((a - 1) / 2)
  set eR : ℤ := (c ^ 2 - 1) / 8 + ((c - 1) / 2) * ((c - 1) / 2) +
    (a ^ 2 - 1) / 8 + ((a - 1) / 2) * ((a - 1) / 2)
  have hLHS_sign : (((powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π₂) :
      𝓞 K) : K) * (-1) ^ (((m - 1) / 2) * ((c - 1) / 2)) *
      (((powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 (Ideal.Quotient.mk _ (τ π₁)) : 𝓞 K) : K) *
        (-1) ^ (((m - 1) / 2) * ((a - 1) / 2)))) = (-1) ^ eL := by
    rw [mul_mul_mul_comm, hL_sym, ← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
    congr 1; simp only [eL]; ring
  have hRHS_sign : (((powerResidueSymbolIdeal (span {(c : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π₂) :
      𝓞 K) : K) * (-1) ^ (((c - 1) / 2) * ((c - 1) / 2)) *
      (((powerResidueSymbolIdeal (span {(a : 𝓞 K)}) 4 (Ideal.Quotient.mk _ (τ π₁)) : 𝓞 K) : K) *
        (-1) ^ (((a - 1) / 2) * ((a - 1) / 2)))) = (-1) ^ eR := by
    rw [hc_sym, ha_sym, ← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num),
      ← zpow_add₀ (by norm_num)]
    congr 1; simp only [eR]; ring
  rw [hLHS_sign, hRHS_sign] at hmasterK
  exact eq_mul_neg_one_zpow_of_mul_eq hmasterK (sign_exponent_modEq hπ₁_coord hπ₂_coord)

/-! ### The general law of biquadratic reciprocity -/

/-- Multiplying a primary element `x = a + b i` by a rational integer `r ≡ 1 (mod 4)` leaves the
parity of `(N(x 𝓞 K) - 1) / 4` equal to that of `(a - 1) / 2`. -/
private theorem absNorm_intCast_mul_sub_one_div_four_modEq {ζ : K} {hζ : IsPrimitiveRoot ζ 4}
    {r x y : ℤ} (hr : r ≡ 1 [ZMOD 4])
    (hxy : IsPrimaryGaussian ((x : 𝓞 K) + (y : 𝓞 K) * hζ.toInteger)) :
    (((absNorm (span {(r : 𝓞 K) * ((x : 𝓞 K) + (y : 𝓞 K) * hζ.toInteger)}) - 1) / 4 : ℕ) : ℤ) ≡
      (x - 1) / 2 [ZMOD 2] := by
  set α : 𝓞 K := (x : 𝓞 K) + (y : 𝓞 K) * hζ.toInteger
  obtain ⟨w, z, hwz⟩ := hζ.exists_intCast_add_intCast_mul_toInteger_eq (by decide) ((r : 𝓞 K) * α)
  have hr_prim : IsPrimaryGaussian ((r : 𝓞 K) * α) := (isPrimaryGaussian_intCast_iff.mpr hr).mul hxy
  have hwz_prim : IsPrimaryGaussian ((w : 𝓞 K) + (z : 𝓞 K) * hζ.toInteger) := hwz.symm ▸ hr_prim
  rw [← hwz, hwz_prim.natCast_absNorm_sub_one_div_four, hwz, map_mul]
  have hr0 : (r : 𝓞 K) = (r : 𝓞 K) + ((0 : ℤ) : 𝓞 K) * hζ.toInteger := by simp
  rw [hr0, hζ.norm_intCast_add_intCast_mul_toInteger_of_four, zero_pow two_ne_zero, add_zero]
  obtain ⟨t, ht⟩ : ∃ t, r = 4 * t + 1 := ⟨(r - 1) / 4, by simp only [Int.ModEq] at hr; omega⟩
  have hcop4 := hxy.absNorm_span_singleton_coprime_four
  have hpos : 1 ≤ absNorm (span {α}) :=
    Nat.one_le_iff_ne_zero.mpr fun h0 ↦ absurd (h0 ▸ hcop4) (by decide)
  obtain ⟨u, hu⟩ := (Nat.modEq_iff_dvd' hpos).mp (absNorm_modEq_one hcop4).symm
  have hN := RingOfIntegers.natCast_absNorm_span_singleton_of_four α
  have hN_eq : Algebra.norm ℤ α = 4 * (u : ℤ) + 1 := by omega
  have hprod_div : (r ^ 2 * Algebra.norm ℤ α - 1) / 4 =
      (u : ℤ) + 2 * (t * (2 * t + 1) * (4 * (u : ℤ) + 1)) := by
    rw [ht, hN_eq]
    have h : (4 * t + 1) ^ 2 * (4 * (u : ℤ) + 1) - 1 =
        4 * ((u : ℤ) + 2 * (t * (2 * t + 1) * (4 * (u : ℤ) + 1))) := by ring
    rw [h, Int.mul_ediv_cancel_left _ (by decide)]
  have hu_eq : (Algebra.norm ℤ α - 1) / 4 = (u : ℤ) := by omega
  refine (Int.modEq_iff_dvd.mpr ?_).trans hxy.norm_sub_one_div_four
  rw [hprod_div, hu_eq]
  exact ⟨-(t * (2 * t + 1) * (4 * (u : ℤ) + 1)), by ring⟩

/-- **The law of biquadratic (quartic) reciprocity.** Let `K = ℚ(i)`, so that `𝓞 K = ℤ[i]`, and
let `π₁` and `π₂` be primary elements of `𝓞 K`. Then
`(π₂ / π₁)_4 = (π₁ / π₂)_4 · (-1) ^ (((N(π₂ 𝓞 K) - 1) / 4) * ((N(π₁ 𝓞 K) - 1) / 4))`,
where the quartic power residue symbols are taken at the principal ideals `π₁ 𝓞 K` and `π₂ 𝓞 K`.
If `π₁` and `π₂` are not coprime, both symbols vanish and the equality still holds. -/
theorem IsPrimaryGaussian.quartic_reciprocity {π₁ π₂ : 𝓞 K} (hπ₁ : IsPrimaryGaussian π₁)
    (hπ₂ : IsPrimaryGaussian π₂) :
    powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) =
      powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) *
        (-1) ^ (((absNorm (span {π₂}) - 1) / 4) * ((absNorm (span {π₁}) - 1) / 4)) := by
  by_cases hcop : IsCoprime (span {π₂}) (span {π₁})
  swap
  · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hcop,
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr (mt IsCoprime.symm hcop), zero_mul]
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
  obtain ⟨m, a, b, hm, hab, hα₁, rfl⟩ := hπ₁.exists_intCast_mul_add_mul_isCoprime hζ
  obtain ⟨n, c, d, hn, hcd, hα₂, rfl⟩ := hπ₂.exists_intCast_mul_add_mul_isCoprime hζ
  set α₁ : 𝓞 K := (a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger
  set α₂ : 𝓞 K := (c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger
  have hm0 : span {(m : 𝓞 K)} ≠ ⊥ := by
    have hm_ne : m ≠ 0 := by simp only [Int.ModEq] at hm; omega
    simpa using hm_ne
  have hn0 : span {(n : 𝓞 K)} ≠ ⊥ := by
    have hn_ne : n ≠ 0 := by simp only [Int.ModEq] at hn; omega
    simpa using hn_ne
  have hα₁_0 : span {α₁} ≠ ⊥ := by simpa using fun h ↦ absurd (h ▸ hα₁.odd_norm) (by simp)
  have hα₂_0 : span {α₂} ≠ ⊥ := by simpa using fun h ↦ absurd (h ▸ hα₂.odd_norm) (by simp)
  have hmn : IsCoprime n m := by
    rw [← span_singleton_mul_span_singleton, ← span_singleton_mul_span_singleton] at hcop
    exact RingOfIntegers.isCoprime_intCast.mp
      ((isCoprime_span_singleton_iff _ _).mp hcop.of_mul_left_left.of_mul_right_left)
  have hLHS : powerResidueSymbolIdeal (span {(m : 𝓞 K) * α₁}) 4
      (Ideal.Quotient.mk _ ((n : 𝓞 K) * α₂)) =
      powerResidueSymbolIdeal (span {α₂}) 4 (Ideal.Quotient.mk _ (m : 𝓞 K)) *
        powerResidueSymbolIdeal (span {α₁}) 4 (Ideal.Quotient.mk _ (n : 𝓞 K)) *
        powerResidueSymbolIdeal (span {α₁}) 4 (Ideal.Quotient.mk _ α₂) := by
    rw [← span_singleton_mul_span_singleton, powerResidueSymbolIdeal_mul_right hm0 hα₁_0,
      map_mul, map_mul, map_mul, map_mul, map_intCast,
      powerResidueSymbolIdeal_intCast_four hmn, one_mul,
      ← hα₂.quartic_reciprocity_intCast hm, mul_assoc]
  have hRHS : powerResidueSymbolIdeal (span {(n : 𝓞 K) * α₂}) 4
      (Ideal.Quotient.mk _ ((m : 𝓞 K) * α₁)) =
      powerResidueSymbolIdeal (span {α₂}) 4 (Ideal.Quotient.mk _ (m : 𝓞 K)) *
        powerResidueSymbolIdeal (span {α₁}) 4 (Ideal.Quotient.mk _ (n : 𝓞 K)) *
        powerResidueSymbolIdeal (span {α₂}) 4 (Ideal.Quotient.mk _ α₁) := by
    rw [← span_singleton_mul_span_singleton, powerResidueSymbolIdeal_mul_right hn0 hα₂_0,
      map_mul, map_mul, map_mul, map_mul, map_intCast,
      powerResidueSymbolIdeal_intCast_four hmn.symm, one_mul,
      ← hα₁.quartic_reciprocity_intCast hn]
    ring
  have hcop_rec : ((powerResidueSymbolIdeal (span {α₁}) 4 (Ideal.Quotient.mk _ α₂) : 𝓞 K) :
      K) = ((powerResidueSymbolIdeal (span {α₂}) 4 (Ideal.Quotient.mk _ α₁) : 𝓞 K) : K) *
        (-1) ^ (((a - 1) / 2) * ((c - 1) / 2)) :=
    quartic_reciprocity_add_mul_of_isCoprime hα₁ hα₂ hab hcd
  rw [hLHS, hRHS]
  simp only [mul_assoc]
  congr 1
  congr 1
  apply RingOfIntegers.coe_injective
  rw [map_mul, ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap, hcop_rec]
  congr 1
  rw [← RingOfIntegers.coe_eq_algebraMap]
  push_cast
  rw [← zpow_natCast, Nat.cast_mul]
  refine (zpow_eq_zpow_of_modEq (n := 2) (by norm_num) ?_).symm
  rw [mul_comm ((a - 1) / 2)]
  exact (absNorm_intCast_mul_sub_one_div_four_modEq hn hα₂).mul
    (absNorm_intCast_mul_sub_one_div_four_modEq hm hα₁)

/-- **The law of biquadratic (quartic) reciprocity, with integer norms.** Let `K = ℚ(i)` and let
`π₁` and `π₂` be primary elements of `𝓞 K = ℤ[i]`. Read in `K`,
`(π₂ / π₁)_4 = (π₁ / π₂)_4 · (-1) ^ (((N(π₂) - 1) / 4) * ((N(π₁) - 1) / 4))`,
where `N = Algebra.norm ℤ`. -/
theorem IsPrimaryGaussian.coe_quartic_reciprocity {π₁ π₂ : 𝓞 K} (hπ₁ : IsPrimaryGaussian π₁)
    (hπ₂ : IsPrimaryGaussian π₂) :
    ((powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) : 𝓞 K) : K) =
      ((powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) : 𝓞 K) : K) *
        (-1) ^ (((Algebra.norm ℤ π₂ - 1) / 4) * ((Algebra.norm ℤ π₁ - 1) / 4)) := by
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
  have hcast {x : 𝓞 K} (hx : IsPrimaryGaussian x) :
      (((absNorm (span {x}) - 1) / 4 : ℕ) : ℤ) = (Algebra.norm ℤ x - 1) / 4 := by
    obtain ⟨a, b, rfl⟩ := hζ.exists_intCast_add_intCast_mul_toInteger_eq (by decide) x
    exact hx.natCast_absNorm_sub_one_div_four
  rw [hπ₁.quartic_reciprocity hπ₂]
  push_cast
  rw [← zpow_natCast, Nat.cast_mul, hcast hπ₂, hcast hπ₁]

/-- **The law of biquadratic reciprocity in coordinates.** For any primary elements
`π₁ = a + b i` and `π₂ = c + d i` of `𝓞 K = ℤ[i]`,
`(π₂ / π₁)_4 = (π₁ / π₂)_4 · (-1) ^ (((a - 1) / 2) * ((c - 1) / 2))`, read in `K`. Neither
coprimality of `(a, b)` or `(c, d)` nor coprimality of `π₁` and `π₂` is required. -/
theorem IsPrimaryGaussian.quartic_reciprocity_add_mul {ζ : K} {hζ : IsPrimitiveRoot ζ 4}
    {a b c d : ℤ} (hπ₁ : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger))
    (hπ₂ : IsPrimaryGaussian ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger)) :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger)) : 𝓞 K) : K) =
      ((powerResidueSymbolIdeal (span {(c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) : 𝓞 K) : K) *
        (-1) ^ (((a - 1) / 2) * ((c - 1) / 2)) := by
  rw [hπ₁.coe_quartic_reciprocity hπ₂]
  congr 1
  exact zpow_eq_zpow_of_modEq (n := 2) (by norm_num)
    (by simpa [mul_comm] using hπ₁.norm_sub_one_div_four.mul hπ₂.norm_sub_one_div_four)

/-! ### Examples -/

section Examples

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 4)
include hζ

/- `((-3) / (-1 + 2i))_4 = ((-1 + 2i) / 3)_4 = -i`: at the inert prime `3` of norm `9`,
`(-1 + 2i) ^ ((9 - 1) / 4) = -3 - 4i ≡ -i (mod 3)`, and primary-rational reciprocity equates the
two symbols. -/
example :
    let π : 𝓞 K := ((-1 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger
    powerResidueSymbolIdeal (span {π}) 4 (Ideal.Quotient.mk _ ((-3 : ℤ) : 𝓞 K)) =
        -hζ.toInteger ∧
      powerResidueSymbolIdeal (span {((3 : ℤ) : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) =
        -hζ.toInteger := by
  intro π
  have hπ : IsPrimaryGaussian π := by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide
  have hQmax : (span {((3 : ℤ) : 𝓞 K)}).IsMaximal := by
    have hp3 : Prime ((3 : ℕ) : 𝓞 K) := prime_natCast_of_mod_four_eq_three Nat.prime_three rfl
    exact ((span_singleton_prime (by exact_mod_cast (by decide : (3 : ℤ) ≠ 0))).mpr
      (by simpa using hp3)).isMaximal (by simp)
  have hNQ : absNorm (span {((3 : ℤ) : 𝓞 K)}) = 9 := by
    simpa using absNorm_span_natCast_four (K := K) 3
  have hcop4 : (absNorm (span {((3 : ℤ) : 𝓞 K)})).Coprime 4 := by rw [hNQ]; decide
  have hsq := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  have hcong : Ideal.Quotient.mk (span {((3 : ℤ) : 𝓞 K)}) (-hζ.toInteger) =
      (Ideal.Quotient.mk (span {((3 : ℤ) : 𝓞 K)}) π) ^ 2 := by
    rw [← map_pow, Ideal.Quotient.eq, mem_span_singleton]
    refine ⟨1 + hζ.toInteger, ?_⟩
    simp only [π]
    push_cast
    linear_combination (-4 : 𝓞 K) * hsq
  have hπ3_ne : Ideal.Quotient.mk (span {((3 : ℤ) : 𝓞 K)}) π ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hcong
    have hu : IsUnit (Ideal.Quotient.mk (span {((3 : ℤ) : 𝓞 K)}) (-hζ.toInteger)) :=
      ((hζ.toInteger_isPrimitiveRoot.isUnit (by decide)).neg).map _
    exact hu.ne_zero hcong
  have hnegi4 : (-hζ.toInteger) ^ 4 = 1 := by
    have hneg1 : (-1 : 𝓞 K) ^ 4 = 1 := by norm_num
    rw [neg_pow, hneg1, one_mul, hζ.toInteger_isPrimitiveRoot.pow_eq_one]
  have hrhs : powerResidueSymbolIdeal (span {((3 : ℤ) : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) =
      -hζ.toInteger := by
    rw [powerResidueSymbolIdeal_of_isMaximal,
      powerResidueSymbol_eq_iff hcop4 hπ3_ne hnegi4, hNQ]
    exact hcong
  refine ⟨?_, hrhs⟩
  have hrec := hπ.quartic_reciprocity_intCast (a := -3) (by decide)
  rw [Int.cast_neg]
  rwa [Int.cast_neg, span_singleton_neg, hrhs] at hrec

/- For `q = 5 ≡ 1 (mod 4)`, `(5 / (3 + 2i))_4 = ((3 + 2i) / 5)_4`. -/
example :
    let π : 𝓞 K := ((3 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger
    powerResidueSymbolIdeal (span {π}) 4 (Ideal.Quotient.mk _ ((5 : ℤ) : 𝓞 K)) =
      powerResidueSymbolIdeal (span {((5 : ℤ) : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) := by
  intro π
  have hπ : IsPrimaryGaussian π := by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide
  exact hπ.quartic_reciprocity_intCast (by decide)

/- For `π₁ = -1 + 2i` (norm `5 ≡ 5 (mod 8)`) and `π₂ = 3 + 2i` (norm `13 ≡ 5 (mod 8)`), the
reciprocity sign is `-1`, so `(π₂ / π₁)_4 = -(π₁ / π₂)_4`. -/
example :
    let π₁ : 𝓞 K := ((-1 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger
    let π₂ : 𝓞 K := ((3 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger
    ((powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) : 𝓞 K) : K) =
      -((powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) : 𝓞 K) : K) := by
  intro π₁ π₂
  have hπ₁ : IsPrimaryGaussian π₁ := by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide
  have hπ₂ : IsPrimaryGaussian π₂ := by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide
  have hsign : (-1 : K) ^ (((-1 - 1 : ℤ) / 2) * ((3 - 1) / 2)) = -1 := by norm_num
  rw [hπ₁.quartic_reciprocity_add_mul hπ₂, hsign, mul_neg_one]

/- For `π₁ = -1 + 2i` (norm `5`) and `π₂ = -3` (norm `9`, where `gcd(-3, 0) = 3 ≠ 1`), the general
biquadratic reciprocity law gives `(π₂ / π₁)_4 = (π₁ / π₂)_4`. -/
example :
    let π₁ : 𝓞 K := ((-1 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger
    let π₂ : 𝓞 K := ((-3 : ℤ) : 𝓞 K)
    powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) =
      powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) := by
  intro π₁ π₂
  have hπ₁ : IsPrimaryGaussian π₁ := by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide
  have hπ₂ : IsPrimaryGaussian π₂ := by rw [isPrimaryGaussian_intCast_iff]; decide
  have h3 : π₂ = -((3 : ℕ) : 𝓞 K) := by simp [π₂]
  have hNπ₂ : absNorm (span {π₂}) = 9 := by
    rw [h3, span_singleton_neg, absNorm_span_natCast_four]
    rfl
  rw [hπ₁.quartic_reciprocity hπ₂, hNπ₂]
  norm_num

end Examples

end TauCeti
