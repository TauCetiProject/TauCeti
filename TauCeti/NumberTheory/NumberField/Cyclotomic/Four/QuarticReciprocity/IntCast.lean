/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.GaussSum
import TauCeti.Algebra.GroupWithZero.Basic
import TauCeti.NumberTheory.LegendreSymbol.Complex
import TauCeti.NumberTheory.NumberField.PrimeIdeal
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Norm
import TauCeti.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.RingTheory.IntegralClosure.Map

/-!
# Quartic reciprocity between a primary element and an odd rational integer

Let `K = ℚ(i)`, given as a number field with `IsCyclotomicExtension {4} ℚ K`, so that
`𝓞 K = ℤ[i]`, and write `(α / β)_4` for the quartic power residue symbol
`Ideal.powerResidueSymbolIdeal (Ideal.span {β}) 4 (Ideal.Quotient.mk _ α)`. This file proves
quartic reciprocity between a primary element `π` of `ℤ[i]` and an odd rational integer `m`:

`(m / π)_4 = (π / m)_4 · (-1) ^ (((m - 1) / 2) * ((N(π) - 1) / 4))`.

For a primary prime `π` and an odd rational prime `q`, the proof splits according to `q mod 4`:

* When `q ≡ 1 (mod 4)`, `q = (σ β) β` splits in `ℤ[i]` and the identity follows by evaluating the
  Gauss sum power `Φ(π 𝓞 K) = π · (σ π) ^ 3`
  (`TauCeti.IsPrimaryGaussian.stickelbergerPhi_span_singleton_four_eq`) modulo `β 𝓞 K` through
  `Ideal.powerResidueSymbol_stickelbergerPhi`.
* When `q ≡ 3 (mod 4)`, `Q = q 𝓞 K` is inert of norm `q²` and the `(q + 1)`-st power of the
  quartic Gauss sum modulo a prime of the algebraic integers over `Q` is computed in two ways: by
  the Frobenius congruence in characteristic `q` and from `g(χ, ψ) ^ 4 = π ^ 3 σ π`.

Multiplicativity in both arguments extends this to any primary `π` and odd rational integer `m`
(`TauCeti.IsPrimaryGaussian.coe_quartic_reciprocity_intCast_of_odd`, and in coordinates
`TauCeti.IsPrimaryGaussian.coe_quartic_reciprocity_intCast_add_mul_of_odd`), and in particular
gives `(a / π)_4 = (π / a)_4` for `a ≡ 1 (mod 4)`
(`TauCeti.IsPrimaryGaussian.quartic_reciprocity_intCast`) and
`(((-1) ^ ((q - 1) / 2) * q) / π)_4 = (π / q)_4` for any odd `q : ℕ`
(`TauCeti.IsPrimaryGaussian.quartic_reciprocity_natCast_of_odd`). The general law of biquadratic
reciprocity between arbitrary primary elements is deduced in
`TauCeti.NumberTheory.NumberField.Cyclotomic.Four.QuarticReciprocity.Primary`.

## Main results

* `TauCeti.IsPrimaryGaussian.coe_quartic_reciprocity_intCast_of_odd`,
  `TauCeti.IsPrimaryGaussian.coe_quartic_reciprocity_intCast_add_mul_of_odd`:
  `(m / π)_4 = (π / m)_4 · (-1) ^ (((m - 1) / 2) * ((N(π) - 1) / 4))` for primary `π` and an odd
  rational integer `m`, with exponent `((m - 1) / 2) * ((c - 1) / 2)` when `π = c + d i`.
* `TauCeti.IsPrimaryGaussian.quartic_reciprocity_intCast`: `(a / π)_4 = (π / a)_4` for primary `π`
  and a rational integer `a ≡ 1 (mod 4)`.
* `TauCeti.IsPrimaryGaussian.quartic_reciprocity_natCast_of_odd`:
  `(((-1) ^ ((q - 1) / 2) * q) / π)_4 = (π / q)_4` for primary `π` and an odd natural number `q`.

## References

* N. Xu, *Reciprocity Laws*, §5, Propositions 5.11–5.12.
* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 9, §§8–9.
-/

public section

open NumberField

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
  have hPmax : (span {π}).IsMaximal :=
    ((span_singleton_prime hp.ne_zero).mpr hp).isMaximal (by simpa using hp.ne_zero)
  -- Factor `q = (τ β) β` in `𝓞 K` using complex conjugation `τ`.
  obtain ⟨σ, _, hτ⟩ := exists_gal_apply_eq_pow_three_of_four (K := K)
  let τ := MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) σ
  obtain ⟨β, hβ, hqβ, hNβ⟩ := exists_natCast_eq_mul_of_mod_four_ne_three
    (σ := (τ : 𝓞 K →+* 𝓞 K)) hτ hq (by omega)
  simp only [RingEquiv.coe_toRingHom] at hqβ
  have hβ0 : span {β} ≠ ⊥ := by simpa using hβ
  have hτβ0 : span {τ β} ≠ ⊥ := by
    rw [← Set.image_singleton, ← map_span]
    exact (map_eq_bot_iff_of_injective τ.injective).not.mpr hβ0
  have hLmax : (span {β}).IsMaximal :=
    (isPrime_of_irreducible_absNorm (hNβ ▸ hq)).isMaximal hβ0
  have hL4 : (absNorm (span {β})).Coprime 4 := by
    rw [hNβ, Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hq1]
    rfl
  have hPL : (absNorm (span {π})).Coprime (absNorm (span {β})) := by
    refine NumberField.coprime_absNorm_of_absNorm_ne
      finrank_eq_two_of_isCyclotomicExtension_four fun hN ↦ hπq ?_
    rw [← mem_span_singleton, hNβ.symm, ← hN]
    exact absNorm_mem (span {π})
  -- Apply `powerResidueSymbol_stickelbergerPhi` at `(P, L) = (π 𝓞 K, β 𝓞 K)`.
  have hstick := powerResidueSymbol_stickelbergerPhi (span {π}) (span {β}) hL4 hPL (by decide)
  rw [hNβ, hπ.stickelbergerPhi_span_singleton_four_eq hτ, map_mul, map_pow, map_mul, map_pow]
    at hstick
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
  rw [← hstick, hconj, ← powerResidueSymbolIdeal_of_isMaximal (span {β}), hqβ, mul_comm (τ β) β,
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
    rw [hgS χ, gaussSum_frob, hχSq, AddChar.pow_mulShift, ← hqF.isUnit.unit_spec,
      gaussSum_mulShift_eq, ← hgS χ⁻¹, ← MulChar.ringHomComp_inv, inv_inv]
  have hχ_ne : χ ≠ 1 := by
    rw [MulChar.ringHomComp_ne_one_iff hf, Ne, ← orderOf_eq_one_iff, orderOf_powerResidueSymbol hP4]
    decide
  have hg_prod : gaussSum χ ψ * gaussSum χ⁻¹ ψ = χ (-1) * absNorm P := by
    rw [← mul_gaussSum_inv_eq_gaussSum χ⁻¹ ψ, MulChar.inv_apply', inv_neg_one, mul_left_comm,
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
    idealQuotientMk_span_natCast_pow_eq_idealQuotientMk_apply_of_mod_four_eq_three hq hq3 hσ π
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
  obtain ⟨ψ, hψ⟩ := exists_primitive_addChar_integralClosure (𝓞 K ⧸ P)
  have hinj : Function.Injective (Classical.arbitrary (K →+* ℂ)).toIntAlgHom :=
    RingHom.injective _
  obtain ⟨I, _, hIQ⟩ :=
    Q.exists_isPrime_comap_isIntegralClosure_map_eq (integralClosure ℤ ℂ) hinj
  let f : 𝓞 K →+* integralClosure ℤ ℂ :=
    (IsIntegralClosure.map (𝓞 K) (integralClosure ℤ ℂ)
      (Classical.arbitrary (K →+* ℂ)).toIntAlgHom).toRingHom
  have hf : Function.Injective f := IsIntegralClosure.map_injective _ _ hinj
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
    refine NumberField.coprime_absNorm_of_absNorm_ne
      finrank_eq_two_of_isCyclotomicExtension_four fun hN ↦ hπq ?_
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
  obtain ⟨γ, _, hσ⟩ := exists_gal_apply_eq_pow_three_of_four (K := K)
  let σ : 𝓞 K →+* 𝓞 K := MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) γ
  have hπQ : Ideal.Quotient.mk Q π ≠ 0 := fun h0 ↦ hNPQ <| by
    rw [← map_natCast (Ideal.Quotient.mk Q), ← Int.cast_natCast,
      RingOfIntegers.natCast_absNorm_span_singleton_of_four,
      intCast_norm_eq_mul_of_four (σ := σ) hσ, map_mul, h0, zero_mul]
  have hmk_eq : Ideal.Quotient.mk Q (powerResidueSymbol P 4 (Ideal.Quotient.mk P (-(q : 𝓞 K)))) =
      Ideal.Quotient.mk Q (powerResidueSymbol Q 4 (Ideal.Quotient.mk Q π)) :=
    mul_right_cancel₀ hNPQ
      ((mk_powerResidueSymbol_neg_natCast_mul_absNorm_of_mod_four_eq_three
        (σ := σ) hπ hq hq3 hqF hσ).trans
        (mk_pow_three_mul_pow_of_mod_four_eq_three (σ := σ) hq hq3 hπQ hσ))
  have hnegq0 : Ideal.Quotient.mk P (-(q : 𝓞 K)) ≠ 0 := by
    rw [map_neg, map_natCast, neg_ne_zero]
    exact hqF
  rw [powerResidueSymbolIdeal_of_isMaximal, powerResidueSymbolIdeal_of_isMaximal]
  exact eq_of_pow_eq_one_of_mk_eq IsPrime.ne_top' hQ4 (powerResidueSymbol_pow_eq_one hP4 hnegq0)
    (powerResidueSymbol_pow_eq_one hQ4 hπQ) hmk_eq

/-- Quartic reciprocity between a primary prime `π` and an odd rational prime `q`:
`(((-1) ^ ((q - 1) / 2) * q) / π)_4 = (π / q)_4`. -/
private theorem quartic_reciprocity_natCast_prime {π : 𝓞 K} (hπ : IsPrimaryGaussian π)
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
  set q : ℕ := p.natAbs with hq_def
  have hq : q.Prime := Int.prime_iff_natAbs_prime.mp hp_int
  have hq_odd : Odd q := Int.natAbs_odd.mpr hp_odd
  have hq2 : q ≠ 2 := fun h2 ↦ absurd (h2 ▸ hq_odd) (by decide)
  have hnat_coe :
      (-1 : K) ^ ((((q - 1) / 2 : ℕ) : ℤ) * N4) *
        ((powerResidueSymbolIdeal (span {π}) 4 (Ideal.Quotient.mk _ (q : 𝓞 K)) : 𝓞 K) : K) =
      ((powerResidueSymbolIdeal (span {(q : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) : 𝓞 K) : K) := by
    have h := congrArg ((↑) : 𝓞 K → K) (quartic_reciprocity_natCast_prime hπ hp hq hq2)
    simp only [map_mul, map_pow, ← RingOfIntegers.coe_eq_algebraMap] at h
    rwa [coe_powerResidueSymbolIdeal_mk_neg_one hπ, ← zpow_natCast, ← zpow_mul'] at h
  have hnat :
      ((powerResidueSymbolIdeal (span {π}) 4 (Ideal.Quotient.mk _ (q : 𝓞 K)) : 𝓞 K) : K) =
      ((powerResidueSymbolIdeal (span {(q : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) : 𝓞 K) : K) *
        (-1) ^ ((((q - 1) / 2 : ℕ) : ℤ) * N4) := by
    have hev : Even (2 * ((((q - 1) / 2 : ℕ) : ℤ) * N4)) := ⟨_, two_mul _⟩
    rw [← hnat_coe, mul_right_comm, ← zpow_add₀ (by norm_num), ← two_mul, hev.neg_one_zpow,
      one_mul]
  rcases Int.natAbs_eq p with hp_eq | hp_eq
  · have hexp : (p - 1) / 2 = (((q - 1) / 2 : ℕ) : ℤ) := by
      have := hq.one_le
      omega
    rw [hexp, hp_eq, ← hq_def, Int.cast_natCast, hnat]
  · have hneg : (p : 𝓞 K) = (-1) * (q : 𝓞 K) := by
      rw [hp_eq, ← hq_def, Int.cast_neg, Int.cast_natCast, neg_one_mul]
    have hspan : span {(p : 𝓞 K)} = span {(q : 𝓞 K)} := by
      rw [hp_eq, ← hq_def, Int.cast_neg, Int.cast_natCast, span_singleton_neg]
    rw [hspan, hneg]
    simp only [map_mul, ← RingOfIntegers.coe_eq_algebraMap]
    rw [coe_powerResidueSymbolIdeal_mk_neg_one hπ, hnat, mul_left_comm,
      ← zpow_add₀ (by norm_num)]
    congr 1
    obtain ⟨k, hk⟩ := hq_odd
    have h1 : (((q - 1) / 2 : ℕ) : ℤ) = k := by omega
    have h2 : (p - 1) / 2 = -((k : ℤ) + 1) := by omega
    rw [h1, h2]
    dsimp only [N4]
    exact zpow_eq_zpow_of_modEq (n := 2) (by norm_num)
      (Int.modEq_iff_dvd.mpr ⟨-(((k : ℤ) + 1) * N4), by dsimp only [N4]; ring⟩)

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
    · simp only [Int.cast_neg, Int.cast_one]
      push_cast
      rw [one_mul, coe_powerResidueSymbolIdeal_mk_neg_one hπ]
      exact zpow_eq_zpow_of_modEq (n := 2) (by norm_num)
        (Int.modEq_iff_dvd.mpr ⟨-N4, by ring⟩)
  | h₃ m' p hm'0 hp_int ih =>
    rw [Int.odd_mul] at hm
    obtain ⟨hp_odd, hm'_odd⟩ := hm
    have hp0 : span {(p : 𝓞 K)} ≠ ⊥ := by simpa using hp_int.ne_zero
    have hm'_span0 : span {(m' : 𝓞 K)} ≠ ⊥ := by simpa using hm'0
    rw [Int.cast_mul, ← span_singleton_mul_span_singleton,
      powerResidueSymbolIdeal_mul_right hp0 hm'_span0]
    simp only [map_mul, ← RingOfIntegers.coe_eq_algebraMap]
    rw [coe_quartic_reciprocity_intCast_prime hπ hp hp_int hp_odd, ih hm'_odd,
      mul_mul_mul_comm, ← zpow_add₀ (by norm_num), ← add_mul]
    congr 1
    refine zpow_eq_zpow_of_modEq (n := 2) (by norm_num) (Int.ModEq.mul_right N4 ?_)
    -- `(p * m' - 1) / 2 ≡ (p - 1) / 2 + (m' - 1) / 2 (mod 2)` for odd `p, m'`.
    obtain ⟨u, rfl⟩ := hp_odd
    obtain ⟨v, rfl⟩ := hm'_odd
    have hxy : ((2 * u + 1) * (2 * v + 1) - 1) / 2 = 2 * (u * v) + u + v := by
      have h : (2 * u + 1) * (2 * v + 1) - 1 = 2 * (2 * (u * v) + u + v) := by ring
      rw [h, Int.mul_ediv_cancel_left _ (by decide)]
    have hu : (2 * u + 1 - 1) / 2 = u := by omega
    have hv : (2 * v + 1 - 1) / 2 = v := by omega
    rw [hxy, hu, hv]
    exact Int.modEq_iff_dvd.mpr ⟨u * v, by ring⟩

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
    induction s using Multiset.induction_on with
    | empty =>
      rw [Multiset.prod_zero, span_singleton_one, absNorm_top, powerResidueSymbolIdeal_top]
      simp
    | cons p s ih =>
      have hp := hs p (Multiset.mem_cons_self p s)
      have hs' : ∀ q ∈ s, Prime q ∧ IsPrimaryGaussian q := fun q hq ↦
        hs q (Multiset.mem_cons_of_mem hq)
      have hs_prim : IsPrimaryGaussian s.prod :=
        hp.2.mul_left_iff.mp (by rwa [Multiset.prod_cons] at hx)
      have hp0 : span {p} ≠ ⊥ := by simpa using hp.1.ne_zero
      have hs0 : span {s.prod} ≠ ⊥ := by
        rw [Ne, span_singleton_eq_bot]
        exact fun h ↦ absurd (h ▸ hs_prim.odd_norm) (by simp)
      have hneg := coe_powerResidueSymbolIdeal_mk_neg_one (hp.2.mul hs_prim)
      rw [← span_singleton_mul_span_singleton, powerResidueSymbolIdeal_mul_right hp0 hs0,
        RingOfIntegers.coe_eq_algebraMap, map_mul, ← RingOfIntegers.coe_eq_algebraMap,
        ← RingOfIntegers.coe_eq_algebraMap, coe_powerResidueSymbolIdeal_mk_neg_one hp.2,
        coe_powerResidueSymbolIdeal_mk_neg_one hs_prim] at hneg
      rw [Multiset.prod_cons]
      simp only [map_mul, ← RingOfIntegers.coe_eq_algebraMap]
      rw [← span_singleton_mul_span_singleton, powerResidueSymbolIdeal_mul_right hp0 hs0]
      simp only [RingHom.map_mul, ← RingOfIntegers.coe_eq_algebraMap]
      rw [coe_quartic_reciprocity_intCast_of_prime_of_odd hp.2 hp.1 hm, ih hs' hs_prim,
        mul_mul_mul_comm, zpow_mul', zpow_mul', ← mul_zpow, hneg, ← zpow_mul']
  rw [hgen hπ, hπ.natCast_absNorm_sub_one_div_four]

/-- **Quartic reciprocity in coordinates between a primary element and an odd rational integer.**
If `K = ℚ(i)`, `π = c + d i` is primary, and `m` is an odd rational integer, then
`(m / π)_4 = (π / m)_4 · (-1) ^ (((m - 1) / 2) * ((c - 1) / 2))`, read in `K`. -/
theorem IsPrimaryGaussian.coe_quartic_reciprocity_intCast_add_mul_of_odd {ζ : K}
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
  simp only [← RingOfIntegers.coe_eq_algebraMap]
  rw [hπ.coe_quartic_reciprocity_intCast_of_odd hodd, heven.neg_one_zpow, mul_one]

/-- **Quartic reciprocity between a primary element and an odd natural number.** Let `K = ℚ(i)`,
so that `𝓞 K = ℤ[i]`, let `π` be a primary element of `𝓞 K`, and let `q` be an odd natural number.
Then `(((-1) ^ ((q - 1) / 2) * q) / π)_4 = (π / q)_4`, the symbols being taken at the principal
ideals `π 𝓞 K` and `q 𝓞 K`. If `π` and `q` are not coprime, both sides vanish. -/
theorem IsPrimaryGaussian.quartic_reciprocity_natCast_of_odd {π : 𝓞 K} (hπ : IsPrimaryGaussian π)
    {q : ℕ} (hq : Odd q) :
    powerResidueSymbolIdeal (span {π}) 4
        (Ideal.Quotient.mk _ ((-1 : 𝓞 K) ^ ((q - 1) / 2) * q)) =
      powerResidueSymbolIdeal (span {(q : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π) := by
  let a : ℤ := (-1) ^ ((q - 1) / 2) * q
  have ha_cast : (a : 𝓞 K) = (-1 : 𝓞 K) ^ ((q - 1) / 2) * q := by simp [a]
  have ha_mod : a ≡ 1 [ZMOD 4] ∧ span {(a : 𝓞 K)} = span {(q : 𝓞 K)} := by
    obtain ⟨k, hk⟩ := hq
    rcases (by omega : q % 4 = 1 ∨ q % 4 = 3) with hq1 | hq3
    · have he : Even ((q - 1) / 2) := ⟨(q - 1) / 4, by omega⟩
      refine ⟨?_, by rw [ha_cast, he.neg_one_pow, one_mul]⟩
      simp only [a, he.neg_one_pow, one_mul, Int.ModEq]
      omega
    · have ho : Odd ((q - 1) / 2) := ⟨(q - 3) / 4, by omega⟩
      refine ⟨?_, by rw [ha_cast, ho.neg_one_pow, neg_one_mul, span_singleton_neg]⟩
      simp only [a, ho.neg_one_pow, neg_one_mul, Int.ModEq]
      omega
  rw [← ha_cast, hπ.quartic_reciprocity_intCast ha_mod.1, ha_mod.2]

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

end Examples

end TauCeti
