/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.JacobiSum
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.StickelbergerPhi.Basic

import Mathlib.NumberTheory.LegendreSymbol.Complex

/-!
# The fourth power of the quartic Gauss sum

Let `K = ℚ(i)`, given as a number field with `IsCyclotomicExtension {4} ℚ K`, so that
`𝓞 K = ℤ[i]`, let `P = π 𝓞 K` be a prime with `π` primary, and let `χ = (· / P)_4` be the
quartic residue symbol at `P`. For a primitive additive character `ψ` of the residue field
`𝓞 K ⧸ P`, with values in an integral domain `R` into which `𝓞 K` embeds, the Gauss sum of `χ`
satisfies

`g(χ, ψ) ^ 4 = N P · π ^ 2 = π ^ 3 σ π`, where `σ` is complex conjugation.

This is the quartic analogue of the cube `g(χ, ψ) ^ 3 = N P · π` of the cubic Gauss sum
(`Ideal.gaussSum_powerResidueSymbol_three_pow_three_eq`), and it is the identity that the proof
of biquadratic reciprocity raises to the power `(q + 1) / 4` or `(q - 1) / 4` and compares with
the Frobenius congruence `g(χ, ψ) ^ q ≡ χ(q)⁻¹ g(χ, ψ)` modulo a rational prime `q`. Typical
choices of `R` are `ℂ` and the ring of integers of `ℚ(i, ζ_p)`.

It combines `g(χ, ψ) ^ 4 = q J(χ, χ) ^ 2` for any character of order `4`
(`TauCeti.gaussSum_pow_four_eq_card_mul_jacobiSum_sq`) with `J(χ, χ) = -χ (-1) π`
(`Ideal.jacobiSum_powerResidueSymbol_four_eq`); and `N P = π σ π`, where the conjugation `σ`
of `ℤ[i]` is any ring endomorphism cubing the fourth roots of unity
(`TauCeti.exists_ringHom_apply_eq_pow_three_of_four`). Conjugating the character identifies the
Stickelberger element `Φ(π 𝓞 K)` with `π · (σ π) ^ 3` for every primary Gaussian integer `π`.

## Main results

* `Ideal.gaussSum_powerResidueSymbol_four_pow_four_eq`: `g(χ, ψ) ^ 4 = N P · π ^ 2`.
* `Ideal.gaussSum_powerResidueSymbol_four_pow_four_eq_pow_three_mul`: `g(χ, ψ) ^ 4 = π ^ 3 σ π`.
* `TauCeti.IsPrimaryGaussian.stickelbergerPhi_span_singleton_four_eq`: `Φ(π 𝓞 K) = π · (σ π) ^ 3`
  for a primary element `π` of `ℤ[i]` and complex conjugation `σ`.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 9, §9.
* N. Xu, *Reciprocity Laws*, §5, Proposition 5.9, and §3, Propositions 3.4 and 3.6.
-/

public section

open NumberField

namespace Ideal

open TauCeti

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]
  {P : Ideal (𝓞 K)} [P.IsMaximal] [Fintype (𝓞 K ⧸ P)] {π : 𝓞 K}
  {R : Type*} [CommRing R] [IsDomain R] {f : 𝓞 K →+* R}

/-- **The fourth power of the quartic Gauss sum.** Let `K = ℚ(i)` and let `P = π 𝓞 K` be a prime
with `π` primary. For every injective ring homomorphism `f` from `𝓞 K` to a domain `R` and every
primitive additive character `ψ` of `𝓞 K ⧸ P` with values in `R`, the Gauss sum of the quartic
residue symbol `χ = (· / P)_4`, pushed to `R` along `f`, satisfies
`g(χ, ψ) ^ 4 = N P · (f π) ^ 2`. -/
theorem gaussSum_powerResidueSymbol_four_pow_four_eq (hπ : P = span {π})
    (hπ' : IsPrimaryGaussian π) (hf : Function.Injective f) {ψ : AddChar (𝓞 K ⧸ P) R}
    (hψ : ψ.IsPrimitive) :
    gaussSum ((powerResidueSymbol P 4).ringHomComp f) ψ ^ 4 = absNorm P * f π ^ 2 := by
  let _ := Ideal.Quotient.field P
  have hP : (absNorm P).Coprime 4 := hπ ▸ hπ'.absNorm_span_singleton_coprime_four
  have hχ : orderOf ((powerResidueSymbol P 4).ringHomComp f) = 4 := by
    rw [MulChar.orderOf_ringHomComp hf, orderOf_powerResidueSymbol hP]
  have hcard : (Fintype.card (𝓞 K ⧸ P) : R) = absNorm P := by
    rw [← Nat.card_eq_fintype_card, ← absNorm_eq_natCard]
  rw [gaussSum_pow_four_eq_card_mul_jacobiSum_sq hχ hψ, jacobiSum_ringHomComp,
    jacobiSum_powerResidueSymbol_four_eq hπ hπ', hcard]
  -- `J(χ, χ) ^ 2 = (χ (-1) π) ^ 2 = π ^ 2`, since `χ (-1) ^ 2 = χ (1) = 1`.
  have hsq : powerResidueSymbol P 4 (-1) ^ 2 = 1 := by
    rw [← map_pow, neg_one_sq, map_one]
  simp [mul_pow, ← map_pow, hsq]

/-- **The fourth power of the quartic Gauss sum, as `π ^ 3 σ π`.** Let `K = ℚ(i)`, let `P = π 𝓞 K`
be a prime with `π` primary, and let `σ` be a ring endomorphism of `𝓞 K` cubing the fourth roots
of unity, that is, complex conjugation. For every injective ring homomorphism `f` from `𝓞 K` to a
domain `R` and every primitive additive character `ψ` of `𝓞 K ⧸ P` with values in `R`, the Gauss
sum of the quartic residue symbol `χ = (· / P)_4`, pushed to `R` along `f`, satisfies
`g(χ, ψ) ^ 4 = f (π ^ 3 σ π)`. -/
theorem gaussSum_powerResidueSymbol_four_pow_four_eq_pow_three_mul (hπ : P = span {π})
    (hπ' : IsPrimaryGaussian π) {σ : 𝓞 K →+* 𝓞 K} (hσ : ∀ x : 𝓞 K, x ^ 4 = 1 → σ x = x ^ 3)
    (hf : Function.Injective f) {ψ : AddChar (𝓞 K ⧸ P) R} (hψ : ψ.IsPrimitive) :
    gaussSum ((powerResidueSymbol P 4).ringHomComp f) ψ ^ 4 = f (π ^ 3 * σ π) := by
  -- `N P = N(π) = π σ π`.
  have hN : (absNorm P : 𝓞 K) = π * σ π := by
    rw [hπ, ← Int.cast_natCast, RingOfIntegers.natCast_absNorm_span_singleton_of_four,
      intCast_norm_eq_mul_of_four hσ]
  rw [gaussSum_powerResidueSymbol_four_pow_four_eq hπ hπ' hf hψ, ← map_natCast f, hN, ← map_pow,
    ← map_mul]
  ring_nf

end Ideal

namespace TauCeti

open Ideal

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

/-- For a maximal ideal `P = π 𝓞 K` of `ℤ[i]` with `π` primary and a ring-homomorphism-like map
`σ` cubing the fourth roots of unity, `Φ(P) = π · (σ π) ^ 3`. -/
private theorem stickelbergerPhi_four_eq_of_isMaximal {P : Ideal (𝓞 K)} [P.IsMaximal] {π : 𝓞 K}
    (hπ : P = span {π}) (hπ' : IsPrimaryGaussian π)
    {F : Type*} [FunLike F (𝓞 K) (𝓞 K)] [RingHomClass F (𝓞 K) (𝓞 K)] {σ : F}
    (hσ : ∀ x : 𝓞 K, x ^ 4 = 1 → σ x = x ^ 3) :
    stickelbergerPhi P 4 = π * σ π ^ 3 := by
  let _ := Ideal.Quotient.field P
  let _ := Fintype.ofFinite (𝓞 K ⧸ P)
  have hP : (absNorm P).Coprime 4 := hπ ▸ hπ'.absNorm_span_singleton_coprime_four
  have hσ_inv : Function.LeftInverse σ σ := apply_apply_eq_self_of_four hσ
  let ι : K →+* ℂ := Classical.arbitrary _
  let f : 𝓞 K →+* ℂ := ι.comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f := ι.injective.comp RingOfIntegers.coe_injective
  have hfσ : Function.Injective (f.comp (RingHomClass.toRingHom σ)) := hf.comp hσ_inv.injective
  have hψ := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (𝓞 K ⧸ P)
  -- Conjugation inverts the quartic residue character, identifying `χ_P` with `σ ∘ (· / P)_4`.
  have hχ : (powerResidueSymbol P 4)⁻¹.ringHomComp f =
      (powerResidueSymbol P 4).ringHomComp (f.comp (RingHomClass.toRingHom σ)) := by
    refine MulChar.ext fun u ↦ ?_
    have hu4 := powerResidueSymbol_pow_eq_one hP u.ne_zero
    have h4 : powerResidueSymbol P 4 * powerResidueSymbol P 4 ^ 3 = 1 :=
      MulChar.ext fun v ↦ by
        rw [MulChar.mul_apply, MulChar.pow_apply_coe, ← pow_succ', MulChar.one_apply_coe,
          powerResidueSymbol_pow_eq_one hP v.ne_zero]
    have hinv : (powerResidueSymbol P 4)⁻¹ u = powerResidueSymbol P 4 u ^ 3 := by
      rw [inv_eq_of_mul_eq_one_right h4, MulChar.pow_apply_coe]
    simp only [MulChar.ringHomComp_apply, RingHom.comp_apply, RingHom.coe_coe, hinv, hσ _ hu4]
  apply hf
  rw [stickelbergerPhi_prime P hP (by decide) hf hψ, hχ,
    gaussSum_powerResidueSymbol_four_pow_four_eq_pow_three_mul hπ hπ'
      (σ := RingHomClass.toRingHom σ) hσ hfσ hψ,
    RingHom.comp_apply, RingHom.coe_coe, map_mul, map_pow, hσ_inv π, mul_comm]

/-- **The Stickelberger element `Φ(π 𝓞 K)` of a primary element of `ℤ[i]`.** If `K = ℚ(i)`, `π` is
primary in `𝓞 K = ℤ[i]`, and `σ` is a ring-homomorphism-like map on `𝓞 K` cubing the fourth roots
of unity (that is, complex conjugation), then `Φ(π 𝓞 K) = π · (σ π) ^ 3`. -/
theorem IsPrimaryGaussian.stickelbergerPhi_span_singleton_four_eq {π : 𝓞 K}
    (hπ : IsPrimaryGaussian π)
    {F : Type*} [FunLike F (𝓞 K) (𝓞 K)] [RingHomClass F (𝓞 K) (𝓞 K)] {σ : F}
    (hσ : ∀ x : 𝓞 K, x ^ 4 = 1 → σ x = x ^ 3) :
    stickelbergerPhi (span {π}) 4 = π * σ π ^ 3 := by
  obtain ⟨s, hs, rfl⟩ := hπ.exists_multiset_prod_eq
  induction s using Multiset.induction_on with
  | empty =>
    rw [Multiset.prod_zero, span_singleton_one, stickelbergerPhi_top, map_one, one_pow, mul_one]
  | cons p s ih =>
    have hp := hs p (Multiset.mem_cons_self p s)
    have hs' : ∀ q ∈ s, Prime q ∧ IsPrimaryGaussian q := fun q hq ↦
      hs q (Multiset.mem_cons_of_mem hq)
    have hs_prim : IsPrimaryGaussian s.prod :=
      hp.2.mul_left_iff.mp (by rwa [Multiset.prod_cons] at hπ)
    have hpmax : (span {p}).IsMaximal :=
      ((span_singleton_prime hp.1.ne_zero).mpr hp.1).isMaximal (by simpa using hp.1.ne_zero)
    have hp0 : span {p} ≠ ⊥ := by simpa using hp.1.ne_zero
    have hs0 : span {s.prod} ≠ ⊥ := by
      rw [Ne, span_singleton_eq_bot]
      exact fun h ↦ absurd (h ▸ hs_prim.odd_norm) (by simp)
    rw [Multiset.prod_cons, ← span_singleton_mul_span_singleton, stickelbergerPhi_mul hp0 hs0,
      stickelbergerPhi_four_eq_of_isMaximal rfl hp.2 hσ, ih hs' hs_prim, map_mul, mul_pow]
    ring

end TauCeti

section Examples

open Ideal

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K] {ζ : K}
  (hζ : IsPrimitiveRoot ζ 4) {P : Ideal (𝓞 K)} [P.IsMaximal] [Fintype (𝓞 K ⧸ P)]
  (hP : P = span {((-1 : ℤ) : 𝓞 K) + (2 : ℤ) * hζ.toInteger})
include hP

/- For the primary element `π = -1 + 2i` of norm `5`, an embedding `f` of `𝓞 K` into `ℂ` and the
primitive additive character `AddChar.FiniteField.primitiveChar_to_Complex` of the residue field,
the fourth power of the Gauss sum at `P = π 𝓞 K` is `f (5 (-1 + 2i) ^ 2) = f (-15 - 20i)`. The
coefficients are complex because `ℤ[i]` contains no nontrivial fifth root of unity, so it admits
no primitive additive character of a field with `5` elements. -/
example {f : 𝓞 K →+* ℂ} (hf : Function.Injective f) :
    letI := Ideal.Quotient.field P
    gaussSum ((powerResidueSymbol P 4).ringHomComp f)
        (AddChar.FiniteField.primitiveChar_to_Complex (𝓞 K ⧸ P)) ^ 4 =
      f (((-15 : ℤ) : 𝓞 K) + (-20 : ℤ) * hζ.toInteger) := by
  let _ := Ideal.Quotient.field P
  rw [gaussSum_powerResidueSymbol_four_pow_four_eq hP
      (by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide) hf
      (AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive _),
    hP, absNorm_span_singleton, hζ.norm_intCast_add_intCast_mul_toInteger_of_four, ← map_natCast f,
    ← map_pow, ← map_mul]
  congr 1
  linear_combination (20 : 𝓞 K) * hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one

end Examples
