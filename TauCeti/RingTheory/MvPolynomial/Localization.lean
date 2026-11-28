/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Localization
import TauCeti.RingTheory.MvPolynomial.Quotient
import TauCeti.RingTheory.MvPolynomial.RegularSequence
import TauCeti.RingTheory.QuotSMulTop
import TauCeti.RingTheory.Regular.Pair

/-!
# Divisibility in multivariate polynomial rings over away localizations

Over a commutative ring `R` and a localization `S` of `R` away from `r : R`, the multivariate
polynomial ring `MvPolynomial σ S` is the localization of `MvPolynomial σ R` at the powers of
`C r` (`MvPolynomial.isLocalization`). Consequently, any divisibility relation between images of
polynomials over `S` descends to `MvPolynomial σ R` after multiplying by a power of `C r`
(`MvPolynomial.exists_C_pow_mul_eq_mul_of_map_localization_away`).

When `r` is regular in `R` and the reduction of `p` modulo `(r)` is regular in
`MvPolynomial σ (R ⧸ Ideal.span {r})`, the pair `[C r, p]` is weakly regular, so `C (r ^ k)` can
be cancelled (`MvPolynomial.dvd_of_C_pow_mul_eq_mul`) and divisibility in `MvPolynomial σ S`
descends to divisibility in `MvPolynomial σ R` (`MvPolynomial.dvd_of_map_localization_away`).

## Main results

* `MvPolynomial.exists_C_pow_mul_eq_mul_of_map_localization_away`: if `map (algebraMap R S) p`
  divides `map (algebraMap R S) x`, then `C (r ^ k) * x = p * q₀` for some `k : ℕ` and
  `q₀ : MvPolynomial σ R`.
* `MvPolynomial.dvd_of_C_pow_mul_eq_mul`: if `r` is regular and `p` is regular modulo `(r)`, then
  `C (r ^ k) * x = p * q` implies `p ∣ x`.
* `MvPolynomial.dvd_of_map_localization_away`: if `r` is regular and `p` is regular modulo `(r)`,
  then `map (algebraMap R S) p ∣ map (algebraMap R S) x` implies `p ∣ x`.
-/

public section

namespace MvPolynomial

attribute [local instance] algebraMvPolynomial in
/-- **Denominator clearing for divisibility over an away localization.** If `p` divides `x` after
extending coefficients from `R` to a localization `S` away from `r : R`, then `C (r ^ k) * x` is a
multiple of `p` in `MvPolynomial σ R` for some `k : ℕ`. -/
theorem exists_C_pow_mul_eq_mul_of_map_localization_away
    {σ R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (r : R)
    [IsLocalization.Away r S] {p x : MvPolynomial σ R}
    (hdvd : map (algebraMap R S) p ∣ map (algebraMap R S) x) :
    ∃ (k : ℕ) (q₀ : MvPolynomial σ R), C (r ^ k) * x = p * q₀ := by
  let f := IsLocalization.toLocalizationMap ((Submonoid.powers r).map (C (σ := σ)))
    (MvPolynomial σ S)
  have hf : f p ∣ f x := by simpa [f, IsLocalization.toLocalizationMap_apply, algebraMap_def]
  obtain ⟨_, ⟨_, ⟨k, rfl⟩, rfl⟩, q₀, hq₀⟩ := f.map_dvd_map.mp hf
  exact ⟨k, q₀, by simpa [map_pow] using hq₀⟩

/-- **Divisibility descent by cancelling powers of a regular scalar.** If `r : R` is regular and
`p : MvPolynomial σ R` is regular modulo `(r)`, then `C (r ^ k) * x = p * q` implies `p ∣ x`:
`[C r, p]` is a weakly regular pair, so `C (r ^ k)` remains regular modulo `p`. -/
theorem dvd_of_C_pow_mul_eq_mul {σ R : Type*} [CommRing R] {r : R} (hr : IsLeftRegular r)
    {p : MvPolynomial σ R}
    (hp : IsLeftRegular (map (Ideal.Quotient.mk (Ideal.span {r})) p))
    {x q : MvPolynomial σ R} {k : ℕ} (h : C (r ^ k) * x = p * q) : p ∣ x := by
  let I : Ideal R := Ideal.span {r}
  have hI : Ideal.span {C (σ := σ) r} = I.map C := by
    rw [Ideal.map_span, Set.image_singleton]
  let φ : MvPolynomial σ (R ⧸ I) ≃+* MvPolynomial σ R ⧸ Ideal.span {C (σ := σ) r} :=
    (quotientEquivQuotientMvPolynomial I).toRingEquiv.trans (Ideal.quotEquivOfEq hI).symm
  have hφp : φ (map (Ideal.Quotient.mk I) p) = Ideal.Quotient.mk (Ideal.span {C (σ := σ) r}) p := by
    simp [φ, quotientEquivQuotientMvPolynomial_map_mk, Ideal.quotEquivOfEq_symm]
  have hp_quot : IsSMulRegular (QuotSMulTop (C (σ := σ) r) (MvPolynomial σ R)) p := by
    refine isSMulRegular_iff_right_eq_zero_of_smul.2 fun z hz ↦ ?_
    let e := QuotSMulTop.equivQuotSpanSingleton (C (σ := σ) r)
    have hez : e (p • z) = 0 := by rw [hz, map_zero]
    rw [map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← hφp,
      ← φ.apply_symm_apply (e z), ← map_mul] at hez
    have hz0 : φ.symm (e z) = 0 :=
      hp.isSMulRegular.right_eq_zero_of_smul (φ.injective (hez.trans (map_zero φ).symm))
    exact e.injective
      ((φ.symm.injective (hz0.trans (map_zero φ.symm).symm)).trans (map_zero e).symm)
  have hpair : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ R) [C r, p] := by
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
      RingTheory.Sequence.isWeaklyRegular_singleton_iff]
    exact ⟨isSMulRegular_C_iff.mpr hr.isSMulRegular, hp_quot⟩
  have hreg : IsSMulRegular (QuotSMulTop p (MvPolynomial σ R)) (C (σ := σ) (r ^ k)) := by
    have h1 := hpair.isSMulRegular_quotSMulTop_pow_swap 1 k
    rwa [pow_one, ← map_pow] at h1
  obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1
    (TauCeti.isSMulRegular_quotSMulTop_iff.1 hreg x q h.symm)
  exact ⟨y, hy.symm⟩

attribute [local instance] algebraMvPolynomial in
/-- **Divisibility descent from an away localization.** If `r : R` is regular and
`p : MvPolynomial σ R` is regular modulo `(r)`, then divisibility by `p` over `Localization.Away r`
(or any `IsLocalization.Away r S`) descends to `MvPolynomial σ R`. -/
theorem dvd_of_map_localization_away {σ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (r : R) [IsLocalization.Away r S] (hr : IsLeftRegular r) {p : MvPolynomial σ R}
    (hp : IsLeftRegular (map (Ideal.Quotient.mk (Ideal.span {r})) p))
    {x : MvPolynomial σ R} (hdvd : map (algebraMap R S) p ∣ map (algebraMap R S) x) :
    p ∣ x := by
  obtain ⟨k, q₀, h⟩ := exists_C_pow_mul_eq_mul_of_map_localization_away r hdvd
  exact dvd_of_C_pow_mul_eq_mul hr hp h

end MvPolynomial
