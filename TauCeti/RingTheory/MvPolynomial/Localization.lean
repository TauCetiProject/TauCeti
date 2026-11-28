/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Divisibility in multivariate polynomial rings over away localizations

Over a commutative ring `R` and a localization `S` of `R` away from `r : R`, the multivariate
polynomial ring `MvPolynomial σ S` is the localization of `MvPolynomial σ R` at the powers of
`C r` (`MvPolynomial.isLocalization`). Consequently, any divisibility relation between images of
polynomials over `S` descends to `MvPolynomial σ R` after multiplying by a power of `C r`
(`MvPolynomial.exists_C_pow_mul_eq_mul_of_map_localization_away`).

When `r` is regular in `R` and the reduction of `p` modulo `(r)` is regular in
`MvPolynomial σ (R ⧸ Ideal.span {r})`, the factor `C (r ^ k)` can be cancelled one power of `r` at
a time (`MvPolynomial.dvd_of_C_pow_mul_eq_mul`), so divisibility in `MvPolynomial σ S` descends
to divisibility in `MvPolynomial σ R` (`MvPolynomial.dvd_of_map_localization_away`).

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
each step cancels `p` modulo `(r)` to extract a factor of `C r` from `q`, then cancels `C r`. -/
theorem dvd_of_C_pow_mul_eq_mul {σ R : Type*} [CommRing R] {r : R} (hr : IsLeftRegular r)
    {p : MvPolynomial σ R}
    (hp : IsLeftRegular (map (Ideal.Quotient.mk (Ideal.span {r})) p))
    {x q : MvPolynomial σ R} {k : ℕ} (h : C (r ^ k) * x = p * q) : p ∣ x := by
  induction k generalizing q with
  | zero =>
    rw [pow_zero, map_one, one_mul] at h
    exact ⟨q, h⟩
  | succ k ih =>
    let I : Ideal R := Ideal.span {r}
    let π : R →+* R ⧸ I := Ideal.Quotient.mk I
    have hπr : π r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    have hq0 : map π p * map π q = 0 := by
      have hmap := congrArg (map π) h
      have hpow : π (r ^ (k + 1)) = 0 := by rw [map_pow, hπr, zero_pow (Nat.succ_ne_zero k)]
      rw [map_mul, map_C, hpow, map_zero, zero_mul, map_mul] at hmap
      exact hmap.symm
    have hmapq : map π q = 0 := hp (hq0.trans (mul_zero _).symm)
    have hker : ∀ r' : R, π r' = 0 ↔ r ∣ r' := fun r' ↦
      (Ideal.Quotient.eq_zero_iff_mem (I := I)).trans Ideal.mem_span_singleton
    obtain ⟨q', hq_eq⟩ := (C_dvd_iff_map_hom_eq_zero π r hker q).mpr hmapq
    have hCr : IsLeftRegular (C (σ := σ) r) := by
      simpa only [MvPolynomial.C_apply] using
        (isLeftRegular_iff_isRegular.mp hr).monomial (m := 0) |>.left
    have hnext : C (r ^ k) * x = p * q' := hCr <| by
      calc C r * (C (r ^ k) * x)
          = C (r ^ (k + 1)) * x := by rw [pow_succ', map_mul, mul_assoc]
        _ = p * q := h
        _ = C r * (p * q') := by rw [hq_eq]; ring
    exact ih hnext

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
