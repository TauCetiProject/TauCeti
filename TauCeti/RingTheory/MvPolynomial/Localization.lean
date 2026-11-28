/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.GroupTheory.MonoidLocalization.Divisibility

/-!
# Divisibility in multivariate polynomial rings over away localizations

Over a commutative ring `R` and a localization `S` of `R` away from `r : R`, the multivariate
polynomial ring `MvPolynomial σ S` is the localization of `MvPolynomial σ R` at the powers of
`C r` (`MvPolynomial.isLocalization`). Consequently, any divisibility relation between images of
polynomials over `S` descends to `MvPolynomial σ R` after multiplying by a power of `C r`
(`MvPolynomial.exists_C_pow_mul_eq_mul_of_map_localization_away`).

## Main results

* `MvPolynomial.exists_C_pow_mul_eq_mul_of_map_localization_away`: if `map (algebraMap R S) p`
  divides `map (algebraMap R S) x`, then `C (r ^ k) * x = p * q₀` for some `k : ℕ` and
  `q₀ : MvPolynomial σ R`.
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

end MvPolynomial
