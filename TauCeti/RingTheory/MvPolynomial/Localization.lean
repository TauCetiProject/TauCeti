/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.MvPolynomial.Localization

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
  obtain ⟨qS, hqS⟩ := hdvd
  obtain ⟨⟨q₁, _, b, ⟨k, rfl⟩, rfl⟩, hq₁⟩ :=
    IsLocalization.surj ((Submonoid.powers r).map (C (σ := σ))) qS
  simp only [algebraMap_def, map_C] at hq₁
  have heq : algebraMap (MvPolynomial σ R) (MvPolynomial σ S) (C (r ^ k) * x) =
      algebraMap (MvPolynomial σ R) (MvPolynomial σ S) (p * q₁) := by
    simp only [algebraMap_def, map_mul, map_C, hqS]
    calc
      C (algebraMap R S (r ^ k)) * (map (algebraMap R S) p * qS)
          = map (algebraMap R S) p * (qS * C (algebraMap R S (r ^ k))) := by ring
      _ = map (algebraMap R S) p * map (algebraMap R S) q₁ := by rw [hq₁]
  obtain ⟨⟨_, _, ⟨m, rfl⟩, rfl⟩, hm⟩ :=
    IsLocalization.exists_of_eq (M := (Submonoid.powers r).map (C (σ := σ)))
      (S := MvPolynomial σ S) heq
  refine ⟨m + k, C (r ^ m) * q₁, ?_⟩
  calc
    C (r ^ (m + k)) * x = C (r ^ m) * (C (r ^ k) * x) := by rw [pow_add, map_mul, mul_assoc]
    _ = C (r ^ m) * (p * q₁) := hm
    _ = p * (C (r ^ m) * q₁) := by ring

end MvPolynomial
