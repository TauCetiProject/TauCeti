/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.GaussSum
public import Mathlib.RingTheory.Ideal.Prime

import Mathlib.Algebra.CharP.Quotient
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Divisibility and prime-ideal congruences for Gauss sums

Two basic arithmetic properties of Gauss sums `gaussSum χ ψ` over finite fields and finite
commutative rings:

* `TauCeti.gaussSum_dvd_card`: over a finite field `F`, for any multiplicative character `χ` and
  any primitive additive character `ψ` with values in a commutative ring `R`, `gaussSum χ ψ` divides
  `(Fintype.card F : R)`. When `χ = 1`, `gaussSum 1 ψ = -1`; when `χ ≠ 1`, Mathlib's
  `gaussSum_mul_gaussSum_eq_card` gives a cofactor directly.
* `TauCeti.gaussSum_mul_sub_gaussSum_mem_of_pow_eq_one`: over a finite commutative ring `F`, if `P`
  is a prime ideal of a commutative ring `R` containing a prime `q`, and `χ₂ : MulChar F R` takes
  `q`-th roots of unity on units of `F`, then `gaussSum (χ₁ * χ₂) ψ - gaussSum χ₁ ψ ∈ P`. In the
  domain `R ⧸ P` of characteristic `q`, every `q`-th root of unity equals `1`, so `χ₂` is congruent
  to `1` on units modulo `P`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Cyclotomic/Stickelberger.lean` (`New.OddPart.gaussSum_dvd_natCast_of_isPrimitive` and
`New.OddPart.gaussSum_add_sub_gaussSum_mem_centrePrime_of_nsmul_eq_zero`), generalized from
`ZMod p` and `𝓞 ℚ̄` to arbitrary finite fields, finite commutative rings, and prime ideals.
-/

@[expose] public section

namespace TauCeti

/-- Over a finite field `F`, the Gauss sum of any multiplicative character `χ` and any primitive
additive character `ψ` with values in a commutative domain `R` divides `(Fintype.card F : R)`. -/
theorem gaussSum_dvd_card {F R : Type*} [Field F] [Fintype F] [CommRing R] [IsDomain R]
    (χ : MulChar F R) {ψ : AddChar F R} (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ∣ (Fintype.card F : R) := by
  classical
  by_cases hχ : χ = 1
  · subst hχ
    have hψ_ne : ψ ≠ 1 := fun h ↦ by
      have := hψ one_ne_zero
      simp [h] at this
    rw [gaussSum_one_left hψ_ne]
    exact ⟨-(Fintype.card F : R), by ring⟩
  · exact ⟨gaussSum χ⁻¹ ψ⁻¹, (gaussSum_mul_gaussSum_eq_card hχ hψ).symm⟩

/-- Over a finite commutative ring `F`, let `P` be a prime ideal of a commutative ring `R`
containing a prime number `q`. If `χ₂ : MulChar F R` satisfies `(χ₂ x) ^ q = 1` for every unit
`x : Fˣ`, then `gaussSum (χ₁ * χ₂) ψ - gaussSum χ₁ ψ ∈ P` for all `χ₁` and `ψ`. -/
theorem gaussSum_mul_sub_gaussSum_mem_of_pow_eq_one {F R : Type*} [CommRing F] [Fintype F]
    [CommRing R] {P : Ideal R} [P.IsPrime] {q : ℕ} (hq_prime : q.Prime) (hq : (q : R) ∈ P)
    (χ₁ χ₂ : MulChar F R) (ψ : AddChar F R) (hχ₂ : ∀ x : Fˣ, χ₂ x ^ q = 1) :
    gaussSum (χ₁ * χ₂) ψ - gaussSum χ₁ ψ ∈ P := by
  classical
  have : Fact q.Prime := ⟨hq_prime⟩
  have hq0 : (q : R ⧸ P) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
    exact hq
  have : CharP (R ⧸ P) q := (CharP.charP_iff_prime_eq_zero hq_prime).mpr hq0
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  simp only [gaussSum, map_sum, map_mul]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    have hu : (Ideal.Quotient.mk P (χ₂ u) - 1) ^ q = 0 := by
      rw [sub_pow_char, one_pow, ← map_pow, hχ₂ u, map_one, sub_self]
    have h1 : Ideal.Quotient.mk P (χ₂ u) = 1 := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hu)
    simp [MulChar.mul_apply, map_mul, h1]
  · simp [MulChar.map_nonunit _ hx]

end TauCeti
