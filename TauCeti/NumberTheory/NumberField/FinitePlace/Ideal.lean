/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# The largest value of a finite place on an ideal

Let `I` be a nonzero ideal of the ring of integers of a number field `K`, `v` a finite place of
`K` with prime `𝔭`, and `m` the multiplicity of `𝔭` in `I`. The largest value of `v` on `I` is
`N 𝔭 ^ (-m)`: every element of `I` lies in `𝔭 ^ m`, and some element of `I` does not lie in
`𝔭 ^ (m + 1)`; the upper bound holds for every ideal. This is the ideal form of Mathlib's
`NumberField.FinitePlace.apply_mul_absNorm_pow_eq_one`, which is the case of a principal ideal.

Together with Mathlib's `NumberField.FinitePlace.finprod_finitePlace_pow_multiplicity`, it reads the
norm of a nonzero ideal place by place: for `I ≠ ⊥`, the product over the finite places of the
largest values on `I` is `(N I)⁻¹`. For the coefficient ideals of a pseudo-basis of an
`𝓞 K`-lattice, this turns the index of the lattice into a product of local factors.

## Main results

* `NumberField.FinitePlace.apply_mul_absNorm_pow_le_one`: an element `x` of `I` has
  `v x * N 𝔭 ^ m ≤ 1`.
* `NumberField.FinitePlace.exists_mem_apply_mul_absNorm_pow_eq_one`: for `I ≠ ⊥` some `x ∈ I`
  attains `v x * N 𝔭 ^ m = 1`.
-/

public section

open Ideal

namespace NumberField.FinitePlace

variable {K : Type*} [Field K] [NumberField K]

/-- **An element of an ideal is bounded at a finite place by the multiplicity of its prime.**
If `𝔭 ^ m` is the exact power of the prime of `v` dividing `I`, every `x ∈ I` has
`v x ≤ N 𝔭 ^ (-m)`. -/
theorem apply_mul_absNorm_pow_le_one (v : FinitePlace K) {I : Ideal (𝓞 K)} {x : 𝓞 K}
    (hx : x ∈ I) :
    v x * v.maximalIdeal.asIdeal.absNorm ^ multiplicity v.maximalIdeal.asIdeal I ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  set 𝔭 := v.maximalIdeal.asIdeal
  -- `𝔭 ^ m` divides `I`, hence `span {x}`, so `m` is at most the multiplicity of `𝔭` in `x`.
  have hspan : span {x} ≠ (⊥ : Ideal (𝓞 K)) := mt span_singleton_eq_bot.mp hx0
  have hle : multiplicity 𝔭 I ≤ multiplicity 𝔭 (span {x}) :=
    (FiniteMultiplicity.of_prime_left v.maximalIdeal.prime hspan).pow_dvd_iff_le_multiplicity.mp
      ((pow_multiplicity_dvd 𝔭 I).trans (dvd_iff_le.mpr ((span_singleton_le_iff_mem _).mpr hx)))
  calc v x * (absNorm 𝔭 : ℝ) ^ multiplicity 𝔭 I
      ≤ v x * (absNorm 𝔭 : ℝ) ^ multiplicity 𝔭 (span {x}) := by
        gcongr
        exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v.maximalIdeal).le
    _ = 1 := v.apply_mul_absNorm_pow_eq_one hx0

/-- **A nonzero ideal attains its bound at a finite place.** If `𝔭 ^ m` is the exact power of
the prime of `v` dividing `I ≠ ⊥`, some `x ∈ I` has `v x = N 𝔭 ^ (-m)`. -/
theorem exists_mem_apply_mul_absNorm_pow_eq_one (v : FinitePlace K) {I : Ideal (𝓞 K)}
    (hI : I ≠ ⊥) :
    ∃ x ∈ I, v x * v.maximalIdeal.asIdeal.absNorm ^ multiplicity v.maximalIdeal.asIdeal I = 1 := by
  set 𝔭 := v.maximalIdeal.asIdeal
  have hfin : FiniteMultiplicity 𝔭 I := .of_prime_left v.maximalIdeal.prime hI
  -- Some element of `I` lies outside `𝔭 ^ (m + 1)`, and its multiplicity is exactly `m`.
  obtain ⟨x, hxI, hx⟩ : ∃ x ∈ I, x ∉ 𝔭 ^ (multiplicity 𝔭 I + 1) := by
    by_contra! h
    exact hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _) (dvd_iff_le.mpr h)
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (zero_mem _)
  have hmul : multiplicity 𝔭 (span {x}) = multiplicity 𝔭 I :=
    multiplicity_eq_of_dvd_of_not_dvd
      ((pow_multiplicity_dvd 𝔭 I).trans (dvd_iff_le.mpr ((span_singleton_le_iff_mem _).mpr hxI)))
      (fun h ↦ hx ((span_singleton_le_iff_mem _).mp (le_of_dvd h)))
  exact ⟨x, hxI, hmul ▸ v.apply_mul_absNorm_pow_eq_one hx0⟩

end NumberField.FinitePlace
