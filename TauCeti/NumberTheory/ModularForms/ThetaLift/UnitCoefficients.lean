/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.FiniteAdeleRing
import Mathlib.RingTheory.Ideal.Over

/-!
# Unit coefficients on a Weil lattice

A finite Weil idele has component `x⁻¹` above primes containing the trace-one generator
`β`, and `1` at the other primes. Both `1` and `ζ (1 - β)^j / x` lie in the lattice when
`x` divides `(β (1 - β))^j` and `ζ` is an integer unit. Over a single prime of the base,
one of these two elements generates the lattice locally at every prime in the fiber.
For the cyclotomic power basis, `x` is the cyclotomic derivative at `ζ`, so the second
vector is the last trace-dual vector multiplied by `ζ (1 - β)^j`.

The choice of these two test vectors is that of `New.Parameters.exists_hasUnitLinearForm`
in `grh/src/New/Derivatives/Vacuum/ShortVectors.lean` of [lsernau/grh-lean][short-proof].

[short-proof]: https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh
-/

public section

open IsDedekindDomain NumberField
open scoped NumberField.AdeleRing

namespace TauCeti

open scoped algebraMap

open Classical in
/-- The trace-dual candidate belongs to the lattice of the finite Weil idele. At a prime
containing `β`, division by the idele cancels the denominator. Elsewhere `β` is a local unit,
so the divisibility by `x` still clears the denominator. -/
theorem traceDualCandidate_div_mem_adicCompletionIntegers {E : Type*} [Field E] [NumberField E]
    {α : 𝔸ᶠ[E]} {β x : 𝓞 E} {j : ℕ}
    (hα : ∀ w : HeightOneSpectrum (𝓞 E), α w =
      if β ∈ w.asIdeal then algebraMap E (w.adicCompletion E) (x : E)⁻¹ else 1)
    (hdiv : x ∣ (β * (1 - β)) ^ j) (a : 𝓞 E) :
    ∀ w : HeightOneSpectrum (𝓞 E),
      algebraMap E (w.adicCompletion E) ((a : E) * ((1 - β : 𝓞 E) : E) ^ j / (x : E)) / α w ∈
        w.adicCompletionIntegers E := by
  intro w
  have hvMap (a : E) : Valued.v (algebraMap E (w.adicCompletion E) a) = w.valuation E a := by
    simp [HeightOneSpectrum.algebraMap_adicCompletion, w.valuedAdicCompletion_eq_valuation']
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, hα]
  split_ifs with hw
  · rw [← map_div₀, hvMap]
    by_cases hx : (x : E) = 0
    · simp [hx]
    · rw [div_inv_eq_mul, div_mul_cancel₀ _ hx, map_mul, map_pow]
      calc
        _ ≤ 1 * 1 := mul_le_mul (w.valuation_le_one a)
          (pow_le_one₀ zero_le (w.valuation_le_one (1 - β))) zero_le zero_le_one
        _ = _ := one_mul _
  · rw [div_one, hvMap, map_div₀, map_mul, map_pow]
    obtain ⟨c, hc⟩ := hdiv
    have hcE := congrArg (fun a : 𝓞 E ↦ (a : E)) hc
    push_cast at hcE
    have hv := congrArg (w.valuation E) hcE
    simp only [map_pow, map_mul, w.valuation_eq_one_iff_notMem.mpr hw, one_mul] at hv
    refine div_le_one_of_le₀ ?_ zero_le
    calc
      _ ≤ 1 * w.valuation E (1 - β : 𝓞 E) ^ j := by
        gcongr
        exact w.valuation_le_one a
      _ = w.valuation E x * w.valuation E c := by
        push_cast
        simpa only [one_mul] using hv
      _ ≤ _ := mul_le_of_le_one_right zero_le (w.valuation_le_one c)

open Classical in
/-- For a trace-one generator coming from the base, one of the two candidates is a unit
relative to the Weil idele at every prime over the given base prime. The same candidate
works throughout the fiber because the local test for `β` is membership in the contracted
ideal. -/
theorem exists_weil_idele_unit_coefficients {R E : Type*} [CommRing R] [Field E] [NumberField E]
    [Algebra R (𝓞 E)] {α : 𝔸ᶠ[E]ˣ} {β : R} {x : 𝓞 E}
    (hα : ∀ w : HeightOneSpectrum (𝓞 E), (α : 𝔸ᶠ[E]) w =
      if algebraMap R (𝓞 E) β ∈ w.asIdeal then
        algebraMap E (w.adicCompletion E) (x : E)⁻¹ else 1)
    (ζ : (𝓞 E)ˣ) (j : ℕ) (v : Ideal R) :
    ∃ y : E, (y = 1 ∨ y = ((ζ : 𝓞 E) : E) * ((1 - algebraMap R (𝓞 E) β : 𝓞 E) : E) ^ j /
        (x : E)) ∧ ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.under R = v →
      Valued.v (algebraMap E (w.adicCompletion E) y / (α : 𝔸ᶠ[E]) w) = 1 := by
  by_cases hβ : β ∈ v
  · refine ⟨_, Or.inr rfl, fun w hw ↦ ?_⟩
    have hb := (Ideal.mem_under R w.asIdeal).mp (hw ▸ hβ)
    have hαw := (hα w).trans (ite_eq_left hb)
    have hx : (x : E) ≠ 0 := by
      intro hx
      have hzero : (α : 𝔸ᶠ[E]) w = 0 := by simpa [hx] using hαw
      exact (Units.map (RestrictedProduct.evalMonoidHom _ w) α).ne_zero hzero
    have hu : (1 - algebraMap R (𝓞 E) β : 𝓞 E) ∉ w.asIdeal := by
      intro hc
      exact w.isPrime.ne_top (w.asIdeal.eq_top_iff_one.mpr (by
        simpa only [sub_add_cancel] using w.asIdeal.add_mem hc hb))
    have hζ : (ζ : 𝓞 E) ∉ w.asIdeal := fun hz ↦
      w.isPrime.ne_top (w.asIdeal.eq_top_of_isUnit_mem hz ζ.isUnit)
    rw [hαw, ← map_div₀, div_inv_eq_mul, div_mul_cancel₀ _ hx]
    simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, w.valuedAdicCompletion_eq_valuation',
      map_mul, map_pow, w.valuation_eq_one_iff_notMem.mpr hζ,
      w.valuation_eq_one_iff_notMem.mpr hu, one_pow, mul_one]
  · refine ⟨1, Or.inl rfl, fun w hw ↦ ?_⟩
    have hb : algebraMap R (𝓞 E) β ∉ w.asIdeal := fun h ↦
      hβ (hw ▸ (Ideal.mem_under R w.asIdeal).mpr h)
    simp [hα, hb]

end TauCeti
