/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Divisibility and additive characters in rings of integers

Two elementary facts that let character sums be formed in a ring of integers `𝓞 L` and the
resulting congruences be read in a smaller ring of integers `𝓞 K`:

* `NumberField.RingOfIntegers.algebraMap_dvd_algebraMap_iff`: for an extension of fields `L / K`,
  divisibility between elements of `𝓞 K` holds in `𝓞 K` exactly when it holds in `𝓞 L`, because
  `𝓞 K` is integrally closed in `K`;
* `AddChar.IsPrimitive.exists_ringOfIntegers`: a primitive additive character of a finite ring
  with values in a field `L` takes its values in `𝓞 L`, since they are roots of unity, and is
  still primitive there.
-/

public section

open NumberField

namespace NumberField.RingOfIntegers

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Divisibility between elements of `𝓞 K` holds in `𝓞 K` exactly when it holds in `𝓞 L`. -/
@[simp]
theorem algebraMap_dvd_algebraMap_iff {x y : 𝓞 K} :
    algebraMap (𝓞 K) (𝓞 L) x ∣ algebraMap (𝓞 K) (𝓞 L) y ↔ x ∣ y := by
  refine ⟨fun ⟨z, hz⟩ ↦ ?_, map_dvd _⟩
  obtain rfl | hx := eq_or_ne x 0
  · rw [zero_dvd_iff]
    exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))).mp
      (by rw [hz, map_zero, zero_mul])
  have hz' : algebraMap K L (y : K) = algebraMap K L (x : K) * (z : L) :=
    congr_arg (fun w : 𝓞 L ↦ (w : L)) hz
  have hx' : (x : K) ≠ 0 := by exact_mod_cast hx
  -- The quotient `y / x ∈ K` is integral over `ℤ`, as its image `z` in `L` is.
  have hint : IsIntegral ℤ ((y : K) / x) := by
    rw [← isIntegral_algebraMap_iff (A := K) (B := L), map_div₀, hz',
      mul_div_cancel_left₀ _ ((map_ne_zero _).mpr hx')]
    exact z.isIntegral_coe
  obtain ⟨w, hw⟩ : ∃ w : 𝓞 K, (w : K) = y / x :=
    ⟨⟨_, (mem_integralClosure_iff ℤ K).mpr hint⟩, rfl⟩
  refine ⟨w, RingOfIntegers.ext ?_⟩
  rw [RingOfIntegers.coe_eq_algebraMap (x * w), map_mul, ← RingOfIntegers.coe_eq_algebraMap,
    ← RingOfIntegers.coe_eq_algebraMap, hw, mul_div_cancel₀ _ hx']

end NumberField.RingOfIntegers

namespace AddChar

variable {R L : Type*} [CommRing R] [Finite R] [Field L]

/-- A primitive additive character `ψ` of a finite ring with values in a field `L` lifts to a
primitive additive character with values in the ring of integers `𝓞 L`. -/
theorem IsPrimitive.exists_ringOfIntegers {ψ : AddChar R L} (hψ : ψ.IsPrimitive) :
    ∃ ψ' : AddChar R (𝓞 L), ψ'.IsPrimitive ∧ ∀ a, (ψ' a : L) = ψ a := by
  have := Fintype.ofFinite R
  -- The values of `ψ` are roots of unity, hence integral over `ℤ`.
  have hint (a : R) : ψ a ∈ integralClosure ℤ L := by
    refine (mem_integralClosure_iff ℤ L).mpr <| IsIntegral.of_pow (Fintype.card_pos (α := R)) ?_
    rw [← map_nsmul_eq_pow, card_nsmul_eq_zero, map_zero_eq_one]
    exact isIntegral_one
  obtain ⟨g, hg⟩ : ∃ g : R → 𝓞 L, ∀ a, (g a : L) = ψ a := ⟨fun a ↦ ⟨ψ a, hint a⟩, fun _ ↦ rfl⟩
  let ψ' : AddChar R (𝓞 L) :=
    { toFun := g
      map_zero_eq_one' := RingOfIntegers.ext <| by
        rw [hg, map_zero_eq_one, RingOfIntegers.coe_eq_algebraMap, map_one]
      map_add_eq_mul' a b := RingOfIntegers.ext <| by
        rw [hg, map_add_eq_mul, RingOfIntegers.coe_eq_algebraMap (g a * g b), map_mul,
          ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap, hg, hg] }
  refine ⟨ψ', fun a ha h ↦ hψ ha ?_, hg⟩
  ext b
  rw [mulShift_apply, one_apply, ← hg]
  exact congr_arg (fun φ : AddChar R (𝓞 L) ↦ (φ b : L)) h

end AddChar
