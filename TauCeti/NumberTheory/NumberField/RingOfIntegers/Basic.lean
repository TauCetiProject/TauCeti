/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Basic facts about algebraic integers

Basic facts about tuples `y : ι → 𝓞 K` of algebraic integers and their images in `K`, about
the integers inside the ring of integers of a number field: an algebraic integer that is rational
is an integer, and about the ring of integers of the subfield `⊤`.

## Main results

* `NumberField.RingOfIntegers.coe_tuple_eq_zero_iff`: a tuple of algebraic integers is zero
  exactly when its image in `K` is zero.
* `NumberField.RingOfIntegers.exists_intCast_eq_of_coe_mem_range`: an algebraic integer that is
  rational is an integer.
* `NumberField.RingOfIntegers.algebraMap_surjective_of_eq_top`: if a subfield `F` of `K` is all
  of `K`, the map `𝓞 F → 𝓞 K` is surjective.
-/

public section

namespace NumberField.RingOfIntegers

variable {K : Type*} [Field K] {ι : Type*}

/-- A tuple of algebraic integers is zero exactly when its image in `K` is zero. -/
@[simp]
theorem coe_tuple_eq_zero_iff {y : ι → 𝓞 K} : (fun i ↦ (y i : K)) = 0 ↔ y = 0 := by
  simp [funext_iff]

/-- An algebraic integer that is rational is an integer. -/
theorem exists_intCast_eq_of_coe_mem_range [CharZero K] {y : 𝓞 K}
    (hy : (y : K) ∈ Set.range (algebraMap ℚ K)) : ∃ m : ℤ, (m : 𝓞 K) = y := by
  obtain ⟨m, hm⟩ := (IsIntegralClosure.mem_range_algebraMap ℤ (B := ℚ) (isIntegral_coe y)).mp hy
  exact ⟨m, ext (by simpa using hm)⟩

/-- If a subfield `F` of `K` is all of `K`, the map `𝓞 F → 𝓞 K` is surjective. -/
theorem algebraMap_surjective_of_eq_top {F : Subfield K} (hF : F = ⊤) :
    Function.Surjective (algebraMap (𝓞 F) (𝓞 K)) := by
  intro x
  have hx : (x : K) ∈ F := hF ▸ Subfield.mem_top _
  refine ⟨⟨⟨x, hx⟩, (isIntegral_algebraMap_iff (A := F) (B := K)).mp x.isIntegral_coe⟩, ?_⟩
  -- The algebra map `𝓞 F → 𝓞 K` is `mapRingHom (algebraMap F K)`, and `algebraMap F K` is the
  -- subfield inclusion, which sends `⟨x, hx⟩` to `x`.
  ext
  exact mapRingHom_apply (algebraMap F K) _

end NumberField.RingOfIntegers
