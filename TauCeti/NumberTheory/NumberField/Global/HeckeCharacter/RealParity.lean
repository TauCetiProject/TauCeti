/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Conductor
public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.InfinityType

/-!
# Real signs and the infinite part of the conductor

A finite-order Hecke character `χ` of a number field `K` has vanishing modulus exponents, so its
component at a real place `w` is `x ↦ sgn(x) ^ ε_w` for the real parity `ε_w : ZMod 2` of its
infinity type (`HeckeCharacter.infinityType_eq_toContinuous_realParity`). This file identifies
these parities with the infinite part of the conductor of `χ`: the real place `w` divides the
conductor exactly when `ε_w = 1`, that is, exactly when `χ` is nontrivial on `K_wˣ`.

The comparison rests on two facts about an arbitrary modulus, proved in
`TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.InfinityType`. If `χ` comes from a ray class
character of `𝔪`, it is trivial at every infinite place outside `𝔪`
(`HeckeCharacter.infiniteComponent_eq_one_of_mem_range_ofRayClassCharacter`). Conversely, if `χ`
comes from `𝔪` and is trivial at a real place `w` of `𝔪`, it still comes from the modulus obtained
by removing `w` from `𝔪` (`HeckeCharacter.mem_range_ofRayClassCharacter_erase`). The conductor is
the least modulus from which `χ` comes, so it omits every real place at which `χ` is trivial.

Consequently the infinity type of a finite-order Hecke character is zero exactly when its conductor
has no real places, and only then is it the continuous infinity type of an
`AlgebraicInfinityType`. Every finite-order Hecke character is nevertheless algebraic
(`HeckeCharacter.isAlgebraic_of_isFiniteOrder`): Weil's type `A₀` compares infinity types only on
the identity component, which does not see the real signs.

## Main results

* `HeckeCharacter.mem_conductor_infinitePart_iff`: a real place divides the conductor of a
  finite-order Hecke character exactly when its real parity there is one.
* `HeckeCharacter.infinityType_eq_zero_iff`: the infinity type of a finite-order Hecke character
  vanishes exactly when its conductor has no real places.
* `HeckeCharacter.infinityType_mem_range_toContinuous_iff`: the same condition characterizes the
  finite-order characters whose infinity type comes from an `AlgebraicInfinityType`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1 and Chapter VII, §6.
* A. Weil, *Basic Number Theory*, Chapter VII, §3.
-/

public section
noncomputable section

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField

namespace TauCeti.GlobalNumberFields

namespace HeckeCharacter

variable {K : Type*} [Field K] [NumberField K]

/-- **The real places outside the conductor.** The real parity of a finite-order Hecke character at
a real place `w` is zero exactly when `w` does not divide its conductor. -/
theorem realParity_infinityType_eq_zero_iff {χ : HeckeCharacter K} (hχ : χ.IsFiniteOrder)
    (w : {w : InfinitePlace K // w.IsReal}) :
    χ.infinityType.realParity w = 0 ↔ w ∉ (χ.conductor hχ).infinitePart := by
  classical
  rw [← infiniteComponent_eq_one_iff hχ]
  refine ⟨fun h hw ↦ ?_, fun hw ↦ ?_⟩
  · -- Removing `w` from the conductor gives a modulus from which `χ` still comes.
    have hdvd := (conductor_dvd_iff hχ).mpr
      (mem_range_ofRayClassCharacter_erase (mem_range_ofRayClassCharacter_conductor hχ) h)
    exact Finset.notMem_erase w _ ((Modulus.dvd_iff.mp hdvd).2 hw)
  · exact infiniteComponent_eq_one_of_mem_range_ofRayClassCharacter
      (mem_range_ofRayClassCharacter_conductor hχ) fun w' hw' h ↦ hw (Subtype.ext h ▸ hw')

/-- **The infinite part of the conductor is the set of real signs.** A real place `w` divides the
conductor of a finite-order Hecke character exactly when its real parity at `w` is one, that is,
when the character is nontrivial on the negative elements of `K_w`. -/
theorem mem_conductor_infinitePart_iff {χ : HeckeCharacter K} (hχ : χ.IsFiniteOrder)
    (w : {w : InfinitePlace K // w.IsReal}) :
    w ∈ (χ.conductor hχ).infinitePart ↔ χ.infinityType.realParity w = 1 := by
  rw [← not_iff_not, ← realParity_infinityType_eq_zero_iff hχ]
  generalize χ.infinityType.realParity w = ε
  revert ε
  decide

/-- **The infinity type of a finite-order Hecke character vanishes exactly when its conductor has
no real places.** -/
theorem infinityType_eq_zero_iff {χ : HeckeCharacter K} (hχ : χ.IsFiniteOrder) :
    χ.infinityType = 0 ↔ (χ.conductor hχ).infinitePart = ∅ := by
  rw [infinityType_eq_toContinuous_realParity hχ, ← map_zero FiniteOrderInfinityType.toContinuous,
    FiniteOrderInfinityType.toContinuous_injective.eq_iff, Finset.eq_empty_iff_forall_notMem,
    funext_iff]
  exact forall_congr' fun w ↦ realParity_infinityType_eq_zero_iff hχ w

/-- **Finite-order Hecke characters with the infinity type of an algebraic infinity type.** The
infinity type of a finite-order Hecke character is `AlgebraicInfinityType.toContinuous n` for some
`n` exactly when its conductor has no real places. In particular a finite-order character whose
conductor contains a real place, although algebraic, does not have the infinity type of any
`AlgebraicInfinityType`. -/
theorem infinityType_mem_range_toContinuous_iff {χ : HeckeCharacter K} (hχ : χ.IsFiniteOrder) :
    χ.infinityType ∈ Set.range AlgebraicInfinityType.toContinuous ↔
      (χ.conductor hχ).infinitePart = ∅ := by
  rw [← infinityType_eq_zero_iff hχ]
  refine ⟨fun ⟨n, hn⟩ ↦ ?_, fun h ↦ ⟨0, by rw [h, map_zero]⟩⟩
  -- The modulus exponent `n` at a real place vanishes, so so does the parity `n mod 2`.
  rw [infinityType_eq_toContinuous_realParity hχ] at hn ⊢
  have hp : χ.infinityType.realParity = 0 := funext fun w ↦ by
    have he := congrArg (fun t : ContinuousInfinityType K ↦ t.realExponent w) hn
    have hpw := congrArg (fun t : ContinuousInfinityType K ↦ t.realParity w) hn
    simp only [AlgebraicInfinityType.toContinuous_realExponent,
      FiniteOrderInfinityType.toContinuous_realExponent, Int.cast_eq_zero] at he
    simpa [he] using hpw.symm
  rw [hp, map_zero]

end HeckeCharacter

end TauCeti.GlobalNumberFields
