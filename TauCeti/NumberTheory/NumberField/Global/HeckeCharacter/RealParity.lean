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

One half holds for every modulus. If `χ` comes from a ray class character of `𝔪`, it is trivial at
every infinite place outside `𝔪`, because the idele classes concentrated there lie in
`raySubgroup 𝔪`. Conversely, if `χ` comes from `𝔪` and is trivial at a real place `w` of `𝔪`, it
still comes from the modulus obtained by removing `w` from `𝔪`: dividing an idele congruent to one
modulo the smaller modulus by its own component at `w` makes it congruent to one modulo `𝔪`. The
conductor is the least modulus from which `χ` comes, so it omits every real place at which `χ` is
trivial.

Consequently the infinity type of a finite-order Hecke character is zero exactly when its conductor
has no real places, and only then is it the continuous infinity type of an
`AlgebraicInfinityType`. Every finite-order Hecke character is nevertheless algebraic
(`HeckeCharacter.isAlgebraic_of_isFiniteOrder`): Weil's type `A₀` compares infinity types only on
the identity component, which does not see the real signs.

## Main results

* `HeckeCharacter.infiniteComponent_eq_one_of_mem_range_ofRayClassCharacter`: a Hecke character
  coming from a ray class character of `𝔪` is trivial at every infinite place outside `𝔪`.
* `HeckeCharacter.infiniteComponent_eq_one_iff`: a finite-order Hecke character is trivial at a
  real place exactly when its real parity there is zero.
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

/-- **A Hecke character coming from a ray class character of `𝔪` is trivial at every infinite
place outside `𝔪`.** The idele classes concentrated at such a place lie in `raySubgroup 𝔪`. -/
theorem infiniteComponent_eq_one_of_mem_range_ofRayClassCharacter {𝔪 : Modulus K}
    {χ : HeckeCharacter K} (hχ : χ ∈ (ofRayClassCharacter 𝔪).range) {w : InfinitePlace K}
    (hw : ∀ w' ∈ 𝔪.infinitePart, (w' : InfinitePlace K) ≠ w) : χ.infiniteComponent w = 1 := by
  obtain ⟨η, rfl⟩ := hχ
  refine ContinuousMonoidHom.ext fun u ↦ ?_
  rw [infiniteComponent_apply, ContinuousMonoidHom.coe_one, Pi.one_apply,
    ofRayClassCharacter_apply_eq_one_of_mem_raySubgroup η (ofCompletion_mem_raySubgroup hw u)]

/-- **A finite-order Hecke character is trivial at a real place exactly when its real parity there
is zero.** Its modulus exponents vanish, so its component at `w` is `x ↦ sgn(x) ^ ε_w`. -/
theorem infiniteComponent_eq_one_iff {χ : HeckeCharacter K} (hχ : χ.IsFiniteOrder)
    (w : {w : InfinitePlace K // w.IsReal}) :
    χ.infiniteComponent w.1 = 1 ↔ χ.infinityType.realParity w = 0 := by
  have hreal : χ.realComponent w = realUnitsCharacter 0 (χ.infinityType.realParity w) := by
    rw [realComponent_eq, infinityType_eq_toContinuous_realParity hχ,
      FiniteOrderInfinityType.toContinuous_realExponent,
      FiniteOrderInfinityType.toContinuous_realParity]
  refine ⟨fun h ↦ ?_, fun h ↦ ContinuousMonoidHom.ext fun u ↦ ?_⟩
  · have h1 : χ.realComponent w = realUnitsCharacter 0 0 :=
      ContinuousMonoidHom.ext fun x ↦ by simp [h]
    exact (realUnitsCharacter_inj.mp (hreal.symm.trans h1)).2
  · have hu := DFunLike.congr_fun hreal
      (Units.mapContinuousMulEquiv (continuousMulEquivRealOfIsReal w.2) u)
    rw [realComponent_apply, ContinuousMulEquiv.symm_apply_apply] at hu
    simpa [h] using hu

open scoped Classical in
/-- A Hecke character coming from `𝔪` and trivial at a real place `w` comes from the modulus with
the same finite part and with `w` removed from the infinite part. -/
private theorem mem_range_ofRayClassCharacter_erase {𝔪 : Modulus K} {χ : HeckeCharacter K}
    (hχ : χ ∈ (ofRayClassCharacter 𝔪).range) {w : {w : InfinitePlace K // w.IsReal}}
    (hw : χ.infiniteComponent w.1 = 1) :
    χ ∈ (ofRayClassCharacter
      ⟨𝔪.finitePart, 𝔪.finitePart_ne_bot, 𝔪.infinitePart.erase w⟩).range := by
  rw [mem_range_ofRayClassCharacter_iff] at hχ ⊢
  intro c hc
  obtain ⟨x, hx, rfl⟩ := mem_raySubgroup_iff.mp hc
  obtain ⟨h₁, h₂, h₃⟩ := mem_ideleCongruenceSubgroup_iff.mp hx
  -- Dividing `x` by its own component at `w` gives an idele congruent to one modulo `𝔪`.
  let u : w.1.Completionˣ := w.1.ideleInfiniteCoord x
  have hy : x * (IdeleGroup.ofCompletion (𝓞 K) K w.1 u)⁻¹ ∈ ideleCongruenceSubgroup 𝔪 := by
    refine mem_ideleCongruenceSubgroup_iff.mpr
      ⟨fun v hv ↦ by simpa using h₁ v hv, fun v hv ↦ by simpa [Modulus.exponent_def] using h₂ v hv,
        fun w' hw' ↦ ?_⟩
    by_cases hww' : w' = w
    · subst hww'
      simp [u]
    · have hne : w'.1 ≠ w.1 := fun h ↦ hww' (Subtype.ext h)
      simpa [hne] using h₃ w' (Finset.mem_erase.mpr ⟨hww', hw'⟩)
  have hsplit : QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K) x =
      QuotientGroup.mk' _ (x * (IdeleGroup.ofCompletion (𝓞 K) K w.1 u)⁻¹) *
        IdeleClassGroup.ofCompletion (𝓞 K) K w.1 u := by
    rw [IdeleClassGroup.ofCompletion_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      ← QuotientGroup.mk_mul, inv_mul_cancel_right]
  rw [MonoidHom.mem_ker, hsplit, map_mul,
    MonoidHom.mem_ker.mp (hχ (mem_raySubgroup_iff.mpr ⟨_, hy, rfl⟩)), one_mul]
  simpa using DFunLike.congr_fun hw u

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
