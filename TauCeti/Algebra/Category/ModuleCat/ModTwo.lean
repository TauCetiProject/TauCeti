/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The mod-two coefficient sequence

Multiplication by two on the integers followed by reduction modulo two forms the short exact
sequence `0 → ℤ → ℤ → ℤ/2 → 0` of `ℤ`-modules. Universe lifting makes this coefficient
sequence available for homology constructions in arbitrary universes.

* `TauCeti.modTwoCoefficientSequence` packages the multiplication and reduction maps.
* `TauCeti.modTwoCoefficientSequence_shortExact` proves its short exactness.
-/

public noncomputable section

open CategoryTheory

universe u

namespace TauCeti

/-- The universe-lifted coefficient sequence `ℤ → ℤ → ℤ/2`, whose first map is multiplication
by two and whose second map is reduction modulo two. The abbreviation keeps its objects and maps
definitionally equal to the prescribed module carriers in importing modules. -/
abbrev modTwoCoefficientSequence : ShortComplex (ModuleCat.{u} ℤ) :=
  let Z := ModuleCat.of ℤ (ULift.{u} ℤ)
  let q : Z ⟶ ModuleCat.of ℤ (ULift.{u} (ZMod 2)) := ModuleCat.ofHom
    ((AddEquiv.ulift.symm.toAddMonoidHom.comp (Int.castAddHom (ZMod 2))).comp
      AddEquiv.ulift.toAddMonoidHom).toIntLinearMap
  ShortComplex.mk ((2 : ℤ) • 𝟙 Z) q (by
    ext a
    have htwo : (2 : ZMod 2) = 0 := by decide
    simp [q, Z, AddEquiv.ulift, Equiv.ulift, htwo])

/-- The first coefficient map is multiplication by two. -/
@[simp]
theorem modTwoCoefficientSequence_f :
    modTwoCoefficientSequence.{u}.f =
      (2 : ℤ) • 𝟙 (ModuleCat.of ℤ (ULift.{u} ℤ)) := rfl

/-- The second coefficient map reduces an integer modulo two. -/
@[simp↓]
theorem modTwoCoefficientSequence_g_apply (z : ℤ) :
    modTwoCoefficientSequence.{u}.g (ULift.up z) = ULift.up (z : ZMod 2) := rfl

/-- Multiplication by two and reduction modulo two form a short exact coefficient sequence,
including after universe lifting. -/
theorem modTwoCoefficientSequence_shortExact : modTwoCoefficientSequence.{u}.ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · intro a
    constructor
    · intro ha
      have ha' : (a.down : ZMod 2) = 0 := congrArg ULift.down ha
      obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a.down 2).mp ha'
      exact ⟨ULift.up b, ULift.down_injective
        (by simpa [modTwoCoefficientSequence, mul_comm] using hb.symm)⟩
    · rintro ⟨b, rfl⟩
      apply ULift.down_injective
      have htwo : (2 : ZMod 2) = 0 := by decide
      simp [modTwoCoefficientSequence, AddEquiv.ulift, Equiv.ulift, htwo]
  · intro a b hab
    apply ULift.down_injective
    have hab' := congrArg ULift.down hab
    simpa [modTwoCoefficientSequence] using hab'
  · intro a
    obtain ⟨b, hb⟩ := ZMod.intCast_surjective a.down
    exact ⟨ULift.up b, ULift.down_injective hb⟩

end TauCeti
