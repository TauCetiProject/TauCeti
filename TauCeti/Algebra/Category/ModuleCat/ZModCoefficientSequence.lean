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
# The mod-`n` coefficient sequence

For a natural number `n`, multiplication by `n` on the integers followed by reduction modulo `n`
forms the sequence `ℤ → ℤ → ℤ/n` of `ℤ`-modules, which is the short exact sequence
`0 → ℤ → ℤ → ℤ/n → 0` when `n ≠ 0`. Universe lifting makes this coefficient sequence available
for homology constructions in arbitrary universes.

* `TauCeti.zmodCoefficientSequence` packages the multiplication and reduction maps.
* `TauCeti.zmodCoefficientSequence_shortExact` proves its short exactness for `n ≠ 0`.
-/

public noncomputable section

open CategoryTheory

universe u

namespace TauCeti

/-- The universe-lifted coefficient sequence `ℤ → ℤ → ℤ/n`, whose first map is multiplication
by `n` and whose second map is reduction modulo `n`. The abbreviation keeps its objects and maps
definitionally equal to the prescribed module carriers in importing modules. -/
abbrev zmodCoefficientSequence (n : ℕ) : ShortComplex (ModuleCat.{u} ℤ) :=
  let Z := ModuleCat.of ℤ (ULift.{u} ℤ)
  let q : Z ⟶ ModuleCat.of ℤ (ULift.{u} (ZMod n)) := ModuleCat.ofHom
    ((AddEquiv.ulift.symm.toAddMonoidHom.comp (Int.castAddHom (ZMod n))).comp
      AddEquiv.ulift.toAddMonoidHom).toIntLinearMap
  ShortComplex.mk ((n : ℤ) • 𝟙 Z) q (by
    ext a
    simp [q, Z, AddEquiv.ulift, Equiv.ulift])

/-- The first coefficient map is multiplication by `n`. -/
@[simp]
theorem zmodCoefficientSequence_f (n : ℕ) :
    (zmodCoefficientSequence.{u} n).f = (n : ℤ) • 𝟙 (ModuleCat.of ℤ (ULift.{u} ℤ)) := rfl

/-- The second coefficient map reduces an integer modulo `n`. -/
@[simp↓]
theorem zmodCoefficientSequence_g_apply (n : ℕ) (z : ℤ) :
    (zmodCoefficientSequence.{u} n).g (ULift.up z) = ULift.up (z : ZMod n) := rfl

/-- For `n ≠ 0`, multiplication by `n` and reduction modulo `n` form a short exact coefficient
sequence, including after universe lifting. -/
theorem zmodCoefficientSequence_shortExact (n : ℕ) [NeZero n] :
    (zmodCoefficientSequence.{u} n).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · intro a
    constructor
    · intro ha
      have ha' : (a.down : ZMod n) = 0 := congrArg ULift.down ha
      obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a.down n).mp ha'
      exact ⟨ULift.up b, ULift.down_injective
        (by simpa [zmodCoefficientSequence] using hb.symm)⟩
    · rintro ⟨b, rfl⟩
      apply ULift.down_injective
      simp [zmodCoefficientSequence, AddEquiv.ulift, Equiv.ulift]
  · intro a b hab
    apply ULift.down_injective
    have hab' := congrArg ULift.down hab
    simpa [zmodCoefficientSequence, NeZero.ne n] using hab'
  · intro a
    obtain ⟨b, hb⟩ := ZMod.intCast_surjective a.down
    exact ⟨ULift.up b, ULift.down_injective hb⟩

end TauCeti
