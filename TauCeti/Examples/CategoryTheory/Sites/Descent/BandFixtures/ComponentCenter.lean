/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ZMod.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.CategoryTheory.Sites.Descent.BandFixtures.ComponentCenter

/-!
# Checks for the centre of a disjoint union of copies of `B(C₃)`

For `I = Bool` and `G = C₃` (written multiplicatively as `Multiplicative (ZMod 3)`), the profile
`(1, 2)` acts by `1` on the `false` component and by `2` on the `true` component, its inverse is
the profile `(2, 1)`, and it is distinguished from the profile `(1, 1)` at `(true, ⋆)`. The
groupoid `Discrete Bool × B(C₃)` has nine centre units, and for empty `I` it has one.
-/

public section

namespace TauCeti.Examples.ComponentCenter

open CategoryTheory CategoryTheory.Pseudofunctor.BandFixtures

/-- The cyclic group of order three, written multiplicatively. -/
abbrev C₃ : Type := Multiplicative (ZMod 3)

/-- The profile `(1, 2)` on `Bool`: `1` at `false`, `2` at `true`. -/
abbrev profile : Bool → C₃ := fun b ↦ Multiplicative.ofAdd (if b then 2 else 1)

/-- The group component of a centre unit at `(b, ⋆)`. -/
abbrev comp (z : (CatCenter (Discrete Bool × SingleObj C₃))ˣ) (b : Bool) : C₃ :=
  (z.val.app (⟨b⟩, SingleObj.star C₃)).2

/-- **Components.** The centre of the profile `(1, 2)` acts by `1` on the `false` component and by
`2` on the `true` component, so taking the value at `false` on both components would be wrong. -/
example : comp (componentCenterUnit profile) false = Multiplicative.ofAdd 1 ∧
    comp (componentCenterUnit profile) true = Multiplicative.ofAdd 2 := by
  simp only [comp, val_componentCenterUnit, componentCenter_app_snd]
  exact ⟨rfl, rfl⟩

/-- **Inverse.** The inverse of the centre unit of `(1, 2)` is the centre of the profile `(2, 1)`,
not `(1, 2)` itself. -/
example : comp (componentCenterUnit profile)⁻¹ false = Multiplicative.ofAdd 2 ∧
    comp (componentCenterUnit profile)⁻¹ true = Multiplicative.ofAdd 1 ∧
    comp (componentCenterUnit profile)⁻¹ true ≠ comp (componentCenterUnit profile) true := by
  simp only [comp, val_componentCenterUnit, val_inv_componentCenterUnit, componentCenter_app_snd]
  decide

/-- **Distinct profiles.** The profiles `(1, 2)` and `(1, 1)` give different centre units,
distinguished at `(true, ⋆)`. -/
example : componentCenterUnit profile ≠
    componentCenterUnit (fun _ : Bool ↦ (Multiplicative.ofAdd 1 : C₃)) := fun h ↦ by
  have := congrArg (comp · true) h
  simp only [comp, val_componentCenterUnit, componentCenter_app_snd] at this
  exact absurd this (by decide)

/-- **Count.** The groupoid `Discrete Bool × B(C₃)` has nine centre units, as many as profiles. -/
example : Nat.card (CatCenter (Discrete Bool × SingleObj C₃))ˣ = 9 := by
  rw [← Nat.card_congr (componentCenterEquiv Bool C₃).toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_fun]
  simp [Fintype.card_multiplicative, ZMod.card]

/-- **Empty index.** For empty `I` there is one profile, and one centre unit. -/
example : Subsingleton (CatCenter (Discrete Empty × SingleObj C₃))ˣ :=
  (componentCenterEquiv Empty C₃).symm.toEquiv.subsingleton

end TauCeti.Examples.ComponentCenter
