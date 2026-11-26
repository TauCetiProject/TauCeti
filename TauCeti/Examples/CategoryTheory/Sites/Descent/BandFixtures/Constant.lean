/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.GroupTheory.Perm.Fin
public import TauCeti.CategoryTheory.Sites.Descent.BandFixtures.Constant

/-!
# Checks for the central sections of a constant pseudofunctor

For the one-object groupoid `B(S₃)` of `S₃`, a unit of the categorical centre acts on the object
by a permutation commuting with every permutation, so it is the identity: no transposition is a
centre unit, and the constant pseudofunctor with fibre `B(S₃)`, on any category, has only the
identity central section over every object.
-/

public section

namespace TauCeti.Examples.BandFixtures

open CategoryTheory CategoryTheory.Pseudofunctor CategoryTheory.Pseudofunctor.BandFixtures

/-- The permutation by which a centre unit of `B(S₃)` acts on its object. -/
abbrev centerPerm (z : (CatCenter (SingleObj (Equiv.Perm (Fin 3))))ˣ) : Equiv.Perm (Fin 3) :=
  z.val.app (SingleObj.star _)

/-- The action of a centre unit of `B(S₃)` commutes with every permutation, by naturality. -/
theorem centerPerm_mul_comm (z : (CatCenter (SingleObj (Equiv.Perm (Fin 3))))ˣ)
    (h : Equiv.Perm (Fin 3)) : centerPerm z * h = h * centerPerm z := by
  simpa only [SingleObj.comp_as_mul] using
    CatCenter.naturality z.val (X := SingleObj.star _) (Y := SingleObj.star _) h

/-- **The `B(S₃)` Check, centre units.** Every centre unit of `B(S₃)` acts by the identity. -/
theorem centerPerm_eq_one (z : (CatCenter (SingleObj (Equiv.Perm (Fin 3))))ˣ) :
    centerPerm z = 1 := by
  have key : ∀ g : Equiv.Perm (Fin 3), (∀ h : Equiv.Perm (Fin 3), g * h = h * g) → g = 1 := by
    decide
  exact key _ (centerPerm_mul_comm z)

/-- **The `B(S₃)` Check, no transposition.** The transposition `(0 1)` is not the action of a
centre unit of `B(S₃)`. -/
theorem centerPerm_ne_swap (z : (CatCenter (SingleObj (Equiv.Perm (Fin 3))))ˣ) :
    centerPerm z ≠ Equiv.swap 0 1 := by
  rw [centerPerm_eq_one]
  decide

/-- The only centre unit of `B(S₃)` is the identity. -/
instance : Subsingleton (CatCenter (SingleObj (Equiv.Perm (Fin 3))))ˣ :=
  ⟨fun z w ↦ Units.ext <| CatCenter.ext _ _ fun _ ↦
    (centerPerm_eq_one z).trans (centerPerm_eq_one w).symm⟩

/-- **The `B(S₃)` Check, sections.** On any category, the constant pseudofunctor with fibre
`B(S₃)` has only the identity central section over every object. -/
instance {C : Type*} [Category* C] (U : C) :
    Subsingleton (IntrinsicBandSections (constant C (SingleObj (Equiv.Perm (Fin 3)))) U) :=
  (constantSectionsEquiv C _ U).symm.toEquiv.subsingleton

end TauCeti.Examples.BandFixtures
