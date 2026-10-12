/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.LocalProperties

/-!
# Isomorphisms of sheaves of modules are local

A morphism of sheaves of modules is an isomorphism if it is one after restriction to every
member of a cover of the terminal object. This lets one check an isomorphism involving a line
bundle, such as its tensor evaluation map, on a cover of free rank-one trivializations.

This is the module-sheaf counterpart of Mathlib's local isomorphism criterion for sheaves.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v w x

namespace SheafOfModules

variable {C : Type u} [Category.{w} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{v}} {M N : _root_.SheafOfModules.{v} R}
  {ι : Type x} {X : ι → C}

/-- A morphism of sheaves of modules that is an isomorphism on every member of a covering
family is an isomorphism globally. -/
theorem _root_.SheafOfModules.isIso_of_coversTop (hX : J.CoversTop X) (f : M ⟶ N)
    (hf : ∀ i, IsIso (f.over (X i))) : IsIso f := by
  have h : IsIso ((_root_.SheafOfModules.toSheaf R).map f) := by
    apply Sheaf.isIso_of_coversTop hX
    intro i
    -- Pullback of the underlying sheaf is definitionally the underlying sheaf of the
    -- restricted module; the two expressions carry different categorical wrappers.
    change IsIso ((_root_.SheafOfModules.toSheaf (R.over (X i))).map (f.over (X i)))
    let h := hf i
    infer_instance
  exact (isIso_iff_of_reflects_iso f (_root_.SheafOfModules.toSheaf R)).mp h

/-- A morphism of sheaves of modules is an isomorphism exactly when its restrictions to a
cover are isomorphisms. -/
theorem _root_.SheafOfModules.isIso_iff_of_coversTop (hX : J.CoversTop X) (f : M ⟶ N) :
    IsIso f ↔ ∀ i, IsIso (f.over (X i)) :=
  ⟨fun _ _ => inferInstance, _root_.SheafOfModules.isIso_of_coversTop hX f⟩

end SheafOfModules

end TauCeti
