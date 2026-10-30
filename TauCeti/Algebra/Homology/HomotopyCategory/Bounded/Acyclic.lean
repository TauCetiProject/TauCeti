/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import TauCeti.Algebra.Homology.HomotopyCategory.Bounded.Basic

/-!
# Acyclic objects and quasi-isomorphisms in the bounded homotopy category

Let `C` be an abelian category. This file defines the acyclic objects
`TauCeti.HomotopyCategory.Bounded.subcategoryAcyclic` and the quasi-isomorphisms
`TauCeti.HomotopyCategory.Bounded.quasiIso` of the homotopy category of bounded cochain
complexes, by restriction along the inclusion into the homotopy category. A morphism is a
quasi-isomorphism exactly when its cone is acyclic
(`TauCeti.HomotopyCategory.Bounded.quasiIso_eq_subcategoryAcyclic_trW`), so the
quasi-isomorphisms are compatible with the shift.

## References

* Mathlib's `Mathlib/Algebra/Homology/HomotopyCategory/Plus.lean`, which defines the
  corresponding notions for bounded below complexes.
-/

public section

open CategoryTheory

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace HomotopyCategory.Bounded

variable (C)

/-- The property of objects of `TauCeti.HomotopyCategory.Bounded C` which are acyclic. -/
abbrev subcategoryAcyclic : ObjectProperty (HomotopyCategory.Bounded C) :=
  (_root_.HomotopyCategory.subcategoryAcyclic C).inverseImage (ι C)

variable {C} in
/-- An object of the bounded homotopy category is acyclic exactly when it is acyclic in the
homotopy category. -/
lemma mem_subcategoryAcyclic_iff (K : HomotopyCategory.Bounded C) :
    subcategoryAcyclic C K ↔ _root_.HomotopyCategory.subcategoryAcyclic C K.obj :=
  Iff.rfl

/-- The quasi-isomorphisms in the homotopy category of bounded cochain complexes. -/
def quasiIso : MorphismProperty (HomotopyCategory.Bounded C) :=
  (_root_.HomotopyCategory.quasiIso C (.up ℤ)).inverseImage (ι C)

variable {C} in
/-- A morphism of bounded complexes is a quasi-isomorphism when it is one in the homotopy
category. -/
lemma quasiIso_iff {K L : HomotopyCategory.Bounded C} (f : K ⟶ L) :
    quasiIso C f ↔ _root_.HomotopyCategory.quasiIso C (.up ℤ) f.hom :=
  Iff.rfl

/-- A morphism of bounded complexes is a quasi-isomorphism exactly when its cone is acyclic. -/
lemma quasiIso_eq_subcategoryAcyclic_trW : quasiIso C = (subcategoryAcyclic C).trW := by
  ext K L f
  rw [quasiIso_iff, _root_.HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
    ObjectProperty.inverseImage_trW_iff, ObjectProperty.ι_map]

instance : (quasiIso C).IsCompatibleWithShift ℤ := by
  rw [quasiIso_eq_subcategoryAcyclic_trW]
  infer_instance

end HomotopyCategory.Bounded

end TauCeti
