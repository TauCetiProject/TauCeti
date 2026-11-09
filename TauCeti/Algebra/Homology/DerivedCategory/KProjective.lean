/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Chain maps from K-projective complexes

A morphism in the derived category from a K-projective complex can be represented by a
chain map. This is the chain-level form of Mathlib's
`CochainComplex.IsKProjective.Qh_map_bijective`, and lets one form mapping cones of derived
morphisms using specified projective models.
-/

public section

open CategoryTheory DerivedCategory

namespace CochainComplex.IsKProjective

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- Every derived morphism from a K-projective complex is represented by a chain map. -/
theorem Q_map_surjective (K L : CochainComplex C ℤ) [K.IsKProjective] :
    Function.Surjective (Q.map : (K ⟶ L) → (Q.obj K ⟶ Q.obj L)) := by
  intro f
  obtain ⟨g, hg⟩ := (Qh_map_bijective K ((HomotopyCategory.quotient _ _).obj L)).surjective
    ((quotientCompQhIso C).hom.app K ≫ f ≫ (quotientCompQhIso C).inv.app L)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨g, ?_⟩
  rw [← cancel_epi ((quotientCompQhIso C).hom.app K),
    ← quotientCompQhIso_hom_naturality, hg]
  simp

end CochainComplex.IsKProjective
