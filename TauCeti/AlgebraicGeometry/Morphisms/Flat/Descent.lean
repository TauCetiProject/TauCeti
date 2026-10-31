/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import TauCeti.RingTheory.Flat.Descent
import TauCeti.RingTheory.Flat.Tower

/-!
# Flat morphisms satisfy fpqc descent and are flat local on the source

A morphism whose base change along a surjective, flat and quasi-compact morphism is flat is
itself flat. The affine statement is the descent of flatness of a module along a faithfully
flat extension of scalars (`RingHom.Flat.codescendsAlong_faithfullyFlat`), and Mathlib's
`AlgebraicGeometry.HasRingHomProperty.descendsAlong_flat` globalizes it.

Flatness is also local on the source for the flat topology: if `f` is flat and surjective and
`f ≫ g` is flat, then `g` is flat (`AlgebraicGeometry.Flat.of_comp_surjective`). At a point `x`
the stalk map of `f` is a flat local homomorphism, hence faithfully flat, and
`Module.Flat.of_faithfullyFlat_of_flat` descends flatness from the stalk map of `f ≫ g` at `x`
to that of `g` at `f x`. No quasi-compactness is needed, because flatness is a property of the
stalk maps.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- **Flat morphisms satisfy fpqc descent.** Flatness descends along surjective, flat,
quasi-compact morphisms. -/
instance Flat.descendsAlong_surjective_inf_flat_inf_quasicompact :
    MorphismProperty.DescendsAlong @Flat.{u} (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat RingHom.Flat.codescendsAlong_faithfullyFlat

/-- **Flatness is local on the source for the flat topology.** If `f` is flat and surjective
and `f ≫ g` is flat, then `g` is flat. -/
theorem Flat.of_comp_surjective {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f]
    [Surjective f] [Flat (f ≫ g)] : Flat g := by
  refine Flat.of_stalkMap g fun y ↦ ?_
  obtain ⟨x, rfl⟩ := f.surjective y
  have hfg : ((f.stalkMap x).hom.comp (g.stalkMap (f x)).hom).Flat := by
    rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]
    exact Flat.stalkMap (f ≫ g) x
  have hf := Flat.stalkMap f x
  algebraize [(g.stalkMap (f x)).hom, (f.stalkMap x).hom,
    (f.stalkMap x).hom.comp (g.stalkMap (f x)).hom]
  -- The stalk map of `f` is a flat local homomorphism, so faithfully flat.
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    .of_flat_of_isLocalHom
  exact Module.Flat.of_faithfullyFlat_of_flat _ _ (X.presheaf.stalk x)

end AlgebraicGeometry
