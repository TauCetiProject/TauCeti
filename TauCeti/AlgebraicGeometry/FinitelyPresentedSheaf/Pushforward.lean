/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite

/-!
# Finite pushforward of coherent sheaves

Pushforward along a finite morphism to a locally Noetherian scheme defines an additive functor
on finitely presented sheaves. Its composite with the inclusion into module sheaves is the
ordinary pushforward. The underlying finite-presentation result is in
`TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite`.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.5.
* The Stacks Project, Tag 01Y6 (coherent pushforward along finite morphisms).
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf

noncomputable section

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]

/-- Pushforward of coherent sheaves along a finite morphism to a locally Noetherian scheme. -/
def pushforward (f : X ⟶ Y) [IsFinite f] :
    FinitelyPresentedSheaf X ⥤ FinitelyPresentedSheaf Y :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Scheme.Modules.pushforward f)
    (fun M ↦ Scheme.Modules.isFinitePresentation_pushforward_of_isFinite f M.obj)

/-- Forgetting finite presentation gives the usual pushforward, on objects and morphisms. -/
@[simp]
lemma pushforward_comp_inclusion (f : X ⟶ Y) [IsFinite f] :
    pushforward f ⋙ ObjectProperty.ι (SheafOfModules.isFinitePresentation Y.ringCatSheaf) =
      ObjectProperty.ι (SheafOfModules.isFinitePresentation X.ringCatSheaf) ⋙
        Scheme.Modules.pushforward f :=
  (rfl)

/-- Finite pushforward of coherent sheaves is additive. -/
instance (f : X ⟶ Y) [IsFinite f] : (pushforward f).Additive := by
  dsimp only [pushforward]
  constructor
  intro M N g h
  exact ObjectProperty.hom_ext _
    ((Scheme.Modules.pushforward f).map_add (f := g.hom) (g := h.hom))

end

end TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf
