/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.InternalHom.Basic
public import TauCeti.AlgebraicGeometry.Modules.Pullback.InternalHom

/-!
# Pullback of internal Hom from a finite locally free sheaf

For a finite locally free sheaf `E` and an arbitrary sheaf of modules `F` on `Y`, the canonical
comparison `f* 𝓗om(E, F) ⟶ 𝓗om(f* E, f* F)` is an isomorphism for every scheme morphism
`f : X ⟶ Y`. No flatness assumption on `f` or finiteness assumption on `F` is needed.

The comparison for quasicoherent sources and its evaluation and curry equations are defined in
`TauCeti.AlgebraicGeometry.Modules.Pullback.InternalHom`. This module specializes its
exact-pairing invertibility criterion to the internal-Hom dual of a finite locally free sheaf.

## References

* The Stacks Project, Tag 0C6I (base change for sheaf Hom).
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X Y : Scheme.{u}} (E : FiniteLocallyFreeSheaf Y) (f : X ⟶ Y)

/-- The internal-Hom dual of `E` forms an exact pairing with `E` in sheaves of modules. -/
local instance : ExactPairing (dual E).obj E.obj :=
  exactPairingOfIsIsoDualTensorIhom (Y := E.obj)

/-- The canonical internal-Hom base-change comparison is invertible for a finite locally free
source and an arbitrary target sheaf of modules. -/
instance isIso_pullbackIhomComparison :
    IsIso (pullbackIhomComparison E.obj f) := by
  have : (dual E).obj.IsQuasicoherent := ((toQuasicoherent Y).obj (dual E)).property
  exact isIso_pullbackIhomComparison_of_exactPairing E.obj f (dual E).obj

/-- Arbitrary pullback commutes with internal Hom from a finite locally free sheaf, naturally
in every target sheaf of modules. -/
def pullbackIhomIso :
    ihom E.obj ⋙ Scheme.Modules.pullback f ≅
      Scheme.Modules.pullback f ⋙ ihom ((Scheme.Modules.pullback f).obj E.obj) :=
  asIso (pullbackIhomComparison E.obj f)

/-- The forward map of the base-change isomorphism is the canonical comparison. -/
@[simp]
theorem pullbackIhomIso_hom :
    (pullbackIhomIso E f).hom = pullbackIhomComparison E.obj f :=
  (rfl)

end

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
