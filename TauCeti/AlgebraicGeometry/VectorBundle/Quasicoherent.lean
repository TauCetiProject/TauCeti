/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree

/-!
# Finite locally free sheaves as quasicoherent sheaves

Finite locally free sheaves on a scheme embed fully faithfully into the symmetric monoidal
category of quasicoherent sheaves by a symmetric monoidal functor.

## Main declarations

* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.toQuasicoherent`: the fully faithful
  symmetric monoidal inclusion;
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable (X : Scheme.{u})

namespace FiniteLocallyFreeSheaf

/-- The fully faithful symmetric monoidal inclusion of finite locally free sheaves into
quasicoherent sheaves. -/
abbrev toQuasicoherent : FiniteLocallyFreeSheaf X ⥤ QuasicoherentSheaf X :=
  ObjectProperty.ιOfLE fun E hE ↦
    let F : _root_.SheafOfModules X.ringCatSheaf := E
    have : F.IsLocallyFree := hE.1
    inferInstanceAs F.IsQuasicoherent

instance : (toQuasicoherent X).Full :=
  ObjectProperty.full_ιOfLE _

instance : (toQuasicoherent X).Faithful :=
  ObjectProperty.faithful_ιOfLE _

@[simp]
theorem toQuasicoherent_obj_obj (E : FiniteLocallyFreeSheaf X) :
    ((toQuasicoherent X).obj E).obj = E.obj :=
  rfl

@[simp]
theorem toQuasicoherent_map_hom {E F : FiniteLocallyFreeSheaf X} (f : E ⟶ F) :
    ((toQuasicoherent X).map f).hom = f.hom :=
  rfl

end FiniteLocallyFreeSheaf

end


end AlgebraicGeometry

end TauCeti
