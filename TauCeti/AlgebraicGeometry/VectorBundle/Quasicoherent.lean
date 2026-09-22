/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Dual
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
public import TauCeti.CategoryTheory.Monoidal.Rigid.Subcategory

/-!
# The monoidal category of quasicoherent sheaves

For a scheme `X`, `QuasicoherentSheaf X` is the full subcategory of `X.Modules` on the
quasicoherent sheaves. It inherits the symmetric monoidal structure of `X.Modules`. Finite
locally free sheaves embed fully faithfully into this category by a symmetric monoidal functor.

Finite free sheaves give the basic dualizable objects in the quasicoherent category. The free
sheaf on a finite type is self-dual there, with evaluation and coevaluation inherited from the
corresponding exact pairing in `X.Modules`.

## Main declarations

* `TauCeti.AlgebraicGeometry.QuasicoherentSheaf X`: quasicoherent sheaves on `X`;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.toQuasicoherent`: the fully faithful
  symmetric monoidal inclusion;
* `TauCeti.AlgebraicGeometry.QuasicoherentSheaf.free`: the finite free quasicoherent sheaf;
* `TauCeti.AlgebraicGeometry.QuasicoherentSheaf.exactPairingFree`: finite free quasicoherent
  sheaves are self-dual.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable (X : Scheme.{u})

attribute [local instance] monoidalCategorySheafOfModules

/-- The symmetry of `X.Modules`, stated for the unfolded type `SheafOfModules X.ringCatSheaf`,
which typeclass search does not see through the definition of `Scheme.Modules`. -/
local instance symmetricCategorySheafOfModules : SymmetricCategory
    (_root_.SheafOfModules X.ringCatSheaf) :=
  _root_.AlgebraicGeometry.Scheme.Modules.instSymmetricCategory X

/-- Quasi-coherence is a monoidal property of `SheafOfModules X.ringCatSheaf`, stated for that
unfolded type rather than for `X.Modules`. -/
local instance isMonoidalIsQuasicoherent : ObjectProperty.IsMonoidal
    (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf) :=
  _root_.AlgebraicGeometry.Scheme.Modules.isMonoidal_isQuasicoherent X

/-- The full category of quasicoherent sheaves of modules on a scheme. -/
abbrev QuasicoherentSheaf : Type _ :=
  (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory

/-- The symmetric monoidal structure on quasicoherent sheaves inherited from `X.Modules`. -/
instance : MonoidalCategory (QuasicoherentSheaf X) :=
  @ObjectProperty.fullMonoidalSubcategory X.Modules _
    (_root_.AlgebraicGeometry.Scheme.Modules.instMonoidalCategory X)
    (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf)
    (_root_.AlgebraicGeometry.Scheme.Modules.isMonoidal_isQuasicoherent X)

/-- The symmetry on quasicoherent sheaves inherited from `X.Modules`. -/
instance : SymmetricCategory (QuasicoherentSheaf X) :=
  ObjectProperty.fullSymmetricSubcategory _

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

namespace QuasicoherentSheaf

/-- The free sheaf on a finite type, as a quasicoherent sheaf.

This is an abbreviation so that instance search sees its underlying finite free sheaf and hence
the exact self-pairing on that sheaf. -/
abbrev free (I : Type u) [Finite I] : QuasicoherentSheaf X :=
  ⟨_root_.SheafOfModules.free (R := X.ringCatSheaf) I, by
    let F : _root_.SheafOfModules X.ringCatSheaf :=
      _root_.SheafOfModules.free (R := X.ringCatSheaf) I
    have : F.IsLocallyFree := by
      simpa [F] using (FiniteLocallyFreeSheaf.free X I).property.1
    exact inferInstanceAs F.IsQuasicoherent⟩

@[simp]
theorem free_obj (I : Type u) [Finite I] :
    (free X I).obj = _root_.SheafOfModules.free (R := X.ringCatSheaf) I :=
  rfl

/-- The free quasicoherent sheaf on a finite type is self-dual. -/
instance exactPairingFree (I : Type u) [Finite I] :
    ExactPairing (free X I) (free X I) :=
  ObjectProperty.exactPairingFullSubcategory _ _

/-- The chosen left dual of a finite free quasicoherent sheaf is itself. -/
instance hasLeftDualFree (I : Type u) [Finite I] : HasLeftDual (free X I) where
  leftDual := free X I

/-- The chosen right dual of a finite free quasicoherent sheaf is itself. -/
instance hasRightDualFree (I : Type u) [Finite I] : HasRightDual (free X I) where
  rightDual := free X I

@[simp]
theorem leftDual_free (I : Type u) [Finite I] :
    HasLeftDual.leftDual (Y := free X I) = free X I :=
  rfl

@[simp]
theorem rightDual_free (I : Type u) [Finite I] :
    HasRightDual.rightDual (X := free X I) = free X I :=
  rfl

/-- The evaluation of the self-duality of a finite free quasicoherent sheaf is the evaluation of
the underlying finite free sheaf of modules. -/
@[simp]
theorem evaluation_free_hom (I : Type u) [Finite I] :
    (ε_ (free X I) (free X I)).hom =
      ε_ (free X I).obj (free X I).obj :=
  rfl

/-- The coevaluation of the self-duality of a finite free quasicoherent sheaf is the
coevaluation of the underlying finite free sheaf of modules. -/
@[simp]
theorem coevaluation_free_hom (I : Type u) [Finite I] :
    (η_ (free X I) (free X I)).hom =
      η_ (free X I).obj (free X I).obj :=
  rfl

end QuasicoherentSheaf

end


end AlgebraicGeometry

end TauCeti
