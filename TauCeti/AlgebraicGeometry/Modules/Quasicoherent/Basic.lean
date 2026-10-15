/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Dual
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic
public import TauCeti.CategoryTheory.Monoidal.Rigid.Subcategory

/-!
# The monoidal category of quasicoherent sheaves

For a scheme `X`, `QuasicoherentSheaf X` is the full subcategory of `X.Modules` on the
quasicoherent sheaves. It inherits the symmetric monoidal structure of `X.Modules`.

Finite free sheaves give the basic dualizable objects in the quasicoherent category. The free
sheaf on a finite type is self-dual there, with evaluation and coevaluation inherited from the
corresponding exact pairing in `X.Modules`.

Quasi-coherence is stable under pullback along an arbitrary morphism of schemes, so pullback of
modules restricts to quasicoherent sheaves.

Pullback of quasicoherent sheaves is compatible with identities and composition. In particular,
an isomorphism of schemes induces an equivalence of their quasicoherent-sheaf categories.

## Main declarations

* `TauCeti.AlgebraicGeometry.QuasicoherentSheaf X`: quasicoherent sheaves on `X`;
* `TauCeti.AlgebraicGeometry.QuasicoherentSheaf.free`: the finite free quasicoherent sheaf;
* `TauCeti.AlgebraicGeometry.QuasicoherentSheaf.exactPairingFree`: finite free quasicoherent
  sheaves are self-dual;
* `TauCeti.AlgebraicGeometry.QuasicoherentSheaf.pullback f`: the pullback of quasicoherent
  sheaves along a morphism of schemes `f`.
-/

-- The pullback comparisons follow the full-subcategory construction in
-- `TauCeti/AlgebraicGeometry/VectorBundle/Functoriality.lean`, which in turn follows
-- `TauCeti/AlgebraicGeometry/LineBundle/Functoriality.lean`.

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

namespace QuasicoherentSheaf

/-- The free sheaf on a finite type, as a quasicoherent sheaf.

This is an abbreviation so that instance search sees its underlying finite free sheaf and hence
the exact self-pairing on that sheaf. -/
abbrev free (I : Type u) [Finite I] : QuasicoherentSheaf X :=
  ⟨_root_.SheafOfModules.free (R := X.ringCatSheaf) I, by
    let F : _root_.SheafOfModules X.ringCatSheaf :=
      _root_.SheafOfModules.free (R := X.ringCatSheaf) I
    have : F.IsLocallyFree := inferInstance
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
  ObjectProperty.exactPairingFullSubcategory_evaluation_hom _ _

/-- The coevaluation of the self-duality of a finite free quasicoherent sheaf is the
coevaluation of the underlying finite free sheaf of modules. -/
@[simp]
theorem coevaluation_free_hom (I : Type u) [Finite I] :
    (η_ (free X I) (free X I)).hom =
      η_ (free X I).obj (free X I).obj :=
  ObjectProperty.exactPairingFullSubcategory_coevaluation_hom _ _

variable {X} in
/-- The pullback of quasicoherent sheaves along a morphism of schemes `f : X ⟶ Y`. -/
def pullback {Y : Scheme.{u}} (f : X ⟶ Y) :
    QuasicoherentSheaf Y ⥤ QuasicoherentSheaf X :=
  (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).lift
    ((_root_.SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι ⋙ Scheme.Modules.pullback f)
    fun E ↦ Scheme.Modules.isQuasicoherent_pullback f E.obj

variable {X} in
/-- The underlying sheaf of the pullback of a quasicoherent sheaf is its pullback as an
`𝒪_Y`-module. -/
@[simp]
lemma pullback_obj_obj {Y : Scheme.{u}} (f : X ⟶ Y) (E : QuasicoherentSheaf Y) :
    ((pullback f).obj E).obj = (Scheme.Modules.pullback f).obj E.obj :=
  (rfl)

variable {X} in
/-- Pullback acts on a morphism of quasicoherent sheaves by the underlying pullback of
modules. -/
@[simp]
lemma pullback_map_hom {Y : Scheme.{u}} (f : X ⟶ Y) {E F : QuasicoherentSheaf Y} (φ : E ⟶ F) :
    ((pullback f).map φ).hom =
      eqToHom (pullback_obj_obj f E) ≫ (Scheme.Modules.pullback f).map φ.hom ≫
        eqToHom (pullback_obj_obj f F).symm := by
  cases pullback_obj_obj f E
  cases pullback_obj_obj f F
  -- `simp` cannot remove the identities here: after `cases` the composite mixes morphisms of
  -- `X.Modules` and of `SheafOfModules X.ringCatSheaf`, which `simp` does not identify. The
  -- remaining equation is the defining equation of the lifted functor `pullback f` on morphisms.
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- Pullback of quasi-coherent modules along the identity is naturally the identity. -/
noncomputable def pullbackId (X : Scheme.{u}) :
    pullback (𝟙 X) ≅ 𝟭 (QuasicoherentSheaf X) :=
  NatIso.ofComponents (fun E => ObjectProperty.isoMk _
    ((eqToIso (pullback_obj_obj (𝟙 X) E)) ≪≫
      (Scheme.Modules.pullbackId X).app E.obj)) (by
    intro E F φ
    apply ObjectProperty.hom_ext
    -- The full-subcategory lift and its underlying module functor are definitionally equal
    -- on morphisms, so this reduces naturality to Mathlib's module comparison.
    change (Scheme.Modules.pullback (𝟙 X)).map φ.hom ≫
        (Scheme.Modules.pullbackId X).hom.app F.obj =
      (Scheme.Modules.pullbackId X).hom.app E.obj ≫ (𝟭 X.Modules).map φ.hom
    exact (Scheme.Modules.pullbackId X).hom.naturality φ.hom)

/-- The identity comparison is Mathlib's comparison on underlying modules. -/
@[simp]
theorem pullbackId_hom_app_hom (X : Scheme.{u}) (E : QuasicoherentSheaf X) :
    ((pullbackId X).hom.app E).hom =
      eqToHom (pullback_obj_obj (𝟙 X) E) ≫
        (Scheme.Modules.pullbackId X).hom.app E.obj := by
  rfl

/-- The inverse identity comparison is Mathlib's inverse on underlying modules. -/
@[simp]
theorem pullbackId_inv_app_hom (X : Scheme.{u}) (E : QuasicoherentSheaf X) :
    ((pullbackId X).inv.app E).hom =
      (Scheme.Modules.pullbackId X).inv.app E.obj ≫
        eqToHom (pullback_obj_obj (𝟙 X) E).symm := by
  rfl

/-- The underlying module of a composite restricted pullback is the composite module
pullback. -/
theorem pullbackComp_obj_obj {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (E : QuasicoherentSheaf Z) :
    ((pullback g ⋙ pullback f).obj E).obj =
      (Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f).obj E.obj :=
  (pullback_obj_obj f ((pullback g).obj E)).trans
    (congrArg (Scheme.Modules.pullback f).obj (pullback_obj_obj g E))

/-- Pullback of quasi-coherent modules respects composition. -/
noncomputable def pullbackComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  NatIso.ofComponents (fun E => ObjectProperty.isoMk _
    ((eqToIso (pullbackComp_obj_obj f g E)) ≪≫
      (Scheme.Modules.pullbackComp f g).app E.obj ≪≫
      eqToIso (pullback_obj_obj (f ≫ g) E).symm)) (by
    intro E F φ
    apply ObjectProperty.hom_ext
    -- Unfolding the full-subcategory lift on morphisms leaves the naturality square for
    -- Mathlib's comparison of the underlying module pullbacks.
    change (Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f).map φ.hom ≫
        (Scheme.Modules.pullbackComp f g).hom.app F.obj =
      (Scheme.Modules.pullbackComp f g).hom.app E.obj ≫
        (Scheme.Modules.pullback (f ≫ g)).map φ.hom
    exact (Scheme.Modules.pullbackComp f g).hom.naturality φ.hom)

/-- The composition comparison is Mathlib's comparison on underlying modules. -/
@[simp]
theorem pullbackComp_hom_app_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (E : QuasicoherentSheaf Z) :
    ((pullbackComp f g).hom.app E).hom =
      eqToHom (pullbackComp_obj_obj f g E) ≫
        (Scheme.Modules.pullbackComp f g).hom.app E.obj ≫
        eqToHom (pullback_obj_obj (f ≫ g) E).symm := by
  rfl

/-- The inverse composition comparison is Mathlib's inverse on underlying modules. -/
@[simp]
theorem pullbackComp_inv_app_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (E : QuasicoherentSheaf Z) :
    ((pullbackComp f g).inv.app E).hom =
      eqToHom (pullback_obj_obj (f ≫ g) E) ≫
        (Scheme.Modules.pullbackComp f g).inv.app E.obj ≫
        eqToHom (pullbackComp_obj_obj f g E).symm := by
  rfl

/-- An isomorphism of schemes induces an equivalence of quasi-coherent modules. -/
noncomputable def equivOfIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    QuasicoherentSheaf Y ≌ QuasicoherentSheaf X := by
  let F := pullback e.hom
  let G := pullback e.inv
  have hFG : F ⋙ G ≅ 𝟭 (QuasicoherentSheaf Y) := by
    let h := pullbackComp e.inv e.hom
    rw [e.inv_hom_id] at h
    exact h ≪≫ pullbackId Y
  have hGF : G ⋙ F ≅ 𝟭 (QuasicoherentSheaf X) := by
    let h := pullbackComp e.hom e.inv
    rw [e.hom_inv_id] at h
    exact h ≪≫ pullbackId X
  exact CategoryTheory.Equivalence.mk F G hFG.symm hGF

/-- The forward functor of the equivalence induced by a scheme isomorphism is pullback. -/
@[simp]
theorem equivOfIso_functor {X Y : Scheme.{u}} (e : X ≅ Y) :
    (equivOfIso e).functor = pullback e.hom := by
  simp only [equivOfIso, CategoryTheory.Equivalence.mk]

/-- The inverse functor of the equivalence induced by a scheme isomorphism is pullback. -/
@[simp]
theorem equivOfIso_inverse {X Y : Scheme.{u}} (e : X ≅ Y) :
    (equivOfIso e).inverse = pullback e.inv := by
  simp only [equivOfIso, CategoryTheory.Equivalence.mk]

end QuasicoherentSheaf

end


end AlgebraicGeometry

end TauCeti
