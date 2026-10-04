/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Basic
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Pushforward of quasicoherent modules along morphisms of spectra

Let `φ : R ⟶ S` be a morphism of commutative rings. Pushforward along the induced morphism
`Spec S ⟶ Spec R` preserves quasicoherent modules. Indeed, Mathlib identifies quasicoherence on
a spectrum with invertibility of the canonical map from the sheaf associated to global sections,
and proves that this map remains invertible after pushforward along `Spec φ`.

The resulting functor `QuasicoherentSheaf.pushforwardSpecMap` is the pushforward operation along
a morphism of spectra. It is compatible with identities and composition of ring maps. This
calculation is the affine-local input for constructing the
quasicoherent coordinate algebra `p_* 𝒪_V` of an affine morphism `p : V ⟶ X`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward_specMap`: pushforward along a
  morphism of spectra preserves quasicoherence;
* `TauCeti.AlgebraicGeometry.QuasicoherentSheaf.pushforwardSpecMap`: the induced functor on
  quasicoherent sheaves;
* `TauCeti.AlgebraicGeometry.QuasicoherentSheaf.pushforwardSpecMapId`,
  `TauCeti.AlgebraicGeometry.QuasicoherentSheaf.pushforwardSpecMapComp`: its compatibility with
  identities and composition.

## References

* The Stacks Project, Tag 01LC: pushforward along a quasi-compact and quasi-separated morphism
  preserves quasi-coherence. The case of a morphism of spectra is the one formalized here.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

universe u

noncomputable section

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- Pushforward of a quasicoherent module along `Spec S ⟶ Spec R` is quasicoherent. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward_specMap
    (M : (Spec S).Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward (Spec.map f)).obj M).IsQuasicoherent :=
  (_root_.AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ _).2
    (_root_.AlgebraicGeometry.isIso_fromTildeΓ_pushforward f M)

namespace AlgebraicGeometry.QuasicoherentSheaf

variable {R S : CommRingCat.{u}}

/-- Pushforward of quasicoherent sheaves along the morphism of spectra induced by a ring
homomorphism. -/
def pushforwardSpecMap (f : R ⟶ S) :
    QuasicoherentSheaf (Spec S) ⥤ QuasicoherentSheaf (Spec R) :=
  (_root_.SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).lift
    ((_root_.SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).ι ⋙
      Scheme.Modules.pushforward (Spec.map f))
    fun M ↦ Scheme.Modules.isQuasicoherent_pushforward_specMap f M.obj

/-- The underlying module of affine quasicoherent pushforward is ordinary module pushforward. -/
@[simp]
theorem pushforwardSpecMap_obj_obj (f : R ⟶ S) (M : QuasicoherentSheaf (Spec S)) :
    ((pushforwardSpecMap f).obj M).obj =
      (Scheme.Modules.pushforward (Spec.map f)).obj M.obj :=
  (rfl)

/-- Affine quasicoherent pushforward acts on morphisms by ordinary module pushforward. -/
@[simp]
theorem pushforwardSpecMap_map_hom (f : R ⟶ S) {M N : QuasicoherentSheaf (Spec S)}
    (g : M ⟶ N) :
    ((pushforwardSpecMap f).map g).hom =
      eqToHom (pushforwardSpecMap_obj_obj f M) ≫
        (Scheme.Modules.pushforward (Spec.map f)).map g.hom ≫
          eqToHom (pushforwardSpecMap_obj_obj f N).symm := by
  cases pushforwardSpecMap_obj_obj f M
  cases pushforwardSpecMap_obj_obj f N
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

variable (R) in
/-- Affine quasicoherent pushforward along the identity ring map is naturally the identity. -/
def pushforwardSpecMapId : pushforwardSpecMap (𝟙 R) ≅ 𝟭 (QuasicoherentSheaf (Spec R)) :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (eqToIso (pushforwardSpecMap_obj_obj (𝟙 R) M) ≪≫
      (Scheme.Modules.pushforwardCongr (Spec.map_id R)).app M.obj ≪≫
      (Scheme.Modules.pushforwardId (Spec R)).app M.obj)) (by
    intro M N φ
    apply ObjectProperty.hom_ext
    -- The full-subcategory lift and ordinary module pushforward agree definitionally on
    -- morphisms, so this is the naturality square of Mathlib's module comparison.
    exact (Scheme.Modules.pushforwardCongr (Spec.map_id R) ≪≫
      Scheme.Modules.pushforwardId (Spec R)).hom.naturality φ.hom)

variable (R) in
/-- The identity comparison is Mathlib's comparison on underlying modules. -/
@[simp]
theorem pushforwardSpecMapId_hom_app_hom (M : QuasicoherentSheaf (Spec R)) :
    ((pushforwardSpecMapId R).hom.app M).hom =
      eqToHom (pushforwardSpecMap_obj_obj (𝟙 R) M) ≫
        (Scheme.Modules.pushforwardCongr (Spec.map_id R)).hom.app M.obj ≫
        (Scheme.Modules.pushforwardId (Spec R)).hom.app M.obj := by
  rfl

variable (R) in
/-- The inverse identity comparison is Mathlib's inverse on underlying modules. -/
@[simp]
theorem pushforwardSpecMapId_inv_app_hom (M : QuasicoherentSheaf (Spec R)) :
    ((pushforwardSpecMapId R).inv.app M).hom =
      (Scheme.Modules.pushforwardId (Spec R)).inv.app M.obj ≫
        (Scheme.Modules.pushforwardCongr (Spec.map_id R)).inv.app M.obj ≫
        eqToHom (pushforwardSpecMap_obj_obj (𝟙 R) M).symm := by
  rfl

/-- The underlying module of a composite affine quasicoherent pushforward is the composite
module pushforward. -/
theorem pushforwardSpecMapComp_obj_obj {T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (M : QuasicoherentSheaf (Spec T)) :
    ((pushforwardSpecMap g ⋙ pushforwardSpecMap f).obj M).obj =
      (Scheme.Modules.pushforward (Spec.map g) ⋙
        Scheme.Modules.pushforward (Spec.map f)).obj M.obj :=
  (rfl)

/-- Affine quasicoherent pushforward respects composition of ring maps. -/
def pushforwardSpecMapComp {T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    pushforwardSpecMap g ⋙ pushforwardSpecMap f ≅ pushforwardSpecMap (f ≫ g) :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (eqToIso (pushforwardSpecMapComp_obj_obj f g M) ≪≫
      (Scheme.Modules.pushforwardComp (Spec.map g) (Spec.map f)).app M.obj ≪≫
      (Scheme.Modules.pushforwardCongr (Spec.map_comp f g).symm).app M.obj ≪≫
      eqToIso (pushforwardSpecMap_obj_obj (f ≫ g) M).symm)) (by
    intro M N φ
    apply ObjectProperty.hom_ext
    -- As for `pushforwardSpecMapId`, this is the naturality square of the module comparison.
    exact (Scheme.Modules.pushforwardComp (Spec.map g) (Spec.map f) ≪≫
      Scheme.Modules.pushforwardCongr (Spec.map_comp f g).symm).hom.naturality φ.hom)

/-- The composition comparison is Mathlib's comparison on underlying modules. -/
@[simp]
theorem pushforwardSpecMapComp_hom_app_hom {T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (M : QuasicoherentSheaf (Spec T)) :
    ((pushforwardSpecMapComp f g).hom.app M).hom =
      eqToHom (pushforwardSpecMapComp_obj_obj f g M) ≫
        (Scheme.Modules.pushforwardComp (Spec.map g) (Spec.map f)).hom.app M.obj ≫
        (Scheme.Modules.pushforwardCongr (Spec.map_comp f g).symm).hom.app M.obj ≫
        eqToHom (pushforwardSpecMap_obj_obj (f ≫ g) M).symm := by
  rfl

/-- The inverse composition comparison is Mathlib's inverse on underlying modules. -/
@[simp]
theorem pushforwardSpecMapComp_inv_app_hom {T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (M : QuasicoherentSheaf (Spec T)) :
    ((pushforwardSpecMapComp f g).inv.app M).hom =
      eqToHom (pushforwardSpecMap_obj_obj (f ≫ g) M) ≫
        (Scheme.Modules.pushforwardCongr (Spec.map_comp f g).symm).inv.app M.obj ≫
        (Scheme.Modules.pushforwardComp (Spec.map g) (Spec.map f)).inv.app M.obj ≫
        eqToHom (pushforwardSpecMapComp_obj_obj f g M).symm := by
  rfl

end AlgebraicGeometry.QuasicoherentSheaf

end

end TauCeti
