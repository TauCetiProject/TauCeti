/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Pushforward of quasicoherent sheaves along morphisms of spectra

Let `φ : R ⟶ S` be a morphism of commutative rings. The induced morphism
`Spec S ⟶ Spec R` is affine, hence quasi-compact and separated, so pushforward along it
preserves quasicoherent modules by
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward`.

The resulting functor `QuasicoherentSheaf.pushforwardSpecMap` is the pushforward operation along
a morphism of spectra. It is compatible with identities and composition of ring maps. This
calculation is the affine-local input for constructing the
quasicoherent coordinate algebra `p_* 𝒪_V` of an affine morphism `p : V ⟶ X`.

## Main declarations

* `TauCeti.AlgebraicGeometry.QuasicoherentSheaf.pushforwardSpecMap`: the induced functor on
  quasicoherent sheaves;
* `TauCeti.AlgebraicGeometry.QuasicoherentSheaf.pushforwardSpecMapId`,
  `TauCeti.AlgebraicGeometry.QuasicoherentSheaf.pushforwardSpecMapComp`: its compatibility with
  identities and composition.
* `TauCeti.AlgebraicGeometry.QuasicoherentSheaf.pullbackPushforwardSpecMapAdjunction`: pullback
  of quasicoherent sheaves along a morphism of spectra is left adjoint to this pushforward.

## References

* The Stacks Project, Tag 01LC: pushforward along a quasi-compact and quasi-separated morphism
  preserves quasi-coherence.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

universe u

noncomputable section

namespace AlgebraicGeometry.QuasicoherentSheaf

variable {R S : CommRingCat.{u}}

/-- Pushforward of quasicoherent sheaves along the morphism of spectra induced by a ring
homomorphism. -/
-- Expose the lift so its underlying objects and morphisms can be used directly in exported
-- comparison formulas, without equality transports through the module category.
@[expose]
def pushforwardSpecMap (f : R ⟶ S) :
    QuasicoherentSheaf (Spec S) ⥤ QuasicoherentSheaf (Spec R) :=
  (_root_.SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).lift
    ((_root_.SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).ι ⋙
      Scheme.Modules.pushforward (Spec.map f))
    fun M ↦ Scheme.Modules.isQuasicoherent_pushforward M.obj (Spec.map f)

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
      (Scheme.Modules.pushforward (Spec.map f)).map g.hom := by
  rfl

variable (R) in
/-- Affine quasicoherent pushforward along the identity ring map is naturally the identity. -/
def pushforwardSpecMapId : pushforwardSpecMap (𝟙 R) ≅ 𝟭 (QuasicoherentSheaf (Spec R)) :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    ((Scheme.Modules.pushforwardCongr (Spec.map_id R)).app M.obj ≪≫
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
      (Scheme.Modules.pushforwardCongr (Spec.map_id R)).hom.app M.obj ≫
        (Scheme.Modules.pushforwardId (Spec R)).hom.app M.obj := by
  rfl

variable (R) in
/-- The inverse identity comparison is Mathlib's inverse on underlying modules. -/
@[simp]
theorem pushforwardSpecMapId_inv_app_hom (M : QuasicoherentSheaf (Spec R)) :
    ((pushforwardSpecMapId R).inv.app M).hom =
      (Scheme.Modules.pushforwardId (Spec R)).inv.app M.obj ≫
        (Scheme.Modules.pushforwardCongr (Spec.map_id R)).inv.app M.obj := by
  rfl

/-- Affine quasicoherent pushforward respects composition of ring maps. -/
def pushforwardSpecMapComp {T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    pushforwardSpecMap g ⋙ pushforwardSpecMap f ≅ pushforwardSpecMap (f ≫ g) :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    ((Scheme.Modules.pushforwardComp (Spec.map g) (Spec.map f)).app M.obj ≪≫
      (Scheme.Modules.pushforwardCongr (Spec.map_comp f g).symm).app M.obj)) (by
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
      (Scheme.Modules.pushforwardComp (Spec.map g) (Spec.map f)).hom.app M.obj ≫
        (Scheme.Modules.pushforwardCongr (Spec.map_comp f g).symm).hom.app M.obj := by
  rfl

/-- The inverse composition comparison is Mathlib's inverse on underlying modules. -/
@[simp]
theorem pushforwardSpecMapComp_inv_app_hom {T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (M : QuasicoherentSheaf (Spec T)) :
    ((pushforwardSpecMapComp f g).inv.app M).hom =
      (Scheme.Modules.pushforwardCongr (Spec.map_comp f g).symm).inv.app M.obj ≫
        (Scheme.Modules.pushforwardComp (Spec.map g) (Spec.map f)).inv.app M.obj := by
  rfl

/-- Pullback of quasicoherent sheaves along the morphism of spectra induced by a ring
homomorphism is left adjoint to pushforward. It is the restriction of Mathlib's
`Scheme.Modules.pullbackPushforwardAdjunction` to quasicoherent sheaves. -/
def pullbackPushforwardSpecMapAdjunction (f : R ⟶ S) :
    pullback (Spec.map f) ⊣ pushforwardSpecMap f :=
  (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).restrictFullyFaithful
    (_root_.SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).fullyFaithfulι
    (_root_.SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).fullyFaithfulι
    (pullbackCompιIso (Spec.map f)).symm (Iso.refl _)

/-- The unit of the affine quasicoherent pullback--pushforward adjunction is the unit of the
adjunction for modules. -/
@[simp]
theorem pullbackPushforwardSpecMapAdjunction_unit_app_hom (f : R ⟶ S)
    (M : QuasicoherentSheaf (Spec R)) :
    ((pullbackPushforwardSpecMapAdjunction f).unit.app M).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).unit.app M.obj ≫
        (Scheme.Modules.pushforward (Spec.map f)).map
          (eqToHom (pullback_obj_obj (Spec.map f) M).symm) := by
  have h :=
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).map_restrictFullyFaithful_unit_app
    (_root_.SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).fullyFaithfulι
    (_root_.SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).fullyFaithfulι
    (L := pullback (Spec.map f)) (R := pushforwardSpecMap f)
    (pullbackCompιIso (Spec.map f)).symm (Iso.refl _) M
  refine h.trans ?_
  rw [Iso.symm_hom, pullbackCompιIso_inv_app]
  -- The identity is formed in `SheafOfModules` rather than in `Scheme.Modules`, so `simp` does
  -- not remove it.
  exact congrArg (_ ≫ ·) (Category.comp_id _)

/-- The counit of the affine quasicoherent pullback--pushforward adjunction is the counit of
the adjunction for modules. -/
@[simp]
theorem pullbackPushforwardSpecMapAdjunction_counit_app_hom (f : R ⟶ S)
    (M : QuasicoherentSheaf (Spec S)) :
    ((pullbackPushforwardSpecMapAdjunction f).counit.app M).hom =
      eqToHom (pullback_obj_obj (Spec.map f) ((pushforwardSpecMap f).obj M)) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).counit.app M.obj := by
  have h :=
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).map_restrictFullyFaithful_counit_app
    (_root_.SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).fullyFaithfulι
    (_root_.SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).fullyFaithfulι
    (L := pullback (Spec.map f)) (R := pushforwardSpecMap f)
    (pullbackCompιIso (Spec.map f)).symm (Iso.refl _) M
  refine h.trans ?_
  rw [Iso.symm_inv, pullbackCompιIso_hom_app]
  -- As above, the identity is formed in `SheafOfModules`, so `simp` does not remove it.
  exact congrArg (_ ≫ ·) ((congrArg (· ≫ _)
    ((Scheme.Modules.pullback (Spec.map f)).map_id _)).trans (Category.id_comp _))

end AlgebraicGeometry.QuasicoherentSheaf

end

end TauCeti
