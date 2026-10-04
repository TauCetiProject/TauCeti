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
a morphism of spectra. This calculation is the affine-local input for constructing the
quasicoherent coordinate algebra `p_* 𝒪_V` of an affine morphism `p : V ⟶ X`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward_specMap`: pushforward along a
  morphism of spectra preserves quasicoherence;
* `TauCeti.AlgebraicGeometry.QuasicoherentSheaf.pushforwardSpecMap`: the induced functor on
  quasicoherent sheaves;
* `TauCeti.AlgebraicGeometry.QuasicoherentSheaf.pushforwardSpecMapCompιIso`: forgetting the
  quasicoherence witness recovers ordinary module pushforward.

## References

* The Stacks Project, Tag 01XB.
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

/-- Forgetting quasicoherence after affine pushforward recovers ordinary module pushforward. -/
def pushforwardSpecMapCompιIso (f : R ⟶ S) :
    pushforwardSpecMap f ⋙
        (_root_.SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι ≅
      (_root_.SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).ι ⋙
        Scheme.Modules.pushforward (Spec.map f) :=
  (_root_.SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).liftCompιIso _ _

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

end AlgebraicGeometry.QuasicoherentSheaf

end

end TauCeti
