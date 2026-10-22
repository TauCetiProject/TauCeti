/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

/-!
# Pullback comparisons are invertible if they are invertible on affine charts

Let `W X : X.Modules ⥤ X.Modules` be an endofunctor of module sheaves for every scheme `X`, such
as a symmetric or exterior power, and let `c f : W Y ⋙ f^* ⟶ f^* ⋙ W X` be comparison maps for
every morphism of schemes `f : X ⟶ Y`. Suppose that the comparisons are compatible with the
composition isomorphisms `Scheme.Modules.pullbackComp`, that they are invertible on
quasicoherent modules along open immersions, and that they are invertible on quasicoherent
modules along morphisms `Spec S ⟶ Spec R` of affine spectra. Then `c f` is invertible on every
quasicoherent module, for every morphism `f`.

The proof reduces first to morphisms with affine target, by restricting to the preimages of the
affine opens of `Y`, then to morphisms between affine schemes, by restricting to the affine opens
of `X`, and finally to morphisms of spectra, along `Scheme.isoSpec`. Each step uses the
composition compatibility and `Scheme.Modules.isIso_iff_of_isOpenCover`. It is the reduction
used for tensor products in `Scheme.Modules.isIso_pullback_δ_of_isQuasicoherent`, stated for an
arbitrary family of comparison maps.

## Main declaration

* `TauCeti.AlgebraicGeometry.isIso_pullbackComparison_app_of_isQuasicoherent`: comparison
  maps compatible with composition, invertible along open immersions and along morphisms of
  affine spectra, are invertible on quasicoherent modules along every morphism.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2 and Exercise II.5.16.
-/

public section

open CategoryTheory

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry Scheme.Modules

universe u

variable (W : ∀ X : Scheme.{u}, X.Modules ⥤ X.Modules)
  (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), W Y ⋙ pullback f ⟶ pullback f ⋙ W X)
  (hcomp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules),
    (c (f ≫ g)).app M ≫ (W X).map ((pullbackComp f g).inv.app M) =
      (pullbackComp f g).inv.app ((W Z).obj M) ≫ (pullback f).map ((c g).app M) ≫
        (c f).app ((pullback g).obj M))

include hcomp

/-- If the comparisons along `g` at `M` and along `f` at `g^* M` are invertible, so is the
comparison along `f ≫ g` at `M`. -/
private lemma isIso_app_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    [IsIso ((c g).app M)] [IsIso ((c f).app ((pullback g).obj M))] :
    IsIso ((c (f ≫ g)).app M) := by
  let e : (pullback (f ≫ g)).obj M ≅ (pullback f).obj ((pullback g).obj M) :=
    ((pullbackComp f g).app M).symm
  let a := (pullbackComp f g).symm.app ((W Z).obj M) ≪≫
    (pullback f).mapIso (asIso ((c g).app M)) ≪≫ asIso ((c f).app ((pullback g).obj M))
  have h : (c (f ≫ g)).app M ≫ (W X).map e.hom = a.hom := hcomp f g M
  rw [(Iso.eq_comp_inv ((W X).mapIso e)).mpr h]
  exact Iso.isIso_hom (a ≪≫ ((W X).mapIso e).symm)

/-- If the comparisons along `f ≫ g` at `M` and along `f` at `g^* M` are invertible, then the
pullback along `f` of the comparison along `g` at `M` is invertible. -/
private lemma isIso_pullback_map_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) [IsIso ((c (f ≫ g)).app M)] [IsIso ((c f).app ((pullback g).obj M))] :
    IsIso ((pullback f).map ((c g).app M)) := by
  let e : (pullback (f ≫ g)).obj M ≅ (pullback f).obj ((pullback g).obj M) :=
    ((pullbackComp f g).app M).symm
  let p := (pullbackComp f g).app ((W Z).obj M)
  let b := asIso ((c f).app ((pullback g).obj M))
  have h : p.inv ≫ (pullback f).map ((c g).app M) ≫ b.hom =
      (c (f ≫ g)).app M ≫ (W X).map e.hom :=
    (hcomp f g M).symm
  rw [(Iso.eq_comp_inv b).mpr ((Iso.inv_comp_eq p).mp h)]
  exact Iso.isIso_hom ((p ≪≫ asIso ((c (f ≫ g)).app M) ≪≫ (W X).mapIso e) ≪≫ b.symm)

variable (hopen : ∀ {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] (M : Y.Modules)
    [M.IsQuasicoherent], IsIso ((c j).app M))
  (hspec : ∀ {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : (Spec R).Modules) [M.IsQuasicoherent],
    IsIso ((c (Spec.map φ)).app M))

include hopen hspec

/-- The comparison is invertible on quasicoherent modules along a morphism of affine schemes. -/
private lemma isIso_app_of_isAffine {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X] [IsAffine Y]
    (M : Y.Modules) [M.IsQuasicoherent] : IsIso ((c f).app M) := by
  -- Transport the computation on spectra along `X ≅ Spec Γ(X)` and `Y ≅ Spec Γ(Y)`.
  have := hopen Y.isoSpec.inv M
  have := hspec f.appTop ((pullback Y.isoSpec.inv).obj M)
  have := hopen X.isoSpec.hom ((pullback (Spec.map f.appTop)).obj
    ((pullback Y.isoSpec.inv).obj M))
  have h₁ := isIso_app_comp W c hcomp X.isoSpec.hom (Spec.map f.appTop)
    ((pullback Y.isoSpec.inv).obj M)
  rw [Scheme.isoSpec_hom_naturality] at h₁
  have h₂ := isIso_app_comp W c hcomp (f ≫ Y.isoSpec.hom) Y.isoSpec.inv M
  rwa [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h₂

/-- The comparison is invertible on quasicoherent modules along a morphism to an affine
scheme. -/
private lemma isIso_app_of_isAffine_target {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y]
    (M : Y.Modules) [M.IsQuasicoherent] : IsIso ((c f).app M) := by
  -- Check after restriction to the affine opens `V` of `X`, where `V.ι ≫ f` is a morphism of
  -- affine schemes.
  refine (isIso_iff_of_isOpenCover (iSup_affineOpens_eq_top X) _).mpr fun V ↦ ?_
  have : IsAffine V.1 := V.2
  have := isIso_app_of_isAffine W c hcomp hopen hspec (V.1.ι ≫ f) M
  have := hopen V.1.ι ((pullback f).obj M)
  exact isIso_pullback_map_app W c hcomp V.1.ι f M

/-- **Pullback comparisons are invertible if they are invertible on affine charts.** Comparison
maps `W Y ⋙ f^* ⟶ f^* ⋙ W X` that are compatible with the composition isomorphisms of pullback,
and are invertible on quasicoherent modules along open immersions and along morphisms of affine
spectra, are invertible on every quasicoherent module along every morphism of schemes. -/
theorem isIso_pullbackComparison_app_of_isQuasicoherent {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) [M.IsQuasicoherent] : IsIso ((c f).app M) := by
  -- Check after restriction to the preimages `f⁻¹ V` of the affine opens `V` of `Y`, using
  -- `(f⁻¹ V).ι ≫ f = f ∣_ V ≫ V.ι` and the affine-target case for `f ∣_ V`.
  refine (isIso_iff_of_isOpenCover
    (TopologicalSpace.IsOpenCover.comap (iSup_affineOpens_eq_top Y) f.base.hom) _).mpr
      fun V ↦ ?_
  have : IsAffine V.1 := V.2
  have := hopen V.1.ι M
  have := isIso_app_of_isAffine_target W c hcomp hopen hspec (f ∣_ V.1) ((pullback V.1.ι).obj M)
  have h := isIso_app_comp W c hcomp (f ∣_ V.1) V.1.ι M
  rw [morphismRestrict_ι] at h
  have := hopen (f ⁻¹ᵁ V.1).ι ((pullback f).obj M)
  exact isIso_pullback_map_app W c hcomp (f ⁻¹ᵁ V.1).ι f M

end TauCeti.AlgebraicGeometry
