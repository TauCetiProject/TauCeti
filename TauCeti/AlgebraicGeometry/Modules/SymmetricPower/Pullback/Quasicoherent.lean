/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.SymmetricPower.Pullback.Affine
public import TauCeti.AlgebraicGeometry.Modules.SymmetricPower.Pullback.Coherence
public import TauCeti.AlgebraicGeometry.Modules.SymmetricPower.Restriction

/-!
# Symmetric powers commute with pullback of quasicoherent sheaves

For every morphism of schemes `f : X ⟶ Y` and every quasicoherent `𝒪_Y`-module `M`, the canonical
comparison `f^* (Symⁿ M) ⟶ Symⁿ (f^* M)` (`Scheme.Modules.pullbackSymmetricPowerComparison`) is
an isomorphism. There are no flatness, finiteness or characteristic hypotheses.

Along an open immersion the comparison is invertible for every sheaf of modules
(`TauCeti.AlgebraicGeometry.isIso_pullbackSymmetricPowerComparison_app_of_isOpenImmersion`, in
`TauCeti.AlgebraicGeometry.Modules.SymmetricPower.Restriction`).

For a general morphism, invertibility is checked on an open cover of `X`. The composition
coherence `TauCeti.AlgebraicGeometry.pullbackSymmetricPowerComparison_comp` reduces it first to
morphisms with affine target, by restricting to preimages of affine opens of `Y`, and then to
morphisms between affine schemes, by restricting to affine opens of the source. Between affine
schemes the comparison is the scalar-extension isomorphism on spectra
(`TauCeti.AlgebraicGeometry.isIso_pullbackSymmetricPowerComparison_of_spec`). The reduction
follows the one for tensor products in `Scheme.Modules.isIso_pullback_δ_of_isQuasicoherent`.

## Main declaration

* `TauCeti.AlgebraicGeometry.isIso_pullbackSymmetricPowerComparison_app`: the comparison along
  an arbitrary morphism is invertible on every quasicoherent sheaf.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise II.5.16.
-/

public section

open CategoryTheory

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

section Local

variable {X Y Z : Scheme.{u}}

/-- If the comparisons along `g` at `M` and along `f` at `g^* M` are invertible, so is the
comparison along `f ≫ g` at `M`. -/
private lemma isIso_comp_app (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) (M : Z.Modules)
    [IsIso ((Scheme.Modules.pullbackSymmetricPowerComparison g n).app M)]
    [IsIso ((Scheme.Modules.pullbackSymmetricPowerComparison f n).app
      ((Scheme.Modules.pullback g).obj M))] :
    IsIso ((Scheme.Modules.pullbackSymmetricPowerComparison (f ≫ g) n).app M) := by
  let W : X.Modules ⥤ X.Modules := _root_.SheafOfModules.symmetricPower X.sheaf n
  let e : (Scheme.Modules.pullback (f ≫ g)).obj M ≅
      (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) :=
    ((Scheme.Modules.pullbackComp f g).app M).symm
  let a := (Scheme.Modules.pullbackComp f g).symm.app
      ((_root_.SheafOfModules.symmetricPower Z.sheaf n).obj M) ≪≫
    (Scheme.Modules.pullback f).mapIso
      (asIso ((Scheme.Modules.pullbackSymmetricPowerComparison g n).app M)) ≪≫
    asIso ((Scheme.Modules.pullbackSymmetricPowerComparison f n).app
      ((Scheme.Modules.pullback g).obj M))
  have h : (Scheme.Modules.pullbackSymmetricPowerComparison (f ≫ g) n).app M ≫ W.map e.hom =
      a.hom := pullbackSymmetricPowerComparison_comp f g n M
  rw [(Iso.eq_comp_inv (W.mapIso e)).mpr h]
  exact Iso.isIso_hom (a ≪≫ (W.mapIso e).symm)

/-- If the comparisons along `f ≫ g` at `M` and along `f` at `g^* M` are invertible, then the
pullback along `f` of the comparison along `g` at `M` is invertible. -/
private lemma isIso_pullback_map_app (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) (M : Z.Modules)
    [IsIso ((Scheme.Modules.pullbackSymmetricPowerComparison (f ≫ g) n).app M)]
    [IsIso ((Scheme.Modules.pullbackSymmetricPowerComparison f n).app
      ((Scheme.Modules.pullback g).obj M))] :
    IsIso ((Scheme.Modules.pullback f).map
      ((Scheme.Modules.pullbackSymmetricPowerComparison g n).app M)) := by
  let W : X.Modules ⥤ X.Modules := _root_.SheafOfModules.symmetricPower X.sheaf n
  let e : (Scheme.Modules.pullback (f ≫ g)).obj M ≅
      (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) :=
    ((Scheme.Modules.pullbackComp f g).app M).symm
  let p := (Scheme.Modules.pullbackComp f g).app
    ((_root_.SheafOfModules.symmetricPower Z.sheaf n).obj M)
  let c := asIso ((Scheme.Modules.pullbackSymmetricPowerComparison f n).app
    ((Scheme.Modules.pullback g).obj M))
  have h : p.inv ≫ (Scheme.Modules.pullback f).map
      ((Scheme.Modules.pullbackSymmetricPowerComparison g n).app M) ≫ c.hom =
      (Scheme.Modules.pullbackSymmetricPowerComparison (f ≫ g) n).app M ≫ W.map e.hom :=
    (pullbackSymmetricPowerComparison_comp f g n M).symm
  rw [(Iso.eq_comp_inv c).mpr ((Iso.inv_comp_eq p).mp h)]
  exact Iso.isIso_hom ((p ≪≫
    asIso ((Scheme.Modules.pullbackSymmetricPowerComparison (f ≫ g) n).app M) ≪≫
    W.mapIso e) ≪≫ c.symm)

/-- The comparison is invertible on quasicoherent sheaves for a morphism of affine schemes. -/
private lemma isIso_app_of_isAffine (f : X ⟶ Y) [IsAffine X] [IsAffine Y] (n : ℕ)
    (M : Y.Modules)
    [M.IsQuasicoherent] :
    IsIso ((Scheme.Modules.pullbackSymmetricPowerComparison f n).app M) := by
  -- Transport the affine computation on spectra along `X ≅ Spec Γ(X)` and `Y ≅ Spec Γ(Y)`.
  have h : IsIso ((Scheme.Modules.pullbackSymmetricPowerComparison
      (X.isoSpec.hom ≫ Spec.map f.appTop) n).app ((Scheme.Modules.pullback Y.isoSpec.inv).obj M)) :=
    isIso_comp_app _ _ n _
  rw [Scheme.isoSpec_hom_naturality] at h
  have h' : IsIso ((Scheme.Modules.pullbackSymmetricPowerComparison
      ((f ≫ Y.isoSpec.hom) ≫ Y.isoSpec.inv) n).app M) :=
    isIso_comp_app _ _ n _
  rwa [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h'

/-- The comparison is invertible on quasicoherent sheaves for a morphism to an affine scheme. -/
private lemma isIso_app_of_isAffine_target (f : X ⟶ Y) [IsAffine Y] (n : ℕ) (M : Y.Modules)
    [M.IsQuasicoherent] :
    IsIso ((Scheme.Modules.pullbackSymmetricPowerComparison f n).app M) := by
  -- Check after restriction to the affine opens `W` of `X`, where `W.ι ≫ f` is a morphism of
  -- affine schemes.
  refine (Scheme.Modules.isIso_iff_of_isOpenCover (iSup_affineOpens_eq_top X) _).mpr fun W ↦ ?_
  have : IsAffine W.1 := W.2
  have := isIso_app_of_isAffine (W.1.ι ≫ f) n M
  exact isIso_pullback_map_app W.1.ι f n M

/-- **Symmetric powers commute with pullback of quasicoherent sheaves**: for every morphism of
schemes `f : X ⟶ Y` and every quasicoherent `𝒪_Y`-module `M`, the canonical comparison
`f^* (Symⁿ M) ⟶ Symⁿ (f^* M)` is an isomorphism. -/
instance isIso_pullbackSymmetricPowerComparison_app (f : X ⟶ Y) (n : ℕ) (M : Y.Modules)
    [M.IsQuasicoherent] :
    IsIso ((Scheme.Modules.pullbackSymmetricPowerComparison f n).app M) := by
  -- Check after restriction to the preimages `f⁻¹ V` of the affine opens `V` of `Y`, using
  -- `(f⁻¹ V).ι ≫ f = f ∣_ V ≫ V.ι` and the affine-target case for `f ∣_ V`.
  refine (Scheme.Modules.isIso_iff_of_isOpenCover
    (TopologicalSpace.IsOpenCover.comap (iSup_affineOpens_eq_top Y) f.base.hom) _).mpr
      fun V ↦ ?_
  have : IsAffine V.1 := V.2
  have := isIso_app_of_isAffine_target (f ∣_ V.1) n ((Scheme.Modules.pullback V.1.ι).obj M)
  have h : IsIso ((Scheme.Modules.pullbackSymmetricPowerComparison (f ∣_ V.1 ≫ V.1.ι) n).app M) :=
    isIso_comp_app _ _ n _
  rw [morphismRestrict_ι] at h
  exact isIso_pullback_map_app (f ⁻¹ᵁ V.1).ι f n M

end Local

end

end TauCeti.AlgebraicGeometry
