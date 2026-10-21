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

Along an open immersion `j` the comparison is invertible for every sheaf of modules: it is the
inverse of the restriction isomorphism `Scheme.Modules.restrictSymmetricPowerIso`, read through
the identification of restriction with pullback
(`TauCeti.AlgebraicGeometry.pullbackSymmetricPowerComparison_app_of_isOpenImmersion`). This rests
on the compatibility of the unit of the restriction--pushforward adjunction with the
symmetric-power comparisons (`Scheme.Modules.restrictAdjunction_unit_app_symmetricPower`).

For a general morphism, invertibility is checked on an open cover of `X`. The composition
coherence `TauCeti.AlgebraicGeometry.pullbackSymmetricPowerComparison_comp` reduces it first to
morphisms with affine target, by restricting to preimages of affine opens of `Y`, and then to
morphisms between affine schemes, by restricting to affine opens of the source. Between affine
schemes the comparison is the scalar-extension isomorphism on spectra
(`TauCeti.AlgebraicGeometry.isIso_pullbackSymmetricPowerComparison_of_spec`). The reduction
follows the one for tensor products in `Scheme.Modules.isIso_pullback_δ_of_isQuasicoherent`.

## Main declarations

* `TauCeti.AlgebraicGeometry.isIso_pullbackSymmetricPowerComparison_app_of_isOpenImmersion`:
  the comparison along an open immersion is invertible on every sheaf of modules;
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

section OpenImmersion

variable {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]

/-- Along an open immersion `j`, the canonical comparison `j^* (Symⁿ M) ⟶ Symⁿ (j^* M)` is the
inverse of the restriction isomorphism `Symⁿ (M|_U) ≅ (Symⁿ M)|_U`, read through the
identification `Scheme.Modules.restrictFunctorIsoPullback` of restriction with pullback. -/
theorem pullbackSymmetricPowerComparison_app_of_isOpenImmersion (n : ℕ) (M : Y.Modules) :
    (Scheme.Modules.pullbackSymmetricPowerComparison j n).app M =
      (Scheme.Modules.restrictFunctorIsoPullback j).inv.app
          ((_root_.SheafOfModules.symmetricPower Y.sheaf n).obj M) ≫
        (Scheme.Modules.restrictSymmetricPowerIso j n).inv.app M ≫
        (_root_.SheafOfModules.symmetricPower U.sheaf n).map
          ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app M) := by
  -- Compare transposes under the pullback--pushforward adjunction `A`. The transpose of the
  -- comparison is `Symⁿ` of the unit followed by the pushforward comparison `q`. On the right,
  -- the units of `A` and of the restriction adjunction `B` differ by the identification `e` of
  -- restriction with pullback, and the unit of `B` factors through `q` and the restriction
  -- isomorphism `r`.
  let A := Scheme.Modules.pullbackPushforwardAdjunction j
  let B := Scheme.Modules.restrictAdjunction j
  let P : U.Modules ⥤ Y.Modules := Scheme.Modules.pushforward j
  let W₁ : Y.Modules ⥤ Y.Modules := _root_.SheafOfModules.symmetricPower Y.sheaf n
  let W₂ : U.Modules ⥤ U.Modules := _root_.SheafOfModules.symmetricPower U.sheaf n
  let q : P ⋙ W₁ ⟶ W₂ ⋙ P :=
    SheafOfModules.pushforwardSymmetricPowerComparison j.toRingCatSheafHom n
  let e : Scheme.Modules.restrictFunctor j ≅ Scheme.Modules.pullback j :=
    Scheme.Modules.restrictFunctorIsoPullback j
  let r : Scheme.Modules.restrictFunctor j ⋙ W₂ ≅ W₁ ⋙ Scheme.Modules.restrictFunctor j :=
    Scheme.Modules.restrictSymmetricPowerIso j n
  have h₁ : A.unit.app (W₁.obj M) ≫
      P.map ((Scheme.Modules.pullbackSymmetricPowerComparison j n).app M) =
      W₁.map (A.unit.app M) ≫ q.app _ :=
    Scheme.Modules.unit_comp_pushforward_map_pullbackSymmetricPowerComparison_app j n M
  have h₂ : B.unit.app (W₁.obj M) = W₁.map (B.unit.app M) ≫ q.app _ ≫ P.map (r.hom.app M) :=
    Scheme.Modules.restrictAdjunction_unit_app_symmetricPower j n M
  have hA : A.unit.app (W₁.obj M) ≫ P.map (e.inv.app (W₁.obj M)) = B.unit.app (W₁.obj M) :=
    Adjunction.unit_leftAdjointUniq_hom_app A B (W₁.obj M)
  have hB : B.unit.app M ≫ P.map (e.hom.app M) = A.unit.app M :=
    Adjunction.unit_leftAdjointUniq_hom_app B A M
  have hq : W₁.map (P.map (e.hom.app M)) ≫ q.app _ = q.app _ ≫ P.map (W₂.map (e.hom.app M)) :=
    q.naturality (e.hom.app M)
  have hr : P.map (r.hom.app M) ≫ P.map (r.inv.app M) = 𝟙 _ :=
    (P.mapIso (r.app M)).hom_inv_id
  have key : W₁.map (A.unit.app M) ≫ q.app _ =
      A.unit.app (W₁.obj M) ≫ P.map (e.inv.app (W₁.obj M) ≫ r.inv.app M ≫ W₂.map (e.hom.app M)) :=
    calc W₁.map (A.unit.app M) ≫ q.app _
        = W₁.map (B.unit.app M) ≫ q.app _ ≫ P.map (W₂.map (e.hom.app M)) := by
          rw [← hB, Functor.map_comp, Category.assoc, hq]
      _ = B.unit.app (W₁.obj M) ≫ P.map (r.inv.app M) ≫ P.map (W₂.map (e.hom.app M)) := by
          rw [h₂, Category.assoc, Category.assoc, reassoc_of% hr]
      _ = _ := by rw [← hA, P.map_comp, P.map_comp, Category.assoc]
  exact (A.homEquiv _ _).injective ((A.homEquiv_unit _ _ _).trans
    (h₁.trans (key.trans (A.homEquiv_unit _ _ _).symm)))

/-- Along an open immersion the canonical symmetric-power comparison is invertible for every
sheaf of modules. -/
instance isIso_pullbackSymmetricPowerComparison_app_of_isOpenImmersion (n : ℕ) (M : Y.Modules) :
    IsIso ((Scheme.Modules.pullbackSymmetricPowerComparison j n).app M) := by
  rw [pullbackSymmetricPowerComparison_app_of_isOpenImmersion]
  exact Iso.isIso_hom ((Scheme.Modules.restrictFunctorIsoPullback j).symm.app _ ≪≫
    (Scheme.Modules.restrictSymmetricPowerIso j n).symm.app M ≪≫
    (_root_.SheafOfModules.symmetricPower U.sheaf n).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback j).app M))

end OpenImmersion

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
