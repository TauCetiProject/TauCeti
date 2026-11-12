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

Invertibility along open immersions is itself formal. Along an open immersion `j`, a comparison
whose transpose under the pullback--pushforward adjunction factors through a pushforward
comparison `q`, as does the unit of the restriction--pushforward adjunction together with a
restriction isomorphism `r`, is the inverse of `r` read through
`Scheme.Modules.restrictFunctorIsoPullback`.

## Main declarations

* `TauCeti.AlgebraicGeometry.pullbackComparison_app_of_isOpenImmersion`: along an open
  immersion, such a comparison is the inverse of the restriction isomorphism;
  `TauCeti.AlgebraicGeometry.isIso_pullbackComparison_app_of_isOpenImmersion` deduces that it is
  invertible.
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

section OpenImmersion

variable {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
  (W₁ : Y.Modules ⥤ Y.Modules) (W₂ : U.Modules ⥤ U.Modules)
  (c : W₁ ⋙ pullback j ⟶ pullback j ⋙ W₂) (q : pushforward j ⋙ W₁ ⟶ W₂ ⋙ pushforward j)
  (r : restrictFunctor j ⋙ W₂ ≅ W₁ ⋙ restrictFunctor j) (M : Y.Modules)

/-- Along an open immersion `j`, let `c : W₁ ⋙ j^* ⟶ j^* ⋙ W₂` be a comparison whose transpose
under the pullback--pushforward adjunction is `W₁` of the unit followed by a pushforward
comparison `q`, and suppose that the unit of the restriction--pushforward adjunction factors
through `q` and a restriction isomorphism `r : W₂ (M|_U) ≅ (W₁ M)|_U`. Then `c` is the inverse
of `r`, read through the identification `Scheme.Modules.restrictFunctorIsoPullback` of
restriction with pullback. -/
theorem pullbackComparison_app_of_isOpenImmersion
    (h₁ : (pullbackPushforwardAdjunction j).unit.app (W₁.obj M) ≫ (pushforward j).map (c.app M) =
      W₁.map ((pullbackPushforwardAdjunction j).unit.app M) ≫ q.app _)
    (h₂ : (restrictAdjunction j).unit.app (W₁.obj M) =
      W₁.map ((restrictAdjunction j).unit.app M) ≫ q.app _ ≫ (pushforward j).map (r.hom.app M)) :
    c.app M = (restrictFunctorIsoPullback j).inv.app (W₁.obj M) ≫ r.inv.app M ≫
      W₂.map ((restrictFunctorIsoPullback j).hom.app M) := by
  -- Compare transposes under the pullback--pushforward adjunction `A`. The transpose of `c` is
  -- `W₁` of the unit followed by `q`. On the right, the units of `A` and of the restriction
  -- adjunction `B` differ by the identification `e` of restriction with pullback, and the unit of
  -- `B` factors through `q` and `r`.
  let A := pullbackPushforwardAdjunction j
  let B := restrictAdjunction j
  let P : U.Modules ⥤ Y.Modules := pushforward j
  let e : restrictFunctor j ≅ pullback j := restrictFunctorIsoPullback j
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

/-- Under the hypotheses of `pullbackComparison_app_of_isOpenImmersion`, the comparison along
the open immersion `j` is invertible. -/
theorem isIso_pullbackComparison_app_of_isOpenImmersion
    (h₁ : (pullbackPushforwardAdjunction j).unit.app (W₁.obj M) ≫ (pushforward j).map (c.app M) =
      W₁.map ((pullbackPushforwardAdjunction j).unit.app M) ≫ q.app _)
    (h₂ : (restrictAdjunction j).unit.app (W₁.obj M) =
      W₁.map ((restrictAdjunction j).unit.app M) ≫ q.app _ ≫ (pushforward j).map (r.hom.app M)) :
    IsIso (c.app M) := by
  rw [pullbackComparison_app_of_isOpenImmersion j W₁ W₂ c q r M h₁ h₂]
  exact Iso.isIso_hom ((restrictFunctorIsoPullback j).symm.app _ ≪≫ r.symm.app M ≪≫
    W₂.mapIso ((restrictFunctorIsoPullback j).app M))

end OpenImmersion

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
