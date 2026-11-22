/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Sheaf
public import TauCeti.AlgebraicGeometry.Sites.Etale.Pullback
import TauCeti.AlgebraicGeometry.Descent.Fpqc
import TauCeti.AlgebraicGeometry.Sites.Etale.Localization
import TauCeti.CategoryTheory.Adjunction.Representable
import TauCeti.CategoryTheory.EffectiveEpi.Representable
import TauCeti.CategoryTheory.Limits.Shapes.Pullback.DescentDatum

/-!
# Effective étale descent for representability of étale sheaves of sets

This file establishes effective étale descent for representability of étale sheaves of sets by
finite étale schemes along a quasi-compact surjective étale morphism.

Given a quasi-compact surjective étale morphism `p : S' ⟶ S` and an étale sheaf of sets `F` on `S`,
if the pulled-back sheaf `(p.smallEtalePullback (Type u)).obj F` on `S'` is representable by a
finite étale `S'`-scheme `X` (meaning
`(toSheaf S').obj X ≅ (p.smallEtalePullback (Type u)).obj F`), then `F` is representable by a
finite étale `S`-scheme `X₀`, with no separately supplied descent datum
(`AlgebraicGeometry.Scheme.Hom.exists_toSheaf_iso_of_smallEtalePullback_iso`). This allows
representability of an étale sheaf of sets by a finite étale scheme to be checked locally after
such an étale cover.

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_toSheaf_iso_of_smallEtalePullback_iso`: representability of
  an étale sheaf of sets by a finite étale scheme satisfies effective descent along any
  quasi-compact surjective étale morphism.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IX, §2.
* The Stacks Project, [Tag 0245](https://stacks.math.columbia.edu/tag/0245).
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.FiniteEtaleScheme

/-- Effective descent for representability of étale sheaves by finite étale schemes along a
quasi-compact surjective étale morphism `p : S' ⟶ S`. -/
theorem exists_toSheaf_iso_of_smallEtalePullback_iso {S S' : Scheme.{u}} (p : S' ⟶ S)
    [AlgebraicGeometry.Etale p] [Surjective p] [QuasiCompact p] (X : TauCeti.FiniteEtaleScheme S')
    (F : Sheaf (smallEtaleTopology S) (Type u))
    (e : (toSheaf S').obj X ≅ (p.smallEtalePullback (Type u)).obj F) :
    ∃ X₀ : TauCeti.FiniteEtaleScheme S, Nonempty ((toSheaf S).obj X₀ ≅ F) := by
  let U₀ : S.Etale := Etale.mk (𝟙 S)
  let hU₀ : IsTerminal U₀ := Etale.mkIdTerminal S
  let U : S.Etale := Etale.mk p
  let p₀ : U ⟶ U₀ := MorphismProperty.Over.homMk p (Category.comp_id p)
  let F₀ : (CategoryTheory.Over U₀)ᵒᵖ ⥤ Type u := (F.over U₀).obj
  -- Representability of `F₀` after base change along `p₀ : U ⟶ U₀`.
  let e' : (smallEtaleTopology S').yoneda.obj ((toEtale S').obj X) ≅
      (p.smallEtaleMap.sheafPushforwardContinuous (Type u)
        (smallEtaleTopology S') (smallEtaleTopology S)).obj F :=
    e ≪≫ (p.smallEtalePullbackIsoMapPushforward (Type u)).app F
  let ePresheaf : U.iteratedSliceEquiv.functor.op ⋙ yoneda.obj ((toEtale S').obj X) ≅
      (CategoryTheory.Over.map p₀).op ⋙ F₀ :=
    Functor.isoWhiskerLeft U.iteratedSliceEquiv.functor.op
      ((sheafToPresheaf (smallEtaleTopology S') (Type u)).mapIso e') ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (NatIso.op U.iteratedSliceEquivFunctorCompMapIso.symm) F.obj ≪≫
      Functor.associator (CategoryTheory.Over.map p₀).op (CategoryTheory.Over.forget U₀).op F.obj
  let X_et : CategoryTheory.Over U := U.iteratedSliceEquiv.inverse.obj ((toEtale S').obj X)
  let e_rep : ((CategoryTheory.Over.map p₀).op ⋙ F₀).RepresentableBy X_et :=
    (U.iteratedSliceEquiv.toAdjunction.representableByComp
      (Functor.RepresentableBy.yoneda ((toEtale S').obj X))).ofIso ePresheaf
  -- Transport `e_rep.descentDatum` to `Scheme` and apply effective fpqc descent.
  let L : S.Etale ⥤ Scheme.{u} := Etale.forget S ⋙ CategoryTheory.Over.forget S
  have hp₀ : L.map p₀ = p := (rfl)
  have hX_hom : L.map X_et.hom = X.obj.hom := (rfl)
  have : Surjective (L.map p₀) := hp₀ ▸ ‹Surjective p›
  have hp_flat : Flat p := inferInstance
  have : Flat (L.map p₀) := hp₀ ▸ hp_flat
  have : QuasiCompact (L.map p₀) := hp₀ ▸ ‹QuasiCompact p›
  obtain ⟨hX_fin, hX_et⟩ := (TauCeti.finiteEtaleSchemeProperty_iff X.obj).mp X.property
  have hX_et_hom : (CategoryTheory.Over.mk (L.map X_et.hom)).hom = X.obj.hom := hX_hom
  have : IsFinite (CategoryTheory.Over.mk (L.map X_et.hom)).hom := hX_et_hom ▸ hX_fin
  have : AlgebraicGeometry.Etale (CategoryTheory.Over.mk (L.map X_et.hom)).hom :=
    hX_et_hom ▸ hX_et
  let D_scheme : TauCeti.DescentDatum (L.map p₀) (CategoryTheory.Over.mk (L.map X_et.hom)) :=
    e_rep.descentDatum.map L
  obtain ⟨X₀_over, hfin, het, f, hf⟩ :=
    D_scheme.exists_isFinite_etale_baseChange_hom_isIso_of_quasiCompact
  let X₀ : TauCeti.FiniteEtaleScheme S :=
    ⟨X₀_over, (TauCeti.finiteEtaleSchemeProperty_iff _).mpr ⟨hfin, het⟩⟩
  let X₀_et : CategoryTheory.Over U₀ :=
    CategoryTheory.Over.mk (hU₀.from ((toEtale S).obj X₀))
  have hX₀_hom : L.map X₀_et.hom = X₀_over.hom :=
    (Category.comp_id _).symm.trans (MorphismProperty.Over.w (hU₀.from ((toEtale S).obj X₀)))
  -- Lift the descended model isomorphism `f` back to `CategoryTheory.Over U`.
  let e_pb_lift :
      Limits.pullback (L.map X₀_et.hom) (L.map p₀) ≅ Limits.pullback X₀_over.hom (L.map p₀) :=
    Limits.pullback.congrHom hX₀_hom rfl
  let e_pb : L.obj (Limits.pullback X₀_et.hom p₀) ≅ Limits.pullback X₀_over.hom (L.map p₀) :=
    PreservesPullback.iso L X₀_et.hom p₀ ≪≫ e_pb_lift
  have he_pb_lift_fst :
      e_pb_lift.hom ≫ Limits.pullback.fst X₀_over.hom (L.map p₀) =
        Limits.pullback.fst (L.map X₀_et.hom) (L.map p₀) :=
    (congrArg (· ≫ Limits.pullback.fst X₀_over.hom (L.map p₀))
      (Limits.pullback.congrHom_hom hX₀_hom rfl)).trans
      ((Limits.pullback.lift_fst _ _ _).trans (Category.comp_id _))
  have he_pb_lift_snd :
      e_pb_lift.hom ≫ Limits.pullback.snd X₀_over.hom (L.map p₀) =
        Limits.pullback.snd (L.map X₀_et.hom) (L.map p₀) :=
    (congrArg (· ≫ Limits.pullback.snd X₀_over.hom (L.map p₀))
      (Limits.pullback.congrHom_hom hX₀_hom rfl)).trans
      ((Limits.pullback.lift_snd _ _ _).trans (Category.comp_id _))
  have he_pb_snd : e_pb.hom ≫ Limits.pullback.snd X₀_over.hom (L.map p₀) =
      L.map (Limits.pullback.snd X₀_et.hom p₀) :=
    (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) he_pb_lift_snd).trans (PreservesPullback.iso_hom_snd L X₀_et.hom p₀))
  let Φ : CategoryTheory.Over U ⥤ CategoryTheory.Over S' :=
    U.iteratedSliceEquiv.functor ⋙ Etale.forget S'
  let hΦ : Φ.FullyFaithful :=
    U.iteratedSliceEquiv.fullyFaithfulFunctor.comp (Etale.forgetFullyFaithful S')
  let g_scheme : Φ.obj ((CategoryTheory.Over.pullback p₀).obj X₀_et) ⟶ Φ.obj X_et :=
    CategoryTheory.Over.homMk (e_pb.hom ≫ f.hom.left) <|
      (Category.assoc _ _ _).trans
        ((congrArg (e_pb.hom ≫ ·) (CategoryTheory.Over.w f.hom)).trans he_pb_snd)
  have hg_scheme_left : g_scheme.left = e_pb.hom ≫ f.hom.left := (rfl)
  have hf_left : IsIso f.hom.left :=
    inferInstanceAs (IsIso ((CategoryTheory.Over.forget (L.obj U)).map f.hom))
  have : IsIso g_scheme := by
    suffices IsIso ((CategoryTheory.Over.forget S').map g_scheme) from
      isIso_of_reflects_iso g_scheme (CategoryTheory.Over.forget S')
    rw [CategoryTheory.Over.forget_map, hg_scheme_left]
    exact IsIso.comp_isIso (f := e_pb.hom) (h := f.hom.left)
  let g_et : (CategoryTheory.Over.pullback p₀).obj X₀_et ⟶ X_et := hΦ.preimage g_scheme
  have : IsIso g_et := by
    let := hΦ.reflectsIsomorphisms
    have : IsIso (Φ.map g_et) := (hΦ.map_preimage g_scheme).symm ▸ ‹IsIso g_scheme›
    exact isIso_of_reflects_iso g_et Φ
  have hg_et : L.map g_et.left = e_pb.hom ≫ f.hom.left :=
    (congrArg CategoryTheory.Over.Hom.left (hΦ.map_preimage g_scheme)).trans hg_scheme_left
  let iX₀ : CategoryTheory.Over.mk (L.map X₀_et.hom) ⟶ X₀_over :=
    CategoryTheory.Over.homMk (𝟙 X₀_over.left) ((Category.id_comp _).trans hX₀_hom.symm)
  let f_map : TauCeti.DescentDatum.Hom ((TauCeti.DescentDatum.baseChange p₀ X₀_et).map L)
      D_scheme :=
    f.comp ((TauCeti.DescentDatum.baseChangeHom (L.map p₀) iX₀).comp
      (TauCeti.DescentDatum.baseChangeMapHom L p₀ X₀_et))
  have hf_map : f_map.hom.left = L.map g_et.left := by
    have hiX₀ : (TauCeti.DescentDatum.baseChangeHom (L.map p₀) iX₀).hom.left = e_pb_lift.hom := by
      refine Limits.pullback.hom_ext ?_ ?_
      · have hw := (TauCeti.DescentDatum.isPullback_baseChangeHom (L.map p₀) iX₀).w
        have hi : iX₀.left = 𝟙 X₀_over.left := (rfl)
        exact hw.trans ((congrArg (_ ≫ ·) hi).trans
          ((Category.comp_id _).trans he_pb_lift_fst.symm))
      · exact (CategoryTheory.Over.w
          (TauCeti.DescentDatum.baseChangeHom (L.map p₀) iX₀).hom).trans he_pb_lift_snd.symm
    dsimp only [f_map]
    rw [TauCeti.DescentDatum.Hom.comp_hom, TauCeti.DescentDatum.Hom.comp_hom,
      CategoryTheory.Over.comp_left, CategoryTheory.Over.comp_left,
      TauCeti.DescentDatum.baseChangeMapHom_hom_left, hiX₀,
      ← Iso.trans_hom (PreservesPullback.iso L X₀_et.hom p₀) e_pb_lift]
    exact hg_et.symm
  let f_et : (TauCeti.DescentDatum.baseChange p₀ X₀_et).Hom e_rep.descentDatum :=
    TauCeti.DescentDatum.Hom.ofMap L g_et f_map hf_map
  have : IsIso f_et.hom := by
    rw [TauCeti.DescentDatum.Hom.ofMap_hom]
    infer_instance
  -- Descend the local representation along `p₀` to represent `F₀` by `X₀_et`.
  have hsurj (T : CategoryTheory.Over U₀) : Surjective (Limits.pullback.fst T.hom p₀).left := by
    have hfst : (Limits.pullback.fst T.hom p₀).left = L.map (Limits.pullback.fst T.hom p₀) := (rfl)
    have hpb : Surjective (Limits.pullback.fst (L.map T.hom) (L.map p₀)) := by
      rw [surjective_iff, ← Set.range_eq_univ, Scheme.Pullback.range_fst,
        range_eq_univ (L.map p₀), Set.preimage_univ]
    rw [hfst, ← PreservesPullback.iso_hom_fst L T.hom p₀]
    exact ⟨hpb.surj.comp (PreservesPullback.iso L T.hom p₀).hom.surjective⟩
  have hF (T : CategoryTheory.Over U₀) :
      Presieve.IsSheafFor F₀ (.singleton ((CategoryTheory.Over.mapPullbackAdj p₀).counit.app T)) :=
    have hcounit : ((CategoryTheory.Over.mapPullbackAdj p₀).counit.app T).left =
        Limits.pullback.fst T.hom p₀ :=
      (rfl)
    have : Surjective ((CategoryTheory.Over.mapPullbackAdj p₀).counit.app T).left.left :=
      hcounit ▸ hsurj T
    isSheafFor_singleton_over_of_surjective F U₀
      ((CategoryTheory.Over.mapPullbackAdj p₀).counit.app T)
  have (T : CategoryTheory.Over U₀) : EffectiveEpi (Limits.pullback.fst T.hom p₀) :=
    have := hsurj T
    Etale.effectiveEpi_of_surjective _
  let rep₀ : F₀.RepresentableBy X₀_et := e_rep.descend hF f_et
  let eqU₀ := (CategoryTheory.Over.equivalenceOfIsTerminal hU₀).symm
  let rep : F.obj.RepresentableBy ((toEtale S).obj X₀) :=
    (eqU₀.toAdjunction.representableByComp rep₀).ofIso
      ((Functor.associator eqU₀.functor.op (CategoryTheory.Over.forget U₀).op F.obj).symm ≪≫
        Functor.isoWhiskerRight
          (NatIso.op (CategoryTheory.Over.equivalenceOfIsTerminal hU₀).counitIso.symm) F.obj ≪≫
        Functor.leftUnitor F.obj)
  exact ⟨X₀, ⟨(fullyFaithfulSheafToPresheaf (smallEtaleTopology S) (Type u)).preimageIso
    rep.toIso⟩⟩

end AlgebraicGeometry.Scheme.Hom
