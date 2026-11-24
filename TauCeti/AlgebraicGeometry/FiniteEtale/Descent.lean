/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Sheaf.Basic
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

/-- Transport an isomorphism `(toSheaf S').obj X ≅ (p.smallEtalePullback (Type u)).obj F` across
`iteratedSliceEquiv` to represent `(Over.map p₀).op ⋙ (F.over U₀).obj`. -/
private noncomputable def representableByOverPullback {S S' : Scheme.{u}} (p : S' ⟶ S)
    [AlgebraicGeometry.Etale p] (X : TauCeti.FiniteEtaleScheme S')
    (F : Sheaf (smallEtaleTopology S) (Type u))
    (e : (toSheaf S').obj X ≅ (p.smallEtalePullback (Type u)).obj F)
    {U₀ : S.Etale} (p₀ : Etale.mk p ⟶ U₀) :
    ((CategoryTheory.Over.map p₀).op ⋙ (F.over U₀).obj).RepresentableBy
      ((Etale.mk p).iteratedSliceEquiv.inverse.obj ((toEtale S').obj X)) :=
  let U : S.Etale := Etale.mk p
  let ePresheaf : U.iteratedSliceEquiv.functor.op ⋙ yoneda.obj ((toEtale S').obj X) ≅
      (CategoryTheory.Over.map p₀).op ⋙ (F.over U₀).obj :=
    Functor.isoWhiskerLeft U.iteratedSliceEquiv.functor.op
      ((sheafToPresheaf (smallEtaleTopology S') (Type u)).mapIso
        (e ≪≫ U.smallEtalePullbackObjIsoOver (Type u) F)) ≪≫
      (sheafToPresheaf ((smallEtaleTopology S).over U) (Type u)).mapIso
        ((U.overSheafEquiv (Type u)).symm.counitIso.app (F.over U)) ≪≫
      eqToIso (congrArg (fun G : CategoryTheory.Over U ⥤ S.Etale ↦ G.op ⋙ F.obj)
        (CategoryTheory.Over.mapForget_eq p₀).symm) ≪≫
      Functor.associator (CategoryTheory.Over.map p₀).op (CategoryTheory.Over.forget U₀).op F.obj
  (U.iteratedSliceEquiv.toAdjunction.representableByComp
    (Functor.RepresentableBy.yoneda ((toEtale S').obj X))).ofIso ePresheaf

private abbrev toScheme (S : Scheme.{u}) : S.Etale ⥤ Scheme.{u} :=
  Etale.forget S ⋙ CategoryTheory.Over.forget S

private lemma toScheme_map_homMk {S S' : Scheme.{u}} (p : S' ⟶ S) [AlgebraicGeometry.Etale p] :
    (toScheme S).map
      (MorphismProperty.Over.homMk p (Category.comp_id p) : Etale.mk p ⟶ Etale.mk (𝟙 S)) =
      p :=
  -- `MorphismProperty.Over.homMk` uses `p` itself as the underlying `.left` morphism.
  MorphismProperty.Over.forget_comp_forget_map @Etale ⊤ S _

private lemma toScheme_map_toEtale_inverse_hom {S S' : Scheme.{u}} (p : S' ⟶ S)
    [AlgebraicGeometry.Etale p] (X : TauCeti.FiniteEtaleScheme S') :
    (toScheme S).map
        ((Etale.mk p).iteratedSliceEquiv.inverse.obj ((toEtale S').obj X)).hom =
      X.obj.hom :=
  (MorphismProperty.Over.forget_comp_forget_map _ ⊤ S _).trans
    ((Etale.iteratedSliceEquiv_inverse_obj_hom_left _ _).trans (by
      -- Unfolds `toEtale` and `Etale.mk` to match `X.obj.hom` across `toScheme.obj`.
      rfl))

/-- Lift a descent-datum isomorphism in `Scheme` between the transported base-change datum of
`X₀_over` and `D.map (toScheme S)` back to an isomorphism of descent data in `S.Etale`. -/
private noncomputable def liftDescentDatumHom {S S' : Scheme.{u}} (p : S' ⟶ S)
    [AlgebraicGeometry.Etale p] (p₀ : Etale.mk p ⟶ Etale.mk (𝟙 S))
    {X_et : CategoryTheory.Over (Etale.mk p)} (D : TauCeti.DescentDatum p₀ X_et)
    (X₀_over : CategoryTheory.Over ((toScheme S).obj (Etale.mk (𝟙 S))))
    (hX₀ : TauCeti.finiteEtaleSchemeProperty S X₀_over)
    (f : TauCeti.DescentDatum.Hom
      (TauCeti.DescentDatum.baseChange ((toScheme S).map p₀) X₀_over)
      (D.map (toScheme S)))
    [IsIso f.hom] :
    { f_et : (TauCeti.DescentDatum.baseChange p₀
      (CategoryTheory.Over.mk ((Etale.mkIdTerminal S).from
        ((toEtale S).obj ⟨X₀_over, hX₀⟩)))).Hom D //
        IsIso f_et.hom } := by
  let U : S.Etale := Etale.mk p
  let X₀ : TauCeti.FiniteEtaleScheme S := ⟨X₀_over, hX₀⟩
  let X₀_et : CategoryTheory.Over (Etale.mk (𝟙 S)) :=
    CategoryTheory.Over.mk ((Etale.mkIdTerminal S).from ((toEtale S).obj X₀))
  have hX₀_hom : (toScheme S).map X₀_et.hom = X₀_over.hom :=
    (Category.comp_id _).symm.trans (MorphismProperty.Over.w
      ((Etale.mkIdTerminal S).from ((toEtale S).obj X₀)))
  -- Identify `baseChange ((toScheme S).map p₀) X₀_over` with
  -- `(baseChange p₀ X₀_et).map (toScheme S)`.
  let iX₀ : CategoryTheory.Over.mk ((toScheme S).map X₀_et.hom) ⟶ X₀_over :=
    CategoryTheory.Over.homMk (𝟙 X₀_over.left) ((Category.id_comp _).trans hX₀_hom.symm)
  have hiX₀ : (CategoryTheory.Over.forget ((toScheme S).obj (Etale.mk (𝟙 S)))).map iX₀ =
      𝟙 X₀_over.left :=
    (CategoryTheory.Over.forget_map (f := iX₀)).trans (CategoryTheory.Over.homMk_left _ _)
  have : IsIso iX₀ := by
    suffices IsIso ((CategoryTheory.Over.forget ((toScheme S).obj (Etale.mk (𝟙 S)))).map iX₀) from
      isIso_of_reflects_iso iX₀ (CategoryTheory.Over.forget ((toScheme S).obj (Etale.mk (𝟙 S))))
    rw [hiX₀]
    exact IsIso.id _
  have : IsIso (TauCeti.DescentDatum.baseChangeHom ((toScheme S).map p₀) iX₀).hom := by
    rw [TauCeti.DescentDatum.baseChangeHom_hom]
    infer_instance
  let f_map : TauCeti.DescentDatum.Hom ((TauCeti.DescentDatum.baseChange p₀ X₀_et).map (toScheme S))
      (D.map (toScheme S)) :=
    f.comp ((TauCeti.DescentDatum.baseChangeHom ((toScheme S).map p₀) iX₀).comp
      (TauCeti.DescentDatum.baseChangeMapHom (toScheme S) p₀ X₀_et))
  have : IsIso f_map.hom := by
    dsimp only [f_map]
    rw [TauCeti.DescentDatum.Hom.comp_hom, TauCeti.DescentDatum.Hom.comp_hom]
    infer_instance
  have : IsIso f_map.hom.left := by
    rw [← CategoryTheory.Over.forget_map]
    infer_instance
  -- Preimage `f_map.hom.left` across the fully faithful functor `Φ : Over U ⥤ Over S'`.
  let Φ : CategoryTheory.Over U ⥤ CategoryTheory.Over S' :=
    U.iteratedSliceEquiv.functor ⋙ Etale.forget S'
  let hΦ : Φ.FullyFaithful :=
    U.iteratedSliceEquiv.fullyFaithfulFunctor.comp (Etale.forgetFullyFaithful S')
  let g_scheme : Φ.obj ((CategoryTheory.Over.pullback p₀).obj X₀_et) ⟶ Φ.obj X_et :=
    CategoryTheory.Over.homMk f_map.hom.left (CategoryTheory.Over.w f_map.hom)
  have : IsIso g_scheme := by
    suffices IsIso ((CategoryTheory.Over.forget S').map g_scheme) from
      isIso_of_reflects_iso g_scheme (CategoryTheory.Over.forget S')
    simp only [CategoryTheory.Over.forget_map, g_scheme]
    exact ‹IsIso f_map.hom.left›
  let g_et : (CategoryTheory.Over.pullback p₀).obj X₀_et ⟶ X_et := hΦ.preimage g_scheme
  have : IsIso g_et := by
    let := hΦ.reflectsIsomorphisms
    have : IsIso (Φ.map g_et) := (hΦ.map_preimage g_scheme).symm ▸ ‹IsIso g_scheme›
    exact isIso_of_reflects_iso g_et Φ
  have hf_map : f_map.hom.left = (toScheme S).map g_et.left :=
    (congrArg CategoryTheory.Over.Hom.left (hΦ.map_preimage g_scheme)).symm
  let f_et : (TauCeti.DescentDatum.baseChange p₀ X₀_et).Hom D :=
    TauCeti.DescentDatum.Hom.ofMap (toScheme S) g_et f_map hf_map
  have : IsIso f_et.hom := by
    rw [TauCeti.DescentDatum.Hom.ofMap_hom]
    infer_instance
  exact ⟨f_et, ‹_›⟩

/-- Base changes of a surjective étale map `p : S' ⟶ S` give sheaf-covering effective
epimorphisms in `Over (Etale.mk (𝟙 S))`. -/
private lemma isSheafFor_mapPullbackAdj_counit {S S' : Scheme.{u}} (p : S' ⟶ S)
    [AlgebraicGeometry.Etale p] [Surjective p] (p₀ : Etale.mk p ⟶ Etale.mk (𝟙 S))
    (hp₀ : (toScheme S).map p₀ = p)
    (F : Sheaf (smallEtaleTopology S) (Type u)) (T : CategoryTheory.Over (Etale.mk (𝟙 S))) :
    Presieve.IsSheafFor (F.over (Etale.mk (𝟙 S))).obj
        (.singleton ((CategoryTheory.Over.mapPullbackAdj p₀).counit.app T)) ∧
      EffectiveEpi (Limits.pullback.fst T.hom p₀) := by
  have : Surjective ((toScheme S).map p₀) := by rw [hp₀]; exact ‹Surjective p›
  have hsurj : Surjective (Limits.pullback.fst T.hom p₀).left :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (IsPullback.of_isLimit (isLimitOfHasPullbackOfPreservesLimit (toScheme S) T.hom p₀)).flip ‹_›
  have hcounit : ((CategoryTheory.Over.mapPullbackAdj p₀).counit.app T).left =
      Limits.pullback.fst T.hom p₀ := by
    simp only [CategoryTheory.Over.mapPullbackAdj_counit_app, CategoryTheory.Over.homMk_left]
  have : Surjective ((CategoryTheory.Over.mapPullbackAdj p₀).counit.app T).left.left :=
    hcounit ▸ hsurj
  exact ⟨isSheafFor_singleton_over_of_surjective F (Etale.mk (𝟙 S))
      ((CategoryTheory.Over.mapPullbackAdj p₀).counit.app T),
    Etale.effectiveEpi_of_surjective _⟩

/-- Transfer representability of `F.over U₀` at a terminal object `U₀ : S.Etale` to an
isomorphism `(toSheaf S).obj X₀ ≅ F` in `Sheaf (smallEtaleTopology S) (Type u)`. -/
private noncomputable def representableOfRepresentableOverTerminal {S : Scheme.{u}}
    {U₀ : S.Etale} (hU₀ : IsTerminal U₀) (F : Sheaf (smallEtaleTopology S) (Type u))
    (X₀ : TauCeti.FiniteEtaleScheme S)
    (rep₀ : (F.over U₀).obj.RepresentableBy
      (CategoryTheory.Over.mk (hU₀.from ((toEtale S).obj X₀)))) :
    (toSheaf S).obj X₀ ≅ F :=
  let eqU₀ := (CategoryTheory.Over.equivalenceOfIsTerminal hU₀).symm
  let rep : F.obj.RepresentableBy ((toEtale S).obj X₀) :=
    (eqU₀.toAdjunction.representableByComp rep₀).ofIso
      ((Functor.associator eqU₀.functor.op (CategoryTheory.Over.forget U₀).op F.obj).symm ≪≫
        Functor.isoWhiskerRight
          (NatIso.op (CategoryTheory.Over.equivalenceOfIsTerminal hU₀).counitIso.symm) F.obj ≪≫
        Functor.leftUnitor F.obj)
  (fullyFaithfulSheafToPresheaf (smallEtaleTopology S) (Type u)).preimageIso rep.toIso

/-- Effective descent for representability of étale sheaves by finite étale schemes along a
quasi-compact surjective étale morphism `p : S' ⟶ S`. -/
theorem exists_toSheaf_iso_of_smallEtalePullback_iso {S S' : Scheme.{u}} (p : S' ⟶ S)
    [AlgebraicGeometry.Etale p] [Surjective p] [QuasiCompact p] (X : TauCeti.FiniteEtaleScheme S')
    (F : Sheaf (smallEtaleTopology S) (Type u))
    (e : (toSheaf S').obj X ≅ (p.smallEtalePullback (Type u)).obj F) :
    ∃ X₀ : TauCeti.FiniteEtaleScheme S, Nonempty ((toSheaf S).obj X₀ ≅ F) := by
  let U₀ : S.Etale := Etale.mk (𝟙 S)
  let hU₀ : IsTerminal U₀ := Etale.mkIdTerminal S
  let p₀ : Etale.mk p ⟶ U₀ := MorphismProperty.Over.homMk p (Category.comp_id p)
  -- Represent `(Over.map p₀).op ⋙ (F.over U₀).obj` and transport its descent datum to `Scheme`.
  let X_et := (Etale.mk p).iteratedSliceEquiv.inverse.obj ((toEtale S').obj X)
  let e_rep := representableByOverPullback p X F e p₀
  have hp₀ : (toScheme S).map p₀ = p := toScheme_map_homMk p
  have hX_hom : (toScheme S).map X_et.hom = X.obj.hom := toScheme_map_toEtale_inverse_hom p X
  have : Surjective ((toScheme S).map p₀) := by rw [hp₀]; exact ‹Surjective p›
  have hp_flat : Flat p := inferInstance
  have : Flat ((toScheme S).map p₀) := by rw [hp₀]; exact hp_flat
  have : QuasiCompact ((toScheme S).map p₀) := by rw [hp₀]; exact ‹QuasiCompact p›
  obtain ⟨hX_fin, hX_et⟩ := (TauCeti.finiteEtaleSchemeProperty_iff X.obj).mp X.property
  have : IsFinite (CategoryTheory.Over.mk ((toScheme S).map X_et.hom)).hom := hX_hom ▸ hX_fin
  have : AlgebraicGeometry.Etale (CategoryTheory.Over.mk ((toScheme S).map X_et.hom)).hom :=
    hX_hom ▸ hX_et
  -- Apply effective fpqc descent in `Scheme` and lift the descended model back to `Over U₀`.
  obtain ⟨X₀_over, hfin, het, f, hf⟩ :=
    (e_rep.descentDatum.map (toScheme S)).exists_isFinite_etale_baseChange_hom_isIso_of_quasiCompact
  have hX₀ : TauCeti.finiteEtaleSchemeProperty S X₀_over :=
    (TauCeti.finiteEtaleSchemeProperty_iff _).mpr ⟨hfin, het⟩
  let X₀ : TauCeti.FiniteEtaleScheme S := ⟨X₀_over, hX₀⟩
  obtain ⟨f_et, hf_et⟩ := liftDescentDatumHom p p₀ e_rep.descentDatum X₀_over hX₀ f
  -- Descend the local representation along `p₀` and identify `F.over U₀` with `F`.
  have hF (T : CategoryTheory.Over U₀) :=
    (isSheafFor_mapPullbackAdj_counit p p₀ hp₀ F T).1
  have (T : CategoryTheory.Over U₀) :=
    (isSheafFor_mapPullbackAdj_counit p p₀ hp₀ F T).2
  exact ⟨X₀, ⟨representableOfRepresentableOverTerminal hU₀ F X₀ (e_rep.descend hF f_et)⟩⟩

end AlgebraicGeometry.Scheme.Hom
