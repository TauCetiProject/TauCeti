/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.RestrictSheaf
import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
import TauCeti.AlgebraicGeometry.Descent.Fpqc
import TauCeti.AlgebraicGeometry.Sites.Etale.Localization
import TauCeti.CategoryTheory.Adjunction.Representable
import TauCeti.CategoryTheory.EffectiveEpi.Representable

/-!
# Effective étale descent for representability of étale sheaves of sets

This file establishes effective étale descent for representability of étale sheaves of sets by
finite étale schemes along a quasi-compact surjective étale morphism.

Given a quasi-compact surjective étale morphism `p : S' ⟶ S` and an étale sheaf of sets `F` on `S`
whose inverse image `p.smallEtalePullback (Type u)` to `S'` is representable by a finite étale
`S'`-scheme `X`, we restrict `F` to the slice of `S.Etale` over the terminal object. Via the
iterated slice equivalence over `Etale.mk p`, the local representation induces a descent datum in
`S.Etale` (`CategoryTheory.Functor.RepresentableBy.descentDatum`). Transporting this datum to
`Scheme` and applying effective fpqc descent for finite étale schemes
(`TauCeti.DescentDatum.exists_isFinite_etale_baseChange_hom_isIso_of_quasiCompact`) produces a
finite étale `S`-scheme `X₀` whose descended model lifts back to `S.Etale`, so
`CategoryTheory.Functor.RepresentableBy.descend` represents `F` by `X₀`.

## Main results

* `TauCeti.FiniteEtaleScheme.exists_toSheaf_iso_of_smallEtalePullback_iso`: representability of an
  étale sheaf of sets by a finite étale scheme satisfies effective descent along any quasi-compact
  surjective étale morphism.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IX, §2.
* The Stacks Project, [Tag 0245](https://stacks.math.columbia.edu/tag/0245).
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

section SingleCoverDescent

private lemma mem_smallEtaleTopology_singleton_of_surjective {S : Scheme.{u}}
    {U V : S.Etale} (f : U ⟶ V) [Surjective f.left] :
    Sieve.generate (.singleton f) ∈ Scheme.smallEtaleTopology S V :=
  (Scheme.mem_smallEtaleTopology_iff _).mpr fun x ↦
    let ⟨u, hu⟩ := f.left.surjective x
    ⟨U, f, u, Sieve.le_generate (.singleton f) _ _ (.mk), hu⟩

private lemma effectiveEpi_of_surjective {S : Scheme.{u}} {U V : S.Etale} (f : U ⟶ V)
    [Surjective f.left] : EffectiveEpi f := by
  refine (Sieve.effectiveEpimorphic_singleton f).mp
    ((Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda _).mpr fun W ↦ ?_)
  rw [Presieve.isSheafFor_iff_generate]
  exact (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := Scheme.smallEtaleTopology S) (yoneda.obj W))
    (Sieve.generate (.singleton f)) (mem_smallEtaleTopology_singleton_of_surjective f)

private lemma isSheafFor_singleton_over_of_surjective {S : Scheme.{u}}
    (F : Sheaf (Scheme.smallEtaleTopology S) (Type u)) {U₀ : S.Etale} (hU₀ : IsTerminal U₀)
    {A B : CategoryTheory.Over U₀} (g : A ⟶ B) [Surjective g.left.left] :
    Presieve.IsSheafFor ((CategoryTheory.Over.forget U₀).op ⋙ F.obj) (.singleton g) := by
  have hg : Presieve.IsSheafFor F.obj (.singleton g.left) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact (isSheaf_iff_isSheaf_of_type _ _).mp F.property _
      (mem_smallEtaleTopology_singleton_of_surjective g.left)
  rw [Presieve.isSheafFor_singleton] at hg ⊢
  intro s hs
  obtain ⟨t, ht, huniq⟩ := hg s fun {W} a₁ a₂ ha ↦ hs
    (CategoryTheory.Over.homMk a₁ (hU₀.hom_ext _ _) : CategoryTheory.Over.mk (hU₀.from W) ⟶ A)
    (CategoryTheory.Over.homMk a₂ (hU₀.hom_ext _ _))
    (CategoryTheory.Over.OverMorphism.ext ha)
  exact ⟨t, ht, fun t' ht' ↦ huniq t' ht'⟩

/-- Action-space comparison isomorphism for a pullback-preserving functor `L : C ⥤ D`. -/
private noncomputable def mapDescentActionIso {C D : Type*} [Category* C] [Category* D]
    [HasPullbacks C] [HasPullbacks D] (L : C ⥤ D) [PreservesLimitsOfShape WalkingCospan L]
    {U₀ U : C} (p₀ : U ⟶ U₀) (X : CategoryTheory.Over U) :
    Limits.pullback (L.map p₀) (L.map X.hom ≫ L.map p₀) ≅
      L.obj (Limits.pullback p₀ (X.hom ≫ p₀)) :=
  (Limits.pullback.congrHom rfl (L.map_comp X.hom p₀)).symm ≪≫
    (PreservesPullback.iso L p₀ (X.hom ≫ p₀)).symm

@[reassoc]
private lemma mapDescentActionIso_hom_fst {C D : Type*} [Category* C] [Category* D]
    [HasPullbacks C] [HasPullbacks D] (L : C ⥤ D) [PreservesLimitsOfShape WalkingCospan L]
    {U₀ U : C} (p₀ : U ⟶ U₀) (X : CategoryTheory.Over U) :
    (mapDescentActionIso L p₀ X).hom ≫ L.map (Limits.pullback.fst p₀ (X.hom ≫ p₀)) =
      Limits.pullback.fst (L.map p₀) (L.map X.hom ≫ L.map p₀) := by
  simp [mapDescentActionIso]

@[reassoc]
private lemma mapDescentActionIso_hom_snd {C D : Type*} [Category* C] [Category* D]
    [HasPullbacks C] [HasPullbacks D] (L : C ⥤ D) [PreservesLimitsOfShape WalkingCospan L]
    {U₀ U : C} (p₀ : U ⟶ U₀) (X : CategoryTheory.Over U) :
    (mapDescentActionIso L p₀ X).hom ≫ L.map (Limits.pullback.snd p₀ (X.hom ≫ p₀)) =
      Limits.pullback.snd (L.map p₀) (L.map X.hom ≫ L.map p₀) := by
  simp [mapDescentActionIso]

/-- Transport a descent datum along a pullback-preserving functor `L : C ⥤ D`. -/
private noncomputable def mapDescentDatum {C D : Type*} [Category* C] [Category* D]
    [HasPullbacks C] [HasPullbacks D] (L : C ⥤ D) [PreservesLimitsOfShape WalkingCospan L]
    {U₀ U : C} {p₀ : U ⟶ U₀} {X : CategoryTheory.Over U} (D₀ : DescentDatum p₀ X) :
    DescentDatum (L.map p₀) (CategoryTheory.Over.mk (L.map X.hom)) where
  act := (mapDescentActionIso L p₀ X).hom ≫ L.map D₀.act
  act_hom := by
    dsimp only [CategoryTheory.Over.mk_left, CategoryTheory.Over.mk_hom]
    have h : L.map D₀.act ≫ L.map X.hom = L.map (Limits.pullback.fst p₀ (X.hom ≫ p₀)) :=
      (L.map_comp _ _).symm.trans (congrArg L.map D₀.act_hom)
    rw [Category.assoc, h]
    exact mapDescentActionIso_hom_fst L p₀ X
  lift_act := by
    dsimp only [CategoryTheory.Over.mk_left, CategoryTheory.Over.mk_hom]
    have hlift : Limits.pullback.lift (L.map X.hom) (𝟙 (L.obj X.left)) (by simp) =
        L.map (Limits.pullback.lift X.hom (𝟙 X.left) (by simp)) ≫
          (mapDescentActionIso L p₀ X).inv := by
      refine Limits.pullback.hom_ext ?_ ?_ <;> simp [mapDescentActionIso]
    rw [hlift, Category.assoc, Iso.inv_hom_id_assoc, ← L.map_comp, D₀.lift_act, L.map_id]
  act_assoc := by
    dsimp only [CategoryTheory.Over.mk_left, CategoryTheory.Over.mk_hom]
    let e₁ := mapDescentActionIso L p₀ X
    let Q := Limits.pullback p₀ (Limits.pullback.fst p₀ (X.hom ≫ p₀) ≫ p₀)
    let Q' := Limits.pullback (L.map p₀)
      (Limits.pullback.fst (L.map p₀) (L.map X.hom ≫ L.map p₀) ≫ L.map p₀)
    let eQ : Q' ≅ L.obj Q :=
      asIso (Limits.pullback.map _ _ _ _ (𝟙 (L.obj U)) e₁.hom (𝟙 (L.obj U₀))
        (by simp) (by simp [e₁, mapDescentActionIso, L.map_comp])) ≪≫
        (PreservesPullback.iso L _ _).symm
    have heQ_fst : eQ.hom ≫ L.map (Limits.pullback.fst p₀ _) = Limits.pullback.fst _ _ := by
      simp [eQ]
    have heQ_snd : eQ.hom ≫ L.map (Limits.pullback.snd p₀ _) =
        Limits.pullback.snd _ _ ≫ e₁.hom := by
      simp [eQ]
    let aL : Q ⟶ Limits.pullback p₀ (X.hom ≫ p₀) := Limits.pullback.lift
      (Limits.pullback.fst p₀ (Limits.pullback.fst p₀ (X.hom ≫ p₀) ≫ p₀))
      (Limits.pullback.snd p₀ (Limits.pullback.fst p₀ (X.hom ≫ p₀) ≫ p₀) ≫ D₀.act)
      (by rw [Category.assoc, D₀.act_hom_assoc]; exact Limits.pullback.condition)
    let aR : Q ⟶ Limits.pullback p₀ (X.hom ≫ p₀) := Limits.pullback.lift
      (Limits.pullback.fst p₀ (Limits.pullback.fst p₀ (X.hom ≫ p₀) ≫ p₀))
      (Limits.pullback.snd p₀ (Limits.pullback.fst p₀ (X.hom ≫ p₀) ≫ p₀) ≫
        Limits.pullback.snd p₀ (X.hom ≫ p₀))
      (by
        rw [Category.assoc, ← Limits.pullback.condition (f := p₀) (g := X.hom ≫ p₀)]
        exact Limits.pullback.condition)
    have he₁_fst : e₁.inv ≫ Limits.pullback.fst (L.map p₀) (L.map X.hom ≫ L.map p₀) =
        L.map (Limits.pullback.fst p₀ (X.hom ≫ p₀)) :=
      (congrArg (e₁.inv ≫ ·) (mapDescentActionIso_hom_fst L p₀ X).symm).trans
        (e₁.inv_hom_id_assoc _)
    have he₁_snd : e₁.inv ≫ Limits.pullback.snd (L.map p₀) (L.map X.hom ≫ L.map p₀) =
        L.map (Limits.pullback.snd p₀ (X.hom ≫ p₀)) :=
      (congrArg (e₁.inv ≫ ·) (mapDescentActionIso_hom_snd L p₀ X).symm).trans
        (e₁.inv_hom_id_assoc _)
    have hact_p : L.map D₀.act ≫ L.map X.hom ≫ L.map p₀ =
        L.map (Limits.pullback.fst p₀ (X.hom ≫ p₀)) ≫ L.map p₀ := by
      rw [← Category.assoc, ← L.map_comp, D₀.act_hom]
    have hL : Limits.pullback.lift (Limits.pullback.fst _ _)
          (Limits.pullback.snd _ _ ≫ e₁.hom ≫ L.map D₀.act)
          (by rw [Category.assoc, Category.assoc, hact_p,
            mapDescentActionIso_hom_fst_assoc]; exact Limits.pullback.condition) =
        eQ.hom ≫ L.map aL ≫ e₁.inv := by
      refine Limits.pullback.hom_ext ?_ ?_
      · rw [Limits.pullback.lift_fst, Category.assoc, Category.assoc, he₁_fst,
          ← L.map_comp aL _]
        dsimp only [aL]
        rw [Limits.pullback.lift_fst, heQ_fst]
      · rw [Limits.pullback.lift_snd, Category.assoc, Category.assoc, he₁_snd,
          ← L.map_comp aL _]
        dsimp only [aL]
        rw [Limits.pullback.lift_snd, L.map_comp, ← Category.assoc eQ.hom, heQ_snd, Category.assoc]
    have hR : Limits.pullback.lift (Limits.pullback.fst _ _)
          (Limits.pullback.snd _ _ ≫ Limits.pullback.snd _ _)
          (by
            rw [Category.assoc,
              ← Limits.pullback.condition (f := L.map p₀) (g := L.map X.hom ≫ L.map p₀)]
            exact Limits.pullback.condition) =
        eQ.hom ≫ L.map aR ≫ e₁.inv := by
      refine Limits.pullback.hom_ext ?_ ?_
      · rw [Limits.pullback.lift_fst, Category.assoc, Category.assoc, he₁_fst,
          ← L.map_comp aR _]
        dsimp only [aR]
        rw [Limits.pullback.lift_fst, heQ_fst]
      · rw [Limits.pullback.lift_snd, Category.assoc, Category.assoc, he₁_snd,
          ← L.map_comp aR _]
        dsimp only [aR]
        rw [Limits.pullback.lift_snd, L.map_comp, ← Category.assoc, heQ_snd,
          Category.assoc, mapDescentActionIso_hom_snd]
    dsimp only [e₁] at hL hR
    rw [hL, hR]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← L.map_comp]
    exact congrArg (eQ.hom ≫ L.map ·) D₀.act_assoc

/-- Effective descent for representability of étale sheaves by finite étale schemes along a
quasi-compact surjective étale morphism `p : S' ⟶ S`. -/
theorem exists_toSheaf_iso_of_smallEtalePullback_iso {S S' : Scheme.{u}} (p : S' ⟶ S) [Etale p]
    [Surjective p] [QuasiCompact p] (X : FiniteEtaleScheme S')
    (F : Sheaf (Scheme.smallEtaleTopology S) (Type u))
    (e : (toSheaf S').obj X ≅ (p.smallEtalePullback (Type u)).obj F) :
    ∃ X₀ : FiniteEtaleScheme S, Nonempty ((toSheaf S).obj X₀ ≅ F) := by
  let U₀ : S.Etale := Scheme.Etale.mk (𝟙 S)
  let hU₀ : IsTerminal U₀ :=
    IsTerminal.isTerminalOfObj (Scheme.Etale.forget S) _ CategoryTheory.Over.mkIdTerminal
  let U : S.Etale := Scheme.Etale.mk p
  let p₀ : U ⟶ U₀ := MorphismProperty.Over.homMk p (Category.comp_id p)
  let F₀ : (CategoryTheory.Over U₀)ᵒᵖ ⥤ Type u := (CategoryTheory.Over.forget U₀).op ⋙ F.obj
  -- Representability of `F₀` after base change along `p₀ : U ⟶ U₀`.
  let e' : (Scheme.smallEtaleTopology S').yoneda.obj ((toEtale S').obj X) ≅
      (p.smallEtaleMap.sheafPushforwardContinuous (Type u)
        (Scheme.smallEtaleTopology S') (Scheme.smallEtaleTopology S)).obj F :=
    e ≪≫ (p.smallEtalePullbackIsoMapPushforward (Type u)).app F
  let ePresheaf : U.iteratedSliceEquiv.functor.op ⋙ yoneda.obj ((toEtale S').obj X) ≅
      (CategoryTheory.Over.map p₀).op ⋙ F₀ :=
    Functor.isoWhiskerLeft U.iteratedSliceEquiv.functor.op
      ((sheafToPresheaf (Scheme.smallEtaleTopology S') (Type u)).mapIso e') ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (NatIso.op U.iteratedSliceEquivFunctorCompMapIso.symm) F.obj ≪≫
      Functor.associator (CategoryTheory.Over.map p₀).op (CategoryTheory.Over.forget U₀).op F.obj
  let X_et : CategoryTheory.Over U := U.iteratedSliceEquiv.inverse.obj ((toEtale S').obj X)
  let e_rep : ((CategoryTheory.Over.map p₀).op ⋙ F₀).RepresentableBy X_et :=
    (U.iteratedSliceEquiv.toAdjunction.representableByComp
      (Functor.RepresentableBy.yoneda ((toEtale S').obj X))).ofIso ePresheaf
  -- Transport `e_rep.descentDatum` to `Scheme` and apply effective fpqc descent.
  let L : S.Etale ⥤ Scheme.{u} := Scheme.Etale.forget S ⋙ CategoryTheory.Over.forget S
  let D_scheme : DescentDatum p X.obj := mapDescentDatum L e_rep.descentDatum
  obtain ⟨X₀_over, hfin, het, f, hf⟩ :=
    D_scheme.exists_isFinite_etale_baseChange_hom_isIso_of_quasiCompact
  let X₀ : FiniteEtaleScheme S := ⟨X₀_over, (finiteEtaleSchemeProperty_iff _).mpr ⟨hfin, het⟩⟩
  let X₀_et : CategoryTheory.Over U₀ :=
    CategoryTheory.Over.mk (hU₀.from ((toEtale S).obj X₀))
  have hX₀_hom : L.map X₀_et.hom = X₀_over.hom :=
    (Category.comp_id _).symm.trans (MorphismProperty.Over.w (hU₀.from ((toEtale S).obj X₀)))
  -- Lift the descended model isomorphism `f` back to `CategoryTheory.Over U`.
  let e_pb_lift : Limits.pullback (L.map X₀_et.hom) (L.map p₀) ≅ Limits.pullback X₀_over.hom p :=
    { hom := Limits.pullback.lift (Limits.pullback.fst (L.map X₀_et.hom) (L.map p₀))
        (Limits.pullback.snd (L.map X₀_et.hom) (L.map p₀))
        (by
          refine (congrArg (fun x : L.obj X₀_et.left ⟶ L.obj U₀ ↦
            Limits.pullback.fst (L.map X₀_et.hom) (L.map p₀) ≫ x) hX₀_hom.symm).trans ?_
          exact Limits.pullback.condition)
      inv := Limits.pullback.lift (Limits.pullback.fst X₀_over.hom p)
        (Limits.pullback.snd X₀_over.hom p)
        (by
          refine (congrArg (fun x : X₀_over.left ⟶ S ↦
            Limits.pullback.fst X₀_over.hom p ≫ x) hX₀_hom).trans ?_
          exact Limits.pullback.condition)
      hom_inv_id := Limits.pullback.hom_ext
        ((Category.assoc _ _ _).trans ((congrArg _ (Limits.pullback.lift_fst _ _ _)).trans
          ((Limits.pullback.lift_fst _ _ _).trans (Category.id_comp _).symm)))
        ((Category.assoc _ _ _).trans ((congrArg _ (Limits.pullback.lift_snd _ _ _)).trans
          ((Limits.pullback.lift_snd _ _ _).trans (Category.id_comp _).symm)))
      inv_hom_id := Limits.pullback.hom_ext
        ((Category.assoc _ _ _).trans ((congrArg _ (Limits.pullback.lift_fst _ _ _)).trans
          ((Limits.pullback.lift_fst _ _ _).trans (Category.id_comp _).symm)))
        ((Category.assoc _ _ _).trans ((congrArg _ (Limits.pullback.lift_snd _ _ _)).trans
          ((Limits.pullback.lift_snd _ _ _).trans (Category.id_comp _).symm))) }
  let e_pb : L.obj (Limits.pullback X₀_et.hom p₀) ≅ Limits.pullback X₀_over.hom p :=
    PreservesPullback.iso L X₀_et.hom p₀ ≪≫ e_pb_lift
  have he_pb_fst : e_pb.hom ≫ Limits.pullback.fst X₀_over.hom p =
      L.map (Limits.pullback.fst X₀_et.hom p₀) :=
    (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (Limits.pullback.lift_fst _ _ _)).trans
        (PreservesPullback.iso_hom_fst L X₀_et.hom p₀))
  have he_pb_snd : e_pb.hom ≫ Limits.pullback.snd X₀_over.hom p =
      L.map (Limits.pullback.snd X₀_et.hom p₀) :=
    (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (Limits.pullback.lift_snd _ _ _)).trans
        (PreservesPullback.iso_hom_snd L X₀_et.hom p₀))
  let Φ : CategoryTheory.Over U ⥤ CategoryTheory.Over S' :=
    U.iteratedSliceEquiv.functor ⋙ Scheme.Etale.forget S'
  let hΦ : Φ.FullyFaithful :=
    U.iteratedSliceEquiv.fullyFaithfulFunctor.comp (Scheme.Etale.forgetFullyFaithful S')
  let g_scheme : Φ.obj ((CategoryTheory.Over.pullback p₀).obj X₀_et) ⟶ Φ.obj X_et :=
    CategoryTheory.Over.homMk (e_pb.hom ≫ f.hom.left) <| by
      change (e_pb.hom ≫ f.hom.left) ≫ X.obj.hom = L.map (Limits.pullback.snd X₀_et.hom p₀)
      rw [Category.assoc, CategoryTheory.Over.w f.hom]
      exact he_pb_snd
  have : IsIso g_scheme := by
    suffices IsIso ((CategoryTheory.Over.forget S').map g_scheme) from
      isIso_of_reflects_iso g_scheme (CategoryTheory.Over.forget S')
    change IsIso (e_pb.hom ≫ f.hom.left)
    infer_instance
  let g_et : (CategoryTheory.Over.pullback p₀).obj X₀_et ⟶ X_et := hΦ.preimage g_scheme
  have : IsIso g_et := by
    let := hΦ.reflectsIsomorphisms
    have : IsIso (Φ.map g_et) := by simpa [g_et] using ‹IsIso g_scheme›
    exact isIso_of_reflects_iso g_et Φ
  have hg_et : L.map g_et.left = e_pb.hom ≫ f.hom.left :=
    congrArg CategoryTheory.Over.Hom.left (hΦ.map_preimage g_scheme)
  let f_et : (DescentDatum.baseChange p₀ X₀_et).Hom e_rep.descentDatum :=
    { hom := g_et
      map_act := L.map_injective <| by
        dsimp only [CategoryTheory.Over.pullback_obj_hom]
        let e₁ : Limits.pullback p (X.obj.hom ≫ p) ≅
            L.obj (Limits.pullback p₀ (X_et.hom ≫ p₀)) :=
          mapDescentActionIso L p₀ X_et
        have hact : L.map e_rep.descentDatum.act = e₁.inv ≫ D_scheme.act :=
          (e₁.inv_hom_id_assoc (L.map e_rep.descentDatum.act)).symm
        have he₁_fst : e₁.inv ≫ Limits.pullback.fst p (X.obj.hom ≫ p) =
            L.map (Limits.pullback.fst p₀ (X_et.hom ≫ p₀)) :=
          (congrArg (e₁.inv ≫ ·) (mapDescentActionIso_hom_fst L p₀ X_et).symm).trans
            (e₁.inv_hom_id_assoc _)
        have he₁_snd : e₁.inv ≫ Limits.pullback.snd p (X.obj.hom ≫ p) =
            L.map (Limits.pullback.snd p₀ (X_et.hom ≫ p₀)) :=
          (congrArg (e₁.inv ≫ ·) (mapDescentActionIso_hom_snd L p₀ X_et).symm).trans
            (e₁.inv_hom_id_assoc _)
        let m₀ : L.obj (Limits.pullback p₀ (Limits.pullback.snd X₀_et.hom p₀ ≫ p₀)) ⟶
            Limits.pullback p (Limits.pullback.snd X₀_over.hom p ≫ p) :=
          Limits.pullback.lift (L.map (Limits.pullback.fst _ _))
            (L.map (Limits.pullback.snd _ _) ≫ e_pb.hom) (by
              have hcond : L.map (Limits.pullback.fst p₀ (Limits.pullback.snd X₀_et.hom p₀ ≫ p₀)) ≫
                  L.map p₀ =
                L.map (Limits.pullback.snd p₀ (Limits.pullback.snd X₀_et.hom p₀ ≫ p₀)) ≫
                  L.map (Limits.pullback.snd X₀_et.hom p₀ ≫ p₀) := by
                rw [← L.map_comp, Limits.pullback.condition, L.map_comp]
              refine hcond.trans ?_
              refine (congrArg (L.map _ ≫ ·) (L.map_comp _ _)).trans ?_
              refine (congrArg (L.map _ ≫ · ≫ L.map p₀) he_pb_snd.symm).trans ?_
              simp only [Category.assoc]
              rfl)
        have hm₁ : L.map (Limits.pullback.map p₀ (Limits.pullback.snd X₀_et.hom p₀ ≫ p₀) p₀
              (X_et.hom ≫ p₀) (𝟙 U) g_et.left (𝟙 U₀) (by simp) (by simp)) ≫ e₁.inv =
            m₀ ≫ Limits.pullback.map p (Limits.pullback.snd X₀_over.hom p ≫ p) p
              (X.obj.hom ≫ p) (𝟙 S') f.hom.left (𝟙 S) (by simp) (by simp) := by
          refine Limits.pullback.hom_ext ?_ ?_
          · refine (Category.assoc _ _ _).trans ((congrArg (L.map _ ≫ ·) he₁_fst).trans ?_)
            have hL : L.map (Limits.pullback.map p₀ (Limits.pullback.snd X₀_et.hom p₀ ≫ p₀) p₀
                  (X_et.hom ≫ p₀) (𝟙 U) g_et.left (𝟙 U₀) (by simp) (by simp)) ≫
                  L.map (Limits.pullback.fst p₀ (X_et.hom ≫ p₀)) =
                L.map (Limits.pullback.fst p₀ (Limits.pullback.snd X₀_et.hom p₀ ≫ p₀)) := by
              rw [← L.map_comp, Limits.pullback.lift_fst, Category.comp_id]
            have hR : (m₀ ≫ Limits.pullback.map p (Limits.pullback.snd X₀_over.hom p ≫ p) p
                  (X.obj.hom ≫ p) (𝟙 S') f.hom.left (𝟙 S) (by simp) (by simp)) ≫
                  Limits.pullback.fst p (X.obj.hom ≫ p) =
                L.map (Limits.pullback.fst p₀ (Limits.pullback.snd X₀_et.hom p₀ ≫ p₀)) := by
              rw [Category.assoc, Limits.pullback.lift_fst, Category.comp_id]
              dsimp only [m₀]
              exact Limits.pullback.lift_fst _ _ _
            exact hL.trans hR.symm
          · refine (Category.assoc _ _ _).trans ((congrArg (L.map _ ≫ ·) he₁_snd).trans ?_)
            have hL : L.map (Limits.pullback.map p₀ (Limits.pullback.snd X₀_et.hom p₀ ≫ p₀) p₀
                  (X_et.hom ≫ p₀) (𝟙 U) g_et.left (𝟙 U₀) (by simp) (by simp)) ≫
                  L.map (Limits.pullback.snd p₀ (X_et.hom ≫ p₀)) =
                L.map (Limits.pullback.snd p₀ (Limits.pullback.snd X₀_et.hom p₀ ≫ p₀)) ≫
                  e_pb.hom ≫ f.hom.left := by
              rw [← L.map_comp, Limits.pullback.lift_snd, L.map_comp]
              exact congrArg (L.map _ ≫ ·) hg_et
            have hR : (m₀ ≫ Limits.pullback.map p (Limits.pullback.snd X₀_over.hom p ≫ p) p
                  (X.obj.hom ≫ p) (𝟙 S') f.hom.left (𝟙 S) (by simp) (by simp)) ≫
                  Limits.pullback.snd p (X.obj.hom ≫ p) =
                L.map (Limits.pullback.snd p₀ (Limits.pullback.snd X₀_et.hom p₀ ≫ p₀)) ≫
                  e_pb.hom ≫ f.hom.left := by
              rw [Category.assoc, Limits.pullback.lift_snd]
              dsimp only [m₀]
              exact (congrArg (· ≫ f.hom.left) (Limits.pullback.lift_snd _ _ _)).trans
                (Category.assoc _ _ _)
            exact hL.trans hR.symm
        have hm₂ : m₀ ≫ (DescentDatum.baseChange p X₀_over).act =
            L.map (DescentDatum.baseChange p₀ X₀_et).act ≫ e_pb.hom := by
          refine Limits.pullback.hom_ext ?_ ?_
          · have hL1 : m₀ ≫ (DescentDatum.baseChange p X₀_over).act ≫
                  Limits.pullback.fst X₀_over.hom p =
                L.map (Limits.pullback.snd _ _) ≫
                  e_pb.hom ≫ Limits.pullback.fst X₀_over.hom p := by
              rw [DescentDatum.baseChange_act_fst, ← Category.assoc]
              dsimp only [CategoryTheory.Over.pullback_obj_hom, m₀]
              exact (congrArg (· ≫ Limits.pullback.fst X₀_over.hom p)
                (Limits.pullback.lift_snd _ _ _)).trans (Category.assoc _ _ _)
            have hL2 : L.map (Limits.pullback.snd p₀ (Limits.pullback.snd X₀_et.hom p₀ ≫ p₀)) ≫
                  (e_pb.hom ≫ Limits.pullback.fst X₀_over.hom p) =
                L.map (Limits.pullback.snd p₀ (Limits.pullback.snd X₀_et.hom p₀ ≫ p₀)) ≫
                  L.map (Limits.pullback.fst X₀_et.hom p₀) :=
              congrArg _ he_pb_fst
            have hM : L.map (Limits.pullback.snd _ _) ≫ L.map (Limits.pullback.fst X₀_et.hom p₀) =
                L.map (DescentDatum.baseChange p₀ X₀_et).act ≫
                  L.map (Limits.pullback.fst X₀_et.hom p₀) := by
              rw [← L.map_comp, ← DescentDatum.baseChange_act_fst p₀ X₀_et, L.map_comp]
            have hR : L.map (DescentDatum.baseChange p₀ X₀_et).act ≫
                  L.map (Limits.pullback.fst X₀_et.hom p₀) =
                (L.map (DescentDatum.baseChange p₀ X₀_et).act ≫ e_pb.hom) ≫
                  Limits.pullback.fst X₀_over.hom p :=
              (congrArg _ he_pb_fst.symm).trans (Category.assoc _ _ _).symm
            exact (Category.assoc _ _ _).trans (hL1.trans (hL2.trans (hM.trans hR)))
          · have hL : m₀ ≫ (DescentDatum.baseChange p X₀_over).act ≫
                  Limits.pullback.snd X₀_over.hom p =
                L.map (Limits.pullback.fst _ _) := by
              rw [DescentDatum.baseChange_act_snd]
              dsimp only [CategoryTheory.Over.pullback_obj_hom]
              simp [m₀]
              rfl
            have hM : L.map (Limits.pullback.fst _ _) =
                L.map (DescentDatum.baseChange p₀ X₀_et).act ≫
                  L.map (Limits.pullback.snd X₀_et.hom p₀) := by
              rw [← DescentDatum.baseChange_act_snd p₀ X₀_et, L.map_comp]
            have hR : L.map (DescentDatum.baseChange p₀ X₀_et).act ≫
                  L.map (Limits.pullback.snd X₀_et.hom p₀) =
                (L.map (DescentDatum.baseChange p₀ X₀_et).act ≫ e_pb.hom) ≫
                  Limits.pullback.snd X₀_over.hom p :=
              (congrArg _ he_pb_snd.symm).trans (Category.assoc _ _ _).symm
            exact (Category.assoc _ _ _).trans (hL.trans (hM.trans hR))
        have s1 : L.map (Limits.pullback.map p₀ (Limits.pullback.snd X₀_et.hom p₀ ≫ p₀) p₀
              (X_et.hom ≫ p₀) (𝟙 U) g_et.left (𝟙 U₀) (by simp) (by simp) ≫
              e_rep.descentDatum.act) =
            (L.map (Limits.pullback.map p₀ (Limits.pullback.snd X₀_et.hom p₀ ≫ p₀) p₀
              (X_et.hom ≫ p₀) (𝟙 U) g_et.left (𝟙 U₀) (by simp) (by simp)) ≫ e₁.inv) ≫
              D_scheme.act :=
          (L.map_comp _ _).trans ((congrArg (L.map _ ≫ ·) hact).trans (Category.assoc _ _ _).symm)
        have s2 : (L.map (Limits.pullback.map p₀ (Limits.pullback.snd X₀_et.hom p₀ ≫ p₀) p₀
              (X_et.hom ≫ p₀) (𝟙 U) g_et.left (𝟙 U₀) (by simp) (by simp)) ≫ e₁.inv) ≫
              D_scheme.act =
            m₀ ≫ Limits.pullback.map p (Limits.pullback.snd X₀_over.hom p ≫ p) p
              (X.obj.hom ≫ p) (𝟙 S') f.hom.left (𝟙 S) (by simp) (by simp) ≫
              D_scheme.act :=
          (congrArg (· ≫ D_scheme.act) hm₁).trans (Category.assoc _ _ _)
        have s3 : m₀ ≫ Limits.pullback.map p (Limits.pullback.snd X₀_over.hom p ≫ p) p
              (X.obj.hom ≫ p) (𝟙 S') f.hom.left (𝟙 S) (by simp) (by simp) ≫
              D_scheme.act =
            (m₀ ≫ (DescentDatum.baseChange p X₀_over).act) ≫ f.hom.left :=
          (congrArg (m₀ ≫ ·) f.map_act).trans (Category.assoc _ _ _).symm
        have s4 : (m₀ ≫ (DescentDatum.baseChange p X₀_over).act) ≫ f.hom.left =
            L.map ((DescentDatum.baseChange p₀ X₀_et).act ≫ g_et.left) :=
          (congrArg (· ≫ f.hom.left) hm₂).trans <|
            (Category.assoc _ _ _).trans <|
              (congrArg (L.map _ ≫ ·) hg_et.symm).trans (L.map_comp _ _).symm
        exact s1.trans (s2.trans (s3.trans s4)) }
  -- Descend the local representation along `p₀` to represent `F₀` by `X₀_et`.
  have hsurj (T : CategoryTheory.Over U₀) : Surjective (pullback.fst T.hom p₀).left := by
    have : Surjective (L.map p₀) := inferInstanceAs (Surjective p)
    have hpst : L.map (pullback.fst T.hom p₀) =
        (PreservesPullback.iso L T.hom p₀).hom ≫ pullback.fst (L.map T.hom) (L.map p₀) :=
      (PreservesPullback.iso_hom_fst L T.hom p₀).symm
    change Surjective (L.map (pullback.fst T.hom p₀))
    rw [hpst]
    infer_instance
  have hF (T : CategoryTheory.Over U₀) :
      Presieve.IsSheafFor F₀ (.singleton ((CategoryTheory.Over.mapPullbackAdj p₀).counit.app T)) :=
    have : Surjective ((CategoryTheory.Over.mapPullbackAdj p₀).counit.app T).left.left :=
      hsurj T
    isSheafFor_singleton_over_of_surjective F hU₀
      ((CategoryTheory.Over.mapPullbackAdj p₀).counit.app T)
  have (T : CategoryTheory.Over U₀) : EffectiveEpi (pullback.fst T.hom p₀) :=
    have := hsurj T
    effectiveEpi_of_surjective _
  let rep₀ : F₀.RepresentableBy X₀_et := e_rep.descend hF f_et
  let eqU₀ := (CategoryTheory.Over.equivalenceOfIsTerminal hU₀).symm
  let rep : F.obj.RepresentableBy ((toEtale S).obj X₀) :=
    (eqU₀.toAdjunction.representableByComp rep₀).ofIso
      ((Functor.associator eqU₀.functor.op (CategoryTheory.Over.forget U₀).op F.obj).symm ≪≫
        Functor.isoWhiskerRight
          (NatIso.op (CategoryTheory.Over.equivalenceOfIsTerminal hU₀).counitIso.symm) F.obj ≪≫
        Functor.leftUnitor F.obj)
  exact ⟨X₀, ⟨(fullyFaithfulSheafToPresheaf (Scheme.smallEtaleTopology S) (Type u)).preimageIso
    rep.toIso⟩⟩

end SingleCoverDescent

end TauCeti.FiniteEtaleScheme
