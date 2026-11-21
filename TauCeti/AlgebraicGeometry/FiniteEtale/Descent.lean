/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.RestrictSheaf
import Mathlib.CategoryTheory.Sites.LocalProperties
import TauCeti.AlgebraicGeometry.Descent.Fpqc
import TauCeti.AlgebraicGeometry.Sites.Etale.Localization

/-!
# Effective étale descent for representability of étale sheaves of sets

This file establishes effective étale descent for representability of étale sheaves of sets by
finite étale schemes along a quasi-compact surjective étale morphism.

Given a quasi-compact surjective étale morphism `p : S' ⟶ S` and an étale sheaf of sets `F` on `S`
whose inverse image `p.smallEtalePullback (Type u)` to `S'` is representable by a finite étale
`S'`-scheme `X`, the sheaf isomorphism induces a descent datum on `X` relative to `p`. Effective
fpqc descent for finite étale schemes
(`TauCeti.DescentDatum.exists_isFinite_etale_baseChange_hom_isIso_of_quasiCompact`) descends `X`
to a finite étale `S`-scheme `X₀`, and the sheaf condition along the surjective étale quotient map
`X ⟶ X₀` descends the tautological section to a sheaf morphism `(toSheaf S).obj X₀ ⟶ F` that is
an isomorphism by étale locality (`CategoryTheory.Sheaf.isIso_of_coversTop`).

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

variable {S S' : Scheme.{u}}

/-- A sheaf of types on the small étale site of `S` satisfies the sheaf condition for any single
morphism `f : U ⟶ V` in `S.Etale` whose underlying morphism of schemes is surjective. -/
private lemma isSheafFor_singleton_of_surjective {S : Scheme.{u}}
    (F : Sheaf (Scheme.smallEtaleTopology S) (Type u))
    {U V : S.Etale} (f : U ⟶ V) [Surjective f.left] :
    Presieve.IsSheafFor F.obj (.singleton f) := by
  rw [Presieve.isSheafFor_iff_generate]
  refine (isSheaf_iff_isSheaf_of_type _ _).mp F.property _
    ((Scheme.mem_smallEtaleTopology_iff _).mpr fun x ↦ ?_)
  obtain ⟨u, hu⟩ := f.left.surjective x
  exact ⟨U, f, u, Sieve.le_generate (.singleton f) _ _ (.mk), hu⟩

/-- Any isomorphism of sheaves of sets is injective on every section set. -/
private lemma iso_app_injective {G F : Sheaf (Scheme.smallEtaleTopology S') (Type u)}
    (e : G ≅ F) (U : S'.Etaleᵒᵖ) : Function.Injective (e.hom.hom.app U) :=
  ((isIso_iff_bijective _).mp
    ((NatTrans.isIso_iff_isIso_app e.hom.hom).mp
      ((sheafToPresheaf _ _).map_isIso e.hom) U)).injective

/-- Lift a morphism `f : W.left ⟶ X.obj.left` over `S` to a morphism
`W ⟶ p.smallEtaleMap.obj ((toEtale S').obj X)` in `S.Etale`. -/
private noncomputable def homToBase (p : S' ⟶ S) [Etale p] (X : FiniteEtaleScheme S') {W : S.Etale}
    (f : W.left ⟶ X.obj.left) (hf : f ≫ X.obj.hom ≫ p = W.hom) :
    W ⟶ p.smallEtaleMap.obj ((toEtale S').obj X) :=
  MorphismProperty.Over.homMk f hf

/-- The second projection `S' ×_S X ⟶ X` as a morphism in `S.Etale`. -/
private noncomputable def actSnd (p : S' ⟶ S) [Etale p] (X : FiniteEtaleScheme S') :
    p.smallEtaleMap.obj (Scheme.Etale.mk (Limits.pullback.fst p (X.obj.hom ≫ p))) ⟶
      p.smallEtaleMap.obj ((toEtale S').obj X) :=
  homToBase p X (Limits.pullback.snd p (X.obj.hom ≫ p)) Limits.pullback.condition.symm

/-- The action morphism in `S'.Etale` induced by
`e : (Scheme.smallEtaleTopology S').yoneda.obj ((toEtale S').obj X) ≅ ...`. -/
private noncomputable def actEtale {p : S' ⟶ S} [Etale p] {X : FiniteEtaleScheme S'}
    {F : Sheaf (Scheme.smallEtaleTopology S) (Type u)}
    (e : (Scheme.smallEtaleTopology S').yoneda.obj ((toEtale S').obj X) ≅
      (p.smallEtaleMap.sheafPushforwardContinuous (Type u)
        (Scheme.smallEtaleTopology S') (Scheme.smallEtaleTopology S)).obj F) :
    Scheme.Etale.mk (Limits.pullback.fst p (X.obj.hom ≫ p)) ⟶ (toEtale S').obj X :=
  e.inv.hom.app (op (Scheme.Etale.mk (Limits.pullback.fst p (X.obj.hom ≫ p))))
    (F.obj.map (actSnd p X).op ((Scheme.smallEtaleTopology S').yonedaEquiv e.hom))

/-- The underlying scheme morphism `S' ×_S X ⟶ X` of the descent action. -/
private noncomputable def actMap {p : S' ⟶ S} [Etale p] {X : FiniteEtaleScheme S'}
    {F : Sheaf (Scheme.smallEtaleTopology S) (Type u)}
    (e : (Scheme.smallEtaleTopology S').yoneda.obj ((toEtale S').obj X) ≅
      (p.smallEtaleMap.sheafPushforwardContinuous (Type u)
        (Scheme.smallEtaleTopology S') (Scheme.smallEtaleTopology S)).obj F) :
    Limits.pullback p (X.obj.hom ≫ p) ⟶ X.obj.left :=
  (actEtale e).left

@[reassoc]
private lemma actMap_hom {p : S' ⟶ S} [Etale p] {X : FiniteEtaleScheme S'}
    {F : Sheaf (Scheme.smallEtaleTopology S) (Type u)}
    (e : (Scheme.smallEtaleTopology S').yoneda.obj ((toEtale S').obj X) ≅
      (p.smallEtaleMap.sheafPushforwardContinuous (Type u)
        (Scheme.smallEtaleTopology S') (Scheme.smallEtaleTopology S)).obj F) :
    actMap e ≫ X.obj.hom = Limits.pullback.fst p (X.obj.hom ≫ p) :=
  MorphismProperty.Over.w (actEtale e)

/-- If `u : W.left ⟶ S' ×_S X` lifts `a` via `actMap e` and `b` via `pullback.snd`, then pulling
back `(Scheme.smallEtaleTopology S').yonedaEquiv e.hom` along `a` and `b` gives the same
section. -/
private lemma map_yonedaEquiv_eq_of_lift {p : S' ⟶ S} [Etale p] {X : FiniteEtaleScheme S'}
    {F : Sheaf (Scheme.smallEtaleTopology S) (Type u)}
    (e : (Scheme.smallEtaleTopology S').yoneda.obj ((toEtale S').obj X) ≅
      (p.smallEtaleMap.sheafPushforwardContinuous (Type u)
        (Scheme.smallEtaleTopology S') (Scheme.smallEtaleTopology S)).obj F)
    {W : S.Etale} {a b : W ⟶ p.smallEtaleMap.obj ((toEtale S').obj X)}
    (u : W.left ⟶ Limits.pullback p (X.obj.hom ≫ p))
    (ha : u ≫ actMap e = a.left) (hb : u ≫ Limits.pullback.snd p (X.obj.hom ≫ p) = b.left) :
    F.obj.map a.op ((Scheme.smallEtaleTopology S').yonedaEquiv e.hom) =
      F.obj.map b.op ((Scheme.smallEtaleTopology S').yonedaEquiv e.hom) := by
  let UP : S'.Etale := Scheme.Etale.mk (Limits.pullback.fst p (X.obj.hom ≫ p))
  have hu : u ≫ Limits.pullback.fst p (X.obj.hom ≫ p) ≫ p = W.hom :=
    (congrArg (u ≫ ·) (actMap_hom_assoc e p).symm).trans
      ((Category.assoc u (actMap e) (X.obj.hom ≫ p)).symm.trans
        ((congrArg (· ≫ X.obj.hom ≫ p) ha).trans (MorphismProperty.Over.w a)))
  let u' : W ⟶ p.smallEtaleMap.obj UP := MorphismProperty.Over.homMk u hu
  have h1 : u' ≫ p.smallEtaleMap.map (actEtale e) = a := MorphismProperty.Over.Hom.ext ha
  have h2 : u' ≫ actSnd p X = b := MorphismProperty.Over.Hom.ext hb
  have hact : F.obj.map (p.smallEtaleMap.map (actEtale e)).op
        ((Scheme.smallEtaleTopology S').yonedaEquiv e.hom) =
      F.obj.map (actSnd p X).op ((Scheme.smallEtaleTopology S').yonedaEquiv e.hom) :=
    ((Scheme.smallEtaleTopology S').map_yonedaEquiv e.hom (actEtale e)).trans <|
      ConcreteCategory.congr_hom
        (congrArg (fun η ↦ η.hom.app (op UP)) e.inv_hom_id)
        (F.obj.map (actSnd p X).op ((Scheme.smallEtaleTopology S').yonedaEquiv e.hom))
  exact (congrArg (fun k ↦ F.obj.map k.op _) h1.symm).trans <|
    (Functor.map_comp_apply F.obj (p.smallEtaleMap.map (actEtale e)).op u'.op _).trans <|
      (congrArg (F.obj.map u'.op) hact).trans <|
        (Functor.map_comp_apply F.obj (actSnd p X).op u'.op _).symm.trans
          (congrArg (fun k ↦ F.obj.map k.op _) h2)

/-- Unit law for the descent datum attached to `e`. -/
private lemma descentDatumOfIso_lift_act {p : S' ⟶ S} [Etale p] {X : FiniteEtaleScheme S'}
    {F : Sheaf (Scheme.smallEtaleTopology S) (Type u)}
    (e : (Scheme.smallEtaleTopology S').yoneda.obj ((toEtale S').obj X) ≅
      (p.smallEtaleMap.sheafPushforwardContinuous (Type u)
        (Scheme.smallEtaleTopology S') (Scheme.smallEtaleTopology S)).obj F) :
    Limits.pullback.lift X.obj.hom (𝟙 X.obj.left) (by simp) ≫ actMap e = 𝟙 X.obj.left := by
  -- Build the endomorphism `f₁` of `(toEtale S').obj X` given by the unit composite, and show
  -- `f₁ = 𝟙 _` by injectivity of `e.hom` on sections over `X`.
  let ι : X.obj.left ⟶ Limits.pullback p (X.obj.hom ≫ p) :=
    Limits.pullback.lift X.obj.hom (𝟙 X.obj.left) (by simp)
  let f₁ : (toEtale S').obj X ⟶ (toEtale S').obj X :=
    MorphismProperty.Over.homMk (ι ≫ actMap e)
      ((Category.assoc ι (actMap e) X.obj.hom).trans
        ((congrArg (ι ≫ ·) (actMap_hom e)).trans (Limits.pullback.lift_fst _ _ _)))
  have hfeq : f₁ = 𝟙 ((toEtale S').obj X) := iso_app_injective e (op ((toEtale S').obj X)) <| by
    rw [← (Scheme.smallEtaleTopology S').map_yonedaEquiv e.hom f₁,
      ← (Scheme.smallEtaleTopology S').map_yonedaEquiv e.hom (𝟙 _)]
    exact map_yonedaEquiv_eq_of_lift e ι rfl (Limits.pullback.lift_snd _ _ _)
  exact congrArg (fun k : (toEtale S').obj X ⟶ (toEtale S').obj X ↦ k.left) hfeq

/-- Associativity (cocycle) law for the descent datum attached to `e`. -/
private lemma descentDatumOfIso_act_assoc {p : S' ⟶ S} [Etale p] {X : FiniteEtaleScheme S'}
    {F : Sheaf (Scheme.smallEtaleTopology S) (Type u)}
    (e : (Scheme.smallEtaleTopology S').yoneda.obj ((toEtale S').obj X) ≅
      (p.smallEtaleMap.sheafPushforwardContinuous (Type u)
        (Scheme.smallEtaleTopology S') (Scheme.smallEtaleTopology S)).obj F) :
    Limits.pullback.lift (Limits.pullback.fst p (Limits.pullback.fst p (X.obj.hom ≫ p) ≫ p))
        (Limits.pullback.snd p (Limits.pullback.fst p (X.obj.hom ≫ p) ≫ p) ≫ actMap e)
        (by rw [Category.assoc, actMap_hom_assoc]; exact Limits.pullback.condition) ≫ actMap e =
      Limits.pullback.lift (Limits.pullback.fst p (Limits.pullback.fst p (X.obj.hom ≫ p) ≫ p))
        (Limits.pullback.snd p (Limits.pullback.fst p (X.obj.hom ≫ p) ≫ p) ≫
          Limits.pullback.snd p (X.obj.hom ≫ p))
        (by
          rw [Category.assoc, ← Limits.pullback.condition (f := p) (g := X.obj.hom ≫ p)]
          exact Limits.pullback.condition) ≫ actMap e := by
  -- Compare the two triple-overlap morphisms `g₁, g₂ : S' ×_S S' ×_S X ⟶ X` via `e.hom`: three
  -- steps of `map_yonedaEquiv_eq_of_lift` chase `q₁ ≫ act → m₁ → m₂ → q₂ ≫ act`.
  let Q := Limits.pullback p (Limits.pullback.fst p (X.obj.hom ≫ p) ≫ p)
  let UQ : S'.Etale :=
    Scheme.Etale.mk (Limits.pullback.fst p (Limits.pullback.fst p (X.obj.hom ≫ p) ≫ p))
  let W : S.Etale := p.smallEtaleMap.obj UQ
  let sndQ : Q ⟶ Limits.pullback p (X.obj.hom ≫ p) := Limits.pullback.snd p _
  let q₁ : Q ⟶ Limits.pullback p (X.obj.hom ≫ p) :=
    Limits.pullback.lift (Limits.pullback.fst p _) (sndQ ≫ actMap e)
      (by rw [Category.assoc, actMap_hom_assoc]; exact Limits.pullback.condition)
  let q₂ : Q ⟶ Limits.pullback p (X.obj.hom ≫ p) :=
    Limits.pullback.lift (Limits.pullback.fst p _) (sndQ ≫ Limits.pullback.snd p (X.obj.hom ≫ p))
      (by
        rw [Category.assoc, ← Limits.pullback.condition (f := p) (g := X.obj.hom ≫ p)]
        exact Limits.pullback.condition)
  let g₁ : UQ ⟶ (toEtale S').obj X := MorphismProperty.Over.homMk (q₁ ≫ actMap e)
    ((Category.assoc q₁ (actMap e) X.obj.hom).trans
      ((congrArg (q₁ ≫ ·) (actMap_hom e)).trans (Limits.pullback.lift_fst _ _ _)))
  let g₂ : UQ ⟶ (toEtale S').obj X := MorphismProperty.Over.homMk (q₂ ≫ actMap e)
    ((Category.assoc q₂ (actMap e) X.obj.hom).trans
      ((congrArg (q₂ ≫ ·) (actMap_hom e)).trans (Limits.pullback.lift_fst _ _ _)))
  have hsnd : sndQ ≫ Limits.pullback.fst p (X.obj.hom ≫ p) ≫ p = W.hom :=
    Limits.pullback.condition.symm
  let m₁ : W ⟶ p.smallEtaleMap.obj ((toEtale S').obj X) :=
    homToBase p X (sndQ ≫ actMap e)
      (((Category.assoc sndQ (actMap e) (X.obj.hom ≫ p)).trans
        (congrArg (sndQ ≫ ·) (actMap_hom_assoc e p))).trans hsnd)
  let m₂ : W ⟶ p.smallEtaleMap.obj ((toEtale S').obj X) :=
    homToBase p X (sndQ ≫ Limits.pullback.snd p (X.obj.hom ≫ p))
      (((Category.assoc sndQ (Limits.pullback.snd p _) (X.obj.hom ≫ p)).trans
        (congrArg (sndQ ≫ ·) Limits.pullback.condition.symm)).trans hsnd)
  have hgeq : g₁ = g₂ := iso_app_injective e (op UQ) <| by
    rw [← (Scheme.smallEtaleTopology S').map_yonedaEquiv e.hom g₁,
      ← (Scheme.smallEtaleTopology S').map_yonedaEquiv e.hom g₂]
    exact (map_yonedaEquiv_eq_of_lift e (b := m₁) q₁ rfl (Limits.pullback.lift_snd _ _ _)).trans <|
      (map_yonedaEquiv_eq_of_lift e (a := m₁) (b := m₂) sndQ rfl rfl).trans
        (map_yonedaEquiv_eq_of_lift e (b := m₂) q₂ rfl (Limits.pullback.lift_snd _ _ _)).symm
  exact congrArg (fun k : UQ ⟶ (toEtale S').obj X ↦ k.left) hgeq

/-- An isomorphism `(Scheme.smallEtaleTopology S').yoneda.obj ((toEtale S').obj X) ≅ ...`
induces a descent datum on `X` relative to `p`. -/
private noncomputable def descentDatumOfIso {p : S' ⟶ S} [Etale p] {X : FiniteEtaleScheme S'}
    {F : Sheaf (Scheme.smallEtaleTopology S) (Type u)}
    (e : (Scheme.smallEtaleTopology S').yoneda.obj ((toEtale S').obj X) ≅
      (p.smallEtaleMap.sheafPushforwardContinuous (Type u)
        (Scheme.smallEtaleTopology S') (Scheme.smallEtaleTopology S)).obj F) :
    DescentDatum p X.obj where
  act := actMap e
  act_hom := actMap_hom e
  lift_act := descentDatumOfIso_lift_act e
  act_assoc := descentDatumOfIso_act_assoc e

/-- Inverse action compatibility for an isomorphism `f : baseChange p X₀ ≅ D` of descent data. -/
private lemma descentDatum_inv_act_compat {p : S' ⟶ S} {X₀ : Over S} {X : Over S'}
    {D : DescentDatum p X} (f : (DescentDatum.baseChange p X₀).Hom D) [IsIso f.hom] :
    D.act ≫ (asIso f.hom).inv.left =
      Limits.pullback.map p (X.hom ≫ p) p (((Over.pullback p).obj X₀).hom ≫ p) (𝟙 S')
        (asIso f.hom).inv.left (𝟙 S) (by simp)
        (by rw [Category.comp_id, ← Category.assoc, (asIso f.hom).inv.w]) ≫
        (DescentDatum.baseChange p X₀).act := by
  let eBC := asIso f.hom
  rw [← cancel_mono eBC.hom.left, Category.assoc, Category.assoc]
  have hinv : eBC.inv.left ≫ eBC.hom.left = 𝟙 _ := congrArg CommaMorphism.left eBC.inv_hom_id
  have hf_act : (DescentDatum.baseChange p X₀).act ≫ eBC.hom.left =
      Limits.pullback.map p (((Over.pullback p).obj X₀).hom ≫ p) p (X.hom ≫ p)
        (𝟙 S') eBC.hom.left (𝟙 S) (by simp) (by simp) ≫ D.act := f.map_act.symm
  have hmap_id : Limits.pullback.map p (X.hom ≫ p) p (((Over.pullback p).obj X₀).hom ≫ p)
        (𝟙 S') eBC.inv.left (𝟙 S) (by simp)
        (by rw [Category.comp_id, ← Category.assoc, eBC.inv.w]) ≫
      Limits.pullback.map p (((Over.pullback p).obj X₀).hom ≫ p) p (X.hom ≫ p)
        (𝟙 S') eBC.hom.left (𝟙 S) (by simp) (by simp) = 𝟙 _ := by
    refine Limits.pullback.hom_ext ?_ ?_ <;> simp [hinv]
  rw [hinv, Category.comp_id, hf_act, ← Category.assoc, hmap_id, Category.id_comp]

/-- The quotient map `X ⟶ X₀` in `S.Etale` induced by an isomorphism of descent data
`f : baseChange p X₀ ≅ descentDatumOfIso e`. -/
private noncomputable def descentQuotientHom {p : S' ⟶ S} [Etale p] {X : FiniteEtaleScheme S'}
    {F : Sheaf (Scheme.smallEtaleTopology S) (Type u)}
    (e : (Scheme.smallEtaleTopology S').yoneda.obj ((toEtale S').obj X) ≅
      (p.smallEtaleMap.sheafPushforwardContinuous (Type u)
        (Scheme.smallEtaleTopology S') (Scheme.smallEtaleTopology S)).obj F)
    (X₀ : FiniteEtaleScheme S) (f : (DescentDatum.baseChange p X₀.obj).Hom (descentDatumOfIso e))
    [IsIso f.hom] :
    p.smallEtaleMap.obj ((toEtale S').obj X) ⟶ (toEtale S).obj X₀ :=
  MorphismProperty.Over.homMk ((asIso f.hom).inv.left ≫ Limits.pullback.fst X₀.obj.hom p)
    ((Category.assoc (asIso f.hom).inv.left (Limits.pullback.fst X₀.obj.hom p) X₀.obj.hom).trans
      ((congrArg ((asIso f.hom).inv.left ≫ ·) Limits.pullback.condition).trans
        ((Category.assoc (asIso f.hom).inv.left (Limits.pullback.snd X₀.obj.hom p) p).symm.trans
          (congrArg (· ≫ p) (asIso f.hom).inv.w))))

/-- Descent compatibility of `(Scheme.smallEtaleTopology S').yonedaEquiv e.hom` along
`descentQuotientHom e X₀ f`. -/
private lemma descent_yonedaEquiv_compat {p : S' ⟶ S} [Etale p] {X : FiniteEtaleScheme S'}
    {F : Sheaf (Scheme.smallEtaleTopology S) (Type u)}
    (e : (Scheme.smallEtaleTopology S').yoneda.obj ((toEtale S').obj X) ≅
      (p.smallEtaleMap.sheafPushforwardContinuous (Type u)
        (Scheme.smallEtaleTopology S') (Scheme.smallEtaleTopology S)).obj F)
    (X₀ : FiniteEtaleScheme S) (f : (DescentDatum.baseChange p X₀.obj).Hom (descentDatumOfIso e))
    [IsIso f.hom] {W : S.Etale} (a₁ a₂ : W ⟶ p.smallEtaleMap.obj ((toEtale S').obj X))
    (hcomm : a₁ ≫ descentQuotientHom e X₀ f = a₂ ≫ descentQuotientHom e X₀ f) :
    F.obj.map a₁.op ((Scheme.smallEtaleTopology S').yonedaEquiv e.hom) =
      F.obj.map a₂.op ((Scheme.smallEtaleTopology S').yonedaEquiv e.hom) := by
  -- Lift `(a₁.left ≫ X.obj.hom, a₂.left)` to `u : W.left ⟶ S' ×_S X`. Because `a₁, a₂` agree
  -- after `descentQuotientHom`, inverse action compatibility gives `u ≫ actMap e = a₁.left`, and
  -- `map_yonedaEquiv_eq_of_lift` equates pulling back along `a₁` and `a₂`.
  let eBC := asIso f.hom
  let x₁ : W.left ⟶ X.obj.left := a₁.left
  let x₂ : W.left ⟶ X.obj.left := a₂.left
  have hx₁ : x₁ ≫ X.obj.hom ≫ p = W.hom := MorphismProperty.Over.w a₁
  have hx₂ : x₂ ≫ X.obj.hom ≫ p = W.hom := MorphismProperty.Over.w a₂
  have hπ₁ : x₁ ≫ eBC.inv.left ≫ Limits.pullback.fst X₀.obj.hom p =
      x₂ ≫ eBC.inv.left ≫ Limits.pullback.fst X₀.obj.hom p :=
    congrArg (fun k : W ⟶ (toEtale S).obj X₀ ↦ k.left) hcomm
  let u : W.left ⟶ Limits.pullback p (X.obj.hom ≫ p) :=
    Limits.pullback.lift (x₁ ≫ X.obj.hom) x₂ (by rw [Category.assoc, hx₁, hx₂])
  have hu_act : u ≫ actMap e = x₁ := by
    have hact_eq : actMap e ≫ eBC.inv.left = _ := descentDatum_inv_act_compat f
    rw [← cancel_mono eBC.inv.left, Category.assoc, hact_eq]
    refine Limits.pullback.hom_ext ?_ ?_
    · simpa only [Category.assoc, DescentDatum.baseChange_act_fst, Limits.pullback.map,
        Limits.pullback.lift_snd_assoc, u] using hπ₁.symm
    · simpa only [Category.assoc, DescentDatum.baseChange_act_snd, Limits.pullback.map,
        Limits.pullback.lift_fst, Category.comp_id, Over.pullback_obj_hom, u] using
          (congrArg (x₁ ≫ ·) eBC.inv.w).symm
  exact map_yonedaEquiv_eq_of_lift e u hu_act (Limits.pullback.lift_snd _ _ _)

/-- Effective descent for representability of étale sheaves by finite étale schemes along a
quasi-compact surjective étale morphism `p : S' ⟶ S`. -/
theorem exists_toSheaf_iso_of_smallEtalePullback_iso (p : S' ⟶ S) [Etale p] [Surjective p]
    [QuasiCompact p] (X : FiniteEtaleScheme S')
    (F : Sheaf (Scheme.smallEtaleTopology S) (Type u))
    (e : (toSheaf S').obj X ≅ (p.smallEtalePullback (Type u)).obj F) :
    ∃ X₀ : FiniteEtaleScheme S, Nonempty ((toSheaf S).obj X₀ ≅ F) := by
  let e' : (Scheme.smallEtaleTopology S').yoneda.obj ((toEtale S').obj X) ≅
      (p.smallEtaleMap.sheafPushforwardContinuous (Type u)
        (Scheme.smallEtaleTopology S') (Scheme.smallEtaleTopology S)).obj F :=
    e ≪≫ (p.smallEtalePullbackIsoMapPushforward (Type u)).app F
  obtain ⟨X₀_over, hfin, het, f, hf⟩ :=
    (descentDatumOfIso e').exists_isFinite_etale_baseChange_hom_isIso_of_quasiCompact
  let X₀ : FiniteEtaleScheme S := ⟨X₀_over, (finiteEtaleSchemeProperty_iff _).mpr ⟨hfin, het⟩⟩
  let eBC : (Over.pullback p).obj X₀.obj ≅ X.obj := asIso f.hom
  let q := descentQuotientHom e' X₀ f
  -- The quotient morphism `q` is surjective, so the tautological section descends to a section
  -- `t₀` over `X₀`, yielding `φ = yonedaEquiv.symm t₀ : (toSheaf S).obj X₀ ⟶ F`.
  have : Surjective q.left := inferInstanceAs
    (Surjective (eBC.inv.left ≫ Limits.pullback.fst X₀.obj.hom p))
  have hsheaf := Presieve.isSheafFor_singleton.mp (isSheafFor_singleton_of_surjective F q)
  obtain ⟨t₀, ht₀, -⟩ := hsheaf ((Scheme.smallEtaleTopology S').yonedaEquiv e'.hom)
    (fun a₁ a₂ hcomm ↦ descent_yonedaEquiv_compat e' X₀ f a₁ a₂ hcomm)
  let φ : (toSheaf S).obj X₀ ⟶ F := (Scheme.smallEtaleTopology S).yonedaEquiv.symm t₀
  let P := p.smallEtaleMap.sheafPushforwardContinuous (Type u)
    (Scheme.smallEtaleTopology S') (Scheme.smallEtaleTopology S)
  -- Compare `(P.map φ)` precomposed with `toSheafCompSmallEtaleMapPushforwardIso` to `e'`.
  have hres : IsIso (P.map φ) := by
    let eFE : (pullback p).obj X₀ ≅ X := ObjectProperty.isoMk _ eBC
    let V₀ : S'.Etale := (toEtale S').obj ((pullback p).obj X₀)
    let θ : (Scheme.smallEtaleTopology S').yoneda.obj V₀ ≅ P.obj ((toSheaf S).obj X₀) :=
      ((toSheafCompSmallEtaleMapPushforwardIso p).app X₀).symm
    have heq : θ.hom ≫ P.map φ =
        (Scheme.smallEtaleTopology S').yoneda.map ((toEtale S').map eFE.hom) ≫ e'.hom := by
      apply (Scheme.smallEtaleTopology S').yonedaEquiv.injective
      have hL : (Scheme.smallEtaleTopology S').yonedaEquiv (θ.hom ≫ P.map φ) =
          F.obj.map ((restrictSectionEquiv p X₀ V₀).symm (𝟙 V₀)).op t₀ :=
        ((Scheme.smallEtaleTopology S').yonedaEquiv_comp θ.hom (P.map φ)).trans <|
          (congrArg ((P.map φ).hom.app (op V₀))
            (((Scheme.smallEtaleTopology S').yonedaEquiv_apply θ.hom).trans
              (ConcreteCategory.congr_hom
                (toSheafCompSmallEtaleMapPushforwardIso_inv_app_hom_app p X₀ V₀) (𝟙 V₀)))).trans
            ((Scheme.smallEtaleTopology S).yonedaEquiv_symm_app_apply t₀ _ _)
      have hR : (Scheme.smallEtaleTopology S').yonedaEquiv
            ((Scheme.smallEtaleTopology S').yoneda.map ((toEtale S').map eFE.hom) ≫ e'.hom) =
          F.obj.map (p.smallEtaleMap.map ((toEtale S').map eFE.hom) ≫ q).op t₀ := by
        rw [← (Scheme.smallEtaleTopology S').yonedaEquiv_naturality
          e'.hom ((toEtale S').map eFE.hom)]
        exact (by rw [← ht₀, ← Functor.map_comp_apply, ← op_comp] :
          F.obj.map (p.smallEtaleMap.map ((toEtale S').map eFE.hom)).op
            ((Scheme.smallEtaleTopology S').yonedaEquiv e'.hom) = _)
      refine hL.trans ((congrArg (fun k ↦ F.obj.map (Quiver.Hom.op k) t₀) ?_).trans hR.symm)
      apply MorphismProperty.Over.Hom.ext
      rw [restrictSectionEquiv_symm_apply_left]
      have hcancel : eBC.hom.left ≫ eBC.inv.left = 𝟙 _ :=
        congrArg CommaMorphism.left eBC.hom_inv_id
      exact (congrArg (· ≫ Limits.pullback.fst X₀.obj.hom p) hcancel.symm).trans
        (Category.assoc _ _ _)
    have : IsIso (θ.hom ≫ P.map φ) := heq ▸ inferInstance
    exact IsIso.of_isIso_comp_left θ.hom (P.map φ)
  -- Conclude by étale locality on `S.Etale` via `Etale.mk p`.
  have hcov : (Scheme.smallEtaleTopology S).CoversTop (fun _ : Unit ↦ Scheme.Etale.mk p) :=
    (Scheme.coversTop_smallEtaleTopology_iff _).mpr fun s ↦ ⟨(), p.surjective s⟩
  have : IsIso φ := Sheaf.isIso_of_coversTop hcov fun _ ↦ by
    let U : S.Etale := Scheme.Etale.mk p
    let α := U.overPullbackCompOverSheafEquivIso (Type u)
    have : IsIso ((U.overSheafEquiv (Type u)).functor.map
        (((Scheme.smallEtaleTopology S).overPullback (Type u) U).map φ)) :=
      (NatIso.isIso_map_iff α φ).mpr hres
    exact isIso_of_reflects_iso _ (U.overSheafEquiv (Type u)).functor
  exact ⟨X₀, ⟨asIso φ⟩⟩

end SingleCoverDescent

end TauCeti.FiniteEtaleScheme
