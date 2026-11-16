/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.RestrictSheaf
import TauCeti.AlgebraicGeometry.Descent.Fpqc

/-!
# Effective étale descent for representability of étale sheaves of sets

This file establishes étale locality of isomorphisms between étale sheaves of sets and effective
étale descent for representability by finite étale schemes along a quasi-compact surjective étale
morphism.

Given a quasi-compact surjective étale morphism `p : S' ⟶ S` and an étale sheaf of sets `F` on `S`
whose restriction to `S'` is representable by a finite étale `S'`-scheme `X`, the sheaf isomorphism
induces a descent datum on `X` relative to `p`. Effective fpqc descent for finite étale schemes
(`TauCeti.DescentDatum.exists_isFinite_etale_baseChange_hom_isIso_of_quasiCompact`) descends `X`
to a finite étale `S`-scheme `X₀`, and the sheaf condition descends the tautological section to an
isomorphism `(toSheaf S).obj X₀ ≅ F` (`exists_toSheaf_iso_of_restrictSheaf_iso`).

## Main definitions

* `TauCeti.FiniteEtaleScheme.yonedaSheafHom`: the Yoneda sheaf morphism `(toSheaf S).obj X ⟶ F`
  associated to a section of `F` over `(toEtale S).obj X`.
* `TauCeti.FiniteEtaleScheme.tautSection`: the tautological section of `F` over `X` induced by an
  isomorphism `(toSheaf S').obj X ≅ (restrictSheaf p).obj F`.

## Main results

* `TauCeti.FiniteEtaleScheme.isIso_of_forall_isIso_restrictSheaf`: being an isomorphism of étale
  sheaves of sets is étale-local.
* `TauCeti.FiniteEtaleScheme.exists_toSheaf_iso_of_restrictSheaf_iso`: representability of an étale
  sheaf of sets by a finite étale scheme satisfies effective descent along any quasi-compact
  surjective étale morphism.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IX, §2.
* The Stacks Project, [Tag 0245](https://stacks.math.columbia.edu/tag/0245).
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

section EtaleLocality

variable {S : Scheme.{u}}

/-- Construct a morphism `etaleMk f ⟶ (toEtale S).obj Y` from `h : X ⟶ Y.obj.left` over `S`. -/
private noncomputable def etaleMkToFE {S X : Scheme.{u}} {f : X ⟶ S} [Etale f]
    {Y : FiniteEtaleScheme S} (h : X ⟶ Y.obj.left) (w : h ≫ Y.obj.hom = f) :
    etaleMk f ⟶ (toEtale S).obj Y :=
  etaleHomMk ((etaleMkObjIso f).hom ≫ h ≫ (toEtaleObjIso Y).inv) (by
    rw [Category.assoc, Category.assoc, toEtaleObjIso_inv_comp, w, etaleMkObjIso_hom_comp])

private lemma etaleMap_etaleMkToFE {S X : Scheme.{u}} {f : X ⟶ S} [Etale f]
    {Y : FiniteEtaleScheme S} (h : X ⟶ Y.obj.left) (w : h ≫ Y.obj.hom = f) :
    etaleMap (etaleMkToFE h w) = (etaleMkObjIso f).hom ≫ h ≫ (toEtaleObjIso Y).inv :=
  etaleMap_etaleHomMk _ _

/-- The Yoneda morphism of sheaves attached to a section of `F` over `(toEtale S).obj X`. -/
noncomputable def yonedaSheafHom {F : Sheaf (Scheme.smallEtaleTopology S) (Type u)}
    {X : FiniteEtaleScheme S} (t : F.obj.obj (op ((toEtale S).obj X))) :
    (toSheaf S).obj X ⟶ F :=
  ObjectProperty.homMk
    { app V := TypeCat.ofHom fun g ↦ F.obj.map g.op t
      naturality {V W} a := by
        ext g
        let g' : V.unop ⟶ (toEtale S).obj X := g
        change F.obj.map (a.unop ≫ g').op t = F.obj.map a (F.obj.map g'.op t)
        rw [op_comp, Functor.map_comp_apply]
        rfl }

@[simp]
lemma yonedaSheafHom_app {F : Sheaf (Scheme.smallEtaleTopology S) (Type u)}
    {X : FiniteEtaleScheme S} (t : F.obj.obj (op ((toEtale S).obj X)))
    {V : S.Etale} (g : V ⟶ (toEtale S).obj X) :
    (yonedaSheafHom t).hom.app (op V) g = F.obj.map g.op t :=
  (rfl)

/-- Two morphisms from `(toSheaf S).obj X` to an étale sheaf `F` agree if and only if they send
`𝟙 ((toEtale S).obj X)` to the same section. -/
lemma yoneda_hom_ext {F : Sheaf (Scheme.smallEtaleTopology S) (Type u)}
    {X : FiniteEtaleScheme S} {φ ψ : (toSheaf S).obj X ⟶ F}
    (h : φ.hom.app (op ((toEtale S).obj X)) (𝟙 ((toEtale S).obj X)) =
      ψ.hom.app (op ((toEtale S).obj X)) (𝟙 ((toEtale S).obj X))) : φ = ψ := by
  ext U g
  let g' : U.unop ⟶ (toEtale S).obj X := g
  have h1 : φ.hom.app U g' = F.obj.map g'.op (φ.hom.app (op ((toEtale S).obj X)) (𝟙 _)) := by
    have hnat := ConcreteCategory.congr_hom (φ.hom.naturality g'.op) (𝟙 ((toEtale S).obj X))
    change φ.hom.app U (g' ≫ 𝟙 _) = _ at hnat
    rwa [Category.comp_id] at hnat
  have h2 : ψ.hom.app U g' = F.obj.map g'.op (ψ.hom.app (op ((toEtale S).obj X)) (𝟙 _)) := by
    have hnat := ConcreteCategory.congr_hom (ψ.hom.naturality g'.op) (𝟙 ((toEtale S).obj X))
    change ψ.hom.app U (g' ≫ 𝟙 _) = _ at hnat
    rwa [Category.comp_id] at hnat
  exact h1.trans ((congrArg (F.obj.map g'.op) h).trans h2.symm)

/-- Gluing along a single surjective morphism `f : U ⟶ V` in `S.Etale`. -/
private lemma isSheafFor_singleton_of_surjective
    (F : Sheaf (Scheme.smallEtaleTopology S) (Type u))
    {U V : S.Etale} (f : U ⟶ V) [Surjective (etaleMap f)] :
    Presieve.IsSheafFor F.obj (.singleton f) := by
  rw [Presieve.isSheafFor_iff_generate]
  have hcov : Sieve.generate (.singleton f) ∈ Scheme.smallEtaleTopology S V := by
    have heq : Sieve.generate (.singleton f) = Sieve.ofArrows (fun _ : Unit ↦ U) (fun _ ↦ f) := by
      ext W g
      constructor
      · rintro ⟨_, u, _, ⟨⟩, rfl⟩
        rw [Sieve.mem_ofArrows_iff]
        exact ⟨(), u, rfl⟩
      · intro hg
        rw [Sieve.mem_ofArrows_iff] at hg
        obtain ⟨_, u, rfl⟩ := hg
        exact ⟨U, u, f, .mk, rfl⟩
    rw [heq, ofArrows_mem_smallEtaleTopology_iff_etale]
    simp [Set.range_eq_univ.mpr (etaleMap f).surjective, Set.iUnion_const]
  exact (isSheaf_iff_isSheaf_of_type _ _).mp F.property _ hcov

/-- Pulling back a jointly surjective étale family to `U : S.Etale` gives a covering sieve of `U`.
-/
private lemma pullback_ofArrows_mem_smallEtaleTopology {ι : Type*} {T : ι → Scheme.{u}}
    (p : ∀ i, T i ⟶ S) [∀ i, Etale (p i)] (hsurj : ⋃ i, Set.range (p i) = .univ) (U : S.Etale) :
    Sieve.ofArrows
      (fun i ↦ etaleMk (etaleHom (etaleMk (Limits.pullback.snd (etaleHom U) (p i))) ≫ p i))
      (fun i ↦ etaleHomMk ((etaleMkObjIso _).hom ≫ (etaleMkObjIso _).hom ≫
        Limits.pullback.fst (etaleHom U) (p i)) (by
          rw [Category.assoc, Category.assoc, Limits.pullback.condition,
            etaleMkObjIso_hom_comp_assoc, etaleMkObjIso_hom_comp])) ∈
      Scheme.smallEtaleTopology S U := by
  rw [ofArrows_mem_smallEtaleTopology_iff_etale]
  ext u
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  obtain ⟨i, t, ht⟩ := Set.mem_iUnion.mp (hsurj.symm ▸ Set.mem_univ (etaleHom U u))
  obtain ⟨w, hw1, -⟩ := Scheme.Pullback.exists_preimage_pullback u t ht.symm
  let e1 := etaleMkObjIso (etaleHom (etaleMk (Limits.pullback.snd (etaleHom U) (p i))) ≫ p i)
  let e2 := etaleMkObjIso (Limits.pullback.snd (etaleHom U) (p i))
  refine ⟨i, e1.inv (e2.inv w), ?_⟩
  rw [etaleMap_etaleHomMk]
  change (Limits.pullback.fst (etaleHom U) (p i)) (e2.hom (e1.hom (e1.inv (e2.inv w)))) = u
  have h1 : e1.hom (e1.inv (e2.inv w)) = e2.inv w :=
    congrArg (fun k ↦ k (e2.inv w)) e1.inv_hom_id
  have h2 : e2.hom (e2.inv w) = w :=
    congrArg (fun k ↦ k w) e2.inv_hom_id
  rw [h1, h2, hw1]

/-- Helper for `isIso_of_forall_isIso_restrictSheaf`: injectivity of `φ` on every `U : S.Etale`
follows from bijectivity on pullbacks along a jointly surjective étale family. -/
private lemma app_injective_of_forall_isIso_restrictSheaf {ι : Type*} {T : ι → Scheme.{u}}
    (p : ∀ i, T i ⟶ S) [∀ i, Etale (p i)] (hsurj : ⋃ i, Set.range (p i) = .univ)
    {G F : Sheaf (Scheme.smallEtaleTopology S) (Type u)} (φ : G ⟶ F)
    (hφ : ∀ i, IsIso ((restrictSheaf (p i)).map φ)) (U : S.Etale) :
    Function.Injective (φ.hom.app (op U)) := by
  let Z (i : ι) : S.Etale :=
    etaleMk (etaleHom (etaleMk (Limits.pullback.snd (etaleHom U) (p i))) ≫ p i)
  let f (i : ι) : Z i ⟶ U :=
    etaleHomMk ((etaleMkObjIso _).hom ≫ (etaleMkObjIso _).hom ≫
      Limits.pullback.fst (etaleHom U) (p i)) (by
        rw [Category.assoc, Category.assoc, Limits.pullback.condition,
          etaleMkObjIso_hom_comp_assoc, etaleMkObjIso_hom_comp])
  have hG := (Presieve.isSheafFor_arrows_iff G.obj f).mp <|
    (Presieve.isSheafFor_iff_generate _).mpr <|
      (isSheaf_iff_isSheaf_of_type _ _).mp G.property _
        (pullback_ofArrows_mem_smallEtaleTopology p hsurj U)
  intro a b hab
  refine (hG (fun i ↦ G.obj.map (f i).op a) (Presieve.Arrows.toCompatible G.obj f a).2).unique
    (fun _ ↦ rfl) fun i ↦ ?_
  have : IsIso (((restrictSheaf (p i)).map φ).hom) :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ _).map ((restrictSheaf (p i)).map φ)))
  have : IsIso (φ.hom.app (op (Z i))) :=
    (NatTrans.isIso_iff_isIso_app ((restrictSheaf (p i)).map φ).hom).mp inferInstance
      (op (etaleMk (Limits.pullback.snd (etaleHom U) (p i))))
  have ha : φ.hom.app (op (Z i)) (G.obj.map (f i).op a) =
      F.obj.map (f i).op (φ.hom.app (op U) a) :=
    ConcreteCategory.congr_hom (φ.hom.naturality (f i).op) a
  have hb : φ.hom.app (op (Z i)) (G.obj.map (f i).op b) =
      F.obj.map (f i).op (φ.hom.app (op U) b) :=
    ConcreteCategory.congr_hom (φ.hom.naturality (f i).op) b
  exact ((isIso_iff_bijective (φ.hom.app (op (Z i)))).mp inferInstance).1
    (hb.trans ((congrArg (F.obj.map (f i).op) hab.symm).trans ha.symm))

/-- A morphism of étale sheaves of sets on `S` is an isomorphism if its restrictions along a
jointly surjective family of étale morphisms are isomorphisms. -/
theorem isIso_of_forall_isIso_restrictSheaf {ι : Type*} {T : ι → Scheme.{u}}
    (p : ∀ i, T i ⟶ S) [∀ i, Etale (p i)] (hsurj : ⋃ i, Set.range (p i) = .univ)
    {G F : Sheaf (Scheme.smallEtaleTopology S) (Type u)} (φ : G ⟶ F)
    (hφ : ∀ i, IsIso ((restrictSheaf (p i)).map φ)) : IsIso φ := by
  have hval : IsIso ((sheafToPresheaf _ _).map φ) := by
    refine (NatTrans.isIso_iff_isIso_app φ.hom).mpr fun U ↦ (isIso_iff_bijective _).mpr
      ⟨app_injective_of_forall_isIso_restrictSheaf p hsurj φ hφ U.unop, fun y ↦ ?_⟩
    let Z (i : ι) : S.Etale :=
      etaleMk (etaleHom (etaleMk (Limits.pullback.snd (etaleHom U.unop) (p i))) ≫ p i)
    let f (i : ι) : Z i ⟶ U.unop :=
      etaleHomMk ((etaleMkObjIso _).hom ≫ (etaleMkObjIso _).hom ≫
        Limits.pullback.fst (etaleHom U.unop) (p i)) (by
          rw [Category.assoc, Category.assoc, Limits.pullback.condition,
            etaleMkObjIso_hom_comp_assoc, etaleMkObjIso_hom_comp])
    have hcov := pullback_ofArrows_mem_smallEtaleTopology p hsurj U.unop
    have hbij (i : ι) : Function.Bijective (φ.hom.app (op (Z i))) := by
      have : IsIso (((restrictSheaf (p i)).map φ).hom) :=
        inferInstanceAs (IsIso ((sheafToPresheaf _ _).map ((restrictSheaf (p i)).map φ)))
      have : IsIso (φ.hom.app (op (Z i))) :=
        (NatTrans.isIso_iff_isIso_app ((restrictSheaf (p i)).map φ).hom).mp inferInstance
          (op (etaleMk (Limits.pullback.snd (etaleHom U.unop) (p i))))
      exact (isIso_iff_bijective _).mp inferInstance
    choose x hx using fun i ↦ (hbij i).2 (F.obj.map (f i).op y)
    have hG := (Presieve.isSheafFor_arrows_iff G.obj f).mp <|
      (Presieve.isSheafFor_iff_generate _).mpr <|
        (isSheaf_iff_isSheaf_of_type _ _).mp G.property _ hcov
    have hF := (Presieve.isSheafFor_arrows_iff F.obj f).mp <|
      (Presieve.isSheafFor_iff_generate _).mpr <|
        (isSheaf_iff_isSheaf_of_type _ _).mp F.property _ hcov
    have hcompat : Presieve.Arrows.Compatible G.obj f x := by
      intro i j W g₁ g₂ hcomm
      apply app_injective_of_forall_isIso_restrictSheaf p hsurj φ hφ W
      have h1 : φ.hom.app (op W) (G.obj.map g₁.op (x i)) =
          F.obj.map g₁.op (φ.hom.app (op (Z i)) (x i)) :=
        ConcreteCategory.congr_hom (φ.hom.naturality g₁.op) (x i)
      have h2 : φ.hom.app (op W) (G.obj.map g₂.op (x j)) =
          F.obj.map g₂.op (φ.hom.app (op (Z j)) (x j)) :=
        ConcreteCategory.congr_hom (φ.hom.naturality g₂.op) (x j)
      rw [h1, h2, hx i, hx j, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
        ← op_comp, ← op_comp, hcomm]
    obtain ⟨t, ht, -⟩ := hG x hcompat
    refine ⟨t, (hF (fun i ↦ F.obj.map (f i).op y)
      (Presieve.Arrows.toCompatible F.obj f y).2).unique (fun i ↦ ?_) (fun _ ↦ rfl)⟩
    have hnat : φ.hom.app (op (Z i)) (G.obj.map (f i).op t) =
        F.obj.map (f i).op (φ.hom.app U t) :=
      ConcreteCategory.congr_hom (φ.hom.naturality (f i).op) t
    exact hnat.symm.trans ((congrArg (φ.hom.app (op (Z i))) (ht i)).trans (hx i))
  exact isIso_of_reflects_iso φ (sheafToPresheaf _ _)

end EtaleLocality

section SingleCoverDescent

variable {S S' : Scheme.{u}}

/-- Regard `(toEtale S').obj X` as an object of `S.Etale` via `p : S' ⟶ S`. -/
noncomputable abbrev toBaseX (p : S' ⟶ S) [Etale p] (X : FiniteEtaleScheme S') : S.Etale :=
  (etaleComp p).obj ((toEtale S').obj X)

/-- Identification of the underlying scheme of `toBaseX p X` with `X.obj.left`. -/
noncomputable def tautIso (p : S' ⟶ S) [Etale p] (X : FiniteEtaleScheme S') :
    etaleObj (toBaseX p X) ≅ X.obj.left :=
  etaleMkObjIso (etaleHom ((toEtale S').obj X) ≫ p) ≪≫ toEtaleObjIso X

lemma tautIso_hom (p : S' ⟶ S) [Etale p] (X : FiniteEtaleScheme S') :
    (tautIso p X).hom = (etaleMkObjIso (etaleHom ((toEtale S').obj X) ≫ p)).hom ≫
      (toEtaleObjIso X).hom :=
  (rfl)

lemma tautIso_inv (p : S' ⟶ S) [Etale p] (X : FiniteEtaleScheme S') :
    (tautIso p X).inv = (toEtaleObjIso X).inv ≫
      (etaleMkObjIso (etaleHom ((toEtale S').obj X) ≫ p)).inv :=
  (rfl)

lemma tautIso_hom_comp (p : S' ⟶ S) [Etale p] (X : FiniteEtaleScheme S') :
    (tautIso p X).hom ≫ X.obj.hom ≫ p = etaleHom (toBaseX p X) := by
  dsimp only [tautIso, Iso.trans_hom]
  rw [Category.assoc, toEtaleObjIso_hom_comp_assoc, etaleMkObjIso_hom_comp]

lemma tautIso_inv_comp (p : S' ⟶ S) [Etale p] (X : FiniteEtaleScheme S') :
    (tautIso p X).inv ≫ etaleHom (toBaseX p X) = X.obj.hom ≫ p := by
  rw [← tautIso_hom_comp, Iso.inv_hom_id_assoc]

/-- The tautological section of `F` over `toBaseX p X` corresponding to an isomorphism
`e : (toSheaf S').obj X ≅ (restrictSheaf p).obj F`. -/
noncomputable def tautSection {p : S' ⟶ S} [Etale p] {X : FiniteEtaleScheme S'}
    {F : Sheaf (Scheme.smallEtaleTopology S) (Type u)}
    (e : (toSheaf S').obj X ≅ (restrictSheaf p).obj F) : F.obj.obj (op (toBaseX p X)) :=
  e.hom.hom.app (op ((toEtale S').obj X)) (𝟙 ((toEtale S').obj X))

lemma tautSection_def {p : S' ⟶ S} [Etale p] {X : FiniteEtaleScheme S'}
    {F : Sheaf (Scheme.smallEtaleTopology S) (Type u)}
    (e : (toSheaf S').obj X ≅ (restrictSheaf p).obj F) :
    tautSection e = e.hom.hom.app (op ((toEtale S').obj X)) (𝟙 ((toEtale S').obj X)) :=
  (rfl)

/-- Naturality evaluates `e.hom` on any section `f` by pulling back `tautSection e`. -/
lemma iso_app_eq_map_tautSection {p : S' ⟶ S} [Etale p] {X : FiniteEtaleScheme S'}
    {F : Sheaf (Scheme.smallEtaleTopology S) (Type u)}
    (e : (toSheaf S').obj X ≅ (restrictSheaf p).obj F) {U : S'.Etale}
    (f : U ⟶ (toEtale S').obj X) :
    e.hom.hom.app (op U) f = F.obj.map ((etaleComp p).map f).op (tautSection e) := by
  have hnat := ConcreteCategory.congr_hom (e.hom.hom.naturality f.op) (𝟙 ((toEtale S').obj X))
  change e.hom.hom.app (op U) (f ≫ 𝟙 _) = F.obj.map ((etaleComp p).map f).op (tautSection e) at hnat
  rwa [Category.comp_id] at hnat

/-- The projection `S' ×_S X ⟶ X` as a morphism in `S.Etale`. -/
private noncomputable def actSnd (p : S' ⟶ S) [Etale p] (X : FiniteEtaleScheme S') :
    (etaleComp p).obj (etaleMk (Limits.pullback.fst p (X.obj.hom ≫ p))) ⟶ toBaseX p X :=
  etaleHomMk ((etaleMkObjIso _).hom ≫ (etaleMkObjIso _).hom ≫
    Limits.pullback.snd p (X.obj.hom ≫ p) ≫ (tautIso p X).inv) (by
    rw [Category.assoc, Category.assoc, Category.assoc, tautIso_inv_comp,
      ← Limits.pullback.condition, etaleMkObjIso_hom_comp_assoc, etaleMkObjIso_hom_comp])

/-- The action morphism in `S'.Etale` induced by `e : (toSheaf S').obj X ≅ (restrictSheaf p).obj F`.
-/
private noncomputable def actEtale {p : S' ⟶ S} [Etale p] {X : FiniteEtaleScheme S'}
    {F : Sheaf (Scheme.smallEtaleTopology S) (Type u)}
    (e : (toSheaf S').obj X ≅ (restrictSheaf p).obj F) :
    etaleMk (Limits.pullback.fst p (X.obj.hom ≫ p)) ⟶ (toEtale S').obj X :=
  e.inv.hom.app (op (etaleMk (Limits.pullback.fst p (X.obj.hom ≫ p))))
    (F.obj.map (actSnd p X).op (tautSection e))

/-- The underlying scheme morphism `S' ×_S X ⟶ X` of the descent action. -/
private noncomputable def actMap {p : S' ⟶ S} [Etale p] {X : FiniteEtaleScheme S'}
    {F : Sheaf (Scheme.smallEtaleTopology S) (Type u)}
    (e : (toSheaf S').obj X ≅ (restrictSheaf p).obj F) :
    Limits.pullback p (X.obj.hom ≫ p) ⟶ X.obj.left :=
  (etaleMkObjIso (Limits.pullback.fst p (X.obj.hom ≫ p))).inv ≫
    etaleMap (actEtale e) ≫ (toEtaleObjIso X).hom

private lemma actMap_hom {p : S' ⟶ S} [Etale p] {X : FiniteEtaleScheme S'}
    {F : Sheaf (Scheme.smallEtaleTopology S) (Type u)}
    (e : (toSheaf S').obj X ≅ (restrictSheaf p).obj F) :
    actMap e ≫ X.obj.hom = Limits.pullback.fst p (X.obj.hom ≫ p) := by
  dsimp only [actMap]
  rw [Category.assoc, Category.assoc, toEtaleObjIso_hom_comp, etaleMap_w, etaleMkObjIso_inv_comp]

private lemma actMap_hom_assoc {p : S' ⟶ S} [Etale p] {X : FiniteEtaleScheme S'}
    {F : Sheaf (Scheme.smallEtaleTopology S) (Type u)}
    (e : (toSheaf S').obj X ≅ (restrictSheaf p).obj F) {T : Scheme.{u}} (g : S' ⟶ T) :
    actMap e ≫ X.obj.hom ≫ g = Limits.pullback.fst p (X.obj.hom ≫ p) ≫ g := by
  rw [← Category.assoc, actMap_hom]

/-- Pulling back `tautSection e` along `u ≫ actMap e` agrees with pulling back along `u ≫ snd`. -/
private lemma map_act_tautSection {p : S' ⟶ S} [Etale p] {X : FiniteEtaleScheme S'}
    {F : Sheaf (Scheme.smallEtaleTopology S) (Type u)}
    (e : (toSheaf S').obj X ≅ (restrictSheaf p).obj F) {W : S.Etale}
    (u : etaleObj W ⟶ Limits.pullback p (X.obj.hom ≫ p))
    (hu : u ≫ Limits.pullback.fst p (X.obj.hom ≫ p) ≫ p = etaleHom W) :
    F.obj.map (etaleHomMk (u ≫ actMap e ≫ (tautIso p X).inv) (by
        rw [Category.assoc, Category.assoc, tautIso_inv_comp, actMap_hom_assoc, hu])).op
        (tautSection e) =
      F.obj.map (etaleHomMk (u ≫ Limits.pullback.snd p (X.obj.hom ≫ p) ≫ (tautIso p X).inv) (by
        rw [Category.assoc, Category.assoc, tautIso_inv_comp, ← Limits.pullback.condition, hu])).op
        (tautSection e) := by
  let UP : S'.Etale := etaleMk (Limits.pullback.fst p (X.obj.hom ≫ p))
  let u' : W ⟶ (etaleComp p).obj UP :=
    etaleHomMk (u ≫ (etaleMkObjIso (Limits.pullback.fst p (X.obj.hom ≫ p))).inv ≫
      (etaleMkObjIso (etaleHom UP ≫ p)).inv) (by
      rw [Category.assoc, Category.assoc, etaleMkObjIso_inv_comp, etaleMkObjIso_inv_comp_assoc, hu])
  have h1 : u' ≫ (etaleComp p).map (actEtale e) =
      etaleHomMk (u ≫ actMap e ≫ (tautIso p X).inv) (by
        rw [Category.assoc, Category.assoc, tautIso_inv_comp, actMap_hom_assoc, hu]) := by
    apply etale_hom_ext
    rw [etaleMap_comp, etaleMap_etaleHomMk, etaleMap_etaleComp_map]
    dsimp only [u']
    rw [etaleMap_etaleHomMk]
    dsimp only [actMap, tautIso, Iso.trans_inv, UP]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  have h2 : u' ≫ actSnd p X =
      etaleHomMk (u ≫ Limits.pullback.snd p (X.obj.hom ≫ p) ≫ (tautIso p X).inv) (by
        rw [Category.assoc, Category.assoc, tautIso_inv_comp, ← Limits.pullback.condition,
          hu]) := by
    apply etale_hom_ext
    rw [etaleMap_comp, etaleMap_etaleHomMk]
    dsimp only [u', actSnd]
    rw [etaleMap_etaleHomMk, etaleMap_etaleHomMk]
    dsimp only [UP]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hact : F.obj.map ((etaleComp p).map (actEtale e)).op (tautSection e) =
      F.obj.map (actSnd p X).op (tautSection e) := by
    rw [← iso_app_eq_map_tautSection e (actEtale e)]
    exact ConcreteCategory.congr_hom
      (congrArg (fun η ↦ η.hom.app (op UP)) e.inv_hom_id)
      (F.obj.map (actSnd p X).op (tautSection e))
  rw [← h1, ← h2, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hact]

/-- Unit law for the descent datum attached to `e`. -/
private lemma descentDatumOfIso_lift_act {p : S' ⟶ S} [Etale p] {X : FiniteEtaleScheme S'}
    {F : Sheaf (Scheme.smallEtaleTopology S) (Type u)}
    (e : (toSheaf S').obj X ≅ (restrictSheaf p).obj F) :
    Limits.pullback.lift X.obj.hom (𝟙 X.obj.left) (by simp) ≫ actMap e = 𝟙 X.obj.left := by
  let f₁ : (toEtale S').obj X ⟶ (toEtale S').obj X :=
    etaleHomMk ((toEtaleObjIso X).hom ≫
      Limits.pullback.lift X.obj.hom (𝟙 X.obj.left) (by simp) ≫ actMap e ≫ (toEtaleObjIso X).inv)
      (by rw [Category.assoc, Category.assoc, Category.assoc, toEtaleObjIso_inv_comp,
            actMap_hom, Limits.pullback.lift_fst, toEtaleObjIso_hom_comp])
  have hinj : Function.Injective (e.hom.hom.app (op ((toEtale S').obj X))) := by
    have : IsIso e.hom.hom := inferInstanceAs (IsIso ((sheafToPresheaf _ _).map e.hom))
    have : IsIso (e.hom.hom.app (op ((toEtale S').obj X))) :=
      (NatTrans.isIso_iff_isIso_app e.hom.hom).mp inferInstance _
    exact ((isIso_iff_bijective _).mp inferInstance).1
  have hfeq : f₁ = 𝟙 ((toEtale S').obj X) := hinj <| by
    rw [iso_app_eq_map_tautSection e f₁, iso_app_eq_map_tautSection e (𝟙 _)]
    have hact := map_act_tautSection e
      ((tautIso p X).hom ≫ Limits.pullback.lift X.obj.hom (𝟙 X.obj.left) (by simp))
      (by rw [Category.assoc, Limits.pullback.lift_fst_assoc, tautIso_hom_comp])
    have hL : (etaleComp p).map f₁ =
        etaleHomMk (((tautIso p X).hom ≫
          Limits.pullback.lift X.obj.hom (𝟙 X.obj.left) (by simp)) ≫
          actMap e ≫ (tautIso p X).inv) (by
          rw [Category.assoc, Category.assoc, Category.assoc, tautIso_inv_comp, actMap_hom_assoc,
            Limits.pullback.lift_fst_assoc, tautIso_hom_comp]) := by
      apply etale_hom_ext
      rw [etaleMap_etaleComp_map, etaleMap_etaleHomMk]
      dsimp only [f₁]
      rw [etaleMap_etaleHomMk]
      dsimp only [tautIso, Iso.trans_hom, Iso.trans_inv]
      simp only [Category.assoc]
    have hR : (etaleComp p).map (𝟙 ((toEtale S').obj X)) =
        etaleHomMk (((tautIso p X).hom ≫
          Limits.pullback.lift X.obj.hom (𝟙 X.obj.left) (by simp)) ≫
          Limits.pullback.snd p (X.obj.hom ≫ p) ≫ (tautIso p X).inv) (by
          rw [Category.assoc, Category.assoc, Category.assoc, tautIso_inv_comp,
            ← Limits.pullback.condition, Limits.pullback.lift_fst_assoc, tautIso_hom_comp]) := by
      apply etale_hom_ext
      simp only [etaleMap_id, etaleMap_etaleHomMk, Category.assoc,
        Limits.pullback.lift_snd_assoc, Category.id_comp, Iso.hom_inv_id]
    rw [hL, hR]
    exact hact
  have hmap := congrArg etaleMap hfeq
  rw [etaleMap_id] at hmap
  dsimp only [f₁] at hmap
  rw [etaleMap_etaleHomMk] at hmap
  rw [← cancel_epi (toEtaleObjIso X).hom, ← cancel_mono (toEtaleObjIso X).inv]
  simpa only [Category.assoc, Category.comp_id, Iso.hom_inv_id] using hmap

/-- Associativity (cocycle) law for the descent datum attached to `e`. -/
private lemma descentDatumOfIso_act_assoc {p : S' ⟶ S} [Etale p] {X : FiniteEtaleScheme S'}
    {F : Sheaf (Scheme.smallEtaleTopology S) (Type u)}
    (e : (toSheaf S').obj X ≅ (restrictSheaf p).obj F) :
    Limits.pullback.lift (Limits.pullback.fst p (Limits.pullback.fst p (X.obj.hom ≫ p) ≫ p))
        (Limits.pullback.snd p (Limits.pullback.fst p (X.obj.hom ≫ p) ≫ p) ≫ actMap e)
        (by rw [Category.assoc, actMap_hom_assoc]; exact Limits.pullback.condition) ≫ actMap e =
      Limits.pullback.lift (Limits.pullback.fst p (Limits.pullback.fst p (X.obj.hom ≫ p) ≫ p))
        (Limits.pullback.snd p (Limits.pullback.fst p (X.obj.hom ≫ p) ≫ p) ≫
          Limits.pullback.snd p (X.obj.hom ≫ p))
        (by
          rw [Category.assoc, ← Limits.pullback.condition (f := p) (g := X.obj.hom ≫ p)]
          exact Limits.pullback.condition) ≫ actMap e := by
  let Q := Limits.pullback p (Limits.pullback.fst p (X.obj.hom ≫ p) ≫ p)
  let UQ : S'.Etale := etaleMk (Limits.pullback.fst p (Limits.pullback.fst p (X.obj.hom ≫ p) ≫ p))
  let q₁ : Q ⟶ Limits.pullback p (X.obj.hom ≫ p) :=
    Limits.pullback.lift (Limits.pullback.fst p _) (Limits.pullback.snd p _ ≫ actMap e)
      (by rw [Category.assoc, actMap_hom_assoc, Limits.pullback.condition])
  let q₂ : Q ⟶ Limits.pullback p (X.obj.hom ≫ p) :=
    Limits.pullback.lift (Limits.pullback.fst p _)
      (Limits.pullback.snd p _ ≫ Limits.pullback.snd p (X.obj.hom ≫ p))
      (by rw [Category.assoc, ← Limits.pullback.condition (f := p) (g := X.obj.hom ≫ p),
            Limits.pullback.condition])
  let g₁ : UQ ⟶ (toEtale S').obj X := etaleMkToFE (q₁ ≫ actMap e)
    (by rw [Category.assoc, actMap_hom]; exact Limits.pullback.lift_fst _ _ _)
  let g₂ : UQ ⟶ (toEtale S').obj X := etaleMkToFE (q₂ ≫ actMap e)
    (by rw [Category.assoc, actMap_hom]; exact Limits.pullback.lift_fst _ _ _)
  have hinj : Function.Injective (e.hom.hom.app (op UQ)) := by
    have : IsIso e.hom.hom := inferInstanceAs (IsIso ((sheafToPresheaf _ _).map e.hom))
    have : IsIso (e.hom.hom.app (op UQ)) :=
      (NatTrans.isIso_iff_isIso_app e.hom.hom).mp inferInstance _
    exact ((isIso_iff_bijective _).mp inferInstance).1
  have hgeq : g₁ = g₂ := hinj <| by
    rw [iso_app_eq_map_tautSection e g₁, iso_app_eq_map_tautSection e g₂]
    let ιQ := (etaleMkObjIso (etaleHom UQ ≫ p)).hom ≫
      (etaleMkObjIso (Limits.pullback.fst p (Limits.pullback.fst p (X.obj.hom ≫ p) ≫ p))).hom
    have hιQ : ιQ ≫ Limits.pullback.fst p _ ≫ p = etaleHom ((etaleComp p).obj UQ) := by
      dsimp only [ιQ]
      rw [Category.assoc, etaleMkObjIso_hom_comp_assoc, etaleMkObjIso_hom_comp]
    have hq₁ : (ιQ ≫ q₁) ≫ Limits.pullback.fst p (X.obj.hom ≫ p) ≫ p =
        etaleHom ((etaleComp p).obj UQ) := by
      rw [Category.assoc, Limits.pullback.lift_fst_assoc]; exact hιQ
    have hsnd : (ιQ ≫ Limits.pullback.snd p _) ≫ Limits.pullback.fst p (X.obj.hom ≫ p) ≫ p =
        etaleHom ((etaleComp p).obj UQ) := by
      rw [Category.assoc, ← Limits.pullback.condition]; exact hιQ
    have hq₂ : (ιQ ≫ q₂) ≫ Limits.pullback.fst p (X.obj.hom ≫ p) ≫ p =
        etaleHom ((etaleComp p).obj UQ) := by
      rw [Category.assoc, Limits.pullback.lift_fst_assoc]; exact hιQ
    have h1 := map_act_tautSection e (ιQ ≫ q₁) hq₁
    have h2 := map_act_tautSection e (ιQ ≫ Limits.pullback.snd p _) hsnd
    have h3 := map_act_tautSection e (ιQ ≫ q₂) hq₂
    have hL : (etaleComp p).map g₁ = etaleHomMk ((ιQ ≫ q₁) ≫ actMap e ≫ (tautIso p X).inv)
        (by rw [Category.assoc, Category.assoc (actMap e), tautIso_inv_comp, actMap_hom_assoc,
          hq₁]) := by
      apply etale_hom_ext
      rw [etaleMap_etaleComp_map, etaleMap_etaleHomMk]
      dsimp only [g₁, ιQ, tautIso, Iso.trans_inv]
      rw [etaleMap_etaleMkToFE]
      simp only [Category.assoc]
    have hR : (etaleComp p).map g₂ = etaleHomMk ((ιQ ≫ q₂) ≫ actMap e ≫ (tautIso p X).inv)
        (by rw [Category.assoc, Category.assoc (actMap e), tautIso_inv_comp, actMap_hom_assoc,
          hq₂]) := by
      apply etale_hom_ext
      rw [etaleMap_etaleComp_map, etaleMap_etaleHomMk]
      dsimp only [g₂, ιQ, tautIso, Iso.trans_inv]
      rw [etaleMap_etaleMkToFE]
      simp only [Category.assoc]
    have hM1 : etaleHomMk ((ιQ ≫ q₁) ≫ Limits.pullback.snd p (X.obj.hom ≫ p) ≫ (tautIso p X).inv)
          (by rw [Category.assoc, Category.assoc (Limits.pullback.snd _ _), tautIso_inv_comp,
            ← Limits.pullback.condition, hq₁]) =
        etaleHomMk ((ιQ ≫ Limits.pullback.snd p _) ≫ actMap e ≫ (tautIso p X).inv)
          (by rw [Category.assoc, Category.assoc (actMap e), tautIso_inv_comp, actMap_hom_assoc,
            hsnd]) := by
      apply etale_hom_ext
      simp only [etaleMap_etaleHomMk, q₁, Category.assoc, Limits.pullback.lift_snd_assoc]
    have hM2 : etaleHomMk ((ιQ ≫ Limits.pullback.snd p _) ≫
          Limits.pullback.snd p (X.obj.hom ≫ p) ≫ (tautIso p X).inv)
          (by rw [Category.assoc, Category.assoc (Limits.pullback.snd _ _), tautIso_inv_comp,
            ← Limits.pullback.condition, hsnd]) =
        etaleHomMk ((ιQ ≫ q₂) ≫ Limits.pullback.snd p (X.obj.hom ≫ p) ≫ (tautIso p X).inv)
          (by rw [Category.assoc, Category.assoc (Limits.pullback.snd _ _), tautIso_inv_comp,
            ← Limits.pullback.condition, hq₂]) := by
      apply etale_hom_ext
      simp only [etaleMap_etaleHomMk, q₂, Category.assoc, Limits.pullback.lift_snd_assoc]
    rw [hL, hR, h1, hM1, h2, hM2, ← h3]
  have hmap := congrArg etaleMap hgeq
  dsimp only [g₁, g₂] at hmap
  rw [etaleMap_etaleMkToFE, etaleMap_etaleMkToFE] at hmap
  rw [← cancel_epi (etaleMkObjIso
      (Limits.pullback.fst p (Limits.pullback.fst p (X.obj.hom ≫ p) ≫ p))).hom,
    ← cancel_mono (toEtaleObjIso X).inv]
  simpa only [Category.assoc] using hmap

/-- An isomorphism `(toSheaf S').obj X ≅ (restrictSheaf p).obj F` induces a descent datum on `X`
relative to `p`. -/
private noncomputable def descentDatumOfIso {p : S' ⟶ S} [Etale p] {X : FiniteEtaleScheme S'}
    {F : Sheaf (Scheme.smallEtaleTopology S) (Type u)}
    (e : (toSheaf S').obj X ≅ (restrictSheaf p).obj F) : DescentDatum p X.obj where
  act := actMap e
  act_hom := actMap_hom e
  lift_act := descentDatumOfIso_lift_act e
  act_assoc := descentDatumOfIso_act_assoc e

/-- Descent compatibility of `tautSection e` along the quotient map `q : toBaseX p X ⟶ X₀`. -/
private lemma descent_tautSection_compat {p : S' ⟶ S} [Etale p] {X : FiniteEtaleScheme S'}
    {F : Sheaf (Scheme.smallEtaleTopology S) (Type u)}
    (e : (toSheaf S').obj X ≅ (restrictSheaf p).obj F)
    (X₀ : FiniteEtaleScheme S) (f : (DescentDatum.baseChange p X₀.obj).Hom (descentDatumOfIso e))
    [IsIso f.hom] {W : S.Etale} (a₁ a₂ : W ⟶ toBaseX p X)
    (hcomm : a₁ ≫ etaleHomMk ((tautIso p X).hom ≫ (asIso f.hom).inv.left ≫
        Limits.pullback.fst X₀.obj.hom p ≫ (toEtaleObjIso X₀).inv) (by
        rw [Category.assoc, Category.assoc, Category.assoc, toEtaleObjIso_inv_comp,
          Limits.pullback.condition, ← Category.assoc (asIso f.hom).inv.left]
        have hw : (asIso f.hom).inv.left ≫ Limits.pullback.snd X₀.obj.hom p = X.obj.hom :=
          (asIso f.hom).inv.w
        rw [hw, tautIso_hom_comp]) =
      a₂ ≫ etaleHomMk ((tautIso p X).hom ≫ (asIso f.hom).inv.left ≫
        Limits.pullback.fst X₀.obj.hom p ≫ (toEtaleObjIso X₀).inv) (by
        rw [Category.assoc, Category.assoc, Category.assoc, toEtaleObjIso_inv_comp,
          Limits.pullback.condition, ← Category.assoc (asIso f.hom).inv.left]
        have hw : (asIso f.hom).inv.left ≫ Limits.pullback.snd X₀.obj.hom p = X.obj.hom :=
          (asIso f.hom).inv.w
        rw [hw, tautIso_hom_comp])) :
    F.obj.map a₁.op (tautSection e) = F.obj.map a₂.op (tautSection e) := by
  let eBC : (Over.pullback p).obj X₀.obj ≅ X.obj := asIso f.hom
  let x₁ := etaleMap a₁ ≫ (tautIso p X).hom
  let x₂ := etaleMap a₂ ≫ (tautIso p X).hom
  have hx₁ : x₁ ≫ X.obj.hom ≫ p = etaleHom W := by
    rw [Category.assoc, tautIso_hom_comp, etaleMap_w]
  have hx₂ : x₂ ≫ X.obj.hom ≫ p = etaleHom W := by
    rw [Category.assoc, tautIso_hom_comp, etaleMap_w]
  have hπ₁ : x₁ ≫ eBC.inv.left ≫ Limits.pullback.fst X₀.obj.hom p =
      x₂ ≫ eBC.inv.left ≫ Limits.pullback.fst X₀.obj.hom p := by
    have hm := congrArg etaleMap hcomm
    rw [etaleMap_comp, etaleMap_comp, etaleMap_etaleHomMk] at hm
    rw [← cancel_mono (toEtaleObjIso X₀).inv]
    simpa only [x₁, x₂, eBC, Category.assoc] using hm
  let u : etaleObj W ⟶ Limits.pullback p (X.obj.hom ≫ p) :=
    Limits.pullback.lift (x₁ ≫ X.obj.hom) x₂ (by rw [Category.assoc, hx₁, hx₂])
  have hu_act : u ≫ actMap e = x₁ := by
    have hw : eBC.inv.left ≫ Limits.pullback.snd X₀.obj.hom p = X.obj.hom := eBC.inv.w
    have hinvW : X.obj.hom ≫ p = eBC.inv.left ≫ ((Over.pullback p).obj X₀.obj).hom ≫ p := by
      rw [← Category.assoc, eBC.inv.w]
    have hact_eq : actMap e ≫ eBC.inv.left =
        Limits.pullback.map p (X.obj.hom ≫ p) p (((Over.pullback p).obj X₀.obj).hom ≫ p) (𝟙 S')
          eBC.inv.left (𝟙 S) (by simp) (by simpa using hinvW) ≫
          (DescentDatum.baseChange p X₀.obj).act := by
      rw [← cancel_mono eBC.hom.left, Category.assoc, Category.assoc]
      have hinv : eBC.inv.left ≫ eBC.hom.left = 𝟙 _ := congrArg CommaMorphism.left eBC.inv_hom_id
      have hf_act : (DescentDatum.baseChange p X₀.obj).act ≫ eBC.hom.left =
          Limits.pullback.map p (((Over.pullback p).obj X₀.obj).hom ≫ p) p (X.obj.hom ≫ p)
            (𝟙 S') eBC.hom.left (𝟙 S) (by simp) (by simp) ≫ actMap e := f.map_act.symm
      rw [hinv, Category.comp_id, hf_act]
      have hmap_id : Limits.pullback.map p (X.obj.hom ≫ p) p
            (((Over.pullback p).obj X₀.obj).hom ≫ p) (𝟙 S') eBC.inv.left (𝟙 S)
            (by simp) (by simpa using hinvW) ≫
          Limits.pullback.map p (((Over.pullback p).obj X₀.obj).hom ≫ p) p (X.obj.hom ≫ p)
            (𝟙 S') eBC.hom.left (𝟙 S) (by simp) (by simp) = 𝟙 _ := by
        refine Limits.pullback.hom_ext ?_ ?_ <;> simp [hinv]
      rw [← Category.assoc, hmap_id, Category.id_comp]
    rw [← cancel_mono eBC.inv.left, Category.assoc, hact_eq]
    refine Limits.pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, DescentDatum.baseChange_act_fst, Limits.pullback.map,
        Limits.pullback.lift_snd_assoc, u]
      exact hπ₁.symm
    · simp only [Category.assoc, DescentDatum.baseChange_act_snd, Limits.pullback.map,
        Limits.pullback.lift_fst, Category.comp_id, u]
      exact (congrArg (fun k ↦ x₁ ≫ k) hw).symm
  have hact := map_act_tautSection e u (by rw [Limits.pullback.lift_fst_assoc, Category.assoc, hx₁])
  have ha₁ : a₁ = etaleHomMk (u ≫ actMap e ≫ (tautIso p X).inv) (by
      rw [Category.assoc, Category.assoc, tautIso_inv_comp, actMap_hom_assoc,
        Limits.pullback.lift_fst_assoc, Category.assoc, hx₁]) := by
    apply etale_hom_ext
    rw [etaleMap_etaleHomMk, ← Category.assoc, hu_act]
    simp [x₁]
  have ha₂ : a₂ = etaleHomMk (u ≫ Limits.pullback.snd p (X.obj.hom ≫ p) ≫ (tautIso p X).inv) (by
      rw [Category.assoc, Category.assoc, tautIso_inv_comp, ← Limits.pullback.condition,
        Limits.pullback.lift_fst_assoc, Category.assoc, hx₁]) := by
    apply etale_hom_ext
    rw [etaleMap_etaleHomMk, ← Category.assoc, Limits.pullback.lift_snd]
    simp [x₂]
  rw [ha₁, ha₂]
  exact hact

/-- Effective descent for representability of étale sheaves by finite étale schemes along a
quasi-compact surjective étale morphism `p : S' ⟶ S`. -/
theorem exists_toSheaf_iso_of_restrictSheaf_iso (p : S' ⟶ S) [Etale p] [Surjective p]
    [QuasiCompact p] (X : FiniteEtaleScheme S')
    (F : Sheaf (Scheme.smallEtaleTopology S) (Type u))
    (e : (toSheaf S').obj X ≅ (restrictSheaf p).obj F) :
    ∃ X₀ : FiniteEtaleScheme S, Nonempty ((toSheaf S).obj X₀ ≅ F) := by
  let D := descentDatumOfIso e
  obtain ⟨X₀_over, hfin, het, f, hf⟩ := D.exists_isFinite_etale_baseChange_hom_isIso_of_quasiCompact
  let X₀ : FiniteEtaleScheme S := ⟨X₀_over, (finiteEtaleSchemeProperty_iff _).mpr ⟨hfin, het⟩⟩
  let eBC : (Over.pullback p).obj X₀.obj ≅ X.obj := asIso f.hom
  let q : toBaseX p X ⟶ (toEtale S).obj X₀ :=
    etaleHomMk ((tautIso p X).hom ≫ eBC.inv.left ≫ Limits.pullback.fst X₀.obj.hom p ≫
      (toEtaleObjIso X₀).inv) (by
      rw [Category.assoc, Category.assoc, Category.assoc, toEtaleObjIso_inv_comp,
        Limits.pullback.condition, ← Category.assoc eBC.inv.left]
      have hw : eBC.inv.left ≫ Limits.pullback.snd X₀.obj.hom p = X.obj.hom := eBC.inv.w
      rw [hw, tautIso_hom_comp])
  have : Surjective (etaleMap q) := by
    rw [show etaleMap q = (tautIso p X).hom ≫ eBC.inv.left ≫ Limits.pullback.fst X₀.obj.hom p ≫
      (toEtaleObjIso X₀).inv from etaleMap_etaleHomMk _ _]
    infer_instance
  have hsheaf := Presieve.isSheafFor_singleton.mp (isSheafFor_singleton_of_surjective F q)
  obtain ⟨t₀, ht₀, -⟩ := hsheaf (tautSection e) (fun a₁ a₂ hcomm ↦
    descent_tautSection_compat e X₀ f a₁ a₂ hcomm)
  let φ : (toSheaf S).obj X₀ ⟶ F := yonedaSheafHom t₀
  have hres : IsIso ((restrictSheaf p).map φ) := by
    let eFE : (pullback p).obj X₀ ≅ X := ObjectProperty.isoMk _ eBC
    let θ := ((toSheafCompRestrictSheafIso p).app X₀).symm
    have heq : θ.hom ≫ (restrictSheaf p).map φ = (toSheaf S').map eFE.hom ≫ e.hom := by
      apply yoneda_hom_ext
      let V₀ : S'.Etale := (toEtale S').obj ((pullback p).obj X₀)
      change ((restrictSheaf p).map φ).hom.app (op V₀)
          ((((toSheafCompRestrictSheafIso p).app X₀).inv.hom.app (op V₀)) (𝟙 V₀)) =
        e.hom.hom.app (op V₀) (((toSheaf S').map eFE.hom).hom.app (op V₀) (𝟙 V₀))
      rw [toSheafCompRestrictSheafIso_inv_app]
      change F.obj.map ((restrictSectionEquiv p X₀ V₀).symm (𝟙 V₀)).op t₀ =
        e.hom.hom.app (op V₀) (𝟙 V₀ ≫ (toEtale S').map eFE.hom)
      rw [Category.id_comp, iso_app_eq_map_tautSection e ((toEtale S').map eFE.hom), ← ht₀,
        ← Functor.map_comp_apply, ← op_comp]
      refine congrArg (fun k ↦ F.obj.map (Quiver.Hom.op k) t₀) ?_
      apply etale_hom_ext
      rw [etaleMap_comp, etaleMap_etaleComp_map, etaleMap_toEtale,
        etaleMap_restrictSectionEquiv_symm, etaleMap_id, Category.id_comp]
      dsimp only [q]
      rw [etaleMap_etaleHomMk, tautIso_hom]
      have hcancel : eFE.hom.hom.left ≫ eBC.inv.left = (pullbackObjIso p X₀).hom :=
        (congrArg CommaMorphism.left eBC.hom_inv_id).trans (pullbackObjIso_hom p X₀).symm
      simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hcancel]
      rfl
    have : IsIso (θ.hom ≫ (restrictSheaf p).map φ) := heq ▸ inferInstance
    exact IsIso.of_isIso_comp_left θ.hom ((restrictSheaf p).map φ)
  have : IsIso φ := isIso_of_forall_isIso_restrictSheaf (fun _ : Unit ↦ p)
    (by simp [Set.range_eq_univ.mpr p.surjective, Set.iUnion_const]) φ (fun _ ↦ hres)
  exact ⟨X₀, ⟨asIso φ⟩⟩

end SingleCoverDescent

end TauCeti.FiniteEtaleScheme
