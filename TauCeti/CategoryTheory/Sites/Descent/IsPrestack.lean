/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-!
# Restricting and gluing morphisms in a prestack

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a pseudofunctor and `M`, `N` objects of `F` over `S`.
Mathlib's presheaf of morphisms `Pseudofunctor.presheafHom M N` on `Over S` has value
`f^* M ⟶ f^* N` at `(Y, f)`, and its value at the terminal object `Over.mk (𝟙 S)` is identified with
`M ⟶ N` by `Pseudofunctor.presheafHomObjHomEquiv`. This file shows that restricting the element
given by `φ : M ⟶ N` to `(Y, f)` gives `f^* φ`
(`CategoryTheory.Pseudofunctor.presheafHom_map_presheafHomObjHomEquiv`). So a morphism `φ` is an
amalgamation of a family of local morphisms exactly when its pullbacks are the members of the
family, which is how the sheaf condition of `presheafHom M N` (the prestack condition) is checked.

For a prestack `F` for a Grothendieck topology `J`, this gives the descent of morphisms along a
covering sieve in the form used to build descent data by hand: a morphism is determined by its
pullbacks to the members of a covering sieve (`IsPrestack.hom_ext`, `IsPrestack.pullHom_ext`),
and a family of local morphisms compatible under pullback glues to a morphism
(`IsPrestack.glue`, `IsPrestack.pullHom_glue`). The local morphisms are written with Mathlib's
`LocallyDiscreteOpToCat.pullHom`, whose composition is computed by `pullHom_comp`.

## References

* [Stacks Project, Definition 026F](https://stacks.math.columbia.edu/tag/026F)
-/

public section

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor

open LocallyDiscreteOpToCat

variable {C : Type*} [Category* C] (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat) {S : C}

/-- The restriction of the element of `F.presheafHom M N` over the terminal object given by
`φ : M ⟶ N` to an object `(Y, f)` of `Over S` is `f^* φ`. -/
lemma presheafHom_map_presheafHomObjHomEquiv {M N : F.obj (.mk (op S))} (φ : M ⟶ N)
    {Y : Over S} (g : Y ⟶ Over.mk (𝟙 S)) :
    (F.presheafHom M N).map g.op (F.presheafHomObjHomEquiv φ) =
      (F.map Y.hom.op.toLoc).toFunctor.map φ := by
  obtain ⟨Y, y, rfl⟩ := Over.mk_surjective Y
  obtain rfl : g = Over.homMk y := by ext; simpa using Over.w g
  -- This is the component, for the family consisting of `y` alone, of Mathlib's identification of
  -- the compatible family given by `φ` with the morphism of descent data `toDescentData.map φ`.
  exact congr(DescentData.Hom.hom
    $(DescentData.subtypeCompatibleHomEquiv_toCompatible_presheafHomObjHomEquiv F
      (fun _ : PUnit.{1} ↦ y) φ) PUnit.unit)

/-- The element of `F.presheafHom M N` over the terminal object given by `φ : M ⟶ N` is
`(𝟙 S)^* φ`. -/
lemma presheafHomObjHomEquiv_eq_map {M N : F.obj (.mk (op S))} (φ : M ⟶ N) :
    F.presheafHomObjHomEquiv φ = (F.map (𝟙 S).op.toLoc).toFunctor.map φ := by
  have := presheafHom_map_presheafHomObjHomEquiv F φ (𝟙 (Over.mk (𝟙 S)))
  rw [op_id, CategoryTheory.Functor.map_id] at this
  exact this

/-- The pullback along `a` of the morphism `M ⟶ N` corresponding to a local morphism
`x : (𝟙 S)^* M ⟶ (𝟙 S)^* N` is the pullback of `x` along `a`. -/
lemma map_presheafHomObjHomEquiv_symm {M N : F.obj (.mk (op S))}
    (x : (F.map (𝟙 S).op.toLoc).toFunctor.obj M ⟶ (F.map (𝟙 S).op.toLoc).toFunctor.obj N)
    {Y : C} (a : Y ⟶ S) :
    (F.map a.op.toLoc).toFunctor.map (F.presheafHomObjHomEquiv.symm x) =
      pullHom (F := F) (M₁ := M) (M₂ := N) (f₁ := 𝟙 S) (f₂ := 𝟙 S) x a a a (Category.comp_id a)
        (Category.comp_id a) := by
  have := presheafHom_map_presheafHomObjHomEquiv F (F.presheafHomObjHomEquiv.symm x)
    (Over.homMk a : Over.mk a ⟶ Over.mk (𝟙 S))
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

variable {F}

/-- The pullback of a composite of local morphisms is the composite of their pullbacks. -/
@[reassoc]
lemma pullHom_comp ⦃X₁ X₂ X₃ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃M₃ : F.obj (.mk (op X₃))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄ ⦃f₃ : Y ⟶ X₃⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (ψ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (gf₃ : Y' ⟶ X₃)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch)
    (hgf₃ : g ≫ f₃ = gf₃ := by cat_disch) :
    pullHom (φ ≫ ψ) g gf₁ gf₃ hgf₁ hgf₃ =
      pullHom φ g gf₁ gf₂ hgf₁ hgf₂ ≫ pullHom ψ g gf₂ gf₃ hgf₂ hgf₃ := by
  simp [pullHom]

/-- The pullback of an identity local morphism is an identity. -/
@[simp]
lemma pullHom_id_self ⦃X : C⦄ ⦃M : F.obj (.mk (op X))⦄ ⦃Y : C⦄ (f : Y ⟶ X) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf : Y' ⟶ X) (hgf : g ≫ f = gf) :
    pullHom (𝟙 ((F.map f.op.toLoc).toFunctor.obj M)) g gf gf hgf hgf = 𝟙 _ := by
  simp [pullHom]

/-- The pullback of `f^* φ` is `(g ≫ f)^* φ`. -/
@[simp]
lemma pullHom_map ⦃X : C⦄ ⦃M N : F.obj (.mk (op X))⦄ (φ : M ⟶ N) ⦃Y : C⦄ (f : Y ⟶ X) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf : Y' ⟶ X) (hgf : g ≫ f = gf) :
    pullHom ((F.map f.op.toLoc).toFunctor.map φ) g gf gf hgf hgf =
      (F.map gf.op.toLoc).toFunctor.map φ := by
  simp [pullHom]

/-- The pullback of the comparison isomorphism `f^* (p^* N) ⟶ k^* N` (for `f ≫ p = k`) is the
comparison isomorphism. -/
@[simp]
lemma pullHom_mapComp'_inv ⦃Z X : C⦄ (p : X ⟶ Z) (N : F.obj (.mk (op Z))) ⦃Y : C⦄ (f : Y ⟶ X)
    (k : Y ⟶ Z) (hk : f ≫ p = k) ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf : Y' ⟶ X) (gk : Y' ⟶ Z)
    (hgf : g ≫ f = gf) (hgk : g ≫ k = gk) :
    pullHom (M₁ := (F.map p.op.toLoc).toFunctor.obj N) (M₂ := N)
      ((F.mapComp' p.op.toLoc f.op.toLoc k.op.toLoc (by rw [← hk]; rfl)).inv.toNatTrans.app N)
        g gf gk hgf hgk =
      (F.mapComp' p.op.toLoc gf.op.toLoc gk.op.toLoc
        (by rw [← hgk, ← hgf, ← hk]; simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
          N := by
  subst hk hgf hgk
  rw [F.mapComp'₀₁₃_inv_app (f₀₁ := p.op.toLoc) (f₁₂ := f.op.toLoc) (f₂₃ := g.op.toLoc)
    (f₀₂ := (f ≫ p).op.toLoc) (f₁₃ := (g ≫ f).op.toLoc) (h₀₂ := rfl) (h₁₃ := rfl)
    (hf := by simp [← Quiver.Hom.comp_toLoc, ← op_comp])]
  simp [pullHom]

/-- The pullback of the comparison isomorphism `k^* N ⟶ f^* (p^* N)` (for `f ≫ p = k`) is the
comparison isomorphism. -/
@[simp]
lemma pullHom_mapComp'_hom ⦃Z X : C⦄ (p : X ⟶ Z) (N : F.obj (.mk (op Z))) ⦃Y : C⦄ (f : Y ⟶ X)
    (k : Y ⟶ Z) (hk : f ≫ p = k) ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf : Y' ⟶ X) (gk : Y' ⟶ Z)
    (hgf : g ≫ f = gf) (hgk : g ≫ k = gk) :
    pullHom (M₁ := N) (M₂ := (F.map p.op.toLoc).toFunctor.obj N)
      ((F.mapComp' p.op.toLoc f.op.toLoc k.op.toLoc (by rw [← hk]; rfl)).hom.toNatTrans.app N)
        g gk gf hgk hgf =
      (F.mapComp' p.op.toLoc gf.op.toLoc gk.op.toLoc
        (by rw [← hgk, ← hgf, ← hk]; simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
          N := by
  subst hk hgf hgk
  rw [F.mapComp'₀₁₃_hom_app (f₀₁ := p.op.toLoc) (f₁₂ := f.op.toLoc) (f₂₃ := g.op.toLoc)
    (f₀₂ := (f ≫ p).op.toLoc) (f₁₃ := (g ≫ f).op.toLoc) (h₀₂ := rfl) (h₁₃ := rfl)
    (hf := by simp [← Quiver.Hom.comp_toLoc, ← op_comp])]
  simp [pullHom]

/-- Pulling back a local morphism between objects of the form `p^* N`, written through the
comparison isomorphisms `(f ≫ p)^* N ≅ f^* (p^* N)`, is pulling back the corresponding local
morphism between pullbacks of `N`. -/
lemma pullHom_mapComp'_conj ⦃Z₁ Z₂ X₁ X₂ : C⦄ (p₁ : X₁ ⟶ Z₁) (p₂ : X₂ ⟶ Z₂)
    ⦃N₁ : F.obj (.mk (op Z₁))⦄ ⦃N₂ : F.obj (.mk (op Z₂))⦄ ⦃Y : C⦄ (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    (k₁ : Y ⟶ Z₁) (k₂ : Y ⟶ Z₂) (hk₁ : f₁ ≫ p₁ = k₁) (hk₂ : f₂ ≫ p₂ = k₂)
    (x : (F.map k₁.op.toLoc).toFunctor.obj N₁ ⟶ (F.map k₂.op.toLoc).toFunctor.obj N₂) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (gk₁ : Y' ⟶ Z₁) (gk₂ : Y' ⟶ Z₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) (hgk₁ : gf₁ ≫ p₁ = gk₁) (hgk₂ : gf₂ ≫ p₂ = gk₂) :
    pullHom (M₁ := (F.map p₁.op.toLoc).toFunctor.obj N₁)
      (M₂ := (F.map p₂.op.toLoc).toFunctor.obj N₂)
      ((F.mapComp' p₁.op.toLoc f₁.op.toLoc k₁.op.toLoc (by rw [← hk₁]; rfl)).inv.toNatTrans.app N₁ ≫
        x ≫ (F.mapComp' p₂.op.toLoc f₂.op.toLoc k₂.op.toLoc
          (by rw [← hk₂]; rfl)).hom.toNatTrans.app N₂) g gf₁ gf₂ hgf₁ hgf₂ =
      (F.mapComp' p₁.op.toLoc gf₁.op.toLoc gk₁.op.toLoc
          (by rw [← hgk₁]; rfl)).inv.toNatTrans.app N₁ ≫
        pullHom x g gk₁ gk₂ (by rw [← hgk₁, ← hgf₁, ← hk₁, Category.assoc])
          (by rw [← hgk₂, ← hgf₂, ← hk₂, Category.assoc]) ≫
        (F.mapComp' p₂.op.toLoc gf₂.op.toLoc gk₂.op.toLoc
          (by rw [← hgk₂]; rfl)).hom.toNatTrans.app N₂ := by
  subst hk₁ hk₂ hgf₁ hgf₂ hgk₁ hgk₂
  simp only [pullHom, Functor.map_comp, Category.assoc]
  rw [F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app_assoc (f₀₁ := p₁.op.toLoc)
      (f₁₂ := f₁.op.toLoc) (f₂₃ := g.op.toLoc) (f₀₂ := (f₁ ≫ p₁).op.toLoc)
      (f₁₃ := (g ≫ f₁).op.toLoc) (f := ((g ≫ f₁) ≫ p₁).op.toLoc) (h₀₂ := rfl) (h₁₃ := rfl)
      (hf := rfl),
    F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app (f₀₁ := p₂.op.toLoc)
      (f₁₂ := f₂.op.toLoc) (f₂₃ := g.op.toLoc) (f₀₂ := (f₂ ≫ p₂).op.toLoc)
      (f₁₃ := (g ≫ f₂).op.toLoc) (f := ((g ≫ f₂) ≫ p₂).op.toLoc) (h₀₂ := rfl) (h₁₃ := rfl)
      (hf := by simp [← Quiver.Hom.comp_toLoc, ← op_comp])]


namespace IsPrestack

variable {J : GrothendieckTopology C} [F.IsPrestack J]

/-- In a prestack, a morphism is determined by its pullbacks to the members of a covering
sieve. -/
lemma hom_ext {Y : C} {M N : F.obj (.mk (op Y))} {R : Sieve Y} (hR : R ∈ J Y) {φ φ' : M ⟶ N}
    (h : ∀ ⦃T : C⦄ (g : T ⟶ Y), R g →
      (F.map g.op.toLoc).toFunctor.map φ = (F.map g.op.toLoc).toFunctor.map φ') :
    φ = φ' := by
  apply F.presheafHomObjHomEquiv.injective
  have hR' : (Sieve.overEquiv (Over.mk (𝟙 Y))).symm R ∈ J.over Y (Over.mk (𝟙 Y)) := by
    rwa [GrothendieckTopology.mem_over_iff, OrderIso.apply_symm_apply]
  refine (((isSheaf_iff_isSheaf_of_type _ _).1
    (IsPrestack.isSheaf J M N)).isSeparated _ hR').ext fun Z g hg ↦ ?_
  rw [presheafHom_map_presheafHomObjHomEquiv, presheafHom_map_presheafHomObjHomEquiv]
  refine h _ ?_
  rw [Sieve.overEquiv_symm_iff] at hg
  rw [← Over.w g]
  simpa using hg

/-- In a prestack, a family of morphisms over the members of a covering sieve which is compatible
under pullback is the family of pullbacks of a morphism. -/
lemma exists_map_eq {Y : C} {M N : F.obj (.mk (op Y))} {R : Sieve Y} (hR : R ∈ J Y)
    (s : ∀ ⦃T : C⦄ (g : T ⟶ Y), R g →
      ((F.map g.op.toLoc).toFunctor.obj M ⟶ (F.map g.op.toLoc).toFunctor.obj N))
    (hs : ∀ ⦃T : C⦄ (g : T ⟶ Y) (hg : R g) ⦃T' : C⦄ (h : T' ⟶ T) (g' : T' ⟶ Y) (hg' : R g')
      (e : h ≫ g = g'), pullHom (s g hg) h g' g' e e = s g' hg') :
    ∃ φ : M ⟶ N, ∀ ⦃T : C⦄ (g : T ⟶ Y) (hg : R g),
      (F.map g.op.toLoc).toFunctor.map φ = s g hg := by
  have hR' : (Sieve.overEquiv (Over.mk (𝟙 Y))).symm R ∈ J.over Y (Over.mk (𝟙 Y)) := by
    rwa [GrothendieckTopology.mem_over_iff, OrderIso.apply_symm_apply]
  have mem {Z : Over Y} (g : Z ⟶ Over.mk (𝟙 Y))
      (hg : ((Sieve.overEquiv (Over.mk (𝟙 Y))).symm R).arrows g) : R Z.hom := by
    rw [Sieve.overEquiv_symm_iff] at hg
    rw [← Over.w g]
    simpa using hg
  let x : Presieve.FamilyOfElements (F.presheafHom M N)
      ((Sieve.overEquiv (Over.mk (𝟙 Y))).symm R).arrows :=
    fun Z g hg ↦ s Z.hom (mem g hg)
  have hx : x.Compatible := by
    intro Z₁ Z₂ W g₁ g₂ f₁ f₂ h₁ h₂ _
    have hW : R W.hom := by rw [← Over.w g₁]; exact R.downward_closed (mem f₁ h₁) _
    exact (hs _ _ g₁.left _ hW (Over.w g₁)).trans (hs _ _ g₂.left _ hW (Over.w g₂)).symm
  let H := ((isSheaf_iff_isSheaf_of_type _ _).1 (IsPrestack.isSheaf J M N)) _ hR'
  refine ⟨F.presheafHomObjHomEquiv.symm (H.amalgamate x hx), fun T g hg ↦ ?_⟩
  have := H.valid_glue hx (Over.homMk g : Over.mk g ⟶ Over.mk (𝟙 Y))
    (by rw [Sieve.overEquiv_symm_iff]; exact hg)
  have h₂ := presheafHom_map_presheafHomObjHomEquiv F
    (F.presheafHomObjHomEquiv.symm (H.amalgamate x hx)) (Over.homMk g : Over.mk g ⟶ Over.mk (𝟙 Y))
  rw [Equiv.apply_symm_apply] at h₂
  exact h₂.symm.trans this

variable ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
  ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄

/-- In a prestack, a local morphism `f₁^* M₁ ⟶ f₂^* M₂` is determined by its pullbacks to the
members of a covering sieve. -/
lemma pullHom_ext {R : Sieve Y} (hR : R ∈ J Y)
    {φ φ' : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂}
    (h : ∀ ⦃T : C⦄ (g : T ⟶ Y), R g →
      pullHom φ g (g ≫ f₁) (g ≫ f₂) = pullHom φ' g (g ≫ f₁) (g ≫ f₂)) :
    φ = φ' :=
  hom_ext hR fun T g hg ↦ by simpa [pullHom, cancel_epi, cancel_mono] using h g hg

/-- In a prestack, a family of local morphisms `gf₁^* M₁ ⟶ gf₂^* M₂` indexed by the members `g`
of a covering sieve of `Y` (with `gf₁ = g ≫ f₁` and `gf₂ = g ≫ f₂`) which is compatible under
pullback is the family of pullbacks of a local morphism `f₁^* M₁ ⟶ f₂^* M₂`. -/
lemma exists_pullHom_eq {R : Sieve Y} (hR : R ∈ J Y)
    (s : ∀ ⦃T : C⦄ (g : T ⟶ Y) (gf₁ : T ⟶ X₁) (gf₂ : T ⟶ X₂), g ≫ f₁ = gf₁ → g ≫ f₂ = gf₂ →
      R g → ((F.map gf₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map gf₂.op.toLoc).toFunctor.obj M₂))
    (hs : ∀ ⦃T : C⦄ (g : T ⟶ Y) (gf₁ : T ⟶ X₁) (gf₂ : T ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
      (hgf₂ : g ≫ f₂ = gf₂) (hg : R g) ⦃T' : C⦄ (h : T' ⟶ T) (g' : T' ⟶ Y) (g'f₁ : T' ⟶ X₁)
      (g'f₂ : T' ⟶ X₂) (hg'f₁ : g' ≫ f₁ = g'f₁) (hg'f₂ : g' ≫ f₂ = g'f₂) (hg' : R g')
      (e : h ≫ g = g'),
      pullHom (s g gf₁ gf₂ hgf₁ hgf₂ hg) h g'f₁ g'f₂ (by rw [← hgf₁, ← hg'f₁, ← e, Category.assoc])
        (by rw [← hgf₂, ← hg'f₂, ← e, Category.assoc]) = s g' g'f₁ g'f₂ hg'f₁ hg'f₂ hg') :
    ∃ φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂,
      ∀ ⦃T : C⦄ (g : T ⟶ Y) (gf₁ : T ⟶ X₁) (gf₂ : T ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
        (hgf₂ : g ≫ f₂ = gf₂) (hg : R g),
        pullHom φ g gf₁ gf₂ hgf₁ hgf₂ = s g gf₁ gf₂ hgf₁ hgf₂ hg := by
  obtain ⟨φ, hφ⟩ := exists_map_eq hR
    (fun T g hg ↦ (F.mapComp' f₁.op.toLoc g.op.toLoc (g ≫ f₁).op.toLoc).inv.toNatTrans.app M₁ ≫
      s g _ _ rfl rfl hg ≫
        (F.mapComp' f₂.op.toLoc g.op.toLoc (g ≫ f₂).op.toLoc).hom.toNatTrans.app M₂)
    (fun T g hg T' h g' hg' e ↦ by
      subst e
      rw [← hs g _ _ rfl rfl hg h _ _ _ rfl rfl hg' rfl]
      exact pullHom_mapComp'_conj f₁ f₂ g g _ _ rfl rfl _ h _ _ _ _ rfl rfl rfl rfl)
  refine ⟨φ, fun T g gf₁ gf₂ hgf₁ hgf₂ hg ↦ ?_⟩
  subst hgf₁ hgf₂
  rw [pullHom, hφ g hg]
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id,
    Cat.Hom.hom_inv_id_toNatTrans_app_assoc]

/-- In a prestack, the local morphism `f₁^* M₁ ⟶ f₂^* M₂` glued from a compatible family of local
morphisms over the members of a covering sieve, see `IsPrestack.exists_pullHom_eq`. -/
noncomputable def glue {R : Sieve Y} (hR : R ∈ J Y)
    (s : ∀ ⦃T : C⦄ (g : T ⟶ Y) (gf₁ : T ⟶ X₁) (gf₂ : T ⟶ X₂), g ≫ f₁ = gf₁ → g ≫ f₂ = gf₂ →
      R g → ((F.map gf₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map gf₂.op.toLoc).toFunctor.obj M₂))
    (hs : ∀ ⦃T : C⦄ (g : T ⟶ Y) (gf₁ : T ⟶ X₁) (gf₂ : T ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
      (hgf₂ : g ≫ f₂ = gf₂) (hg : R g) ⦃T' : C⦄ (h : T' ⟶ T) (g' : T' ⟶ Y) (g'f₁ : T' ⟶ X₁)
      (g'f₂ : T' ⟶ X₂) (hg'f₁ : g' ≫ f₁ = g'f₁) (hg'f₂ : g' ≫ f₂ = g'f₂) (hg' : R g')
      (e : h ≫ g = g'),
      pullHom (s g gf₁ gf₂ hgf₁ hgf₂ hg) h g'f₁ g'f₂ (by rw [← hgf₁, ← hg'f₁, ← e, Category.assoc])
        (by rw [← hgf₂, ← hg'f₂, ← e, Category.assoc]) = s g' g'f₁ g'f₂ hg'f₁ hg'f₂ hg') :
    (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂ :=
  (exists_pullHom_eq hR s hs).choose

/-- The pullbacks of the glued local morphism are the given local morphisms. -/
lemma pullHom_glue {R : Sieve Y} (hR : R ∈ J Y)
    (s : ∀ ⦃T : C⦄ (g : T ⟶ Y) (gf₁ : T ⟶ X₁) (gf₂ : T ⟶ X₂), g ≫ f₁ = gf₁ → g ≫ f₂ = gf₂ →
      R g → ((F.map gf₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map gf₂.op.toLoc).toFunctor.obj M₂))
    (hs : ∀ ⦃T : C⦄ (g : T ⟶ Y) (gf₁ : T ⟶ X₁) (gf₂ : T ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
      (hgf₂ : g ≫ f₂ = gf₂) (hg : R g) ⦃T' : C⦄ (h : T' ⟶ T) (g' : T' ⟶ Y) (g'f₁ : T' ⟶ X₁)
      (g'f₂ : T' ⟶ X₂) (hg'f₁ : g' ≫ f₁ = g'f₁) (hg'f₂ : g' ≫ f₂ = g'f₂) (hg' : R g')
      (e : h ≫ g = g'),
      pullHom (s g gf₁ gf₂ hgf₁ hgf₂ hg) h g'f₁ g'f₂ (by rw [← hgf₁, ← hg'f₁, ← e, Category.assoc])
        (by rw [← hgf₂, ← hg'f₂, ← e, Category.assoc]) = s g' g'f₁ g'f₂ hg'f₁ hg'f₂ hg')
    ⦃T : C⦄ (g : T ⟶ Y) (gf₁ : T ⟶ X₁) (gf₂ : T ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) (hg : R g) :
    pullHom (glue hR s hs) g gf₁ gf₂ hgf₁ hgf₂ = s g gf₁ gf₂ hgf₁ hgf₂ hg :=
  (exists_pullHom_eq hR s hs).choose_spec g gf₁ gf₂ hgf₁ hgf₂ hg

end IsPrestack

end CategoryTheory.Pseudofunctor
