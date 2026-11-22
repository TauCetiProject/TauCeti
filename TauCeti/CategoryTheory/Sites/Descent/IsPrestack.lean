/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.CategoryTheory.Sites.Hypercover.One
public import TauCeti.CategoryTheory.Bicategory.Functor.LocallyDiscrete

import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes
import TauCeti.CategoryTheory.Sites.Over

/-!
# Prestack restriction, gluing, and closure properties

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a pseudofunctor and `M`, `N` objects of `F` over `S`.
Mathlib's presheaf of morphisms `Pseudofunctor.presheafHom M N` on `Over S` has value
`f^* M ⟶ f^* N` at `(Y, f)`, and its value at the terminal object `Over.mk (𝟙 S)` is identified with
`M ⟶ N` by `Pseudofunctor.presheafHomObjHomEquiv`. This file shows that restricting the element
given by `φ : M ⟶ N` to `(Y, f)` gives `f^* φ`
(`CategoryTheory.Pseudofunctor.presheafHom_map_presheafHomObjHomEquiv`). So a morphism `φ` is an
amalgamation of a family of local morphisms exactly when its pullbacks are the members of the
family, which is how the sheaf condition of `presheafHom M N` (the prestack condition) is checked.

It also shows that pulling back morphisms between pullbacks commutes with restricting `F` along a
functor `p : D ⥤ C`: for the pseudofunctor `p.op.toPseudofunctor.comp F`, pulling back along `g`
is pulling back along `p.map g` for `F`
(`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_toPseudofunctor_comp`).

For a prestack `F` for a Grothendieck topology `J`, this gives the descent of morphisms along a
covering sieve in the form used to build descent data by hand: a morphism is determined by its
pullbacks to the members of a covering sieve (`IsPrestack.hom_ext`, `IsPrestack.pullHom_ext`),
and a family of local morphisms compatible under pullback glues to a morphism
(`IsPrestack.glue`, `IsPrestack.pullHom_glue`). The local morphisms are written with Mathlib's
`LocallyDiscreteOpToCat.pullHom`, whose composition is computed by `pullHom_comp`. It also
establishes general gluing and closure properties for `IsPrestack` and `IsPrestackFor` by lifting
Mathlib's sheaf criteria (`Presieve.isSheafFor_trans`, `Presieve.isSheafFor_of_factorsThru`, and
`GrothendieckTopology.OneHypercover.isSheafFor_sieve_of_pullback` by Christian Merten) to
`F.presheafHom`.

## Main results

* `CategoryTheory.Pseudofunctor.presheafHom_map_presheafHomObjHomEquiv`: restricting the element
  of `F.presheafHom M N` given by `φ : M ⟶ N` to `(Y, f)` gives `f^* φ`.
* `CategoryTheory.Pseudofunctor.isSeparatedFor_presheafHom_of_hom_ext`: joint injectivity of
  restriction on morphisms in `F(Y.left)` along a sieve `R` implies separation of
  `F.presheafHom M N` for the corresponding sieve on `Y : Over S₀`.
* `CategoryTheory.Pseudofunctor.pullHom_comp`,
  `CategoryTheory.Pseudofunctor.pullHom_id_self`,
  `CategoryTheory.Pseudofunctor.pullHom_map`,
  `CategoryTheory.Pseudofunctor.pullHom_mapComp'_hom`,
  `CategoryTheory.Pseudofunctor.pullHom_mapComp'_inv`,
  `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_toPseudofunctor_comp`:
  composition, identity, comparison, and restriction laws for `pullHom`.
* `CategoryTheory.Pseudofunctor.map_map_eq_iff_map_comp`: equality of morphisms after iterated
  restriction along `f` then `g` is equivalent to equality after restriction along `g ≫ f`.
* `CategoryTheory.Pseudofunctor.IsPrestack.hom_ext`,
  `CategoryTheory.Pseudofunctor.IsPrestack.pullHom_ext`,
  `CategoryTheory.Pseudofunctor.IsPrestack.glue`,
  `CategoryTheory.Pseudofunctor.IsPrestack.pullHom_glue`: separation and gluing of morphisms
  over covering sieves of a prestack.
* `CategoryTheory.Pseudofunctor.IsPrestack.of_le`: a prestack for a finer Grothendieck topology
  is a prestack for any coarser topology.
* `CategoryTheory.Pseudofunctor.isPrestackFor_top`: every pseudofunctor satisfies descent of
  morphisms for the maximal presieve `⊤`.
* `CategoryTheory.Pseudofunctor.IsPrestackFor.hom_ext`,
  `CategoryTheory.Pseudofunctor.IsPrestackFor.existsUnique_map_eq`: separation and gluing of
  morphisms over a presieve or sieve satisfying `F.IsPrestackFor`.
* `CategoryTheory.Pseudofunctor.IsPrestackFor.comp`: transitivity of `IsPrestackFor` along
  `J`-covering compositions when `F` is a `J`-prestack.
* `CategoryTheory.Pseudofunctor.IsPrestackFor.of_le`,
  `CategoryTheory.Pseudofunctor.IsPrestackFor.of_le'`: refinement for `IsPrestackFor` along an
  inclusion of presieves or sieves `R₁ ≤ R₂` whose pullbacks along arrows of `R₂` satisfy
  joint injectivity of restriction on morphisms.
* `CategoryTheory.Pseudofunctor.IsPrestackFor.of_pullback`,
  `CategoryTheory.Pseudofunctor.IsPrestackFor.of_pullback'`: base-change locality of
  `IsPrestackFor` along a `J`-`1`-hypercover when `F` is a `J`-prestack.

## References

* Jean Giraud, *Cohomologie non abélienne*, Chapter II, §1.2.
* [Stacks Project, Definition 026F](https://stacks.math.columbia.edu/tag/026F)
-/

public section

universe t t' v' v u' u

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor

section

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

/-- Joint injectivity of restriction on morphisms in `F(Y.left)` along a sieve `R` implies that
`F.presheafHom M N` is separated for the corresponding sieve on `Y : Over S₀`. -/
lemma isSeparatedFor_presheafHom_of_hom_ext {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat} {S₀ : C}
    (M N : F.obj (.mk (op S₀))) (Y : Over S₀) (R : Sieve Y.left)
    (hR : ∀ {φ ψ : (F.map Y.hom.op.toLoc).toFunctor.obj M ⟶
        (F.map Y.hom.op.toLoc).toFunctor.obj N},
      (∀ ⦃Z : C⦄ (r : Z ⟶ Y.left), R r →
        (F.map r.op.toLoc).toFunctor.map φ = (F.map r.op.toLoc).toFunctor.map ψ) → φ = ψ) :
    Presieve.IsSeparatedFor (F.presheafHom M N) ((Sieve.overEquiv Y).symm R).arrows := by
  intro x φ ψ hφ hψ
  refine hR fun Z r hr ↦ ?_
  have hr' : ((Sieve.overEquiv Y).symm R).arrows (Over.homMk r rfl : Over.mk (r ≫ Y.hom) ⟶ Y) :=
    (Sieve.overEquiv_symm_iff R _).2 hr
  have h' : pullHom φ r (r ≫ Y.hom) (r ≫ Y.hom) rfl rfl =
      pullHom ψ r (r ≫ Y.hom) (r ≫ Y.hom) rfl rfl :=
    (hφ _ hr').trans (hψ _ hr').symm
  rw [map_eq_pullHom φ r (r ≫ Y.hom) (r ≫ Y.hom) rfl rfl,
    map_eq_pullHom ψ r (r ≫ Y.hom) (r ≫ Y.hom) rfl rfl, h']

/-- Two morphisms `M ⟶ N` over `Z` have equal iterated pullbacks along `f : Y ⟶ Z` and `g : X ⟶ Y`
if and only if they have equal pullbacks along `g ≫ f`. -/
lemma map_map_eq_iff_map_comp {X Y Z : C} (f : Y ⟶ Z) (g : X ⟶ Y)
    {M N : F.obj (.mk (op Z))} {φ ψ : M ⟶ N} :
    (F.map g.op.toLoc).toFunctor.map ((F.map f.op.toLoc).toFunctor.map φ) =
      (F.map g.op.toLoc).toFunctor.map ((F.map f.op.toLoc).toFunctor.map ψ) ↔
      (F.map (g ≫ f).op.toLoc).toFunctor.map φ =
        (F.map (g ≫ f).op.toLoc).toFunctor.map ψ := by
  rw [← F.mapComp'_naturality_1 f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]) φ,
    ← F.mapComp'_naturality_1 f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]) ψ,
    cancel_epi, cancel_mono]

namespace LocallyDiscreteOpToCat

variable {D : Type*} [Category* D] (p : D ⥤ C)

/-- Pulling back a morphism between pullbacks along a morphism `g` of `D`, for the restriction
`p.op.toPseudofunctor.comp F` of `F` along `p : D ⥤ C`, is pulling it back along `p.map g` for
`F`. -/
lemma pullHom_toPseudofunctor_comp ⦃X₁ X₂ : D⦄
    ⦃M₁ : (p.op.toPseudofunctor.comp F).obj (.mk (op X₁))⦄
    ⦃M₂ : (p.op.toPseudofunctor.comp F).obj (.mk (op X₂))⦄ ⦃Y : D⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : ((p.op.toPseudofunctor.comp F).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      ((p.op.toPseudofunctor.comp F).map f₂.op.toLoc).toFunctor.obj M₂)
    ⦃Y' : D⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom φ g gf₁ gf₂ hgf₁ hgf₂ =
      pullHom (F := F) (X₁ := p.obj X₁) (X₂ := p.obj X₂) (M₁ := M₁) (M₂ := M₂) (f₁ := p.map f₁)
        (f₂ := p.map f₂) φ (p.map g) (p.map gf₁) (p.map gf₂) (by rw [← hgf₁, p.map_comp])
        (by rw [← hgf₂, p.map_comp]) := by
  unfold pullHom
  rw [comp_mapComp'_eq_mapComp' _ _ f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (by rw [← hgf₁]; rfl),
    comp_mapComp'_eq_mapComp' _ _ f₂.op.toLoc g.op.toLoc gf₂.op.toLoc (by rw [← hgf₂]; rfl)]
  -- Both sides now use the comparisons of `F`; the pullback functors along `g.op.toLoc` for the
  -- restriction and along `(p.map g).op.toLoc` for `F` agree by unfolding `Pseudofunctor.comp`.
  rfl

end LocallyDiscreteOpToCat

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
      rw [← hs g _ _ rfl rfl hg h _ _ _ rfl rfl hg' rfl,
        pullHom_comp _ _ h (h ≫ g) ((h ≫ g) ≫ f₁) (h ≫ g) rfl (Category.assoc _ _ _).symm rfl,
        pullHom_comp _ _ h ((h ≫ g) ≫ f₁) ((h ≫ g) ≫ f₂) (h ≫ g) (Category.assoc _ _ _).symm
          (Category.assoc _ _ _).symm rfl]
      simp only [pullHom_mapComp'_inv, pullHom_mapComp'_hom])
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

end

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

/-- A prestack for a Grothendieck topology `J₂` is a prestack for any coarser topology `J₁ ≤ J₂`.
-/
lemma IsPrestack.of_le {J₁ J₂ : GrothendieckTopology C} (h : J₁ ≤ J₂) [F.IsPrestack J₂] :
    F.IsPrestack J₁ :=
  .of_isPrestackFor fun _ R hR ↦ F.isPrestackFor' R (h _ hR)

variable (F) in
/-- Every pseudofunctor satisfies descent of morphisms for the maximal presieve `⊤`. -/
@[simp]
lemma isPrestackFor_top (S : C) : F.IsPrestackFor (⊤ : Presieve S) := by
  rw [← IsPrestackFor_generate_iff, Sieve.generate_top, isPrestackFor_iff_isSheafFor]
  intro M N
  simpa using Presieve.isSheafFor_top (F.presheafHom M N)

/-- If `F` satisfies descent of morphisms for a presieve `R`, two morphisms `M₁ ⟶ M₂` in
`F.obj (.mk (op W))` are equal if their pullbacks along every morphism in `R` agree. -/
lemma IsPrestackFor.hom_ext {W : C} {M₁ M₂ : F.obj (.mk (op W))} {R : Presieve W}
    (hR : F.IsPrestackFor R) {φ ψ : M₁ ⟶ M₂}
    (h : ∀ ⦃Z : C⦄ (r : Z ⟶ W), R r →
      (F.map r.op.toLoc).toFunctor.map φ = (F.map r.op.toLoc).toFunctor.map ψ) :
    φ = ψ :=
  hR.fullyFaithful.map_injective (DescentData.hom_ext fun r ↦ h r.obj.hom r.property)

/-- If `F` satisfies descent of morphisms for a sieve `R`, a family of morphisms
`r^* M₁ ⟶ r^* M₂` over `R` that is compatible with `pullHom` descends to a unique morphism
`M₁ ⟶ M₂`. -/
lemma IsPrestackFor.existsUnique_map_eq {W : C} {M₁ M₂ : F.obj (.mk (op W))} {R : Sieve W}
    (hR : F.IsPrestackFor R.arrows)
    (m : ∀ ⦃Z : C⦄ (r : Z ⟶ W), R r →
      ((F.map r.op.toLoc).toFunctor.obj M₁ ⟶ (F.map r.op.toLoc).toFunctor.obj M₂))
    (hm : ∀ ⦃Z' Z : C⦄ (g : Z' ⟶ Z) (r : Z ⟶ W) (hr : R r),
      m (g ≫ r) (R.downward_closed hr g) = pullHom (m r hr) g (g ≫ r) (g ≫ r) rfl rfl) :
    ∃! φ : M₁ ⟶ M₂, ∀ ⦃Z : C⦄ (r : Z ⟶ W) (hr : R r),
      (F.map r.op.toLoc).toFunctor.map φ = m r hr := by
  have hsh := (F.isPrestackFor_iff_isSheafFor R).1 hR M₁ M₂
  have mem_hom {Z : Over W} {g : Z ⟶ Over.mk (𝟙 W)}
      (hg : ((Sieve.overEquiv (Over.mk (𝟙 W))).symm R).arrows g) : R Z.hom := by
    have hg' : R g.left := (Sieve.overEquiv_symm_iff R g).1 hg
    rw [← Over.w g]
    simpa using hg'
  let x : Presieve.FamilyOfElements (F.presheafHom M₁ M₂)
      ((Sieve.overEquiv (Over.mk (𝟙 W))).symm R).arrows := fun _ _ hg ↦ m _ (mem_hom hg)
  have hx : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Z Z' g f hg
    have haux : ∀ {w : Z'.left ⟶ W} (hw : f.left ≫ Z.hom = w),
        m w (by rw [← hw]; exact R.downward_closed (mem_hom hg) f.left) =
          pullHom (m Z.hom (mem_hom hg)) f.left w w (by simp [hw]) (by simp [hw]) := by
      rintro w rfl
      exact hm f.left Z.hom (mem_hom hg)
    exact haux (Over.w f)
  obtain ⟨y, hy, _⟩ := hsh x hx
  let φ : M₁ ⟶ M₂ := F.presheafHomObjHomEquiv.symm y
  have hφ : ∀ ⦃Z : C⦄ (r : Z ⟶ W) (hr : R r), (F.map r.op.toLoc).toFunctor.map φ = m r hr := by
    intro Z r hr
    let g : Over.mk r ⟶ Over.mk (𝟙 W) := Over.homMk r (Category.comp_id r)
    have hmem : ((Sieve.overEquiv (Over.mk (𝟙 W))).symm R).arrows g :=
      (Sieve.overEquiv_symm_iff R g).2 hr
    have h1 := hy g hmem
    rw [← Equiv.apply_symm_apply F.presheafHomObjHomEquiv y,
      presheafHom_map_presheafHomObjHomEquiv] at h1
    exact h1
  exact ⟨φ, hφ, fun ψ hψ ↦ hR.hom_ext fun Z r hr ↦ (hψ r hr).trans (hφ r hr).symm⟩

/-- **Transitivity of `IsPrestackFor` along `J`-covering compositions.** If `F` is a prestack for
`J`, `F` satisfies descent of morphisms for `p : ∀ j, Y j ⟶ S`, and each `u j : ∀ k, X j k ⟶ Y j`
is a `J`-covering family, then `F` satisfies descent of morphisms for the composite family
`u j k ≫ p j`. -/
theorem IsPrestackFor.comp {J : GrothendieckTopology C} [F.IsPrestack J]
    {S : C} {κ : Type t} {Y : κ → C} {p : ∀ j, Y j ⟶ S} (hp : F.IsPrestackFor (.ofArrows Y p))
    {ι : κ → Type t'} {X : ∀ j, ι j → C} (u : ∀ j k, X j k ⟶ Y j)
    (hu : ∀ j, Sieve.ofArrows (X j) (u j) ∈ J (Y j)) :
    F.IsPrestackFor (.ofArrows (fun jk : Σ j, ι j ↦ X jk.1 jk.2)
      (fun jk ↦ u jk.1 jk.2 ≫ p jk.1)) := by
  let S₁ : Sieve S := Sieve.ofArrows Y p
  let S₂ : Sieve S := Sieve.ofArrows (fun jk : Σ j, ι j ↦ X jk.1 jk.2)
    (fun jk ↦ u jk.1 jk.2 ≫ p jk.1)
  have hle : S₂ ≤ S₁ := (Sieve.generate_le_iff _ _).2 (Presieve.ofArrows_le_iff.2 fun jk ↦
    ⟨Y jk.1, u jk.1 jk.2, p jk.1, Presieve.ofArrows.mk jk.1, rfl⟩)
  rw [← IsPrestackFor_generate_iff, isPrestackFor_iff_isSheafFor]
  intro M N
  refine Presieve.isSheafFor_trans (F.presheafHom M N)
    ((Sieve.overEquiv (Over.mk (𝟙 S))).symm S₁)
    ((Sieve.overEquiv (Over.mk (𝟙 S))).symm S₂)
    ((F.isPrestackFor_iff_isSheafFor S₁).1 ((F.IsPrestackFor_generate_iff _).2 hp) M N)
    (fun Z f hf ↦ ?_) (fun Z f hf ↦ ?_)
  · rw [Sieve.pullback_eq_top_of_mem _ ((Sieve.overEquiv _).symm.monotone hle _ hf)]
    exact Presieve.isSeparatedFor_top _
  · obtain ⟨_, a, _, ⟨j⟩, ha⟩ := (Sieve.overEquiv_symm_iff S₁ f).1 hf
    have hmem : S₂.pullback f.left ∈ J Z.left := by
      refine J.superset_covering ?_ (J.pullback_stable a (hu j))
      rintro W r ⟨_, b, _, ⟨k⟩, hb⟩
      exact ⟨X j k, b, u j k ≫ p j, Presieve.ofArrows.mk (⟨j, k⟩ : Σ j, ι j),
        by rw [← Category.assoc, hb, Category.assoc, ha]⟩
    refine IsPrestackFor.isSheafFor' Z ?_ M N
    rw [Sieve.overEquiv_pullback, OrderIso.apply_symm_apply]
    exact F.isPrestackFor' _ hmem

/-- **Refinement for `IsPrestackFor`.** If `R₁ ≤ R₂` are presieves on `S`, `F` satisfies descent of
morphisms for `R₁`, and restriction along `(Sieve.generate R₁).pullback g` is jointly injective on
morphisms for every arrow `g` in `R₂`, then `F` satisfies descent of morphisms for `R₂`. -/
theorem IsPrestackFor.of_le {S : C} {R₁ R₂ : Presieve S}
    (h₁ : F.IsPrestackFor R₁) (h : R₁ ≤ R₂)
    (h₂ : ∀ ⦃Y : C⦄ (g : Y ⟶ S), R₂ g →
      ∀ ⦃M N : F.obj (.mk (op Y))⦄ {φ ψ : M ⟶ N},
        (∀ ⦃Z : C⦄ (r : Z ⟶ Y), (Sieve.generate R₁).pullback g r →
          (F.map r.op.toLoc).toFunctor.map φ = (F.map r.op.toLoc).toFunctor.map ψ) → φ = ψ) :
    F.IsPrestackFor R₂ := by
  rw [← IsPrestackFor_generate_iff, isPrestackFor_iff_isSheafFor] at h₁ ⊢
  intro M N
  rw [Sieve.overEquiv_symm_generate, ← Presieve.isSheafFor_iff_generate]
  have h₁' := h₁ M N
  rw [Sieve.overEquiv_symm_generate, ← Presieve.isSheafFor_iff_generate] at h₁'
  refine Presieve.isSheafFor_of_factorsThru (F.presheafHom M N)
    (Presieve.factorsThru_of_le _ _ fun _ _ hf ↦ h _ _ hf) h₁'
    fun Y g hg ↦ ⟨((Sieve.overEquiv Y).symm ((Sieve.generate R₁).pullback g.left)).arrows,
      isSeparatedFor_presheafHom_of_hom_ext M N Y ((Sieve.generate R₁).pullback g.left)
        fun {φ ψ} h ↦ h₂ g.left hg h, ?_⟩
  rintro Z f ⟨W, a, b, hb, hab⟩
  exact ⟨Over.mk b,
    Over.homMk a (by
      dsimp at hab ⊢
      rw [hab, ← Over.w f]
      simpa using congrArg (f.left ≫ ·) (Over.w g)),
    Over.homMk b (Category.comp_id b), hb, Over.OverMorphism.ext hab⟩

/-- **Refinement for `IsPrestackFor` (sieve form).** If `R₁ ≤ R₂` are sieves on `S`, `F` satisfies
descent of morphisms for `R₁`, and restriction along `R₁.pullback g` is jointly injective on
morphisms for every arrow `g` in `R₂`, then `F` satisfies descent of morphisms for `R₂`. -/
theorem IsPrestackFor.of_le' {S : C} {R₁ R₂ : Sieve S}
    (h₁ : F.IsPrestackFor R₁.arrows) (h : R₁ ≤ R₂)
    (h₂ : ∀ ⦃Y : C⦄ (g : Y ⟶ S), R₂ g →
      ∀ ⦃M N : F.obj (.mk (op Y))⦄ {φ ψ : M ⟶ N},
        (∀ ⦃Z : C⦄ (r : Z ⟶ Y), R₁.pullback g r →
          (F.map r.op.toLoc).toFunctor.map φ = (F.map r.op.toLoc).toFunctor.map ψ) → φ = ψ) :
    F.IsPrestackFor R₂.arrows :=
  h₁.of_le h fun Y g hg M N φ ψ hφ ↦ h₂ g hg fun Z r hr ↦ hφ r (by simpa using hr)

/-- **Base-change locality for `IsPrestackFor` along a `1`-hypercover (sieve form).** If `F` is a
prestack for `J`, `E` is a `J`-`1`-hypercover of `S`, and a sieve `R` on `S` satisfies
`IsPrestackFor` after pullback along every `E.f i` and joint injectivity of restriction after
pullback along every `E.p₁ k ≫ E.f i`, then `F.IsPrestackFor R.arrows`. -/
theorem IsPrestackFor.of_pullback' {J : GrothendieckTopology C} [F.IsPrestack J]
    {S : C} {R : Sieve S} (E : J.OneHypercover.{t} S)
    (h₁ : ∀ i, F.IsPrestackFor (R.pullback (E.f i)).arrows)
    (h₂ : ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j),
      ∀ ⦃M N : F.obj (.mk (op (E.Y k)))⦄ {φ ψ : M ⟶ N},
        (∀ ⦃Z : C⦄ (r : Z ⟶ E.Y k), R.pullback (E.p₁ k ≫ E.f i) r →
          (F.map r.op.toLoc).toFunctor.map φ = (F.map r.op.toLoc).toFunctor.map ψ) → φ = ψ) :
    F.IsPrestackFor R.arrows := by
  rw [isPrestackFor_iff_isSheafFor]
  intro M N
  refine (E.over (Over.mk (𝟙 S))).isSheafFor_sieve_of_pullback
    ((isSheaf_iff_isSheaf_of_type _ _).1 (IsPrestack.isSheaf J M N)) (fun i ↦ ?_) (fun i j k ↦ ?_)
  · refine IsPrestackFor.isSheafFor' _ ?_ M N
    rw [Sieve.overEquiv_pullback, OrderIso.apply_symm_apply]
    exact h₁ i
  · rw [← Sieve.overEquiv_symm_pullback]
    exact isSeparatedFor_presheafHom_of_hom_ext M N _ _ fun {φ ψ} h ↦ h₂ k h

/-- **Base-change locality for `IsPrestackFor` along a `1`-hypercover.** If `F` is a prestack for
`J`, `E` is a `J`-`1`-hypercover of `S`, and a presieve `R` on `S` satisfies `IsPrestackFor` after
pullback of `Sieve.generate R` along every `E.f i` and joint injectivity of restriction after
pullback along every `E.p₁ k ≫ E.f i`, then `F.IsPrestackFor R`. -/
theorem IsPrestackFor.of_pullback {J : GrothendieckTopology C} [F.IsPrestack J]
    {S : C} {R : Presieve S} (E : J.OneHypercover.{t} S)
    (h₁ : ∀ i, F.IsPrestackFor ((Sieve.generate R).pullback (E.f i)).arrows)
    (h₂ : ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j),
      ∀ ⦃M N : F.obj (.mk (op (E.Y k)))⦄ {φ ψ : M ⟶ N},
        (∀ ⦃Z : C⦄ (r : Z ⟶ E.Y k), (Sieve.generate R).pullback (E.p₁ k ≫ E.f i) r →
          (F.map r.op.toLoc).toFunctor.map φ = (F.map r.op.toLoc).toFunctor.map ψ) → φ = ψ) :
    F.IsPrestackFor R :=
  (F.IsPrestackFor_generate_iff R).1 (IsPrestackFor.of_pullback' E h₁ h₂)

end CategoryTheory.Pseudofunctor
