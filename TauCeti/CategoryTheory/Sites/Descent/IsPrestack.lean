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
functor `p : D ⥤ C`
(`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_toPseudofunctor_comp`), and
establishes general gluing and closure properties for `IsPrestack` and `IsPrestackFor` by lifting
Mathlib's sheaf criteria (`Presieve.isSheafFor_trans`, `Presieve.isSheafFor_of_factorsThru`, and
`GrothendieckTopology.OneHypercover.isSheafFor_sieve_of_pullback` by Christian Merten) to
`F.presheafHom`.

## Main results

* `CategoryTheory.Pseudofunctor.presheafHom_map_presheafHomObjHomEquiv`: restricting the element
  of `F.presheafHom M N` given by `φ : M ⟶ N` to `(Y, f)` gives `f^* φ`.
* `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_toPseudofunctor_comp`: pulling back
  a morphism between pullbacks commutes with restricting `F` along a functor `p : D ⥤ C`.
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
* The Stacks Project, Section 8.4, *Stacks*, Tag 026F.
-/

public section

universe t t' v' v u' u

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor

section

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

/-- Joint injectivity of restriction on morphisms in `F(Y.left)` along a sieve `R` implies that
`F.presheafHom M N` is separated for the corresponding sieve on `Y : Over S₀`. -/
private lemma isSeparatedFor_presheafHom_of_hom_ext {S₀ : C} (M N : F.obj (.mk (op S₀)))
    (Y : Over S₀) (R : Sieve Y.left)
    (hR : ∀ ⦃M' N' : F.obj (.mk (op Y.left))⦄ {φ ψ : M' ⟶ N'},
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
        (h₂ g.left hg), ?_⟩
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
    exact isSeparatedFor_presheafHom_of_hom_ext M N _ _ (h₂ k)

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
