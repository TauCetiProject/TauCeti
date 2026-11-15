/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions

/-!
# Functorial left resolutions give left derivability structures

Let `Φ : LocalizerMorphism W₁ W₂` be a localizer morphism whose underlying functor
`Φ.functor : C₁ ⥤ C₂` is fully faithful, and assume that `W₁` is the inverse image of `W₂` under
`Φ.functor`. Given a left resolution functor `ρ : C₂ ⥤ C₁` equipped with a natural transformation
`p : ρ ⋙ Φ.functor ⟶ 𝟭 C₂` whose components lie in `W₂`, this file constructs:

* `CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_of_counit_of_counit`: a localizer
  morphism admitting an inverse up to natural transformations `Φ ⋙ Ψ ⟶ 𝟭` and `Ψ ⋙ Φ ⟶ 𝟭` with
  components in `W₁` and `W₂` induces an equivalence on localized categories.
* `CategoryTheory.LocalizerMorphism.hasLeftResolutions_arrow_of_functorial_resolutions`: every
  arrow of `C₂` admits a left resolution in `Arrow C₁`.
* `CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_of_functorial_left_resolutions`: `Φ`
  induces an equivalence on localized categories when `W₂` satisfies two-out-of-three.
* `CategoryTheory.LocalizerMorphism.isConnected_leftResolution_of_functorial_resolutions`: each
  left resolution category `Φ.LeftResolution X₂` is connected when `W₂` is multiplicative and
  satisfies two-out-of-three.
* `CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_of_functorial_resolutions`: `Φ` is
  a left derivability structure.

This is the dual of Joël Riou's construction of right derivability structures from functorial
right resolutions in
`Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions`
(and of `CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_of_unit_of_unit` in
`Mathlib.CategoryTheory.Localization.LocalizerMorphism`).

## References

* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]
-/

public section

namespace CategoryTheory

open Category Localization CategoryTheory.Functor

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

section Counit

variable (Φ : LocalizerMorphism W₁ W₂)

/-- If a localizer morphism `Φ : LocalizerMorphism W₁ W₂` admits a localizer morphism
`Ψ : LocalizerMorphism W₂ W₁` in the opposite direction together with natural transformations
`η₁ : Φ.functor ⋙ Ψ.functor ⟶ 𝟭 C₁` and `η₂ : Ψ.functor ⋙ Φ.functor ⟶ 𝟭 C₂` whose components lie
in `W₁` and `W₂`, then `Φ` induces an equivalence on the localized categories. -/
lemma isLocalizedEquivalence_of_counit_of_counit (Ψ : LocalizerMorphism W₂ W₁)
    (η₁ : Φ.functor ⋙ Ψ.functor ⟶ 𝟭 C₁) (η₂ : Ψ.functor ⋙ Φ.functor ⟶ 𝟭 C₂)
    (hη₁ : ∀ X₁, W₁ (η₁.app X₁)) (hη₂ : ∀ X₂, W₂ (η₂.app X₂)) :
    Φ.IsLocalizedEquivalence where
  isEquivalence := by
    have : IsIso (whiskerRight η₁ W₁.Q) := by
      rw [NatTrans.isIso_iff_isIso_app]
      exact fun _ ↦ Localization.inverts W₁.Q W₁ _ (hη₁ _)
    have : IsIso (whiskerRight η₂ W₂.Q) := by
      rw [NatTrans.isIso_iff_isIso_app]
      exact fun _ ↦ Localization.inverts W₂.Q W₂ _ (hη₂ _)
    refine (Localization.equivalence W₁.Q W₁ W₂.Q W₂ (Φ.functor ⋙ W₂.Q)
      (Φ.localizedFunctor W₁.Q W₂.Q)
      (Ψ.functor ⋙ W₁.Q) (Ψ.localizedFunctor W₂.Q W₁.Q) ?_ ?_).isEquivalence_functor
    · exact Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (CatCommSq.iso Ψ.functor W₂.Q W₁.Q _).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        asIso (whiskerRight η₁ W₁.Q) ≪≫ Functor.leftUnitor _
    · exact Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (CatCommSq.iso Φ.functor W₁.Q W₂.Q _).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        asIso (whiskerRight η₂ W₂.Q) ≪≫ Functor.leftUnitor _

end Counit

variable (Φ : LocalizerMorphism W₁ W₂)
  {ρ : C₂ ⥤ C₁} (p : ρ ⋙ Φ.functor ⟶ 𝟭 C₂) (hp : ∀ X₂, W₂ (p.app X₂))
  (hW₁ : W₁ = W₂.inverseImage Φ.functor)

include hp in
/-- Functorial left resolutions of objects induce left resolutions of arrows. -/
lemma hasLeftResolutions_arrow_of_functorial_resolutions :
    Φ.arrow.HasLeftResolutions :=
  fun f ↦
    ⟨{ X₁ := Arrow.mk (ρ.map f.hom)
       w := Arrow.homMk (p.app _) (p.app _) (p.naturality f.hom).symm
       hw := ⟨hp _, hp _⟩ }⟩

namespace functorialLeftResolutions

variable {Φ p}

/-- When `W₁` is the inverse image of `W₂` along `Φ.functor` and `p : ρ ⋙ Φ.functor ⟶ 𝟭 C₂` is a
functorial left resolution with components in `W₂`, the resolution functor `ρ` is a localizer
morphism from `W₂` to `W₁`. -/
def localizerMorphismInv [W₂.HasTwoOutOfThreeProperty] :
    LocalizerMorphism W₂ W₁ where
  functor := ρ
  map := by
    rw [hW₁]
    intro X Y f hf
    have := p.naturality f
    dsimp at this
    simp only [MorphismProperty.inverseImage_iff]
    rw [← W₂.postcomp_iff _ _ (hp Y), this]
    exact W₂.comp_mem _ _ (hp X) hf

@[simp]
lemma localizerMorphismInv_functor [W₂.HasTwoOutOfThreeProperty] :
    (localizerMorphismInv hp hW₁).functor = ρ := (rfl)

variable [Φ.functor.Full] [Φ.functor.Faithful]

variable (p) in
/-- When `Φ.functor` is fully faithful, a functorial left resolution `p : ρ ⋙ Φ.functor ⟶ 𝟭 C₂`
induces a natural transformation `Φ.functor ⋙ ρ ⟶ 𝟭 C₁`. -/
noncomputable def π : Φ.functor ⋙ ρ ⟶ 𝟭 C₁ :=
  ((whiskeringRight C₁ C₁ C₂).obj Φ.functor).preimage (whiskerLeft Φ.functor p)

@[simp]
lemma Φ_functor_map_π_app (X₁ : C₁) :
    Φ.functor.map ((π p).app X₁) = p.app (Φ.functor.obj X₁) :=
  congr($(((whiskeringRight C₁ C₁ C₂).obj Φ.functor).map_preimage
    (X := Φ.functor ⋙ ρ) (Y := 𝟭 C₁) (whiskerLeft Φ.functor p)).app X₁)

include hW₁ hp in
lemma W₁_π_app (X₁ : C₁) : W₁ ((π p).app X₁) := by
  simpa [hW₁] using hp (Φ.functor.obj X₁)

end functorialLeftResolutions

variable [Φ.functor.Full] [Φ.functor.Faithful] [W₂.HasTwoOutOfThreeProperty]

open functorialLeftResolutions
include hp hW₁

/-- If `Φ.functor` is fully faithful, `W₁` is induced by `W₂`, and `Φ` admits functorial left
resolutions, then `Φ` induces an equivalence on localized categories. -/
lemma isLocalizedEquivalence_of_functorial_left_resolutions :
    Φ.IsLocalizedEquivalence :=
  Φ.isLocalizedEquivalence_of_counit_of_counit (localizerMorphismInv hp hW₁) (π p) p
    (W₁_π_app hp hW₁) hp

variable [W₂.IsMultiplicative]

/-- If `Φ.functor` is fully faithful, `W₁` is induced by `W₂`, and `Φ` admits functorial left
resolutions, then every left resolution category `Φ.LeftResolution X₂` is connected. -/
lemma isConnected_leftResolution_of_functorial_resolutions (X₂ : C₂) :
    letI : W₁.IsMultiplicative := by rw [hW₁]; infer_instance
    IsConnected (Φ.LeftResolution X₂) := by
  have : W₁.IsMultiplicative := by rw [hW₁]; infer_instance
  have : Nonempty (Φ.LeftResolution X₂) := ⟨{ hw := hp X₂, .. }⟩
  have : IsPreconnected (Φ.LeftResolution X₂) :=
    zigzag_isPreconnected (fun L₀ L₄ ↦
      calc
        Zigzag L₀ { hw := W₂.comp_mem _ _ (hp _) L₀.hw, .. } :=
          Zigzag.of_inv { f := (π p).app L₀.X₁ }
        Zigzag (J := Φ.LeftResolution X₂) _ { hw := hp X₂, .. } :=
          Zigzag.of_hom
            { f := ρ.map L₀.w
              comm := p.naturality L₀.w }
        Zigzag (J := Φ.LeftResolution X₂) _ { hw := W₂.comp_mem _ _ (hp _) L₄.hw, .. } :=
          Zigzag.of_inv
            { f := ρ.map L₄.w
              comm := p.naturality L₄.w }
        Zigzag _ L₄ := Zigzag.of_hom { f := (π p).app L₄.X₁ })
  constructor

/-- If `Φ.functor` is fully faithful, `W₁` is induced by `W₂`, and `Φ` admits functorial left
resolutions, then `Φ` is a left derivability structure. -/
lemma isLeftDerivabilityStructure_of_functorial_resolutions :
    Φ.IsLeftDerivabilityStructure := by
  have : W₁.IsMultiplicative := by rw [hW₁]; infer_instance
  have := Φ.isLocalizedEquivalence_of_functorial_left_resolutions p hp hW₁
  have := Φ.hasLeftResolutions_arrow_of_functorial_resolutions p hp
  have := Φ.isConnected_leftResolution_of_functorial_resolutions p hp hW₁
  apply IsLeftDerivabilityStructure.mk'

end LocalizerMorphism

end CategoryTheory
