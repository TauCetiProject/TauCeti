/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions

/-!
# Functorial left resolutions give left derivability structures

Let `Φ : LocalizerMorphism W₁ W₂` be a morphism of localizers whose underlying functor
`Φ.functor : C₁ ⥤ C₂` is fully faithful and induces `W₁ = W₂.inverseImage Φ.functor`. Assume
that `C₂` admits functorial left resolutions in `C₁`, given by a functor `ρ : C₂ ⥤ C₁` and a
natural transformation `p : ρ ⋙ Φ.functor ⟶ 𝟭 C₂` whose components belong to `W₂`. When `W₂` is
multiplicative and satisfies the two-out-of-three property, `Φ` is a left derivability structure
(`CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_of_functorial_resolutions`).

This is the left-resolution dual of
`Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions`. Connectedness
of the categories of left resolutions is deduced by passing to opposite categories and applying
`CategoryTheory.LocalizerMorphism.isConnected_rightResolution_of_functorial_resolutions`.

## References

* B. Kahn and G. Maltsiniotis, *Structures de dérivabilité*, Adv. Math. 218 (2008), 1286–1318,
  Lemme 6.5.
-/

public section

namespace CategoryTheory

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

/-- If morphisms of localizers `Φ : LocalizerMorphism W₁ W₂` and `Ψ : LocalizerMorphism W₂ W₁`
are equipped with natural transformations `η₁ : Φ.functor ⋙ Ψ.functor ⟶ 𝟭 C₁` and
`η₂ : Ψ.functor ⋙ Φ.functor ⟶ 𝟭 C₂` whose components lie in `W₁` and `W₂` respectively, then `Φ`
is a localized equivalence. -/
lemma isLocalizedEquivalence_of_counit_of_counit (Φ : LocalizerMorphism W₁ W₂)
    (Ψ : LocalizerMorphism W₂ W₁)
    (η₁ : Φ.functor ⋙ Ψ.functor ⟶ 𝟭 C₁) (η₂ : Ψ.functor ⋙ Φ.functor ⟶ 𝟭 C₂)
    (hη₁ : ∀ X₁, W₁ (η₁.app X₁)) (hη₂ : ∀ X₂, W₂ (η₂.app X₂)) :
    Φ.IsLocalizedEquivalence where
  isEquivalence := by
    have : IsIso (Functor.whiskerRight η₁ W₁.Q) := by
      rw [NatTrans.isIso_iff_isIso_app]
      exact fun _ ↦ Localization.inverts W₁.Q W₁ _ (hη₁ _)
    have : IsIso (Functor.whiskerRight η₂ W₂.Q) := by
      rw [NatTrans.isIso_iff_isIso_app]
      exact fun _ ↦ Localization.inverts W₂.Q W₂ _ (hη₂ _)
    refine (Localization.equivalence W₁.Q W₁ W₂.Q W₂ (Φ.functor ⋙ W₂.Q)
      (Φ.localizedFunctor W₁.Q W₂.Q) (Ψ.functor ⋙ W₁.Q) (Ψ.localizedFunctor W₂.Q W₁.Q) ?_ ?_
        ).isEquivalence_functor
    · exact Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (CatCommSq.iso Ψ.functor W₂.Q W₁.Q _).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        asIso (Functor.whiskerRight η₁ W₁.Q) ≪≫ Functor.leftUnitor _
    · exact Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (CatCommSq.iso Φ.functor W₁.Q W₂.Q _).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        asIso (Functor.whiskerRight η₂ W₂.Q) ≪≫ Functor.leftUnitor _

variable (Φ : LocalizerMorphism W₁ W₂)
  {ρ : C₂ ⥤ C₁} (p : ρ ⋙ Φ.functor ⟶ 𝟭 C₂) (hp : ∀ X₂, W₂ (p.app X₂))
  (hW₁ : W₁ = W₂.inverseImage Φ.functor)

include hp in
/-- Functorial left resolutions on `C₂` induce left resolutions in the arrow category. -/
lemma hasLeftResolutions_arrow_of_functorial_resolutions :
    Φ.arrow.HasLeftResolutions :=
  fun f ↦
    ⟨{ X₁ := Arrow.mk (ρ.map f.hom)
       w := Arrow.homMk (p.app _) (p.app _) (p.naturality f.hom).symm
       hw := ⟨hp _, hp _⟩ }⟩

namespace functorialLeftResolutions
open CategoryTheory.Functor

variable {p}

/-- If `Φ : LocalizerMorphism W₁ W₂` has `W₁ = W₂.inverseImage Φ.functor` and `ρ : C₂ ⥤ C₁`
provides functorial left resolutions via `p : ρ ⋙ Φ.functor ⟶ 𝟭 C₂`, then `ρ` defines a morphism
of localizers in the reverse direction. -/
def localizerMorphismInv [W₂.HasTwoOutOfThreeProperty] :
    LocalizerMorphism W₂ W₁ where
  functor := ρ
  map := by
    rw [hW₁]
    intro X Y f hf
    have hnat := p.naturality f
    dsimp at hnat
    simp only [MorphismProperty.inverseImage_iff]
    rw [← W₂.postcomp_iff _ _ (hp Y), hnat]
    exact W₂.comp_mem _ _ (hp X) hf

/-- The underlying functor of `localizerMorphismInv` is the resolution functor `ρ`. -/
@[simp]
lemma localizerMorphismInv_functor [W₂.HasTwoOutOfThreeProperty] :
    (localizerMorphismInv Φ hp hW₁).functor = ρ :=
  (rfl)

variable [Φ.functor.Full] [Φ.functor.Faithful]

variable (p) in
/-- If `Φ.functor` is fully faithful and `p : ρ ⋙ Φ.functor ⟶ 𝟭 C₂` gives functorial left
resolutions, this is the induced natural transformation `Φ.functor ⋙ ρ ⟶ 𝟭 C₁`. -/
noncomputable def π : Φ.functor ⋙ ρ ⟶ 𝟭 C₁ :=
  ((whiskeringRight C₁ C₁ C₂).obj Φ.functor).preimage (whiskerLeft Φ.functor p)

/-- Applying `Φ.functor` to `(π Φ p).app X₁` recovers `p.app (Φ.functor.obj X₁)`. -/
@[simp]
lemma Φ_functor_map_π_app (X₁ : C₁) :
    Φ.functor.map ((π Φ p).app X₁) = p.app (Φ.functor.obj X₁) :=
  congr($(((whiskeringRight C₁ C₁ C₂).obj Φ.functor).map_preimage
    (X := Φ.functor ⋙ ρ) (Y := 𝟭 C₁) (whiskerLeft Φ.functor p)).app X₁)

include hW₁ hp in
/-- Each component of `π Φ p` belongs to `W₁`. -/
lemma W₁_π_app (X₁ : C₁) : W₁ ((π Φ p).app X₁) := by
  simpa [hW₁] using hp (Φ.functor.obj X₁)

end functorialLeftResolutions

variable [Φ.functor.Full] [Φ.functor.Faithful] [W₂.HasTwoOutOfThreeProperty]

open functorialLeftResolutions
include hp hW₁

/-- A fully faithful localizer morphism admitting functorial left resolutions is a localized
equivalence. -/
lemma isLocalizedEquivalence_of_functorial_left_resolutions :
    Φ.IsLocalizedEquivalence :=
  Φ.isLocalizedEquivalence_of_counit_of_counit
    (localizerMorphismInv Φ hp hW₁) (π Φ p) p (W₁_π_app Φ hp hW₁) hp

variable [W₂.IsMultiplicative]

/-- Under functorial left resolutions, the category `Φ.LeftResolution X₂` of left resolutions of
any object `X₂ : C₂` is connected. -/
lemma isConnected_leftResolution_of_functorial_resolutions (X₂ : C₂) :
    letI : W₁.IsMultiplicative := by rw [hW₁]; infer_instance
    IsConnected (Φ.LeftResolution X₂) := by
  have : W₁.IsMultiplicative := by rw [hW₁]; infer_instance
  have hW₁op : W₁.op = W₂.op.inverseImage Φ.op.functor := by
    ext X Y f
    simp [hW₁]
  let pop : 𝟭 C₂ᵒᵖ ⟶ ρ.op ⋙ Φ.op.functor :=
    (Functor.opId C₂).inv ≫ NatTrans.op p ≫ (Functor.opComp ρ Φ.functor).hom
  have hpop : ∀ X : C₂ᵒᵖ, W₂.op (pop.app X) := fun X ↦ by
    simpa [pop] using hp X.unop
  have : IsConnected (Φ.op.RightResolution (Opposite.op X₂)) :=
    Φ.op.isConnected_rightResolution_of_functorial_resolutions pop hpop hW₁op
      (Opposite.op X₂)
  have : IsConnected (Φ.LeftResolution X₂)ᵒᵖ :=
    isConnected_of_equivalent (LeftResolution.opEquivalence Φ X₂).symm
  exact isConnected_of_isConnected_op

/-- A fully faithful localizer morphism `Φ : LocalizerMorphism W₁ W₂` with
`W₁ = W₂.inverseImage Φ.functor` that admits functorial left resolutions is a left derivability
structure whenever `W₂` is multiplicative and has the two-out-of-three property. -/
lemma isLeftDerivabilityStructure_of_functorial_resolutions :
    Φ.IsLeftDerivabilityStructure := by
  have : W₁.IsMultiplicative := by rw [hW₁]; infer_instance
  have := Φ.isLocalizedEquivalence_of_functorial_left_resolutions p hp hW₁
  have := Φ.hasLeftResolutions_arrow_of_functorial_resolutions p hp
  have := Φ.isConnected_leftResolution_of_functorial_resolutions p hp hW₁
  exact IsLeftDerivabilityStructure.mk' Φ

end LocalizerMorphism

end CategoryTheory
