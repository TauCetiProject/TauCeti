/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions

/-!
# Functorial left resolutions give left derivability structures

Let `Φ : LocalizerMorphism W₁ W₂` be a morphism of localizers equipped with a left resolution
functor `ρ : C₂ ⥤ C₁` and a natural transformation `π : ρ ⋙ Φ.functor ⟶ 𝟭 C₂` whose components
belong to `W₂`. Then:
* every morphism in `C₂` admits a left resolution in the arrow category;
* when `Φ.functor` is full and `W₂` is multiplicative, the category `Φ.LeftResolution X₂` of left
  resolutions of each `X₂ : C₂` is connected;
* when `Φ.functor` is fully faithful, `W₁ = W₂.inverseImage Φ.functor`, and `W₂` satisfies the
  two-out-of-three property, `Φ` induces an equivalence on localized categories;
* under both sets of hypotheses, `Φ` is a left derivability structure.

This provides the left-resolution counterpart to Joël Riou's right-resolution constructor in
`Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions`.

## Main results

* `CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_iff_op`: a localizer morphism is a
  localized equivalence if and only if its opposite is.
* `CategoryTheory.LocalizerMorphism.hasLeftResolutions_arrow_of_functorial_resolutions`: functorial
  left resolutions supply left resolutions of arrows.
* `CategoryTheory.LocalizerMorphism.isConnected_leftResolution_of_functorial_resolutions`: when
  `Φ.functor` is full and `W₂` is multiplicative, each left-resolution category is connected.
* `CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_of_functorial_left_resolutions`: a fully
  faithful induced localizer morphism admitting functorial left resolutions is a localized
  equivalence.
* `CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_of_functorial_resolutions`:
  functorial left resolutions yield a left derivability structure.

## References

* Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*, Adv. Math. 218 (2008),
  1286–1318.
-/

public section

namespace CategoryTheory.LocalizerMorphism

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  (Φ : LocalizerMorphism W₁ W₂)

/-- A localizer morphism induces an equivalence on localized categories if and only if its opposite
localizer morphism does. -/
lemma isLocalizedEquivalence_iff_op :
    Φ.IsLocalizedEquivalence ↔ Φ.op.IsLocalizedEquivalence := by
  refine ⟨fun _ ↦ inferInstance, fun _ ↦ ?_⟩
  let G := Φ.localizedFunctor W₁.Q W₂.Q
  let : CatCommSq Φ.op.functor W₁.Q.op W₂.Q.op G.op :=
    ⟨NatIso.op (CatCommSq.iso Φ.functor W₁.Q W₂.Q G).symm⟩
  have : G.op.IsEquivalence := Φ.op.isEquivalence W₁.Q.op W₂.Q.op G.op
  exact ⟨G.op.asEquivalence.unop.isEquivalence_functor⟩

variable {ρ : C₂ ⥤ C₁} (π : ρ ⋙ Φ.functor ⟶ 𝟭 C₂) (hπ : ∀ X₂, W₂ (π.app X₂))

include hπ

/-- Functorial left resolutions supply left resolutions in the category of arrows. -/
lemma hasLeftResolutions_arrow_of_functorial_resolutions :
    Φ.arrow.HasLeftResolutions :=
  fun f ↦
    ⟨{ X₁ := Arrow.mk (ρ.map f.hom)
       w := Arrow.homMk (π.app _) (π.app _) (by
         have h := (π.naturality f.hom).symm
         dsimp at h ⊢
         exact h)
       hw := ⟨hπ _, hπ _⟩ }⟩

/-- Under functorial left resolutions with `Φ.functor` full and `W₂` multiplicative, the category
`Φ.LeftResolution X₂` of left resolutions of every object `X₂` is connected. -/
lemma isConnected_leftResolution_of_functorial_resolutions
    [Φ.functor.Full] [W₂.IsMultiplicative] (X₂ : C₂) :
    IsConnected (Φ.LeftResolution X₂) := by
  have : Nonempty (Φ.LeftResolution X₂) := ⟨LeftResolution.mk (π.app X₂) (hπ X₂)⟩
  have hzig : ∀ R : Φ.LeftResolution X₂, Zigzag R (LeftResolution.mk (π.app X₂) (hπ X₂)) := by
    intro R
    let R' : Φ.LeftResolution X₂ :=
      LeftResolution.mk (π.app (Φ.functor.obj R.X₁) ≫ R.w) (W₂.comp_mem _ _ (hπ _) R.hw)
    let f₁ : R' ⟶ R := LeftResolution.Hom.mk
      (Φ.functor.preimage (show Φ.functor.obj R'.X₁ ⟶ Φ.functor.obj R.X₁ from
        π.app (Φ.functor.obj R.X₁)))
      (by simp [R'])
    let f₂ : R' ⟶ LeftResolution.mk (π.app X₂) (hπ X₂) := LeftResolution.Hom.mk
      (ρ.map R.w) (by
        have h := π.naturality R.w
        dsimp [R'] at h ⊢
        exact h)
    exact (Zigzag.of_inv f₁).trans (Zigzag.of_hom f₂)
  have : IsPreconnected (Φ.LeftResolution X₂) :=
    zigzag_isPreconnected fun R₁ R₂ ↦ (hzig R₁).trans (hzig R₂).symm
  constructor

variable (hW₁ : W₁ = W₂.inverseImage Φ.functor)
  [Φ.functor.Full] [Φ.functor.Faithful] [W₂.HasTwoOutOfThreeProperty]

include hW₁

/-- If `Φ` is a fully faithful localizer morphism with `W₁ = W₂.inverseImage Φ.functor` admitting
functorial left resolutions, then `Φ` induces an equivalence on localized categories. -/
lemma isLocalizedEquivalence_of_functorial_left_resolutions :
    Φ.IsLocalizedEquivalence := by
  have hW₁' : W₁.op = W₂.op.inverseImage Φ.op.functor := by
    ext
    simp [hW₁]
  rw [Φ.isLocalizedEquivalence_iff_op]
  exact Φ.op.isLocalizedEquivalence_of_functorial_right_resolutions (ρ := ρ.op) (NatTrans.op π)
    (fun X₂ ↦ hπ X₂.unop) hW₁'

/-- A fully faithful localizer morphism with `W₁ = W₂.inverseImage Φ.functor` admitting functorial
left resolutions is a left derivability structure. -/
lemma isLeftDerivabilityStructure_of_functorial_resolutions [W₂.IsMultiplicative] :
    Φ.IsLeftDerivabilityStructure := by
  have hW₁' : W₁.op = W₂.op.inverseImage Φ.op.functor := by
    ext
    simp [hW₁]
  rw [Φ.isLeftDerivabilityStructure_iff_op]
  exact Φ.op.isRightDerivabilityStructure_of_functorial_resolutions (ρ := ρ.op) (NatTrans.op π)
    (fun Y₂ ↦ hπ Y₂.unop) hW₁'

end CategoryTheory.LocalizerMorphism
