/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions

/-!
# Left derivability structures from functorial resolutions

Dual to Mathlib's `LocalizerMorphism.isRightDerivabilityStructure_of_functorial_resolutions`, a
localizer morphism `Φ : LocalizerMorphism W₁ W₂` whose underlying functor is fully faithful and
whose source class `W₁` is the inverse image of a multiplicative class `W₂` satisfying the
two-out-of-three property is a left derivability structure whenever it admits a functorial left
resolution: a functor `ρ : C₂ ⥤ C₁` equipped with a natural transformation
`p : ρ ⋙ Φ.functor ⟶ 𝟭 C₂` whose components lie in `W₂`.

## Main results

* `CategoryTheory.LocalizerMorphism.hasLeftResolutions_arrow_of_functorial_resolutions`: a
  functorial left resolution lifts to left resolutions of morphisms.
* `CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_of_functorial_left_resolutions`: a
  functorial left resolution exhibits `Φ` as a localized equivalence.
* `CategoryTheory.LocalizerMorphism.isConnected_leftResolution_of_functorial_resolutions`: every
  category of left resolutions is connected.
* `CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_of_functorial_resolutions`: a
  functorial left resolution yields a left derivability structure.
-/

public section

namespace CategoryTheory.LocalizerMorphism

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  (Φ : LocalizerMorphism W₁ W₂)
  {ρ : C₂ ⥤ C₁} (p : ρ ⋙ Φ.functor ⟶ 𝟭 C₂) (hp : ∀ X₂, W₂ (p.app X₂))
  (hW₁ : W₁ = W₂.inverseImage Φ.functor)

/-- The opposite natural transformation `𝟭 C₂ᵒᵖ ⟶ ρ.op ⋙ Φ.op.functor` induced by a
functorial left resolution `p : ρ ⋙ Φ.functor ⟶ 𝟭 C₂`. -/
private def opNatTrans : 𝟭 C₂ᵒᵖ ⟶ ρ.op ⋙ Φ.op.functor where
  app X := (p.app X.unop).op
  naturality _ _ f := Quiver.Hom.unop_inj (p.naturality f.unop).symm

private lemma opNatTrans_mem (hp : ∀ X₂, W₂ (p.app X₂)) (X₂ : C₂ᵒᵖ) :
    W₂.op ((opNatTrans Φ p).app X₂) :=
  hp X₂.unop

private lemma op_inverseImage_eq (hW₁ : W₁ = W₂.inverseImage Φ.functor) :
    W₁.op = W₂.op.inverseImage Φ.op.functor :=
  congrArg MorphismProperty.op hW₁

/-- A localizer morphism is a localized equivalence if and only if its opposite is. -/
lemma isLocalizedEquivalence_iff_op :
    Φ.IsLocalizedEquivalence ↔ Φ.op.IsLocalizedEquivalence := by
  refine ⟨fun _ ↦ inferInstance, fun _ ↦ ⟨?_⟩⟩
  let G := Φ.localizedFunctor W₁.Q W₂.Q
  have : CatCommSq Φ.op.functor W₁.Q.op W₂.Q.op G.op :=
    ⟨NatIso.op (CatCommSq.iso Φ.functor W₁.Q W₂.Q G).symm⟩
  have : G.op.IsEquivalence := Φ.op.isEquivalence W₁.Q.op W₂.Q.op G.op
  exact G.op.asEquivalence.unop.isEquivalence_functor

include hp in
/-- A functorial left resolution yields left resolutions of arrows. -/
lemma hasLeftResolutions_arrow_of_functorial_resolutions :
    Φ.arrow.HasLeftResolutions :=
  fun f ↦
    ⟨{ X₁ := Arrow.mk (ρ.map f.hom)
       w := Arrow.homMk (p.app _) (p.app _) (p.naturality f.hom).symm
       hw := ⟨hp _, hp _⟩ }⟩

variable [Φ.functor.Full] [Φ.functor.Faithful] [W₂.HasTwoOutOfThreeProperty]

include hp hW₁ in
/-- A fully faithful localizer morphism with an induced class of weak equivalences and a functorial
left resolution induces an equivalence on localized categories. -/
lemma isLocalizedEquivalence_of_functorial_left_resolutions :
    Φ.IsLocalizedEquivalence := by
  rw [isLocalizedEquivalence_iff_op]
  exact Φ.op.isLocalizedEquivalence_of_functorial_right_resolutions (opNatTrans Φ p)
    (opNatTrans_mem Φ p hp) (op_inverseImage_eq Φ hW₁)

variable [W₂.IsMultiplicative]

include hp hW₁ in
/-- Under a functorial left resolution, the category of left resolutions of any object is
connected. -/
lemma isConnected_leftResolution_of_functorial_resolutions (X₂ : C₂) :
    letI : W₁.IsMultiplicative := by rw [hW₁]; infer_instance
    IsConnected (Φ.LeftResolution X₂) := by
  have : W₁.IsMultiplicative := by rw [hW₁]; infer_instance
  have : IsConnected (Φ.op.RightResolution (Opposite.op X₂)) :=
    Φ.op.isConnected_rightResolution_of_functorial_resolutions (opNatTrans Φ p)
      (opNatTrans_mem Φ p hp) (op_inverseImage_eq Φ hW₁) (Opposite.op X₂)
  have : IsConnected (Φ.LeftResolution X₂)ᵒᵖ :=
    isConnected_of_equivalent (LeftResolution.opEquivalence Φ X₂).symm
  exact isConnected_of_isConnected_op

include hp hW₁ in
/-- **Functorial left resolutions give a left derivability structure.** If `Φ.functor` is fully
faithful, `W₁` is the inverse image of a multiplicative class `W₂` with the two-out-of-three
property, and `p : ρ ⋙ Φ.functor ⟶ 𝟭 C₂` is a functorial left resolution in `W₂`, then `Φ` is a
left derivability structure. -/
theorem isLeftDerivabilityStructure_of_functorial_resolutions :
    Φ.IsLeftDerivabilityStructure := by
  rw [isLeftDerivabilityStructure_iff_op]
  exact Φ.op.isRightDerivabilityStructure_of_functorial_resolutions (opNatTrans Φ p)
    (opNatTrans_mem Φ p hp) (op_inverseImage_eq Φ hW₁)

end CategoryTheory.LocalizerMorphism
