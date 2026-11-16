/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Basic
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions
import TauCeti.CategoryTheory.Localization.LocalizerMorphism

/-!
# Functorial left resolutions give left derivability structures

Let `Φ : LocalizerMorphism W₁ W₂` be a localizer morphism whose underlying functor
`Φ.functor : C₁ ⥤ C₂` is fully faithful, and assume that `W₁` is the inverse image of `W₂` under
`Φ.functor`. Given a left resolution functor `ρ : C₂ ⥤ C₁` equipped with a natural transformation
`p : ρ ⋙ Φ.functor ⟶ 𝟭 C₂` whose components lie in `W₂`, this file deduces by opposite-category
duality from Joël Riou's right-resolution constructors in
`Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions`:

* `CategoryTheory.LocalizerMorphism.hasLeftResolutions_arrow_of_functorial_resolutions`: every
  arrow of `C₂` admits a left resolution in `Arrow C₁`.
* `CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_of_functorial_left_resolutions`: `Φ`
  induces an equivalence on localized categories when `W₂` satisfies two-out-of-three.
* `CategoryTheory.LocalizerMorphism.isConnected_leftResolution_of_functorial_resolutions`: each
  left resolution category `Φ.LeftResolution X₂` is connected when `W₂` is multiplicative and
  satisfies two-out-of-three.
* `CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_of_functorial_resolutions`: `Φ` is
  a left derivability structure.

## References

* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]
-/

public section

namespace CategoryTheory

open Category Localization CategoryTheory.Functor

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

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

variable [Φ.functor.Full] [Φ.functor.Faithful] [W₂.HasTwoOutOfThreeProperty]

include hp hW₁

/-- If `Φ.functor` is fully faithful, `W₁` is induced by `W₂`, and `Φ` admits functorial left
resolutions, then `Φ` induces an equivalence on localized categories. -/
lemma isLocalizedEquivalence_of_functorial_left_resolutions :
    Φ.IsLocalizedEquivalence := by
  have hW₁' : W₁.op = W₂.op.inverseImage Φ.op.functor :=
    (congr_arg MorphismProperty.op hW₁).trans (MorphismProperty.op_inverseImage W₂ Φ.functor)
  exact Φ.isLocalizedEquivalence_op_iff.1
    (Φ.op.isLocalizedEquivalence_of_functorial_right_resolutions (ρ := ρ.op) (NatTrans.op p)
      (fun X₂ ↦ hp X₂.unop) hW₁')

variable [W₂.IsMultiplicative]

/-- If `Φ.functor` is fully faithful, `W₁` is induced by `W₂`, and `Φ` admits functorial left
resolutions, then every left resolution category `Φ.LeftResolution X₂` is connected. -/
lemma isConnected_leftResolution_of_functorial_resolutions (X₂ : C₂) :
    letI : W₁.IsMultiplicative := by rw [hW₁]; infer_instance
    IsConnected (Φ.LeftResolution X₂) := by
  have : W₁.IsMultiplicative := by rw [hW₁]; infer_instance
  have hW₁' : W₁.op = W₂.op.inverseImage Φ.op.functor :=
    (congr_arg MorphismProperty.op hW₁).trans (MorphismProperty.op_inverseImage W₂ Φ.functor)
  have := Φ.op.isConnected_rightResolution_of_functorial_resolutions (ρ := ρ.op) (NatTrans.op p)
    (fun X₂ ↦ hp X₂.unop) hW₁' (.op X₂)
  have := isConnected_of_equivalent (LeftResolution.opEquivalence Φ X₂).symm
  exact isConnected_of_isConnected_op

/-- If `Φ.functor` is fully faithful, `W₁` is induced by `W₂`, and `Φ` admits functorial left
resolutions, then `Φ` is a left derivability structure. -/
lemma isLeftDerivabilityStructure_of_functorial_resolutions :
    Φ.IsLeftDerivabilityStructure := by
  have hW₁' : W₁.op = W₂.op.inverseImage Φ.op.functor :=
    (congr_arg MorphismProperty.op hW₁).trans (MorphismProperty.op_inverseImage W₂ Φ.functor)
  exact Φ.isLeftDerivabilityStructure_iff_op.2
    (Φ.op.isRightDerivabilityStructure_of_functorial_resolutions (ρ := ρ.op) (NatTrans.op p)
      (fun X₂ ↦ hp X₂.unop) hW₁')

end LocalizerMorphism

end CategoryTheory
