/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Basic
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions

/-!
# Left derivability structures from functorial resolutions

This file dualizes Mathlib's
`Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions` to left
derivability structures. Given a localizer morphism `Φ : LocalizerMorphism W₁ W₂` whose underlying
functor `Φ.functor : C₁ ⥤ C₂` is fully faithful and induces `W₁` as the inverse image of `W₂`, a
functorial left resolution `p : ρ ⋙ Φ.functor ⟶ 𝟭 C₂` with components in `W₂` makes `Φ` a left
derivability structure whenever `W₂` is multiplicative and has the two-out-of-three property.

## Main results

* `CategoryTheory.LocalizerMorphism.hasLeftResolutions_arrow_of_functorial_resolutions`: functorial
  left resolutions induce left resolutions of arrows.
* `CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_of_functorial_resolutions`:
  functorial left resolutions into a fully faithful induced localizer morphism yield a left
  derivability structure.

## References

* Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*, Adv. Math. 218 (2008),
  1286–1318.
* Joël Riou's right-resolution dual in
  `Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions`.
-/

public section

namespace CategoryTheory

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂)
  {ρ : C₂ ⥤ C₁} (p : ρ ⋙ Φ.functor ⟶ 𝟭 C₂) (hp : ∀ X₂, W₂ (p.app X₂))
  (hW₁ : W₁ = W₂.inverseImage Φ.functor)

include hp in
/-- Functorial left resolutions induce left resolutions of arrows. -/
lemma hasLeftResolutions_arrow_of_functorial_resolutions :
    Φ.arrow.HasLeftResolutions :=
  fun f ↦
    ⟨{ X₁ := Arrow.mk (ρ.map f.hom)
       w := Arrow.homMk (p.app _) (p.app _) (p.naturality f.hom).symm
       hw := ⟨hp _, hp _⟩ }⟩

variable [Φ.functor.Full] [Φ.functor.Faithful] [W₂.HasTwoOutOfThreeProperty]
  [W₂.IsMultiplicative]

include hp hW₁ in
/-- A fully faithful localizer morphism carrying the induced morphism property is a left
derivability structure whenever it admits functorial left resolutions and the ambient morphism
property is multiplicative with the two-out-of-three property. -/
lemma isLeftDerivabilityStructure_of_functorial_resolutions :
    Φ.IsLeftDerivabilityStructure := by
  rw [Φ.isLeftDerivabilityStructure_iff_op]
  let i : 𝟭 C₂ᵒᵖ ⟶ ρ.op ⋙ Φ.op.functor :=
    { app X₂ := (p.app X₂.unop).op
      naturality _ _ f := by
        simpa using congrArg Quiver.Hom.op (p.naturality f.unop).symm }
  exact Φ.op.isRightDerivabilityStructure_of_functorial_resolutions i
    (fun X₂ ↦ hp X₂.unop) (by ext _ _ f; exact congr($hW₁ f.unop))

end LocalizerMorphism

end CategoryTheory
