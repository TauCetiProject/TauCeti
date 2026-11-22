/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FinitePresentation.Coherent.Basic
public import TauCeti.CategoryTheory.Abelian.Progenerator.Basic

/-!
# Coherence of the endomorphism ring of a progenerator

If `P` is a progenerator of an abelian category `C`, the progenerator equivalence
`TauCeti.IsProgenerator.progeneratorEquivalence` identifies `C` with the full subcategory of
finitely presented `(End P)ᵐᵒᵖ`-modules. Since `C` has kernels, so does this full subcategory,
and Chase's coherence theorem (`TauCeti.hasKernels_finitePresentationModules_iff_isCoherentRing`)
shows that `(End P)ᵐᵒᵖ` is left coherent.

## Main results

* `TauCeti.IsProgenerator.isCoherentRing_end_mulOpposite`: for any progenerator `P` of an abelian
  category, `(End P)ᵐᵒᵖ` is left coherent.

## References

* Henning Krause, *Krull-Schmidt categories and projective covers*, Expo. Math. 33 (2015),
  535–549, Proposition 2.3 and Proposition 3.10.
-/

public section

namespace TauCeti.IsProgenerator

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

attribute [local instance] Abelian.hasFiniteBiproducts

variable {P : C}

/-- **Coherence of the endomorphism ring of a progenerator.** If `P` is a progenerator of an abelian
category `C`, then `(End P)ᵐᵒᵖ` is left coherent: the full subcategory of finitely presented
`(End P)ᵐᵒᵖ`-modules is equivalent to `C` and therefore has kernels. -/
theorem isCoherentRing_end_mulOpposite (hP : IsProgenerator P) : IsCoherentRing (End P)ᵐᵒᵖ := by
  have : HasEqualizers (finitePresentationModules (End P)ᵐᵒᵖ).FullSubcategory :=
    Adjunction.hasLimitsOfShape_of_equivalence hP.progeneratorEquivalence.inverse
  exact hasKernels_finitePresentationModules_iff_isCoherentRing.mp inferInstance

end TauCeti.IsProgenerator
