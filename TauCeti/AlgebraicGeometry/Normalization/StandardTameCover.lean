/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Normalization
public import TauCeti.RingTheory.AdjoinRoot.StandardTameCover.Basic

import TauCeti.AlgebraicGeometry.Normalization.SpecIntegralClosure
import TauCeti.RingTheory.AdjoinRoot.StandardTameCover.Normalization

/-!
# Relative normalization of standard tame covers

## Main results

* `TauCeti.IsFiniteProductOfStandardTameCovers.overNormalizationSpecIso` identifies the
  relative normalization of the restriction of a product of standard tame covers to a principal
  open with the spectrum of the product algebra, over the base.
* `TauCeti.IsFiniteProductOfStandardTameCovers.overNormalizationSpecIso_toNormalization`
  identifies the map from the restriction to this normalization.

The comparison uses Tau Ceti's
`IsFiniteProductOfStandardTameCovers.isIntegralClosure` and
`AlgebraicGeometry.normalizationSpecIso` for Mathlib's relative
normalization `Scheme.Hom.normalization`.

## References

* [Stacks Project, Lemma 58.31.6](https://stacks.math.columbia.edu/tag/0EYH).
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.IsFiniteProductOfStandardTameCovers

universe u

variable {A C B : Type u} [CommRing A] [CommRing C] [CommRing B]
  [Algebra A C] [Algebra A B] [Algebra C B] [IsScalarTower A C B] {a : A}

/-- Over a divisor cut out by a nonzerodivisor `a` with reduced quotient, the relative
normalization of a product of standard tame covers restricted to `D(a)` is `Spec C`.
The comparison identifies both the map from the restriction and the structure map to `Spec A`.
This is the affine calculation in Stacks, Lemma 58.31.6 (0EYH). -/
@[stacks 0EYH "relative normalization of the affine standard local model"]
noncomputable def overNormalizationSpecIso (h : IsFiniteProductOfStandardTameCovers A C a)
    (ha : a ∈ nonZeroDivisors A) [IsReduced (A ⧸ Ideal.span {a})]
    [IsLocalization.Away (algebraMap A C a) B] :
    Over.mk (Spec.algebraMap A B).fromNormalization ≅ Over.mk (Spec.algebraMap A C) :=
  letI := h.isIntegralClosure ha B
  Over.isoMk (AlgebraicGeometry.normalizationSpecIso A B C)
    AlgebraicGeometry.normalizationSpecIso_hom_algebraMap

/-- The comparison over `Spec A` identifies the map from the restriction to `D(a)` with
the localization morphism to the original product of standard tame covers. -/
@[reassoc (attr := simp)]
theorem overNormalizationSpecIso_toNormalization
    (h : IsFiniteProductOfStandardTameCovers A C a) (ha : a ∈ nonZeroDivisors A)
    [IsReduced (A ⧸ Ideal.span {a})] [IsLocalization.Away (algebraMap A C a) B] :
    (Spec.algebraMap A B).toNormalization ≫ (h.overNormalizationSpecIso (B := B) ha).hom.left =
      Spec.algebraMap C B := by
  simp only [overNormalizationSpecIso, Over.isoMk_hom_left,
    AlgebraicGeometry.toNormalization_normalizationSpecIso_hom]

end TauCeti.IsFiniteProductOfStandardTameCovers
