/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Morphisms out of an affine scheme agree on a cover by basic opens

A set `s` generating the unit ideal of a commutative ring `R` gives Mathlib's affine open cover
`AlgebraicGeometry.Scheme.affineOpenCoverOfSpanRangeEqTop` of `Spec R` by the basic opens
`Spec R[1/a]`, `a ∈ s`. This file records the resulting extensionality principle for morphisms out
of `Spec R`, stated with the localization maps `R → R[1/a]`.

## Main results

* `TauCeti.AlgebraicGeometry.Spec.hom_ext_of_span_eq_top`: two morphisms `Spec R ⟶ X` which agree
  after composing with every `Spec R[1/a] ⟶ Spec R`, `a ∈ s`, are equal.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.Spec

/-- Two morphisms out of `Spec R` agree once they agree on the basic opens `Spec R[1/a]`, `a ∈ s`,
for a set `s` generating the unit ideal of `R`. -/
theorem hom_ext_of_span_eq_top {R : Type u} [CommRing R] (s : Set R) (hs : Ideal.span s = ⊤)
    {X : Scheme.{u}} {f g : Spec (.of R) ⟶ X}
    (h : ∀ a : s, Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away a.1))) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away a.1))) ≫ g) : f = g :=
  (Scheme.affineOpenCoverOfSpanRangeEqTop (R := .of R) (fun a : s ↦ a.1)
    (by rwa [Subtype.range_coe])).openCover.hom_ext _ _ h

end TauCeti.AlgebraicGeometry.Spec
