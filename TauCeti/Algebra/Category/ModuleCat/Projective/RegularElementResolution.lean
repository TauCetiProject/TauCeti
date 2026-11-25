/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Span
public import TauCeti.RingTheory.Ideal.Quotient.Operations

/-!
# The two-term resolution of the quotient by a nonzerodivisor

For a commutative ring `A` and an element `f ∈ A`, multiplication by `f` followed by the quotient
map gives the short complex `A --f--> A ⟶ A ⧸ (f)`. When `f` is a nonzerodivisor, multiplication
by `f` is injective with image the ideal `(f)`, so

`0 ⟶ A --f--> A ⟶ A ⧸ (f) ⟶ 0`

is short exact. Its first two terms are free, so
`CategoryTheory.ShortComplex.ShortExact.projectiveResolution` turns it into the two-term projective
resolution `A --f--> A` of `A ⧸ (f)`, augmented by the quotient map.

## Main definitions

* `TauCeti.regularElementShortComplex f`: the short complex `A --f--> A ⟶ A ⧸ (f)`.

## Main results

* `TauCeti.regularElementShortComplex_shortExact`: for a nonzerodivisor `f` it is short exact.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u

namespace TauCeti

variable {A : Type u} [CommRing A] (f : A)

/-- The short complex `A --f--> A ⟶ A ⧸ (f)` of `A`-modules: multiplication by `f`, followed by
the quotient map. -/
abbrev regularElementShortComplex : ShortComplex (ModuleCat.{u} A) :=
  ModuleCat.shortComplexOfCompEqZero (LinearMap.mulLeft A f)
    (Ideal.Quotient.mkₐ A (Ideal.span {f})).toLinearMap
    (Ideal.exact_mulLeft_mkₐ_span_singleton f).linearMap_comp_eq_zero

variable {f} in
/-- For a nonzerodivisor `f`, the sequence `0 ⟶ A --f--> A ⟶ A ⧸ (f) ⟶ 0` is short exact. -/
theorem regularElementShortComplex_shortExact (hf : IsLeftRegular f) :
    (regularElementShortComplex f).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (Ideal.exact_mulLeft_mkₐ_span_singleton f) hf
    (Ideal.Quotient.mkₐ_surjective A _)

end TauCeti
