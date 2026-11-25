/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Span
public import TauCeti.RingTheory.Ideal.Quotient.Operations
import TauCeti.Algebra.Category.ModuleCat.ExtendScalarsQuotient

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
* `TauCeti.extendScalars_map_ofHom_mulLeft`: multiplication by `f` reduces to zero modulo
  `(f)`.
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

/-- Reducing multiplication by `f` modulo `(f)` gives the zero map. -/
@[simp]
theorem extendScalars_map_ofHom_mulLeft :
    (ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {f}))).map
      (ModuleCat.ofHom (LinearMap.mulLeft A f)) = 0 := by
  ext m
  apply (Ideal.extendScalarsMkEquivQuotSMul (Ideal.span {f}) A).injective
  -- `ext` states the goal on `1 ⊗ₜ m` with `1 : A ⧸ (f)`, whereas the `tmul` lemmas expect `1`
  -- in the restriction of scalars of `A ⧸ (f)`; the two types agree only after unfolding
  -- `ModuleCat.restrictScalars`, so both lemmas need `erw`.
  erw [ModuleCat.ExtendScalars.map_tmul]
  rw [← map_one (Ideal.Quotient.mk (Ideal.span {f}))]
  erw [Ideal.extendScalarsMkEquivQuotSMul_mk_tmul]
  have h0 : (Submodule.Quotient.mk ((1 : A) • LinearMap.mulLeft A f m) :
      A ⧸ (Ideal.span {f} • ⊤ : Submodule A A)) = 0 := by
    -- keep `mk (f * m)` together so that membership in `(f)` can be tested
    simp [-map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact h0.trans ((Ideal.extendScalarsMkEquivQuotSMul (Ideal.span {f}) A).map_zero).symm

end TauCeti
