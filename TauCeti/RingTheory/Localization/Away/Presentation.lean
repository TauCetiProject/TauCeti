/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import TauCeti.RingTheory.Ideal.Quotient.Operations
public import TauCeti.RingTheory.Polynomial.Ideal

/-!
# A free resolution of an away localization

Let `A` be a commutative ring and `f : A`. The `A`-module `A[1/f]` is the quotient
`A[X] ⧸ (f X - 1)` (`Localization.awayEquivAdjoin`), and multiplication by `f X - 1` on `A[X]` is
injective. This gives a short exact sequence of `A`-modules

`0 → A[X] → A[X] → A[1/f] → 0`

whose first two terms are free. So `A[1/f]` has projective dimension at most one.

## Main definitions and results

* `TauCeti.awayPresentation f`: the short complex `0 → A[X] → A[X] → A[1/f] → 0`, with first map
  multiplication by `f X - 1` and second map `X ↦ 1/f`.
* `TauCeti.awayPresentation_shortExact`: it is short exact.

## References

* [Stacks Project, Lemma 15.93.1 (Tag 091P)](https://stacks.math.columbia.edu/tag/091P), whose
  proof uses this resolution.
-/

public section

noncomputable section

open CategoryTheory Polynomial

universe u

namespace TauCeti

variable {A : Type u} [CommRing A] (f : A)

/-- The free resolution `0 → A[X] → A[X] → A[1/f] → 0` of the `A`-module `A[1/f]`, whose first
map is multiplication by `f X - 1` and whose second map is `X ↦ 1/f`
(`Localization.awayEquivAdjoin`). It is short exact (`TauCeti.awayPresentation_shortExact`) with
free, hence projective, first two terms, so `A[1/f]` has projective dimension at most one. -/
def awayPresentation : ShortComplex (ModuleCat.{u} A) :=
  ModuleCat.shortComplexOfCompEqZero (LinearMap.mulLeft A (C f * X - 1 : A[X]))
    ((Localization.awayEquivAdjoin f).symm.toLinearMap ∘ₗ
      (Ideal.Quotient.mkₐ A (Ideal.span {C f * X - 1})).toLinearMap)
    ((Ideal.exact_mulLeft_mkₐ_span_singleton (C f * X - 1 : A[X])).comp_injective _
      (Localization.awayEquivAdjoin f).symm.injective (map_zero _)).linearMap_comp_eq_zero

@[simp]
theorem awayPresentation_X₁ : (awayPresentation f).X₁ = ModuleCat.of A A[X] := by
  unfold awayPresentation
  rfl

@[simp]
theorem awayPresentation_X₂ : (awayPresentation f).X₂ = ModuleCat.of A A[X] := by
  unfold awayPresentation
  rfl

@[simp]
theorem awayPresentation_X₃ :
    (awayPresentation f).X₃ = ModuleCat.of A (Localization.Away f) := by
  unfold awayPresentation
  rfl

/-- The first map of `TauCeti.awayPresentation f` is multiplication by `f X - 1`. -/
theorem awayPresentation_f : (awayPresentation f).f = eqToHom (awayPresentation_X₁ f) ≫
    ModuleCat.ofHom (LinearMap.mulLeft A (C f * X - 1 : A[X])) ≫
      eqToHom (awayPresentation_X₂ f).symm := by
  unfold awayPresentation
  rfl

/-- The second map of `TauCeti.awayPresentation f` is the quotient map
`A[X] → A[X] ⧸ (f X - 1)` followed by `Localization.awayEquivAdjoin`, sending `X` to `1/f`. -/
theorem awayPresentation_g : (awayPresentation f).g = eqToHom (awayPresentation_X₂ f) ≫
    ModuleCat.ofHom ((Localization.awayEquivAdjoin f).symm.toLinearMap ∘ₗ
      (Ideal.Quotient.mkₐ A (Ideal.span {C f * X - 1})).toLinearMap) ≫
      eqToHom (awayPresentation_X₃ f).symm := by
  unfold awayPresentation
  rfl

theorem awayPresentation_shortExact : (awayPresentation f).ShortExact := by
  unfold awayPresentation
  exact ModuleCat.shortComplex_shortExact _
    ((Ideal.exact_mulLeft_mkₐ_span_singleton (C f * X - 1 : A[X])).comp_injective _
      (Localization.awayEquivAdjoin f).symm.injective (map_zero _))
    (mulLeft_C_mul_X_sub_one_injective A f)
    ((Localization.awayEquivAdjoin f).symm.surjective.comp (Ideal.Quotient.mkₐ_surjective A _))

instance : Projective (awayPresentation f).X₁ :=
  inferInstanceAs (Projective (ModuleCat.of A A[X]))

instance : Projective (awayPresentation f).X₂ :=
  inferInstanceAs (Projective (ModuleCat.of A A[X]))

end TauCeti
