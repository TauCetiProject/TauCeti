/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import TauCeti.Algebra.Module.Injective.Frobenius
public import TauCeti.CategoryTheory.Exact.Abelian
public import TauCeti.CategoryTheory.Exact.Frobenius

/-!
# All modules over a Frobenius algebra form a Frobenius category

Let `A` be a finite-dimensional algebra over a field with a Frobenius functional. This file proves
that the canonical exact structure on the abelian category `ModuleCat A` of **all** left
`A`-modules, not only the finitely generated ones, is a Frobenius exact structure: there are enough
projectives and enough injectives, and the projective and injective objects coincide. Its
`ProjectiveStableCategory` is therefore the stable category of all `A`-modules, triangulated by
`TauCeti.ExactStructure.IsFrobenius.stableIsTriangulated`.

The finitely generated analogue, over any finite-dimensional algebra which is self-injective on
both sides, is `FGModuleCat.abelian_isFrobenius`. For arbitrary modules the input is
`LinearMap.IsFrobeniusFunctional.moduleProjective_iff_moduleInjective`.

## Main results

* `ModuleCat.projective_iff_injective_of_isFrobeniusFunctional`: over a finite-dimensional algebra
  with a Frobenius functional, an object of `ModuleCat A` is projective exactly when it is
  injective.
* `ModuleCat.abelian_isFrobenius`: the canonical exact structure on `ModuleCat A` is Frobenius.

## References

* M. Khovanov, *Hopfological algebra and categorification at a root of unity: the first steps*,
  J. Knot Theory Ramifications 25 (2016), Proposition 1.
* D. Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
-/

public section

namespace ModuleCat

open CategoryTheory TauCeti

universe w

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A] [FiniteDimensional k A]
  [Small.{w} A] {φ : A →ₗ[k] k}

/-- **Projective and injective modules over a Frobenius algebra coincide.** Over a
finite-dimensional algebra with a Frobenius functional, an object of `ModuleCat A`, not
necessarily finitely generated, is projective if and only if it is injective. -/
theorem projective_iff_injective_of_isFrobeniusFunctional (hφ : φ.IsFrobeniusFunctional)
    (X : ModuleCat.{w} A) : Projective X ↔ Injective X := by
  rw [← IsProjective.iff_projective, ← Module.injective_iff_injective_object]
  exact hφ.moduleProjective_iff_moduleInjective X

/-- **All modules over a Frobenius algebra form a Frobenius category.** For a finite-dimensional
algebra `A` with a Frobenius functional, the canonical exact structure on the category of all
left `A`-modules is Frobenius. -/
theorem abelian_isFrobenius (hφ : φ.IsFrobeniusFunctional) :
    (ExactStructure.abelian (ModuleCat.{w} A)).IsFrobenius where
  enoughProjectives := ExactStructure.abelian_enoughProjectives
  enoughInjectives := ExactStructure.abelian_enoughInjectives
  projective_iff_injective X := by
    rw [ExactStructure.abelian_isProjective_iff, ExactStructure.abelian_isInjective_iff]
    exact projective_iff_injective_of_isFrobeniusFunctional hφ X

end ModuleCat
