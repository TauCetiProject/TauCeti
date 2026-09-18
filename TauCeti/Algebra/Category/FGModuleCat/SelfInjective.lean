/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Injective
public import TauCeti.Algebra.Category.FGModuleCat.Projective
public import TauCeti.Algebra.Module.Injective.SelfInjective

/-!
# Projectives over a self-injective ring

This file relates module-theoretic self-injectivity to projective and injective objects in the
category `FGModuleCat R` of finitely generated modules.

Categorical projectivity of a finitely generated module implies module-theoretic projectivity
(`FGModuleCat.moduleProjective_of_projective`). Consequently, over a noetherian ring whose regular
left module is injective, every projective object of `FGModuleCat R` is injective.

These results supply one direction of the projective--injective identification for the Frobenius
exact category of finite-dimensional modules over a self-injective finite-dimensional algebra.

## Main results

* `FGModuleCat.injective_of_projective_of_moduleInjective_self`: over a noetherian self-injective
  ring, every projective object of `FGModuleCat R` is injective.

## References

* T. Y. Lam, *Lectures on Modules and Rings*, Sections 3 and 16.
* D. Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
-/

public section

namespace TauCeti

open CategoryTheory

universe u

variable {R : Type u} [Ring R] [IsNoetherianRing R]

/-- Over a noetherian self-injective ring, every projective object among the finitely generated
modules is injective. -/
theorem _root_.FGModuleCat.injective_of_projective_of_moduleInjective_self
    (hR : Module.Injective R R) (X : FGModuleCat.{u} R) [Projective X] : Injective X := by
  have := FGModuleCat.moduleProjective_of_projective X
  have := Module.Injective.of_finite_projective (P := X) hR
  exact FGModuleCat.injective_of_moduleInjective X

end TauCeti
