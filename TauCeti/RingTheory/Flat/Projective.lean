/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Projectivity of finite flat algebras of finite presentation

A module-finite commutative algebra `A` over a commutative ring `R` is projective as an `R`-module
if and only if it is flat as an `R`-module and finitely presented as an `R`-algebra. Indeed,
for a finite `R`-algebra, finite presentation as a module is equivalent to finite presentation as
an algebra (`Module.FinitePresentation.iff_finitePresentation_of_finite`), every finitely
generated projective module is flat and finitely presented, and conversely every flat finitely
presented module is projective (`Module.Flat.projective_of_finitePresentation`).

## Main results

* `TauCeti.moduleProjective_iff_flat_and_finitePresentation`: a finite commutative algebra is
  projective as a module if and only if it is flat and finitely presented as an algebra.

## References

* [The Stacks Project, Tag 00NX](https://stacks.math.columbia.edu/tag/00NX)
* [The Stacks Project, Tag 0564](https://stacks.math.columbia.edu/tag/0564)
-/

public section

namespace TauCeti

universe u v

/-- A finite commutative algebra is projective as a module exactly when it is flat as a module
and finitely presented as an algebra. -/
theorem moduleProjective_iff_flat_and_finitePresentation
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A] :
    Module.Projective R A ↔ Module.Flat R A ∧ Algebra.FinitePresentation R A := by
  rw [← Module.FinitePresentation.iff_finitePresentation_of_finite]
  exact ⟨fun _ ↦ ⟨inferInstance, Module.finitePresentation_of_projective R A⟩,
    fun ⟨_, _⟩ ↦ Module.Flat.projective_of_finitePresentation⟩

end TauCeti
