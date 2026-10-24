/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Complex

import Mathlib.Algebra.AlgebraicCard
import TauCeti.Analysis.Normed.Field.Approximation

/-!
# `ℂ_p` is separable

The field `ℂ_[p]` of `p`-adic complex numbers is the completion of an algebraic closure of
`ℚ_[p]`. It contains the countable set of algebraic numbers, the elements algebraic over `ℚ`, as
a dense subset. Indeed the image of the algebraic closure of `ℚ_[p]` is dense, and each of its
elements is a limit of algebraic numbers: approximate its minimal polynomial over `ℚ_[p]` by one
over `ℚ` and take a nearby root (`IsAlgebraic.mem_closure_setOf_isAlgebraic`).

Separability is what makes `ℂ_p` fail to be spherically complete, so that the closed unit disc
over `ℂ_p` has points of type (4).

## Main results

* `PadicComplex.dense_setOf_isAlgebraic`: the algebraic numbers are dense in `ℂ_[p]`.
* `PadicComplex.separableSpace`: `ℂ_[p]` is a separable space.

## References

* A. M. Robert, *A Course in p-adic Analysis*, Graduate Texts in Mathematics 198, Springer, 2000,
  Chapter 3, for the density of the algebraic numbers in `ℂ_p` and the separability of `ℂ_p`.
-/

public section

namespace PadicComplex

variable (p : ℕ) [Fact p.Prime]

/-- **The algebraic numbers are dense in `ℂ_[p]`.** -/
theorem dense_setOf_isAlgebraic : Dense {x : ℂ_[p] | IsAlgebraic ℚ x} := by
  have hℚ : DenseRange (algebraMap ℚ ℚ_[p]) := by
    rw [show ⇑(algebraMap ℚ ℚ_[p]) = Rat.cast from funext (eq_ratCast _)]
    exact Padic.denseRange_ratCast p
  refine dense_closure.mp <|
    Dense.mono ?_ (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p))
  rintro _ ⟨x, rfl⟩
  rw [coe_eq]
  exact ((Algebra.IsAlgebraic.isAlgebraic x).algebraMap (A := ℂ_[p])).mem_closure_setOf_isAlgebraic
    hℚ

/-- **`ℂ_[p]` is separable**: the countable set of algebraic numbers is dense. -/
instance separableSpace : TopologicalSpace.SeparableSpace ℂ_[p] :=
  ⟨⟨_, Algebraic.countable ℚ ℂ_[p], dense_setOf_isAlgebraic p⟩⟩

end PadicComplex
