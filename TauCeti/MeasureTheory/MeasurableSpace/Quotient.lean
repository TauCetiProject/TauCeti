/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Points of a quotient measurable space

For an equivalence relation `E` on a measurable space `X`, a singleton `{⟦x⟧}` of `Quotient E` is
measurable for Mathlib's quotient σ-algebra exactly when its preimage, the class of `x`, is
measurable in `X`. So if every class of `E` is measurable, the quotient has measurable singletons,
and if there are moreover countably many classes, Mathlib's instance
`MeasurableSingletonClass.toDiscreteMeasurableSpace` makes every subset of the quotient measurable.

## Main results

* `Setoid.measurableSingletonClass_quotient`: measurable classes give measurable singletons.
-/

public section

namespace Setoid

variable {X : Type*} [MeasurableSpace X] {E : Setoid X}

/-- If every class of `E` is measurable, then the quotient σ-algebra on `Quotient E` has
measurable singletons. -/
theorem measurableSingletonClass_quotient (hE : ∀ x, MeasurableSet {y | E x y}) :
    MeasurableSingletonClass (Quotient E) := by
  refine ⟨fun q => ?_⟩
  induction q using Quotient.ind with | _ x => ?_
  refine measurableSet_quotient.2 ?_
  have : (Quotient.mk'' : X → Quotient E) ⁻¹' {Quotient.mk E x} = {y | E x y} := by
    ext y
    exact ⟨fun h => E.symm (Quotient.exact h), fun h => Quotient.sound (E.symm h)⟩
  rw [this]
  exact hE x

end Setoid
