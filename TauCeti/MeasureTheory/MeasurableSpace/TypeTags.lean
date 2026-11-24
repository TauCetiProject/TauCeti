/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurable singletons on the `Additive` and `Multiplicative` type tags

`Mathlib.MeasureTheory.MeasurableSpace.Constructions` equips the type tags `Additive α` and
`Multiplicative α` with the σ-algebra of `α` (mapped along `Additive.ofMul` and
`Multiplicative.ofAdd`), so every subset has the same measurability on the type tag as on `α`.
However, Mathlib does not register `MeasurableSingletonClass` on either type tag, so typeclass
search does not find `MeasurableSingletonClass (Additive α)` or
`MeasurableSingletonClass (Multiplicative α)` from `[MeasurableSingletonClass α]`.

This file supplies both definitional transport instances at the measurable-space level, depending
only on `Mathlib.MeasureTheory.MeasurableSpace.Constructions` without pulling in group or
Haar-measure theory.

## Main definitions

* `Additive.instMeasurableSingletonClass`: `Additive α` inherits measurable singletons from `α`.
* `Multiplicative.instMeasurableSingletonClass`: `Multiplicative α` inherits measurable singletons
  from `α`.
-/

public section

namespace Additive

/-- `Additive α` inherits measurable singletons from `α`. -/
instance instMeasurableSingletonClass {α : Type*} [MeasurableSpace α]
    [h : MeasurableSingletonClass α] : MeasurableSingletonClass (Additive α) := h

end Additive

namespace Multiplicative

/-- `Multiplicative α` inherits measurable singletons from `α`. -/
instance instMeasurableSingletonClass {α : Type*} [MeasurableSpace α]
    [h : MeasurableSingletonClass α] : MeasurableSingletonClass (Multiplicative α) := h

end Multiplicative
