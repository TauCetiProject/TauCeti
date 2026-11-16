/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.AEEqFun

/-!
# Equality of sums of almost-everywhere equivalence classes

Two classes in `α →ₘ[μ] β` are equal exactly when their representatives agree almost everywhere,
and the representative of a sum is the sum of the representatives almost everywhere. Combining
these, an identity `a + b = c + d` between sums of classes is an almost-everywhere identity between
the sums of their representatives (`MeasureTheory.AEEqFun.add_eq_add_iff_ae_eq`). This is the form
in which a decomposition of a function into two summands, each in its own function space, is
compared with another such decomposition.
-/

public section

namespace MeasureTheory.AEEqFun

/-- Two sums in `α →ₘ[μ] β` are equal exactly when the sums of their representatives agree almost
everywhere. -/
theorem add_eq_add_iff_ae_eq {α β : Type*} {mα : MeasurableSpace α}
    {μ : Measure α} [TopologicalSpace β] [Add β] [ContinuousAdd β] {a b c d : α →ₘ[μ] β} :
    a + b = c + d ↔ ⇑a + ⇑b =ᵐ[μ] ⇑c + ⇑d := by
  rw [AEEqFun.ext_iff, (AEEqFun.coeFn_add a b).congr_left, (AEEqFun.coeFn_add c d).congr_right]

end MeasureTheory.AEEqFun
