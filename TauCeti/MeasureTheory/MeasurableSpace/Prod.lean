/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Products of discrete σ-algebras

The product of the discrete σ-algebras on two types is again discrete as soon as the first type is
countable. Countability is what makes this work: every subset `s` of the product is the countable
union of the measurable rectangles `{a} ×ˢ (Prod.mk a ⁻¹' s)` over the points `a` of the first
factor. No hypothesis on the second factor is needed.

## Main results

* `TauCeti.MeasureTheory.prod_top_eq_top_of_countable`: the product of the discrete σ-algebras on
  a countable type and an arbitrary type is discrete.
-/

public section

namespace TauCeti.MeasureTheory

/-- The product of the discrete σ-algebras on a countable type `α` and an arbitrary type `β` is
discrete. -/
theorem prod_top_eq_top_of_countable (α β : Type*) [Countable α] :
    (⊤ : MeasurableSpace α).prod (⊤ : MeasurableSpace β) = ⊤ := by
  let _ : MeasurableSpace α := ⊤
  let _ : MeasurableSpace β := ⊤
  refine top_unique fun s _ => measurableSet_setOfPred.2 ?_
  exact measurable_from_prod_countable_right fun _ => measurable_from_top

end TauCeti.MeasureTheory
