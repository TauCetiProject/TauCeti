/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Operations on two-sided ideals

Supplementary lemma for `TwoSidedIdeal.asIdeal`, the inclusion of two-sided ideals of a unital
ring into left ideals (`Mathlib.RingTheory.TwoSidedIdeal.Operations`). This connects `I.asIdeal = ⊤`
with `I = ⊤` so that `Ideal`-level characterizations of properness transfer directly to
`TwoSidedIdeal`.

## Main results

* `TwoSidedIdeal.asIdeal_eq_top_iff`: a two-sided ideal equals `⊤` if and only if its underlying
  left ideal `I.asIdeal` equals `⊤`.
-/

public section

namespace TwoSidedIdeal

/-- A two-sided ideal equals `⊤` if and only if its underlying left ideal equals `⊤`. -/
@[simp]
theorem asIdeal_eq_top_iff {R : Type*} [Ring R] (I : TwoSidedIdeal R) :
    I.asIdeal = ⊤ ↔ I = ⊤ := by
  simp only [SetLike.ext_iff, mem_asIdeal, Submodule.mem_top, mem_top]

end TwoSidedIdeal

end
