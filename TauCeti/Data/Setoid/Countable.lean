/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Setoid.Basic
public import Mathlib.Data.Set.Countable

/-!
# Countably many classes met by a set

For a setoid `s` on `α` and a set `K ⊆ α`, there are two ways to count the classes of `s` that
`K` meets: the quotient of `K` by the restriction `s.comap (↑)`, or the image of `K` in the
quotient by `s`. Mathlib's `Setoid.comapQuotientEquiv` puts the two in bijection, so one is
countable exactly when the other is.

The quotient form is the one that comparison maps between quotients produce. The image form is
monotone in `K` and is the natural one for "`K` meets countably many classes".

## Main results

* `Setoid.countable_quotient_comap_val_iff`: the restriction of `s` to `K` has countably many
  classes exactly when `K` meets countably many classes of `s`.
-/

public section

namespace Setoid

/-- The restriction of a setoid `s` to a set `K` has countably many classes exactly when `K` meets
countably many classes of `s`. -/
theorem countable_quotient_comap_val_iff {α : Type*} {s : Setoid α} {K : Set α} :
    Countable (Quotient (s.comap ((↑) : K → α))) ↔ (Quotient.mk s '' K).Countable := by
  rw [(comapQuotientEquiv _ _).countable_iff, Set.countable_coe_iff, Set.range_comp,
    Subtype.range_coe]

end Setoid
