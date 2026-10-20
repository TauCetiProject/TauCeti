/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Semantics

/-!
# Left-variable support of first-order terms

Term realization depends only on the valuation of the variables in `Term.varFinsetLeft`
when the right-variable valuation is fixed. Relabelling right variables preserves this support.

The public lemmas are `TauCeti.realize_congr_varFinsetLeft` and
`TauCeti.varFinsetLeft_relabel`; use these qualified names or `open TauCeti` to apply them.
-/

public section

universe u v uα w

namespace TauCeti

open FirstOrder.Language

variable {L : FirstOrder.Language.{u, v}} {α : Type uα}

/-- Term realization depends only on the free valuation on its finite left-variable support;
the valuation of the right variables is held fixed. -/
theorem realize_congr_varFinsetLeft [DecidableEq α] {β : Type*} {M : Type w} [L.Structure M]
    (t : L.Term (α ⊕ β)) {v₁ v₂ : α → M} (ys : β → M)
    (h : Set.EqOn v₁ v₂ ↑t.varFinsetLeft) :
    t.realize (Sum.elim v₁ ys) = t.realize (Sum.elim v₂ ys) := by
  rw [← t.realize_restrictVarLeft' (Set.Subset.refl _),
    ← t.realize_restrictVarLeft' (Set.Subset.refl _)]
  have hv : v₁ ∘ ((↑) : (↑t.varFinsetLeft : Set α) → α) = v₂ ∘ (↑) :=
    funext fun a => h a.property
  rw [hv]

/-- Relabelling right variables preserves a term's finite left-variable support. -/
@[simp]
theorem varFinsetLeft_relabel [DecidableEq α] {β γ : Type*}
    (t : L.Term (α ⊕ β)) (f : β → γ) :
    (t.relabel (Sum.map id f)).varFinsetLeft = t.varFinsetLeft := by
  induction t with
  | var a => cases a <;> simp
  | func g ts ih => simp [ih]

end TauCeti
