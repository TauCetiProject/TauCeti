/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Young.YoungDiagram

/-!
# Sublevel diagrams

The cells with labels strictly below a threshold form a Young diagram when the labels are
monotone in the product order.
-/

public section

namespace YoungDiagram

variable {A : Type*} [Preorder A] [DecidableLT A]

/-- The cells of a Young diagram whose monotone labels are strictly below a threshold. -/
def sublevel (μ : YoungDiagram) (f : ↥μ.cells → A) (hf : Monotone f) (a : A) : YoungDiagram where
  cells := (μ.cells.attach.filter fun c => f c < a).map ⟨Subtype.val, Subtype.val_injective⟩
  isLowerSet := by
    intro d c hcd hd
    obtain ⟨⟨d', hd'⟩, hmem, he⟩ := Finset.mem_map.mp hd
    change d' = d at he
    subst d
    have hc : c ∈ μ.cells := μ.isLowerSet hcd hd'
    exact Finset.mem_map.mpr ⟨⟨c, hc⟩, Finset.mem_filter.mpr
      ⟨Finset.mem_attach _ _, (hf hcd).trans_lt (Finset.mem_filter.mp hmem).2⟩, rfl⟩

/-- A cell belongs to a sublevel diagram exactly when it has a label below the threshold. -/
theorem mem_sublevel {μ : YoungDiagram} {f : ↥μ.cells → A} {hf : Monotone f} {a : A}
    {c : ℕ × ℕ} : c ∈ μ.sublevel f hf a ↔ ∃ hc : c ∈ μ.cells, f ⟨c, hc⟩ < a := by
  rw [← mem_cells]
  change c ∈ (μ.cells.attach.filter fun c => f c < a).map _ ↔ _
  constructor
  · rintro h
    obtain ⟨⟨_, hc⟩, hlt, rfl⟩ := Finset.mem_map.mp h
    exact ⟨hc, (Finset.mem_filter.mp hlt).2⟩
  · rintro ⟨hc, hlt⟩
    exact Finset.mem_map.mpr ⟨⟨c, hc⟩, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hlt⟩, rfl⟩

end YoungDiagram
