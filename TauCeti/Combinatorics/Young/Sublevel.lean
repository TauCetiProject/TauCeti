/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Young.YoungDiagram

/-!
# Strict sublevel diagrams

The cells with labels strictly below a threshold form a Young diagram when the labels are
monotone in the product order.
-/

public section

namespace YoungDiagram

variable {A : Type*} [Preorder A] [DecidableLT A]

/-- The cells of a Young diagram whose monotone labels are strictly below a threshold. -/
def strictSublevel (μ : YoungDiagram) (f : ↥μ.cells → A) (hf : Monotone f) (a : A) :
    YoungDiagram where
  cells := (μ.cells.attach.filter fun c => f c < a).map ⟨Subtype.val, Subtype.val_injective⟩
  isLowerSet := by
    intro d c hcd hd
    obtain ⟨⟨d', hd'⟩, hmem, he⟩ := Finset.mem_map.mp hd
    simp only [Function.Embedding.coeFn_mk] at he
    subst d
    have hc : c ∈ μ.cells := μ.isLowerSet hcd hd'
    exact Finset.mem_map.mpr ⟨⟨c, hc⟩, Finset.mem_filter.mpr
      ⟨Finset.mem_attach _ _, (hf hcd).trans_lt (Finset.mem_filter.mp hmem).2⟩, rfl⟩

/-- A cell belongs to a strict sublevel diagram exactly when it has a label below the threshold. -/
@[simp]
theorem mem_strictSublevel {μ : YoungDiagram} {f : ↥μ.cells → A} {hf : Monotone f} {a : A}
    {c : ℕ × ℕ} :
    c ∈ μ.strictSublevel f hf a ↔ ∃ hc : c ∈ μ.cells, f ⟨c, hc⟩ < a := by
  have hcells : (μ.strictSublevel f hf a).cells =
      (μ.cells.attach.filter fun c => f c < a).map ⟨Subtype.val, Subtype.val_injective⟩ := rfl
  rw [← mem_cells, hcells]
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_attach, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨⟨_, hc⟩, hlt, rfl⟩
    exact ⟨hc, hlt⟩
  · rintro ⟨hc, hlt⟩
    exact ⟨⟨c, hc⟩, hlt, rfl⟩

end YoungDiagram
