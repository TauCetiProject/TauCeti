/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.RowTiling

/-!
# Regression examples: row tilings

* **Frozen tilings.** `ε ≡ 1` gives the tiling `M₁` of all edges of direction 1 and `ε ≡ 0` the
  tiling `M₃` of all edges of direction 3, while no `ε` gives `M₂`, whose edges all have
  direction 2.
* **A non-periodic row tiling.** For `ε = 1_{[0,∞)}`, `W(−1,0)` contains `((−1,0),3)` and `W(0,0)`
  contains `((0,0),1)`; the translate `τ_{e₁} M_ε` is `M_{1_{[1,∞)}}`, which differs from `M_ε` at
  `((0,0),1)`, while `τ_{e₂}` fixes `M_ε`.
* **Rows, not columns.** Reading `ε` along a column instead,
  `{((x,y),1) : ε_y = 1} ∪ {((x,y),3) : ε_y = 0}`, is not a tiling for `ε = 1_{{0}}`: the face
  `B(0,0)` contains none of its edges.

Edge directions `1, 2, 3` are the indices `0, 1, 2` of `TriEdge.k`.
-/

public section

namespace TauCeti.Examples.RowTiling

open TauCeti

/-! ### Frozen tilings -/

/-- `ε ≡ 1` gives `M₁`, the configuration of all edges of direction 1. -/
example : rowTiling (fun _ => true) = fun e => decide (e.k = 0) :=
  funext rowTiling_true

/-- `ε ≡ 0` gives `M₃`, the configuration of all edges of direction 3. -/
example : rowTiling (fun _ => false) = fun e => decide (e.k = 2) :=
  funext rowTiling_false

/-- No row tiling is `M₂`, the configuration of all edges of direction 2. -/
theorem rowTiling_ne_frozen_two (ε : ℤ → Bool) : rowTiling ε ≠ fun e => decide (e.k = 1) :=
  fun h => by simpa using congrFun h ⟨(0, 0), 1⟩

/-! ### A non-periodic row tiling -/

/-- The indicator `1_{[0,∞)}`. -/
def nonnegInd (x : ℤ) : Bool := decide (0 ≤ x)

/-- `W(−1,0)` contains the edge `((−1,0),3)` of `M_ε`, and `W(0,0)` its edge `((0,0),1)`. -/
theorem rowTiling_nonnegInd_edges :
    (⟨(-1, 0), 2⟩ : TriEdge) ∈ (⟨(-1, 0), true⟩ : TriFace).edges ∧
      rowTiling nonnegInd ⟨(-1, 0), 2⟩ = true ∧
    (⟨(0, 0), 0⟩ : TriEdge) ∈ (⟨(0, 0), true⟩ : TriFace).edges ∧
      rowTiling nonnegInd ⟨(0, 0), 0⟩ = true := by
  simp [nonnegInd]

/-- The translate of `M_{1_{[0,∞)}}` by `e₁` is `M_{1_{[1,∞)}}`. -/
theorem vadd_rowTiling_nonnegInd :
    ((1, 0) : ℤ × ℤ) +ᵥ rowTiling nonnegInd = rowTiling fun x => decide (1 ≤ x) := by
  rw [rowTiling_vadd_one_zero]
  congr 1
  funext x
  simp only [nonnegInd, decide_eq_decide]
  omega

/-- The translate by `e₁` differs from `M_{1_{[0,∞)}}` at the edge `((0,0),1)`. -/
theorem vadd_rowTiling_nonnegInd_ne :
    (((1, 0) : ℤ × ℤ) +ᵥ rowTiling nonnegInd) ⟨(0, 0), 0⟩ = false ∧
      rowTiling nonnegInd ⟨(0, 0), 0⟩ = true := by
  rw [vadd_rowTiling_nonnegInd]
  simp [nonnegInd]

/-- The translation by `e₂` fixes `M_{1_{[0,∞)}}`. -/
example : ((0, 1) : ℤ × ℤ) +ᵥ rowTiling nonnegInd = rowTiling nonnegInd :=
  rowTiling_vadd_zero_mk 1 nonnegInd

/-! ### Rows, not columns -/

/-- Reading `ε` along a column: `{((x,y),1) : ε_y = 1} ∪ {((x,y),3) : ε_y = 0}`. -/
def columnTiling (ε : ℤ → Bool) (e : TriEdge) : Bool :=
  if e.k = 0 then ε e.v.2 else if e.k = 2 then !ε e.v.2 else false

/-- For `ε = 1_{{0}}` the column reading is not a plane tiling: the face `B(0,0)` would have to
contain `((0,1),1)`, absent since `ε_1 = 0`, or `((0,0),3)`, absent since `ε_0 = 1`. -/
theorem not_isTiling_columnTiling :
    ¬ IsTiling Set.univ {e | columnTiling (fun y => decide (y = 0)) e = true} := by
  intro h
  obtain ⟨e, ⟨he, hef⟩, -⟩ := isTiling_univ_iff.1 h ⟨(0, 0), false⟩
  simp only [TriFace.edges_mk_false, Finset.mem_insert, Finset.mem_singleton] at hef
  rcases hef with rfl | rfl | rfl <;> simp [columnTiling] at he

end TauCeti.Examples.RowTiling
