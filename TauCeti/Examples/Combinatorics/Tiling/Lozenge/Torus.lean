/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Torus
import Mathlib.Tactic.FinCases

/-!
# Checks: torus tilings and height changes

* `n₁ = n₂ = 1`: the torus tilings are exactly the three tilings `{e | e.k = j}` by lozenges of a
  single type, with height changes `(1, 0)`, `(0, 1)`, `(0, 0)`.
* `n₁ = n₂ = 2`, `(a, b) = (1, 1)`: the floor tiling of `H(x, y) = ⌊(x + y)/2⌋` is a torus tiling
  with height change `(1, 1)`, and it has no type-3 lozenge, since `H` increases by `1` along every
  `e₃`, matching `4 − 2 − 2 = 0`.
-/

public section

open Pointwise

namespace TauCeti.Examples.LozengeTorusChecks

open TauCeti

/-! ### The `1 × 1` torus -/

/-- A set of edges invariant under the translations by `(1, 0)` and `(0, 1)` contains an edge
exactly when it contains the edge of the same direction at the origin. -/
theorem mem_iff_of_vadd_eq {M : Set TriEdge} (h₁ : ((1 : ℤ), (0 : ℤ)) +ᵥ M = M)
    (h₂ : ((0 : ℤ), (1 : ℤ)) +ᵥ M = M) (v : ℤ × ℤ) (k : Fin 3) :
    (⟨v, k⟩ : TriEdge) ∈ M ↔ (⟨0, k⟩ : TriEdge) ∈ M := by
  have step : ∀ (w : ℤ × ℤ), w +ᵥ M = M → ∀ e : TriEdge, w +ᵥ e ∈ M ↔ e ∈ M := fun w hw e => by
    have := Set.vadd_mem_vadd_set_iff (a := w) (s := M) (x := e)
    rwa [hw] at this
  have key : ∀ P : ℤ → Prop, (∀ x, P (x + 1) ↔ P x) → ∀ x, P x ↔ P 0 := by
    intro P hP x
    induction x using Int.induction_on with
    | zero => rfl
    | succ n ih => rw [hP, ih]
    | pred n ih => rw [← ih, ← hP, sub_add_cancel]
  obtain ⟨x, y⟩ := v
  rw [key (fun x => (⟨(x, y), k⟩ : TriEdge) ∈ M) (fun x => by
      simpa [add_comm] using step _ h₁ ⟨(x, y), k⟩) x,
    key (fun y => (⟨(0, y), k⟩ : TriEdge) ∈ M) (fun y => by
      simpa [add_comm] using step _ h₂ ⟨(0, y), k⟩) y]
  rfl

/-- The tilings by lozenges of a single type are `1 × 1` torus tilings. -/
theorem isTorusTiling_setOf_k_eq (j : Fin 3) : IsTorusTiling 1 1 {e : TriEdge | e.k = j} := by
  refine isTorusTiling_def.2 ⟨isTiling_univ_iff.2 fun f => ?_, ?_, ?_⟩
  · rw [TriFace.existsUnique_mem_edges_iff]
    exact ⟨j, TriFace.edge_k f j, fun k hk => by simpa using hk⟩
  all_goals
    ext e
    simp [Set.mem_vadd_set_iff_neg_vadd_mem]

/-- **The `1 × 1` torus has exactly three tilings**, one of each type. -/
example (M : Set TriEdge) : IsTorusTiling 1 1 M ↔ ∃ j : Fin 3, M = {e | e.k = j} := by
  refine ⟨fun h => ?_, fun ⟨j, hj⟩ => hj ▸ isTorusTiling_setOf_k_eq j⟩
  have hM := isTorusTiling_def.1 h
  have hmem := mem_iff_of_vadd_eq (by exact_mod_cast hM.2.1) (by exact_mod_cast hM.2.2)
  obtain ⟨j, hj, hu⟩ := (TriFace.existsUnique_mem_edges_iff ⟨0, true⟩ M).1
    (hM.1.existsUnique (Set.mem_univ _))
  have hk : ∀ k : Fin 3, (⟨0, k⟩ : TriEdge) ∈ M ↔ TriFace.edge ⟨0, true⟩ k ∈ M := fun k => by
    rw [TriFace.edge_mk_true]
    exact (hmem _ k).symm
  refine ⟨j, Set.ext fun ⟨v, k⟩ => ?_⟩
  change _ ↔ k = j
  rw [hmem, hk]
  exact ⟨fun hk' => hu k hk', fun hkj => hkj ▸ hj⟩

/-- The height changes of the three `1 × 1` torus tilings are `(1, 0)`, `(0, 1)`, `(0, 0)`. -/
example : heightChange 1 1 {e : TriEdge | e.k = 0} = (1, 0) ∧
    heightChange 1 1 {e : TriEdge | e.k = 1} = (0, 1) ∧
    heightChange 1 1 {e : TriEdge | e.k = 2} = (0, 0) := by
  simp [heightChange_def, Finset.filter_singleton]

/-! ### The floor tiling of `⌊(x + y)/2⌋` on the `2 × 2` torus -/

/-- `⌊(x + y)/2⌋`. -/
def halfSumHeight (v : ℤ × ℤ) : ℤ :=
  (v.1 + v.2) / 2

theorem isHeightFunction_halfSumHeight : IsHeightFunction halfSumHeight := by
  rw [isHeightFunction_def]
  rintro ⟨⟨x, y⟩, k⟩
  fin_cases k <;> simp [halfSumHeight] <;> omega

/-- The floor tiling of `⌊(x + y)/2⌋` is a `2 × 2` torus tiling. -/
theorem isTorusTiling_tilingOfHeight_halfSumHeight :
    IsTorusTiling 2 2 (tilingOfHeight halfSumHeight) := by
  refine isTorusTiling_def.2 ⟨isHeightFunction_halfSumHeight.isTiling_tilingOfHeight, ?_, ?_⟩ <;>
  · ext ⟨⟨x, y⟩, k⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, mem_tilingOfHeight, mem_tilingOfHeight]
    fin_cases k <;> simp [halfSumHeight] <;> omega

/-- Its height change is `(1, 1)`. -/
example : heightChange 2 2 (tilingOfHeight halfSumHeight) = (1, 1) := by
  have hT := isHeightFunction_halfSumHeight.tilingHeight_tilingOfHeight (by simp [halfSumHeight])
  have h₁ := isTorusTiling_tilingOfHeight_halfSumHeight.heightChange_fst_eq
  have h₂ := isTorusTiling_tilingOfHeight_halfSumHeight.heightChange_snd_eq
  rw [hT] at h₁ h₂
  norm_num [halfSumHeight] at h₁ h₂
  exact Prod.ext (by exact_mod_cast h₁) (by exact_mod_cast h₂)

/-- It has no type-3 lozenge: `H` increases by `1` along every `e₃`. -/
example (e : TriEdge) (he : e ∈ tilingOfHeight halfSumHeight) : e.k ≠ 2 := by
  obtain ⟨⟨x, y⟩, k⟩ := e
  rw [mem_tilingOfHeight] at he
  rintro rfl
  simp [halfSumHeight] at he
  omega

end TauCeti.Examples.LozengeTorusChecks
