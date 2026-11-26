/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.ModelTheory.RelationalConfiguration.UnravelTree
public import TauCeti.Examples.ModelTheory.RelationalConfiguration.Unravelling
public import TauCeti.ModelTheory.RelationalConfiguration.UnravelOrder

/-!
# Checks for the linear order of an unravelled graph code

Examples and sanity checks for the order `TauCeti.RelationalConfiguration.unravelOrderRel χ` on
`List ℚ × ℕ`, the lexicographic sum over `List ℚ` of the blocks `ω + (χ(x) + 2)`, and for its codes
`TauCeti.RelationalConfiguration.unravelOrderCode c`.

* A point of the `ω`-part of a block and the first point of the finite part of the same block are
  not near: the interval between them is infinite, as `ω` has no maximum. Points of distinct
  blocks are not near either, by density of `List ℚ`.
* The images of the empty graph and of the complete graph on `ℕ` are not isomorphic: the colour
  of the node `[1, 1/2]` for the empty graph occurs at no node for the complete graph. At the node
  `[1, 2]`, whose entries have the same colour `0`, the two colourings agree.
* The finite part of the block of the root has `χ_c([]) + 2` points, the same number for every
  code.
* For the constant-true code, outside `graphClass`, the image is still a coded linear order, and
  the finite part of the block of a node of length `1` has a size that no finite condensation
  class of the image of a simple graph has; so the image is isomorphic to the image of no code in
  `graphClass`.
-/

public section

namespace TauCeti.Examples.UnravelOrder

open FirstOrder FirstOrder.Language TauCeti.RelationalConfiguration

/-! ### Infinite intervals -/

/-- A point of the `ω`-part of the block of `x` and the first point `(x, 0)` of its finite part
bound an infinite interval. -/
theorem not_isNear_omega_zero (χ : List ℚ → ℕ) (x : List ℚ) {i : ℕ} (hi : χ x + 2 ≤ i) :
    ¬ IsNear (unravelOrderRel χ) (x, i) (x, 0) := by
  rw [isNear_comm, isNear_unravelOrderRel_iff (by simp)]
  simp only [not_and, not_lt]
  exact fun _ => hi

/-- Two points of distinct blocks bound an infinite interval, by density of `List ℚ`. -/
theorem not_isNear_of_ne (χ : List ℚ → ℕ) {x y : List ℚ} (hxy : x ≠ y) (i j : ℕ) :
    ¬ IsNear (unravelOrderRel χ) (x, i) (y, j) := by
  wlog h : x < y generalizing x y i j
  · exact fun hn => this hxy.symm j i ((lt_or_gt_of_ne hxy).resolve_left h) hn.symm
  obtain ⟨z, hxz, hzy⟩ := exists_between h
  refine fun hn => (isNear_iff.1 hn).not_infinite ?_
  exact Set.infinite_of_injective_forall_mem (Prod.mk_right_injective z) fun k =>
    Or.inl ⟨unravelOrderRel_iff.2 (Or.inl hxz), unravelOrderRel_iff.2 (Or.inl hzy)⟩

/-! ### The empty and the complete graph -/

/-- The colour of the node `[1, 1/2]` for the empty graph, two distinct vertices `(0, 1)` that are
not adjacent, occurs at no node for the complete graph. -/
theorem unravelColor_top_ne (y : List ℚ) :
    unravelColor (⊤ : SimpleGraph ℕ).toRelationalConfiguration y ≠
      unravelColor UnravellingChecks.empty [1, 1 / 2] := by
  intro h
  obtain ⟨hl, hb⟩ := unravelColor_eq_iff.1 h
  have h01 := hb 0 (by simp [hl]) 1 (by simp [hl])
  simp [Prod.ext_iff, UnravellingChecks.empty_def, unravelVertex_def] at h01

/-- **The images of the empty and of the complete graph are not isomorphic.** -/
theorem not_isoSetoid_unravelOrderCode_empty_top :
    ¬ isoSetoid Language.order ℕ (unravelOrderCode UnravellingChecks.empty)
      (unravelOrderCode (⊤ : SimpleGraph ℕ).toRelationalConfiguration) := by
  rw [isoSetoid_unravelOrderCode_iff]
  intro h
  obtain ⟨Φ, hΦ⟩ := isoSetoid_iff_exists_orderIso_unravelColor.1 h
  exact unravelColor_top_ne (Φ [1, 1 / 2]) (congrFun hΦ [1, 1 / 2])

/-- Distinct rationals do not suffice to tell the colourings apart: at `[1, 2]` both entries have
colour `0`, both colourings record equal, non-adjacent vertices, and the colours agree. -/
theorem unravelColor_empty_eq_unravelColor_top :
    unravelColor UnravellingChecks.empty [1, 2] =
      unravelColor (⊤ : SimpleGraph ℕ).toRelationalConfiguration [1, 2] := by
  refine unravelColor_eq_iff.2 ⟨rfl, fun i hi j hj => ?_⟩
  have hv (k : ℕ) (hk : k < 2) : unravelVertex [1, 2] k = 0 := by
    interval_cases k <;> simp [unravelVertex_def]
  simp only [List.length_cons, List.length_nil] at hi hj
  refine Prod.ext ?_ ?_ <;> simp [hv i hi, hv j hj, UnravellingChecks.empty_def]

/-! ### The block of the root -/

/-- The finite part of the block of the root has `χ_c([]) + 2` points. -/
theorem ncard_setOf_isNear_root (c : RelationalConfiguration Language.graph ℕ) :
    {q | IsNear (unravelOrderRel (unravelColor c)) ([], 0) q}.ncard = unravelColor c [] + 2 :=
  ncard_setOf_isNear_unravelOrderRel (by simp)

/-- The size of the finite part of the block of the root is the same for every code. -/
theorem ncard_setOf_isNear_root_eq (c d : RelationalConfiguration Language.graph ℕ) :
    {q | IsNear (unravelOrderRel (unravelColor c)) ([], 0) q}.ncard =
      {q | IsNear (unravelOrderRel (unravelColor d)) ([], 0) q}.ncard := by
  rw [ncard_setOf_isNear_root, ncard_setOf_isNear_root,
    (unravelColor_eq_iff (c := c) (d := d) (x := []) (y := [])).2
      ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩]

/-! ### A code outside `graphClass` -/

/-- The image of the constant-true code is a coded linear order. -/
example : unravelOrderCode UnravellingChecks.full ∈ linearOrderClass :=
  unravelOrderCode_mem_linearOrderClass UnravellingChecks.full

/-- **A size of finite condensation classes that no simple graph has.** For every `c ∈ graphClass`,
no condensation class of the order for `c` has the size of the finite part of the block of `[q]`
for the constant-true code (an infinite class has `ncard` `0`). -/
theorem ncard_setOf_isNear_ne {c : RelationalConfiguration Language.graph ℕ}
    (hc : c ∈ graphClass) (q : ℚ) (p : List ℚ × ℕ) :
    {p' | IsNear (unravelOrderRel (unravelColor c)) p p'}.ncard ≠
      {p' | IsNear (unravelOrderRel (unravelColor UnravellingChecks.full)) ([q], 0) p'}.ncard := by
  rw [ncard_setOf_isNear_unravelOrderRel (p := ([q], 0)) (by simp)]
  by_cases hp : {p' | IsNear (unravelOrderRel (unravelColor c)) p p'}.Finite
  · rw [ncard_setOf_isNear_unravelOrderRel (finite_setOf_isNear_unravelOrderRel_iff.1 hp),
      UnravellingChecks.full_def]
    exact fun h => UnravelTree.unravelColor_mk_true_ne hc q p.1 (Nat.add_right_cancel h).symm
  · rw [Set.Infinite.ncard hp]
    omega

/-- The image of the constant-true code is isomorphic to the image of no code in `graphClass`. -/
theorem not_isoSetoid_unravelOrderCode_full {c : RelationalConfiguration Language.graph ℕ}
    (hc : c ∈ graphClass) :
    ¬ isoSetoid Language.order ℕ (unravelOrderCode UnravellingChecks.full)
      (unravelOrderCode c) := by
  rw [isoSetoid_unravelOrderCode_iff, UnravellingChecks.full_def]
  intro h
  obtain ⟨Φ, hΦ⟩ := isoSetoid_iff_exists_orderIso_unravelColor.1 h
  exact UnravelTree.unravelColor_mk_true_ne hc 1 (Φ [1]) (congrFun hΦ [1]).symm

end TauCeti.Examples.UnravelOrder
