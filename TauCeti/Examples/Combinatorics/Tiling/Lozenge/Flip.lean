/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Flip

/-!
# Checks: the flip of the unit hexagon

The unit hexagon is the set of six faces round `0`. Its two tilings are
`T_a = {(0,3), ((−1,0),1), ((0,−1),2)}` (`highFlipEdges 0`) and
`T_b = {(0,1), (0,2), ((−1,−1),3)}` (`lowFlipEdges 0`).

* `T_a` admits the flip at `0` and becomes `T_b`, and the flip can be undone.
* The flip changes the pairs `W(0)–B(0)`, `W(−e₁)–B(−e₃)`, `W(−e₃)–B(−e₂)` matched by `T_a` into
  `W(0)–B(−e₂)`, `W(−e₁)–B(0)`, `W(−e₃)–B(−e₃)`: a 3-cycle of the black partners.
* Both tilings have one lozenge of each type.
-/

public section

namespace TauCeti.Examples.FlipChecks

open TauCeti

/-- `T_a` is a tiling of the unit hexagon. -/
example : IsTiling (vertexFaces (0, 0) : Set TriFace) (highFlipEdges (0, 0)) :=
  isTiling_highFlipEdges _

/-- `T_b` is a tiling of the unit hexagon. -/
example : IsTiling (vertexFaces (0, 0) : Set TriFace) (lowFlipEdges (0, 0)) :=
  isTiling_lowFlipEdges _

/-- `T_a` admits the flip at `0` and becomes `T_b`. -/
theorem isFlipAt_highFlipEdges_lowFlipEdges :
    IsFlipAt (0, 0) (highFlipEdges (0, 0)) (lowFlipEdges (0, 0)) :=
  isFlipAt_def.2 (Or.inl ⟨subset_rfl, by rw [Set.sdiff_self, Set.empty_union]⟩)

/-- The flip from `T_a` to `T_b` can be undone. -/
example : IsFlip (lowFlipEdges (0, 0)) (highFlipEdges (0, 0)) :=
  isFlipAt_highFlipEdges_lowFlipEdges.isFlip.symm (isTiling_highFlipEdges (0, 0))

/-- The pairs of faces matched by `T_a`: `W(0)–B(0)`, `W(−e₁)–B(−e₃)`, `W(−e₃)–B(−e₂)`. -/
example : (fun e : TriEdge => (e.whiteFace, e.blackFace)) '' highFlipEdges (0, 0) =
    {(⟨(0, 0), true⟩, ⟨(0, 0), false⟩), (⟨(-1, 0), true⟩, ⟨(-1, -1), false⟩),
      (⟨(-1, -1), true⟩, ⟨(0, -1), false⟩)} := by
  simp [highFlipEdges_def, Set.image_insert_eq]

/-- The pairs of faces matched by `T_b`: `W(0)–B(−e₂)`, `W(−e₁)–B(0)`, `W(−e₃)–B(−e₃)`. -/
example : (fun e : TriEdge => (e.whiteFace, e.blackFace)) '' lowFlipEdges (0, 0) =
    {(⟨(0, 0), true⟩, ⟨(0, -1), false⟩), (⟨(-1, 0), true⟩, ⟨(0, 0), false⟩),
      (⟨(-1, -1), true⟩, ⟨(-1, -1), false⟩)} := by
  simp [lowFlipEdges_def, Set.image_insert_eq]

/-- Both tilings have one lozenge of each type. -/
example (k : Fin 3) :
    (∃! e, e ∈ highFlipEdges (0, 0) ∧ e.k = k) ∧ ∃! e, e ∈ lowFlipEdges (0, 0) ∧ e.k = k :=
  ⟨existsUnique_mem_highFlipEdges_k _ k, existsUnique_mem_lowFlipEdges_k _ k⟩

end TauCeti.Examples.FlipChecks
