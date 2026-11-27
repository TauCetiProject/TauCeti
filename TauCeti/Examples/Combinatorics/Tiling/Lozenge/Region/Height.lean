/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Region.Height
public import TauCeti.Combinatorics.Tiling.Lozenge.Flip
public import TauCeti.Examples.Combinatorics.Tiling.Lozenge.Cochain

/-!
# Checks: heights on regions

* `R = {W(0)}` with `H(0) = 0`: the free tilings `{(0,1)}`, `{(e₁,2)}`, `{(0,3)}` have
  `(H(e₁), H(e₃)) = (1,1)`, `(0,1)`, `(0,0)`, which are all the height functions; none is a
  tiling, because neutral boundary increments would force `H(e₁) = 0 = H(e₃)` and `H(e₃) = 1`.
* On `R_ring` the tiling `T = {(0,2), ((1,1),1), ((0,−1),3), ((−1,−1),3), ((1,0),1), ((1,1),2)}`
  has increments `0`, `0`, `1` along `(0,1)`, `(e₁,2)`, `(0,3)`, which sum to `−1` around `W(0)`:
  `T` has no height function, so simple connectivity cannot be dropped.
* On the unit hexagon round `0`, normalised by `H(1,0) = 0`: the tilings
  `T_a = highFlipEdges 0` and `T_b = lowFlipEdges 0` both give `H = 0` at `(1,0)`, `(0,1)`,
  `(1,1)` and `H = −1` at `(−1,0)`, `(0,−1)`, `(−1,−1)`, while `H(0) = 0` for `T_a` (because
  `(0,1) ∉ T_a`) and `H(0) = −1` for `T_b` (because `(0,1) ∈ T_b`).
-/

public section

namespace TauCeti.Examples.LozengeRegionHeightChecks

open TauCeti

/-! ### A single face -/

/-- The white face `W(0)`. -/
abbrev whiteZero : TriFace := ⟨(0, 0), true⟩

theorem mem_regionEdges_whiteZero {e : TriEdge} (he : e ∈ whiteZero.edges) :
    e ∈ regionEdges {whiteZero} :=
  edges_subset_regionEdges rfl he

/-- The increments of a height function on `W(0)` with free tiling `T` along the edges `(0,1)`,
`(e₁,2)` and `(0,3)`. -/
theorem increments_whiteZero {H : ℤ × ℤ → ℤ} {T : Set TriEdge}
    (hH : IsHeightFunctionOn {whiteZero} H) (hT : tilingOfHeightOn {whiteZero} H = T) :
    H (1, 0) - H 0 = heightCochain T ⟨(0, 0), 0⟩ ∧
      H (1, 1) - H (1, 0) = heightCochain T ⟨(1, 0), 1⟩ ∧
      H (1, 1) - H 0 = heightCochain T ⟨(0, 0), 2⟩ := by
  subst hT
  have h₁ := hH.heightCochain_tilingOfHeightOn (e := ⟨(0, 0), 0⟩)
    (mem_regionEdges_whiteZero (by simp))
  have h₂ := hH.heightCochain_tilingOfHeightOn (e := ⟨(1, 0), 1⟩)
    (mem_regionEdges_whiteZero (by simp))
  have h₃ := hH.heightCochain_tilingOfHeightOn (e := ⟨(0, 0), 2⟩)
    (mem_regionEdges_whiteZero (by simp))
  simp only [TriEdge.target_mk, latticeDir_zero, latticeDir_one, latticeDir_two,
    Prod.mk_add_mk, Prod.mk_zero_zero] at h₁ h₂ h₃
  norm_num at h₁ h₂ h₃
  exact ⟨h₁.symm, h₂.symm, h₃.symm⟩

/-- The free tiling `{(0,1)}` of `W(0)` has `(H(e₁), H(e₃)) = (1, 1)`. -/
example {H : ℤ × ℤ → ℤ} (hH : IsHeightFunctionOn {whiteZero} H)
    (hT : tilingOfHeightOn {whiteZero} H = {⟨(0, 0), 0⟩}) (h0 : H 0 = 0) :
    (H (1, 0), H (1, 1)) = (1, 1) := by
  have := increments_whiteZero hH hT
  simp [heightCochain_of_mem, heightCochain_of_notMem] at this
  simp only [Prod.mk.injEq]
  omega

/-- The free tiling `{(e₁,2)}` of `W(0)` has `(H(e₁), H(e₃)) = (0, 1)`. -/
example {H : ℤ × ℤ → ℤ} (hH : IsHeightFunctionOn {whiteZero} H)
    (hT : tilingOfHeightOn {whiteZero} H = {⟨(1, 0), 1⟩}) (h0 : H 0 = 0) :
    (H (1, 0), H (1, 1)) = (0, 1) := by
  have := increments_whiteZero hH hT
  simp [heightCochain_of_mem, heightCochain_of_notMem] at this
  simp only [Prod.mk.injEq]
  omega

/-- The free tiling `{(0,3)}` of `W(0)` has `(H(e₁), H(e₃)) = (0, 0)`. -/
example {H : ℤ × ℤ → ℤ} (hH : IsHeightFunctionOn {whiteZero} H)
    (hT : tilingOfHeightOn {whiteZero} H = {⟨(0, 0), 2⟩}) (h0 : H 0 = 0) :
    (H (1, 0), H (1, 1)) = (0, 0) := by
  have := increments_whiteZero hH hT
  simp [heightCochain_of_mem, heightCochain_of_notMem] at this
  simp only [Prod.mk.injEq]
  omega

/-- These are all the height functions on `W(0)` vanishing at `0`. -/
example {H : ℤ × ℤ → ℤ} (hH : IsHeightFunctionOn {whiteZero} H) (h0 : H 0 = 0) :
    (H (1, 0), H (1, 1)) ∈ ({(1, 1), (0, 1), (0, 0)} : Set (ℤ × ℤ)) := by
  have h₁ := isHeightFunctionOn_def.1 hH ⟨(0, 0), 0⟩ (mem_regionEdges_whiteZero (by simp))
  have h₂ := isHeightFunctionOn_def.1 hH ⟨(1, 0), 1⟩ (mem_regionEdges_whiteZero (by simp))
  have h₃ := isHeightFunctionOn_def.1 hH ⟨(0, 0), 2⟩ (mem_regionEdges_whiteZero (by simp))
  simp only [TriEdge.target_mk, latticeDir_zero, latticeDir_one, latticeDir_two,
    Prod.mk_add_mk, Prod.mk_zero_zero] at h₁ h₂ h₃
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  norm_num at h₁ h₂ h₃
  omega

/-- No height function on `W(0)` gives a tiling: neutral increments along the three boundary
edges would force `H(e₁) = H(0) = H(e₃)` and `H(e₃) = H(0) + 1`. -/
example {H : ℤ × ℤ → ℤ} (hH : IsHeightFunctionOn {whiteZero} H) :
    ¬IsTiling {whiteZero} (tilingOfHeightOn {whiteZero} H) := by
  rw [hH.isTiling_tilingOfHeightOn_iff]
  intro h
  have hb : ∀ e ∈ whiteZero.edges, e ∈ boundaryEdges {whiteZero} := by
    intro e he
    simp only [TriFace.edges_mk_true, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> rw [mem_boundaryEdges_iff] <;> simp [Prod.ext_iff]
  have h₁ := h ⟨(0, 0), 0⟩ (hb _ (by simp))
  have h₂ := h ⟨(1, 0), 1⟩ (hb _ (by simp))
  have h₃ := h ⟨(0, 0), 2⟩ (hb _ (by simp))
  simp at h₁ h₂ h₃
  omega

/-! ### The unit hexagon -/

/-- The unit hexagon: the six faces round `0`. -/
abbrev hexagon : Set TriFace := (vertexFaces 0 : Set TriFace)

/-- An edge whose white face lies in the unit hexagon is an edge of it. -/
theorem mem_regionEdges_hexagon (e : TriEdge) (he : 0 ∈ e.whiteFace.vertices := by
    simp [Prod.ext_iff]) : e ∈ regionEdges hexagon :=
  mem_regionEdges_iff.2 (Or.inl (by simpa using he))

/-- The increments of a height function on the hexagon with free tiling `T` along the three edges
out of `0` and the three edges into `0`. -/
theorem increments_hexagon {H : ℤ × ℤ → ℤ} {T : Set TriEdge}
    (hH : IsHeightFunctionOn hexagon H) (hT : tilingOfHeightOn hexagon H = T) :
    H (1, 0) - H 0 = heightCochain T ⟨0, 0⟩ ∧ H (0, 1) - H 0 = heightCochain T ⟨0, 1⟩ ∧
      H (1, 1) - H 0 = heightCochain T ⟨0, 2⟩ ∧
      H 0 - H (-1, 0) = heightCochain T ⟨(-1, 0), 0⟩ ∧
      H 0 - H (0, -1) = heightCochain T ⟨(0, -1), 1⟩ ∧
      H 0 - H (-1, -1) = heightCochain T ⟨(-1, -1), 2⟩ := by
  subst hT
  have h₁ := hH.heightCochain_tilingOfHeightOn (e := ⟨0, 0⟩) (mem_regionEdges_hexagon _)
  have h₂ := hH.heightCochain_tilingOfHeightOn (e := ⟨0, 1⟩) (mem_regionEdges_hexagon _)
  have h₃ := hH.heightCochain_tilingOfHeightOn (e := ⟨0, 2⟩) (mem_regionEdges_hexagon _)
  have h₄ := hH.heightCochain_tilingOfHeightOn (e := ⟨(-1, 0), 0⟩) (mem_regionEdges_hexagon _)
  have h₅ := hH.heightCochain_tilingOfHeightOn (e := ⟨(0, -1), 1⟩) (mem_regionEdges_hexagon _)
  have h₆ := hH.heightCochain_tilingOfHeightOn (e := ⟨(-1, -1), 2⟩)
    (mem_regionEdges_hexagon _)
  simp only [TriEdge.target_mk, latticeDir_zero, latticeDir_one, latticeDir_two,
    Prod.mk_add_mk] at h₁ h₂ h₃ h₄ h₅ h₆
  norm_num at h₁ h₂ h₃ h₄ h₅ h₆
  exact ⟨h₁.symm, h₂.symm, h₃.symm, h₄.symm, h₅.symm, h₆.symm⟩

/-- The heights of `T_a = highFlipEdges 0` on the hexagon, normalised by `H(1,0) = 0`. -/
example {H : ℤ × ℤ → ℤ} (hH : IsHeightFunctionOn hexagon H)
    (hT : tilingOfHeightOn hexagon H = highFlipEdges 0) (h₀ : H (1, 0) = 0) :
    H (0, 1) = 0 ∧ H (1, 1) = 0 ∧ H (-1, 0) = -1 ∧ H (0, -1) = -1 ∧ H (-1, -1) = -1 ∧
      H 0 = 0 := by
  have := increments_hexagon hH hT
  simp [heightCochain_of_mem, heightCochain_of_notMem, Prod.ext_iff] at this
  omega

/-- The heights of `T_b = lowFlipEdges 0` on the hexagon, normalised by `H(1,0) = 0`. -/
example {H : ℤ × ℤ → ℤ} (hH : IsHeightFunctionOn hexagon H)
    (hT : tilingOfHeightOn hexagon H = lowFlipEdges 0) (h₀ : H (1, 0) = 0) :
    H (0, 1) = 0 ∧ H (1, 1) = 0 ∧ H (-1, 0) = -1 ∧ H (0, -1) = -1 ∧ H (-1, -1) = -1 ∧
      H 0 = -1 := by
  have := increments_hexagon hH hT
  simp [heightCochain_of_mem, heightCochain_of_notMem, Prod.ext_iff] at this
  omega

/-! ### The ring -/

/-- The tiling `T = {(0,2), ((1,1),1), ((0,−1),3), ((−1,−1),3), ((1,0),1), ((1,1),2)}` of `R_ring`
(directions numbered `1, 2, 3` as in the roadmap, `0, 1, 2` in Lean). -/
def ringTiling : Finset TriEdge :=
  {⟨(0, 0), 1⟩, ⟨(1, 1), 0⟩, ⟨(0, -1), 2⟩, ⟨(-1, -1), 2⟩, ⟨(1, 0), 0⟩, ⟨(1, 1), 1⟩}

open TauCeti.Examples.Cochain in
/-- `T` is a tiling of `R_ring`. -/
theorem isTiling_ringTiling : IsTiling ringRegion (ringTiling : Set TriEdge) := by
  refine isTiling_def.2 ⟨fun e he f hf => ?_, fun f hf => ?_⟩
  · rw [TriFace.mem_edges_iff] at hf
    simp only [ringTiling, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hf with rfl | rfl <;>
      simp [ringRegion]
  · rw [TriFace.existsUnique_mem_edges_iff]
    simp only [ringRegion, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [ExistsUnique, Fin.forall_fin_succ, ringTiling, Prod.ext_iff]

open TauCeti.Examples.Cochain in
/-- The height cochain of `T` is `0`, `0`, `1` along the edges `(0,1)`, `(e₁,2)`, `(0,3)` of
`W(0)`, so it sums to `−1` around `W(0)`. -/
example : faceSum (heightCochain (ringTiling : Set TriEdge)) ⟨(0, 0), true⟩ = -1 := by
  rw [faceSum_def]
  simp [heightCochain_of_notMem, ringTiling, neutralIncrement_def]

open TauCeti.Examples.Cochain in
/-- **Simple connectivity cannot be dropped**: the tiling `T` of the connected region `R_ring` has
no height function on `R_ring`. -/
example : ¬ ∃ H, IsHeightFunctionOn ringRegion H ∧
    tilingOfHeightOn ringRegion H = (ringTiling : Set TriEdge) := by
  rintro ⟨H, hH, hT⟩
  have h₁ := hH.heightCochain_tilingOfHeightOn (e := ⟨(0, 0), 0⟩)
    (mem_regionEdges_iff.2 (Or.inr (by simp [ringRegion])))
  have h₂ := hH.heightCochain_tilingOfHeightOn (e := ⟨(1, 0), 1⟩)
    (mem_regionEdges_iff.2 (Or.inr (by simp [ringRegion])))
  have h₃ := hH.heightCochain_tilingOfHeightOn (e := ⟨(0, 0), 2⟩)
    (mem_regionEdges_iff.2 (Or.inr (by simp [ringRegion])))
  rw [hT] at h₁ h₂ h₃
  simp [heightCochain_of_notMem, ringTiling, neutralIncrement_def, latticeDir_zero,
    latticeDir_one, latticeDir_two] at h₁ h₂ h₃
  omega

end TauCeti.Examples.LozengeRegionHeightChecks
