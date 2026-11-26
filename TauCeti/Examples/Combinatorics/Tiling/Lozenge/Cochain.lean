/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Hole

/-!
# Regression examples: edge cochains and simply connected regions

* A single face `W(0)` is simply connected.
* The ring `R_ring` of the twelve faces other than `W(0)` that meet `W(0)` is connected but not
  simply connected: the ray cochain `TauCeti.rayCochain W(0)`, equal to `1` on the edges
  `((i, 0), 2)` and `((i, 0), 3)` for `i ≥ 1` (those crossed by the path of faces `B(1,0), W(1,0),
  B(2,0), W(2,0), …`) and `0` elsewhere, is closed on every face except `W(0)`, while it sums to
  `1` around the boundary of `W(0)`, whose three edges are edges of `R_ring`. The same cochain
  shows that the plane minus `W(0)` is not simply connected, so the simple connectivity of the
  plane needs every face.
* The unit hexagon around `0` is simply connected, by shelling in the order `W(0)`, `B(0)`,
  `W(−e₁)`, `B(−e₃)`, `W(−e₃)` (each glued along one edge, adding one new vertex) and `B(−e₂)`
  (glued along two edges).
* The neutral cochain `c₀` is not closed on any face; the cochain of the all-type-1 tiling `M₁`
  (`1` along `e₁` and `e₃`, `0` along `e₂`) has primitive `x`, and that of the all-type-3 tiling
  `M₃` is `0`, with primitive `0`.
-/

public section

namespace TauCeti.Examples.Cochain

open TauCeti

/-- A single face is simply connected. -/
example : IsSimplyConnectedRegion {(⟨(0, 0), true⟩ : TriFace)} :=
  isSimplyConnectedRegion_singleton _

/-- The ray cochain of `W(0)`, equal to `1` on the edges `((i, 0), 2)` and `((i, 0), 3)` for
`i ≥ 1` and `0` elsewhere, is closed on every face other than `W(0)`. -/
theorem isClosedCochainOn_rayCochain_whiteZero :
    IsClosedCochainOn {f | f ≠ ⟨(0, 0), true⟩} (rayCochain ⟨(0, 0), true⟩) :=
  isClosedCochainOn_iff_faceSum.2 fun _ hf => faceSum_rayCochain_of_ne hf

/-- The ray cochain of `W(0)` is not exact on any region containing the three faces `B(0, −1)`,
`B(1, 0)` and `B(0, 0)`, which carry the three edges of `W(0)`. -/
theorem not_isExactCochainOn_rayCochain_whiteZero {R : Set TriFace} (h₁ : ⟨(0, -1), false⟩ ∈ R)
    (h₂ : ⟨(1, 0), false⟩ ∈ R) (h₃ : ⟨(0, 0), false⟩ ∈ R) :
    ¬ IsExactCochainOn R (rayCochain ⟨(0, 0), true⟩) := by
  intro h
  obtain ⟨g, hg⟩ := isExactCochainOn_def.1 h
  rw [isCochainPrimitiveOn_def] at hg
  have e₁ := hg ⟨(0, 0), 0⟩ (mem_regionEdges_iff.2 (Or.inr (by simpa using h₁)))
  have e₂ := hg ⟨(1, 0), 1⟩ (mem_regionEdges_iff.2 (Or.inr (by simpa using h₂)))
  have e₃ := hg ⟨(0, 0), 2⟩ (mem_regionEdges_iff.2 (Or.inr (by simpa using h₃)))
  simp only [rayCochain_def, TriEdge.target_mk, latticeDir_zero, latticeDir_one,
    latticeDir_two] at e₁ e₂ e₃
  norm_num at e₁ e₂ e₃
  omega

/-- The plane minus `W(0)` is not simply connected. -/
example : ¬ IsSimplyConnectedRegion {f | f ≠ ⟨(0, 0), true⟩} := fun h =>
  not_isExactCochainOn_rayCochain_whiteZero (by simp) (by simp) (by simp)
    (h.isExactCochainOn_of_isClosedCochainOn _ isClosedCochainOn_rayCochain_whiteZero)

/-- The ring `R_ring` of the twelve faces other than `W(0)` that meet `W(0)`. -/
@[expose] def ringRegion : Set TriFace :=
  {⟨(-1, 0), true⟩, ⟨(-1, -1), true⟩, ⟨(0, -1), true⟩, ⟨(1, 0), true⟩, ⟨(1, 1), true⟩,
    ⟨(0, 1), true⟩, ⟨(0, 0), false⟩, ⟨(0, -1), false⟩, ⟨(-1, -1), false⟩, ⟨(1, -1), false⟩,
    ⟨(1, 0), false⟩, ⟨(1, 1), false⟩}

/-- The ring `R_ring` listed face by face, each face sharing a vertex with an earlier one: first
`B(0)`, then faces at the vertex `0` or at `e₃`, both vertices of `B(0)`, or at `e₁`, a vertex of
`B(0, −1)`. -/
theorem ringRegion_eq : ringRegion =
    insert ⟨(1, -1), false⟩ (insert ⟨(0, -1), true⟩ (insert ⟨(1, 1), false⟩
      (insert ⟨(1, 0), false⟩ (insert ⟨(1, 0), true⟩ (insert ⟨(0, 1), true⟩
        (insert ⟨(1, 1), true⟩ (insert ⟨(0, -1), false⟩ (insert ⟨(-1, -1), false⟩
          (insert ⟨(-1, -1), true⟩ (insert ⟨(-1, 0), true⟩ {⟨(0, 0), false⟩})))))))))) := by
  ext f
  simp only [ringRegion, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- **The ring `R_ring` is connected**, although it is not simply connected (below). -/
theorem isConnectedRegion_ringRegion : IsConnectedRegion ringRegion := by
  rw [ringRegion_eq]
  have hB₀ : ∀ S : Set TriFace, (⟨(0, 0), false⟩ : TriFace) ∈ S →
      (0, 0) ∈ regionVertices S ∧ (1, 1) ∈ regionVertices S := fun S hS =>
    ⟨mem_regionVertices.2 ⟨_, hS, by simp⟩, mem_regionVertices.2 ⟨_, hS, by simp⟩⟩
  have hB₁ : ∀ S : Set TriFace, (⟨(0, -1), false⟩ : TriFace) ∈ S → (1, 0) ∈ regionVertices S :=
    fun S hS => mem_regionVertices.2 ⟨_, hS, by simp⟩
  refine IsConnectedRegion.insert_of_mem_regionVertices (u := (1, 0)) ?_ (by simp)
    (hB₁ _ (by simp))
  refine IsConnectedRegion.insert_of_mem_regionVertices (u := (1, 0)) ?_ (by simp)
    (hB₁ _ (by simp))
  refine IsConnectedRegion.insert_of_mem_regionVertices (u := (1, 1)) ?_ (by simp)
    (hB₀ _ (by simp)).2
  refine IsConnectedRegion.insert_of_mem_regionVertices (u := (1, 1)) ?_ (by simp)
    (hB₀ _ (by simp)).2
  refine IsConnectedRegion.insert_of_mem_regionVertices (u := (1, 0)) ?_ (by simp)
    (hB₁ _ (by simp))
  refine IsConnectedRegion.insert_of_mem_regionVertices (u := (1, 1)) ?_ (by simp)
    (hB₀ _ (by simp)).2
  refine IsConnectedRegion.insert_of_mem_regionVertices (u := (1, 1)) ?_ (by simp)
    (hB₀ _ (by simp)).2
  refine IsConnectedRegion.insert_of_mem_regionVertices (u := (0, 0)) ?_ (by simp)
    (hB₀ _ (by simp)).1
  refine IsConnectedRegion.insert_of_mem_regionVertices (u := (0, 0)) ?_ (by simp)
    (hB₀ _ (by simp)).1
  refine IsConnectedRegion.insert_of_mem_regionVertices (u := (0, 0)) ?_ (by simp)
    (hB₀ _ (by simp)).1
  refine IsConnectedRegion.insert_of_mem_regionVertices (u := (0, 0)) ?_ (by simp)
    (hB₀ _ (by simp)).1
  exact isConnectedRegion_singleton _

/-- The ring around `W(0)` is not simply connected. -/
example : ¬ IsSimplyConnectedRegion ringRegion := fun h =>
  not_isExactCochainOn_rayCochain_whiteZero (by simp [ringRegion]) (by simp [ringRegion])
    (by simp [ringRegion])
    (h.isExactCochainOn_of_isClosedCochainOn _
      (isClosedCochainOn_rayCochain_whiteZero.mono fun f hf => by
        simp only [ringRegion, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
        rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp))

/-- The unit hexagon around `0` is simply connected, by shelling. -/
example : IsSimplyConnectedRegion
    {⟨(0, -1), false⟩, ⟨(-1, -1), true⟩, ⟨(-1, -1), false⟩, ⟨(-1, 0), true⟩, ⟨(0, 0), false⟩,
      ⟨(0, 0), true⟩} := by
  have h1 := isSimplyConnectedRegion_singleton (⟨(0, 0), true⟩ : TriFace)
  have h2 := h1.insert_of_notMem_regionVertices (f := ⟨(0, 0), false⟩) (i := 2) (p := (0, 1))
    (by simp) (by simp) (by simp [Prod.ext_iff])
  have h3 := h2.insert_of_notMem_regionVertices (f := ⟨(-1, 0), true⟩) (i := 1) (p := (-1, 0))
    (by simp) (by simp) (by simp [Prod.ext_iff])
  have h4 := h3.insert_of_notMem_regionVertices (f := ⟨(-1, -1), false⟩) (i := 0) (p := (-1, -1))
    (by simp) (by simp) (by simp [Prod.ext_iff])
  have h5 := h4.insert_of_notMem_regionVertices (f := ⟨(-1, -1), true⟩) (i := 2) (p := (0, -1))
    (by simp) (by simp) (by simp [Prod.ext_iff])
  exact h5.insert_of_two_edges (f := ⟨(0, -1), false⟩) (i := 0) (j := 1) (by decide)
    (by simp) (by simp)

/-- The neutral cochain is not closed on any face: on `W(v)` it gives `0 + 0 ≠ 1`. -/
example (f : TriFace) : ¬ IsClosedCochainOn {f} neutralIncrement := by
  obtain ⟨v, _ | _⟩ := f <;> simp

/-- The cochain of the all-type-1 tiling `M₁` has primitive `x`. -/
example : IsCochainPrimitiveOn Set.univ (fun e => if e.k = 1 then 0 else 1) fun u => u.1 := by
  refine isCochainPrimitiveOn_def.2 ?_
  rintro ⟨v, k⟩ -
  fin_cases k <;> simp

/-- The cochain of the all-type-3 tiling `M₃` is `0`, with primitive `0`. -/
example : IsCochainPrimitiveOn Set.univ 0 0 := isCochainPrimitiveOn_def.2 fun _ _ => by simp

end TauCeti.Examples.Cochain
