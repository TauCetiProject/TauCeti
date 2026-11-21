/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.VertexCover

/-!
# Minimum vertex covers of simple graphs

A *minimum vertex cover* of a simple graph `G` is a vertex cover whose extended cardinality
`Set.encard` in `ℕ∞` is at most that of every vertex cover of `G`. Formulating minimality through
`Set.encard` avoids the degeneracy of `Set.ncard` on infinite sets and aligns directly with
Mathlib's `ℕ∞`-valued `SimpleGraph.vertexCoverNum`: a vertex cover is minimum if and only if its
`Set.encard` equals `G.vertexCoverNum`, and every simple graph admits a minimum vertex cover without
any finiteness hypothesis. Note that in `ℕ∞` all infinite covers count as `⊤` (infinite
cardinalities are not distinguished, so when `G.vertexCoverNum = ⊤`, every infinite vertex cover is
minimum). On finite vertex types, minimality agrees with comparison by `Set.ncard`.

## Main definitions

* `SimpleGraph.IsMinimumVertexCover G c`: `c` is a vertex cover of `G` minimizing `c.encard`.

## Main results

* `SimpleGraph.isMinimumVertexCover_iff_encard_eq`: a vertex cover is minimum if and only if its
  `encard` equals `G.vertexCoverNum`.
* `SimpleGraph.exists_isMinimumVertexCover`: every simple graph has a minimum vertex cover.
* `SimpleGraph.isMinimumVertexCover_preimage_iso` and `SimpleGraph.isMinimumVertexCover_image_iso`:
  graph isomorphisms preserve minimum vertex covers.
* `SimpleGraph.isMinimumVertexCover_iff_ncard_le`: on a finite vertex type, minimality is
  equivalently characterized by `Set.ncard`.
-/

public section

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {c c' : Set V}

/-- A vertex set `c` is a *minimum vertex cover* of `G` if it is a vertex cover whose extended
cardinality `Set.encard` in `ℕ∞` is at most that of every vertex cover of `G` (with every infinite
cover counting as `⊤`). -/
def IsMinimumVertexCover (G : SimpleGraph V) (c : Set V) : Prop :=
  G.IsVertexCover c ∧ ∀ ⦃c' : Set V⦄, G.IsVertexCover c' → c.encard ≤ c'.encard

theorem isMinimumVertexCover_def :
    G.IsMinimumVertexCover c ↔
      G.IsVertexCover c ∧ ∀ ⦃c' : Set V⦄, G.IsVertexCover c' → c.encard ≤ c'.encard :=
  Iff.rfl

/-- Every minimum vertex cover is a vertex cover. -/
theorem IsMinimumVertexCover.isVertexCover (hc : G.IsMinimumVertexCover c) : G.IsVertexCover c :=
  hc.1

/-- A minimum vertex cover has `Set.encard` at most that of any vertex cover. -/
theorem IsMinimumVertexCover.encard_le (hc : G.IsMinimumVertexCover c) (hc' : G.IsVertexCover c') :
    c.encard ≤ c'.encard :=
  hc.2 hc'

/-- A vertex cover is minimum if and only if its `Set.encard` equals the vertex cover number. -/
theorem isMinimumVertexCover_iff_encard_eq :
    G.IsMinimumVertexCover c ↔ G.IsVertexCover c ∧ c.encard = G.vertexCoverNum := by
  refine and_congr_right fun hc ↦ ⟨fun h ↦ ?_, fun h c' hc' ↦ ?_⟩
  · obtain ⟨s, hs_eq, hs⟩ := G.vertexCoverNum_exists
    exact le_antisymm (hs_eq ▸ h hs) hc.vertexCoverNum_le
  · exact h.trans_le hc'.vertexCoverNum_le

/-- Every minimum vertex cover has `Set.encard` equal to the vertex cover number. -/
theorem IsMinimumVertexCover.encard_eq (hc : G.IsMinimumVertexCover c) :
    c.encard = G.vertexCoverNum :=
  (isMinimumVertexCover_iff_encard_eq.mp hc).2

/-- Any two minimum vertex covers of the same graph have the same `Set.encard` (with every
infinite cover counting as `⊤`). -/
theorem IsMinimumVertexCover.encard_eq_of_isMinimumVertexCover (hc : G.IsMinimumVertexCover c)
    (hc' : G.IsMinimumVertexCover c') : c.encard = c'.encard :=
  hc.encard_eq.trans hc'.encard_eq.symm

/-- The `Set.encard` of a minimum vertex cover is the least `Set.encard` among all vertex
covers. -/
theorem IsMinimumVertexCover.isLeast_encard (hc : G.IsMinimumVertexCover c) :
    IsLeast {n : ℕ∞ | ∃ s : Set V, G.IsVertexCover s ∧ s.encard = n} c.encard :=
  ⟨⟨c, hc.1, rfl⟩, fun _ ⟨_, hs, hsn⟩ ↦ hsn ▸ hc.2 hs⟩

/-- Every simple graph admits a minimum vertex cover. -/
theorem exists_isMinimumVertexCover (G : SimpleGraph V) :
    ∃ c : Set V, G.IsMinimumVertexCover c := by
  obtain ⟨c, hc_eq, hc⟩ := G.vertexCoverNum_exists
  exact ⟨c, isMinimumVertexCover_iff_encard_eq.mpr ⟨hc, hc_eq⟩⟩

/-- The empty set is a minimum vertex cover if and only if the graph is empty. -/
@[simp]
theorem isMinimumVertexCover_empty_iff : G.IsMinimumVertexCover ∅ ↔ G = ⊥ := by
  rw [isMinimumVertexCover_iff_encard_eq, isVertexCover_empty, Set.encard_empty,
    eq_comm (a := (0 : ℕ∞)), vertexCoverNum_eq_zero, and_self]

/-- The unique minimum vertex cover of the empty graph is the empty set. -/
@[simp]
theorem isMinimumVertexCover_bot_iff : (⊥ : SimpleGraph V).IsMinimumVertexCover c ↔ c = ∅ := by
  rw [isMinimumVertexCover_iff_encard_eq, vertexCoverNum_bot]
  simp

/-- On a subsingleton vertex type, the unique minimum vertex cover is the empty set. -/
@[simp]
theorem isMinimumVertexCover_of_subsingleton_iff [Subsingleton V] :
    G.IsMinimumVertexCover c ↔ c = ∅ := by
  have hG : G = ⊥ := Subsingleton.elim G ⊥
  rw [hG, isMinimumVertexCover_bot_iff]

/-- Pulling a vertex set back along a graph isomorphism preserves minimum vertex covers. -/
@[simp]
theorem isMinimumVertexCover_preimage_iso (f : G ≃g H) {c : Set W} :
    G.IsMinimumVertexCover (f ⁻¹' c) ↔ H.IsMinimumVertexCover c := by
  rw [isMinimumVertexCover_iff_encard_eq, isMinimumVertexCover_iff_encard_eq,
    isVertexCover_preimage_iso, vertexCoverNum_congr f,
    ← Set.image_eq_preimage_of_inverse f.apply_symm_apply f.symm_apply_apply,
    f.symm.injective.encard_image]

/-- Mapping a vertex set along a graph isomorphism preserves minimum vertex covers. -/
@[simp]
theorem isMinimumVertexCover_image_iso (f : G ≃g H) {c : Set V} :
    H.IsMinimumVertexCover (f '' c) ↔ G.IsMinimumVertexCover c := by
  rw [RelIso.image_eq_preimage_symm, isMinimumVertexCover_preimage_iso]

/-- If the vertex cover number is finite, then every minimum vertex cover is finite. -/
theorem IsMinimumVertexCover.finite_of_vertexCoverNum_ne_top (hc : G.IsMinimumVertexCover c)
    (h : G.vertexCoverNum ≠ ⊤) : c.Finite :=
  Set.encard_ne_top_iff.mp (hc.encard_eq.trans_ne h)

/-- A minimum vertex cover has `ncard` at most that of any finite vertex cover. -/
theorem IsMinimumVertexCover.ncard_le (hc : G.IsMinimumVertexCover c) (hc' : G.IsVertexCover c')
    (hfin : c'.Finite) : c.ncard ≤ c'.ncard :=
  ENat.toNat_le_toNat (hc.encard_le hc') (Set.encard_ne_top_iff.mpr hfin)

/-- Every minimum vertex cover has `ncard` equal to `G.vertexCoverNum.toNat`. -/
theorem IsMinimumVertexCover.ncard_eq_toNat (hc : G.IsMinimumVertexCover c) :
    c.ncard = G.vertexCoverNum.toNat := by
  rw [Set.ncard_def, hc.encard_eq]

/-- Any two minimum vertex covers of the same graph have the same `ncard`. -/
theorem IsMinimumVertexCover.ncard_eq_of_isMinimumVertexCover (hc : G.IsMinimumVertexCover c)
    (hc' : G.IsMinimumVertexCover c') : c.ncard = c'.ncard := by
  rw [hc.ncard_eq_toNat, hc'.ncard_eq_toNat]

/-- A finite vertex cover is minimum if and only if its `ncard` equals the vertex cover number. -/
theorem isMinimumVertexCover_iff_ncard_eq (hfin : c.Finite) :
    G.IsMinimumVertexCover c ↔ G.IsVertexCover c ∧ (c.ncard : ℕ∞) = G.vertexCoverNum := by
  rw [isMinimumVertexCover_iff_encard_eq, hfin.cast_ncard_eq]

/-- On a finite vertex type, a vertex cover is minimum if and only if it minimizes `ncard` among
all vertex covers. -/
theorem isMinimumVertexCover_iff_ncard_le [Finite V] :
    G.IsMinimumVertexCover c ↔
      G.IsVertexCover c ∧ ∀ ⦃c' : Set V⦄, G.IsVertexCover c' → c.ncard ≤ c'.ncard := by
  refine and_congr_right fun _ ↦ ⟨fun h c' hc' ↦ ?_, fun h c' hc' ↦ ?_⟩
  · exact ENat.toNat_le_toNat (h hc') (Set.encard_ne_top_iff.mpr c'.toFinite)
  · rw [← c.toFinite.cast_ncard_eq, ← c'.toFinite.cast_ncard_eq]
    exact Nat.cast_le.mpr (h hc')

/-- On a finite vertex type, the `ncard` of a minimum vertex cover is the least `ncard` among all
vertex covers. -/
theorem IsMinimumVertexCover.isLeast_ncard [Finite V] (hc : G.IsMinimumVertexCover c) :
    IsLeast {n : ℕ | ∃ s : Set V, G.IsVertexCover s ∧ s.ncard = n} c.ncard :=
  ⟨⟨c, hc.1, rfl⟩, fun _ ⟨s, hs, hsn⟩ ↦ hsn ▸ hc.ncard_le hs s.toFinite⟩

end SimpleGraph
