/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.VertexCover
public import Mathlib.Order.Filter.Extr

import TauCeti.Data.Set.Card

/-!
# Minimum vertex covers of simple graphs

A *minimum vertex cover* of a simple graph `G` is a vertex cover whose extended cardinality
`Set.encard` in `ℕ∞` is at most that of every vertex cover of `G`. Formulating cardinality
optimality through `Set.encard` avoids the degeneracy of `Set.ncard` on infinite sets and aligns
directly with Mathlib's `ℕ∞`-valued `SimpleGraph.vertexCoverNum`: a vertex cover is minimum if and
only if its `Set.encard` equals `G.vertexCoverNum`, and every simple graph admits a minimum vertex
cover without any finiteness hypothesis. Note that in `ℕ∞` all infinite covers count as `⊤`
(infinite cardinalities are not distinguished, so when `G.vertexCoverNum = ⊤`, every infinite
vertex cover is minimum). A finite vertex cover is minimum if and only if its `Set.ncard` is at
most that of every finite vertex cover (and, on a finite vertex type, at most that of every vertex
cover).

## Main definitions

* `SimpleGraph.IsMinimumVertexCover G c`: `c` is a vertex cover of `G` minimizing `c.encard`.

## Main results

* `SimpleGraph.isMinimumVertexCover_iff_encard_eq`: a vertex cover is minimum if and only if its
  `encard` equals `G.vertexCoverNum`.
* `SimpleGraph.exists_isMinimumVertexCover`: every simple graph has a minimum vertex cover.
* `SimpleGraph.IsMinimumVertexCover.minimal`: every finite minimum vertex cover is minimal.
* `SimpleGraph.Iso.isMinimumVertexCover_preimage_iff` and
  `SimpleGraph.Iso.isMinimumVertexCover_image_iff`: graph isomorphisms preserve minimum vertex
  covers.
* `SimpleGraph.isMinimumVertexCover_iff_ncard_le`: a finite vertex cover is minimum if and only
  if its `Set.ncard` is at most that of every finite vertex cover (and at most that of every vertex
  cover on a finite vertex type via `SimpleGraph.isMinimumVertexCover_iff_ncard_le_of_finite`).

## References

* [Mathlib PR #33032](https://github.com/leanprover-community/mathlib4/pull/33032) for the design
  precedent of `SimpleGraph.IsMinimumVertexCover` and its characteristic API.
-/

public section

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {c c' : Set V}

/-- A vertex set `c` is a *minimum vertex cover* of `G` if it is a vertex cover whose extended
cardinality `Set.encard` in `ℕ∞` is at most that of every vertex cover of `G` (with every infinite
cover counting as `⊤`). -/
def IsMinimumVertexCover (G : SimpleGraph V) (c : Set V) : Prop :=
  G.IsVertexCover c ∧ IsMinOn Set.encard {s | G.IsVertexCover s} c

theorem isMinimumVertexCover_def :
    G.IsMinimumVertexCover c ↔
      G.IsVertexCover c ∧ ∀ ⦃c' : Set V⦄, G.IsVertexCover c' → c.encard ≤ c'.encard := by
  simp [IsMinimumVertexCover, isMinOn_iff]

/-- Every minimum vertex cover is a vertex cover. -/
@[grind →]
theorem IsMinimumVertexCover.isVertexCover (hc : G.IsMinimumVertexCover c) : G.IsVertexCover c :=
  hc.1

/-- A minimum vertex cover has `Set.encard` at most that of any vertex cover. -/
theorem IsMinimumVertexCover.encard_le (hc : G.IsMinimumVertexCover c) (hc' : G.IsVertexCover c') :
    c.encard ≤ c'.encard :=
  (isMinimumVertexCover_def.mp hc).2 hc'

/-- A finite minimum vertex cover is a minimal vertex cover. -/
theorem IsMinimumVertexCover.minimal (hc : G.IsMinimumVertexCover c) (hfin : c.Finite) :
    Minimal G.IsVertexCover c :=
  ⟨hc.1, fun _ hc' hsub ↦ (hfin.eq_of_subset_of_encard_le' hsub (hc.encard_le hc')).ge⟩

/-- A vertex cover is minimum if and only if its `Set.encard` equals the vertex cover number. -/
theorem isMinimumVertexCover_iff_encard_eq :
    G.IsMinimumVertexCover c ↔ G.IsVertexCover c ∧ c.encard = G.vertexCoverNum := by
  refine ⟨fun ⟨hc, hmin⟩ ↦ ⟨hc, ?_⟩, fun ⟨hc, h⟩ ↦
    isMinimumVertexCover_def.2 ⟨hc, fun _ hc' ↦ h.trans_le hc'.vertexCoverNum_le⟩⟩
  unfold vertexCoverNum
  exact (IsMinOn.iInf_eq hc hmin).symm.trans iInf_subtype

/-- Every minimum vertex cover has `Set.encard` equal to the vertex cover number. -/
@[grind →]
theorem IsMinimumVertexCover.encard_eq (hc : G.IsMinimumVertexCover c) :
    c.encard = G.vertexCoverNum :=
  (isMinimumVertexCover_iff_encard_eq.mp hc).2

/-- The `Set.encard` of a minimum vertex cover is the least `Set.encard` among all vertex
covers. -/
theorem IsMinimumVertexCover.isLeast_encard (hc : G.IsMinimumVertexCover c) :
    IsLeast {n : ℕ∞ | ∃ s : Set V, G.IsVertexCover s ∧ s.encard = n} c.encard :=
  ⟨⟨c, hc.isVertexCover, rfl⟩, fun _ ⟨_, hs, hsn⟩ ↦ hsn ▸ hc.encard_le hs⟩

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
theorem Iso.isMinimumVertexCover_preimage_iff (f : G ≃g H) {c : Set W} :
    G.IsMinimumVertexCover (f ⁻¹' c) ↔ H.IsMinimumVertexCover c := by
  rw [isMinimumVertexCover_iff_encard_eq, isMinimumVertexCover_iff_encard_eq,
    isVertexCover_preimage_iso, vertexCoverNum_congr f,
    Set.encard_preimage_of_bijective f.bijective c]

/-- Mapping a vertex set along a graph isomorphism preserves minimum vertex covers. -/
@[simp]
theorem Iso.isMinimumVertexCover_image_iff (f : G ≃g H) {c : Set V} :
    H.IsMinimumVertexCover (f '' c) ↔ G.IsMinimumVertexCover c := by
  rw [RelIso.image_eq_preimage_symm, Iso.isMinimumVertexCover_preimage_iff]

/-- If the vertex cover number is finite, then every minimum vertex cover is finite. -/
theorem IsMinimumVertexCover.finite_of_vertexCoverNum_ne_top (hc : G.IsMinimumVertexCover c)
    (h : G.vertexCoverNum ≠ ⊤) : c.Finite :=
  Set.encard_ne_top_iff.mp (hc.encard_eq.trans_ne h)

/-- A minimum vertex cover has `ncard` at most that of any finite vertex cover. -/
theorem IsMinimumVertexCover.ncard_le (hc : G.IsMinimumVertexCover c) (hc' : G.IsVertexCover c')
    (hfin : c'.Finite) : c.ncard ≤ c'.ncard := by
  have hle := hc.encard_le hc'
  exact (Set.encard_le_encard_iff_ncard_le_ncard (hfin.finite_of_encard_le hle) hfin).1 hle

/-- Every minimum vertex cover has `ncard` equal to `G.vertexCoverNum.toNat`. -/
theorem IsMinimumVertexCover.ncard_eq_toNat (hc : G.IsMinimumVertexCover c) :
    c.ncard = G.vertexCoverNum.toNat := by
  rw [Set.ncard_def, hc.encard_eq]

/-- A finite vertex cover is minimum if and only if its `ncard` equals the vertex cover number. -/
theorem isMinimumVertexCover_iff_ncard_eq (hfin : c.Finite) :
    G.IsMinimumVertexCover c ↔ G.IsVertexCover c ∧ (c.ncard : ℕ∞) = G.vertexCoverNum := by
  rw [isMinimumVertexCover_iff_encard_eq, hfin.cast_ncard_eq]

/-- A finite vertex cover is minimum if and only if its `ncard` is at most that of every finite
vertex cover. -/
theorem isMinimumVertexCover_iff_ncard_le (hfin : c.Finite) :
    G.IsMinimumVertexCover c ↔
      G.IsVertexCover c ∧ ∀ ⦃c' : Set V⦄, G.IsVertexCover c' → c'.Finite → c.ncard ≤ c'.ncard := by
  refine ⟨fun hc ↦ ⟨hc.isVertexCover, fun _ hc' hfin' ↦ hc.ncard_le hc' hfin'⟩,
    fun ⟨hc, h⟩ ↦ isMinimumVertexCover_def.2 ⟨hc, fun c' hc' ↦ ?_⟩⟩
  obtain hfin' | hinf' := c'.finite_or_infinite
  · exact (Set.encard_le_encard_iff_ncard_le_ncard hfin hfin').2 (h hc' hfin')
  · simp [hinf'.encard_eq]

/-- On a finite vertex type, a vertex cover is minimum if and only if it minimizes `ncard` among
all vertex covers. -/
theorem isMinimumVertexCover_iff_ncard_le_of_finite [Finite V] :
    G.IsMinimumVertexCover c ↔
      G.IsVertexCover c ∧ ∀ ⦃c' : Set V⦄, G.IsVertexCover c' → c.ncard ≤ c'.ncard := by
  rw [isMinimumVertexCover_iff_ncard_le c.toFinite]
  exact and_congr_right fun _ ↦ ⟨fun h c' hc' ↦ h hc' c'.toFinite, fun h c' hc' _ ↦ h hc'⟩

/-- The `ncard` of a finite minimum vertex cover is the least `ncard` among all finite vertex
covers. -/
theorem IsMinimumVertexCover.isLeast_ncard (hc : G.IsMinimumVertexCover c) (hfin : c.Finite) :
    IsLeast {n : ℕ | ∃ s : Set V, G.IsVertexCover s ∧ s.Finite ∧ s.ncard = n} c.ncard :=
  ⟨⟨c, hc.1, hfin, rfl⟩, fun _ ⟨_, hs, hsfin, hsn⟩ ↦ hsn ▸ hc.ncard_le hs hsfin⟩

/-- On a finite vertex type, the `ncard` of a minimum vertex cover is the least `ncard` among all
vertex covers. -/
theorem IsMinimumVertexCover.isLeast_ncard_of_finite [Finite V] (hc : G.IsMinimumVertexCover c) :
    IsLeast {n : ℕ | ∃ s : Set V, G.IsVertexCover s ∧ s.ncard = n} c.ncard :=
  let ⟨_, hmin⟩ := hc.isLeast_ncard c.toFinite
  ⟨⟨c, hc.1, rfl⟩, fun _ ⟨s, hs, hsn⟩ ↦ hmin ⟨s, hs, s.toFinite, hsn⟩⟩

end SimpleGraph
