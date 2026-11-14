/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Compactness.Compact
import TauCeti.GroupTheory.GroupAction.Stabilizer.Basic

/-!
# Open and compact set stabilizers for continuous group actions

For a topological space `M` acting continuously on a topological space `X`, the set
`{m : M | MapsTo (m • ·) K U}` of elements carrying a compact subset `K ⊆ X` into an open subset
`U ⊆ X` is open in `M` (`IsCompact.isOpen_setOf_mapsTo_smul`), by the generalized tube lemma applied
to `{m} ×ˢ K` inside the preimage of `U` under `(· • ·)`.

Consequently, for a group `G` with continuous inversion acting continuously on `X`, the setwise
stabilizer `MulAction.stabilizer G s` (under `open scoped Pointwise`, `{g | g • s = s}`) of a
compact open subset `s ⊆ X` is open in `G`, being `{g | MapsTo (g • ·) s s} ∩
(·⁻¹) ⁻¹' {g | MapsTo (g • ·) s s}` via `TauCeti.mem_stabilizer_set_iff_mapsTo`. Only continuity of
inversion on `G` and joint continuity of the action on `X` are required; continuity of
multiplication on `G` is not used.

When `G` is a topological group acting on itself by left translation and `s` is nonempty, compact,
and open, `MulAction.stabilizer G s` is an open (hence closed) subgroup contained in `s / {a}` for
any `a ∈ s`, and is therefore compact.

## Main results

* `IsCompact.isOpen_setOf_mapsTo_smul`, and its additive form
  `IsCompact.isOpen_setOf_mapsTo_vadd`: the elements carrying a compact set into an open set under a
  continuous action form an open set.
* `TauCeti.MulAction.isOpen_stabilizer_of_isCompact_of_isOpen`, and its additive form
  `TauCeti.AddAction.isOpen_stabilizer_of_isCompact_of_isOpen`: the setwise stabilizer of a compact
  open set under a continuous action is open.
* `TauCeti.MulAction.isCompact_stabilizer_of_isCompact_of_isOpen`, and its additive form
  `TauCeti.AddAction.isCompact_stabilizer_of_isCompact_of_isOpen`: in a topological group, the left
  translation stabilizer of a nonempty compact open subset is compact.

## References

* L. Kramer, *Locally Compact Groups and Lie Groups*, Chapter 1 (version of 19 May 2020),
  Lemma 1.41, pp. 17–18.
-/

public section

open Set
open scoped Pointwise

namespace IsCompact

/-- **Elements carrying a compact set into an open set under a continuous action form an open set.**
For each `m` mapping `K` into `U`, the generalized tube lemma supplies an open neighbourhood of `m`
mapping `K` into `U`. -/
@[to_additive
/-- **Elements carrying a compact set into an open set under a continuous additive action form an
open set.** For each `m` mapping `K` into `U`, the generalized tube lemma supplies an open
neighbourhood of `m` mapping `K` into `U`. -/]
theorem isOpen_setOf_mapsTo_smul {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]
    [SMul M X] [ContinuousSMul M X] {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) :
    IsOpen {m : M | MapsTo (m • ·) K U} := by
  rw [isOpen_iff_forall_mem_open]
  intro m hm
  obtain ⟨V, _, hVo, _, hmV, hKV, hVU⟩ := generalized_tube_lemma isCompact_singleton hK
    (hU.preimage continuous_smul) (by rintro ⟨m', x⟩ ⟨rfl : m' = m, hx⟩; exact hm hx)
  exact ⟨V, fun m' hm' x hx ↦ hVU (mk_mem_prod hm' (hKV hx)), hVo, singleton_subset_iff.mp hmV⟩

end IsCompact

namespace TauCeti

/-- **The setwise stabilizer of a compact open set is open.** If `G` has continuous inversion and
acts continuously on `X`, then `MulAction.stabilizer G s` is open in `G` for every compact open
`s ⊆ X`. Continuity of multiplication on `G` is not required. -/
@[to_additive AddAction.isOpen_stabilizer_of_isCompact_of_isOpen
/-- **The setwise stabilizer of a compact open set is open.** If `G` has continuous negation and
acts continuously on `X`, then `AddAction.stabilizer G s` is open in `G` for every compact open
`s ⊆ X`. Continuity of addition on `G` is not required. -/]
theorem MulAction.isOpen_stabilizer_of_isCompact_of_isOpen {G X : Type*} [Group G]
    [TopologicalSpace G] [ContinuousInv G] [TopologicalSpace X] [MulAction G X]
    [ContinuousSMul G X] {s : Set X} (hs : IsCompact s) (hso : IsOpen s) :
    IsOpen (MulAction.stabilizer G s : Set G) := by
  have h : (MulAction.stabilizer G s : Set G) =
      {g : G | MapsTo (g • ·) s s} ∩ (·⁻¹) ⁻¹' {g : G | MapsTo (g • ·) s s} := by
    ext g
    exact mem_stabilizer_set_iff_mapsTo
  rw [h]
  exact (hs.isOpen_setOf_mapsTo_smul hso).inter
    ((hs.isOpen_setOf_mapsTo_smul hso).preimage continuous_inv)

/-- **The left translation stabilizer of a nonempty compact open subset is compact.** In a
topological group `G`, the stabilizer `MulAction.stabilizer G s` of a nonempty compact open
`s ⊆ G` is open, hence closed, and lies inside the compact translate `s / {a}` for any `a ∈ s`. -/
@[to_additive AddAction.isCompact_stabilizer_of_isCompact_of_isOpen
/-- **The translation stabilizer of a nonempty compact open subset is compact.** In a topological
additive group `G`, the stabilizer `AddAction.stabilizer G s` of a nonempty compact open `s ⊆ G` is
open, hence closed, and lies inside the compact translate `s - {a}` for any `a ∈ s`. -/]
theorem MulAction.isCompact_stabilizer_of_isCompact_of_isOpen {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {s : Set G} (hs₀ : s.Nonempty) (hs : IsCompact s)
    (hso : IsOpen s) : IsCompact (MulAction.stabilizer G s : Set G) := by
  obtain ⟨a, ha⟩ := hs₀
  have hclosed : IsClosed (MulAction.stabilizer G s : Set G) :=
    Subgroup.isClosed_of_isOpen _ (isOpen_stabilizer_of_isCompact_of_isOpen hs hso)
  have hdiv : IsCompact (s / {a}) := by
    simp_rw [div_singleton, div_eq_mul_inv]
    exact hs.image (continuous_mul_const a⁻¹)
  exact hdiv.of_isClosed_subset hclosed (_root_.MulAction.stabilizer_subset_div_right ha)

end TauCeti
