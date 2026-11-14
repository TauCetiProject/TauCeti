/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Compactness.Compact

/-!
# Open and compact set stabilizers for continuous group actions

For a group `G` acting continuously on a topological space `X`, the pointwise set stabilizer
`MulAction.stabilizer G s` of a compact open subset `s ⊆ X` is open in `G`. Indeed, for each
`g` stabilizing `s`, both `{g} ×ˢ s` and `{g⁻¹} ×ˢ s` map into the open set `s` under the action,
so the generalized tube lemma supplies open neighbourhoods `U₁` of `g` and `U₂` of `g⁻¹` sending `s`
into itself; then `U₁ ∩ U₂⁻¹` is an open neighbourhood of `g` inside `MulAction.stabilizer G s`.
Only continuity of inversion on `G` and joint continuity of the action on `X` are required;
continuity of multiplication on `G` is not used.

When `G` is a topological group acting on itself by left translation and `s` is nonempty, compact,
and open, `MulAction.stabilizer G s` is an open (hence closed) subgroup contained in `s / {a}` for
any `a ∈ s`, and is therefore compact. In particular, every compact open neighbourhood `s` of `1`
contains a compact open subgroup, namely its left translation stabilizer. This strengthens
Mathlib's `IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one`, which assumes
`[CompactSpace G]`, to arbitrary (possibly noncompact) topological groups.

## Main results

* `TauCeti.MulAction.isOpen_stabilizer_of_isCompact_of_isOpen`, and its additive form
  `TauCeti.AddAction.isOpen_stabilizer_of_isCompact_of_isOpen`: the stabilizer of a compact open
  set under a continuous action is open.
* `TauCeti.MulAction.isCompact_stabilizer_of_isCompact_of_isOpen`, and its additive form
  `TauCeti.AddAction.isCompact_stabilizer_of_isCompact_of_isOpen`: in a topological group, the left
  translation stabilizer of a nonempty compact open subset is compact.
* `TauCeti.IsTopologicalGroup.exists_openSubgroup_isCompact_subset_of_isCompact_of_isOpen`, and its
  additive form
  `TauCeti.IsTopologicalAddGroup.exists_openAddSubgroup_isCompact_subset_of_isCompact_of_isOpen`:
  every compact open identity neighbourhood in a topological group contains a compact open subgroup.

## References

* L. Kramer, *Locally Compact Groups and Lie Groups*, Chapter 1 (version of 19 May 2020),
  Lemma 1.41, pp. 17–18.
-/

public section

open Set
open scoped Pointwise

namespace TauCeti

/-- **The set stabilizer of a compact open set is open.** If `G` has continuous inversion and acts
continuously on `X`, then `MulAction.stabilizer G s` is open in `G` for every compact open
`s ⊆ X`. Continuity of multiplication on `G` is not required. -/
@[to_additive AddAction.isOpen_stabilizer_of_isCompact_of_isOpen
/-- **The set stabilizer of a compact open set is open.** If `G` has continuous negation and acts
continuously on `X`, then `AddAction.stabilizer G s` is open in `G` for every compact open
`s ⊆ X`. Continuity of addition on `G` is not required. -/]
theorem MulAction.isOpen_stabilizer_of_isCompact_of_isOpen {G X : Type*} [Group G]
    [TopologicalSpace G] [ContinuousInv G] [TopologicalSpace X] [MulAction G X]
    [ContinuousSMul G X] {s : Set X} (hs : IsCompact s) (hso : IsOpen s) :
    IsOpen (MulAction.stabilizer G s : Set G) := by
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  have hpre : IsOpen {p : G × X | p.1 • p.2 ∈ s} := hso.preimage continuous_smul
  have hsub₁ : ({g} : Set G) ×ˢ s ⊆ {p : G × X | p.1 • p.2 ∈ s} := by
    rintro ⟨g', x⟩ ⟨rfl : g' = g, hx⟩
    exact (_root_.MulAction.mem_stabilizer_set.mp hg x).mpr hx
  have hsub₂ : ({g⁻¹} : Set G) ×ˢ s ⊆ {p : G × X | p.1 • p.2 ∈ s} := by
    rintro ⟨g', x⟩ ⟨rfl : g' = g⁻¹, hx⟩
    exact (_root_.MulAction.mem_stabilizer_set.mp (inv_mem hg) x).mpr hx
  obtain ⟨U₁, _, hU₁o, _, hgU₁, hs₁, hU₁s⟩ :=
    generalized_tube_lemma isCompact_singleton hs hpre hsub₁
  obtain ⟨U₂, _, hU₂o, _, hginvU₂, hs₂, hU₂s⟩ :=
    generalized_tube_lemma isCompact_singleton hs hpre hsub₂
  refine ⟨U₁ ∩ U₂⁻¹, ?_, hU₁o.inter hU₂o.inv, singleton_subset_iff.mp hgU₁,
    Set.mem_inv.mpr (singleton_subset_iff.mp hginvU₂)⟩
  rintro h ⟨hh₁, hh₂⟩
  refine _root_.MulAction.mem_stabilizer_set.mpr fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · exact inv_smul_smul h x ▸ hU₂s (mk_mem_prod (Set.mem_inv.mp hh₂) (hs₂ hx))
  · exact hU₁s (mk_mem_prod hh₁ (hs₁ hx))

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

/-- **Every compact open identity neighbourhood contains a compact open subgroup.** Given a compact
open subset `s` of a topological group `G` with `1 ∈ s`, its left translation stabilizer
`MulAction.stabilizer G s` is a compact open subgroup contained in `s`. -/
@[to_additive
IsTopologicalAddGroup.exists_openAddSubgroup_isCompact_subset_of_isCompact_of_isOpen
/-- **Every compact open neighbourhood of zero contains a compact open additive subgroup.** Given a
compact open subset `s` of a topological additive group `G` with `0 ∈ s`, its translation
stabilizer `AddAction.stabilizer G s` is a compact open additive subgroup contained in `s`. -/]
theorem IsTopologicalGroup.exists_openSubgroup_isCompact_subset_of_isCompact_of_isOpen
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {s : Set G}
    (hs : IsCompact s) (hso : IsOpen s) (h1 : (1 : G) ∈ s) :
    ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ s :=
  ⟨⟨_root_.MulAction.stabilizer G s, MulAction.isOpen_stabilizer_of_isCompact_of_isOpen hs hso⟩,
    MulAction.isCompact_stabilizer_of_isCompact_of_isOpen ⟨1, h1⟩ hs hso,
    fun g hg ↦ by simpa only [smul_eq_mul, mul_one] using
      (_root_.MulAction.mem_stabilizer_set.mp hg 1).mpr h1⟩

end TauCeti
