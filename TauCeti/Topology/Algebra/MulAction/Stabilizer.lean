/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Open setwise stabilizers of compact open subsets

For a continuous action of a topological group `G` on a topological space `α`, the setwise
stabilizer `{g : G | g • C = C}` (`MulAction.stabilizer G C`) of any compact open subset `C ⊆ α`
is an open subgroup of `G` (`IsCompact.isOpen_mulAction_stabilizer`, bundled as
`IsCompact.stabilizerOpenSubgroup`), with no separation assumptions on `G` or `α`.

For the left translation action of `G` on itself, when `1 ∈ C` the stabilizer is contained in `C`
(`IsCompact.stabilizerOpenSubgroup_subset`) and compact
(`IsCompact.isCompact_stabilizerOpenSubgroup`). Every result carries `@[to_additive]` for
continuous additive actions and `OpenAddSubgroup`.

## Main definitions

* `IsCompact.stabilizerOpenSubgroup`: the setwise stabilizer in `G` of a compact open subset `C`
  of a `G`-space, bundled as an `OpenSubgroup G` (with additive counterpart
  `IsCompact.stabilizerOpenAddSubgroup`).

## Main results

* `IsCompact.isOpen_mulAction_stabilizer`: the setwise stabilizer of a compact open subset under a
  continuous group action is open.
* `IsCompact.stabilizerOpenSubgroup_subset` and `IsCompact.isCompact_stabilizerOpenSubgroup`: when
  `1 ∈ C`, the left translation stabilizer lies in `C` and is compact.

## References

* L. Kramer, *Locally Compact Groups and Lie Groups*, Chapter 1 (version of 19 May 2020),
  Lemma 1.41, p. 17, <https://www.uni-muenster.de/AGKramer/content/ch1.pdf>.
-/

public section

open Filter Set Topology
open scoped Pointwise

section Action

variable {G α : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace α] [MulAction G α] [ContinuousSMul G α]

/-- A generalization of Kramer's translation-stabilizer lemma: for a continuous action of a
topological group `G` on a topological space `α`, the setwise stabilizer `{g : G | g • C = C}` of
any compact open subset `C ⊆ α` is open in `G`. Neither Hausdorffness of `G` nor Hausdorffness of
`α` is required. -/
@[to_additive
/-- For a continuous additive action of a topological additive group `G` on a topological space `α`,
the setwise stabilizer `{g : G | g +ᵥ C = C}` of any compact open subset `C ⊆ α` is open in `G`.
Neither Hausdorffness of `G` nor Hausdorffness of `α` is required. -/]
theorem IsCompact.isOpen_mulAction_stabilizer {C : Set α} (hC : IsCompact C) (hC_open : IsOpen C) :
    IsOpen (MulAction.stabilizer G C : Set G) := by
  obtain ⟨V, W, hV_open, _, h1V, hCW, hVW⟩ := generalized_tube_lemma
    (isCompact_singleton (x := (1 : G))) hC (hC_open.preimage continuous_smul)
    (fun p hp ↦ by
      rw [Set.mem_preimage, mem_singleton_iff.mp hp.1, one_smul]
      exact hp.2)
  have h1 : (1 : G) ∈ V := h1V (mem_singleton 1)
  have hU_mem : V ∩ V⁻¹ ∈ 𝓝 (1 : G) :=
    (hV_open.inter hV_open.inv).mem_nhds ⟨h1, by simpa using h1⟩
  refine Subgroup.isOpen_of_mem_nhds _ (mem_of_superset hU_mem ?_)
  rintro g ⟨hgV, hgVinv⟩
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_set]
  refine fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ Set.mem_preimage.mp (hVW (mk_mem_prod hgV (hCW hx)))⟩
  simpa using Set.mem_preimage.mp (hVW (mk_mem_prod (Set.mem_inv.mp hgVinv) (hCW hx)))

variable (G) in
/-- The setwise stabilizer `{g : G | g • C = C}` of a compact open subset `C` under a continuous
action of a topological group `G`, bundled as an `OpenSubgroup G`. -/
@[to_additive
/-- The setwise stabilizer `{g : G | g +ᵥ C = C}` of a compact open subset `C` under a continuous
additive action of a topological additive group `G`, bundled as an `OpenAddSubgroup G`. -/]
def IsCompact.stabilizerOpenSubgroup {C : Set α} (hC : IsCompact C) (hC_open : IsOpen C) :
    OpenSubgroup G :=
  ⟨MulAction.stabilizer G C, hC.isOpen_mulAction_stabilizer hC_open⟩

/-- The underlying set of `hC.stabilizerOpenSubgroup G hC_open` is the setwise stabilizer of
`C`. -/
@[to_additive (attr := simp)
/-- The underlying set of `hC.stabilizerOpenAddSubgroup G hC_open` is the setwise additive
stabilizer of `C`. -/]
theorem IsCompact.coe_stabilizerOpenSubgroup {C : Set α} (hC : IsCompact C) (hC_open : IsOpen C) :
    ((hC.stabilizerOpenSubgroup G hC_open : OpenSubgroup G) : Set G) =
      (MulAction.stabilizer G C : Set G) :=
  (rfl)

/-- The underlying subgroup of `hC.stabilizerOpenSubgroup G hC_open` is
`MulAction.stabilizer G C`. -/
@[to_additive (attr := simp)
/-- The underlying additive subgroup of `hC.stabilizerOpenAddSubgroup G hC_open` is
`AddAction.stabilizer G C`. -/]
theorem IsCompact.toSubgroup_stabilizerOpenSubgroup {C : Set α} (hC : IsCompact C)
    (hC_open : IsOpen C) :
    (hC.stabilizerOpenSubgroup G hC_open).toSubgroup = MulAction.stabilizer G C :=
  (rfl)

/-- An element belongs to `hC.stabilizerOpenSubgroup G hC_open` precisely when its action preserves
`C`. -/
@[to_additive (attr := simp, grind =)
/-- An element belongs to `hC.stabilizerOpenAddSubgroup G hC_open` precisely when its additive
action preserves `C`. -/]
theorem IsCompact.mem_stabilizerOpenSubgroup {C : Set α} (hC : IsCompact C) (hC_open : IsOpen C)
    {g : G} : g ∈ hC.stabilizerOpenSubgroup G hC_open ↔ g • C = C :=
  MulAction.mem_stabilizer_iff

end Action

section LeftTranslation

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- When `1 ∈ C`, the open left translation stabilizer `hC.stabilizerOpenSubgroup G hC_open` is
contained in `C`. -/
@[to_additive
/-- When `0 ∈ C`, the open translation stabilizer `hC.stabilizerOpenAddSubgroup G hC_open` is
contained in `C`. -/]
theorem IsCompact.stabilizerOpenSubgroup_subset {C : Set G} (hC : IsCompact C) (hC_open : IsOpen C)
    (h1 : (1 : G) ∈ C) : (hC.stabilizerOpenSubgroup G hC_open : Set G) ⊆ C := by
  simpa using MulAction.stabilizer_subset_div_right h1

/-- When `1 ∈ C`, the open left translation stabilizer `hC.stabilizerOpenSubgroup G hC_open` is
compact. -/
@[to_additive
/-- When `0 ∈ C`, the open translation stabilizer `hC.stabilizerOpenAddSubgroup G hC_open` is
compact. -/]
theorem IsCompact.isCompact_stabilizerOpenSubgroup {C : Set G} (hC : IsCompact C)
    (hC_open : IsOpen C) (h1 : (1 : G) ∈ C) :
    IsCompact (hC.stabilizerOpenSubgroup G hC_open : Set G) :=
  hC.of_isClosed_subset (hC.stabilizerOpenSubgroup G hC_open).isClosed
    (hC.stabilizerOpenSubgroup_subset hC_open h1)

end LeftTranslation
