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
# Openness and compactness of set stabilizers

Let a topological group `G` act continuously on a topological space `X`. If a subset `C ⊆ X` is
both compact and open, Wallace's tube lemma produces an open neighbourhood `V` of `1 : G` carrying
`C` into itself. Intersecting `V` with `V⁻¹` gives a symmetric open identity neighbourhood on
which every group element maps `C` onto itself, so `MulAction.stabilizer G C` contains a
neighbourhood of `1` and is therefore an open subgroup of `G`.

Specializing to the left-translation action of a topological group `G` on itself, the stabilizer
of a compact open subset `C ⊆ G` containing `1` is an open subgroup contained in `C`; since every
open subgroup is closed, it is also compact. This is the stabilizer construction of Kramer's proof
of van Dantzig's theorem, written for left translations in place of right translations.

## Main definitions and results

* `MulAction.isOpen_stabilizer_of_isCompact`, with additive form
  `AddAction.isOpen_stabilizer_of_isCompact`: the pointwise stabilizer of a compact open subset
  under a continuous group action is open.
* `OpenSubgroup.stabilizer`, with additive form `OpenAddSubgroup.stabilizer`: that stabilizer
  bundled as an `OpenSubgroup`, together with its coercion and membership simp lemmas.
* `MulAction.stabilizer_subset_of_one_mem` and `MulAction.isCompact_stabilizer`, with additive
  forms `AddAction.stabilizer_subset_of_zero_mem` and `AddAction.isCompact_stabilizer`: for a
  subset `C ⊆ G` containing `1`, the left-translation stabilizer lies in `C`, and is compact
  whenever `C` is compact and open.

## References

* L. Kramer, *Locally Compact Groups and Lie Groups*, Chapter 1 (2020), Lemma 1.41, pp. 17–18.
-/

public section

open Set
open scoped Pointwise Topology

namespace MulAction

/-- **The pointwise stabilizer of a compact open set is open.** For a continuous action of `G` on
`X`, Wallace's tube lemma gives an open neighbourhood of `1` mapping `C` into itself, and its
symmetric core lies in `MulAction.stabilizer G C`. -/
@[to_additive /-- **The pointwise stabilizer of a compact open set is open.** For a continuous
additive action of `G` on `X`, Wallace's tube lemma gives an open neighbourhood of `0` mapping `C`
into itself, and its symmetric core lies in `AddAction.stabilizer G C`. -/]
theorem isOpen_stabilizer_of_isCompact {G X : Type*} [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] [ContinuousInv G] [TopologicalSpace X] [MulAction G X]
    [ContinuousSMul G X] {C : Set X} (hC : IsCompact C) (hC_open : IsOpen C) :
    IsOpen (stabilizer G C : Set G) := by
  -- Apply the tube lemma to `{1} ×ˢ C` inside the open preimage of `C` under the action map.
  obtain ⟨V, W, hV_open, -, h1V, hCW, hVW⟩ :=
    generalized_tube_lemma (isCompact_singleton : IsCompact ({(1 : G)} : Set G)) hC
      (hC_open.preimage continuous_smul) fun p hp ↦ by
        rw [mem_preimage, mem_singleton_iff.mp hp.1, one_smul]
        exact hp.2
  have hmaps : ∀ g ∈ V, MapsTo (g • ·) C C := fun g hg x hx ↦ hVW (mk_mem_prod hg (hCW hx))
  -- Elements of the symmetric open neighbourhood `V ∩ V⁻¹` map `C` into itself in both directions.
  have h1 : (1 : G) ∈ V := h1V (mem_singleton 1)
  have hnhds : V ∩ V⁻¹ ∈ 𝓝 (1 : G) :=
    (hV_open.inter hV_open.inv).mem_nhds ⟨h1, by simpa using h1⟩
  refine Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset hnhds fun g hg ↦ ?_)
  exact mem_stabilizer_set.mpr fun x ↦
    ⟨fun hx ↦ by simpa using hmaps g⁻¹ (mem_inv.mp hg.2) hx, fun hx ↦ hmaps g hg.1 hx⟩

/-- If `1 ∈ C`, every element stabilizing `C` under left translation belongs to `C`. -/
@[to_additive /-- If `0 ∈ C`, every element stabilizing `C` under left translation belongs to
`C`. -/]
theorem stabilizer_subset_of_one_mem {G : Type*} [Group G] {C : Set G} (h1 : (1 : G) ∈ C) :
    (stabilizer G C : Set G) ⊆ C := by
  simpa using stabilizer_subset_div_right h1

/-- **Left-translation stabilizer of a compact open identity neighbourhood.** If `C ⊆ G` is
compact, open, and contains `1`, then `MulAction.stabilizer G C` is compact: it is an open (hence
closed) subgroup contained in `C`. -/
@[to_additive /-- **Translation stabilizer of a compact open neighbourhood of zero.** If `C ⊆ G`
is compact, open, and contains `0`, then `AddAction.stabilizer G C` is compact: it is an open
(hence closed) additive subgroup contained in `C`. -/]
theorem isCompact_stabilizer {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {C : Set G} (hC : IsCompact C) (hC_open : IsOpen C) (h1 : (1 : G) ∈ C) :
    IsCompact (stabilizer G C : Set G) :=
  hC.of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ (isOpen_stabilizer_of_isCompact hC hC_open))
    (stabilizer_subset_of_one_mem h1)

end MulAction

namespace OpenSubgroup

section Action

variable (G : Type*) {X : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  [ContinuousInv G] [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X] {C : Set X}

/-- The pointwise stabilizer of a compact open set under a continuous group action, bundled as an
`OpenSubgroup`. -/
@[to_additive /-- The pointwise stabilizer of a compact open set under a continuous additive group
action, bundled as an `OpenAddSubgroup`. -/]
def stabilizer (hC : IsCompact C) (hC_open : IsOpen C) : OpenSubgroup G where
  toSubgroup := MulAction.stabilizer G C
  isOpen' := MulAction.isOpen_stabilizer_of_isCompact hC hC_open

variable {G}

/-- The underlying subgroup of `OpenSubgroup.stabilizer` is `MulAction.stabilizer`. -/
@[to_additive (attr := simp, norm_cast) /-- The underlying additive subgroup of
`OpenAddSubgroup.stabilizer` is `AddAction.stabilizer`. -/]
theorem toSubgroup_stabilizer (hC : IsCompact C) (hC_open : IsOpen C) :
    (stabilizer G hC hC_open : Subgroup G) = MulAction.stabilizer G C :=
  (rfl)

/-- The underlying set of `OpenSubgroup.stabilizer` is that of `MulAction.stabilizer`. -/
@[to_additive (attr := simp) /-- The underlying set of `OpenAddSubgroup.stabilizer` is that of
`AddAction.stabilizer`. -/]
theorem coe_stabilizer (hC : IsCompact C) (hC_open : IsOpen C) :
    (stabilizer G hC hC_open : Set G) = (MulAction.stabilizer G C : Set G) :=
  (rfl)

/-- An element belongs to `OpenSubgroup.stabilizer` if and only if it fixes `C` setwise. -/
@[to_additive (attr := simp) /-- An element belongs to `OpenAddSubgroup.stabilizer` if and only if
it fixes `C` setwise. -/]
theorem mem_stabilizer_iff (hC : IsCompact C) (hC_open : IsOpen C) {g : G} :
    g ∈ stabilizer G hC hC_open ↔ g • C = C :=
  Iff.rfl

end Action

section LeftTranslation

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {C : Set G}

/-- For a compact open set `C ⊆ G` containing `1`, its bundled left-translation stabilizer is
contained in `C`. -/
@[to_additive /-- For a compact open set `C ⊆ G` containing `0`, its bundled translation
stabilizer is contained in `C`. -/]
theorem stabilizer_subset (hC : IsCompact C) (hC_open : IsOpen C) (h1 : (1 : G) ∈ C) :
    (stabilizer G hC hC_open : Set G) ⊆ C :=
  MulAction.stabilizer_subset_of_one_mem h1

/-- For a compact open set `C ⊆ G` containing `1`, its bundled left-translation stabilizer is
compact. -/
@[to_additive /-- For a compact open set `C ⊆ G` containing `0`, its bundled translation
stabilizer is compact. -/]
theorem isCompact_stabilizer (hC : IsCompact C) (hC_open : IsOpen C) (h1 : (1 : G) ∈ C) :
    IsCompact (stabilizer G hC hC_open : Set G) :=
  MulAction.isCompact_stabilizer hC hC_open h1

/-- The bundled left-translation stabilizer of a compact open subgroup is the subgroup itself. -/
@[to_additive (attr := simp) /-- The bundled translation stabilizer of a compact open additive
subgroup is the subgroup itself. -/]
theorem stabilizer_coe (H : OpenSubgroup G) (hH : IsCompact (H : Set G)) :
    stabilizer G hH H.isOpen = H :=
  toSubgroup_injective (MulAction.stabilizer_subgroup H.toSubgroup)

end LeftTranslation

end OpenSubgroup

end
