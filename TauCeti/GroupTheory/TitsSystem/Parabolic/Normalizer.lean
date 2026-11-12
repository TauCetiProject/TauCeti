/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.GroupTheory.TitsSystem.Parabolic.Classification

/-!
# Parabolic subgroups of a Tits system are self-normalizing

Every subgroup containing the distinguished subgroup `B` of a Tits system is its own
normalizer. In particular this holds for every standard parabolic, including `B` itself.
Consequently a parabolic has no additional symmetries under conjugation beyond those
coming from its own elements; its conjugates can be parametrized by its cosets.

The argument uses the classification of overgroups of `B` in
`TauCeti.GroupTheory.TitsSystem.Parabolic.Classification`. If a simple cell lies in the
normalizer of an overgroup `P`, the nondegeneracy axiom supplies an element of a conjugate
of `B` outside `B`. The rank-one Bruhat law puts that element in the simple cell, while
normalization puts it in `P`. Thus the entire simple cell already lies in `P`.

These are statements about abstract subgroups of a group with a BN-pair, without a
finiteness or sphericality assumption. They do not assert scheme-theoretic normalizer
equalities for parabolic subgroup schemes.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter IV, §2, no. 5.
* T. A. Springer, *Linear Algebraic Groups*, second edition (1998), §8.3.
-/

public section

open scoped Pointwise

namespace TauCeti.TitsSystem

universe u

variable {G : Type u} [Group G] (T : TitsSystem G)

private theorem bruhatCell_subset_of_subset_normalizer {P : Subgroup G}
    (hB : T.subgroupB ≤ P) {s : T.WeylGroup} (hs : s ∈ T.simple)
    (hN : T.bruhatCell s ⊆ Subgroup.normalizer (P : Set G)) :
    T.bruhatCell s ⊆ P := by
  obtain ⟨r, hr, b, hb⟩ := T.exists_conj_not_mem s hs
  have hrCell : (r : G) ∈ T.bruhatCell s := by
    rw [← hr, T.bruhatCell_mk]
    exact DoubleCoset.mem_doubleCoset_self _ _ _
  have hrbCell : (r : G) * b ∈ T.bruhatCell s := by
    rw [← T.bruhatCell_mul_subgroupB s]
    exact Set.mul_mem_mul hrCell b.property
  have hriCell : (r : G)⁻¹ ∈ T.bruhatCell s := by
    simpa only [T.inv_bruhatCell, T.inv_simple hs] using Set.inv_mem_inv.mpr hrCell
  have hxCell : (r : G) * b * (r : G)⁻¹ ∈ T.bruhatCell s := by
    have hx := Set.mul_mem_mul hrbCell hriCell
    rw [T.bruhatCell_mul_self_eq_union_of_mem_simple hs, T.bruhatCell_one] at hx
    exact hx.resolve_left hb
  have hxP : (r : G) * b * (r : G)⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp (hN hrCell) b).mp (hB b.property)
  exact T.bruhatCell_subset_of_mem hB hxCell hxP

/-- Every subgroup containing the distinguished `B` of a Tits system is self-normalizing. -/
theorem normalizer_eq_of_subgroupB_le {P : Subgroup G} (hB : T.subgroupB ≤ P) :
    Subgroup.normalizer (P : Set G) = P := by
  apply le_antisymm ?_ Subgroup.le_normalizer
  have hBN : T.subgroupB ≤ Subgroup.normalizer (P : Set G) :=
    hB.trans Subgroup.le_normalizer
  rw [← T.standardParabolic_eq_of_subgroupB_le hBN]
  exact (T.standardParabolic_le_iff _ P).mpr
    ⟨hB, fun s hs ↦ T.bruhatCell_subset_of_subset_normalizer hB s.property hs⟩

/-- Every standard parabolic of a Tits system is self-normalizing. -/
@[simp]
theorem normalizer_standardParabolic (J : Set T.simple) :
    Subgroup.normalizer (T.standardParabolic J : Set G) = T.standardParabolic J :=
  T.normalizer_eq_of_subgroupB_le (T.subgroupB_le_standardParabolic J)

/-- The distinguished subgroup `B` of a Tits system is self-normalizing. -/
@[simp]
theorem normalizer_subgroupB :
    Subgroup.normalizer (T.subgroupB : Set G) = T.subgroupB :=
  T.normalizer_eq_of_subgroupB_le le_rfl

end TauCeti.TitsSystem
