/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Instances.Real.Lemmas
import TauCeti.Analysis.Normed.Group.Ultra
import TauCeti.NumberTheory.Padics.Basic
import TauCeti.Topology.Algebra.Group.Perm
import TauCeti.Topology.Algebra.Nonarchimedean.LocallyProfinite

/-!
# Examples and boundary checks for Van Dantzig's theorem

Concrete checks illustrating the translation-stabilizer construction and the hypotheses of Van
Dantzig's theorem:

1. **Noncompact `2`-adic additive group `ℚ_[2]`:** `ℚ_[2]` is locally compact, Hausdorff, totally
   disconnected, and noncompact. The subsets `ℤ_[2]` and `2 • ℤ_[2]` inside `ℚ_[2]` coincide with
   the ultrametric closed balls of radii `1` and `2⁻¹`, have additive translation stabilizers equal
   to those compact open additive subgroups, and the family `(2 : ℚ_[2]) ^ m • ℤ_[2]` (`m : ℤ`)
   forms a neighbourhood basis of `0` in `ℚ_[2]`.
2. **Discrete symmetric group `Equiv.Perm (Fin 3)`:** the compact clopen identity neighbourhood
   `C = {1, swap 0 1, swap 0 2}` is not closed under multiplication (`swap 0 1 * swap 0 2 ∉ C`),
   while its left translation stabilizer `MulAction.stabilizer (Equiv.Perm (Fin 3)) C` is `{1}`.
3. **Trivial group `Unit` and real line `ℝ`:** `OpenSubgroup Unit` has `⊤` as its unique compact
   open basis element, whereas in the locally compact connected group `ℝ` the open interval
   `Set.Ioo (-1 : ℝ) 1` contains no open additive subgroup.
-/

open Filter Metric Set Topology
open scoped Pointwise

namespace TauCeti

/-- The `2`-adic field `ℚ_[2]` is noncompact, locally compact, Hausdorff, totally disconnected, and
a nonarchimedean additive group. -/
example :
    ¬ CompactSpace ℚ_[2] ∧ LocallyCompactSpace ℚ_[2] ∧ T2Space ℚ_[2] ∧
      TotallyDisconnectedSpace ℚ_[2] ∧ NonarchimedeanAddGroup ℚ_[2] :=
  ⟨not_compactSpace_iff.mpr inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance⟩

/-- In `ℚ_[2]`, `C = ℤ_[2]` has additive translation stabilizer equal to `ℤ_[2]` itself. -/
example :
    (AddAction.stabilizer ℚ_[2] (Set.range (PadicInt.Coe.ringHom (p := 2))) : Set ℚ_[2]) =
      Set.range (PadicInt.Coe.ringHom (p := 2)) := by
  have h : Set.range (PadicInt.Coe.ringHom (p := 2)) =
      (IsUltrametricDist.closedBall_openAddSubgroup ℚ_[2] one_pos : Set ℚ_[2]) := by
    rw [IsUltrametricDist.coe_closedBall_openAddSubgroup]
    exact Subset.antisymm
      (range_subset_iff.mpr fun a ↦
        mem_closedBall_zero_iff.mpr (PadicInt.norm_coe_ringHom_le_one a))
      PadicInt.closedBall_subset_range_coe_ringHom
  rw [h, ← OpenAddSubgroup.coe_toAddSubgroup, AddAction.stabilizer_addSubgroup]

/-- In `ℚ_[2]`, `C = 2 • ℤ_[2]` has additive translation stabilizer equal to `2 • ℤ_[2]`. -/
example :
    (AddAction.stabilizer ℚ_[2]
      ((2 : ℚ_[2]) • Set.range (PadicInt.Coe.ringHom (p := 2))) : Set ℚ_[2]) =
      (2 : ℚ_[2]) • Set.range (PadicInt.Coe.ringHom (p := 2)) := by
  have h : (2 : ℚ_[2]) • Set.range (PadicInt.Coe.ringHom (p := 2)) =
      (IsUltrametricDist.closedBall_openAddSubgroup ℚ_[2]
        (inv_pos.mpr two_pos) : Set ℚ_[2]) := by
    rw [Subset.antisymm
      (range_subset_iff.mpr fun a ↦
        mem_closedBall_zero_iff.mpr (PadicInt.norm_coe_ringHom_le_one a))
      PadicInt.closedBall_subset_range_coe_ringHom,
      smul_unitClosedBall, IsUltrametricDist.coe_closedBall_openAddSubgroup]
    congr 1
    simpa using Padic.norm_p (p := 2)
  rw [h, ← OpenAddSubgroup.coe_toAddSubgroup, AddAction.stabilizer_addSubgroup]

/-- The compact open subgroups `2 ^ m • ℤ_[2]` (`m : ℤ`) form a neighbourhood basis of `0` in
`ℚ_[2]`. -/
example :
    (𝓝 (0 : ℚ_[2])).HasBasis (fun _ : ℤ ↦ True)
      fun m : ℤ ↦ (2 : ℚ_[2]) ^ m • Set.range (PadicInt.Coe.ringHom (p := 2)) := by
  have hzpow (m : ℤ) :
      (2 : ℚ_[2]) ^ m • Set.range (PadicInt.Coe.ringHom (p := 2)) =
        (IsUltrametricDist.closedBall_openAddSubgroup ℚ_[2]
          (zpow_pos two_pos (-m)) : Set ℚ_[2]) := by
    rw [Subset.antisymm
      (range_subset_iff.mpr fun a ↦
        mem_closedBall_zero_iff.mpr (PadicInt.norm_coe_ringHom_le_one a))
      PadicInt.closedBall_subset_range_coe_ringHom,
      smul_unitClosedBall, IsUltrametricDist.coe_closedBall_openAddSubgroup]
    congr 1
    simpa using Padic.norm_p_zpow (p := 2) m
  refine ⟨fun U ↦ ⟨fun hU ↦ ?_, fun ⟨m, _, hm⟩ ↦ ?_⟩⟩
  · obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hU
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (2⁻¹ : ℝ) ^ n < ε :=
      exists_pow_lt_of_lt_one hε (by norm_num)
    refine ⟨n, trivial, ?_⟩
    rw [hzpow, IsUltrametricDist.coe_closedBall_openAddSubgroup]
    refine Subset.trans (Metric.closedBall_subset_closedBall ?_) hball
    simpa [zpow_neg, zpow_natCast, inv_pow] using hn.le
  · rw [hzpow] at hm
    exact mem_of_superset
      (IsUltrametricDist.closedBall_openAddSubgroup ℚ_[2] (zpow_pos two_pos (-m))).mem_nhds_zero hm

/-- In discrete `S₃ = Equiv.Perm (Fin 3)`, `C = {1, (0 1), (0 2)}` is compact and clopen, is not a
subgroup because `(0 1) * (0 2)` lies outside `C`, and has trivial left translation stabilizer. -/
example :
    let C : Set (Equiv.Perm (Fin 3)) := {1, Equiv.swap 0 1, Equiv.swap 0 2}
    IsCompact C ∧
      IsClopen C ∧
      Equiv.swap (0 : Fin 3) 1 * Equiv.swap 0 2 ∉ C ∧
      MulAction.stabilizer (Equiv.Perm (Fin 3)) C = ⊥ := by
  intro C
  have hnotmem : Equiv.swap (0 : Fin 3) 1 * Equiv.swap 0 2 ∉ C := by
    simp only [C, mem_insert_iff, mem_singleton_iff]
    decide
  refine ⟨C.toFinite.isCompact, isClopen_discrete _, hnotmem, ?_⟩
  refine (Subgroup.eq_bot_iff_forall _).mpr fun σ hσ ↦ ?_
  have h1 : σ ∈ C := by
    simpa using (MulAction.mem_stabilizer_set.mp hσ 1).mpr (by simp [C])
  rcases (by simpa only [C, mem_insert_iff, mem_singleton_iff] using h1 :
      σ = 1 ∨ σ = Equiv.swap 0 1 ∨ σ = Equiv.swap 0 2) with rfl | rfl | rfl
  · rfl
  · exact absurd ((MulAction.mem_stabilizer_set.mp hσ (Equiv.swap 0 2)).mpr (by simp [C])) hnotmem
  · exact absurd ((MulAction.mem_stabilizer_set.mp hσ (Equiv.swap 0 1)).mpr (by simp [C]))
      (by simp only [C, mem_insert_iff, mem_singleton_iff]; decide)

/-- The trivial group `Unit` has a unique open subgroup `⊤`, which is compact and forms the
singleton compact open neighbourhood basis at `1`. -/
example :
    (∀ H : OpenSubgroup Unit, H = ⊤) ∧
      (𝓝 (1 : Unit)).HasBasis (fun H : OpenSubgroup Unit ↦ H = ⊤ ∧ IsCompact (H : Set Unit))
        fun H ↦ (H : Set Unit) := by
  refine ⟨fun H ↦ by ext ⟨⟩; exact ⟨fun _ ↦ trivial, fun _ ↦ H.one_mem⟩, ?_⟩
  refine ⟨fun U ↦ ⟨fun hU ↦ ⟨⊤, ⟨rfl, isCompact_univ⟩, ?_⟩, fun ⟨H, _, hHU⟩ ↦
    mem_of_superset H.mem_nhds_one hHU⟩⟩
  rintro ⟨⟩ _
  exact mem_of_mem_nhds hU

/-- `ℝ` is locally compact, yet the neighbourhood `(-1, 1)` of `0` contains no open additive
subgroup: local compactness without total disconnectedness does not yield open subgroups inside
small neighbourhoods. -/
example :
    LocallyCompactSpace ℝ ∧ ¬ ∃ H : OpenAddSubgroup ℝ, (H : Set ℝ) ⊆ Set.Ioo (-1 : ℝ) 1 := by
  refine ⟨inferInstance, ?_⟩
  rintro ⟨H, hH⟩
  have huniv : (H : Set ℝ) = univ := H.isClopen.eq_univ ⟨0, H.zero_mem⟩
  have h1 : (1 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := hH (huniv ▸ mem_univ 1)
  exact lt_irrefl (1 : ℝ) h1.2

end TauCeti
