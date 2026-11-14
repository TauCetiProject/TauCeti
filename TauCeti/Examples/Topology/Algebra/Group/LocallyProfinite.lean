/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import TauCeti.Topology.Algebra.Group.LocallyProfinite
import TauCeti.Topology.Algebra.Group.Perm

/-!
# Examples of locally profinite groups and set stabilizers

These concrete examples exercise `OpenSubgroup.stabilizer`, `OpenAddSubgroup.stabilizer`, and van
Dantzig's theorem across four contrasting topological groups:

* In the noncompact locally profinite additive group `ℚ_[2]`, the subsets `ℤ_[2]` and `2 • ℤ_[2]`
  are compact open additive subgroups equal to their own translation stabilizers, and the scaled
  lattices `(2 : ℚ_[2]) ^ m • ℤ_[2]` (`m : ℤ`) form a compact open additive subgroup basis of
  `𝓝 (0 : ℚ_[2])`.
* In the discrete symmetric group `Equiv.Perm (Fin 3)` (`S₃`), the subset
  `C = {1, swap 0 1, swap 0 2}` is compact and clopen and contains `1`, yet is not a subgroup
  because `swap 0 1 * swap 0 2` is a `3`-cycle outside `C`; its left-translation stabilizer is the
  trivial subgroup `⊥` (`{1}`).
* The trivial group `Unit` has `{⊤}` as its singleton family of compact open subgroups, forming a
  basis of `𝓝 (1 : Unit)`.
* On the locally compact Hausdorff additive group `ℝ`, the neighbourhood `Ioo (-1 : ℝ) 1` of `0`
  contains no open additive subgroup, witnessing that local compactness without total
  disconnectedness does not yield van Dantzig's conclusion.
-/

open Set Filter Topology
open scoped Pointwise

namespace TauCeti

/-- `ℚ_[2]` is a locally profinite (locally compact, totally disconnected, nonarchimedean) additive
group that is not compact. -/
example : LocallyCompactSpace ℚ_[2] ∧ TotallyDisconnectedSpace ℚ_[2] ∧
    NonarchimedeanAddGroup ℚ_[2] ∧ ¬ CompactSpace ℚ_[2] :=
  ⟨inferInstance, inferInstance, inferInstance, not_compactSpace_iff.mpr inferInstance⟩

/-- In `ℚ_[2]`, `C = ℤ_[2]` and `C = 2 • ℤ_[2]` are compact open subsets whose additive translation
stabilizers are `ℤ_[2]` and `2 • ℤ_[2]` respectively, and the scaled compact open additive
subgroups `(2 : ℚ_[2]) ^ m • ℤ_[2]` (`m : ℤ`) form a filter basis of `𝓝 (0 : ℚ_[2])`. -/
example :
    ∃ (hC : IsCompact (PadicInt.subring 2 : Set ℚ_[2]))
      (hO : IsOpen (PadicInt.subring 2 : Set ℚ_[2])),
      (OpenAddSubgroup.stabilizer ℚ_[2] hC hO : Set ℚ_[2]) = (PadicInt.subring 2 : Set ℚ_[2]) ∧
      (AddAction.stabilizer ℚ_[2] ((2 : ℚ_[2]) • (PadicInt.subring 2 : Set ℚ_[2])) : Set ℚ_[2]) =
        (2 : ℚ_[2]) • (PadicInt.subring 2 : Set ℚ_[2]) ∧
      (𝓝 (0 : ℚ_[2])).HasBasis (fun _ : ℤ ↦ True)
        fun m : ℤ ↦ (2 : ℚ_[2]) ^ m • (PadicInt.subring 2 : Set ℚ_[2]) := by
  have hnorm (k : ℤ) : ‖(2 : ℚ_[2]) ^ k‖ = (2 : ℝ) ^ (-k) := by
    simpa using Padic.norm_p_zpow (p := 2) k
  have hball (m : ℤ) : (2 : ℚ_[2]) ^ m • (PadicInt.subring 2 : Set ℚ_[2]) =
      Metric.closedBall (0 : ℚ_[2]) ((2 : ℝ) ^ (-m)) := by
    ext x
    simp only [mem_smul_set, SetLike.mem_coe, PadicInt.mem_subring_iff, smul_eq_mul,
      Metric.mem_closedBall, dist_zero_right]
    refine ⟨?_, fun hx ↦ ⟨(2 : ℚ_[2]) ^ (-m) * x, ?_, ?_⟩⟩
    · rintro ⟨y, hy, rfl⟩
      rw [norm_mul, hnorm]
      exact mul_le_of_le_one_right (zpow_nonneg zero_le_two (-m)) hy
    · rw [norm_mul, hnorm, neg_neg]
      exact (mul_le_mul_of_nonneg_left hx (zpow_nonneg zero_le_two m)).trans_eq
        (by rw [← zpow_add₀ two_ne_zero, add_neg_cancel, zpow_zero])
    · rw [← mul_assoc, ← zpow_add₀ (two_ne_zero : (2 : ℚ_[2]) ≠ 0), add_neg_cancel, zpow_zero,
        one_mul]
  have hZ2 : (PadicInt.subring 2 : Set ℚ_[2]) = Metric.closedBall (0 : ℚ_[2]) 1 := by
    simpa using hball 0
  let twoZ2 : AddSubgroup ℚ_[2] :=
    (PadicInt.subring 2).toAddSubgroup.map (AddMonoidHom.mulLeft (2 : ℚ_[2]))
  have htwoZ2 : (twoZ2 : Set ℚ_[2]) = (2 : ℚ_[2]) • (PadicInt.subring 2 : Set ℚ_[2]) := by
    ext x; simp [twoZ2, mem_smul_set, smul_eq_mul]
  refine ⟨hZ2 ▸ isCompact_closedBall (0 : ℚ_[2]) 1,
    hZ2 ▸ (IsUltrametricDist.isClopen_closedBall (0 : ℚ_[2]) one_ne_zero).isOpen, ?_, ?_, ?_⟩
  · simpa using congrArg ((↑) : AddSubgroup ℚ_[2] → Set ℚ_[2])
      (AddAction.stabilizer_addSubgroup (PadicInt.subring 2).toAddSubgroup)
  · simpa [htwoZ2] using congrArg ((↑) : AddSubgroup ℚ_[2] → Set ℚ_[2])
      (AddAction.stabilizer_addSubgroup twoZ2)
  · simp_rw [hball]
    refine Metric.nhds_basis_closedBall.to_hasBasis'
      (fun ε hε ↦ ?_) (fun m _ ↦ Metric.closedBall_mem_nhds 0 (zpow_pos two_pos (-m)))
    obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt 2 hε
    exact ⟨(k : ℤ), trivial, Metric.closedBall_subset_closedBall hk.le⟩

/-- In discrete `S₃`, `C = {1, (0 1), (0 2)}` is compact and clopen, contains `1`, and is not a
subgroup because `(0 1)(0 2)` lies outside `C`; its left-translation stabilizer is `{1}` (`⊥`). -/
example :
    let C : Set (Equiv.Perm (Fin 3)) := {1, Equiv.swap 0 1, Equiv.swap 0 2}
    IsCompact C ∧ IsClopen C ∧
      Equiv.swap (0 : Fin 3) 1 * Equiv.swap 0 2 ∉ C ∧
      (¬ ∃ H : Subgroup (Equiv.Perm (Fin 3)), (H : Set (Equiv.Perm (Fin 3))) = C) ∧
      (OpenSubgroup.stabilizer (Equiv.Perm (Fin 3))
        C.toFinite.isCompact (isOpen_discrete C) :
          Subgroup (Equiv.Perm (Fin 3))) = ⊥ := by
  intro C
  have hnot : Equiv.swap (0 : Fin 3) 1 * Equiv.swap 0 2 ∉ C := by
    simp only [C, mem_insert_iff, mem_singleton_iff]
    decide
  refine ⟨C.toFinite.isCompact, isClopen_discrete C, hnot, ?_, ?_⟩
  · rintro ⟨H, hH⟩
    have h01 : Equiv.swap (0 : Fin 3) 1 ∈ H := by simp [← SetLike.mem_coe, hH, C]
    have h02 : Equiv.swap (0 : Fin 3) 2 ∈ H := by simp [← SetLike.mem_coe, hH, C]
    exact hnot (hH ▸ H.mul_mem h01 h02)
  · rw [OpenSubgroup.toSubgroup_stabilizer, eq_bot_iff]
    intro g hg
    have hgC : g ∈ C := MulAction.stabilizer_subset_of_one_mem (by simp [C]) hg
    have hg_mem := MulAction.mem_stabilizer_set.mp hg
    rcases hgC with rfl | rfl | rfl
    · rfl
    · exact False.elim (hnot ((hg_mem (Equiv.swap 0 2)).mpr (by simp [C])))
    · have hnot' : Equiv.swap (0 : Fin 3) 2 * Equiv.swap 0 1 ∉ C := by
        simp only [C, mem_insert_iff, mem_singleton_iff]
        decide
      exact False.elim (hnot' ((hg_mem (Equiv.swap 0 1)).mpr (by simp [C])))

/-- The trivial group `Unit` has `{⊤}` as its singleton family of compact open subgroups, and this
singleton forms a filter basis of `𝓝 (1 : Unit)`. -/
example : {H : OpenSubgroup Unit | IsCompact (H : Set Unit)} = {⊤} ∧
    (𝓝 (1 : Unit)).HasBasis (fun H : OpenSubgroup Unit ↦ IsCompact (H : Set Unit))
      fun H ↦ (H : Set Unit) := by
  refine ⟨?_, IsTopologicalGroup.nhds_one_hasBasis_isCompact_openSubgroup Unit⟩
  ext H
  refine ⟨fun _ ↦ mem_singleton_iff.mpr ?_, ?_⟩
  · ext x
    exact ⟨fun _ ↦ trivial, fun _ ↦ Subsingleton.elim (1 : Unit) x ▸ H.one_mem⟩
  · rintro rfl
    exact isCompact_univ

/-- On the locally compact Hausdorff group `ℝ`, the identity neighbourhood `Ioo (-1 : ℝ) 1`
contains no open additive subgroup, so local compactness alone does not yield van Dantzig's
conclusion. -/
example : LocallyCompactSpace ℝ ∧ T2Space ℝ ∧ Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) ∧
    ¬ ∃ H : OpenAddSubgroup ℝ, (H : Set ℝ) ⊆ Ioo (-1 : ℝ) 1 := by
  refine ⟨inferInstance, inferInstance, Ioo_mem_nhds (by norm_num) (by norm_num), ?_⟩
  rintro ⟨H, hH⟩
  have huniv : (H : Set ℝ) = univ := IsClopen.eq_univ H.isClopen ⟨0, H.zero_mem⟩
  have h1 : (1 : ℝ) ∈ Ioo (-1 : ℝ) 1 := hH (huniv ▸ mem_univ 1)
  exact lt_irrefl (1 : ℝ) h1.2

end TauCeti
