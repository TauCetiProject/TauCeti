/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Instances.Real.Lemmas
public import TauCeti.NumberTheory.Padics.Basic
public import TauCeti.Topology.Algebra.Group.Perm
public import TauCeti.Topology.Algebra.Nonarchimedean.LocallyProfinite

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

public section

open Filter Metric Set Topology
open scoped Pointwise

namespace TauCeti.Examples.LocallyProfinite

section PadicTwo

/-- The `2`-adic field `ℚ_[2]` is noncompact, locally compact, Hausdorff, totally disconnected, and
a nonarchimedean additive group. -/
theorem padicTwo_locallyProfinite_and_not_compactSpace :
    ¬ CompactSpace ℚ_[2] ∧ LocallyCompactSpace ℚ_[2] ∧ T2Space ℚ_[2] ∧
      TotallyDisconnectedSpace ℚ_[2] ∧ NonarchimedeanAddGroup ℚ_[2] := by
  refine ⟨fun h ↦ ?_, inferInstance, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨R, hR⟩ := (@isCompact_univ ℚ_[2] _ h).isBounded.exists_norm_le
  obtain ⟨x, hx⟩ := NormedField.exists_lt_norm ℚ_[2] R
  exact hx.not_ge (hR x (mem_univ x))

/-- Scaling `ℤ_[2] ⊆ ℚ_[2]` by `2 ^ m` (`m : ℤ`) yields the ultrametric closed ball of radius
`2 ^ (-m)`, which is the carrier of a compact open additive subgroup of `ℚ_[2]`. -/
theorem padicTwo_zpow_smul_padicInt_eq_closedBall (m : ℤ) :
    (2 : ℚ_[2]) ^ m • Set.range (PadicInt.Coe.ringHom (p := 2)) =
      (IsUltrametricDist.closedBall_openAddSubgroup ℚ_[2]
        (zpow_pos two_pos (-m)) : Set ℚ_[2]) := by
  have hrange : Set.range (PadicInt.Coe.ringHom (p := 2)) = closedBall (0 : ℚ_[2]) 1 :=
    Subset.antisymm
      (by rintro _ ⟨a, rfl⟩; simpa [mem_closedBall_zero_iff] using
        PadicInt.norm_coe_ringHom_le_one a)
      PadicInt.closedBall_subset_range_coe_ringHom
  have h2ne : (2 : ℚ_[2]) ^ m ≠ 0 := zpow_ne_zero m two_ne_zero
  have hnorm2 : ‖(2 : ℚ_[2]) ^ m‖ = (2 : ℝ) ^ (-m) := by
    simpa using Padic.norm_p_zpow (p := 2) m
  rw [hrange]
  ext x
  change x ∈ (2 : ℚ_[2]) ^ m • closedBall (0 : ℚ_[2]) 1 ↔
    x ∈ closedBall (0 : ℚ_[2]) ((2 : ℝ) ^ (-m))
  simp only [mem_smul_set, smul_eq_mul, mem_closedBall_zero_iff]
  refine ⟨?_, fun hx ↦ ⟨((2 : ℚ_[2]) ^ m)⁻¹ * x, ?_, mul_inv_cancel_left₀ h2ne x⟩⟩
  · rintro ⟨y, hy, rfl⟩
    calc ‖(2 : ℚ_[2]) ^ m * y‖ = (2 : ℝ) ^ (-m) * ‖y‖ := by rw [norm_mul, hnorm2]
      _ ≤ (2 : ℝ) ^ (-m) * 1 := mul_le_mul_of_nonneg_left hy (zpow_pos two_pos (-m)).le
      _ = (2 : ℝ) ^ (-m) := mul_one _
  · rw [norm_mul, norm_inv, hnorm2, zpow_neg, inv_inv]
    calc (2 : ℝ) ^ m * ‖x‖ ≤ (2 : ℝ) ^ m * (2 : ℝ) ^ (-m) :=
          mul_le_mul_of_nonneg_left hx (zpow_pos two_pos m).le
      _ = 1 := by rw [← zpow_add₀ two_ne_zero, add_neg_cancel, zpow_zero]

/-- In `ℚ_[2]`, `C = ℤ_[2]` has additive translation stabilizer equal to `ℤ_[2]` itself. -/
theorem padicTwo_stabilizer_padicInt :
    (AddAction.stabilizer ℚ_[2] (Set.range (PadicInt.Coe.ringHom (p := 2))) : Set ℚ_[2]) =
      Set.range (PadicInt.Coe.ringHom (p := 2)) := by
  have h := padicTwo_zpow_smul_padicInt_eq_closedBall 0
  simp only [zpow_zero, one_smul, neg_zero] at h
  rw [h, ← OpenAddSubgroup.coe_toAddSubgroup, AddAction.stabilizer_addSubgroup]

/-- In `ℚ_[2]`, `C = 2 • ℤ_[2]` has additive translation stabilizer equal to `2 • ℤ_[2]`. -/
theorem padicTwo_stabilizer_two_smul_padicInt :
    (AddAction.stabilizer ℚ_[2]
      ((2 : ℚ_[2]) • Set.range (PadicInt.Coe.ringHom (p := 2))) : Set ℚ_[2]) =
      (2 : ℚ_[2]) • Set.range (PadicInt.Coe.ringHom (p := 2)) := by
  have h := padicTwo_zpow_smul_padicInt_eq_closedBall 1
  simp only [zpow_one] at h
  rw [h, ← OpenAddSubgroup.coe_toAddSubgroup, AddAction.stabilizer_addSubgroup]

/-- The compact open subgroups `2 ^ m • ℤ_[2]` (`m : ℤ`) form a neighbourhood basis of `0` in
`ℚ_[2]`. -/
theorem padicTwo_nhds_zero_hasBasis :
    (𝓝 (0 : ℚ_[2])).HasBasis (fun _ : ℤ ↦ True)
      fun m : ℤ ↦ (2 : ℚ_[2]) ^ m • Set.range (PadicInt.Coe.ringHom (p := 2)) := by
  refine ⟨fun U ↦ ⟨fun hU ↦ ?_, fun ⟨m, _, hm⟩ ↦ ?_⟩⟩
  · obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hU
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (2⁻¹ : ℝ) ^ n < ε :=
      exists_pow_lt_of_lt_one hε (by norm_num)
    refine ⟨n, trivial, ?_⟩
    rw [padicTwo_zpow_smul_padicInt_eq_closedBall]
    refine Subset.trans (Metric.closedBall_subset_closedBall ?_) hball
    simpa [zpow_neg, zpow_natCast, inv_pow] using hn.le
  · rw [padicTwo_zpow_smul_padicInt_eq_closedBall] at hm
    exact mem_of_superset
      (IsUltrametricDist.closedBall_openAddSubgroup ℚ_[2] (zpow_pos two_pos (-m))).mem_nhds_zero hm

end PadicTwo

section SymmetricThree

/-- The subset `{1, (0 1), (0 2)}` of `Equiv.Perm (Fin 3)`. -/
def symThreeClopenSet : Set (Equiv.Perm (Fin 3)) :=
  {1, Equiv.swap 0 1, Equiv.swap 0 2}

/-- Membership in `symThreeClopenSet` unfolds to the three explicit permutations. -/
@[simp]
theorem mem_symThreeClopenSet_iff {σ : Equiv.Perm (Fin 3)} :
    σ ∈ symThreeClopenSet ↔ σ = 1 ∨ σ = Equiv.swap 0 1 ∨ σ = Equiv.swap 0 2 :=
  Iff.rfl

/-- In discrete `S₃ = Equiv.Perm (Fin 3)`, `C = {1, (0 1), (0 2)}` is compact and clopen, is not a
subgroup because `(0 1) * (0 2)` lies outside `C`, and has trivial left translation stabilizer. -/
theorem symThreeClopenSet_isCompact_isClopen_and_stabilizer_eq_bot :
    IsCompact symThreeClopenSet ∧
      IsClopen symThreeClopenSet ∧
      Equiv.swap (0 : Fin 3) 1 * Equiv.swap 0 2 ∉ symThreeClopenSet ∧
      MulAction.stabilizer (Equiv.Perm (Fin 3)) symThreeClopenSet = ⊥ := by
  refine ⟨symThreeClopenSet.toFinite.isCompact, isClopen_discrete _, ?_, ?_⟩
  · rw [mem_symThreeClopenSet_iff]
    decide
  · refine (Subgroup.eq_bot_iff_forall _).mpr fun σ hσ ↦ ?_
    have h1 : σ ∈ symThreeClopenSet := by
      simpa using (MulAction.mem_stabilizer_set.mp hσ 1).mpr (Or.inl rfl)
    rcases mem_symThreeClopenSet_iff.mp h1 with rfl | rfl | rfl
    · rfl
    · exfalso
      have hmem : Equiv.swap (0 : Fin 3) 1 * Equiv.swap 0 2 ∈ symThreeClopenSet :=
        (MulAction.mem_stabilizer_set.mp hσ (Equiv.swap 0 2)).mpr (Or.inr (Or.inr rfl))
      revert hmem
      rw [mem_symThreeClopenSet_iff]
      decide
    · exfalso
      have hmem : Equiv.swap (0 : Fin 3) 2 * Equiv.swap 0 1 ∈ symThreeClopenSet :=
        (MulAction.mem_stabilizer_set.mp hσ (Equiv.swap 0 1)).mpr (Or.inr (Or.inl rfl))
      revert hmem
      rw [mem_symThreeClopenSet_iff]
      decide

end SymmetricThree

section TrivialAndReal

/-- The trivial group `Unit` has a unique open subgroup `⊤`, which is compact and forms the
singleton compact open neighbourhood basis at `1`. -/
theorem unit_openSubgroup_eq_top_and_nhds_one_hasBasis :
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
theorem real_locallyCompactSpace_and_not_exists_openAddSubgroup_subset_Ioo :
    LocallyCompactSpace ℝ ∧ ¬ ∃ H : OpenAddSubgroup ℝ, (H : Set ℝ) ⊆ Set.Ioo (-1 : ℝ) 1 := by
  refine ⟨inferInstance, ?_⟩
  rintro ⟨H, hH⟩
  have huniv : (H : Set ℝ) = univ := H.isClopen.eq_univ ⟨0, H.zero_mem⟩
  have h1 : (1 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := hH (huniv ▸ mem_univ 1)
  exact lt_irrefl (1 : ℝ) h1.2

end TrivialAndReal

end TauCeti.Examples.LocallyProfinite
