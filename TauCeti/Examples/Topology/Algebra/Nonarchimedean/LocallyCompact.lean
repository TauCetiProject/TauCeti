/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.GroupTheory.Perm.Fin
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import TauCeti.Topology.Algebra.Group.OpenSubgroup.Compact
import TauCeti.Topology.Algebra.Group.Perm
import TauCeti.Topology.Algebra.MulAction.Stabilizer
import TauCeti.Topology.Algebra.Nonarchimedean.LocallyCompact

/-!
# Examples of compact open set-stabilizers and van Dantzig's theorem

Concrete instances and sharpness witnesses for `TauCeti.openStabilizer`,
`OpenSubgroup.toProfiniteGrp`, and van Dantzig's theorem:

1. In the noncompact locally profinite additive group `ℚ_[2]`, the subsets `ℤ_[2]` and `2 ℤ_[2]`
   are compact open additive subgroups equal to their own translation stabilizers, and the scaled
   lattices `2 ^ m • ℤ_[2]` (`m : ℤ`) form a compact open additive subgroup basis of `𝓝 0`.
2. In the discrete symmetric group `Equiv.Perm (Fin 3)`, the subset `C = {1, swap 0 1, swap 0 2}`
   is compact, clopen, and contains `1`, yet is not a subgroup (`swap 0 1 * swap 0 2 ∉ C`); its
   left-translation open stabilizer is `⊥ = {1}`.
3. On the trivial group `Unit`, `{1}` is the unique open subgroup and gives the singleton compact
   open basis of `𝓝 1`.
4. On connected locally compact `ℝ`, `Ioo (-1) 1 ∈ 𝓝 0` contains no open additive subgroup, showing
   that local compactness and Hausdorff separation alone do not yield open subgroups.
-/

open Filter Metric Set Topology
open scoped Pointwise

namespace TauCeti.Examples

/-! ### 1. `2`-adic rationals `ℚ_[2]` and scaled lattices `2 ^ m • ℤ_[2]` -/

-- `ℚ_[2]` is noncompact, yet locally compact, totally disconnected, and nonarchimedean.
example : ¬ CompactSpace ℚ_[2] := by
  intro h
  obtain ⟨r, hr⟩ := isCompact_univ.isBounded.subset_closedBall (0 : ℚ_[2])
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt r (one_lt_two : (1 : ℝ) < 2)
  have hmem : ((2 : ℚ_[2])⁻¹) ^ n ∈ closedBall (0 : ℚ_[2]) r := hr (mem_univ _)
  have h2 : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := by simpa using Padic.norm_p (p := 2)
  rw [mem_closedBall, dist_zero_right, norm_pow, norm_inv, h2, inv_inv] at hmem
  exact hn.not_ge hmem

-- Downstream synthesis of `NonarchimedeanGroup` on any locally profinite group, and on open
-- subgroups thereof.
example (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [TotallyDisconnectedSpace G] (U : OpenSubgroup G) : NonarchimedeanGroup U :=
  inferInstance

example : NonarchimedeanAddGroup ℚ_[2] := inferInstance

example : NonarchimedeanRing ℚ_[2] := inferInstance

-- `C = ℤ_[2]` and `C = 2 ℤ_[2]` have additive translation stabilizers `ℤ_[2]` and `2 ℤ_[2]`.
example :
    (AddAction.stabilizer ℚ_[2] (Set.range (Subtype.val : ℤ_[2] → ℚ_[2])) : Set ℚ_[2]) =
      Set.range (Subtype.val : ℤ_[2] → ℚ_[2]) := by
  let A : AddSubgroup ℚ_[2] := (PadicInt.subring 2).toAddSubgroup
  have hA : Set.range (Subtype.val : ℤ_[2] → ℚ_[2]) = (A : Set ℚ_[2]) := Subtype.range_coe
  rw [hA]
  exact congrArg SetLike.coe (AddAction.stabilizer_addSubgroup A)

example :
    (AddAction.stabilizer ℚ_[2]
        ((2 : ℚ_[2]) • Set.range (Subtype.val : ℤ_[2] → ℚ_[2])) : Set ℚ_[2]) =
      (2 : ℚ_[2]) • Set.range (Subtype.val : ℤ_[2] → ℚ_[2]) := by
  let A : AddSubgroup ℚ_[2] :=
    (PadicInt.subring 2).toAddSubgroup.map (AddMonoidHom.mulLeft (2 : ℚ_[2]))
  have hA : (2 : ℚ_[2]) • Set.range (Subtype.val : ℤ_[2] → ℚ_[2]) = (A : Set ℚ_[2]) := by
    rw [Subtype.range_coe, AddSubgroup.coe_map, AddMonoidHom.coe_mulLeft]
    rfl
  rw [hA]
  exact congrArg SetLike.coe (AddAction.stabilizer_addSubgroup A)

-- Each `2 ^ m • ℤ_[2]` is a compact clopen closed ball, and `{2 ^ m • ℤ_[2] | m : ℤ}` is a basis
-- of `𝓝 0`.
example : (∀ m : ℤ, IsCompact ((2 : ℚ_[2]) ^ m • Set.range (Subtype.val : ℤ_[2] → ℚ_[2])) ∧
      IsClopen ((2 : ℚ_[2]) ^ m • Set.range (Subtype.val : ℤ_[2] → ℚ_[2]))) ∧
    (𝓝 (0 : ℚ_[2])).HasBasis (fun _ : ℤ ↦ True)
      (fun m : ℤ ↦ (2 : ℚ_[2]) ^ m • Set.range (Subtype.val : ℤ_[2] → ℚ_[2])) := by
  have h2 : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := by simpa using Padic.norm_p (p := 2)
  have hball (m : ℤ) : (2 : ℚ_[2]) ^ m • Set.range (Subtype.val : ℤ_[2] → ℚ_[2]) =
      closedBall (0 : ℚ_[2]) ((2 : ℝ) ^ (-m)) := by
    have h2ne : (2 : ℚ_[2]) ^ m ≠ 0 := zpow_ne_zero m two_ne_zero
    have h2norm : ‖(2 : ℚ_[2]) ^ m‖ = (2 : ℝ) ^ (-m) := by
      rw [norm_zpow, h2, inv_zpow, zpow_neg]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-m) := zpow_pos two_pos (-m)
    ext x
    simp only [mem_smul_set, mem_range, mem_closedBall, dist_zero_right]
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      calc ‖(2 : ℚ_[2]) ^ m • (y : ℚ_[2])‖
          = (2 : ℝ) ^ (-m) * ‖(y : ℚ_[2])‖ := by rw [smul_eq_mul, norm_mul, h2norm]
        _ ≤ (2 : ℝ) ^ (-m) * 1 := mul_le_mul_of_nonneg_left y.2 hpos.le
        _ = (2 : ℝ) ^ (-m) := mul_one _
    · intro hx
      have hsub : ‖((2 : ℚ_[2]) ^ m)⁻¹ * x‖ ≤ 1 := by
        rw [norm_mul, norm_inv, h2norm, inv_mul_le_iff₀ hpos, mul_one]
        exact hx
      exact ⟨((2 : ℚ_[2]) ^ m)⁻¹ * x, ⟨⟨((2 : ℚ_[2]) ^ m)⁻¹ * x, hsub⟩, rfl⟩,
        by simp [smul_eq_mul, h2ne]⟩
  simp_rw [hball]
  refine ⟨fun m ↦ ⟨isCompact_closedBall 0 _,
    IsUltrametricDist.isClopen_closedBall 0 (zpow_pos two_pos (-m)).ne'⟩, ?_⟩
  refine Metric.nhds_basis_closedBall.to_hasBasis (fun ε hε ↦ ?_)
    fun m _ ↦ ⟨(2 : ℝ) ^ (-m), zpow_pos two_pos (-m), Subset.rfl⟩
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2⁻¹ : ℝ) < 1)
  refine ⟨n, trivial, closedBall_subset_closedBall ?_⟩
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  exact hn.le

/-! ### 2. Discrete `S₃`: compact clopen identity neighbourhood that is not a subgroup -/

-- `C = {1, (0 1), (0 2)}` is compact, clopen, and contains `1`, yet `(0 1) * (0 2) ∉ C`, and its
-- left-translation open stabilizer is compact and equal to `{1}`.
example :
    let C : Set (Equiv.Perm (Fin 3)) := {1, Equiv.swap 0 1, Equiv.swap 0 2}
    let H := openStabilizer (Equiv.Perm (Fin 3)) C (Set.toFinite C).isCompact (isOpen_discrete C)
    IsCompact C ∧ IsClopen C ∧ (1 : Equiv.Perm (Fin 3)) ∈ C ∧
      Equiv.swap (0 : Fin 3) 1 ∈ C ∧ Equiv.swap (0 : Fin 3) 2 ∈ C ∧
      Equiv.swap (0 : Fin 3) 1 * Equiv.swap (0 : Fin 3) 2 ∉ C ∧
      IsCompact (H : Set (Equiv.Perm (Fin 3))) ∧ (H : Subgroup (Equiv.Perm (Fin 3))) = ⊥ := by
  intro C H
  have hCc : IsCompact C := (Set.toFinite C).isCompact
  have h1C : (1 : Equiv.Perm (Fin 3)) ∈ C := by simp [C]
  refine ⟨hCc, isClopen_discrete C, h1C, by simp [C], by simp [C], by decide,
    isCompact_openStabilizer hCc (isOpen_discrete C) ⟨1, h1C⟩, ?_⟩
  rw [eq_bot_iff]
  intro σ hσ
  have hsub : σ ∈ C := openStabilizer_subset_of_one_mem hCc (isOpen_discrete C) h1C hσ
  rcases hsub with rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exfalso
    have hmem : Equiv.swap (0 : Fin 3) 1 * Equiv.swap 0 2 ∈ C := by
      rw [← (mem_openStabilizer.mp hσ)]
      exact smul_mem_smul_set (by simp [C])
    exact (by decide : Equiv.swap (0 : Fin 3) 1 * Equiv.swap (0 : Fin 3) 2 ∉ C) hmem
  · exfalso
    have hmem : Equiv.swap (0 : Fin 3) 2 * Equiv.swap 0 1 ∈ C := by
      rw [← (mem_openStabilizer.mp hσ)]
      exact smul_mem_smul_set (by simp [C])
    exact (by decide : Equiv.swap (0 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1 ∉ C) hmem

/-! ### 3. Trivial group and connected `ℝ` -/

-- The trivial group `Unit` has the singleton `{1}` as its unique compact open subgroup basis.
example : (𝓝 (1 : Unit)).HasBasis (fun H : OpenSubgroup Unit ↦ IsCompact (H : Set Unit))
    fun H ↦ (H : Set Unit) :=
  NonarchimedeanGroup.nhds_one_hasBasis_openSubgroup_isCompact Unit

example (H : OpenSubgroup Unit) : (H : Set Unit) = {1} :=
  Set.ext fun u ↦ ⟨fun _ ↦ Subsingleton.elim u 1, fun hu ↦ hu ▸ H.one_mem⟩

-- `ℝ` is locally compact and Hausdorff, yet `Ioo (-1) 1 ∈ 𝓝 0` contains no open additive subgroup.
example : LocallyCompactSpace ℝ ∧ Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) ∧
    ¬ ∃ H : OpenAddSubgroup ℝ, (H : Set ℝ) ⊆ Set.Ioo (-1 : ℝ) 1 := by
  refine ⟨inferInstance, Ioo_mem_nhds (by norm_num) (by norm_num), ?_⟩
  rintro ⟨H, hH⟩
  have huniv : (H : Set ℝ) = Set.univ := H.isClopen.eq_univ ⟨0, H.zero_mem⟩
  have h2 : (2 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := hH (huniv ▸ mem_univ 2)
  norm_num at h2

end TauCeti.Examples
