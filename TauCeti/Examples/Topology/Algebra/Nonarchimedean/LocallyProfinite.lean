/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.NumberTheory.Padics.ProperSpace
public import TauCeti.Topology.Algebra.Nonarchimedean.LocallyProfinite

/-!
# Examples of locally profinite groups and translation stabilizers

Concrete checks exercising `TauCeti.Topology.Algebra.Nonarchimedean.LocallyProfinite` and
`TauCeti.Topology.Algebra.Group.OpenSubgroup.Basic`:

* every compact open subgroup of a Hausdorff totally disconnected topological group inherits
  `CompactSpace`, `TotallyDisconnectedSpace`, `T2Space`, and `IsTopologicalGroup`;
* every trivial topological group (`Subsingleton G`) has a compact open subgroup basis at `1`;
* in connected `ℝ`, the interval `(-1, 1)` contains no open additive subgroup;
* in `ℚ_[2]`, `ℤ_[2]` and `2ℤ_[2]` are compact open additive subgroups equal to their own
  translation stabilizers, and the balls `2^m ℤ_[2]` (`m : ℤ`) form a compact open additive
  subgroup basis of `𝓝 (0 : ℚ_[2])`;
* in discrete `Equiv.Perm (Fin 3)`, `C = {1, swap 0 1, swap 0 2}` is compact and clopen with
  `1 ∈ C`, is not a subgroup, and has trivial left translation stabilizer.
-/

public section

open Filter Set Topology TauCeti
open scoped Pointwise

namespace TauCeti.Examples.Topology.LocallyProfinite

-- Every compact open subgroup of a Hausdorff totally disconnected topological group is profinite
-- (`CompactSpace`, `TotallyDisconnectedSpace`, `T2Space`, and `IsTopologicalGroup`).
example {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [TotallyDisconnectedSpace G] (U : OpenSubgroup G) (hU : IsCompact (U : Set G)) :
    CompactSpace U ∧ TotallyDisconnectedSpace U ∧ T2Space U ∧ IsTopologicalGroup U :=
  ⟨isCompact_iff_compactSpace.mp hU, inferInstance, inferInstance, inferInstance⟩

-- Every trivial topological group (`Subsingleton G`, e.g. `{1}`) has the singleton compact open
-- subgroup basis.
example (G : Type*) [Group G] [TopologicalSpace G] [Subsingleton G] :
    (𝓝 (1 : G)).HasBasis (fun H : OpenSubgroup G ↦ IsCompact (H : Set G))
      fun H ↦ (H : Set G) :=
  TauCeti.nhds_one_hasBasis_isCompact_openSubgroup

-- In `ℝ`, the interval `(-1, 1)` contains no open additive subgroup.
example : ¬ ∃ H : OpenAddSubgroup ℝ, (H : Set ℝ) ⊆ Set.Ioo (-1 : ℝ) 1 := by
  rintro ⟨H, hH⟩
  rw [H.eq_top_of_preconnectedSpace] at hH
  have h2 : (2 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := hH (OpenAddSubgroup.mem_top 2)
  norm_num at h2

-- In the noncompact additive group `ℚ_[2]`, `ℤ_[2]` (`closedBall 0 1`) and `2ℤ_[2]`
-- (`closedBall 0 2⁻¹`) are compact open additive subgroups equal to their own translation
-- stabilizers, and the balls `2^m ℤ_[2]` (`closedBall 0 (2 ^ (-m))`, `m : ℤ`) form a compact open
-- additive subgroup basis of `𝓝 (0 : ℚ_[2])`.
section PadicTwo

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

@[to_additive (attr := simp)]
private theorem coe_closedBall_openSubgroup {S : Type*} [SeminormedGroup S] [IsUltrametricDist S]
    {r : ℝ} (hr : 0 < r) :
    (IsUltrametricDist.closedBall_openSubgroup S hr : Set S) = Metric.closedBall 1 r :=
  rfl

example :
    let z2 : OpenAddSubgroup ℚ_[2] := IsUltrametricDist.closedBall_openAddSubgroup ℚ_[2] zero_lt_one
    let twoZ2 : OpenAddSubgroup ℚ_[2] :=
      IsUltrametricDist.closedBall_openAddSubgroup ℚ_[2] (by norm_num : (0 : ℝ) < 2⁻¹)
    IsCompact (z2 : Set ℚ_[2]) ∧ IsCompact (twoZ2 : Set ℚ_[2]) ∧
      AddAction.stabilizer ℚ_[2] (z2 : Set ℚ_[2]) = z2.toAddSubgroup ∧
      AddAction.stabilizer ℚ_[2] (twoZ2 : Set ℚ_[2]) = twoZ2.toAddSubgroup ∧
      (𝓝 (0 : ℚ_[2])).HasBasis (fun _ : ℤ ↦ True)
        (fun m : ℤ ↦ (IsUltrametricDist.closedBall_openAddSubgroup ℚ_[2]
          (zpow_pos (by norm_num : (0 : ℝ) < 2) (-m)) : Set ℚ_[2])) := by
  refine ⟨by rw [coe_closedBall_openAddSubgroup]; exact isCompact_closedBall (0 : ℚ_[2]) 1,
    by rw [coe_closedBall_openAddSubgroup]; exact isCompact_closedBall (0 : ℚ_[2]) 2⁻¹,
    by rw [← OpenAddSubgroup.coe_toAddSubgroup]; exact AddAction.stabilizer_addSubgroup _,
    by rw [← OpenAddSubgroup.coe_toAddSubgroup]; exact AddAction.stabilizer_addSubgroup _,
    ⟨fun U ↦ ⟨fun hU ↦ ?_, fun ⟨m, _, hmU⟩ ↦ ?_⟩⟩⟩
  · obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (2⁻¹ : ℝ) < 1)
    refine ⟨(n : ℤ) + 1, trivial, fun x hx ↦ hrU (Metric.mem_ball.mpr ?_)⟩
    rw [coe_closedBall_openAddSubgroup] at hx
    have hlt : (2 : ℝ) ^ (-((n : ℤ) + 1)) < (2⁻¹ : ℝ) ^ n := by
      rw [inv_pow, ← zpow_natCast, ← zpow_neg]
      exact zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega)
    exact (Metric.mem_closedBall.mp hx).trans_lt (hlt.trans hn)
  · rw [coe_closedBall_openAddSubgroup] at hmU
    exact mem_of_superset (Metric.closedBall_mem_nhds 0 (zpow_pos (by norm_num : (0 : ℝ) < 2) (-m)))
      hmU

end PadicTwo

-- In discrete `S₃`, `C = {1, swap 0 1, swap 0 2}` is compact and clopen with `1 ∈ C`, is not a
-- subgroup (`swap 0 1 * swap 0 2` lies outside `C`), and has trivial left translation stabilizer.
section PermFin3

open Equiv

/-- The discrete topology on `Perm (Fin 3)` for the finite-permutation stabilizer check. -/
local instance permFin3TopologicalSpace : TopologicalSpace (Perm (Fin 3)) := ⊥

/-- `Perm (Fin 3)` has discrete topology under `permFin3TopologicalSpace`. -/
local instance permFin3DiscreteTopology : DiscreteTopology (Perm (Fin 3)) := ⟨rfl⟩

private abbrev s3Clopen : Set (Perm (Fin 3)) :=
  {1, swap 0 1, swap 0 2}

example :
    IsCompact s3Clopen ∧ IsClopen s3Clopen ∧ (1 : Perm (Fin 3)) ∈ s3Clopen ∧
      swap (0 : Fin 3) 1 * swap 0 2 ∉ s3Clopen ∧
      MulAction.stabilizer (Perm (Fin 3)) s3Clopen = ⊥ := by
  refine ⟨s3Clopen.toFinite.isCompact, isClopen_discrete _, by simp [s3Clopen], by decide, ?_⟩
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  have hg1 : g ∈ s3Clopen := by
    refine s3Clopen.toFinite.isCompact.stabilizerOpenSubgroup_subset (isOpen_discrete _)
      (by simp [s3Clopen]) ?_
    rwa [s3Clopen.toFinite.isCompact.coe_stabilizerOpenSubgroup (isOpen_discrete _)]
  rcases hg1 with rfl | rfl | rfl
  · rfl
  · have hmem : swap (0 : Fin 3) 1 * swap 0 2 ∈ s3Clopen := by
      rw [← MulAction.mem_stabilizer_iff.mp hg]
      exact Set.smul_mem_smul_set (by simp [s3Clopen])
    exact absurd hmem (by decide)
  · have hmem : swap (0 : Fin 3) 2 * swap 0 1 ∈ s3Clopen := by
      rw [← MulAction.mem_stabilizer_iff.mp hg]
      exact Set.smul_mem_smul_set (by simp [s3Clopen])
    exact absurd hmem (by decide)

end PermFin3

end TauCeti.Examples.Topology.LocallyProfinite
