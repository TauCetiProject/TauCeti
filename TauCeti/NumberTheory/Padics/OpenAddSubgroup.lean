/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.Topology.Algebra.Group.Pointwise
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Fractional lattices as compact open additive subgroups of `ℚ_[p]`

In the noncompact locally profinite field `ℚ_[p]`, the closed ultrametric balls
`{x : ℚ_[p] | ‖x‖ ≤ p ^ (-m)}` (`m : ℤ`) are the fractional `ℤ_[p]`-lattices `p ^ m • ℤ_[p]`.
Because `ℚ_[p]` is ultrametric and proper, each such ball is a compact clopen additive subgroup
(`Padic.zpowOpenAddSubgroup p m : OpenAddSubgroup ℚ_[p]`), its additive translation stabilizer in
`ℚ_[p]` is itself, and as `m` ranges over `ℤ` these subgroups form an antitone `ℤ`-indexed
neighbourhood basis of `0 : ℚ_[p]`.

## Main definitions

* `Padic.zpowOpenAddSubgroup p m`: the compact open additive subgroup of `ℚ_[p]` of elements of
  norm at most `p ^ (-m)`, built via `IsUltrametricDist.closedBall_openAddSubgroup`.

## Main results

* `Padic.mem_zpowOpenAddSubgroup_iff_exists_padicInt` and `Padic.coe_zpowOpenAddSubgroup`:
  `zpowOpenAddSubgroup p m` has underlying set `(p : ℚ_[p]) ^ m • (PadicInt.subring p : Set ℚ_[p])`;
  at `m = 0` and `m = 1` this recovers `ℤ_[p]` and `p • ℤ_[p]`.
* `Padic.isCompact_zpowOpenAddSubgroup`, `Padic.isCompact_zpow_smul_subring`, and
  `Padic.isClopen_zpow_smul_subring`: compactness and clopenness of `p ^ m • ℤ_[p]` in `ℚ_[p]`.
* `Padic.zpowOpenAddSubgroup_antitone`: `m ↦ zpowOpenAddSubgroup p m` is antitone.
* `Padic.stabilizer_zpow_smul_subring` and `Padic.stabilizerOpenAddSubgroup_zpow_smul_subring`:
  the translation stabilizer of `p ^ m • ℤ_[p]` in `ℚ_[p]` is `zpowOpenAddSubgroup p m`.
* `Padic.nhds_zero_hasBasis_zpowOpenAddSubgroup` and `Padic.nhds_zero_hasBasis_zpow_smul_subring`:
  the fractional lattices `p ^ m • ℤ_[p]` (`m : ℤ`) form a neighbourhood basis of `0 : ℚ_[p]`.
-/

public section

open Filter Metric Set
open scoped Pointwise Topology

namespace Padic

section Prime

variable (p : ℕ) [Fact p.Prime]

/-- The compact open additive subgroup `{x : ℚ_[p] | ‖x‖ ≤ p ^ (-m)}` (`m : ℤ`), realized as the
ultrametric closed ball of radius `p ^ (-m)` around `0` via
`IsUltrametricDist.closedBall_openAddSubgroup`. Its underlying set is the fractional lattice
`p ^ m • ℤ_[p]` (`Padic.coe_zpowOpenAddSubgroup`). -/
noncomputable def zpowOpenAddSubgroup (m : ℤ) : OpenAddSubgroup ℚ_[p] :=
  IsUltrametricDist.closedBall_openAddSubgroup ℚ_[p]
    (zpow_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) (-m))

variable {p}

theorem coe_zpowOpenAddSubgroup_eq_closedBall (m : ℤ) :
    ((zpowOpenAddSubgroup p m : OpenAddSubgroup ℚ_[p]) : Set ℚ_[p]) =
      closedBall (0 : ℚ_[p]) ((p : ℝ) ^ (-m)) :=
  (rfl)

@[simp]
theorem mem_zpowOpenAddSubgroup_iff {m : ℤ} {x : ℚ_[p]} :
    x ∈ zpowOpenAddSubgroup p m ↔ ‖x‖ ≤ (p : ℝ) ^ (-m) :=
  mem_closedBall_zero_iff

/-- An element of `ℚ_[p]` has norm at most `p ^ (-m)` if and only if it is `p ^ m` times a
`p`-adic integer. -/
theorem mem_zpowOpenAddSubgroup_iff_exists_padicInt {m : ℤ} {x : ℚ_[p]} :
    x ∈ zpowOpenAddSubgroup p m ↔ ∃ y : ℤ_[p], (p : ℚ_[p]) ^ m * (y : ℚ_[p]) = x := by
  rw [mem_zpowOpenAddSubgroup_iff]
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpR0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  constructor
  · intro hx
    have hz : ‖(p : ℚ_[p]) ^ (-m) * x‖ ≤ 1 := by
      calc ‖(p : ℚ_[p]) ^ (-m) * x‖
          = (p : ℝ) ^ m * ‖x‖ := by rw [norm_mul, Padic.norm_p_zpow, neg_neg]
        _ ≤ (p : ℝ) ^ m * (p : ℝ) ^ (-m) :=
            mul_le_mul_of_nonneg_left hx (zpow_nonneg (Nat.cast_nonneg p) m)
        _ = 1 := by rw [← zpow_add₀ hpR0, add_neg_cancel, zpow_zero]
    refine ⟨Padic.lift ((p : ℚ_[p]) ^ (-m) * x) hz, ?_⟩
    rw [PadicInt.coe_lift, ← mul_assoc, ← zpow_add₀ hp0, add_neg_cancel, zpow_zero, one_mul]
  · rintro ⟨y, rfl⟩
    rw [norm_mul, Padic.norm_p_zpow]
    exact mul_le_of_le_one_right (zpow_nonneg (Nat.cast_nonneg p) (-m)) y.norm_le_one

/-- The underlying set of `zpowOpenAddSubgroup p m` is the fractional lattice
`(p : ℚ_[p]) ^ m • (PadicInt.subring p : Set ℚ_[p])`. -/
theorem coe_zpowOpenAddSubgroup (m : ℤ) :
    ((zpowOpenAddSubgroup p m : OpenAddSubgroup ℚ_[p]) : Set ℚ_[p]) =
      (p : ℚ_[p]) ^ m • (PadicInt.subring p : Set ℚ_[p]) := by
  ext x
  rw [SetLike.mem_coe, mem_zpowOpenAddSubgroup_iff_exists_padicInt]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, y.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

/-- At `m = 0`, `zpowOpenAddSubgroup p 0` has underlying set `ℤ_[p]`. -/
theorem coe_zpowOpenAddSubgroup_zero :
    ((zpowOpenAddSubgroup p 0 : OpenAddSubgroup ℚ_[p]) : Set ℚ_[p]) =
      (PadicInt.subring p : Set ℚ_[p]) := by
  simpa using coe_zpowOpenAddSubgroup (p := p) 0

/-- At `m = 0`, `zpowOpenAddSubgroup p 0` has underlying additive subgroup
`(PadicInt.subring p).toAddSubgroup`. -/
@[simp]
theorem toAddSubgroup_zpowOpenAddSubgroup_zero :
    (zpowOpenAddSubgroup p 0).toAddSubgroup = (PadicInt.subring p).toAddSubgroup :=
  SetLike.coe_injective coe_zpowOpenAddSubgroup_zero

/-- At `m = 1`, `zpowOpenAddSubgroup p 1` has underlying set `p • ℤ_[p]`. -/
theorem coe_zpowOpenAddSubgroup_one :
    ((zpowOpenAddSubgroup p 1 : OpenAddSubgroup ℚ_[p]) : Set ℚ_[p]) =
      (p : ℚ_[p]) • (PadicInt.subring p : Set ℚ_[p]) := by
  simpa using coe_zpowOpenAddSubgroup (p := p) 1

/-- Every fractional lattice `zpowOpenAddSubgroup p m` is compact in `ℚ_[p]`. -/
theorem isCompact_zpowOpenAddSubgroup (m : ℤ) :
    IsCompact ((zpowOpenAddSubgroup p m : OpenAddSubgroup ℚ_[p]) : Set ℚ_[p]) :=
  isCompact_closedBall (0 : ℚ_[p]) ((p : ℝ) ^ (-m))

/-- Every fractional lattice `(p : ℚ_[p]) ^ m • ℤ_[p]` is compact in `ℚ_[p]`. -/
theorem isCompact_zpow_smul_subring (m : ℤ) :
    IsCompact ((p : ℚ_[p]) ^ m • (PadicInt.subring p : Set ℚ_[p])) :=
  coe_zpowOpenAddSubgroup (p := p) m ▸ isCompact_zpowOpenAddSubgroup m

/-- Every fractional lattice `(p : ℚ_[p]) ^ m • ℤ_[p]` is clopen in `ℚ_[p]`. -/
theorem isClopen_zpow_smul_subring (m : ℤ) :
    IsClopen ((p : ℚ_[p]) ^ m • (PadicInt.subring p : Set ℚ_[p])) :=
  coe_zpowOpenAddSubgroup (p := p) m ▸ (zpowOpenAddSubgroup p m).isClopen

/-- `PadicInt.subring p` is compact as a subset of `ℚ_[p]`. -/
theorem isCompact_padicInt_subring : IsCompact (PadicInt.subring p : Set ℚ_[p]) :=
  coe_zpowOpenAddSubgroup_zero (p := p) ▸ isCompact_zpowOpenAddSubgroup 0

/-- `PadicInt.subring p` is clopen as a subset of `ℚ_[p]`. -/
theorem isClopen_padicInt_subring : IsClopen (PadicInt.subring p : Set ℚ_[p]) :=
  coe_zpowOpenAddSubgroup_zero (p := p) ▸ (zpowOpenAddSubgroup p 0).isClopen

/-- The filtration `m ↦ zpowOpenAddSubgroup p m` is antitone: larger exponents give smaller
balls. -/
theorem zpowOpenAddSubgroup_antitone : Antitone (zpowOpenAddSubgroup p) := fun _ _ hmn _ hx ↦ by
  rw [mem_zpowOpenAddSubgroup_iff] at hx ⊢
  exact hx.trans
    (zpow_le_zpow_right₀ (Nat.one_le_cast.mpr (Fact.out : p.Prime).pos) (neg_le_neg hmn))

/-- The additive translation stabilizer of `(p : ℚ_[p]) ^ m • ℤ_[p]` in `ℚ_[p]` is
`(zpowOpenAddSubgroup p m).toAddSubgroup`. -/
@[simp]
theorem stabilizer_zpow_smul_subring (m : ℤ) :
    AddAction.stabilizer ℚ_[p] ((p : ℚ_[p]) ^ m • (PadicInt.subring p : Set ℚ_[p])) =
      (zpowOpenAddSubgroup p m).toAddSubgroup := by
  rw [← coe_zpowOpenAddSubgroup, ← OpenAddSubgroup.coe_toAddSubgroup,
    AddAction.stabilizer_addSubgroup]

/-- Packaged as an open additive subgroup, the translation stabilizer of `(p : ℚ_[p]) ^ m • ℤ_[p]`
is `zpowOpenAddSubgroup p m`. -/
@[simp]
theorem stabilizerOpenAddSubgroup_zpow_smul_subring (m : ℤ) :
    AddAction.stabilizerOpenAddSubgroup (isCompact_zpow_smul_subring (p := p) m)
        (isClopen_zpow_smul_subring (p := p) m).isOpen =
      zpowOpenAddSubgroup p m :=
  OpenAddSubgroup.toAddSubgroup_injective <| by
    rw [AddAction.toAddSubgroup_stabilizerOpenAddSubgroup, stabilizer_zpow_smul_subring]

/-- The additive translation stabilizer of `ℤ_[p]` in `ℚ_[p]` is `ℤ_[p]` itself. -/
@[simp]
theorem stabilizer_padicInt_subring :
    AddAction.stabilizer ℚ_[p] (PadicInt.subring p : Set ℚ_[p]) =
      (PadicInt.subring p).toAddSubgroup := by
  rw [← coe_zpowOpenAddSubgroup_zero, ← OpenAddSubgroup.coe_toAddSubgroup,
    AddAction.stabilizer_addSubgroup, toAddSubgroup_zpowOpenAddSubgroup_zero]

/-- The additive translation stabilizer of `p • ℤ_[p]` in `ℚ_[p]` is
`(zpowOpenAddSubgroup p 1).toAddSubgroup`. -/
@[simp]
theorem stabilizer_smul_padicInt_subring :
    AddAction.stabilizer ℚ_[p] ((p : ℚ_[p]) • (PadicInt.subring p : Set ℚ_[p])) =
      (zpowOpenAddSubgroup p 1).toAddSubgroup := by
  simpa using stabilizer_zpow_smul_subring (p := p) 1

variable (p)

/-- The compact open additive subgroups `zpowOpenAddSubgroup p m` (`m : ℤ`) form a neighbourhood
basis of `0 : ℚ_[p]`. -/
theorem nhds_zero_hasBasis_zpowOpenAddSubgroup :
    (𝓝 (0 : ℚ_[p])).HasBasis (fun _ : ℤ ↦ True)
      fun m ↦ ((zpowOpenAddSubgroup p m : OpenAddSubgroup ℚ_[p]) : Set ℚ_[p]) := by
  refine (Metric.nhds_basis_closedBall (x := (0 : ℚ_[p]))).to_hasBasis
    (fun ε hε ↦ ?_) (fun m _ ↦ ⟨(p : ℝ) ^ (-m),
      zpow_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) (-m), Subset.rfl⟩)
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
  exact ⟨k, trivial, closedBall_subset_closedBall hk.le⟩

/-- The fractional lattices `(p : ℚ_[p]) ^ m • ℤ_[p]` (`m : ℤ`) form a neighbourhood basis of
`0 : ℚ_[p]`. -/
theorem nhds_zero_hasBasis_zpow_smul_subring :
    (𝓝 (0 : ℚ_[p])).HasBasis (fun _ : ℤ ↦ True)
      fun m ↦ (p : ℚ_[p]) ^ m • (PadicInt.subring p : Set ℚ_[p]) := by
  simpa only [coe_zpowOpenAddSubgroup] using nhds_zero_hasBasis_zpowOpenAddSubgroup p

end Prime

end Padic

end
