/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Analysis.Normed.Field.Basic
public import TauCeti.Analysis.Normed.Group.DiscreteSubgroup
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Units stabilizing a discrete subgroup of a normed division ring

Let `L` be a nonzero discrete additive subgroup of a proper normed division ring `𝕜`, viewed as a
`ℤ`-submodule. The units `u` of `𝕜` act on such subgroups by left multiplication, and those with
`u • L = L` form the stabilizer `MulAction.stabilizer 𝕜ˣ L`. For a lattice `Λ ⊂ ℂ` this is the
group of linear automorphisms `z ↦ u z` of the complex torus `ℂ / Λ`, which contains `-1`.

A shortest nonzero vector `l₀` of `L` exists (`Submodule.exists_norm_le_of_ne_bot`). A stabilizing
unit `u` and its inverse both carry `l₀` to a nonzero vector of `L`, so `‖u‖ = 1`
(`Submodule.norm_eq_one_of_mem_stabilizer`), and `u` is determined by `u * l₀`, a vector of `L` of
norm `‖l₀‖`. Hence the stabilizer is finite (`Submodule.finite_stabilizer_units`).

## Main results

* `Submodule.mem_stabilizer_units_iff`: a unit stabilizes `L` exactly when multiplication by it
  and by its inverse carries `L` into itself.
* `Submodule.norm_eq_one_of_mem_stabilizer`: a unit stabilizing it has norm one.
* `Submodule.finite_stabilizer_units`: the units stabilizing it form a finite group.
-/

public section

open Metric Pointwise

namespace Submodule

/-- A unit `u` of a ring stabilizes an additive subgroup `L` exactly when multiplication by `u` and
by `u⁻¹` both carry `L` into itself. -/
theorem mem_stabilizer_units_iff {R : Type*} [Ring R] {L : Submodule ℤ R} {u : Rˣ} :
    u ∈ MulAction.stabilizer Rˣ L ↔
      (∀ l ∈ L, (u : R) * l ∈ L) ∧ ∀ l ∈ L, ((u⁻¹ : Rˣ) : R) * l ∈ L := by
  have hle {v : Rˣ} : v • L ≤ L ↔ ∀ l ∈ L, (v : R) * l ∈ L := by
    simp [IsConcreteLE.le_iff, mem_smul_pointwise_iff_exists, Units.smul_def]
  rw [MulAction.mem_stabilizer_iff, ← hle, ← hle]
  refine ⟨fun h ↦ ⟨h.le, ?_⟩, fun ⟨h, h'⟩ ↦ h.antisymm fun l hl ↦ ?_⟩
  · calc u⁻¹ • L = u⁻¹ • u • L := by rw [h]
      _ ≤ L := (inv_smul_smul u L).le
  · have := smul_mem_pointwise_smul _ u L (h' (smul_mem_pointwise_smul l u⁻¹ L hl))
    rwa [smul_inv_smul] at this

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] [ProperSpace 𝕜] (L : Submodule ℤ 𝕜)
  [DiscreteTopology L]

variable {L} in
/-- A unit of a proper normed division ring stabilizing a nonzero discrete additive subgroup has
norm one. -/
theorem norm_eq_one_of_mem_stabilizer (hL : L ≠ ⊥) {u : 𝕜ˣ} (hu : u ∈ MulAction.stabilizer 𝕜ˣ L) :
    ‖(u : 𝕜)‖ = 1 := by
  obtain ⟨l₀, hl₀, hl₀0, hmin⟩ := L.exists_norm_le_of_ne_bot hL
  have hge {v : 𝕜ˣ} (hv : v ∈ MulAction.stabilizer 𝕜ˣ L) : 1 ≤ ‖(v : 𝕜)‖ := by
    have := hmin _ ((mem_stabilizer_units_iff.mp hv).1 l₀ hl₀) (mul_ne_zero v.ne_zero hl₀0)
    rw [norm_mul] at this
    exact le_of_mul_le_mul_right (by simpa using this) (norm_pos_iff.mpr hl₀0)
  have h₁ := hge hu
  have h₂ := hge (inv_mem hu)
  rw [Units.val_inv_eq_inv_val, norm_inv] at h₂
  exact le_antisymm ((one_le_inv₀ (h₁.trans_lt' one_pos)).mp h₂) h₁

/-- The units of a proper normed division ring stabilizing a nonzero discrete additive subgroup `L`
form a finite group: such a unit is determined by its value on a shortest nonzero vector of `L`,
which it carries to a vector of `L` of the same norm. -/
theorem finite_stabilizer_units (hL : L ≠ ⊥) : Finite (MulAction.stabilizer 𝕜ˣ L) := by
  obtain ⟨l₀, hl₀, hl₀0, -⟩ := L.exists_norm_le_of_ne_bot hL
  have hfin : (closedBall (0 : 𝕜) ‖l₀‖ ∩ (L : Set 𝕜)).Finite :=
    finite_isBounded_inter_isClosed (s := (L : Set 𝕜))
      (isDiscrete_iff_discreteTopology.mpr ‹_›) isBounded_closedBall
      (AddSubgroup.isClosed_of_discreteTopology (U := L.toAddSubgroup))
  have := hfin.to_subtype
  refine Finite.of_injective (β := ↥(closedBall (0 : 𝕜) ‖l₀‖ ∩ (L : Set 𝕜)))
    (fun u ↦ ⟨(u : 𝕜ˣ) * l₀, ?_, (mem_stabilizer_units_iff.mp u.2).1 l₀ hl₀⟩) fun u v h ↦ ?_
  · simp [norm_mul, norm_eq_one_of_mem_stabilizer hL u.2]
  · exact Subtype.ext (Units.ext (mul_right_cancel₀ hl₀0 (congrArg Subtype.val h)))

end Submodule
