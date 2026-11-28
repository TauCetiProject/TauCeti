/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup
import Mathlib.Basic.Real.Pointwise
import Mathlib.Topology.Algebra.Group.Units

/-!
# Least operator norm in a right coset

The infimum of the matrix operator norm over a right coset `H g` varies continuously with `g`.
When the form is nonsingular and the subgroup is closed, the infimum is attained. These facts
allow norm cutoffs on a group of isometries to be imposed on cosets without choosing a section.
-/

public section

open Matrix Set Filter Topology
open scoped Matrix.Norms.L2Operator

namespace Subgroup

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] {J : Matrix n n 𝕜}
  (H : Subgroup (unitaryGroupOf J))

/-- The infimum of the operator norms of matrices in the right coset `H g`. -/
noncomputable def rightCosetOpNorm (g : unitaryGroupOf J) : ℝ :=
  ⨅ h : H, ‖((h.val * g : GL n 𝕜) : Matrix n n 𝕜)‖

/-- Express the coset norm as the infimum over subgroup elements. -/
theorem rightCosetOpNorm_def (g : unitaryGroupOf J) :
    H.rightCosetOpNorm g = ⨅ h : H, ‖((h.val * g : GL n 𝕜) : Matrix n n 𝕜)‖ := (rfl)

/-- A bound lies below the coset norm exactly when it lies below every representative's norm. -/
theorem le_rightCosetOpNorm_iff {g : unitaryGroupOf J} {a : ℝ} :
    a ≤ H.rightCosetOpNorm g ↔ ∀ h : H, a ≤ ‖((h.val * g : GL n 𝕜) : Matrix n n 𝕜)‖ := by
  rw [rightCosetOpNorm_def]
  exact le_ciInf_iff ⟨0, by rintro _ ⟨h, rfl⟩; positivity⟩

/-- The coset norm is no larger than the norm of any representative. -/
theorem rightCosetOpNorm_le (g : unitaryGroupOf J) (h : H) :
    H.rightCosetOpNorm g ≤ ‖((h.val * g : GL n 𝕜) : Matrix n n 𝕜)‖ :=
  (H.le_rightCosetOpNorm_iff.mp le_rfl) h

/-- Left multiplication by an element of `H` does not change the coset norm. -/
@[simp] theorem rightCosetOpNorm_mul_left (g : unitaryGroupOf J) (h : H) :
    H.rightCosetOpNorm (h.val * g) = H.rightCosetOpNorm g := by
  simpa only [rightCosetOpNorm, Equiv.coe_mulRight, Subgroup.coe_mul, mul_assoc] using
    (Equiv.mulRight h).iInf_comp (g := fun u : H ↦ ‖((u.val * g : GL n 𝕜) : Matrix n n 𝕜)‖)

/-- Under right multiplication the coset norm increases by at most the norm of the multiplier. -/
theorem rightCosetOpNorm_mul_le (g t : unitaryGroupOf J) :
    H.rightCosetOpNorm (g * t) ≤ H.rightCosetOpNorm g * ‖((t : GL n 𝕜) : Matrix n n 𝕜)‖ := by
  conv_rhs => rw [mul_comm, rightCosetOpNorm, Real.mul_iInf_of_nonneg (norm_nonneg _)]
  refine le_ciInf fun h ↦ (H.rightCosetOpNorm_le (g * t) h).trans ?_
  simpa only [Subgroup.coe_mul, Units.val_mul, mul_assoc, mul_comm (a := ‖((t : GL n 𝕜) :
    Matrix n n 𝕜)‖)] using norm_mul_le ((h.val * g : GL n 𝕜) : Matrix n n 𝕜)
      ((t : GL n 𝕜) : Matrix n n 𝕜)

/-- The coset norm is continuous, even without closedness of the subgroup. -/
theorem continuous_rightCosetOpNorm : Continuous H.rightCosetOpNorm := by
  by_cases hn : Nonempty n
  swap
  · have := not_nonempty_iff.mp hn
    have hzero : H.rightCosetOpNorm = 0 := by
      funext g
      simp [rightCosetOpNorm, Subsingleton.elim (α := Matrix n n 𝕜) _ 0]
    rw [hzero]
    exact continuous_const
  have := hn
  refine continuous_iff_continuousAt.mpr fun g ↦ ?_
  let A : unitaryGroupOf J → Matrix n n 𝕜 := fun t ↦ ((t : GL n 𝕜) : Matrix n n 𝕜)
  have hA : Continuous A := unitaryGroupOf.continuous_val
  have hu : Continuous (fun y ↦ H.rightCosetOpNorm g * ‖A (g⁻¹ * y)‖) :=
    continuous_const.mul ((hA.comp (continuous_const.mul continuous_id)).norm)
  have h₁ : Tendsto (fun y ↦ H.rightCosetOpNorm g * ‖A (g⁻¹ * y)‖) (𝓝 g)
      (𝓝 (H.rightCosetOpNorm g)) := by
    simpa only [inv_mul_cancel, A, Subgroup.coe_one, Units.val_one, norm_one, mul_one] using
      hu.continuousAt (x := g).tendsto
  have hd : Continuous (fun y ↦ ‖A (y⁻¹ * g)‖) :=
    (hA.comp (continuous_inv.mul continuous_const)).norm
  have h₂ : Tendsto (fun y ↦ H.rightCosetOpNorm g / ‖A (y⁻¹ * g)‖) (𝓝 g)
      (𝓝 (H.rightCosetOpNorm g)) := by
    have hg : ‖A (g⁻¹ * g)‖ = 1 := by simp [A]
    have hg₀ : ‖A (g⁻¹ * g)‖ ≠ 0 := hg.trans_ne one_ne_zero
    have hc : ContinuousAt (fun y ↦ H.rightCosetOpNorm g / ‖A (y⁻¹ * g)‖) g :=
      continuousAt_const.div hd.continuousAt hg₀
    simpa only [hg, div_one] using hc.tendsto
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le h₂ h₁ (fun y ↦ ?_) (fun y ↦ ?_)
  · have hy : 0 < ‖A (y⁻¹ * g)‖ := norm_pos_iff.mpr (Units.ne_zero _)
    exact (div_le_iff₀ hy).mpr (by simpa [A] using H.rightCosetOpNorm_mul_le y (y⁻¹ * g))
  · simpa [A] using H.rightCosetOpNorm_mul_le g (g⁻¹ * y)

/-- In the isometry group of a nonsingular form, each right coset of a closed subgroup has a
representative attaining its coset norm. -/
theorem exists_norm_eq_rightCosetOpNorm (hJ : IsUnit J) (hH : IsClosed (H : Set (unitaryGroupOf J)))
    (g : unitaryGroupOf J) : ∃ h : H, ‖((h.val * g : GL n 𝕜) : Matrix n n 𝕜)‖ =
      H.rightCosetOpNorm g := by
  let A : unitaryGroupOf J → Matrix n n 𝕜 := fun t ↦ ((t : GL n 𝕜) : Matrix n n 𝕜)
  have hA : IsClosedEmbedding A := unitaryGroupOf.isClosedEmbedding_val hJ
  have : ProperSpace (Matrix n n 𝕜) := FiniteDimensional.proper_rclike 𝕜 _
  let S := A ⁻¹' Metric.closedBall 0 ‖A g‖ ∩ (fun t ↦ t * g⁻¹) ⁻¹' (H : Set (unitaryGroupOf J))
  have hS : IsCompact S := (hA.isCompact_preimage (isCompact_closedBall _ _)).inter_right
    (hH.preimage (continuous_id.mul continuous_const))
  have hgS : g ∈ S := ⟨by simp [Metric.mem_closedBall, dist_zero_right], by simp⟩
  obtain ⟨t, ht, hmin⟩ := hS.exists_isMinOn ⟨g, hgS⟩ hA.continuous.norm.continuousOn
  let h : H := ⟨t * g⁻¹, ht.2⟩
  have he : (h.val * g : GL n 𝕜) = (t : GL n 𝕜) := by simp [h]
  refine ⟨h, le_antisymm ?_ (H.rightCosetOpNorm_le g h)⟩
  rw [he, H.le_rightCosetOpNorm_iff]
  have hle {v : unitaryGroupOf J} (hv : v ∈ S) : ‖A t‖ ≤ ‖A v‖ := hmin hv
  intro u
  by_cases hu : ‖A (u.val * g)‖ ≤ ‖A g‖
  · have hmem : u.val * g ∈ S := ⟨mem_closedBall_zero_iff.mpr hu, by simp⟩
    simpa only [A, Subgroup.coe_mul] using hle hmem
  · simpa only [A, Subgroup.coe_mul] using (hle hgS).trans (le_of_not_ge hu)

end Subgroup
