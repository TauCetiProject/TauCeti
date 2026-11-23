/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.UnitInterval

/-!
# Radial contraction of a space homeomorphic to a closed ball

Let `e : M ≃ₜ closedBall (0 : Q) 1` identify a topological space `M` with the closed unit ball of
a real seminormed space. Pulling back the radial contraction `(s, v) ↦ (1 - s) • v` of the ball
along `e` gives a contraction `Homeomorph.closedBallContraction e : unitInterval × M → M` of
`M` onto the centre `e.symm 0`. At every positive time its only fixed point is the centre,
it moves the whole of `M` into the preimage of the open ball, and it does not increase the
norm `‖e x‖`. If `M` is compact, small times move every point within any given neighbourhood
of the diagonal.

For compact `M` and a continuous displacement `S : M × M → F` vanishing exactly on the
diagonal in a neighbourhood of it, as a secant of a frame on a surface does, the map
`x ↦ S (x, closedBallContraction e (s, x))` for a small `s > 0` is then a continuous function
on `M` whose only zero is the centre. The homeomorphism `e` is never differentiated.

## Main results

* `Homeomorph.closedBallContraction`: the contraction, with `continuous_closedBallContraction`,
  `closedBallContraction_zero`, `closedBallContraction_one` and
  `closedBallContraction_eq_self_iff`.
* `Homeomorph.exists_pos_forall_prodMk_closedBallContraction_mem`: on a compact space, some
  positive time moves every point within a given neighbourhood of the diagonal.
-/
public section

open Set Metric
open scoped unitInterval Topology
noncomputable section
namespace Homeomorph
variable {M Q : Type*} [TopologicalSpace M] [SeminormedAddCommGroup Q] [NormedSpace ℝ Q]
  (e : M ≃ₜ closedBall (0 : Q) 1)

/-- The radial contraction `(s, v) ↦ (1 - s) • v` of the closed unit ball, pulled back to `M`
along `e`. -/
def closedBallContraction (z : unitInterval × M) : M :=
  e.symm ⟨(1 - (z.1 : ℝ)) • (e z.2 : Q), by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr z.1.property.2)]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp (e z.2).property)
      (sub_nonneg.mpr z.1.property.2)).trans (by simp [z.1.property.1])⟩

/-- In the coordinates given by `e`, the contraction at time `s` is multiplication by `1 - s`. -/
@[simp, grind =]
theorem coe_apply_closedBallContraction (s : unitInterval) (x : M) :
    (e (e.closedBallContraction (s, x)) : Q) = (1 - (s : ℝ)) • (e x : Q) := by
  simp [closedBallContraction]

/-- The contraction is jointly continuous in time and space. -/
@[fun_prop]
theorem continuous_closedBallContraction : Continuous e.closedBallContraction := by
  apply e.symm.continuous.comp
  apply Continuous.subtype_mk
  exact (continuous_const.sub (continuous_subtypeVal.comp continuous_fst)).smul
    (continuous_subtypeVal.comp (e.continuous.comp continuous_snd))

/-- At time zero the contraction is the identity. -/
@[simp, grind =]
theorem closedBallContraction_zero (x : M) : e.closedBallContraction (0, x) = x := by
  apply e.injective
  apply Subtype.ext
  simp

/-- At time one every point has reached the centre. -/
@[simp, grind =]
theorem closedBallContraction_one (x : M) :
    e.closedBallContraction (1, x) = e.symm ⟨0, mem_closedBall_self zero_le_one⟩ := by
  apply e.injective
  apply Subtype.ext
  simp

/-- The centre is fixed at every time. -/
@[simp, grind =]
theorem closedBallContraction_symm_zero (s : unitInterval) :
    e.closedBallContraction (s, e.symm ⟨0, mem_closedBall_self zero_le_one⟩) =
      e.symm ⟨0, mem_closedBall_self zero_le_one⟩ := by
  apply e.injective
  apply Subtype.ext
  simp

/-- At positive times the centre is the only fixed point. -/
@[grind .]
theorem closedBallContraction_eq_self_iff (s : unitInterval) (x : M) :
    e.closedBallContraction (s, x) = x ↔ s = 0 ∨ (e x : Q) = 0 := by
  rw [← e.injective.eq_iff, Subtype.ext_iff, coe_apply_closedBallContraction]
  constructor
  · intro h
    have hz : (s : ℝ) • (e x : Q) = 0 := by
      have hh := congrArg (fun v : Q ↦ (e x : Q) - v) h
      simpa [sub_smul] using hh
    simpa using smul_eq_zero.mp hz
  · rintro (rfl | hx)
    · simp
    · simp [hx]

/-- The norm of the coordinates scales by exactly `1 - s`. -/
theorem norm_apply_closedBallContraction (s : unitInterval) (x : M) :
    ‖(e (e.closedBallContraction (s, x)) : Q)‖ = (1 - (s : ℝ)) * ‖(e x : Q)‖ := by
  rw [coe_apply_closedBallContraction, norm_smul,
    Real.norm_of_nonneg (sub_nonneg.mpr s.property.2)]

/-- At positive times the contraction moves all of `M` into the preimage of the open ball. -/
theorem norm_apply_closedBallContraction_lt_one {s : unitInterval} (hs : 0 < s) (x : M) :
    ‖(e (e.closedBallContraction (s, x)) : Q)‖ < 1 := by
  rw [norm_apply_closedBallContraction]
  have h := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp (e x).property)
    (sub_nonneg.mpr s.property.2)
  have hs' : 0 < (s : ℝ) := unitInterval.coe_pos.mpr hs
  nlinarith

/-- The contraction does not increase the norm of the coordinates given by `e`. -/
theorem norm_apply_closedBallContraction_le (s : unitInterval) (x : M) :
    ‖(e (e.closedBallContraction (s, x)) : Q)‖ ≤ ‖(e x : Q)‖ := by
  rw [norm_apply_closedBallContraction]
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [s.property.1])

omit [NormedSpace ℝ Q] in
/-- Every neighbourhood of the centre contains the preimage of a ball of positive radius. -/
theorem exists_pos_forall_mem_of_norm_apply_lt {V : Set M}
    (hV : V ∈ 𝓝 (e.symm ⟨0, mem_closedBall_self zero_le_one⟩)) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : M, ‖(e x : Q)‖ < r → x ∈ V := by
  have hpre := e.symm.continuous.continuousAt.preimage_mem_nhds hV
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨r, hr, fun x hx ↦ ?_⟩
  have hmem : e x ∈ Metric.ball
      (⟨0, mem_closedBall_self zero_le_one⟩ : closedBall (0 : Q) 1) r := by
    simpa only [mem_ball, Subtype.dist_eq, dist_zero_right] using hx
  simpa using hsub hmem

variable [CompactSpace M]

/-- On a compact space, for small times the contraction moves every point within a given
neighbourhood of the diagonal. -/
theorem eventually_forall_prodMk_closedBallContraction_mem {U : Set (M × M)}
    (hU : U ∈ 𝓝ˢ (diagonal M)) :
    ∀ᶠ s in 𝓝 (0 : unitInterval), ∀ x, (x, e.closedBallContraction (s, x)) ∈ U := by
  have hc : Continuous (fun z : unitInterval × M ↦ (z.2, e.closedBallContraction z)) :=
    continuous_snd.prodMk e.continuous_closedBallContraction
  simpa only [mem_univ, forall_true_left] using
    isCompact_univ.eventually_forall_of_forall_eventually
      (x₀ := (0 : unitInterval))
      (P := fun s x ↦ (x, e.closedBallContraction (s, x)) ∈ U) (fun x _ ↦ by
        have hx := mem_nhdsSet_iff_forall.mp hU (x, x) (mem_diagonal x)
        apply hc.continuousAt.preimage_mem_nhds
        simpa only [closedBallContraction_zero] using hx)

/-- On a compact space, some positive time moves every point within a given neighbourhood
of the diagonal. -/
theorem exists_pos_forall_prodMk_closedBallContraction_mem {U : Set (M × M)}
    (hU : U ∈ 𝓝ˢ (diagonal M)) :
    ∃ s : unitInterval, 0 < s ∧ ∀ x, (x, e.closedBallContraction (s, x)) ∈ U := by
  obtain ⟨s, hs, hpos⟩ := nonempty_nhds_inter_Ioi
    (e.eventually_forall_prodMk_closedBallContraction_mem hU)
    (not_isMax_of_lt (zero_lt_one' unitInterval))
  exact ⟨s, hpos, hs⟩

end Homeomorph
