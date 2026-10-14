/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Topology.Bases

/-!
# The ultrametric inequality for quotients and differences

In an ultrametric seminormed group, `‖x / y‖ ≤ max ‖x‖ ‖y‖`; additively,
`‖x - y‖ ≤ max ‖x‖ ‖y‖`, and likewise for `‖·‖₊`. These are the companions of Mathlib's
`IsUltrametricDist.norm_mul_le_max` and `IsUltrametricDist.norm_add_le_max`. Consequently, if
`‖x - y‖ < ‖x‖` then `‖x‖ = ‖y‖`: an element and a strictly smaller perturbation of it have the
same norm.

A separable ultrametric additive group with a strictly decreasing sequence of norms `‖cₙ‖`
bounded away from `0` is not spherically complete: there are decreasing closed balls of radii
`‖cₙ‖` with empty intersection (`IsUltrametricDist.exists_antitone_closedBall_iInter_eq_empty`).
Enumerate a dense sequence `xₙ` and choose the `(n + 1)`-st ball to avoid `xₙ`, keeping the centre
when it is already far from `xₙ` and moving it by `cₙ` otherwise. A common point `b` of the balls
would have all of them containing the ball of radius `inf ‖cₙ‖ > 0` about `b`, hence some `xₙ`.
For `ℂ_p` this is the classical construction of a decreasing sequence of discs without a common
point; see A. M. Robert, *A Course in p-adic Analysis*, Graduate Texts in Mathematics 198,
Springer, 2000, Chapter 3.
-/

public section

namespace IsUltrametricDist

variable {S : Type*} [SeminormedGroup S] [IsUltrametricDist S]

/-- The ultrametric inequality for a quotient: `‖x / y‖ ≤ max ‖x‖ ‖y‖`. -/
@[to_additive /-- The ultrametric inequality for a difference: `‖x - y‖ ≤ max ‖x‖ ‖y‖`. -/]
theorem norm_div_le_max (x y : S) : ‖x / y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [div_eq_mul_inv] using norm_mul_le_max x y⁻¹

/-- The ultrametric inequality for a quotient: `‖x / y‖₊ ≤ max ‖x‖₊ ‖y‖₊`. -/
@[to_additive /-- The ultrametric inequality for a difference: `‖x - y‖₊ ≤ max ‖x‖₊ ‖y‖₊`. -/]
theorem nnnorm_div_le_max (x y : S) : ‖x / y‖₊ ≤ max ‖x‖₊ ‖y‖₊ := by
  simpa [div_eq_mul_inv] using nnnorm_mul_le_max x y⁻¹

/-- In an ultrametric group, if `‖x / y‖ < ‖x‖` then `x` and `y` have the same norm. -/
@[to_additive /-- In an ultrametric additive group, if `‖x - y‖ < ‖x‖` then `x` and `y` have the
same norm. -/]
theorem norm_eq_of_norm_div_lt_left {x y : S} (h : ‖x / y‖ < ‖x‖) : ‖x‖ = ‖y‖ := by
  have h' := norm_eq_of_mul_norm_lt_max (x := x) (y := y⁻¹)
    ((div_eq_mul_inv x y ▸ h).trans_le (le_max_left _ _))
  rwa [norm_inv'] at h'

section SphericalCompleteness

open Metric

variable {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E]

/-- **A separable ultrametric group is not spherically complete** once its norms take a strictly
decreasing sequence of values `‖cₙ‖` bounded below by some `ρ > 0`: there are decreasing closed
balls of radii `‖cₙ‖`, starting at any centre `a₀`, with empty intersection. -/
theorem exists_antitone_closedBall_iInter_eq_empty [TopologicalSpace.SeparableSpace E]
    {c : ℕ → E} (hc : StrictAnti fun n ↦ ‖c n‖) {ρ : ℝ} (hρ : 0 < ρ) (hcρ : ∀ n, ρ ≤ ‖c n‖)
    (a₀ : E) :
    ∃ a : ℕ → E, a 0 = a₀ ∧ Antitone (fun n ↦ closedBall (a n) ‖c n‖) ∧
      ⋂ n, closedBall (a n) ‖c n‖ = ∅ := by
  obtain ⟨x, hx⟩ := TopologicalSpace.exists_dense_seq E
  -- the next centre stays at `b` if `b` is far from `xₙ`, and moves by `cₙ` otherwise
  let step (n : ℕ) (b : E) : E := if ‖c (n + 1)‖ < ‖b - x n‖ then b else b + c n
  have hstep (n : ℕ) (b : E) :
      ‖step n b - b‖ ≤ ‖c n‖ ∧ ‖c (n + 1)‖ < ‖step n b - x n‖ := by
    by_cases h : ‖c (n + 1)‖ < ‖b - x n‖
    · simp [step, h]
    · have hlt : ‖b - x n‖ < ‖c n‖ := (not_lt.mp h).trans_lt (hc n.lt_succ_self)
      simp only [step, h, ite_false, add_sub_cancel_left, le_rfl, true_and]
      rw [show b + c n - x n = c n + (b - x n) by abel, norm_add_eq_max_of_norm_ne_norm hlt.ne',
        max_eq_left hlt.le]
      exact hc n.lt_succ_self
  let a (n : ℕ) : E := Nat.rec a₀ step n
  have hsucc (n : ℕ) : a (n + 1) = step n (a n) := rfl
  refine ⟨a, rfl, antitone_nat_of_succ_le fun n ↦ ?_, Set.eq_empty_of_forall_notMem fun b hb ↦ ?_⟩
  · -- the `(n + 1)`-st centre lies in the `n`-th ball, which it therefore also centres
    have hmem : a (n + 1) ∈ closedBall (a n) ‖c n‖ := by
      rw [mem_closedBall, dist_eq_norm, hsucc]
      exact (hstep n (a n)).1
    rw [closedBall_eq_of_mem hmem]
    exact closedBall_subset_closedBall (hc n.lt_succ_self).le
  · -- a common point `b` is close to some `xₘ`, which then lies in the `(m + 1)`-st ball
    rw [Set.mem_iInter] at hb
    obtain ⟨m, hm⟩ := Metric.denseRange_iff.mp hx b ρ hρ
    have hle : dist (x m) (a (m + 1)) ≤ ‖c (m + 1)‖ :=
      (dist_triangle_max _ b _).trans <| max_le (by rw [dist_comm]; exact hm.le.trans (hcρ _))
        (mem_closedBall.mp (hb (m + 1)))
    have hfar := (hstep m (a m)).2
    rw [← hsucc, ← dist_eq_norm, dist_comm] at hfar
    exact hfar.not_ge hle

end SphericalCompleteness

end IsUltrametricDist
