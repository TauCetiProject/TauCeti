/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# The derivative of the distance to a set

In a proper real normed space, the distance `x ↦ infDist x s` to a nonempty set `s` is
`1`-Lipschitz, so its derivative has norm at most one wherever it exists. Away from the closure
of `s` the norm is exactly one (`TauCeti.norm_fderiv_infDist_eq_one`): moving from `x` straight
towards a nearest point of the closure decreases the distance at unit speed. Combined with
Rademacher's theorem, this says that the distance function solves the eikonal equation
`‖D (infDist · s)‖ = 1` almost everywhere off the closure of `s`. This is the identity that turns
the coarea formula for the distance function into a formula for the volume of parallel sets.
-/

public section

open Metric Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- **The distance to a set solves the eikonal equation.** In a proper real normed space, at
every point `x` off the closure of a nonempty set `s` where the distance function
`infDist · s` is differentiable, its derivative has norm one. -/
theorem norm_fderiv_infDist_eq_one {s : Set E} (hs : s.Nonempty) {x : E} (hx : x ∉ closure s)
    (hd : DifferentiableAt ℝ (infDist · s) x) : ‖fderiv ℝ (infDist · s) x‖ = 1 := by
  obtain ⟨p, hpc, hp⟩ := exists_mem_closure_infDist_eq_dist hs x
  have hpos : 0 < infDist x s :=
    infDist_nonneg.lt_of_ne' fun h => hx ((mem_closure_iff_infDist_zero hs).2 h)
  set d := infDist x s
  have hv : ‖p - x‖ = d := by rw [hp, dist_comm, dist_eq_norm]
  -- On the segment from `x` to a nearest point `p`, the distance decreases at unit speed.
  have hline : ∀ t ∈ Icc (0 : ℝ) 1, infDist (x + t • (p - x)) s = d - t * d := by
    intro t ht
    have hdist : dist (x + t • (p - x)) p = (1 - t) * d := by
      rw [dist_eq_norm, show x + t • (p - x) - p = (1 - t) • (x - p) by module, norm_smul,
        Real.norm_of_nonneg (sub_nonneg.2 ht.2), ← dist_eq_norm, ← hp]
    have hdist' : dist x (x + t • (p - x)) = t * d := by
      rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg ht.1, hv]
    refine le_antisymm ?_ ?_
    · calc infDist (x + t • (p - x)) s ≤ dist (x + t • (p - x)) p := by
            rw [← infDist_closure]; exact infDist_le_dist_of_mem hpc
        _ = d - t * d := by rw [hdist]; ring
    · linarith [infDist_le_infDist_add_dist (x := x) (y := x + t • (p - x)) (s := s)]
  have hmem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hderiv : HasDerivWithinAt (fun t : ℝ => infDist (x + t • (p - x)) s)
      (fderiv ℝ (infDist · s) x (p - x)) (Icc 0 1) 0 := by
    have hlin : HasDerivAt (fun t : ℝ => x + t • (p - x)) (p - x) 0 := by
      simpa only [one_smul] using
        HasDerivAt.const_add x ((hasDerivAt_id' (0 : ℝ)).smul_const (p - x))
    exact (hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hlin (by simp)).hasDerivWithinAt
  have haff : HasDerivWithinAt (fun t : ℝ => infDist (x + t • (p - x)) s) (-d) (Icc 0 1) 0 := by
    have h : HasDerivAt (fun t : ℝ => d - t * d) (-d) 0 := by
      simpa only [one_mul] using HasDerivAt.const_sub d ((hasDerivAt_id' (0 : ℝ)).mul_const d)
    exact h.hasDerivWithinAt.congr hline (hline 0 hmem)
  have heq : fderiv ℝ (infDist · s) x (p - x) = -d :=
    (uniqueDiffOn_Icc_zero_one 0 hmem).eq_deriv _ hderiv haff
  refine le_antisymm ?_ ?_
  · simpa using norm_fderiv_le_of_lipschitz ℝ (lipschitz_infDist_pt (s := s)) (x₀ := x)
  · have hop := (fderiv ℝ (infDist · s) x).le_opNorm (p - x)
    rw [heq, norm_neg, Real.norm_of_nonneg hpos.le, hv] at hop
    exact le_of_mul_le_mul_right (by rwa [one_mul]) hpos

end TauCeti
