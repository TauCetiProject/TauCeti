/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.DividedDifference.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Analysis.Complex.PiBall
import TauCeti.Topology.MetricSpace.Pseudo.Pi

/-!
# Polydisc supremum bounds for coordinate divided differences

For any function `f : (ι → ℂ) → E` complex differentiable on a closed polydisc `closedBall c R`
(with no completeness assumption on `E`), applying Hahn–Banach and the one-variable maximum
modulus principle along the `i`-th coordinate bounds `TauCeti.partialDslope i ζ f` by
`2 * M / (R - r)` on `closedBall c R` whenever `ζ ∈ closedBall (c i) r` with `r < R` and `f` is
bounded by `M` on `closedBall c R` (`TauCeti.norm_partialDslope_le`).

## References

* [M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer, 2000]:
  §4.3, proof of Lemma 4.8, Step 2, pp. 124–125.
-/

public section

open Function Metric Set

namespace TauCeti

/-- **Polydisc maximum modulus bound for `partialDslope`.** If `f : (ι → ℂ) → E` is complex
differentiable and bounded by `M` on `closedBall c R`, and `ζ ∈ closedBall (c i) r` with `r < R`,
then `‖partialDslope i ζ f z‖ ≤ 2 * M / (R - r)` for every `z ∈ closedBall c R`. -/
theorem norm_partialDslope_le {ι E : Type*} [DecidableEq ι] [Fintype ι] [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : (ι → ℂ) → E} {c : ι → ℂ} {r R M : ℝ} {i : ι} {ζ : ℂ}
    (hf : DifferentiableOn ℂ f (closedBall c R)) (hζ : ζ ∈ closedBall (c i) r)
    (hrR : r < R) (hM : ∀ w ∈ closedBall c R, ‖f w‖ ≤ M) {z : ι → ℂ} (hz : z ∈ closedBall c R) :
    ‖partialDslope i ζ f z‖ ≤ 2 * M / (R - r) := by
  have hr : 0 ≤ r := dist_nonneg.trans (mem_closedBall.mp hζ)
  have hR : 0 < R := hr.trans_lt hrR
  have hRr : 0 < R - r := sub_pos.mpr hrR
  have hζ_ball : ζ ∈ ball (c i) R := mem_ball.mpr ((mem_closedBall.mp hζ).trans_lt hrR)
  have hζM : ‖f (update z i ζ)‖ ≤ M :=
    norm_update_le (closedBall_subset_closedBall hrR.le hζ) hM hz
  set h : ℂ → E := fun u ↦ f (update z i u)
  have hh_diff : DifferentiableOn ℂ h (closedBall (c i) R) :=
    hf.comp (fun u _ ↦ (hasFDerivAt_update z u).differentiableAt.differentiableWithinAt)
      fun u hu ↦ update_mem_closedBall hu hz
  have hh_at : DifferentiableAt ℂ h ζ :=
    (hh_diff.mono ball_subset_closedBall).differentiableAt (isOpen_ball.mem_nhds hζ_ball)
  obtain ⟨φ, hφ_norm, hφ_val⟩ := exists_dual_vector'' ℂ (partialDslope i ζ f z)
  set g : ℂ → ℂ := dslope (φ ∘ h) ζ
  have hg_diff : DifferentiableOn ℂ g (ball (c i) R) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds hζ_ball)).mpr
      (φ.differentiable.comp_differentiableOn (hh_diff.mono ball_subset_closedBall))
  have hg_cont : ContinuousOn g (closure (ball (c i) R)) := by
    rw [closure_ball (c i) hR.ne', continuousOn_dslope (closedBall_mem_nhds_of_mem hζ_ball)]
    exact ⟨φ.continuous.comp_continuousOn hh_diff.continuousOn, φ.differentiableAt.comp ζ hh_at⟩
  have hg_fr (u : ℂ) (hu : u ∈ frontier (ball (c i) R)) : ‖g u‖ ≤ 2 * M / (R - r) := by
    rw [frontier_ball (c i) hR.ne'] at hu
    have huR : ‖u - c i‖ = R := by simpa [dist_eq_norm] using mem_sphere.mp hu
    have hζr : ‖ζ - c i‖ ≤ r := by simpa [dist_eq_norm] using mem_closedBall.mp hζ
    have huζ : R - r ≤ ‖u - ζ‖ := by linarith [norm_sub_le_norm_sub_add_norm_sub u ζ (c i)]
    have hfuM : ‖f (update z i u)‖ ≤ M := norm_update_le (sphere_subset_closedBall hu) hM hz
    rw [le_div_iff₀ hRr, mul_comm]
    calc (R - r) * ‖g u‖
        ≤ ‖u - ζ‖ * ‖g u‖ := mul_le_mul_of_nonneg_right huζ (norm_nonneg _)
      _ = ‖(u - ζ) • g u‖ := (norm_smul (u - ζ) (g u)).symm
      _ = ‖φ (h u - h ζ)‖ := by
          rw [sub_smul_dslope, Function.comp_apply, Function.comp_apply, ← map_sub]
      _ ≤ ‖φ‖ * ‖h u - h ζ‖ := φ.le_opNorm _
      _ ≤ 1 * (‖h u‖ + ‖h ζ‖) :=
          mul_le_mul hφ_norm (norm_sub_le _ _) (norm_nonneg _) zero_le_one
      _ ≤ 2 * M := by linarith
  have hzi : z i ∈ closure (ball (c i) R) := by
    rw [closure_ball (c i) hR.ne']
    exact mem_closedBall.mpr ((dist_le_pi_dist z c i).trans (mem_closedBall.mp hz))
  have hgz := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball ⟨hg_diff, hg_cont⟩
    hg_fr hzi
  have hφ_eq : g (z i) = (‖partialDslope i ζ f z‖ : ℂ) :=
    (φ.dslope_comp h ζ (z i) fun _ ↦ hh_at).trans (by dsimp only [h]; rwa [← partialDslope_apply])
  simpa [hφ_eq] using hgz

end TauCeti
