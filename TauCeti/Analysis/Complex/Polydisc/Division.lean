/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# Bounds after division in one coordinate of a polydisc

The maximum modulus principle applied to a coordinate slice propagates a bound from the face
`‖z i‖ = R` to the whole closed polydisc. Consequently, removing factors
`∏ ζ ∈ S, (z i - ζ) ^ m` whose roots lie in a smaller disc gives a bound for the analytic
cofactor. On the smaller polydisc this gives a quantitative bound for the original function.
These estimates are useful when successively dividing an analytic function by its coordinate
zeros in interpolation arguments.

The special case of a power of a coordinate retains the sharper ratio `r / R`, rather than
the ratio `2 * r / (R - r)` needed for arbitrary roots in the smaller disc.

The argument uses Mathlib's `Complex.norm_le_of_forall_mem_frontier_norm_le` on each slice.
-/

public section

open Finset Function Metric

namespace TauCeti

variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℂ F]
  {f g : (ι → ℂ) → F} {R r M : ℝ}

/-- A bound on the face where one coordinate has modulus `R` holds on the whole closed
polydisc for a function analytic on a neighbourhood of that polydisc. -/
theorem norm_le_of_forall_norm_coord_eq (i : ι)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hM : ∀ z ∈ closedBall 0 R, ‖z i‖ = R → ‖f z‖ ≤ M)
    {z : ι → ℂ} (hz : z ∈ closedBall 0 R) : ‖f z‖ ≤ M := by
  classical
  have hzR : ‖z‖ ≤ R := by simpa using hz
  have hR : 0 ≤ R := (norm_nonneg z).trans hzR
  rcases hR.eq_or_lt with hR | hR
  · apply hM z hz
    exact le_antisymm ((norm_le_pi_norm z i).trans hzR) (hR ▸ norm_nonneg _)
  have hmem {w : ℂ} (hw : w ∈ closedBall 0 R) : update z i w ∈ closedBall 0 R := by
    rw [closedBall_pi _ hR.le] at hz ⊢
    exact (Set.update_mem_pi_iff_of_mem hz).2 fun _ => by simpa using hw
  have hd : DifferentiableOn ℂ (fun w => f (update z i w)) (closedBall 0 R) := by
    intro w hw
    exact ((hf _ (hmem hw)).differentiableAt.comp w
      (hasFDerivAt_update z w).differentiableAt).differentiableWithinAt
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    (hd.diffContOnCl_ball Set.Subset.rfl) (C := M)
  have hzi : z i ∈ closure (ball (0 : ℂ) R) := by
    rw [closure_ball _ hR.ne']
    simpa using (norm_le_pi_norm z i).trans hzR
  simpa using hmax (fun w hw => by
    rw [frontier_ball _ hR.ne'] at hw
    exact hM _ (hmem (sphere_subset_closedBall hw)) (by simpa using hw)) hzi

/-- Removing powers of one-coordinate linear factors, with roots of modulus at most `r < R`,
bounds the analytic cofactor by `M / (R - r) ^ (m * S.card)` on the large polydisc. -/
theorem norm_le_of_eq_prod_smul (i : ι) (S : Finset ℂ) (m : ℕ)
    (hrR : r < R) (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hS : ∀ ζ ∈ S, ‖ζ‖ ≤ r)
    (hfg : ∀ z ∈ closedBall 0 R, f z = (∏ ζ ∈ S, (z i - ζ) ^ m) • g z)
    (hf : ∀ z ∈ closedBall 0 R, ‖f z‖ ≤ M)
    {z : ι → ℂ} (hz : z ∈ closedBall 0 R) :
    ‖g z‖ ≤ M / (R - r) ^ (m * S.card) := by
  refine norm_le_of_forall_norm_coord_eq i hg (fun w hw hwi => ?_) hz
  have hprod : (R - r) ^ (m * S.card) ≤ ‖∏ ζ ∈ S, (w i - ζ) ^ m‖ := by
    have hc : (R - r) ^ (m * S.card) = ∏ _ζ ∈ S, (R - r) ^ m := by
      simp [pow_mul]
    rw [norm_prod, hc]
    refine prod_le_prod₀ (fun _ _ => by positivity) fun ζ hζ => ?_
    rw [norm_pow]
    gcongr
    exact (sub_le_sub_left (hS ζ hζ) R).trans (hwi ▸ norm_sub_norm_le _ _)
  apply (le_div_iff₀ (pow_pos (sub_pos.mpr hrR) (m * S.card))).2
  calc
    ‖g w‖ * (R - r) ^ (m * S.card) ≤ ‖g w‖ * ‖∏ ζ ∈ S, (w i - ζ) ^ m‖ := by
      gcongr
    _ = ‖f w‖ := by rw [hfg w hw, norm_smul, mul_comm]
    _ ≤ M := hf w hw

/-- If one-coordinate factors have roots in the disc of radius `r < R`, their product times an
analytic cofactor is bounded on the small polydisc by `M * (2 * r / (R - r)) ^ (m * S.card)`,
where `M` bounds the product on the large polydisc. -/
theorem norm_le_mul_pow_of_eq_prod_smul (i : ι) (S : Finset ℂ) (m : ℕ)
    (hr : 0 ≤ r) (hrR : r < R) (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hS : ∀ ζ ∈ S, ‖ζ‖ ≤ r)
    (hfg : ∀ z ∈ closedBall 0 R, f z = (∏ ζ ∈ S, (z i - ζ) ^ m) • g z)
    (hf : ∀ z ∈ closedBall 0 R, ‖f z‖ ≤ M)
    {z : ι → ℂ} (hz : z ∈ closedBall 0 r) :
    ‖f z‖ ≤ M * (2 * r / (R - r)) ^ (m * S.card) := by
  have hzR := closedBall_subset_closedBall hrR.le hz
  have hgz := norm_le_of_eq_prod_smul i S m hrR hg hS hfg hf hzR
  have hprod : ‖∏ ζ ∈ S, (z i - ζ) ^ m‖ ≤ (2 * r) ^ (m * S.card) := by
    have hc : (2 * r) ^ (m * S.card) = ∏ _ζ ∈ S, (2 * r) ^ m := by
      simp [pow_mul]
    rw [norm_prod, hc]
    refine prod_le_prod₀ (fun _ _ => norm_nonneg _) fun ζ hζ => ?_
    rw [norm_pow]
    gcongr
    calc
      ‖z i - ζ‖ ≤ ‖z i‖ + ‖ζ‖ := norm_sub_le _ _
      _ ≤ r + r := add_le_add ((norm_le_pi_norm z i).trans (by simpa using hz)) (hS ζ hζ)
      _ = 2 * r := by ring
  rw [hfg z hzR, norm_smul]
  calc
    _ ≤ (2 * r) ^ (m * S.card) * (M / (R - r) ^ (m * S.card)) :=
      mul_le_mul hprod hgz (norm_nonneg _) (by positivity)
    _ = M * (2 * r / (R - r)) ^ (m * S.card) := by rw [div_pow]; ring

/-- Dividing by a pure power of one coordinate bounds the analytic cofactor by `M / R ^ m`
on the entire large polydisc. -/
theorem norm_le_of_eq_pow_smul (i : ι) (m : ℕ) (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hfg : ∀ z ∈ closedBall 0 R, f z = z i ^ m • g z)
    (hf : ∀ z ∈ closedBall 0 R, ‖f z‖ ≤ M)
    {z : ι → ℂ} (hz : z ∈ closedBall 0 R) : ‖g z‖ ≤ M / R ^ m := by
  simpa using norm_le_of_eq_prod_smul i {0} m hR hg (by simp)
    (by simpa using hfg) hf hz

/-- For a pure coordinate power the small-polydisc bound has the sharp ratio `r / R`.
The two radii may be equal. -/
theorem norm_le_mul_pow_of_eq_pow_smul (i : ι) (m : ℕ) (hr : 0 ≤ r) (hrR : r ≤ R)
    (hR : 0 < R) (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hfg : ∀ z ∈ closedBall 0 R, f z = z i ^ m • g z)
    (hf : ∀ z ∈ closedBall 0 R, ‖f z‖ ≤ M)
    {z : ι → ℂ} (hz : z ∈ closedBall 0 r) : ‖f z‖ ≤ M * (r / R) ^ m := by
  have hzR := closedBall_subset_closedBall hrR hz
  have hgz := norm_le_of_eq_pow_smul i m hR hg hfg hf hzR
  rw [hfg z hzR, norm_smul, norm_pow]
  calc
    ‖z i‖ ^ m * ‖g z‖ ≤ r ^ m * (M / R ^ m) := by
      apply mul_le_mul _ hgz (norm_nonneg _) (by positivity)
      gcongr
      exact (norm_le_pi_norm z i).trans (by simpa using hz)
    _ = M * (r / R) ^ m := by rw [div_pow]; ring

end TauCeti
