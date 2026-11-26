/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cauchy estimates for divided differences

Let `a` be inside the disc of radius `R` about `c`. On the boundary, division by `z - a`
costs at most the reciprocal of `R - dist a c`, the distance from `a` to the circle.
This gives a Cauchy estimate for the derivatives of the holomorphic divided difference
`dslope f a` at `c`.

For a Laplace transform written as the divided difference of a holomorphic function at `1`,
one takes `c = 1 + H` and `R = H + η`. The normalized Taylor coefficient then gains a factor
`(H / (H + η)) ^ (k + 1)`, bounded by `exp (-(k + 1) * η / (H + η))`.
For `0 < η ≤ H`, the prefactor `2 * M * R / η` is at most `4 * M * H / η`, and the
exponential is at most `exp (-(k + 1) * η / (2 * H))`. These are the bounds used in the
rate form of the Tauberian argument.

## Main results

* `Complex.norm_iteratedDeriv_dslope_le_of_forall_mem_sphere` uses the boundary oscillation
  about the value at the anchor.
* `Complex.norm_scaled_taylorCoeff_dslope_le` uses a bound on the boundary values of the original
  function and gives the geometric gain.
* `Complex.norm_scaled_taylorCoeff_dslope_le_exp` gives its exponential form.
-/

@[expose] public section

open Filter Metric Set

namespace Complex

/-- Cauchy's estimate for a divided difference, with the boundary oscillation measured relative
to the value at an interior anchor. -/
theorem norm_iteratedDeriv_dslope_le_of_forall_mem_sphere {f : ℂ → ℂ} {a c : ℂ} {R B : ℝ}
    (ha : a ∈ ball c R) (hf : DiffContOnCl ℂ f (ball c R))
    (hB : ∀ z ∈ sphere c R, ‖f z - f a‖ ≤ B) (k : ℕ) :
    ‖iteratedDeriv k (dslope f a) c‖ ≤ k.factorial * (B / (R - dist a c)) / R ^ k := by
  have haR : dist a c < R := mem_ball.mp ha
  have hR : 0 < R := dist_nonneg.trans_lt haR
  have hnbhd := isOpen_ball.mem_nhds ha
  have hg : DiffContOnCl ℂ (dslope f a) (ball c R) :=
    ⟨(differentiableOn_dslope hnbhd).2 hf.differentiableOn,
      (continuousOn_dslope (mem_of_superset hnbhd subset_closure)).2
        ⟨hf.continuousOn, hf.differentiableOn.differentiableAt hnbhd⟩⟩
  refine norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR hg fun z hz ↦ ?_
  have hgap : R - dist a c ≤ ‖z - a‖ := by
    linarith [dist_triangle z a c, mem_sphere.mp hz, dist_eq_norm z a]
  rw [le_div_iff₀ (sub_pos.mpr haR)]
  calc
    ‖dslope f a z‖ * (R - dist a c) ≤ ‖z - a‖ * ‖dslope f a z‖ :=
      (mul_le_mul_of_nonneg_left hgap (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = ‖f z - f a‖ := by rw [← norm_smul, sub_smul_dslope]
    _ ≤ B := hB z hz

/-- Multiply the Taylor coefficient of the divided difference by `(c - a) ^ (k + 1)`.
The resulting bound has a geometric factor in `dist a c / R`. The maximum modulus principle
supplies the bound at the anchor from the same bound on the circle. -/
theorem norm_scaled_taylorCoeff_dslope_le {f : ℂ → ℂ} {a c : ℂ} {R M : ℝ}
    (ha : a ∈ ball c R) (hf : DiffContOnCl ℂ f (ball c R))
    (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (k : ℕ) :
    ‖(c - a) ^ (k + 1) / k.factorial * iteratedDeriv k (dslope f a) c‖ ≤
      (2 * M * R / (R - dist a c)) * (dist a c / R) ^ (k + 1) := by
  have hgap : 0 < R - dist a c := sub_pos.mpr (mem_ball.mp ha)
  have hR : 0 < R := dist_nonneg.trans_lt (mem_ball.mp ha)
  have hfa : ‖f a‖ ≤ M := norm_le_of_forall_mem_frontier_norm_le isBounded_ball hf
    (fun z hz ↦ hM z (frontier_ball_subset_sphere hz)) (subset_closure ha)
  have hB (z : ℂ) (hz : z ∈ sphere c R) : ‖f z - f a‖ ≤ 2 * M := by
    calc
      ‖f z - f a‖ ≤ ‖f z‖ + ‖f a‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith [hM z hz]
  rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast, ← dist_eq_norm, dist_comm c a]
  calc
    _ ≤ dist a c ^ (k + 1) / k.factorial *
        (k.factorial * (2 * M / (R - dist a c)) / R ^ k) :=
      mul_le_mul_of_nonneg_left (norm_iteratedDeriv_dslope_le_of_forall_mem_sphere ha hf hB k)
        (by positivity)
    _ = _ := by
      rw [div_pow, pow_succ R]
      field_simp [hR.ne', hgap.ne']

/-- Exponential form of the bound for the scaled Taylor coefficient. The decay is controlled by
the ratio of the gap `R - dist a c` to the radius. -/
theorem norm_scaled_taylorCoeff_dslope_le_exp {f : ℂ → ℂ} {a c : ℂ} {R M : ℝ}
    (ha : a ∈ ball c R) (hf : DiffContOnCl ℂ f (ball c R))
    (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (k : ℕ) :
    ‖(c - a) ^ (k + 1) / k.factorial * iteratedDeriv k (dslope f a) c‖ ≤
      (2 * M * R / (R - dist a c)) *
        Real.exp (-(k + 1) * ((R - dist a c) / R)) := by
  have haR : dist a c < R := mem_ball.mp ha
  have hR : 0 < R := dist_nonneg.trans_lt haR
  have hM₀ : 0 ≤ M := by
    have hz : c + (R : ℂ) ∈ sphere c R := by
      simp [mem_sphere_iff_norm, abs_of_nonneg hR.le]
    exact (norm_nonneg _).trans (hM _ hz)
  have hratio : dist a c / R ≤ Real.exp (-((R - dist a c) / R)) := by
    rw [show dist a c / R = 1 - (R - dist a c) / R by field_simp; ring]
    exact Real.one_sub_le_exp_neg _
  refine (norm_scaled_taylorCoeff_dslope_le ha hf hM k).trans ?_
  rw [show -(k + 1 : ℝ) * ((R - dist a c) / R) =
    (↑(k + 1) : ℝ) * (-((R - dist a c) / R)) by push_cast; ring, Real.exp_natCast_mul]
  gcongr

end Complex
