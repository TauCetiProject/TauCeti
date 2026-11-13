/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.QuadraticReaction

/-!
# The scalar curvature lower bound for three-dimensional Ricci flow

Under a Ricci flow `∂ₜg = -2 Ric` on a closed three-manifold, the scalar curvature evolves by
`∂ₜR = ΔR + 2|Ric|²`, and `|Ric|² ≥ R² / 3`. So at every spatial minimum `∂ₜR ≥ (2/3) R²`. For
normalized initial metrics `R ≥ -6` at time zero, and the quadratic-reaction comparison
`TauCeti.div_one_sub_mul_le_of_mul_sq_le_deriv_of_isLocalMin` with `c = 2/3` and `ρ = -6`
propagates this to `R ≥ -6 / (1 + 4t)`. The comparison restarts at any nonnegative time `a`: the
bound `R ≥ -6 / (1 + 4a)` at time `a` propagates to the same bound `-6 / (1 + 4t)` at later times,
which is the form needed on each smooth epoch of a Ricci flow with surgery.

This is a scalar statement about a function satisfying the differential inequality at spatial
local minima: no existence of a geometric flow or evolution equation is asserted here.

## Main results

* `TauCeti.neg_six_div_one_add_four_mul_le_of_mul_sq_le_deriv_of_isLocalMin`: the
  three-dimensional scalar curvature bound `-6 / (1 + 4t)` on a time interval `[a, b]`.
* `TauCeti.neg_six_div_one_add_four_mul_le_of_mul_sq_le_deriv_of_isLocalMin_of_neg_six_le`: the
  same bound from normalized initial data `-6 ≤ u` at time zero.

## References

* J. W. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Clay Mathematics
  Monographs 3 (2007), Chapter 4 (the maximum principle and the scalar curvature lower bound
  for normalized initial metrics).
-/

public section

namespace TauCeti

open Set

variable {X : Type*} [TopologicalSpace X] {u : ℝ → X → ℝ}

/-- **The scalar curvature lower bound in dimension three, restarted at time `a`.**

On a compact space `X`, let `0 ≤ a` and let `u` be continuous on `[a, b] × X` and differentiable
in time, with `∂ₜu ≥ (2/3) u²` at every spatial local minimum lying below the bound. If
`u ≥ -6 / (1 + 4a)` at time `a`, then `u ≥ -6 / (1 + 4t)` for every `t ∈ [a, b]`. This is the
form used on each smooth epoch of a Ricci flow with surgery. -/
theorem neg_six_div_one_add_four_mul_le_of_mul_sq_le_deriv_of_isLocalMin [CompactSpace X]
    {a b : ℝ} (ha : 0 ≤ a) (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ univ))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, IsLocalMin (u t) x →
      u t x < -6 / (1 + 4 * t) → 2 / 3 * u t x ^ 2 ≤ deriv (fun s ↦ u s x) t)
    (hinit : ∀ x, -6 / (1 + 4 * a) ≤ u a x) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ x, -6 / (1 + 4 * t) ≤ u t x := by
  intro t ht x
  -- Shift `[a, b]` to `[0, b - a]` and apply the comparison with `ρ = -6 / (1 + 4a)`.
  have ha' : 0 < 1 + 4 * a := by linarith
  have hden (s : ℝ) : 1 - 2 / 3 * (-6 / (1 + 4 * a)) * s = (1 + 4 * (a + s)) / (1 + 4 * a) := by
    field_simp
    ring
  have hbar (s : ℝ) :
      -6 / (1 + 4 * a) / (1 - 2 / 3 * (-6 / (1 + 4 * a)) * s) = -6 / (1 + 4 * (a + s)) := by
    rw [hden, div_div_div_cancel_right₀ ha'.ne']
  have hcont' : ContinuousOn (Function.uncurry fun s y ↦ u (a + s) y) (Icc 0 (b - a) ×ˢ univ) :=
    hcont.comp (f := fun p : ℝ × X ↦ (a + p.1, p.2)) (by fun_prop) fun p hp ↦
      ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, mem_univ _⟩
  have h := div_one_sub_mul_le_of_mul_sq_le_deriv_of_isLocalMin (u := fun s y ↦ u (a + s) y)
    (c := 2 / 3) (by norm_num) (by rw [hden]; exact div_pos (by linarith [ht.1, ht.2]) ha') hcont'
    (fun s hs y ↦ ((hdiff ⟨by linarith [hs.1], by linarith [hs.2]⟩ y).hasDerivAt.comp_const_add
      a s).differentiableAt)
    (fun s hs y hmin hlt ↦ by
      rw [deriv_comp_const_add (fun r ↦ u r y)]
      exact hloc ⟨by linarith [hs.1], by linarith [hs.2]⟩ y hmin (by rwa [hbar] at hlt))
    (fun y ↦ by simpa using hinit y) (t := t - a) ⟨by linarith [ht.1], by linarith [ht.2]⟩ x
  rwa [hbar, add_sub_cancel] at h

/-- **The scalar curvature lower bound in dimension three.**

On a compact space `X`, let `u` be continuous on `[0, T] × X` and differentiable in time, with
`∂ₜu ≥ (2/3) u²` at every spatial local minimum lying below the bound. If `u ≥ -6` at time zero,
then `u ≥ -6 / (1 + 4t)` for every `t ∈ [0, T]`. For the scalar curvature of a Ricci flow on a
closed three-manifold, `-6` is the lower bound for normalized initial metrics. -/
theorem neg_six_div_one_add_four_mul_le_of_mul_sq_le_deriv_of_isLocalMin_of_neg_six_le
    [CompactSpace X] {T : ℝ} (hcont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, IsLocalMin (u t) x →
      u t x < -6 / (1 + 4 * t) → 2 / 3 * u t x ^ 2 ≤ deriv (fun s ↦ u s x) t)
    (hinit : ∀ x, -6 ≤ u 0 x) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ x, -6 / (1 + 4 * t) ≤ u t x :=
  neg_six_div_one_add_four_mul_le_of_mul_sq_le_deriv_of_isLocalMin le_rfl hcont hdiff hloc
    (fun x ↦ by simpa using hinit x)

end TauCeti
