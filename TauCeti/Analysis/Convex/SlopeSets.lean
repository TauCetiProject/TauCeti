/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.MetricSpace.HausdorffDistance

import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Slopes of affine functions that are nonpositive on a set

For a point `x₀` and a height `a ≤ 0`, the admissible slopes on a set `s` are the vectors `p` with
`a + ⟪x - x₀, p⟫ ≤ 0` for all `x ∈ s`, that is, those for which the affine function through
`(x₀, a)` with slope `p` is nonpositive on `s`. This file shows that the admissible slopes on a set
form a convex set, that for `s` inside the closure of a bounded set `Ω` containing `x₀` every slope
of norm below `-a / diam Ω` is admissible, and that for an open convex set `Ω` with a point of the
complement and `s ⊆ closure Ω` there is an admissible slope of norm `-a / dist (x₀, Ωᶜ)`.

## Main results

* `TauCeti.convex_setOf_forall_add_inner_le`: the slopes which are nonpositive on a set form a
  convex set.
* `TauCeti.ball_subset_setOf_forall_add_inner_le`: a ball of admissible slopes.
* `TauCeti.exists_mem_setOf_forall_add_inner_le_dist_eq`: an admissible slope of norm
  `-a / dist (x₀, Ωᶜ)`.
-/

public section

namespace TauCeti

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {Ω s : Set E} {a : ℝ} {x₀ : E}

/-- The set of slopes `p` with `a + ⟪x - x₀, p⟫ ≤ 0` for all `x` in a set `s` is convex. -/
theorem convex_setOf_forall_add_inner_le (s : Set E) (a : ℝ) (x₀ : E) :
    Convex ℝ {p : E | ∀ x ∈ s, a + inner ℝ (x - x₀) p ≤ 0} := by
  have : {p : E | ∀ x ∈ s, a + inner ℝ (x - x₀) p ≤ 0} =
      ⋂ x ∈ s, {p : E | inner ℝ (x - x₀) p ≤ -a} := by
    ext p
    simp [le_neg_iff_add_nonpos_left]
  rw [this]
  exact convex_iInter₂ fun x _ ↦ convex_halfSpace_le (innerₛₗ ℝ (x - x₀)).isLinear _

/-- For a bounded set `Ω` containing `x₀`, a set `s ⊆ closure Ω` and a height `a`, every slope of
norm below `-a / diam Ω` makes the affine function through `(x₀, a)` nonpositive on `s`. -/
theorem ball_subset_setOf_forall_add_inner_le (hΩ : Bornology.IsBounded Ω) (hx₀ : x₀ ∈ Ω)
    (hs : s ⊆ closure Ω) :
    ball (0 : E) (-a / diam Ω) ⊆ {p : E | ∀ x ∈ s, a + inner ℝ (x - x₀) p ≤ 0} := by
  rcases (diam_nonneg (s := Ω)).eq_or_lt with hD | hD
  · rw [← hD, div_zero, ball_eq_empty.2 le_rfl]
    exact empty_subset _
  intro p hp x hx
  rw [mem_ball_zero_iff] at hp
  have hxD : ‖x - x₀‖ ≤ diam Ω := by
    rw [← dist_eq_norm]
    calc dist x x₀ ≤ diam (closure Ω) :=
          dist_le_diam_of_mem hΩ.closure (hs hx) (subset_closure hx₀)
      _ = diam Ω := diam_closure Ω
  have := (real_inner_le_norm (x - x₀) p).trans
    (mul_le_mul hxD hp.le (norm_nonneg p) hD.le)
  rw [mul_div_cancel₀ _ hD.ne'] at this
  linarith

/-- If `Ω` is open and convex with `x₀ ∈ Ω`, the complement of `Ω` is nonempty, `s ⊆ closure Ω` and
`a ≤ 0`, there is a slope `q` of norm `-a / dist(x₀, Ωᶜ)` with `a + ⟪x - x₀, q⟫ ≤ 0` on `s`. -/
theorem exists_mem_setOf_forall_add_inner_le_dist_eq [FiniteDimensional ℝ E]
    (hΩo : IsOpen Ω) (hconv : Convex ℝ Ω) (hx₀ : x₀ ∈ Ω) (hs : s ⊆ closure Ω) (hh : 0 ≤ -a)
    (hΩc : Ωᶜ.Nonempty) :
    ∃ q ∈ {p : E | ∀ x ∈ s, a + inner ℝ (x - x₀) p ≤ 0},
      dist q 0 = -a / infDist x₀ Ωᶜ := by
  set h := -a
  set d := infDist x₀ Ωᶜ
  have hd : 0 < d := (hΩo.isClosed_compl.notMem_iff_infDist_pos hΩc).1 fun h' => h' hx₀
  obtain ⟨z, hz, hzd⟩ := hΩo.isClosed_compl.exists_infDist_eq_dist hΩc x₀
  obtain ⟨g, hg⟩ := geometric_hahn_banach_open_point hconv hΩo hz
  set w := (InnerProductSpace.toDual ℝ E).symm g
  have hw : ∀ a, inner ℝ w a = g a := fun a => InnerProductSpace.toDual_symm_apply
  have hw0 : w ≠ 0 := fun h' => by simpa [← hw, h'] using hg x₀ hx₀
  have hw0' : 0 < ‖w‖ := norm_pos_iff.2 hw0
  refine ⟨(h / (d * ‖w‖)) • w, fun x hx => ?_, ?_⟩
  · have hgx : g x ≤ g z :=
      closure_minimal (fun a ha => (hg a ha).le) (isClosed_le g.continuous continuous_const)
        (hs hx)
    have hdz : d = ‖z - x₀‖ := by
      rw [dist_comm, dist_eq_norm] at hzd
      exact hzd
    have hgz : g (z - x₀) ≤ ‖w‖ * d := by
      rw [← hw, hdz]
      exact real_inner_le_norm w (z - x₀)
    rw [map_sub] at hgz
    have key : h / (d * ‖w‖) * (g x - g x₀) ≤ h :=
      calc h / (d * ‖w‖) * (g x - g x₀) ≤ h / (d * ‖w‖) * (‖w‖ * d) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = h := by field_simp
    rw [real_inner_smul_right, real_inner_comm, hw, map_sub]
    linarith
  · rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity)]
    field_simp

end TauCeti
