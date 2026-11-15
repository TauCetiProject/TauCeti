/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Exterior cones at the boundary of a Lipschitz domain

Let `Ω` be a subset of a real inner product space `E` with a Lipschitz boundary chart centred at a
frontier point `ξ`: in the coordinates of an affine isometry `E ≃ WithLp 2 (ℝ × G)` sending `ξ` to
the origin, `Ω` is the region above the graph of a `K`-Lipschitz function inside a cylinder. Every
point below the downward cone `{(s, y) | s ≤ -K ‖y‖}` lies outside `Ω` near the origin. So `Ω`
satisfies the **exterior cone condition** at `ξ`: a truncated closed cone with vertex `ξ`, axis
the downward normal of the chart and half-aperture `arccos c` for some `c < 1` depending only on
`K`, misses `Ω`. This is the geometric input for the regularity of the boundary points of a
Lipschitz domain in the Dirichlet problem for harmonic functions.

## Main declarations

* `Set.IsLipschitzChart.exists_inner_sub_lt_mul_norm_sub`: a Lipschitz chart centred at a
  frontier point gives an exterior cone there.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 2.8 (the exterior cone condition).
-/

public section

namespace Set.IsLipschitzChart

open InnerProductSpace Metric TauCeti
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] {Ω : Set E} {ξ : E}

/-- **A Lipschitz chart gives an exterior cone.** If `Ω` has a Lipschitz boundary chart centred at
the frontier point `ξ`, then a truncated closed cone with vertex `ξ`, pointing below the graph,
misses `Ω`: there are a unit vector `v`, a number `c < 1` and a radius `ρ > 0` with
`⟪v, x - ξ⟫ < c ‖x - ξ‖` for every `x ∈ Ω` with `‖x - ξ‖ < ρ`. -/
theorem exists_inner_sub_lt_mul_norm_sub
    {e : E ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × G)} {γ : G → ℝ} {K : NNReal} {h r : ℝ}
    (hc : Ω.IsLipschitzChart e γ K h r) (hξ : ξ ∈ frontier Ω) (heξ : e ξ = 0) :
    ∃ v : E, ‖v‖ = 1 ∧ ∃ c < 1, ∃ ρ > 0, ∀ x ∈ Ω, dist x ξ < ρ → ⟪v, x - ξ⟫_ℝ < c * ‖x - ξ‖ := by
  set ℓ := e.linearIsometryEquiv
  have hℓ : ∀ x, ℓ (x - ξ) = e x := fun x ↦ by simpa [heξ] using e.map_vsub x ξ
  -- The graph passes through the centre of the chart.
  have hγ0 : γ 0 = 0 := by
    have := hc.fst_apply_eq_of_mem_frontier hξ
      (heξ ▸ zero_mem_normalCylinder hc.height_pos hc.radius_pos)
    simpa [heξ] using this.symm
  -- The axis `v` is the downward normal direction `(-1, 0)` of the chart.
  set v := ℓ.symm (WithLp.toLp 2 ((-1 : ℝ), (0 : G)))
  have hv : ‖v‖ = 1 := by
    rw [ℓ.symm.norm_map, WithLp.prod_norm_eq_of_L2]
    simp
  set c : ℝ := 1 - 1 / (2 * (1 + (K : ℝ) ^ 2))
  have hK2 : 0 < 1 + (K : ℝ) ^ 2 := by positivity
  have hc0 : 0 < c := by
    simp only [c]
    rw [sub_pos, div_lt_one (by positivity)]
    nlinarith
  -- `c² (1 + K²) ≥ K²`: the cone of aperture `arccos c` about the downward axis lies inside the
  -- downward cone of slope `K`.
  have hcK : (K : ℝ) ^ 2 ≤ c ^ 2 * (1 + (K : ℝ) ^ 2) := by
    simp only [c]
    field_simp
    nlinarith [sq_nonneg (K : ℝ)]
  have hδ : 0 < 1 / (2 * (1 + (K : ℝ) ^ 2)) := by positivity
  refine ⟨v, hv, c, by simp only [c]; linarith, min h r, lt_min hc.height_pos hc.radius_pos,
    fun x hx hxξ ↦ ?_⟩
  set z := e x
  have hz : ℓ (x - ξ) = z := hℓ x
  have hnz : ‖z‖ = ‖x - ξ‖ := by rw [← hz, ℓ.norm_map]
  have hz2 := WithLp.prod_norm_sq_eq_of_L2 z
  rw [Real.norm_eq_abs, sq_abs] at hz2
  have hzlt : ‖z‖ < min h r := by rwa [hnz, ← dist_eq_norm]
  have hfst : |z.fst| < h := by
    rw [← Real.norm_eq_abs]
    exact ((WithLp.norm_fst_le (x := z)).trans_lt hzlt).trans_le (min_le_left h r)
  have hsnd : ‖z.snd‖ < r :=
    ((WithLp.norm_snd_le (x := z)).trans_lt hzlt).trans_le (min_le_right h r)
  -- In the chart, `x ∈ Ω` lies above the graph, hence above the downward cone of slope `K`.
  have hmem : γ z.snd < z.fst :=
    (hc.mem_iff (by simp only [mem_normalCylinder]; exact ⟨(abs_lt.1 hfst).1,
      (abs_lt.1 hfst).2, hsnd⟩)).1 hx
  have hlip : -(K * ‖z.snd‖) ≤ γ z.snd := by
    have := hc.lipschitzWith.dist_le_mul z.snd 0
    rw [Real.dist_eq, hγ0, sub_zero, dist_zero_right] at this
    linarith [neg_abs_le (γ z.snd)]
  have hinner : ⟪v, x - ξ⟫_ℝ = -z.fst := by
    rw [← ℓ.inner_map_map, hz, LinearIsometryEquiv.apply_symm_apply,
      WithLp.prod_inner_apply]
    simp
  rw [hinner, ← hnz]
  -- Square the inequality `-z.fst < c ‖z‖` when its left side is nonnegative.
  rcases lt_or_ge 0 z.fst with hpos | hneg
  · linarith [mul_nonneg hc0.le (norm_nonneg z)]
  · have ha : 0 ≤ -z.fst := by linarith
    have hlt : -z.fst < K * ‖z.snd‖ := by linarith
    have hsq : (-z.fst) ^ 2 < (c * ‖z‖) ^ 2 := by
      have h1 : (-z.fst) ^ 2 < (K : ℝ) ^ 2 * ‖z.snd‖ ^ 2 := by
        rw [← mul_pow]
        exact pow_lt_pow_left₀ hlt ha two_ne_zero
      nlinarith
    exact (pow_lt_pow_iff_left₀ ha (by positivity) two_ne_zero).1 hsq

end Set.IsLipschitzChart
