/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Interpolation
public import TauCeti.Analysis.InnerProductSpace.GraphPatch

/-!
# Interpolation inequalities up to the boundary of a domain

The interpolation inequalities of `TauCeti.Analysis.Holder.Interpolation` bound the gradient and the
Hessian of a `C²` function at the centre `x` of a ball in a set `s` by the supremum `M` of the
function and the Hölder constant `H` of its Hessian on `s`. At a point of the closure of a domain
there is no such ball. It suffices, however, to have a ball `B(y, 2 ε) ⊆ s` nearby, joined to `x`
by a segment in `s` (`HolderOnWith.norm_iteratedFDeriv_two_le_of_contDiffOn_of_mem` and
`HolderOnWith.norm_fderiv_le_of_contDiffOn_of_segment_subset`), giving

`‖D²u(x)‖ ≤ 2 M / ε² + 3 H ε^α + H ‖x - y‖^α`,
`‖Du(x)‖ ≤ M / ε + H ε^(1 + α) + ‖x - y‖ (2 M / ε² + 3 H ε^α + H ‖x - y‖^α)`.

On a bounded domain whose boundary is locally the graph of a Lipschitz function, for instance a
bounded domain with `C^{2,α}` boundary, such balls exist at every point of the closure with
`‖x - y‖ ≤ κ ε` for all small `ε` (`TauCeti.exists_closedBall_subset_segment_subset_closure`). This
gives the interpolation inequalities on the closure of the domain,

`‖Du‖ ≤ C (M / ε + H ε^(1 + α))` and `‖D²u‖ ≤ C (M / ε² + H ε^α)`,

with `C` depending only on the domain. They reduce the lower-order norms on the right of a global
Schauder estimate to the supremum of the function.

## Main declarations

* `TauCeti.exists_norm_fderiv_le_and_norm_iteratedFDeriv_two_le_of_isBounded`: the interpolation
  inequalities on the closure of a bounded domain with Lipschitz graph boundary.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.8 (interpolation inequalities on domains, Lemma 6.35).
-/

public section

open Set
open scoped NNReal InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace TauCeti

/-- **Interpolation inequalities up to the boundary of a domain.** Let `Ω` be a bounded subset of a
finite-dimensional (more generally, proper) real inner product space such that near each frontier
point `x`, `ball x r ∩ Ω = ball x r ∩ {z | γ z < ⟪z, ν⟫}` for a unit vector `ν`, a radius `r > 0`
and a Lipschitz function `γ` invariant along `ν`; for instance a bounded domain with `C^{2,α}`
boundary. Then there are `C` and `ε₀ > 0` such that for every `0 < ε ≤ ε₀`, every `u` which is
`C²` on an open set `U ⊇ closure Ω` with `‖u‖ ≤ M` on `closure Ω` and `D²u` `α`-Hölder with
constant `H` on `closure Ω` satisfies, at every point of `closure Ω`,

`‖Du‖ ≤ C (M / ε + H ε^(1 + α))` and `‖D²u‖ ≤ C (M / ε² + H ε^α)`.

The constants depend only on `Ω`, through the constants of its uniform interior ball condition
(`TauCeti.exists_closedBall_subset_segment_subset_closure`), and on `α`. -/
theorem exists_norm_fderiv_le_and_norm_iteratedFDeriv_two_le_of_isBounded
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E] {Ω : Set E}
    (hbdry : ∀ x ∈ frontier Ω, ∃ (ν : E) (γ : E → ℝ) (G : ℝ≥0) (r : ℝ), ‖ν‖ = 1 ∧
      LipschitzWith G γ ∧ (∀ z (t : ℝ), γ (z + t • ν) = γ z) ∧ 0 < r ∧
      Metric.ball x r ∩ Ω = Metric.ball x r ∩ {z | γ z < ⟪z, ν⟫_ℝ})
    (hΩ : Bornology.IsBounded Ω) (α : ℝ≥0) :
    ∃ (C : ℝ≥0) (ε₀ : ℝ), 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∀ {U : Set E} {u : E → F} {M : ℝ} {H : ℝ≥0}, IsOpen U → closure Ω ⊆ U →
        ContDiffOn ℝ 2 u U → (∀ z ∈ closure Ω, ‖u z‖ ≤ M) →
        HolderOnWith H α (iteratedFDeriv ℝ 2 u) (closure Ω) → ∀ z ∈ closure Ω,
          ‖fderiv ℝ u z‖ ≤ C * (M / ε + H * ε ^ (1 + (α : ℝ))) ∧
            ‖iteratedFDeriv ℝ 2 u z‖ ≤ C * (M / ε ^ 2 + H * ε ^ (α : ℝ)) := by
  obtain ⟨κ, ε₀, hε₀, hgeo⟩ := exists_closedBall_subset_segment_subset_closure hbdry hΩ
  set k : ℝ := max κ 0
  have hk : 0 ≤ k := le_max_right _ _
  -- The constant `C = (1 + 4 k) (3 + (2 k)^α)`.
  set A : ℝ := 3 + (2 * k) ^ (α : ℝ)
  have hA : 3 ≤ A := le_add_of_nonneg_right (by positivity)
  refine ⟨((1 + 4 * k) * A).toNNReal, ε₀ / 2, half_pos hε₀,
    fun ε hε hεε₀ {U u M H} hU hΩU hu hM hH z hz => ?_⟩
  -- A closed ball of radius `2 ε` in `Ω` at distance at most `2 k ε` from `z`.
  obtain ⟨y, hy, hseg, hzy⟩ := hgeo z hz (2 * ε) (by positivity) (by linarith)
  have hys : Metric.closedBall y (2 * ε) ⊆ closure Ω := hy.trans subset_closure
  have hzy' : dist z y ≤ 2 * k * ε := hzy.trans (by nlinarith [le_max_left κ 0])
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z hz)
  have hpow : dist z y ^ (α : ℝ) ≤ (2 * k) ^ (α : ℝ) * ε ^ (α : ℝ) := by
    rw [← Real.mul_rpow (by positivity) hε.le]
    exact Real.rpow_le_rpow dist_nonneg (by linarith) α.coe_nonneg
  have hH0 : 0 ≤ (H : ℝ) * ε ^ (α : ℝ) := by positivity
  have hD2 := hH.norm_iteratedFDeriv_two_le_of_contDiffOn_of_mem hU hu hΩU hM hz hε hys
  have hD1 := hH.norm_fderiv_le_of_contDiffOn_of_segment_subset hU hu hΩU hM hseg hε hys
  rw [mul_div_assoc] at hD1 hD2
  -- The Hessian bound near `y`, moved to `z` with the Hölder bound.
  have hB : 2 * (M / ε ^ 2) + 3 * H * ε ^ (α : ℝ) + H * dist z y ^ (α : ℝ) ≤
      2 * (M / ε ^ 2) + A * (H * ε ^ (α : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hpow H.coe_nonneg
    simp only [A]
    linarith
  have hA1 : 0 ≤ A - 1 := by linarith
  rw [Real.coe_toNNReal _ (by positivity)]
  constructor
  · -- Along the segment, of length at most `2 k ε`, the gradient changes by at most
    -- `4 k M / ε + 2 k A H ε^(1 + α)`.
    have hε1 : ε ^ (1 + (α : ℝ)) = ε * ε ^ (α : ℝ) := by
      rw [Real.rpow_add' hε.le (by positivity), Real.rpow_one]
    have hP : 0 ≤ M / ε := by positivity
    have hQ : 0 ≤ (H : ℝ) * (ε * ε ^ (α : ℝ)) := by positivity
    have hdB := mul_le_mul hzy' hB (by positivity) (by positivity)
    have hk2 : 2 * k * ε * (2 * (M / ε ^ 2) + A * (H * ε ^ (α : ℝ))) =
        4 * k * (M / ε) + 2 * k * A * (H * (ε * ε ^ (α : ℝ))) := by
      field_simp
      ring
    rw [hε1] at hD1 ⊢
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + 4 * k) hA1) hP,
      mul_nonneg (add_nonneg hA1 (mul_nonneg (mul_nonneg zero_le_two hk) (by linarith : 0 ≤ A)))
        hQ]
  · have hCA : A ≤ (1 + 4 * k) * A := le_mul_of_one_le_left (by linarith) (by linarith)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (1 + 4 * k) * A - 2)
      (by positivity : (0 : ℝ) ≤ M / ε ^ 2), mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * k * A) hH0]

end TauCeti
