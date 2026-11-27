/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.VacuumDecay

/-!
# Zero localization at every threshold from the decay of the vacuum defect

In the large-parameter analysis of the Seiberg–Witten equations on a symplectic four-manifold, a
solution at parameter `r` has normalized spinor `χ = α u₀ + β`, and `Z` denotes the zero set of
`α`. The natural length scale is `h = (2 r)^(-1/2)`. Taubes's zero localization says that for every
threshold `σ < 1` there is a constant `K` such that, once `r` is large, every point with
`|α|² ≤ σ` lies within distance `K / √r` of `Z`.

Rescaled compactness only gives a weak form of this: a lower bound `|α|² ≥ θ`, for one fixed
`θ > 0`, at every point at distance at least `ρ / √r` from `Z`. This file upgrades such a lower
bound, in a flat chart, to localization at every threshold `σ < 1`, uniformly in the solution. The
mechanism is the exponential decay of the vacuum defect on balls where `|α|² ≥ θ`
(`TauCeti.SeibergWitten.one_sub_sq_le_div_add_mul_exp`).

* **The off-zero bound.** If the open ball of radius `R ≥ 2 ρ / √r` about `x` misses `Z`, every
  point of the concentric ball of radius `R / 2` is at distance at least `ρ / √r` from `Z`, so
  `|α|² ≥ θ` there, and the decay estimate on that ball gives

  `1 - |α(x)|² ≤ 1216 C² / (θ³ r) + 2 log θ⁻¹ e^{2n/3} exp (-√(θ r) R / 8)`

  (`TauCeti.SeibergWitten.one_sub_sq_le_div_add_mul_exp_of_forall_le_dist`). With
  `h = (2 r)^(-1/2)` the exponential is `exp (-c R / h)` for `c = √θ / (8 √2)`: this is the
  off-zero bound taken as a hypothesis in `TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.Localization`,
  for radii at least `2 √2 ρ h` of balls on which the analytic hypotheses hold, even without the
  term `(C / r) w₊`.
* **Localization.** For every `σ < 1` there are `K > 0` and `r₀ ≥ 1`, depending only on `C`, `θ`,
  `ρ`, `σ` and the dimension of the chart, such that for `r ≥ r₀` every point `x` with
  `|α(x)|² ≤ σ` lies within distance `K / √r` of `Z`, provided the analytic hypotheses hold on the
  ball of radius `K / √r` about `x`
  (`TauCeti.SeibergWitten.exists_forall_exists_dist_le_div_sqrt_of_sq_le`). The choice
  `σ = 1 / 2` covers the support of the cutoff current.

The analytic inputs are those of `TauCeti.SeibergWitten.one_sub_sq_le_div_add_mul_exp`: the
projected Weitzenböck equation for `α`, the gradient inequality for `|α|²` and Taubes's coarse
bounds, stated for functions `a`, `b`, `da`, `db`, `q` standing for `|α|`, `|β|`, `|∇_a α|`,
`|∇β|`, `|∂bar_a α|`, together with the lower bound on `|α|²` away from `Z`. The set `Z` is
arbitrary: the statements use only distances to it. The lower bound itself, which comes from
rescaled compactness and the classification of zero-free flat limits, is not proved here, and the
estimates are stated in a flat chart.

## Main results

* `TauCeti.SeibergWitten.one_sub_sq_le_div_add_mul_exp_of_forall_le_dist`: the off-zero bound
  from a lower bound on `|α|²` away from `Z`.
* `TauCeti.SeibergWitten.exists_forall_exists_dist_le_div_sqrt_of_sq_le`: localization of
  `{|α|² ≤ σ}` within distance `K / √r` of `Z`, for every `σ < 1`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Proposition 4.4.
-/

public section

open InnerProductSpace Laplacian Metric
open scoped Gradient

namespace TauCeti.SeibergWitten

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E]

/-- **The off-zero bound from a lower bound away from the zeros.** Consider functions `a`, `b`,
`da`, `db`, `q` on a finite-dimensional real inner product space, standing for `|α|`, `|β|`,
`|∇_a α|`, `|∇β|`, `|∂bar_a α|` of a solution of Taubes's large-parameter Seiberg–Witten equations
at parameter `r ≥ 1`, and a set `Z` (the zero set of `α`). Let `0 < θ ≤ 1` and `C ≥ 1`, and
suppose that on the open ball of radius `R > 0` about `x`:

* `|α|²` is of class `C²`, and the projected Weitzenböck equation, the gradient inequality at
  `ε = θ / (8 C)` and Taubes's coarse bounds hold, as in
  `TauCeti.SeibergWitten.one_sub_sq_le_div_add_mul_exp`;
* `|α|² ≥ θ` at every point at distance at least `ρ` from `Z`.

If `2 ρ ≤ R` and the ball misses `Z`, then

`1 - |α(x)|² ≤ 1216 C² / (θ³ r) + 2 log θ⁻¹ e^{2n/3} exp (-√(θ r) R / 8)`,  `n = dim E`. -/
theorem one_sub_sq_le_div_add_mul_exp_of_forall_le_dist {a b da db q : E → ℝ} {Z : Set E} {x : E}
    {r R ρ C θ : ℝ} (hr : 1 ≤ r) (hR : 0 < R) (hρ : 2 * ρ ≤ R) (hC : 1 ≤ C) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hZ : ∀ z ∈ Z, R ≤ dist x z)
    (hlow : ∀ y ∈ ball x R, (∀ z ∈ Z, ρ ≤ dist y z) → θ ≤ a y ^ 2)
    (hcd : ∀ y ∈ ball x R, ContDiffAt ℝ 2 (fun y ↦ a y ^ 2) y)
    (hW : ∀ y ∈ ball x R, -(C * a y * (db y + a y + b y)) ≤
      -Δ (fun y ↦ a y ^ 2) y / 2 + da y ^ 2 + r / 4 * (a y ^ 2 + b y ^ 2 - 1) * a y ^ 2)
    (hG : ∀ y ∈ ball x R, 2 * a y ^ 2 * ((1 - θ / (8 * C)) * da y ^ 2 -
      (2 + 18 / (θ / (8 * C))) * q y ^ 2) ≤ ‖∇ (fun y ↦ a y ^ 2) y‖ ^ 2)
    (hβ : ∀ y ∈ ball x R, b y ^ 2 ≤ C / r * max (1 - a y ^ 2) 0 + C / r ^ 2)
    (hgrad : ∀ y ∈ ball x R, da y ^ 2 + r * db y ^ 2 ≤ C * r * max (1 - a y ^ 2) 0 + C)
    (hup : ∀ y ∈ ball x R, a y ^ 2 ≤ 1 + C / r) (hq : ∀ y ∈ ball x R, q y ^ 2 ≤ C) :
    1 - a x ^ 2 ≤ 1216 * C ^ 2 / (θ ^ 3 * r) +
      2 * Real.log θ⁻¹ * Real.exp (2 * Module.finrank ℝ E / 3) *
        Real.exp (-(√(θ * r) * R / 8)) := by
  -- The decay estimate is applied on the closed ball of radius `R / 2`, inside the open ball.
  have hsub : closedBall x (R / 2) ⊆ ball x R := closedBall_subset_ball (by linarith)
  have hsub' : ball x (R / 2) ⊆ ball x R := ball_subset_ball (by linarith)
  -- Every point of the smaller ball is at distance at least `R / 2 ≥ ρ` from `Z`.
  have hθa : ∀ y ∈ closedBall x (R / 2), θ ≤ a y ^ 2 := by
    refine fun y hy ↦ hlow y (hsub hy) fun z hz ↦ ?_
    have := dist_triangle_left x z y
    rw [mem_closedBall] at hy
    linarith [hZ z hz]
  have hdecay := one_sub_sq_le_div_add_mul_exp (z := x) (R := R / 2) hr (by linarith) hC hθ hθ1
    (fun y hy ↦ (hcd y (hsub hy)).continuousAt.continuousWithinAt)
    (fun y hy ↦ hcd y (hsub' hy)) hθa (fun y hy ↦ hW y (hsub' hy)) (fun y hy ↦ hG y (hsub' hy))
    (fun y hy ↦ hβ y (hsub' hy)) (fun y hy ↦ hgrad y (hsub' hy)) (fun y hy ↦ hup y (hsub' hy))
    (fun y hy ↦ hq y (hsub' hy))
  rwa [show √(θ * r) * (R / 2) / 4 = √(θ * r) * R / 8 by ring] at hdecay

/-- The constants of the localization: if `θ > 0` and `η > 0`, then for `K` and `r`
large enough the bound of `TauCeti.SeibergWitten.one_sub_sq_le_div_add_mul_exp_of_forall_le_dist`
at radius `K / √r` is below `η`. -/
private theorem exists_div_add_mul_exp_lt {C θ η B : ℝ} (hθ : 0 < θ) (hη : 0 < η)
    (ρ : ℝ) :
    ∃ K r₀ : ℝ, 0 < K ∧ 2 * ρ ≤ K ∧ 1 ≤ r₀ ∧ ∀ r, r₀ ≤ r →
      1216 * C ^ 2 / (θ ^ 3 * r) + B * Real.exp (-(√(θ * r) * (K / √r) / 8)) < η := by
  set A := 1216 * C ^ 2 / θ ^ 3 with hA
  refine ⟨max (max (2 * ρ) 1) (8 * Real.log (2 * B / η) / √θ), max 1 (4 * A / η),
    lt_of_lt_of_le one_pos ((le_max_right _ _).trans (le_max_left _ _)),
    (le_max_left _ _).trans (le_max_left _ _), le_max_left _ _, fun r hr ↦ ?_⟩
  set K := max (max (2 * ρ) 1) (8 * Real.log (2 * B / η) / √θ) with hK
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hr0 : 0 < r := one_pos.trans_le hr1
  -- The first term is at most `η / 4`.
  have h₁ : 1216 * C ^ 2 / (θ ^ 3 * r) ≤ η / 4 := by
    have hAr : 4 * A / η ≤ r := (le_max_right _ _).trans hr
    rw [div_le_iff₀ hη] at hAr
    rw [show 1216 * C ^ 2 / (θ ^ 3 * r) = A / r by rw [hA, div_div], div_le_iff₀ hr0]
    linarith
  -- The radius `K / √r` turns the exponent into `-√θ K / 8`, independent of `r`.
  have hexp : √(θ * r) * (K / √r) / 8 = √θ * K / 8 := by
    rw [Real.sqrt_mul hθ.le]
    field_simp
  rw [hexp]
  -- The second term is at most `η / 2`, because `K ≥ 8 log (2 B / η) / √θ`.
  have h₂ : B * Real.exp (-(√θ * K / 8)) ≤ η / 2 := by
    rcases le_or_gt B 0 with hB | hB
    · exact (mul_nonpos_of_nonpos_of_nonneg hB (Real.exp_pos _).le).trans (by positivity)
    have hlog : Real.log (2 * B / η) ≤ √θ * K / 8 := by
      have := le_max_right (max (2 * ρ) 1) (8 * Real.log (2 * B / η) / √θ)
      rw [← hK, div_le_iff₀ (Real.sqrt_pos.2 hθ)] at this
      linarith
    calc B * Real.exp (-(√θ * K / 8)) ≤ B * Real.exp (-Real.log (2 * B / η)) := by gcongr
      _ = η / 2 := by
        rw [Real.exp_neg, Real.exp_log (by positivity)]
        field_simp
  linarith

/-- **Zero localization at every threshold.** Let `C ≥ 1`, `0 < θ ≤ 1`, `ρ` real and `σ < 1`.
There are constants `K > 0` and `r₀ ≥ 1`, depending only on `C`, `θ`, `ρ`, `σ` and `E`, with the
following property. Consider functions `a`, `b`, `da`, `db`, `q` standing for `|α|`, `|β|`,
`|∇_a α|`, `|∇β|`, `|∂bar_a α|` of a solution of Taubes's large-parameter Seiberg–Witten equations
at parameter `r ≥ r₀`, a set `Z` (the zero set of `α`) and a point `x` such that on the open ball
of radius `K / √r` about `x`:

* `|α|²` is of class `C²`, and the projected Weitzenböck equation, the gradient inequality at
  `ε = θ / (8 C)` and Taubes's coarse bounds hold, as in
  `TauCeti.SeibergWitten.one_sub_sq_le_div_add_mul_exp`;
* `|α|² ≥ θ` at every point at distance at least `ρ / √r` from `Z`.

If `|α(x)|² ≤ σ`, then `x` lies within distance `K / √r` of a point of `Z`. -/
theorem exists_forall_exists_dist_le_div_sqrt_of_sq_le (C θ ρ : ℝ) (hC : 1 ≤ C) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) {σ : ℝ} (hσ : σ < 1) :
    ∃ K r₀ : ℝ, 0 < K ∧ 1 ≤ r₀ ∧ ∀ {a b da db q : E → ℝ} {Z : Set E} {x : E} {r : ℝ}, r₀ ≤ r →
      (∀ y ∈ ball x (K / √r), (∀ z ∈ Z, ρ / √r ≤ dist y z) → θ ≤ a y ^ 2) →
      (∀ y ∈ ball x (K / √r), ContDiffAt ℝ 2 (fun y ↦ a y ^ 2) y) →
      (∀ y ∈ ball x (K / √r), -(C * a y * (db y + a y + b y)) ≤
        -Δ (fun y ↦ a y ^ 2) y / 2 + da y ^ 2 + r / 4 * (a y ^ 2 + b y ^ 2 - 1) * a y ^ 2) →
      (∀ y ∈ ball x (K / √r), 2 * a y ^ 2 * ((1 - θ / (8 * C)) * da y ^ 2 -
        (2 + 18 / (θ / (8 * C))) * q y ^ 2) ≤ ‖∇ (fun y ↦ a y ^ 2) y‖ ^ 2) →
      (∀ y ∈ ball x (K / √r), b y ^ 2 ≤ C / r * max (1 - a y ^ 2) 0 + C / r ^ 2) →
      (∀ y ∈ ball x (K / √r), da y ^ 2 + r * db y ^ 2 ≤ C * r * max (1 - a y ^ 2) 0 + C) →
      (∀ y ∈ ball x (K / √r), a y ^ 2 ≤ 1 + C / r) →
      (∀ y ∈ ball x (K / √r), q y ^ 2 ≤ C) →
      a x ^ 2 ≤ σ → ∃ z ∈ Z, dist x z ≤ K / √r := by
  obtain ⟨K, r₀, hK, hρK, hr₀, hlt⟩ := exists_div_add_mul_exp_lt
    (B := 2 * Real.log θ⁻¹ * Real.exp (2 * Module.finrank ℝ E / 3)) (C := C) hθ (sub_pos.2 hσ) ρ
  refine ⟨K, r₀, hK, hr₀, fun {a b da db q Z x r} hr hlow hcd hW hG hβ hgrad hup hq hσx ↦ ?_⟩
  -- Otherwise the ball of radius `K / √r` misses `Z`, and the off-zero bound at that radius
  -- forces `1 - |α(x)|² < 1 - σ`.
  by_contra! hfar
  have hr1 : 1 ≤ r := hr₀.trans hr
  have hsr : 0 < √r := Real.sqrt_pos.2 (one_pos.trans_le hr1)
  have hbound := one_sub_sq_le_div_add_mul_exp_of_forall_le_dist hr1 (div_pos hK hsr)
    (by rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hρK hsr.le) hC hθ hθ1
    (fun z hz ↦ (hfar z hz).le) hlow hcd hW hG hβ hgrad hup hq
  linarith [hlt r hr]

end TauCeti.SeibergWitten
