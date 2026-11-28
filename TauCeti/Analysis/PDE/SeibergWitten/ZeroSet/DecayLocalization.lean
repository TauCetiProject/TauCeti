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
rescaled compactness and the classification of zero-free flat limits, is not proved here.

**In a chart of a curved metric.** On a closed four-manifold the estimates are read in charts,
where the Laplace–Beltrami operator of the metric `g` is the operator in non-divergence form
`L = ∑ᵢⱼ Aⁱʲ ∂ᵢ∂ⱼ + ∂_v`, with `A = g⁻¹` and drift `v = -gⁱʲ Γᵏᵢⱼ`. Under `0 ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` and
`‖v‖ ≤ B`, the decay estimate of the vacuum defect in a chart
(`TauCeti.SeibergWitten.one_sub_sq_le_div_add_exp_mul_mul_exp`) gives the same two statements:

* the off-zero bound
  `1 - |α(x)|² ≤ 1216 C² / (θ³ r) + e^{n/8} log θ⁻¹ exp (-θ r R / (16 (√(θ r) √Λ + B)))`
  (`TauCeti.SeibergWitten.one_sub_sq_le_div_add_exp_mul_mul_exp_of_forall_le_dist`);
* localization at every threshold `σ < 1`, in the namespace `TauCeti.SeibergWitten`
  (`exists_forall_exists_dist_le_div_sqrt_of_sq_le_of_sum_mul_fderiv_fderiv_add_fderiv`).
  At radius `K / √r` and `r ≥ 1` the rate of the off-zero bound is at least
  `θ K / (16 (√θ √Λ + B))`, so `K` and `r₀` depend on the metric only through `Λ` and `B`, and are
  uniform over the charts of a compact family of metrics.

## Main results

* `TauCeti.SeibergWitten.one_sub_sq_le_div_add_mul_exp_of_forall_le_dist`: the off-zero bound
  from a lower bound on `|α|²` away from `Z`.
* `TauCeti.SeibergWitten.exists_forall_exists_dist_le_div_sqrt_of_sq_le`: localization of
  `{|α|² ≤ σ}` within distance `K / √r` of `Z`, for every `σ < 1`.
* `TauCeti.SeibergWitten.one_sub_sq_le_div_add_exp_mul_mul_exp_of_forall_le_dist` and, in the
  same namespace,
  `exists_forall_exists_dist_le_div_sqrt_of_sq_le_of_sum_mul_fderiv_fderiv_add_fderiv`: the same
  two statements in a chart of a curved metric.

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

/-- The constants of the localization: if `η > 0` and `κ > 0`, then for `K` and `r` large enough
`1216 C² / (θ³ r) + B exp (-κ K) < η`. The rate `κ` is that of the off-zero bound at radius
`K / √r`: `√θ / 8` in a flat chart and `θ / (16 (√θ √Λ + B))` in a chart of a curved metric. -/
private theorem exists_div_add_mul_exp_lt {C θ η B κ : ℝ} (hη : 0 < η) (hκ : 0 < κ) (ρ : ℝ) :
    ∃ K r₀ : ℝ, 0 < K ∧ 2 * ρ ≤ K ∧ 1 ≤ r₀ ∧ ∀ r, r₀ ≤ r →
      1216 * C ^ 2 / (θ ^ 3 * r) + B * Real.exp (-(κ * K)) < η := by
  set A := 1216 * C ^ 2 / θ ^ 3 with hA
  refine ⟨max (max (2 * ρ) 1) (Real.log (2 * B / η) / κ), max 1 (4 * A / η),
    lt_of_lt_of_le one_pos ((le_max_right _ _).trans (le_max_left _ _)),
    (le_max_left _ _).trans (le_max_left _ _), le_max_left _ _, fun r hr ↦ ?_⟩
  set K := max (max (2 * ρ) 1) (Real.log (2 * B / η) / κ) with hK
  have hr0 : 0 < r := one_pos.trans_le ((le_max_left _ _).trans hr)
  -- The first term is at most `η / 4`.
  have h₁ : 1216 * C ^ 2 / (θ ^ 3 * r) ≤ η / 4 := by
    have hAr : 4 * A / η ≤ r := (le_max_right _ _).trans hr
    rw [div_le_iff₀ hη] at hAr
    rw [show 1216 * C ^ 2 / (θ ^ 3 * r) = A / r by rw [hA, div_div], div_le_iff₀ hr0]
    linarith
  -- The second term is at most `η / 2`, because `K ≥ log (2 B / η) / κ`.
  have h₂ : B * Real.exp (-(κ * K)) ≤ η / 2 := by
    rcases le_or_gt B 0 with hB | hB
    · exact (mul_nonpos_of_nonpos_of_nonneg hB (Real.exp_pos _).le).trans (by positivity)
    have hlog : Real.log (2 * B / η) ≤ κ * K := by
      have := le_max_right (max (2 * ρ) 1) (Real.log (2 * B / η) / κ)
      rw [← hK, div_le_iff₀ hκ] at this
      linarith
    calc B * Real.exp (-(κ * K)) ≤ B * Real.exp (-Real.log (2 * B / η)) := by gcongr
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
    (B := 2 * Real.log θ⁻¹ * Real.exp (2 * Module.finrank ℝ E / 3)) (C := C) (θ := θ)
    (sub_pos.2 hσ) (div_pos (Real.sqrt_pos.2 hθ) (by norm_num : (0 : ℝ) < 8)) ρ
  refine ⟨K, r₀, hK, hr₀, fun {a b da db q Z x r} hr hlow hcd hW hG hβ hgrad hup hq hσx ↦ ?_⟩
  -- Otherwise the ball of radius `K / √r` misses `Z`, and the off-zero bound at that radius
  -- forces `1 - |α(x)|² < 1 - σ`.
  by_contra! hfar
  have hr1 : 1 ≤ r := hr₀.trans hr
  have hsr : 0 < √r := Real.sqrt_pos.2 (one_pos.trans_le hr1)
  have hbound := one_sub_sq_le_div_add_mul_exp_of_forall_le_dist hr1 (div_pos hK hsr)
    (by rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hρK hsr.le) hC hθ hθ1
    (fun z hz ↦ (hfar z hz).le) hlow hcd hW hG hβ hgrad hup hq
  -- At radius `K / √r` the exponent is `√θ K / 8`, independent of `r`.
  rw [show √(θ * r) * (K / √r) / 8 = √θ / 8 * K by rw [Real.sqrt_mul hθ.le]; field_simp]
    at hbound
  linarith [hlt r hr]

/-! ### In a chart of a curved metric -/

section Chart

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The off-zero bound in a chart of a curved metric.** On `ℝⁿ = EuclideanSpace ℝ ι`, let
`L = ∑ᵢⱼ Aⁱʲ ∂ᵢ∂ⱼ + ∂_v` be an operator in non-divergence form, such as the Laplace–Beltrami
operator of a metric `g` written in a chart, with `A = g⁻¹` and `v` the drift `-gⁱʲ Γᵏᵢⱼ`.
Consider functions `a`, `b`, `da`, `db`, `q`, standing for `|α|`, `|β|`, `|∇_a α|`, `|∇β|`,
`|∂bar_a α|` of a solution of Taubes's large-parameter Seiberg–Witten equations at parameter
`r ≥ 1`, and a set `Z` (the zero set of `α`). Let `0 < θ ≤ 1` and `C ≥ 1`, and suppose that on
the open ball of radius `R > 0` about `x`:

* `0 ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` and `‖v‖ ≤ B`;
* `|α|²` is of class `C²`, and the projected Weitzenböck equation written with `L`, the gradient
  inequality in the metric `g` at `ε = θ / (8 C)` and Taubes's coarse bounds hold, as in
  `TauCeti.SeibergWitten.one_sub_sq_le_div_add_exp_mul_mul_exp`;
* `|α|² ≥ θ` at every point at distance at least `ρ` from `Z`.

If `2 ρ ≤ R` and the ball misses `Z`, then

`1 - |α(x)|² ≤ 1216 C² / (θ³ r) + e^{n/8} log θ⁻¹ exp (-θ r R / (16 (√(θ r) √Λ + B)))`,
`n = card ι`. -/
theorem one_sub_sq_le_div_add_exp_mul_mul_exp_of_forall_le_dist
    {A : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {a b da db q : EuclideanSpace ℝ ι → ℝ} {Z : Set (EuclideanSpace ℝ ι)}
    {x : EuclideanSpace ℝ ι} {r R ρ C θ Λ B : ℝ} (hr : 1 ≤ r) (hR : 0 < R) (hρ : 2 * ρ ≤ R)
    (hC : 1 ≤ C) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hZ : ∀ z ∈ Z, R ≤ dist x z)
    (hA : ∀ y ∈ ball x R, ∀ ξ : EuclideanSpace ℝ ι, 0 ≤ (A y).toQuadraticForm' ξ)
    (hΛ : ∀ y ∈ ball x R, ∀ ξ : EuclideanSpace ℝ ι, (A y).toQuadraticForm' ξ ≤ Λ * ‖ξ‖ ^ 2)
    (hv : ∀ y ∈ ball x R, ‖v y‖ ≤ B)
    (hlow : ∀ y ∈ ball x R, (∀ z ∈ Z, ρ ≤ dist y z) → θ ≤ a y ^ 2)
    (hcd : ∀ y ∈ ball x R, ContDiffAt ℝ 2 (fun z ↦ a z ^ 2) y)
    (hW : ∀ y ∈ ball x R, -(C * a y * (db y + a y + b y)) ≤
      -(∑ i, ∑ j, A y i j * fderiv ℝ (fderiv ℝ fun z ↦ a z ^ 2) y (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) + fderiv ℝ (fun z ↦ a z ^ 2) y (v y)) / 2 +
        da y ^ 2 + r / 4 * (a y ^ 2 + b y ^ 2 - 1) * a y ^ 2)
    (hG : ∀ y ∈ ball x R, 2 * a y ^ 2 * ((1 - θ / (8 * C)) * da y ^ 2 -
      (2 + 18 / (θ / (8 * C))) * q y ^ 2) ≤
        ∑ i, ∑ j, A y i j * (fderiv ℝ (fun z ↦ a z ^ 2) y (EuclideanSpace.single i 1) *
          fderiv ℝ (fun z ↦ a z ^ 2) y (EuclideanSpace.single j 1)))
    (hβ : ∀ y ∈ ball x R, b y ^ 2 ≤ C / r * max (1 - a y ^ 2) 0 + C / r ^ 2)
    (hgrad : ∀ y ∈ ball x R, da y ^ 2 + r * db y ^ 2 ≤ C * r * max (1 - a y ^ 2) 0 + C)
    (hup : ∀ y ∈ ball x R, a y ^ 2 ≤ 1 + C / r) (hq : ∀ y ∈ ball x R, q y ^ 2 ≤ C) :
    1 - a x ^ 2 ≤ 1216 * C ^ 2 / (θ ^ 3 * r) +
      Real.exp ((Fintype.card ι : ℝ) / 8) * Real.log θ⁻¹ *
        Real.exp (-(θ * r * R / (16 * (√(θ * r) * √Λ + B)))) := by
  -- The decay estimate is applied on the ball of radius `R / 2`, inside the ball of radius `R`.
  have hsub : ball x (R / 2) ⊆ ball x R := ball_subset_ball (by linarith)
  -- Every point of the smaller ball is at distance more than `R / 2 ≥ ρ` from `Z`.
  have hθa : ∀ y ∈ ball x (R / 2), θ ≤ a y ^ 2 := by
    refine fun y hy ↦ hlow y (hsub hy) fun z hz ↦ ?_
    have := dist_triangle_left x z y
    rw [mem_ball] at hy
    linarith [hZ z hz]
  have hdecay := one_sub_sq_le_div_add_exp_mul_mul_exp (R := R / 2) hr (by linarith) hC hθ hθ1
    (fun y hy ↦ hA y (hsub hy)) (fun y hy ↦ hΛ y (hsub hy)) (fun y hy ↦ hv y (hsub hy))
    (fun y hy ↦ hcd y (hsub hy)) hθa (fun y hy ↦ hW y (hsub hy)) (fun y hy ↦ hG y (hsub hy))
    (fun y hy ↦ hβ y (hsub hy)) (fun y hy ↦ hgrad y (hsub hy)) (fun y hy ↦ hup y (hsub hy))
    (fun y hy ↦ hq y (hsub hy))
  generalize √(θ * r) * √Λ + B = D at hdecay ⊢
  rwa [show θ * r * (R / 2) / (8 * D) = θ * r * R / (16 * D) by ring] at hdecay

/-- At radius `K / √r`, the rate of the off-zero bound in a chart is at least
`θ K / (16 (√θ √Λ + B))`, uniformly in `r ≥ 1`. -/
private theorem mul_le_div_of_one_le {r K θ Λ B : ℝ} (hr : 1 ≤ r) (hK : 0 ≤ K) (hθ : 0 < θ)
    (hΛ : 0 < Λ) (hB : 0 ≤ B) :
    θ / (16 * (√θ * √Λ + B)) * K ≤ θ * r * (K / √r) / (16 * (√(θ * r) * √Λ + B)) := by
  have hs : 1 ≤ √r := Real.one_le_sqrt.2 hr
  -- With `s = √r`, the right side is `θ s K / (16 (√θ √Λ s + B))`.
  have hrhs : θ * r * (K / √r) / (16 * (√(θ * r) * √Λ + B)) =
      θ * √r * K / (16 * (√θ * √Λ * √r + B)) := by
    rw [Real.sqrt_mul hθ.le, ← Real.mul_self_sqrt (zero_le_one.trans hr)]
    rw [Real.sqrt_mul_self (Real.sqrt_nonneg r)]
    field_simp
  rw [hrhs, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  -- Cross-multiplied, the inequality reduces to `θ K B ≤ θ K B √r`.
  have hθKB : 0 ≤ θ * K * B := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hs hθKB]

/-- **Zero localization at every threshold in a chart of a curved metric.** Let `C ≥ 1`,
`0 < θ ≤ 1`, `Λ > 0`, `B` and `ρ` real, and `σ < 1`. There are constants `K > 0` and `r₀ ≥ 1`,
depending only on `C`, `θ`, `ρ`, `σ`, `Λ`, `B` and `ι`, with the following property. On
`ℝⁿ = EuclideanSpace ℝ ι`, let `L = ∑ᵢⱼ Aⁱʲ ∂ᵢ∂ⱼ + ∂_v` be an operator in non-divergence form, such
as the Laplace–Beltrami operator of a metric `g` written in a chart. Consider functions `a`, `b`,
`da`, `db`, `q` standing for `|α|`, `|β|`, `|∇_a α|`, `|∇β|`, `|∂bar_a α|` of a solution of
Taubes's large-parameter Seiberg–Witten equations at parameter `r ≥ r₀`, a set `Z` (the zero set of
`α`) and a point `x` such that on the open ball of radius `K / √r` about `x`:

* `0 ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` and `‖v‖ ≤ B`;
* `|α|²` is of class `C²`, and the projected Weitzenböck equation written with `L`, the gradient
  inequality in the metric `g` at `ε = θ / (8 C)` and Taubes's coarse bounds hold, as in
  `TauCeti.SeibergWitten.one_sub_sq_le_div_add_exp_mul_mul_exp`;
* `|α|² ≥ θ` at every point at distance at least `ρ / √r` from `Z`.

If `|α(x)|² ≤ σ`, then `x` lies within distance `K / √r` of a point of `Z`. The constants depend
on the metric only through the bounds `Λ` on `g⁻¹` and `B` on the drift, so they are uniform over
the charts of a compact family of metrics. -/
theorem exists_forall_exists_dist_le_div_sqrt_of_sq_le_of_sum_mul_fderiv_fderiv_add_fderiv
    (C θ ρ Λ B : ℝ) (hC : 1 ≤ C) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hΛ0 : 0 < Λ) {σ : ℝ}
    (hσ : σ < 1) :
    ∃ K r₀ : ℝ, 0 < K ∧ 1 ≤ r₀ ∧ ∀ {A : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {a b da db q : EuclideanSpace ℝ ι → ℝ}
      {Z : Set (EuclideanSpace ℝ ι)} {x : EuclideanSpace ℝ ι} {r : ℝ}, r₀ ≤ r →
      (∀ y ∈ ball x (K / √r), ∀ ξ : EuclideanSpace ℝ ι, 0 ≤ (A y).toQuadraticForm' ξ) →
      (∀ y ∈ ball x (K / √r), ∀ ξ : EuclideanSpace ℝ ι,
        (A y).toQuadraticForm' ξ ≤ Λ * ‖ξ‖ ^ 2) →
      (∀ y ∈ ball x (K / √r), ‖v y‖ ≤ B) →
      (∀ y ∈ ball x (K / √r), (∀ z ∈ Z, ρ / √r ≤ dist y z) → θ ≤ a y ^ 2) →
      (∀ y ∈ ball x (K / √r), ContDiffAt ℝ 2 (fun z ↦ a z ^ 2) y) →
      (∀ y ∈ ball x (K / √r), -(C * a y * (db y + a y + b y)) ≤
        -(∑ i, ∑ j, A y i j * fderiv ℝ (fderiv ℝ fun z ↦ a z ^ 2) y (EuclideanSpace.single i 1)
            (EuclideanSpace.single j 1) + fderiv ℝ (fun z ↦ a z ^ 2) y (v y)) / 2 +
          da y ^ 2 + r / 4 * (a y ^ 2 + b y ^ 2 - 1) * a y ^ 2) →
      (∀ y ∈ ball x (K / √r), 2 * a y ^ 2 * ((1 - θ / (8 * C)) * da y ^ 2 -
        (2 + 18 / (θ / (8 * C))) * q y ^ 2) ≤
          ∑ i, ∑ j, A y i j * (fderiv ℝ (fun z ↦ a z ^ 2) y (EuclideanSpace.single i 1) *
            fderiv ℝ (fun z ↦ a z ^ 2) y (EuclideanSpace.single j 1))) →
      (∀ y ∈ ball x (K / √r), b y ^ 2 ≤ C / r * max (1 - a y ^ 2) 0 + C / r ^ 2) →
      (∀ y ∈ ball x (K / √r), da y ^ 2 + r * db y ^ 2 ≤ C * r * max (1 - a y ^ 2) 0 + C) →
      (∀ y ∈ ball x (K / √r), a y ^ 2 ≤ 1 + C / r) →
      (∀ y ∈ ball x (K / √r), q y ^ 2 ≤ C) →
      a x ^ 2 ≤ σ → ∃ z ∈ Z, dist x z ≤ K / √r := by
  -- `max B 0` is `B` whenever the drift bound holds on a nonempty ball.
  have hκ : 0 < θ / (16 * (√θ * √Λ + max B 0)) :=
    div_pos hθ (mul_pos (by norm_num) (add_pos_of_pos_of_nonneg
      (mul_pos (Real.sqrt_pos.2 hθ) (Real.sqrt_pos.2 hΛ0)) (le_max_right _ _)))
  obtain ⟨K, r₀, hK, hρK, hr₀, hlt⟩ := exists_div_add_mul_exp_lt
    (B := Real.exp ((Fintype.card ι : ℝ) / 8) * Real.log θ⁻¹) (C := C) (θ := θ)
    (sub_pos.2 hσ) hκ ρ
  refine ⟨K, r₀, hK, hr₀, fun {A v a b da db q Z x r} hr hA hΛ hv hlow hcd hW hG hβ hgrad hup hq
    hσx ↦ ?_⟩
  -- Otherwise the ball of radius `K / √r` misses `Z`, and the off-zero bound at that radius
  -- forces `1 - |α(x)|² < 1 - σ`.
  by_contra! hfar
  have hr1 : 1 ≤ r := hr₀.trans hr
  have hsr : 0 < √r := Real.sqrt_pos.2 (one_pos.trans_le hr1)
  have hB : 0 ≤ B := (norm_nonneg _).trans (hv x (mem_ball_self (div_pos hK hsr)))
  have hbound := one_sub_sq_le_div_add_exp_mul_mul_exp_of_forall_le_dist hr1 (div_pos hK hsr)
    (by rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hρK hsr.le) hC hθ hθ1
    (fun z hz ↦ (hfar z hz).le) hA hΛ hv hlow hcd hW hG hβ hgrad hup hq
  -- The rate at radius `K / √r` is at least `κ K`, so the bound is below `1 - σ`.
  have hD : 0 ≤ Real.exp ((Fintype.card ι : ℝ) / 8) * Real.log θ⁻¹ :=
    mul_nonneg (Real.exp_pos _).le (Real.log_nonneg (one_le_inv_iff₀.mpr ⟨hθ, hθ1⟩))
  have hexp := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg
    (mul_le_div_of_one_le hr1 hK.le hθ hΛ0 hB))) hD
  rw [max_eq_left hB] at hlt
  linarith [hlt r hr]

end Chart

end TauCeti.SeibergWitten
