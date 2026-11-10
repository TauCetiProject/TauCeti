/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Perron.Regular
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.InnerProductSpace.Laplacian.Zonal

/-!
# The exterior cone condition

Let `Ω` be an open subset of a finite-dimensional real inner product space `E` of dimension `n`,
and let `ξ ∉ Ω`. The **exterior cone condition** at `ξ` asks for a truncated open circular cone
with vertex `ξ` that misses `Ω`: for a unit vector `v`, an aperture parameter `a < 1` and a radius
`ρ > 0`, no point `x` of `Ω ∩ ball ξ ρ` lies in the cone `a ‖x - ξ‖ < ⟪x - ξ, v⟫` of axis `v`
and half-angle `arccos a`. This file shows that such a point is regular, so that the Dirichlet
problem for the Laplacian is solvable on every bounded open set satisfying the exterior cone
condition at each boundary point (Gilbarg–Trudinger, Section 2.8 and the exterior cone condition
among the problems of Chapter 2). Unlike the exterior sphere condition, it holds at the
reentrant corners of polyhedra.

**The barrier.** In polar coordinates about `ξ`, with `r = ‖x - ξ‖` and `s = ⟪x - ξ, v⟫ / r` the
cosine of the angle with the axis, the barrier is

`w(x) = r ^ μ (c - exp (κ s))`,  `κ = n / (1 - a²)`,  `c = 2 exp κ`,  `μ = exp (-2κ) / (2 (n + 1))`

for `0 ≤ a < 1` (a smaller cone only weakens the hypothesis, so `a ≥ 0` is no restriction). It is
continuous, vanishes at `ξ` and is positive elsewhere, since `exp (κ s) ≤ exp κ < c`. By the
Laplacian of zonal functions (`TauCeti.laplacian_norm_rpow_mul_comp_inner_div_norm`),

`r ^ (2 - μ) Δw = μ (μ + n - 2) (c - exp (κ s)) - exp (κ s) (κ² (1 - s²) - κ (n - 1) s)`,

and outside the cone, where `-1 ≤ s ≤ a`, the second term dominates: the concave quadratic
`κ² (1 - s²) - κ (n - 1) s` is at least `κ` at both ends `s = -1` and `s = a` when `n ≥ 2`, and
the first term is at most `κ exp (-κ)` by the choice of `μ`. So `w` is superharmonic on
`Ω ∩ ball ξ ρ`, a local barrier, which `TauCeti.IsBarrier.exists_isBarrier_of_inter` turns into
a barrier relative to `Ω`.

## Main declarations

* `TauCeti.exists_isBarrier_of_exterior_cone`: a point satisfying the exterior cone condition
  admits a barrier.
* `TauCeti.exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier_of_exterior_cone`: **the
  Dirichlet problem** is solvable on bounded open sets satisfying the exterior cone condition.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 2.8 and the problems of Chapter 2.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian Metric Set Filter Topology
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The angular inequality behind the cone barrier: for `-1 ≤ s ≤ a` with `0 ≤ a < 1`, the
parameters `κ (1 - a²) = n`, `c = 2 exp κ` and a small `μ` make the right-hand side of the zonal
Laplacian formula for `r ^ μ (c - exp (κ s))` nonpositive. -/
private lemma cone_barrier_ineq {n : ℕ} (hn : 1 ≤ n) {a s κ μ : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hs1 : -1 ≤ s) (hsa : s ≤ a) (hκ : κ * (1 - a ^ 2) = n) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (hμ : μ * (n - 1) * (2 * Real.exp κ) ≤ κ * Real.exp (-κ)) :
    μ * (μ + n - 2) * (2 * Real.exp κ - Real.exp (κ * s)) -
      Real.exp (κ * s) * (κ ^ 2 * (1 - s ^ 2) - κ * (n - 1) * s) ≤ 0 := by
  have h1a : 0 < 1 - a ^ 2 := by nlinarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hκ0 : 0 < κ := by
    by_contra h
    nlinarith
  have hE : 0 < Real.exp (κ * s) := Real.exp_pos _
  -- The value `exp (κ s)` lies between `exp (-κ)` and `exp κ`.
  have hEle : Real.exp (κ * s) ≤ Real.exp κ := Real.exp_le_exp.2 (by nlinarith)
  have hEge : Real.exp (-κ) ≤ Real.exp (κ * s) := Real.exp_le_exp.2 (by nlinarith)
  have hg0 : 0 ≤ 2 * Real.exp κ - Real.exp (κ * s) := by linarith [Real.exp_pos κ]
  rcases hn.eq_or_lt with hn | hn
  · -- In dimension one, `μ (μ - 1) ≤ 0` and the angular term is nonnegative.
    subst hn
    have hm : μ * (μ + ((1 : ℕ) : ℝ) - 2) ≤ 0 := by push_cast; nlinarith
    have hQ : 0 ≤ κ ^ 2 * (1 - s ^ 2) - κ * (((1 : ℕ) : ℝ) - 1) * s := by
      have h1s : 0 ≤ 1 - s ^ 2 := by nlinarith
      push_cast
      nlinarith [mul_nonneg (sq_nonneg κ) h1s]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hm hg0, mul_nonneg hE.le hQ]
  · -- In dimension at least two, the angular term is at least `κ`, by concavity in `s`.
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hQ : κ ≤ κ ^ 2 * (1 - s ^ 2) - κ * (n - 1) * s := by
      -- The concave quadratic `h` is nonnegative at `s = -1` and `s = a`, hence in between.
      have key : (a + 1) * (κ * (1 - s ^ 2) - (n - 1) * s - 1) =
          (a - s) * (n - 2) + (s + 1) * ((n - 1) * (1 - a)) +
            κ * (a + 1) * ((s + 1) * (a - s)) := by
        linear_combination (s + 1) * hκ
      have hR : 0 ≤ (a - s) * (n - 2) + (s + 1) * ((n - 1) * (1 - a)) +
          κ * (a + 1) * ((s + 1) * (a - s)) := by
        have h₁ := mul_nonneg (by linarith : (0 : ℝ) ≤ s + 1) (by linarith : 0 ≤ a - s)
        have h₂ := mul_nonneg (by linarith : (0 : ℝ) ≤ n - 1) (by linarith : 0 ≤ 1 - a)
        have h₃ := mul_nonneg (mul_nonneg hκ0.le (by linarith : (0 : ℝ) ≤ a + 1)) h₁
        nlinarith
      have hh : 0 ≤ κ * (1 - s ^ 2) - (n - 1) * s - 1 :=
        (mul_nonneg_iff_of_pos_left (by linarith : (0 : ℝ) < a + 1)).1 (key ▸ hR)
      nlinarith [mul_nonneg hκ0.le hh]
    have hm0 : 0 ≤ μ * (μ + n - 2) := by nlinarith
    have hm : μ * (μ + n - 2) ≤ μ * (n - 1) := by nlinarith
    calc μ * (μ + n - 2) * (2 * Real.exp κ - Real.exp (κ * s)) -
          Real.exp (κ * s) * (κ ^ 2 * (1 - s ^ 2) - κ * (n - 1) * s)
        ≤ μ * (n - 1) * (2 * Real.exp κ) - Real.exp (-κ) * κ := by
          gcongr ?_ - ?_
          · exact mul_le_mul hm (by linarith) hg0 (by nlinarith)
          · exact mul_le_mul hEge hQ hκ0.le hE.le
      _ ≤ 0 := by linarith

/-- The cone barrier with vertex at the origin, axis `v` and parameters `κ`, `μ`:
`x ↦ ‖x‖ ^ μ (2 exp κ - exp (κ s))`, where `s = ⟪v, x⟫ / ‖x‖`. -/
private noncomputable def coneBarrier (v : E) (κ μ : ℝ) (x : E) : ℝ :=
  ‖x‖ ^ μ * (2 * Real.exp κ - Real.exp (κ * (⟪v, x⟫_ℝ / ‖x‖)))

omit [FiniteDimensional ℝ E] in
/-- For `κ ≥ 0`, the angular factor `2 exp κ - exp (κ s)` of the cone barrier lies in
`(0, 2 exp κ]`. -/
private lemma coneBarrier_angular_mem {v : E} (hv : ‖v‖ = 1) {κ : ℝ} (hκ : 0 ≤ κ) (y : E) :
    0 < 2 * Real.exp κ - Real.exp (κ * (⟪v, y⟫_ℝ / ‖y‖)) ∧
      2 * Real.exp κ - Real.exp (κ * (⟪v, y⟫_ℝ / ‖y‖)) ≤ 2 * Real.exp κ := by
  have hs : ⟪v, y⟫_ℝ / ‖y‖ ≤ 1 :=
    (abs_le.1 (by simpa [hv] using abs_real_inner_div_norm_mul_norm_le_one v y)).2
  have : Real.exp (κ * (⟪v, y⟫_ℝ / ‖y‖)) ≤ Real.exp κ := Real.exp_le_exp.2 (by nlinarith)
  constructor <;> linarith [Real.exp_pos κ, Real.exp_pos (κ * (⟪v, y⟫_ℝ / ‖y‖))]

omit [FiniteDimensional ℝ E] in
/-- The cone barrier is positive away from its vertex. -/
private lemma coneBarrier_pos {v : E} (hv : ‖v‖ = 1) {κ : ℝ} (hκ : 0 ≤ κ) (μ : ℝ) {y : E}
    (hy : y ≠ 0) : 0 < coneBarrier v κ μ y :=
  mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.2 hy) μ) (coneBarrier_angular_mem hv hκ y).1

omit [FiniteDimensional ℝ E] in
/-- The cone barrier is smooth away from its vertex. -/
private lemma contDiffAt_coneBarrier (v : E) (κ μ : ℝ) {y : E} (hy : y ≠ 0) :
    ContDiffAt ℝ 2 (coneBarrier v κ μ) y := by
  have hr : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have hs : ContDiffAt ℝ 2 (fun y : E ↦ ⟪v, y⟫_ℝ / ‖y‖) y :=
    (innerSL ℝ v).contDiff.contDiffAt.div (contDiffAt_norm ℝ hy) hr
  exact ((contDiffAt_norm ℝ hy).rpow_const_of_ne hr).mul
    (contDiffAt_const.sub (contDiffAt_const.mul hs).exp)

omit [FiniteDimensional ℝ E] in
/-- For `μ > 0` the cone barrier is continuous, with value `0` at its vertex, since it is bounded
by `2 exp κ ‖y‖ ^ μ`. -/
private lemma continuous_coneBarrier {v : E} (hv : ‖v‖ = 1) {κ μ : ℝ} (hκ : 0 ≤ κ)
    (hμ : 0 < μ) : Continuous (coneBarrier v κ μ) := by
  refine continuous_iff_continuousAt.2 fun y ↦ ?_
  rcases eq_or_ne y 0 with rfl | hy
  · have hpow : Tendsto (fun y : E ↦ 2 * Real.exp κ * ‖y‖ ^ μ) (𝓝 0) (𝓝 0) := by
      have : Continuous fun y : E ↦ 2 * Real.exp κ * ‖y‖ ^ μ :=
        continuous_const.mul (continuous_norm.rpow_const fun _ ↦ .inr hμ.le)
      simpa [Real.zero_rpow hμ.ne'] using this.tendsto 0
    have h0 : coneBarrier v κ μ 0 = 0 := by simp [coneBarrier, Real.zero_rpow hμ.ne']
    rw [ContinuousAt, h0]
    refine squeeze_zero_norm (fun y ↦ ?_) hpow
    have h := coneBarrier_angular_mem hv hκ y
    rw [coneBarrier, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg y) μ),
      abs_of_pos h.1, mul_comm]
    exact mul_le_mul_of_nonneg_right h.2 (Real.rpow_nonneg (norm_nonneg y) μ)
  · exact (contDiffAt_coneBarrier v κ μ hy).continuousAt

/-- The cone barrier has nonpositive Laplacian at every `x ≠ 0` outside the cone
`a ‖x‖ < ⟪v, x⟫`, under the constraints of `cone_barrier_ineq` on its parameters. -/
private lemma laplacian_coneBarrier_nonpos {v : E} (hv : ‖v‖ = 1) {a κ μ : ℝ} (ha0 : 0 ≤ a)
    (ha1 : a < 1) (hκ : κ * (1 - a ^ 2) = Module.finrank ℝ E) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (hμ : μ * (Module.finrank ℝ E - 1) * (2 * Real.exp κ) ≤ κ * Real.exp (-κ)) {x : E}
    (hx : x ≠ 0) (hxa : ⟪v, x⟫_ℝ ≤ a * ‖x‖) : Δ (coneBarrier v κ μ) x ≤ 0 := by
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  set s := ⟪v, x⟫_ℝ / ‖x‖ with hs
  have hs1 : |s| ≤ 1 := by simpa [hv] using abs_real_inner_div_norm_mul_norm_le_one v x
  have hsa : s ≤ a := by rwa [hs, div_le_iff₀ hr]
  have hn : 1 ≤ Module.finrank ℝ E := by
    have : Nontrivial E := ⟨⟨x, 0, hx⟩⟩
    exact Module.finrank_pos
  set F : ℝ → ℝ := fun t ↦ 2 * Real.exp κ - Real.exp (κ * t) with hF
  have hd : ∀ t, HasDerivAt F (-(κ * Real.exp (κ * t))) t := fun t ↦ by
    simpa [mul_comm] using ((hasDerivAt_mul_const κ).exp.const_sub (2 * Real.exp κ) :
      HasDerivAt (fun t ↦ 2 * Real.exp κ - Real.exp (t * κ)) _ t)
  have hdF : deriv F = fun t ↦ -(κ * Real.exp (κ * t)) := funext fun t ↦ (hd t).deriv
  have hd2 : ∀ t, HasDerivAt (fun t ↦ -(κ * Real.exp (κ * t))) (-(κ ^ 2 * Real.exp (κ * t))) t :=
    fun t ↦ by
      have h := (((hasDerivAt_id t).const_mul κ).exp.const_mul κ).neg
      simp only [id] at h
      convert h using 1
      ring
  have hFc : ContDiffAt ℝ 2 F s := by
    simp only [hF]
    fun_prop
  rw [show coneBarrier v κ μ = fun y ↦ ‖y‖ ^ μ * F (⟪v, y⟫_ℝ / ‖y‖) from rfl,
    laplacian_norm_rpow_mul_comp_inner_div_norm hv μ hx hFc, hdF, (hd2 s).deriv]
  refine mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hr.le _) ?_
  have h := cone_barrier_ineq hn ha0 ha1 (abs_le.1 hs1).1 hsa hκ hμ0 hμ1 hμ
  simp only [hF] at h ⊢
  linarith

omit [FiniteDimensional ℝ E] in
/-- Admissible parameters of the cone barrier for `0 ≤ a < 1`: `κ = n / (1 - a²)` and
`μ = exp (-2κ) / (2 (n + 1))`, where `n = dim E`. -/
private lemma exists_coneBarrier_params {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    ∃ κ μ : ℝ, 0 ≤ κ ∧ κ * (1 - a ^ 2) = Module.finrank ℝ E ∧ 0 < μ ∧ μ ≤ 1 ∧
      μ * (Module.finrank ℝ E - 1) * (2 * Real.exp κ) ≤ κ * Real.exp (-κ) := by
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  have h1a : 0 < 1 - a ^ 2 := by nlinarith
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  set κ := n / (1 - a ^ 2) with hκ_def
  have hκ0 : 0 ≤ κ := div_nonneg hn0 h1a.le
  set μ := Real.exp (-(2 * κ)) / (2 * (n + 1))
  have hμle : μ * (2 * (n + 1)) = Real.exp (-(2 * κ)) := div_mul_cancel₀ _ (by positivity)
  refine ⟨κ, μ, hκ0, div_mul_cancel₀ n h1a.ne', by positivity, ?_, ?_⟩
  · have : Real.exp (-(2 * κ)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    nlinarith
  have hpos := Real.exp_pos (-κ)
  -- In dimension zero the left side is negative; otherwise `κ ≥ 1` and
  -- `μ (n - 1) 2 exp κ = (n - 1) / (n + 1) exp (-κ) ≤ exp (-κ)`.
  rcases eq_or_lt_of_le hn0 with hn | hn
  · rw [← hn]
    nlinarith [Real.exp_pos κ, show (0 : ℝ) < μ by positivity]
  have hn1 : 1 ≤ n := Nat.one_le_cast.2 (Nat.cast_pos.1 hn)
  have hκ1 : 1 ≤ κ := by
    rw [hκ_def, le_div_iff₀ h1a]
    nlinarith
  have hexp : Real.exp (-(2 * κ)) * Real.exp κ = Real.exp (-κ) := by
    rw [← Real.exp_add]
    ring_nf
  calc μ * (n - 1) * (2 * Real.exp κ) = (n - 1) / (n + 1) * Real.exp (-κ) := by
        rw [← hexp, ← hμle]
        field_simp
    _ ≤ 1 * Real.exp (-κ) := by
        gcongr
        rw [div_le_one (by linarith)]
        linarith
    _ ≤ κ * Real.exp (-κ) := by gcongr

variable [MeasurableSpace E] [BorelSpace E] {Ω : Set E}

/-- **The local cone barrier.** If `ξ ∉ Ω` and no point `x` of `Ω ∩ ball ξ ρ` lies in the open
cone `a ‖x - ξ‖ < ⟪x - ξ, v⟫` of axis the unit vector `v`, with `0 ≤ a < 1`, then the cone barrier
`r ^ μ (2 exp κ - exp (κ s))`, with `r = ‖x - ξ‖` and `s = ⟪v, x - ξ⟫ / r`, is a barrier at `ξ`
relative to `Ω ∩ ball ξ ρ` for admissible parameters `κ`, `μ`. -/
private lemma isBarrier_coneBarrier (hΩ : IsOpen Ω) {ξ : E} (hξ : ξ ∉ Ω) {v : E} (hv : ‖v‖ = 1)
    {a ρ κ μ : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hcone : ∀ x ∈ Ω ∩ ball ξ ρ, ⟪x - ξ, v⟫_ℝ ≤ a * ‖x - ξ‖) (hκ0 : 0 ≤ κ)
    (hκ : κ * (1 - a ^ 2) = Module.finrank ℝ E) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (hμ : μ * (Module.finrank ℝ E - 1) * (2 * Real.exp κ) ≤ κ * Real.exp (-κ)) :
    IsBarrier (Ω ∩ ball ξ ρ) ξ fun x ↦ coneBarrier v κ μ (x + -ξ) := by
  have hne : ∀ x ∈ Ω ∩ ball ξ ρ, x + -ξ ≠ 0 := fun x hx h ↦
    hξ (by rw [← sub_eq_add_neg, sub_eq_zero] at h; exact h ▸ hx.1)
  refine ⟨subharmonicOn_of_laplacian_nonneg (hΩ.inter isOpen_ball) (fun x hx ↦ ?_)
    fun x hx ↦ ?_, ((continuous_coneBarrier hv hκ0 hμ0).comp
      (continuous_id.add continuous_const)).continuousOn, ?_, fun x _ hx ↦ ?_⟩
  · -- The barrier is smooth on `Ω ∩ ball ξ ρ`, which avoids the vertex `ξ`.
    exact ((contDiffAt_coneBarrier v κ μ (hne x hx)).comp x
      (contDiffAt_id.add contDiffAt_const)).neg.contDiffWithinAt
  · -- Its Laplacian is nonpositive outside the cone.
    have hxa : ⟪v, x + -ξ⟫_ℝ ≤ a * ‖x + -ξ‖ := by
      rw [← sub_eq_add_neg, real_inner_comm]
      exact hcone x hx
    rw [show (-fun x ↦ coneBarrier v κ μ (x + -ξ)) = fun x ↦ (-coneBarrier v κ μ) (x + -ξ)
      from rfl, laplacian_comp_add_right, laplacian_neg]
    simp only [Pi.neg_apply, neg_nonneg]
    exact laplacian_coneBarrier_nonpos hv ha0 ha1 hκ hμ0 hμ1 hμ (hne x hx) hxa
  · simp [coneBarrier, Real.zero_rpow hμ0.ne']
  · exact coneBarrier_pos hv hκ0 μ (by rwa [← sub_eq_add_neg, sub_ne_zero])

/-- **The exterior cone condition gives a barrier.** Let `Ω` be open and `ξ ∉ Ω`. If, for a unit
vector `v`, some `a < 1` and some `ρ > 0`, no point `x ∈ Ω ∩ ball ξ ρ` lies in the open cone
`a ‖x - ξ‖ < ⟪x - ξ, v⟫` with vertex `ξ` and axis `v`, then `ξ` admits a barrier relative to
`Ω`: it is a regular boundary point. -/
theorem exists_isBarrier_of_exterior_cone (hΩ : IsOpen Ω) {ξ : E} (hξ : ξ ∉ Ω) {v : E}
    (hv : ‖v‖ = 1) {a ρ : ℝ} (ha : a < 1) (hρ : 0 < ρ)
    (hcone : ∀ x ∈ Ω ∩ ball ξ ρ, ⟪x - ξ, v⟫_ℝ ≤ a * ‖x - ξ‖) :
    ∃ w, IsBarrier Ω ξ w := by
  -- Shrinking the cone to `max a 0` keeps the hypothesis.
  have hcone' : ∀ x ∈ Ω ∩ ball ξ ρ, ⟪x - ξ, v⟫_ℝ ≤ max a 0 * ‖x - ξ‖ := fun x hx ↦
    (hcone x hx).trans (mul_le_mul_of_nonneg_right (le_max_left a 0) (norm_nonneg _))
  obtain ⟨κ, μ, hκ0, hκ, hμ0, hμ1, hμ⟩ :=
    exists_coneBarrier_params (E := E) (le_max_right a 0) (max_lt ha one_pos)
  exact (isBarrier_coneBarrier hΩ hξ hv (le_max_right a 0) (max_lt ha one_pos) hcone' hκ0 hκ
    hμ0 hμ1 hμ).exists_isBarrier_of_inter hΩ (ball_mem_nhds ξ hρ)

/-- **The Dirichlet problem under the exterior cone condition.** Let `Ω` be a bounded open set
such that at every boundary point `ξ` some truncated open circular cone with vertex `ξ` misses
`Ω`: for a unit vector `v`, some `a < 1` and some `ρ > 0`, no point `x ∈ Ω ∩ ball ξ ρ` satisfies
`a ‖x - ξ‖ < ⟪x - ξ, v⟫`. Then for boundary data `g` continuous on `frontier Ω` there is a
function harmonic in `Ω`, continuous on `closure Ω` and equal to `g` on `frontier Ω`. -/
theorem exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier_of_exterior_cone
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hcone : ∀ ξ ∈ frontier Ω, ∃ v : E, ‖v‖ = 1 ∧ ∃ a < 1, ∃ ρ > 0,
      ∀ x ∈ Ω ∩ ball ξ ρ, ⟪x - ξ, v⟫_ℝ ≤ a * ‖x - ξ‖)
    {g : E → ℝ} (hg : ContinuousOn g (frontier Ω)) :
    ∃ u, HarmonicOnNhd u Ω ∧ ContinuousOn u (closure Ω) ∧ EqOn u g (frontier Ω) := by
  refine exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier hΩ hb (fun ξ hξ ↦ ?_) hg
  obtain ⟨v, hv, a, ha, ρ, hρ, h⟩ := hcone ξ hξ
  have hξ' : ξ ∈ closure Ω \ Ω := hΩ.frontier_eq ▸ hξ
  exact exists_isBarrier_of_exterior_cone hΩ hξ'.2 hv ha hρ h

end TauCeti
