/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Perron.Regular
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.InnerProductSpace.Laplacian.Zonal
import TauCeti.Analysis.Sobolev.LipschitzDomain.ExteriorCone

/-!
# The exterior cone condition

Let `Ω` be an open subset of a finite-dimensional real inner product space `E` of dimension `n`.
A point `ξ ∈ frontier Ω` satisfies the **exterior cone condition** if some truncated closed cone
with vertex `ξ` misses `Ω`: for a unit vector `e`, a number `c < 1` and a radius `ρ > 0`, no point
`x ∈ Ω` with `‖x - ξ‖ < ρ` satisfies `c ‖x - ξ‖ ≤ ⟪e, x - ξ⟫`. For `-1 < c < 1` this is the
cone of axis `e` and half-aperture `arccos c`. This file proves that every such point is regular,
so that the Dirichlet problem for harmonic functions is solvable on every bounded open set
satisfying the exterior cone condition at each boundary point, in particular on every bounded
Lipschitz domain. The condition is weaker than the exterior sphere condition: it holds at the
reentrant corner of an L-shaped domain, where no exterior ball touches the boundary.

## The barrier

Put `y = x - ξ` and `t = ⟪e, y⟫ / ‖y‖`, so that `t < c` on the truncated set `Ω ∩ ball ξ ρ`. The
explicit local barrier is

`w x = ‖y‖ ^ μ (A - exp (k t))`

with `k = n / (1 - c)`, `A = 2 exp (k c)` and `μ = min 1 (k exp (-k) / A)`. It vanishes at `ξ`, and
it is positive elsewhere on `closure (Ω ∩ ball ξ ρ)` because `exp (k t) ≤ exp (k c) < A` there.
Farther from `ξ` the cone bound need not hold, and `w` may be negative. The Laplacian of
a homogeneous zonal function (`TauCeti.laplacian_norm_rpow_mul_comp_inner_div_norm`) gives

`Δ w = ‖y‖ ^ (μ - 2) (μ (μ + n - 2) (A - exp (k t)) - k exp (k t) (k (1 - t²) - (n - 1) t))`.

For `-1 ≤ t ≤ c` one has `k (1 - t²) - (n - 1) t ≥ n - 1`, since the difference is
`(1 + t) (k (1 - t) - (n - 1))` and `k (1 - c) ≥ n - 1`. So the second term is at most
`-(n - 1) k exp (-k)`, while the first is at most `(n - 1) μ A` because `μ ≤ 1`, and
`μ A ≤ k exp (-k)` makes `Δ w ≤ 0`. Hence `w` is superharmonic
(`ContDiffOn.subharmonicOn_of_laplacian_nonneg`) on the open cone `{t < c}`, which contains
`Ω ∩ ball ξ ρ`. Since regularity is local (`TauCeti.IsBarrier.exists_isBarrier_of_inter`), this
local barrier on `Ω ∩ ball ξ ρ` produces a barrier relative to all of `Ω`.

This is the barrier `r ^ μ f(θ)` suggested by Gilbarg and Trudinger, with the explicit angular
profile `f = A - exp (k cos θ)` in place of an eigenfunction of the spherical Laplacian.

## Main declarations

* `TauCeti.subharmonicOn_neg_norm_sub_rpow_mul_sub_exp`: the explicit barrier is superharmonic
  on the open cone.
* `TauCeti.isBarrier_norm_sub_rpow_mul_sub_exp`: the explicit barrier on a set contained in a cone
  with vertex `ξ`.
* `TauCeti.exists_isBarrier_of_exterior_cone`: a boundary point satisfying the exterior cone
  condition is regular.
* `TauCeti.exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier_of_exterior_cone`: the
  Dirichlet problem is solvable on bounded open sets satisfying the exterior cone condition.
* `Set.IsLipschitzDomain.exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier`: the Dirichlet
  problem is solvable on bounded Lipschitz domains.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 2.8 and the exercise on the exterior cone condition among the problems of Chapter 2.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian Metric Set Filter Topology
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Set E} {ξ e : E} {c ρ k A μ : ℝ}

/-- The bracket of the zonal Laplacian formula for the profile `F t = exp (k t) - A` is
nonnegative for `-1 ≤ t ≤ c`. -/
private lemma zonal_bracket_nonneg {n t : ℝ} (hn : 1 ≤ n) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (hk0 : 0 ≤ k) (hk : n - 1 ≤ k * (1 - c)) (hA : Real.exp (k * c) ≤ A)
    (hμA : μ * A ≤ k * Real.exp (-k)) (ht1 : -1 ≤ t) (htc : t ≤ c) :
    0 ≤ μ * (μ + n - 2) * (Real.exp (k * t) - A) + (1 - t ^ 2) * (k * (k * Real.exp (k * t))) -
      (n - 1) * t * (k * Real.exp (k * t)) := by
  set X := Real.exp (k * t)
  have hX : 0 < X := Real.exp_pos _
  -- `X ≤ A`, since `k t ≤ k c`, and `exp (-k) ≤ X`, since `-k ≤ k t`.
  have hXA : X ≤ A := (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left htc hk0)).trans hA
  have hXk : Real.exp (-k) ≤ X := Real.exp_le_exp.2 (by nlinarith)
  -- The angular factor `k (1 - t²) - (n - 1) t` is at least `n - 1`.
  have hq : n - 1 ≤ k * (1 - t ^ 2) - (n - 1) * t := by
    have h1 : 0 ≤ 1 + t := by linarith
    have h2 : n - 1 ≤ k * (1 - t) := hk.trans (mul_le_mul_of_nonneg_left (by linarith) hk0)
    linarith [mul_le_mul_of_nonneg_right h2 h1]
  -- The radial term is at least `-(n - 1) μ A`, as `μ (μ + n - 2) ≤ μ (n - 1)` and `X ≤ A`.
  have hrad : -((n - 1) * (μ * A)) ≤ μ * (μ + n - 2) * (X - A) := by
    have h1 : μ * (μ + n - 2) * (A - X) ≤ μ * (n - 1) * (A - X) :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
    have h2 : μ * (n - 1) * (A - X) ≤ μ * (n - 1) * A :=
      mul_le_mul_of_nonneg_left (by linarith) (by nlinarith)
    nlinarith
  have hang : (n - 1) * (k * Real.exp (-k)) ≤ k * X * (k * (1 - t ^ 2) - (n - 1) * t) := by
    have h1 : (n - 1) * (k * Real.exp (-k)) ≤ (n - 1) * (k * X) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hXk hk0) (by linarith)
    have h2 : (n - 1) * (k * X) ≤ (k * (1 - t ^ 2) - (n - 1) * t) * (k * X) :=
      mul_le_mul_of_nonneg_right hq (mul_nonneg hk0 hX.le)
    linarith
  have hfin : (n - 1) * (μ * A) ≤ (n - 1) * (k * Real.exp (-k)) :=
    mul_le_mul_of_nonneg_left hμA (by linarith)
  nlinarith

/-- The derivative of the profile `s ↦ exp (k s) - A`. -/
private lemma deriv_exp_mul_sub_const (k A : ℝ) :
    deriv (fun s : ℝ ↦ Real.exp (k * s) - A) = fun s ↦ k * Real.exp (k * s) := by
  funext s
  rw [((hasDerivAt_id' (x := s)).const_mul k).exp.sub_const A |>.deriv]
  ring

/-- The second derivative of the profile `s ↦ exp (k s) - A`. -/
private lemma deriv_deriv_exp_mul_sub_const (k A : ℝ) :
    deriv (deriv fun s : ℝ ↦ Real.exp (k * s) - A) = fun s ↦ k * (k * Real.exp (k * s)) := by
  rw [deriv_exp_mul_sub_const]
  funext s
  rw [((hasDerivAt_id' (x := s)).const_mul k).exp.const_mul k |>.deriv]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The cosine `⟪e, y⟫ / ‖y‖` of the angle between a unit vector `e` and `y` lies in `[-1, 1]`. -/
private lemma abs_inner_div_norm_le_one (he : ‖e‖ = 1) (y : E) : |⟪e, y⟫_ℝ / ‖y‖| ≤ 1 := by
  simpa [he] using abs_real_inner_div_norm_mul_norm_le_one e y

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A point of the closed cone `{⟪e, y⟫ ≤ c ‖y‖}` other than the vertex has cosine at most `c`. -/
private lemma inner_div_norm_le_of_le_mul_norm {y : E} (hy : y ≠ 0) (h : ⟪e, y⟫_ℝ ≤ c * ‖y‖) :
    ⟪e, y⟫_ℝ / ‖y‖ ≤ c :=
  (div_le_iff₀ (norm_pos_iff.2 hy)).2 h

/-- `k ≥ 0` whenever `0 < μ A ≤ k exp (-k)`. -/
private lemma nonneg_of_mul_le_mul_exp_neg (hμ0 : 0 < μ) (hApos : 0 < A)
    (hμA : μ * A ≤ k * Real.exp (-k)) : 0 ≤ k := by
  by_contra hneg
  have : k * Real.exp (-k) < 0 := mul_neg_of_neg_of_pos (not_le.1 hneg) (Real.exp_pos _)
  linarith [mul_pos hμ0 hApos]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The function `y ↦ ‖y‖ ^ μ * (A - exp (k ⟪e, y⟫ / ‖y‖))` is smooth away from the origin. -/
private lemma contDiffAt_norm_rpow_mul_sub_exp {y : E} (hy : y ≠ 0) :
    ContDiffAt ℝ 2 (fun y : E ↦ ‖y‖ ^ μ * (A - Real.exp (k * (⟪e, y⟫_ℝ / ‖y‖)))) y := by
  have hnorm : ContDiffAt ℝ 2 (fun y : E ↦ ‖y‖) y := contDiffAt_norm ℝ hy
  have hr : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  exact (hnorm.rpow_const_of_ne hr).mul (contDiffAt_const.sub
    ((contDiffAt_const.mul ((innerSL ℝ e).contDiff.contDiffAt.div hnorm hr)).exp))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For `μ > 0` and `k ≥ 0`, the function `y ↦ ‖y‖ ^ μ * (A - exp (k ⟪e, y⟫ / ‖y‖))` is
continuous: away from the origin it is smooth, and at the origin it tends to `0` because it is
bounded by `‖y‖ ^ μ (A + exp k)`. -/
private lemma continuous_norm_rpow_mul_sub_exp (he : ‖e‖ = 1) (hμ0 : 0 < μ) (hk0 : 0 ≤ k) :
    Continuous fun y : E ↦ ‖y‖ ^ μ * (A - Real.exp (k * (⟪e, y⟫_ℝ / ‖y‖))) := by
  refine continuous_iff_continuousAt.2 fun y ↦ ?_
  rcases eq_or_ne y 0 with rfl | hy
  · have hlim : Tendsto (fun y : E ↦ ‖y‖ ^ μ * (|A| + Real.exp k)) (𝓝 0) (𝓝 0) := by
      have : Tendsto (fun y : E ↦ ‖y‖ ^ μ) (𝓝 0) (𝓝 0) := by
        simpa [Real.zero_rpow hμ0.ne'] using
          ((continuous_norm.rpow_const fun _ ↦ Or.inr hμ0.le).tendsto (0 : E))
      simpa using this.mul_const (|A| + Real.exp k)
    rw [ContinuousAt, norm_zero, Real.zero_rpow hμ0.ne', zero_mul]
    refine squeeze_zero_norm (fun y ↦ ?_) hlim
    have ht : ⟪e, y⟫_ℝ / ‖y‖ ≤ 1 := (abs_le.1 (abs_inner_div_norm_le_one he y)).2
    have hexp : Real.exp (k * (⟪e, y⟫_ℝ / ‖y‖)) ≤ Real.exp k :=
      Real.exp_le_exp.2 (by nlinarith)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg y) _)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (norm_nonneg y) _)
    rw [abs_le]
    constructor <;> nlinarith [Real.exp_pos (k * (⟪e, y⟫_ℝ / ‖y‖)), le_abs_self A, neg_abs_le A]
  · exact (contDiffAt_norm_rpow_mul_sub_exp hy).continuousAt

/-- **The exterior cone barrier is superharmonic on the cone.** Let `e` be a unit vector, `c` a
real number, `0 < μ ≤ 1`, `dim E - 1 ≤ k (1 - c)`, `exp (k c) ≤ A` and `μ A ≤ k exp (-k)`. Then
the function `x ↦ ‖x - ξ‖ ^ μ (A - exp (k ⟪e, x - ξ⟫ / ‖x - ξ‖))` is superharmonic, that is its
negative is subharmonic, on the open cone `{x | ⟪e, x - ξ⟫ < c ‖x - ξ‖}`. -/
theorem subharmonicOn_neg_norm_sub_rpow_mul_sub_exp (he : ‖e‖ = 1) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (hk : (Module.finrank ℝ E : ℝ) - 1 ≤ k * (1 - c))
    (hA : Real.exp (k * c) ≤ A) (hμA : μ * A ≤ k * Real.exp (-k)) :
    SubharmonicOn (-fun x ↦ ‖x - ξ‖ ^ μ * (A - Real.exp (k * (⟪e, x - ξ⟫_ℝ / ‖x - ξ‖))))
      {x | ⟪e, x - ξ⟫_ℝ < c * ‖x - ξ‖} := by
  have hn : (1 : ℝ) ≤ Module.finrank ℝ E := by
    have : Nontrivial E := ⟨⟨e, 0, fun h ↦ by simp [h] at he⟩⟩
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hk0 : 0 ≤ k := nonneg_of_mul_le_mul_exp_neg hμ0 ((Real.exp_pos _).trans_le hA) hμA
  -- The open cone `V = {⟪e, x - ξ⟫ < c ‖x - ξ‖}` avoids `ξ`.
  set V : Set E := {x | ⟪e, x - ξ⟫_ℝ < c * ‖x - ξ‖} with hV_def
  have hV : IsOpen V := isOpen_lt (by fun_prop) (by fun_prop)
  have hξV : ∀ x ∈ V, x - ξ ≠ 0 := fun x hx h ↦ by simp [hV_def, h] at hx
  -- `-w` has nonnegative Laplacian on `V`, by the zonal formula and the bracket estimate.
  refine ContDiffOn.subharmonicOn_of_laplacian_nonneg (fun x hx ↦
    ((contDiffAt_norm_rpow_mul_sub_exp (hξV x hx)).comp x
      (contDiffAt_id.sub contDiffAt_const)).neg.contDiffWithinAt) hV fun x hx ↦ ?_
  set y := x - ξ
  have hy : y ≠ 0 := hξV x hx
  have hneg : (-fun x ↦ ‖x - ξ‖ ^ μ * (A - Real.exp (k * (⟪e, x - ξ⟫_ℝ / ‖x - ξ‖)))) =
      fun x ↦ (fun y : E ↦ ‖y‖ ^ μ * (Real.exp (k * (⟪e, y⟫_ℝ / ‖y‖)) - A)) (x + -ξ) := by
    funext x
    simp only [Pi.neg_apply, ← sub_eq_add_neg]
    ring
  have hF : ContDiffAt ℝ 2 (fun s ↦ Real.exp (k * s) - A) (⟪e, y⟫_ℝ / ‖y‖) :=
    ((contDiffAt_const.mul contDiffAt_id).exp).sub contDiffAt_const
  have htr := congrFun (laplacian_comp_add_right
    (fun y : E ↦ ‖y‖ ^ μ * (Real.exp (k * (⟪e, y⟫_ℝ / ‖y‖)) - A)) (-ξ)) x
  rw [hneg, htr, ← sub_eq_add_neg,
    laplacian_norm_rpow_mul_comp_inner_div_norm he hy μ hF, deriv_deriv_exp_mul_sub_const,
    deriv_exp_mul_sub_const]
  have htc : ⟪e, y⟫_ℝ / ‖y‖ ≤ c := inner_div_norm_le_of_le_mul_norm hy (le_of_lt hx)
  exact mul_nonneg (Real.rpow_nonneg (norm_nonneg y) _) (zonal_bracket_nonneg hn hμ0 hμ1 hk0 hk
    hA hμA (abs_le.1 (abs_inner_div_norm_le_one he y)).1 htc)

/-- **The exterior cone barrier.** Let `e` be a unit vector and `c` a real number, and suppose
`⟪e, x - ξ⟫ < c ‖x - ξ‖` at every point `x` of `Ω`, so that `Ω` lies in the open cone of axis
`-e` with vertex `ξ` complementary to the closed cone `{c ‖x - ξ‖ ≤ ⟪e, x - ξ⟫}`. Let
`0 < μ ≤ 1`, `dim E - 1 ≤ k (1 - c)`, `exp (k c) < A` and `μ A ≤ k exp (-k)`. Then
`x ↦ ‖x - ξ‖ ^ μ (A - exp (k ⟪e, x - ξ⟫ / ‖x - ξ‖))` is a barrier at `ξ` relative to `Ω`. -/
theorem isBarrier_norm_sub_rpow_mul_sub_exp (he : ‖e‖ = 1) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (hk : (Module.finrank ℝ E : ℝ) - 1 ≤ k * (1 - c))
    (hA : Real.exp (k * c) < A) (hμA : μ * A ≤ k * Real.exp (-k))
    (hcone : ∀ x ∈ Ω, ⟪e, x - ξ⟫_ℝ < c * ‖x - ξ‖) :
    IsBarrier Ω ξ fun x ↦ ‖x - ξ‖ ^ μ * (A - Real.exp (k * (⟪e, x - ξ⟫_ℝ / ‖x - ξ‖))) := by
  have hk0 : 0 ≤ k := nonneg_of_mul_le_mul_exp_neg hμ0 ((Real.exp_pos _).trans hA) hμA
  -- On `closure Ω` the cosine is at most `c`.
  have hcl : closure Ω ⊆ {x | ⟪e, x - ξ⟫_ℝ ≤ c * ‖x - ξ‖} :=
    closure_minimal (fun x hx ↦ (hcone x hx).le) (isClosed_le (by fun_prop) (by fun_prop))
  refine ⟨(subharmonicOn_neg_norm_sub_rpow_mul_sub_exp he hμ0 hμ1 hk hA.le hμA).mono hcone,
    ((continuous_norm_rpow_mul_sub_exp he hμ0 hk0).comp
      (continuous_id.sub continuous_const)).continuousOn,
    by simp [Real.zero_rpow hμ0.ne'], fun x hx hxξ ↦ ?_⟩
  have hy : x - ξ ≠ 0 := sub_ne_zero.2 hxξ
  have htc : ⟪e, x - ξ⟫_ℝ / ‖x - ξ‖ ≤ c := inner_div_norm_le_of_le_mul_norm hy (hcl hx)
  refine mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.2 hy) _) (sub_pos.2 ?_)
  exact (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left htc hk0)).trans_lt hA

/-- **The exterior cone condition gives regularity.** Let `Ω` be open, `e` a unit vector, `c < 1`
and `ρ > 0`, and suppose that the truncated closed cone
`{x | ‖x - ξ‖ < ρ, c ‖x - ξ‖ ≤ ⟪e, x - ξ⟫}` with vertex `ξ` misses `Ω`. Then `ξ` admits a barrier
relative to `Ω`. -/
theorem exists_isBarrier_of_exterior_cone (hΩ : IsOpen Ω) (he : ‖e‖ = 1) (hc : c < 1)
    (hρ : 0 < ρ) (hcone : ∀ x ∈ Ω, dist x ξ < ρ → ⟪e, x - ξ⟫_ℝ < c * ‖x - ξ‖) :
    ∃ w, IsBarrier Ω ξ w := by
  have : Nontrivial E := ⟨⟨e, 0, fun h ↦ by simp [h] at he⟩⟩
  have hn : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hc' : 0 < 1 - c := sub_pos.2 hc
  set k : ℝ := Module.finrank ℝ E / (1 - c)
  set A : ℝ := 2 * Real.exp (k * c)
  have hk : 0 < k := div_pos hn hc'
  have hApos : 0 < A := mul_pos two_pos (Real.exp_pos _)
  have hk1 : (Module.finrank ℝ E : ℝ) - 1 ≤ k * (1 - c) := by
    rw [div_mul_cancel₀ _ hc'.ne']
    linarith
  have hμ0 : 0 < min 1 (k * Real.exp (-k) / A) :=
    lt_min one_pos (div_pos (mul_pos hk (Real.exp_pos _)) hApos)
  have hμA : min 1 (k * Real.exp (-k) / A) * A ≤ k * Real.exp (-k) :=
    (le_div_iff₀ hApos).1 (min_le_right _ _)
  -- The explicit barrier relative to `Ω ∩ ball ξ ρ`, which lies in the open cone.
  have hw := isBarrier_norm_sub_rpow_mul_sub_exp (Ω := Ω ∩ ball ξ ρ) he hμ0 (min_le_left _ _)
    hk1 (by simp only [A]; linarith [Real.exp_pos (k * c)]) hμA
    fun x hx ↦ hcone x hx.1 (mem_ball.1 hx.2)
  exact hw.exists_isBarrier_of_inter hΩ (ball_mem_nhds ξ hρ)

/-- **The Dirichlet problem under the exterior cone condition.** Let `Ω` be a bounded open set
such that every boundary point `ξ` is the vertex of a truncated closed cone missing `Ω`: there are
a unit vector `e`, a number `c < 1` and a radius `ρ > 0` with `⟪e, x - ξ⟫ < c ‖x - ξ‖` for every
`x ∈ Ω` with `‖x - ξ‖ < ρ`. For boundary data `g` continuous on `frontier Ω`, there is a function
harmonic in `Ω`, continuous on `closure Ω` and equal to `g` on `frontier Ω`. -/
theorem exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier_of_exterior_cone
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hext : ∀ ξ ∈ frontier Ω, ∃ e : E, ‖e‖ = 1 ∧ ∃ c < 1, ∃ ρ > 0,
      ∀ x ∈ Ω, dist x ξ < ρ → ⟪e, x - ξ⟫_ℝ < c * ‖x - ξ‖)
    {g : E → ℝ} (hg : ContinuousOn g (frontier Ω)) :
    ∃ u, HarmonicOnNhd u Ω ∧ ContinuousOn u (closure Ω) ∧ EqOn u g (frontier Ω) := by
  refine exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier hΩ hb (fun ξ hξ ↦ ?_) hg
  obtain ⟨e, he, c, hc, ρ, hρ, hcone⟩ := hext ξ hξ
  exact exists_isBarrier_of_exterior_cone hΩ he hc hρ hcone

/-! ### Lipschitz domains -/

section Lipschitz

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- **The Dirichlet problem on a bounded Lipschitz domain.** If `Ω` is a bounded Lipschitz domain,
then for boundary data `g` continuous on `frontier Ω` there is a function harmonic in `Ω`,
continuous on `closure Ω` and equal to `g` on `frontier Ω`. -/
theorem _root_.Set.IsLipschitzDomain.exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier
    (hΩ : Ω.IsLipschitzDomain G) (hb : Bornology.IsBounded Ω)
    {g : E → ℝ} (hg : ContinuousOn g (frontier Ω)) :
    ∃ u, HarmonicOnNhd u Ω ∧ ContinuousOn u (closure Ω) ∧ EqOn u g (frontier Ω) := by
  refine exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier_of_exterior_cone hΩ.isOpen hb
    (fun ξ hξ ↦ ?_) hg
  -- Recentre a chart around `ξ` at `ξ`; it then supplies an exterior cone.
  obtain ⟨e, γ, K, h, r, hc, hξC⟩ := Set.isLipschitzDomain_iff_exists_mem_normalCylinder.1 hΩ ξ hξ
  obtain ⟨e', γ', h', r', hc', heξ⟩ := hc.exists_isLipschitzChart_eq_zero hξC
  exact hc'.exists_inner_sub_lt_mul_norm_sub hξ heξ

end Lipschitz

end TauCeti
