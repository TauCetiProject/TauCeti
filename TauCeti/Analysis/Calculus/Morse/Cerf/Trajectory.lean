/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.OneDimensional
-- Private: used only inside proofs.
import Mathlib.Analysis.Convex.Deriv
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Analysis.Convex.Deriv
import TauCeti.Analysis.Convex.StrictTangent

/-!
# The trajectory joining the two critical points born at a birth

Let `g s : ℝ → ℝ` be a one-parameter family of functions of one variable, jointly `C³` near
`(t, x)`, where `x` is a critical point of `g t` with

`(g t)'(x) = 0`, `(g t)''(x) = 0`, `0 < (g t)'''(x)`.

This is the situation at a birth–death point after the splitting lemma: the reduced family of
`TauCeti.exists_normalized_splitting_chart_of_ker_eq_span_singleton` has these derivatives at
`(t, 0)`, up to the sign of the third derivative, which changes when the kernel vector is replaced
by its negative. Near `x`, the derivative `(g s)'` is strictly convex for `s` close to `t`, since
its second derivative `(g s)'''` is positive, and it is positive at the two ends of a fixed
interval `(x - r, x + r)`, since `(g t)'` vanishes to second order at `x` only. Therefore, for
every `s` close to `t` at which `(g s)'(x) < 0` (on one side of `t` when the family is
transverse, `∂ₛ (g s)'(x) ≠ 0`), the function `g s` has exactly two critical points `p < x < q`
in `(x - r, x + r)`: a nondegenerate local maximum `p`, with `(g s)''(p) < 0`, and a nondegenerate
local minimum `q`, with `0 < (g s)''(q)`, and `g s` decreases between them. They are the two
critical points born at the birth, as in Cerf's model `x³ / 3 - s x`, and they are joined by
exactly one unparametrized negative gradient trajectory of `g s`
(`TauCeti.exists_pos_eventually_setOf_deriv_eq_zero_eq_pair_and_isIntegralCurve`), by
`TauCeti.exists_isIntegralCurve_neg_gradient_of_deriv_neg`.

This is the local trajectory statement at a birth for an arbitrary family, not only for the
model `TauCeti.birthDeathPotential`, in which it is
`TauCeti.exists_eq_birthDeathOrbit_comp_add`. The trajectories of the full family in the
splitting chart, with the transverse quadratic directions added, are not treated here.

## Main results

* `TauCeti.exists_pos_eventually_setOf_deriv_eq_zero_eq_pair_and_isIntegralCurve`: the two critical
  points born at a birth in one variable and the trajectory joining them.

## References

* J. Cerf, *La stratification naturelle des espaces de fonctions différentiables réelles et le
  théorème de la pseudo-isotopie*, Publ. Math. IHÉS **39** (1970), 5–173, Chapter III.
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4 (births and deaths in generic one-parameter families).
-/

public section

open Filter Function Set
open scoped Topology Gradient

namespace TauCeti

/-! ### The pair born at a birth -/

section Birth

variable {g : ℝ → ℝ → ℝ} {t x : ℝ}

/-- Near `(t, x)`, where `(g t)'` vanishes to second order and `0 < (g t)'''`, there is `r > 0`
such that for `s` close to `t` the function `g s` is `C³` on `[x - r, x + r]`, its derivative is
strictly convex there and positive at both ends. -/
private theorem exists_pos_eventually_strictConvexOn_deriv
    (hg : ContDiffAt ℝ 3 (uncurry g) (t, x)) (h1 : deriv (g t) x = 0)
    (h2 : deriv (deriv (g t)) x = 0) (h3 : 0 < deriv (deriv (deriv (g t))) x) :
    ∃ r > 0, ∀ᶠ s in 𝓝 t, (∀ y ∈ Icc (x - r) (x + r), ContDiffAt ℝ 3 (g s) y) ∧
      StrictConvexOn ℝ (Icc (x - r) (x + r)) (deriv (g s)) ∧
      0 < deriv (g s) (x - r) ∧ 0 < deriv (g s) (x + r) := by
  -- A square around `(t, x)` on which the family is `C³`, with positive third derivative.
  have hD : ContinuousAt (uncurry fun s ↦ deriv (deriv (deriv (g s)))) (t, x) :=
    (((hg.contDiffAt_deriv_snd (m := 2) (by norm_num)).contDiffAt_deriv_snd (m := 1)
      (by norm_num)).contDiffAt_deriv_snd (m := 0) (by norm_num)).continuousAt
  obtain ⟨ρ, hρ, hbox⟩ := Metric.eventually_nhds_iff.1 ((hg.eventually (by simp)).and
    (hD.eventually (lt_mem_nhds h3)))
  refine ⟨ρ / 2, half_pos hρ, ?_⟩
  have hρI : ∀ s, |s - t| < ρ → ∀ y ∈ Icc (x - ρ / 2) (x + ρ / 2), dist (s, y) (t, x) < ρ :=
    fun s hs y hy ↦ by
      rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt (a := y - x)]
      exact ⟨hs, by linarith [hy.1], by linarith [hy.2]⟩
  -- On that square, `(g s)'` is strictly convex on `[x - r, x + r]`, since `0 < (g s)'''`.
  have hconv : ∀ s, |s - t| < ρ → StrictConvexOn ℝ (Icc (x - ρ / 2) (x + ρ / 2)) (deriv (g s)) :=
    fun s hs ↦ strictConvexOn_of_deriv2_pos' (convex_Icc _ _)
      (fun y hy ↦ (((hbox (hρI s hs y hy)).1.uncurry_left.derivWithin (m := 2)
        (by norm_num)).continuousAt).continuousWithinAt) fun y hy ↦ (hbox (hρI s hs y hy)).2
  -- `(g t)'` is positive away from `x`, so `(g s)'` is positive at `x ± r` for `s` close to `t`.
  have hxI : x ∈ Icc (x - ρ / 2) (x + ρ / 2) := ⟨by linarith, by linarith⟩
  have ht : |t - t| < ρ := by simpa using hρ
  have hend : ∀ y ∈ Icc (x - ρ / 2) (x + ρ / 2), y ≠ x → ∀ᶠ s in 𝓝 t, 0 < deriv (g s) y := by
    intro y hy hyx
    have hC : ContDiffAt ℝ 3 (g t) x := (hbox (hρI t ht x hxI)).1.uncurry_left
    have hd : HasDerivAt (deriv (g t)) 0 x :=
      h2 ▸ ((hC.derivWithin (m := 2) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
    have hcont : ContinuousAt (fun s ↦ uncurry (fun s ↦ deriv (g s)) (s, y)) t :=
      ((hbox (hρI t ht y hy)).1.contDiffAt_deriv_snd (m := 0) (by norm_num)).continuousAt.comp
        (f := fun s ↦ (s, y)) (by fun_prop)
    have h := (hconv t ht).mul_sub_lt_sub_of_hasDerivWithinAt hxI hy hyx.symm hd.hasDerivWithinAt
    rw [zero_mul, h1, sub_zero] at h
    exact hcont.eventually (lt_mem_nhds h)
  have hts : ∀ᶠ s in 𝓝 t, |s - t| < ρ := by
    filter_upwards [Metric.ball_mem_nhds t hρ] with s hs
    rwa [Metric.mem_ball, Real.dist_eq] at hs
  filter_upwards [hts, hend (x - ρ / 2) ⟨le_rfl, by linarith⟩ (by linarith),
    hend (x + ρ / 2) ⟨by linarith, le_rfl⟩ (by linarith)] with s hs hl hu
  exact ⟨fun y hy ↦ (hbox (hρI s hs y hy)).1.uncurry_left, hconv s hs, hl, hu⟩

/-- **The two critical points born at a birth, and the trajectory joining them.** Let `g s` be a
family of functions of one variable, jointly `C³` at `(t, x)`, where `(g t)'(x) = 0`,
`(g t)''(x) = 0` and `0 < (g t)'''(x)`. Then there is `r > 0` such that, for every `s` close to `t`
with `(g s)'(x) < 0`:

* the critical points of `g s` in `(x - r, x + r)` are exactly two points `p < x < q`, with
  `(g s)''(p) < 0 < (g s)''(q)`, and `(g s)' < 0` on `(p, q)`;
* there is a negative gradient trajectory `γ` of `g s` with values in `(p, q)`, tending to `p` at
  `-∞` and to `q` at `+∞`, and every negative gradient trajectory of `g s` tending to `p` at `-∞`
  and to `q` at `+∞` is a time translate of `γ`. -/
theorem exists_pos_eventually_setOf_deriv_eq_zero_eq_pair_and_isIntegralCurve
    (hg : ContDiffAt ℝ 3 (uncurry g) (t, x)) (h1 : deriv (g t) x = 0)
    (h2 : deriv (deriv (g t)) x = 0) (h3 : 0 < deriv (deriv (deriv (g t))) x) :
    ∃ r > 0, ∀ᶠ s in 𝓝 t, deriv (g s) x < 0 → ∃ p q : ℝ,
      p ∈ Ioo (x - r) x ∧ q ∈ Ioo x (x + r) ∧
      {y ∈ Ioo (x - r) (x + r) | deriv (g s) y = 0} = {p, q} ∧
      deriv (deriv (g s)) p < 0 ∧ 0 < deriv (deriv (g s)) q ∧
      (∀ y ∈ Ioo p q, deriv (g s) y < 0) ∧
      ∃ γ : ℝ → ℝ, IsIntegralCurve γ (fun _ y ↦ -∇ (g s) y) ∧ (∀ σ, γ σ ∈ Ioo p q) ∧
        Tendsto γ atBot (𝓝 p) ∧ Tendsto γ atTop (𝓝 q) ∧
        ∀ δ : ℝ → ℝ, IsIntegralCurve δ (fun _ y ↦ -∇ (g s) y) → Tendsto δ atBot (𝓝 p) →
          Tendsto δ atTop (𝓝 q) → ∃ τ, δ = fun σ ↦ γ (σ + τ) := by
  obtain ⟨r, hr, hev⟩ := exists_pos_eventually_strictConvexOn_deriv hg h1 h2 h3
  refine ⟨r, hr, ?_⟩
  filter_upwards [hev] with s ⟨hC, hconv, hl, hu⟩ hneg
  -- The two zeros of the strictly convex function `(g s)'`, and the trajectory joining them.
  obtain ⟨p, hp, q, hq, hset, hp0, hq0, hbetween, hdp, hdq⟩ := hconv.exists_setOf_eq_zero_eq_pair
    (fun y hy ↦ ((hC y hy).derivWithin (m := 2) (by norm_num)).differentiableAt (by norm_num))
    hl hu ⟨by linarith, by linarith⟩ hneg
  obtain ⟨γ, hγ, -, hmem, hbot, htop, huniq⟩ := exists_isIntegralCurve_neg_gradient_of_deriv_neg
    (hp.2.trans hq.1) (fun y hy ↦ (hC y ⟨by linarith [hy.1, hp.1], by linarith [hy.2, hq.2]⟩).of_le
      (by norm_num)) hp0 hq0 hbetween
  exact ⟨p, q, hp, hq, hset, hdp, hdq, hbetween, γ, hγ, hmem, hbot, htop, huniq⟩

end Birth

end TauCeti
