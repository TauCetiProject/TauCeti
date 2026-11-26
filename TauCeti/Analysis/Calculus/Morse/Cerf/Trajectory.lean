/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.OneDimensional
-- Private: used only inside proofs.
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Analysis.Calculus.ContDiff.Prod

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
`TauCeti.exists_eq_birthDeathOrbit_comp_add`. With the transverse quadratic directions of the
splitting lemma added, the trajectories of the product follow from it as in
`TauCeti.exists_eq_birthDeathOrbit_separatedSum`.

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

/-! ### A strictly convex function with two zeros -/

section Convex

variable {φ : ℝ → ℝ} {l u x y : ℝ}

/-- A strictly convex function vanishing to first order at `x` is positive at every other point. -/
private theorem pos_of_strictConvexOn (hφ : StrictConvexOn ℝ (Icc l u) φ) (hx : x ∈ Icc l u)
    (hy : y ∈ Icc l u) (hxy : x ≠ y) (hd : HasDerivAt φ 0 x) (h0 : φ x = 0) : 0 < φ y := by
  obtain ⟨m, hmdef⟩ : ∃ m, m = (x + y) / 2 := ⟨_, rfl⟩
  have hm : m ∈ openSegment ℝ x y := by
    rcases lt_or_gt_of_ne hxy with h | h
    · rw [openSegment_eq_Ioo h]
      constructor <;> linarith
    · rw [openSegment_symm, openSegment_eq_Ioo h]
      constructor <;> linarith
  have hmI : m ∈ Icc l u := (convex_Icc l u).openSegment_subset hx hy hm
  -- The tangent line at `x` is the zero line, so `φ m ≥ 0`.
  have hm0 : 0 ≤ φ m := by
    rcases lt_or_gt_of_ne hxy with h | h
    · have hxm : x < m := by linarith
      have := hφ.convexOn.le_slope_of_hasDerivAt hx hmI hxm hd
      rw [slope_def_field, h0, sub_zero, le_div_iff₀ (sub_pos.2 hxm), zero_mul] at this
      exact this
    · have hmx : m < x := by linarith
      have := hφ.convexOn.slope_le_of_hasDerivAt hmI hx hmx hd
      rw [slope_def_field, h0, zero_sub, div_le_iff₀ (sub_pos.2 hmx), zero_mul] at this
      linarith
  -- By strict convexity, `φ m < max (φ x) (φ y) = max 0 (φ y)`.
  have hlt := hφ.lt_on_openSegment hx hy hxy hm
  rw [h0] at hlt
  rcases lt_max_iff.1 (hm0.trans_lt hlt) with h | h
  · exact absurd h (lt_irrefl 0)
  · exact h

/-- A strictly convex function, differentiable on `[l, u]`, positive at `l` and `u` and negative
at `x ∈ (l, u)`, has exactly two zeros `p < x < q` in `(l, u)`. It is negative between them, with
negative derivative at `p` and positive derivative at `q`. -/
private theorem exists_setOf_eq_zero_eq_pair_of_strictConvexOn (hφ : StrictConvexOn ℝ (Icc l u) φ)
    (hd : ∀ y ∈ Icc l u, DifferentiableAt ℝ φ y) (hl : 0 < φ l) (hu : 0 < φ u)
    (hx : x ∈ Ioo l u) (hφx : φ x < 0) :
    ∃ p ∈ Ioo l x, ∃ q ∈ Ioo x u, {y ∈ Ioo l u | φ y = 0} = {p, q} ∧
      (∀ y ∈ Ioo p q, φ y < 0) ∧ deriv φ p < 0 ∧ 0 < deriv φ q := by
  have hc : ContinuousOn φ (Icc l u) := fun y hy ↦ (hd y hy).continuousAt.continuousWithinAt
  -- A zero on each side of `x`, by the intermediate value theorem.
  obtain ⟨p, hp, hp0⟩ := intermediate_value_Ioo' hx.1.le
    (hc.mono (Icc_subset_Icc_right hx.2.le)) ⟨hφx, hl⟩
  obtain ⟨q, hq, hq0⟩ := intermediate_value_Ioo hx.2.le
    (hc.mono (Icc_subset_Icc_left hx.1.le)) ⟨hφx, hu⟩
  have hpI : p ∈ Icc l u := ⟨hp.1.le, hp.2.le.trans hx.2.le⟩
  have hqI : q ∈ Icc l u := ⟨hx.1.le.trans hq.1.le, hq.2.le⟩
  have hxI : x ∈ Icc l u := Ioo_subset_Icc_self hx
  have hpq : p < q := hp.2.trans hq.1
  -- By strict convexity `φ` is below the chord on a segment whose ends are not positive.
  have hneg : ∀ {a b z : ℝ}, a ∈ Icc l u → b ∈ Icc l u → a < z → z < b → φ a ≤ 0 →
      φ b ≤ 0 → φ z < 0 := by
    intro a b z ha hb haz hzb ha0 hb0
    have hz : z ∈ openSegment ℝ a b := by
      rw [openSegment_eq_Ioo (haz.trans hzb)]
      exact ⟨haz, hzb⟩
    exact (hφ.lt_on_openSegment ha hb (haz.trans hzb).ne hz).trans_le (max_le ha0 hb0)
  have hbetween : ∀ y ∈ Ioo p q, φ y < 0 := fun y hy ↦
    hneg hpI hqI hy.1 hy.2 hp0.le hq0.le
  refine ⟨p, hp, q, hq, Set.ext fun y ↦ ⟨fun ⟨hy, hy0⟩ ↦ ?_, ?_⟩, hbetween, ?_, ?_⟩
  · -- A third zero would make `φ` negative at `p`, at `q` or at itself.
    have hyI : y ∈ Icc l u := Ioo_subset_Icc_self hy
    rcases lt_trichotomy y p with h | rfl | h
    · exact absurd hp0 (hneg hyI hxI h hp.2 hy0.le hφx.le).ne
    · exact .inl rfl
    rcases lt_trichotomy y q with h' | rfl | h'
    · exact absurd hy0 (hbetween y ⟨h, h'⟩).ne
    · exact .inr rfl
    · exact absurd hq0 (hneg hxI hyI hq.1 h' hφx.le hy0.le).ne
  · rintro (rfl | rfl)
    exacts [⟨⟨hp.1, hp.2.trans hx.2⟩, hp0⟩, ⟨⟨hx.1.trans hq.1, hq.2⟩, hq0⟩]
  · -- The derivative at `p` is at most the slope of the chord from `p` to `x`, which is negative.
    have := hφ.convexOn.deriv_le_slope hpI hxI hp.2 (hd p hpI)
    rw [slope_def_field, hp0, sub_zero] at this
    exact this.trans_lt (div_neg_of_neg_of_pos hφx (sub_pos.2 hp.2))
  · -- The derivative at `q` is at least the slope of the chord from `x` to `q`, which is positive.
    have := hφ.convexOn.slope_le_deriv hxI hqI hq.1 (hd q hqI)
    rw [slope_def_field, hq0, zero_sub] at this
    exact (div_pos (neg_pos.2 hφx) (sub_pos.2 hq.1)).trans_le this

end Convex

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
    exact hcont.eventually (lt_mem_nhds (pos_of_strictConvexOn (hconv t ht) hxI hy hyx.symm hd h1))
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
  obtain ⟨p, hp, q, hq, hset, hbetween, hdp, hdq⟩ := exists_setOf_eq_zero_eq_pair_of_strictConvexOn
    hconv (fun y hy ↦ ((hC y hy).derivWithin (m := 2) (by norm_num)).differentiableAt
      (by norm_num)) hl hu ⟨by linarith, by linarith⟩ hneg
  have hp0 := (hset.symm.subset (Or.inl rfl : p ∈ ({p, q} : Set ℝ))).2
  have hq0 := (hset.symm.subset (Or.inr rfl : q ∈ ({p, q} : Set ℝ))).2
  obtain ⟨γ, hγ, -, hmem, hbot, htop, huniq⟩ := exists_isIntegralCurve_neg_gradient_of_deriv_neg
    (hp.2.trans hq.1) (fun y hy ↦ (hC y ⟨by linarith [hy.1, hp.1], by linarith [hy.2, hq.2]⟩).of_le
      (by norm_num)) hp0 hq0 hbetween
  exact ⟨p, q, hp, hq, hset, hdp, hdq, hbetween, γ, hγ, hmem, hbot, htop, huniq⟩

end Birth


end TauCeti
