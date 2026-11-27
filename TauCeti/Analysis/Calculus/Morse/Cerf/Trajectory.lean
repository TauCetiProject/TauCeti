/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.OneDimensional
public import TauCeti.Analysis.Calculus.Morse.Prod
-- Private: used only inside proofs.
import Mathlib.Analysis.Convex.Deriv
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Analysis.Calculus.Morse.GradientFlow
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
`TauCeti.exists_eq_birthDeathOrbit_comp_add`.

**Transverse directions.** In the splitting chart of a birth–death point
(`TauCeti.exists_normalized_splitting_chart_of_ker_eq_span_singleton`) the family becomes
`(a, b) ↦ g s a + Q b`, where `g` is the reduced family of one variable and `Q` a nondegenerate
quadratic form in the transverse coordinates `b`; Cerf's normal form is the case
`g s a = a³ / 3 - s a`. For such separated sums, on the `L²` product of `ℝ` with a real Hilbert
space `F` and for any differentiable `Q`, the birth looks the same
(`TauCeti.exists_pos_eventually_setOf_fderiv_separatedSum_eq_zero_and_isIntegralCurve`): in the
slab `(x - r, x + r) × F` the critical points are the points `(p, b)` and `(q, b)` above the
critical points `b` of `Q`, and the negative gradient trajectories of the separated sum from
`(p, b)` to `(q, b)` are the time translates of `σ ↦ (γ σ, b)`. Their transverse component is
constant because a negative gradient trajectory of `Q` with the same limit at both ends is constant;
the first component of a trajectory of the separated sum is a trajectory of `g s` wherever it goes
(`IsIntegralCurve.fst_of_separatedSum`), so the uniqueness holds among all trajectories, not only
those in the slab. When `F` is finite-dimensional the two critical points above `b` have Morse
indices `ind_Q(b) + 1` and `ind_Q(b)`
(`TauCeti.exists_pos_eventually_morseIndex_separatedSum_toLp`), as in Cerf's normal form. These
statements use the product metric of the chart coordinates; the comparison with the trajectories
of another metric is not treated here.

## Main results

* `TauCeti.exists_pos_eventually_setOf_deriv_eq_zero_eq_pair_and_isIntegralCurve`: the two critical
  points born at a birth in one variable and the trajectory joining them.
* `TauCeti.exists_pos_eventually_setOf_fderiv_separatedSum_eq_zero_and_isIntegralCurve`: the same
  with transverse directions: the critical points of `(a, b) ↦ g s a + Q b` near the birth and
  the trajectories joining the newborn pairs.
* `TauCeti.exists_pos_eventually_morseIndex_separatedSum_toLp`: their Morse indices.

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


/-- The conclusion of
`TauCeti.exists_pos_eventually_setOf_deriv_eq_zero_eq_pair_and_isIntegralCurve` for one function
`φ` of the family, on an interval `[x - r, x + r]` on which `φ` is `C³`, with a
strictly convex derivative, positive at both ends and negative at `x`. -/
private theorem exists_setOf_deriv_eq_zero_eq_pair_and_isIntegralCurve {φ : ℝ → ℝ} {r : ℝ}
    (hr : 0 < r) (hC : ∀ y ∈ Icc (x - r) (x + r), ContDiffAt ℝ 3 φ y)
    (hconv : StrictConvexOn ℝ (Icc (x - r) (x + r)) (deriv φ)) (hl : 0 < deriv φ (x - r))
    (hu : 0 < deriv φ (x + r)) (hneg : deriv φ x < 0) :
    ∃ p q : ℝ, p ∈ Ioo (x - r) x ∧ q ∈ Ioo x (x + r) ∧
      {y ∈ Ioo (x - r) (x + r) | deriv φ y = 0} = {p, q} ∧
      deriv (deriv φ) p < 0 ∧ 0 < deriv (deriv φ) q ∧
      (∀ y ∈ Ioo p q, deriv φ y < 0) ∧
      ∃ γ : ℝ → ℝ, IsIntegralCurve γ (fun _ y ↦ -∇ φ y) ∧ (∀ σ, γ σ ∈ Ioo p q) ∧
        Tendsto γ atBot (𝓝 p) ∧ Tendsto γ atTop (𝓝 q) ∧
        ∀ δ : ℝ → ℝ, IsIntegralCurve δ (fun _ y ↦ -∇ φ y) → Tendsto δ atBot (𝓝 p) →
          Tendsto δ atTop (𝓝 q) → ∃ τ, δ = fun σ ↦ γ (σ + τ) := by
  -- The two zeros of the strictly convex function `φ'`, and the trajectory joining them.
  obtain ⟨p, hp, q, hq, hset, hp0, hq0, hbetween, hdp, hdq⟩ := hconv.exists_setOf_eq_zero_eq_pair
    (fun y hy ↦ ((hC y hy).derivWithin (m := 2) (by norm_num)).differentiableAt (by norm_num))
    hl hu ⟨by linarith, by linarith⟩ hneg
  obtain ⟨γ, hγ, -, hmem, hbot, htop, huniq⟩ := exists_isIntegralCurve_neg_gradient_of_deriv_neg
    (hp.2.trans hq.1) (fun y hy ↦ (hC y ⟨by linarith [hy.1, hp.1], by linarith [hy.2, hq.2]⟩).of_le
      (by norm_num)) hp0 hq0 hbetween
  exact ⟨p, q, hp, hq, hset, hdp, hdq, hbetween, γ, hγ, hmem, hbot, htop, huniq⟩

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
  exact exists_setOf_deriv_eq_zero_eq_pair_and_isIntegralCurve hr hC hconv hl hu hneg

end Birth

/-! ### The birth with transverse directions -/

section Transverse

variable {g : ℝ → ℝ → ℝ} {t x : ℝ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {Q : F → ℝ}

/-- **The birth in the presence of transverse directions.** Let `g s` be a family of functions of
one variable as in `TauCeti.exists_pos_eventually_setOf_deriv_eq_zero_eq_pair_and_isIntegralCurve`,
jointly `C³` at `(t, x)` with `(g t)'(x) = 0`, `(g t)''(x) = 0` and `0 < (g t)'''(x)`, and let `Q`
be a differentiable function on a real Hilbert space `F`. Consider the separated sums
`(a, b) ↦ g s a + Q b` on `ℝ × F`, with the `L²` product metric. There is `r > 0` such that, for
every `s` close to `t` with `(g s)'(x) < 0`, there are `p < x < q` in `(x - r, x + r)` with:

* the critical points of the separated sum in the slab `(x - r, x + r) × F` are the points `(p, b)`
  and `(q, b)` with `b` a critical point of `Q`; they are nondegenerate when `b` is;
* there is a negative gradient trajectory `γ` of `g s` with values in `(p, q)`, from `p` to `q`,
  such that for every critical point `b` of `Q` the curve `σ ↦ (γ σ, b)` is a negative gradient
  trajectory of the separated sum, and every negative gradient trajectory of the separated sum
  from `(p, b)` to `(q, b)` is one of its time translates.

The uniqueness is global: it concerns all trajectories of the separated sum in `ℝ × F`, not only
those in the slab. -/
theorem exists_pos_eventually_setOf_fderiv_separatedSum_eq_zero_and_isIntegralCurve
    [CompleteSpace F] (hg : ContDiffAt ℝ 3 (uncurry g) (t, x)) (h1 : deriv (g t) x = 0)
    (h2 : deriv (deriv (g t)) x = 0) (h3 : 0 < deriv (deriv (deriv (g t))) x)
    (hQ : Differentiable ℝ Q) :
    ∃ r > 0, ∀ᶠ s in 𝓝 t, deriv (g s) x < 0 → ∃ p q : ℝ,
      p ∈ Ioo (x - r) x ∧ q ∈ Ioo x (x + r) ∧
      {z : WithLp 2 (ℝ × F) | z.fst ∈ Ioo (x - r) (x + r) ∧
          fderiv ℝ (separatedSum (g s) Q) z = 0} =
        {z | (z.fst = p ∨ z.fst = q) ∧ fderiv ℝ Q z.snd = 0} ∧
      (∀ b, IsNondegenerateCriticalPoint Q b →
        IsNondegenerateCriticalPoint (separatedSum (g s) Q) (WithLp.toLp 2 (p, b)) ∧
          IsNondegenerateCriticalPoint (separatedSum (g s) Q) (WithLp.toLp 2 (q, b))) ∧
      ∃ γ : ℝ → ℝ, IsIntegralCurve γ (fun _ a ↦ -∇ (g s) a) ∧ (∀ σ, γ σ ∈ Ioo p q) ∧
        Tendsto γ atBot (𝓝 p) ∧ Tendsto γ atTop (𝓝 q) ∧
        ∀ b, fderiv ℝ Q b = 0 →
          IsIntegralCurve (fun σ ↦ WithLp.toLp 2 (γ σ, b))
            (fun _ w ↦ -∇ (separatedSum (g s) Q) w) ∧
          ∀ z : ℝ → WithLp 2 (ℝ × F),
            IsIntegralCurve z (fun _ w ↦ -∇ (separatedSum (g s) Q) w) →
            Tendsto z atBot (𝓝 (WithLp.toLp 2 (p, b))) →
            Tendsto z atTop (𝓝 (WithLp.toLp 2 (q, b))) →
            ∃ τ, z = fun σ ↦ WithLp.toLp 2 (γ (σ + τ), b) := by
  obtain ⟨r, hr, hev⟩ := exists_pos_eventually_strictConvexOn_deriv hg h1 h2 h3
  refine ⟨r, hr, ?_⟩
  filter_upwards [hev] with s ⟨hC, hconv, hl, hu⟩ hneg
  obtain ⟨p, q, hp, hq, hset, hdp, hdq, -, γ, hγ, hmem, hbot, htop, huniq⟩ :=
    exists_setOf_deriv_eq_zero_eq_pair_and_isIntegralCurve hr hC hconv hl hu hneg
  have hdiff (a : ℝ) (ha : a ∈ Ioo (x - r) (x + r)) : DifferentiableAt ℝ (g s) a :=
    (hC a (Ioo_subset_Icc_self ha)).differentiableAt (by norm_num)
  -- On the line, the differential vanishes exactly when the derivative does.
  have hfderiv (a : ℝ) : fderiv ℝ (g s) a = 0 ↔ deriv (g s) a = 0 := by
    rw [← toSpanSingleton_deriv]
    exact ⟨fun h ↦ by simpa using congrArg (· 1) h, fun h ↦ by simp [h]⟩
  have hpq : p ∈ Ioo (x - r) (x + r) ∧ deriv (g s) p = 0 ∧ q ∈ Ioo (x - r) (x + r) ∧
      deriv (g s) q = 0 := by
    have hp' : p ∈ {y ∈ Ioo (x - r) (x + r) | deriv (g s) y = 0} := hset ▸ Or.inl rfl
    have hq' : q ∈ {y ∈ Ioo (x - r) (x + r) | deriv (g s) y = 0} := hset ▸ Or.inr rfl
    exact ⟨hp'.1, hp'.2, hq'.1, hq'.2⟩
  obtain ⟨hpI, hp0, hqI, hq0⟩ := hpq
  -- The two critical points of `g s` are nondegenerate.
  have hnd (a : ℝ) (ha : a ∈ Ioo (x - r) (x + r)) (h0 : deriv (g s) a = 0)
      (hd2 : deriv (deriv (g s)) a ≠ 0) : IsNondegenerateCriticalPoint (g s) a :=
    (isNondegenerateCriticalPoint_real_iff ((hC a (Ioo_subset_Icc_self ha)).of_le
      (by norm_num))).2 ⟨h0, by rwa [iteratedDeriv_succ, iteratedDeriv_one]⟩
  -- Along `γ` the function `g s` is differentiable, since `γ` stays in `(p, q)`.
  have hγd (σ : ℝ) : DifferentiableAt ℝ (g s) (γ σ) :=
    hdiff _ ⟨hpI.1.trans (hmem σ).1, (hmem σ).2.trans hqI.2⟩
  refine ⟨p, q, hp, hq, ?_, fun b hb ↦ ⟨(hnd p hpI hp0 hdp.ne).separatedSum hb,
    (hnd q hqI hq0 hdq.ne').separatedSum hb⟩, γ, hγ, hmem, hbot, htop, fun b hb ↦ ⟨?_, ?_⟩⟩
  · -- The critical points of the separated sum in the slab.
    ext z
    constructor
    · rintro ⟨hz, hz0⟩
      rw [fderiv_separatedSum_eq_zero_iff (hdiff _ hz) (hQ _), hfderiv] at hz0
      have hz' : z.fst ∈ ({p, q} : Set ℝ) := hset ▸ ⟨hz, hz0.1⟩
      exact ⟨hz', hz0.2⟩
    · rintro ⟨hz | hz, hz0⟩
      · exact ⟨hz ▸ hpI, (fderiv_separatedSum_eq_zero_iff (hdiff _ (hz ▸ hpI)) (hQ _)).2
          ⟨(hfderiv _).2 (hz ▸ hp0), hz0⟩⟩
      · exact ⟨hz ▸ hqI, (fderiv_separatedSum_eq_zero_iff (hdiff _ (hz ▸ hqI)) (hQ _)).2
          ⟨(hfderiv _).2 (hz ▸ hq0), hz0⟩⟩
  · -- The trajectory `σ ↦ (γ σ, b)`.
    have hb' : ∇ Q b = 0 := by rw [gradient, hb, map_zero]
    exact hγ.separatedSum (isIntegralCurve_const_neg_gradient_iff.2 hb') hγd fun _ ↦ hQ _
  · -- Every trajectory from `(p, b)` to `(q, b)` is a translate of it.
    exact fun z hz ↦ hz.exists_eq_toLp_comp_add_of_separatedSum hQ hγd huniq

/-- **The Morse indices of the two critical points born at a birth, with transverse directions.**
In the situation of
`TauCeti.exists_pos_eventually_setOf_fderiv_separatedSum_eq_zero_and_isIntegralCurve`, on a
finite-dimensional space `F`: there is `r > 0` such that, for every `s` close to `t` with
`(g s)'(x) < 0`, the two critical points `p < x < q` of `g s` in `(x - r, x + r)` give, above every
point `b` at which `Q` is `C²`, points `(p, b)` and `(q, b)` of Morse indices `ind_Q(b) + 1` and
`ind_Q(b)` for the separated sum `(a, b) ↦ g s a + Q b`. -/
theorem exists_pos_eventually_morseIndex_separatedSum_toLp [FiniteDimensional ℝ F]
    (hg : ContDiffAt ℝ 3 (uncurry g) (t, x)) (h1 : deriv (g t) x = 0)
    (h2 : deriv (deriv (g t)) x = 0) (h3 : 0 < deriv (deriv (deriv (g t))) x) :
    ∃ r > 0, ∀ᶠ s in 𝓝 t, deriv (g s) x < 0 → ∃ p q : ℝ,
      p ∈ Ioo (x - r) x ∧ q ∈ Ioo x (x + r) ∧
      {a ∈ Ioo (x - r) (x + r) | deriv (g s) a = 0} = {p, q} ∧
      ∀ b, ContDiffAt ℝ 2 Q b →
        morseIndex (separatedSum (g s) Q) (WithLp.toLp 2 (p, b)) = morseIndex Q b + 1 ∧
          morseIndex (separatedSum (g s) Q) (WithLp.toLp 2 (q, b)) = morseIndex Q b := by
  obtain ⟨r, hr, hev⟩ := exists_pos_eventually_strictConvexOn_deriv hg h1 h2 h3
  refine ⟨r, hr, ?_⟩
  filter_upwards [hev] with s ⟨hC, hconv, hl, hu⟩ hneg
  obtain ⟨p, q, hp, hq, hset, hdp, hdq, -⟩ :=
    exists_setOf_deriv_eq_zero_eq_pair_and_isIntegralCurve hr hC hconv hl hu hneg
  have hC2 (a : ℝ) (ha : a ∈ Ioo (x - r) (x + r)) : ContDiffAt ℝ 2 (g s) a :=
    (hC a (Ioo_subset_Icc_self ha)).of_le (by norm_num)
  have hpI : p ∈ Ioo (x - r) (x + r) := ⟨hp.1, by linarith [hp.2, hq.1, hq.2]⟩
  have hqI : q ∈ Ioo (x - r) (x + r) := ⟨by linarith [hp.1, hp.2, hq.1], hq.2⟩
  refine ⟨p, q, hp, hq, hset, fun b hb ↦ ⟨?_, ?_⟩⟩
  · rw [morseIndex_separatedSum (hC2 p hpI) hb, morseIndex_real_of_neg (by
      rwa [iteratedDeriv_succ, iteratedDeriv_one]), add_comm, WithLp.toLp_snd]
  · rw [morseIndex_separatedSum (hC2 q hqI) hb, morseIndex_real_of_pos (by
      rwa [iteratedDeriv_succ, iteratedDeriv_one]), zero_add, WithLp.toLp_snd]

end Transverse

end TauCeti
