/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.Analysis.Convex.StrictConvexSpace

/-!
# The Hopf–Lax formula and its subsolution inequality

For a Lagrangian `L : E → ℝ` and an initial datum `φ : E → ℝ` on a real vector space, the
*Hopf–Lax formula*

`u (t, x) = inf_y (φ y + t L ((x - y) / t))`

defines, for `t > 0`, the value function of the control problem with running cost `L` and initial
cost `φ`. For convex `L` it is the candidate solution of the Hamilton–Jacobi equation
`∂ₜ u + H (∇ₓ u) = 0` with `H` the convex conjugate of `L`. This file proves the inequality that
makes `u` a subsolution of that equation without any differentiability:

`u (t + h, x + h w) ≤ u (t, x) + h L w` for `t > 0`, `h ≥ 0` and every velocity `w`.

It is the statement that moving at velocity `w` for time `h` costs at most `h L w`. At a point where
`u` is differentiable it gives `∂ₜ u + ⟨∇ₓ u, w⟩ ≤ L w` for every `w`, that is
`∂ₜ u + H (∇ₓ u) ≤ 0`, and the inequality survives averaging `u` against a probability kernel in
space-time. This is the form in which Hopf–Lax functions are tested against solutions of the
continuity equation to bound transport costs by the kinetic action, as in the lower bound of the
Benamou–Brenier formula for the cost `L w = ‖w‖ ^ p`.

The infimum is taken in `ℝ`, so the results assume `φ` and `L` bounded below, which makes it finite
for `t ≥ 0`. At `t = 0` the formula degenerates to the infimum of `φ`; the Hopf–Lax function
recovers `φ` as a limit `t → 0⁺` only under additional hypotheses. For the cost `‖w‖ ^ p` with
`1 < p`, this holds at every point where `φ` is lower semicontinuous, and for a bounded `φ` the
Hopf–Lax function is jointly continuous at positive times, whatever the regularity of `φ`. Times
`t < 0` are not studied here.

## Main definitions

* `TauCeti.hopfLax L φ t x`: the Hopf–Lax value `inf_y (φ y + t L (t⁻¹ (x - y)))`.

## Main results

* `TauCeti.hopfLax_le` and `TauCeti.le_hopfLax_iff`: the Hopf–Lax value is the greatest lower bound
  of the penalized values.
* `TauCeti.hopfLax_mono`: the Hopf–Lax value is monotone in the Lagrangian and initial datum.
* `TauCeti.hopfLax_le_add_mul` and `TauCeti.add_mul_le_hopfLax`: the bounds
  `m + t l ≤ u (t, x) ≤ φ x + t L 0` for lower bounds `m` of `φ` and `l` of `L`.
* `TauCeti.hopfLax_add_add_smul_le`: the subsolution inequality
  `u (t + h, x + h w) ≤ u (t, x) + h L w` for convex `L`.
* `TauCeti.antitoneOn_hopfLax`: for convex `L` with `L 0 ≤ 0`, `u (t, x)` decreases in `t > 0`.
* `TauCeti.upperSemicontinuousOn_hopfLax`: for continuous `L`, `u` is jointly upper semicontinuous
  on the open half-space `t > 0`.
* `TauCeti.hopfLax_norm_rpow` and `TauCeti.hopfLax_norm_rpow_add_add_smul_le`: for the cost
  `L w = ‖w‖ ^ p`, the formula reads `u (t, x) = inf_y (φ y + ‖x - y‖ ^ p / t ^ (p - 1))`, and the
  subsolution inequality holds in real seminormed spaces for `1 ≤ p`.
* `TauCeti.hopfLax_norm_rpow_le` and `TauCeti.abs_hopfLax_norm_rpow_le`: for the cost `‖w‖ ^ p`
  with `p > 0`, `u (t, x) ≤ φ x`, and `u` is bounded by any bound of `φ`.
* `TauCeti.lowerSemicontinuousOn_hopfLax_norm_rpow` and `TauCeti.continuousOn_hopfLax_norm_rpow`:
  for `1 ≤ p` and bounded `φ`, `u` is jointly continuous on the open half-space `t > 0`; in
  particular it is continuous in space at each time `t > 0`
  (`TauCeti.continuous_hopfLax_norm_rpow`).
* `TauCeti.tendsto_hopfLax_norm_rpow_nhdsGT_zero`: for `1 < p` and `φ` bounded below,
  `u (t, x) → φ x` as `t → 0⁺` at every point `x` where `φ` is lower semicontinuous.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society 2010, §3.3.2, on the Hopf–Lax formula.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 7.
-/

public section

noncomputable section

open Set Filter Topology

namespace TauCeti

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {L φ : E → ℝ} {t h : ℝ}

/-- The *Hopf–Lax value* `inf_y (φ y + t L (t⁻¹ (x - y)))` of the initial datum `φ` for the
Lagrangian `L` at time `t` and position `x`. The infimum is taken in `ℝ`; it is the honest infimum
when `φ` and `L` are bounded below and `t ≥ 0`. -/
def hopfLax (L φ : E → ℝ) (t : ℝ) (x : E) : ℝ :=
  ⨅ y, φ y + t * L (t⁻¹ • (x - y))

/-- The defining formula of the Hopf–Lax value. -/
theorem hopfLax_def (L φ : E → ℝ) (t : ℝ) (x : E) :
    hopfLax L φ t x = ⨅ y, φ y + t * L (t⁻¹ • (x - y)) :=
  (rfl)

/-- At time `1` the Hopf–Lax value is the infimal convolution `inf_y (φ y + L (x - y))`. -/
@[simp]
theorem hopfLax_one (L φ : E → ℝ) (x : E) : hopfLax L φ 1 x = ⨅ y, φ y + L (x - y) := by
  simp [hopfLax_def]

/-- For `t ≥ 0` and `φ`, `L` bounded below, the penalized values are bounded below. -/
private theorem bddBelow_range_penalty (hφ : BddBelow (range φ)) (hL : BddBelow (range L))
    (ht : 0 ≤ t) (x : E) : BddBelow (range fun y ↦ φ y + t * L (t⁻¹ • (x - y))) := by
  obtain ⟨m, hm⟩ := hφ
  obtain ⟨l, hl⟩ := hL
  exact ⟨m + t * l, forall_mem_range.2 fun y ↦
    add_le_add (hm (mem_range_self y)) (mul_le_mul_of_nonneg_left (hl (mem_range_self _)) ht)⟩

/-- The Hopf–Lax value is at most the penalized value at any point `y`. -/
theorem hopfLax_le (hφ : BddBelow (range φ)) (hL : BddBelow (range L)) (ht : 0 ≤ t) (x y : E) :
    hopfLax L φ t x ≤ φ y + t * L (t⁻¹ • (x - y)) :=
  ciInf_le (bddBelow_range_penalty hφ hL ht x) y

/-- A lower bound for every penalized value is a lower bound for the Hopf–Lax value. -/
theorem le_hopfLax {c : ℝ} {x : E} (h : ∀ y, c ≤ φ y + t * L (t⁻¹ • (x - y))) :
    c ≤ hopfLax L φ t x :=
  le_ciInf h

/-- The Hopf–Lax value is the greatest lower bound of the penalized values. -/
theorem le_hopfLax_iff (hφ : BddBelow (range φ)) (hL : BddBelow (range L)) (ht : 0 ≤ t)
    {c : ℝ} {x : E} : c ≤ hopfLax L φ t x ↔ ∀ y, c ≤ φ y + t * L (t⁻¹ • (x - y)) :=
  ⟨fun hc y ↦ hc.trans (hopfLax_le hφ hL ht x y), le_hopfLax⟩

/-- The Hopf–Lax value lies below the initial datum plus the cost `t L 0` of staying put. -/
theorem hopfLax_le_add_mul (hφ : BddBelow (range φ)) (hL : BddBelow (range L)) (ht : 0 ≤ t)
    (x : E) : hopfLax L φ t x ≤ φ x + t * L 0 := by
  simpa using hopfLax_le hφ hL ht x x

/-- The Hopf–Lax value is monotone in the Lagrangian and initial datum at nonnegative times. -/
theorem hopfLax_mono {K ψ : E → ℝ} (hφ : BddBelow (range φ)) (hL : BddBelow (range L))
    (ht : 0 ≤ t) (hLK : L ≤ K) (hφψ : φ ≤ ψ) (x : E) :
    hopfLax L φ t x ≤ hopfLax K ψ t x :=
  ciInf_mono (bddBelow_range_penalty hφ hL ht x) fun y ↦
    add_le_add (hφψ y) (mul_le_mul_of_nonneg_left (hLK _) ht)

/-- For lower bounds `m` of `φ` and `l` of `L`, the Hopf–Lax value at time `t ≥ 0` is at least
`m + t l`. -/
theorem add_mul_le_hopfLax {m l : ℝ} (hm : ∀ y, m ≤ φ y) (hl : ∀ w, l ≤ L w) (ht : 0 ≤ t)
    (x : E) : m + t * l ≤ hopfLax L φ t x :=
  le_hopfLax fun y ↦ add_le_add (hm y) (mul_le_mul_of_nonneg_left (hl _) ht)

/-- **The Hopf–Lax subsolution inequality.** For a convex Lagrangian `L`, moving from `(t, x)` at
velocity `w` for time `h ≥ 0` raises the Hopf–Lax value by at most `h L w`:
`u (t + h, x + h w) ≤ u (t, x) + h L w` for `t > 0`. -/
theorem hopfLax_add_add_smul_le (hφ : BddBelow (range φ)) (hL : BddBelow (range L))
    (hLc : ConvexOn ℝ univ L) (ht : 0 < t) (hh : 0 ≤ h) (x w : E) :
    hopfLax L φ (t + h) (x + h • w) ≤ hopfLax L φ t x + h * L w := by
  have hth : 0 < t + h := add_pos_of_pos_of_nonneg ht hh
  rw [← sub_le_iff_le_add]
  refine le_hopfLax fun y ↦ ?_
  -- The velocity from `y` to `x + h w` over time `t + h` is the convex combination of the velocity
  -- `t⁻¹ (x - y)` from `y` to `x` over time `t`, with weight `t / (t + h)`, and of `w`.
  have hcomb : (t + h)⁻¹ • (x + h • w - y) =
      (t / (t + h)) • (t⁻¹ • (x - y)) + (h / (t + h)) • w := by
    match_scalars <;> field_simp
  have hconv := hLc.2 (mem_univ (t⁻¹ • (x - y))) (mem_univ w) (div_nonneg ht.le hth.le)
    (div_nonneg hh hth.le) (by rw [← add_div, div_self hth.ne'])
  rw [← hcomb, smul_eq_mul, smul_eq_mul] at hconv
  have hmul : (t + h) * L ((t + h)⁻¹ • (x + h • w - y)) ≤ t * L (t⁻¹ • (x - y)) + h * L w :=
    (mul_le_mul_of_nonneg_left hconv hth.le).trans_eq (by field_simp)
  linarith [hopfLax_le hφ hL hth.le (x + h • w) y]

/-- For a convex Lagrangian, the Hopf–Lax value grows by at most `h L 0` from time `t > 0` to time
`t + h`. -/
theorem hopfLax_add_le (hφ : BddBelow (range φ)) (hL : BddBelow (range L))
    (hLc : ConvexOn ℝ univ L) (ht : 0 < t) (hh : 0 ≤ h) (x : E) :
    hopfLax L φ (t + h) x ≤ hopfLax L φ t x + h * L 0 := by
  simpa using hopfLax_add_add_smul_le hφ hL hLc ht hh x 0

/-- For a convex Lagrangian with `L 0 ≤ 0`, the Hopf–Lax value at a fixed point decreases in time
`t > 0`. -/
theorem antitoneOn_hopfLax (hφ : BddBelow (range φ)) (hL : BddBelow (range L))
    (hLc : ConvexOn ℝ univ L) (hL0 : L 0 ≤ 0) (x : E) :
    AntitoneOn (hopfLax L φ · x) (Ioi 0) := by
  intro s hs t _ hst
  have h := hopfLax_add_le hφ hL hLc hs (sub_nonneg.2 hst) x
  rw [add_sub_cancel] at h
  exact h.trans (add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hst) hL0))

/-- For a continuous Lagrangian, the Hopf–Lax value is jointly upper semicontinuous in time and
space on the open half-space `t > 0`, as an infimum of continuous functions. No regularity of `φ` is
needed. -/
theorem upperSemicontinuousOn_hopfLax [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] (hφ : BddBelow (range φ)) (hL : BddBelow (range L))
    (hLc : Continuous L) :
    UpperSemicontinuousOn (fun q : ℝ × E ↦ hopfLax L φ q.1 q.2) {q | 0 < q.1} :=
  upperSemicontinuousOn_ciInf (fun q hq ↦ bddBelow_range_penalty hφ hL (le_of_lt hq) q.2)
    fun _ ↦ (continuousOn_const.add (continuousOn_fst.mul (hLc.comp_continuousOn
      ((continuousOn_fst.inv₀ fun _ hq ↦ ne_of_gt hq).smul
        (continuousOn_snd.sub continuousOn_const))))).upperSemicontinuousOn

end Module

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {φ : E → ℝ} {t h p : ℝ}

/-- For the cost `L w = ‖w‖ ^ p`, the Hopf–Lax value at time `t > 0` is
`inf_y (φ y + ‖x - y‖ ^ p / t ^ (p - 1))`. -/
theorem hopfLax_norm_rpow (φ : E → ℝ) (ht : 0 < t) (x : E) :
    hopfLax (‖·‖ ^ p) φ t x = ⨅ y, φ y + ‖x - y‖ ^ p / t ^ (p - 1) := by
  refine iInf_congr fun y ↦ ?_
  dsimp only
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le),
    Real.mul_rpow (inv_nonneg.2 ht.le) (norm_nonneg _), Real.inv_rpow ht.le,
    Real.rpow_sub_one ht.ne']
  field_simp

/-- **The Hopf–Lax subsolution inequality for the `p`-th power cost.** In a real seminormed space,
for `1 ≤ p` and `φ` bounded below, `u (t + h, x + h w) ≤ u (t, x) + h ‖w‖ ^ p` for `t > 0` and
`h ≥ 0`. -/
theorem hopfLax_norm_rpow_add_add_smul_le (hp : 1 ≤ p) (hφ : BddBelow (range φ)) (ht : 0 < t)
    (hh : 0 ≤ h) (x w : E) :
    hopfLax (‖·‖ ^ p) φ (t + h) (x + h • w) ≤ hopfLax (‖·‖ ^ p) φ t x + h * ‖w‖ ^ p :=
  hopfLax_add_add_smul_le hφ ⟨0, forall_mem_range.2 fun _ ↦ by positivity⟩
    (convexOn_norm_rpow (E := E) hp) ht hh x w

/-- For `t > 0`, the Hopf–Lax value for the cost `‖w‖ ^ p` lies below the penalized
value `φ y + ‖x - y‖ ^ p / t ^ (p - 1)` at any point `y`. -/
private theorem hopfLax_norm_rpow_le_add_div (hφ : BddBelow (range φ)) (ht : 0 < t)
    (x y : E) : hopfLax (‖·‖ ^ p) φ t x ≤ φ y + ‖x - y‖ ^ p / t ^ (p - 1) := by
  obtain ⟨m, hm⟩ := hφ
  rw [hopfLax_norm_rpow φ ht]
  exact ciInf_le ⟨m, forall_mem_range.2 fun y ↦ le_add_of_le_of_nonneg (hm ⟨y, rfl⟩)
    (by positivity)⟩ y

omit [NormedSpace ℝ E] in
/-- For `p ≥ 0`, `t > 0` and a lower bound `m` of `φ`, at any point `y` at distance at least
`R ≥ 0` from `x` the penalized value `φ y + ‖x - y‖ ^ p / t ^ (p - 1)` is at least
`m + R ^ p / t ^ (p - 1)`. -/
private theorem add_rpow_div_le_add_norm_rpow_div {m R : ℝ} (hp : 0 ≤ p) (hm : ∀ y, m ≤ φ y)
    (hR : 0 ≤ R) (ht : 0 < t) {x y : E} (hy : R ≤ ‖x - y‖) :
    m + R ^ p / t ^ (p - 1) ≤ φ y + ‖x - y‖ ^ p / t ^ (p - 1) :=
  add_le_add (hm y) (div_le_div_of_nonneg_right (Real.rpow_le_rpow hR hy hp) (by positivity))

/-- For `p > 0` and `t ≥ 0`, the Hopf–Lax value for the cost `‖w‖ ^ p` lies below the initial
datum. -/
theorem hopfLax_norm_rpow_le (hp : 0 < p) (hφ : BddBelow (range φ)) (ht : 0 ≤ t)
    (x : E) : hopfLax (‖·‖ ^ p) φ t x ≤ φ x := by
  simpa [Real.zero_rpow hp.ne'] using
    hopfLax_le_add_mul (L := fun w : E ↦ ‖w‖ ^ p) hφ
      ⟨0, forall_mem_range.2 fun w ↦ by positivity⟩ ht x

/-- For `p > 0` and `t ≥ 0`, the Hopf–Lax value for the cost `‖w‖ ^ p` is bounded by any bound of
the initial datum. -/
theorem abs_hopfLax_norm_rpow_le (hp : 0 < p) {C : ℝ} (hφ : ∀ y, |φ y| ≤ C) (ht : 0 ≤ t)
    (x : E) : |hopfLax (‖·‖ ^ p) φ t x| ≤ C := by
  have hm (y : E) : -C ≤ φ y := (abs_le.1 (hφ y)).1
  refine abs_le.2 ⟨?_, (hopfLax_norm_rpow_le hp ⟨-C, forall_mem_range.2 hm⟩ ht x).trans
    (abs_le.1 (hφ x)).2⟩
  simpa using add_mul_le_hopfLax (L := fun w : E ↦ ‖w‖ ^ p) (l := 0) hm (fun w ↦ by positivity)
    ht x

/-- For `1 ≤ p` and a bounded initial datum `φ`, the Hopf–Lax value for the cost `‖w‖ ^ p` is
jointly lower semicontinuous in time and space on the open half-space `t > 0`. No regularity of `φ`
is needed. -/
theorem lowerSemicontinuousOn_hopfLax_norm_rpow (hp : 1 ≤ p)
    (hφ : Bornology.IsBounded (range φ)) :
    LowerSemicontinuousOn (fun q : ℝ × E ↦ hopfLax (‖·‖ ^ p) φ q.1 q.2) {q | 0 < q.1} := by
  -- Points `y` far from `x` cannot compete with `y = x`, and for `y` in a bounded region the
  -- penalties `‖x - y‖ ^ p / t ^ (p - 1)` are uniformly equicontinuous in `(t, x)`.
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  obtain ⟨A, hA⟩ := hφ.bddBelow
  obtain ⟨B, hB⟩ := hφ.bddAbove
  rintro ⟨t₀, x₀⟩ (ht₀ : 0 < t₀) m (hm : m < hopfLax (‖·‖ ^ p) φ t₀ x₀)
  set u₀ := hopfLax (‖·‖ ^ p) φ t₀ x₀
  have hε : 0 < (u₀ - m) / 2 := by linarith
  -- Beyond distance `R` from `x`, the penalty exceeds the oscillation of `φ` for `t ≤ 2 t₀`.
  obtain ⟨R, hR0, hR⟩ := ((eventually_gt_atTop 0).and ((tendsto_rpow_atTop hp0).eventually_ge_atTop
    ((B - A + 1) * (2 * t₀) ^ (p - 1)))).exists
  -- The penalty `(t, d) ↦ d ^ p / t ^ (p - 1)` is uniformly continuous on a compact box.
  let g : ℝ × ℝ → ℝ := fun z ↦ z.2 ^ p / z.1 ^ (p - 1)
  let K : Set (ℝ × ℝ) := Icc (t₀ / 2) (2 * t₀) ×ˢ Icc 0 (R + 1)
  have hg : ContinuousOn g K := by
    refine ContinuousOn.div (continuousOn_snd.rpow_const fun _ _ ↦ Or.inr hp0.le)
      (continuousOn_fst.rpow_const fun z hz ↦ Or.inl ?_) fun z hz ↦ ?_ <;>
    · have : 0 < z.1 := by linarith [hz.1.1]
      positivity
  obtain ⟨δ, hδ, hgδ⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hg) _ hε
  have hr : 0 < min (min δ (t₀ / 2)) 1 := by positivity
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (t₀, x₀) hr)] with ⟨t, x⟩ hq
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, dist_eq_norm] at hq
  obtain ⟨htt, hxx⟩ := hq
  have htδ : |t - t₀| < δ := htt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have htt₀ : |t - t₀| < t₀ / 2 := htt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hxδ : ‖x - x₀‖ < δ := hxx.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hx₁ : ‖x - x₀‖ < 1 := hxx.trans_le (min_le_right _ _)
  have ht : t ∈ Icc (t₀ / 2) (2 * t₀) := by
    constructor <;> linarith [abs_lt.1 htt₀]
  have htpos : 0 < t := by linarith [ht.1]
  refine (show m < u₀ - (u₀ - m) / 2 by linarith).trans_le ?_
  rw [hopfLax_norm_rpow φ htpos]
  refine le_ciInf fun y ↦ ?_
  by_cases hy : ‖x - y‖ < R
  · -- Nearby points: compare with the penalty at `(t₀, x₀)` by uniform continuity.
    have hy₀ : ‖x₀ - y‖ ≤ R + 1 := by
      linarith [norm_sub_le_norm_sub_add_norm_sub x₀ x y, norm_sub_rev x₀ x]
    have hmem : (t, ‖x - y‖) ∈ K := ⟨ht, norm_nonneg _, by linarith⟩
    have hmem₀ : (t₀, ‖x₀ - y‖) ∈ K := ⟨⟨by linarith, by linarith⟩, norm_nonneg _, hy₀⟩
    have hdist : dist (t, ‖x - y‖) (t₀, ‖x₀ - y‖) < δ := by
      rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
      refine ⟨htδ, (abs_norm_sub_norm_le _ _).trans_lt ?_⟩
      rwa [sub_sub_sub_cancel_right]
    have hclose := hgδ _ hmem _ hmem₀ hdist
    rw [Real.dist_eq] at hclose
    have := hopfLax_norm_rpow_le_add_div (p := p) hφ.bddBelow ht₀ x₀ y
    simp only [g] at hclose
    linarith [(abs_lt.1 hclose).1]
  · -- Distant points: the penalty alone exceeds the oscillation of `φ`.
    have hRt : B - A + 1 ≤ R ^ p / t ^ (p - 1) := by
      rw [le_div_iff₀ (by positivity)]
      exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow htpos.le ht.2 (by linarith))
        (by linarith [hA ⟨x₀, rfl⟩, hB ⟨x₀, rfl⟩])).trans hR
    have := add_rpow_div_le_add_norm_rpow_div hp0.le (fun y ↦ hA ⟨y, rfl⟩) hR0.le htpos
      (not_lt.1 hy)
    have := hopfLax_norm_rpow_le hp0 hφ.bddBelow ht₀.le x₀
    linarith [hB ⟨x₀, rfl⟩]

/-- For `1 ≤ p` and a bounded initial datum `φ`, the Hopf–Lax value for the cost `‖w‖ ^ p` is
jointly continuous in time and space on the open half-space `t > 0`. -/
theorem continuousOn_hopfLax_norm_rpow (hp : 1 ≤ p) (hφ : Bornology.IsBounded (range φ)) :
    ContinuousOn (fun q : ℝ × E ↦ hopfLax (‖·‖ ^ p) φ q.1 q.2) {q | 0 < q.1} :=
  continuousOn_iff_lower_upperSemicontinuousOn.2 ⟨lowerSemicontinuousOn_hopfLax_norm_rpow hp hφ,
    upperSemicontinuousOn_hopfLax hφ.bddBelow ⟨0, forall_mem_range.2 fun _ ↦ by positivity⟩
      (continuous_norm.rpow_const fun _ ↦ Or.inr (zero_le_one.trans hp))⟩

/-- For `1 ≤ p`, a bounded initial datum `φ` and a time `t > 0`, the Hopf–Lax value for the cost
`‖w‖ ^ p` is continuous in space. -/
theorem continuous_hopfLax_norm_rpow (hp : 1 ≤ p) (hφ : Bornology.IsBounded (range φ))
    (ht : 0 < t) : Continuous (hopfLax (‖·‖ ^ p) φ t) :=
  (continuousOn_hopfLax_norm_rpow hp hφ).comp_continuous (Continuous.prodMk_right t) fun _ ↦ ht

/-- **The Hopf–Lax value recovers the initial datum.** For `1 < p` and `φ` bounded below, at every
point `x` at which `φ` is lower semicontinuous, the Hopf–Lax value for the cost `‖w‖ ^ p` tends to
`φ x` as `t → 0⁺`. The hypothesis `1 < p` is needed: for `p = 1` the Hopf–Lax value
`inf_y (φ y + ‖x - y‖)` does not depend on `t > 0`. -/
theorem tendsto_hopfLax_norm_rpow_nhdsGT_zero (hp : 1 < p) (hφ : BddBelow (range φ)) {x : E}
    (hx : LowerSemicontinuousAt φ x) :
    Tendsto (fun t ↦ hopfLax (‖·‖ ^ p) φ t x) (𝓝[>] 0) (𝓝 (φ x)) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  obtain ⟨B, hB⟩ := hφ
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · obtain ⟨m, ham, hmx⟩ := exists_between ha
    obtain ⟨δ, hδ, hδφ⟩ := Metric.eventually_nhds_iff.1 (hx m hmx)
    -- The penalty for leaving the ball of radius `δ` blows up as `t → 0⁺`.
    have hpen : Tendsto (fun t : ℝ ↦ δ ^ p * t ^ (1 - p)) (𝓝[>] 0) atTop :=
      Tendsto.const_mul_atTop (by positivity) (tendsto_rpow_neg_nhdsGT_zero (by linarith))
    filter_upwards [self_mem_nhdsWithin, hpen.eventually_ge_atTop (m - B)] with t (ht : 0 < t) hδt
    refine ham.trans_le ?_
    rw [hopfLax_norm_rpow φ ht]
    refine le_ciInf fun y ↦ ?_
    by_cases hy : dist y x < δ
    · linarith [hδφ hy, show 0 ≤ ‖x - y‖ ^ p / t ^ (p - 1) by positivity]
    · have := add_rpow_div_le_add_norm_rpow_div hp0.le (fun y ↦ hB ⟨y, rfl⟩) hδ.le ht
        (show δ ≤ ‖x - y‖ by rw [← dist_eq_norm, dist_comm]; exact not_lt.1 hy)
      rw [show 1 - p = -(p - 1) by ring, Real.rpow_neg ht.le, ← div_eq_mul_inv] at hδt
      linarith
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact (hopfLax_norm_rpow_le hp0 ⟨B, hB⟩ ht.le x).trans_lt ha

end Seminormed

end TauCeti
