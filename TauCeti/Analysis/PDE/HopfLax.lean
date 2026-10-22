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
recovers `φ` as a limit `t → 0⁺` only under additional hypotheses. That limit, and times `t ≤ 0`,
are not studied here.

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

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society 2010, §3.3.2, on the Hopf–Lax formula.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 7.
-/

public section

noncomputable section

open Set

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

end Seminormed

end TauCeti
