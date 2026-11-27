/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Filter.Extr
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.Algebra.Order.Field

/-!
# The logarithmic barrier and the central path

A convex program `minimize f₀ x subject to g i x ≤ 0` over a convex set `S` can be approached
from the inside of its feasible region. The logarithmic barrier `φ x = -∑ i, log (-g i x)` is
finite at the strictly feasible points, those `x ∈ S` with `g i x < 0` for every `i`, and a
*central point* for a parameter `t > 0` is a strictly feasible minimizer of `t f₀ + φ` over the
strictly feasible points.

This file proves, from convexity alone, that central points are near-optimal. If `f₀` and every
`g i` are convex on `S`, `m` is the number of constraints and `x` is a central point for `t`, then
`f₀ x - m / t ≤ f₀ z` for every feasible `z`; more precisely `f₀ x - m / t` is at most the
Lagrangian `f₀ z + ∑ i, λ i * g i z` at the multipliers `λ i = -1 / (t * g i x)`, for every
`z ∈ S`. No differentiability and no constraint qualification is assumed: the segment from `x`
towards `z` starts out strictly feasible by convexity, and comparing the barrier along it with
`1 - u⁻¹ ≤ log u` gives the bound in the limit at `x`.

Two consequences follow. The centering gap bounds how far a central point for `t` is from
minimizing `μ t f₀ + φ`, which measures the work needed to recenter for the parameter `μ t`.
The bound on outer iterations says after how many parameter increases `t ↦ μ t` the central
points are `ε`-optimal.

## Main definitions

* `TauCeti.logBarrier g`: the logarithmic barrier `x ↦ -∑ i, log (-g i x)` of the constraints
  `g i ≤ 0`.
* `TauCeti.strictFeasibleSet S g`: the points `x ∈ S` with `g i x < 0` for every `i`.

## Main results

* `TauCeti.centralPath_bound`: at a central point `x` for `t > 0`,
  `f₀ x - m / t ≤ f₀ z + ∑ i, g i z / (-(t * g i x))` for every `z ∈ S`.
* `TauCeti.centralPath_sub_le`: at a central point `x` for `t > 0`, `f₀ x - m / t ≤ f₀ z` for
  every feasible `z`.
* `TauCeti.centering_gap`: at a central point `x` for `t ≥ 0`, for every `μ > 0` and every
  strictly feasible `y`, `(μ t f₀ x + φ x) - (μ t f₀ y + φ y) ≤ m (μ - 1 - log μ)`.
* `TauCeti.centralPath_sub_le_of_log_div_log_le`: if `x` is a central point for `μ ^ k * t₀`
  with `μ > 1`, and `log (m / (ε t₀)) / log μ ≤ k`, then `f₀ x - f₀ z ≤ ε` for every feasible
  `z`.

## References

* S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004:
  §11.2.2 for the central points and their duality gap `m / t` (there for differentiable data),
  §11.3.3, (11.13), for the number of outer iterations, and §11.5.2 for the centering gap (there
  for `μ > 1` and `y` the next central point).
-/

public section

open Filter Finset
open scoped Topology

namespace TauCeti

variable {E ι : Type*}

/-- The strictly feasible points of `S` for the constraints `g i ≤ 0`: the `x ∈ S` with
`g i x < 0` for every `i`. -/
def strictFeasibleSet (S : Set E) (g : ι → E → ℝ) : Set E :=
  {x | x ∈ S ∧ ∀ i, g i x < 0}

@[simp]
theorem mem_strictFeasibleSet {S : Set E} {g : ι → E → ℝ} {x : E} :
    x ∈ strictFeasibleSet S g ↔ x ∈ S ∧ ∀ i, g i x < 0 := Iff.rfl

theorem strictFeasibleSet_subset (S : Set E) (g : ι → E → ℝ) : strictFeasibleSet S g ⊆ S :=
  fun _ hx => hx.1

@[simp]
theorem strictFeasibleSet_of_isEmpty [IsEmpty ι] (S : Set E) (g : ι → E → ℝ) :
    strictFeasibleSet S g = S := by
  ext x
  simp

variable [Fintype ι]

/-- The logarithmic barrier `x ↦ -∑ i, log (-g i x)` of the constraints `g i ≤ 0`. It is meant
to be used at strictly feasible points, where every `-g i x` is positive. -/
noncomputable def logBarrier (g : ι → E → ℝ) (x : E) : ℝ :=
  -∑ i, Real.log (-g i x)

theorem logBarrier_def (g : ι → E → ℝ) (x : E) :
    logBarrier g x = -∑ i, Real.log (-g i x) := (rfl)

@[simp]
theorem logBarrier_of_isEmpty [IsEmpty ι] (g : ι → E → ℝ) (x : E) : logBarrier g x = 0 := by
  simp [logBarrier]

/-- The difference of the barrier at two strictly feasible points is the sum of the logarithms
of the ratios of the constraint values. -/
theorem logBarrier_sub_logBarrier {g : ι → E → ℝ} {x y : E} (hx : ∀ i, g i x < 0)
    (hy : ∀ i, g i y < 0) :
    logBarrier g x - logBarrier g y = ∑ i, Real.log (g i y / g i x) := by
  simp only [logBarrier, Real.log_neg_eq_log]
  rw [sum_congr rfl fun i _ => Real.log_div (hy i).ne (hx i).ne, sum_sub_distrib]
  ring

/-- One constraint along a segment: if `a < 0`, `q = 1 + s (b / a - 1) > 0` and
`u ≤ (1 - s) a + s b`, then `log (-u)` exceeds `log (-a)` by at least `s (b / a - 1) / q`. -/
private lemma mul_div_le_log_neg_sub_log_neg {a b u s : ℝ} (ha : a < 0)
    (hq : 0 < 1 + s * (b / a - 1)) (hu : u ≤ (1 - s) * a + s * b) :
    s * ((b / a - 1) / (1 + s * (b / a - 1))) ≤ Real.log (-u) - Real.log (-a) := by
  have ha0 : a ≠ 0 := ha.ne
  have hcomb : (1 - s) * a + s * b = a * (1 + s * (b / a - 1)) := by
    field_simp
    ring
  have hpos : 0 < -a * (1 + s * (b / a - 1)) := mul_pos (neg_pos.2 ha) hq
  have hlog := Real.log_le_log hpos (show -a * (1 + s * (b / a - 1)) ≤ -u by
    rw [neg_mul, ← hcomb]
    linarith)
  rw [Real.log_mul (neg_pos.2 ha).ne' hq.ne'] at hlog
  have hinv := Real.one_sub_inv_le_log_of_pos hq
  set c := b / a - 1
  have heq : s * (c / (1 + s * c)) = 1 - (1 + s * c)⁻¹ := by
    have := hq.ne'
    field_simp
    ring
  linarith

variable [AddCommGroup E] [Module ℝ E] {S : Set E} {f₀ : E → ℝ} {g : ι → E → ℝ} {t : ℝ} {x : E}

/-- The central point inequality with the ratios of the constraint values: at a central point
`x` for `t > 0`, `∑ i, (g i z / g i x - 1) ≤ t (f₀ z - f₀ x)` for every `z ∈ S`. -/
private lemma sum_div_sub_one_le (hf₀ : ConvexOn ℝ S f₀) (hg : ∀ i, ConvexOn ℝ S (g i))
    (hx : x ∈ strictFeasibleSet S g)
    (hmin : IsMinOn (fun z => t * f₀ z + logBarrier g z) (strictFeasibleSet S g) x)
    (ht : 0 ≤ t) {z : E} (hz : z ∈ S) :
    ∑ i, (g i z / g i x - 1) ≤ t * (f₀ z - f₀ x) := by
  set c : ι → ℝ := fun i => g i z / g i x - 1 with hc
  -- The difference quotient of the barrier along the segment, as a function of the step `s`.
  have hcont : ContinuousAt (fun s : ℝ => ∑ i, c i / (1 + s * c i)) 0 := by
    fun_prop (disch := simp)
  have hlim : Tendsto (fun s : ℝ => ∑ i, c i / (1 + s * c i)) (𝓝[>] 0) (𝓝 (∑ i, c i)) := by
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hlim ?_
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s < 1 ∧ ∀ i, 0 < 1 + s * c i := by
    refine eventually_mem_nhdsWithin.and (Eventually.and ?_ ?_)
    · exact nhdsWithin_le_nhds (eventually_lt_nhds one_pos)
    · refine nhdsWithin_le_nhds (eventually_all.2 fun i => ?_)
      have : Tendsto (fun s : ℝ => 1 + s * c i) (𝓝 0) (𝓝 1) := by
        have : ContinuousAt (fun s : ℝ => 1 + s * c i) 0 := by fun_prop
        simpa using this.tendsto
      exact this.eventually_const_lt one_pos
  filter_upwards [hsmall] with s ⟨hs, hs1, hq⟩
  -- The point `x + s (z - x)` of the segment and the convexity bounds there.
  set xs : E := (1 - s) • x + s • z
  have hmem : xs ∈ S := hf₀.1 hx.1 hz (by linarith) hs.le (by ring)
  have hgxs (i : ι) : g i xs ≤ (1 - s) * g i x + s * g i z := by
    simpa using (hg i).2 hx.1 hz (by linarith) hs.le (by ring)
  have hfxs : f₀ xs ≤ (1 - s) * f₀ x + s * f₀ z := by
    simpa using hf₀.2 hx.1 hz (by linarith) hs.le (by ring)
  have hstep (i : ι) : s * (c i / (1 + s * c i)) ≤ Real.log (-g i xs) - Real.log (-g i x) :=
    mul_div_le_log_neg_sub_log_neg (hx.2 i) (hq i) (hgxs i)
  have hfeas : xs ∈ strictFeasibleSet S g := by
    refine ⟨hmem, fun i => ?_⟩
    have : (1 - s) * g i x + s * g i z = g i x * (1 + s * c i) := by
      simp only [hc]
      field_simp [(hx.2 i).ne]
      ring
    nlinarith [hgxs i, hx.2 i, hq i]
  have hminxs : t * f₀ x + logBarrier g x ≤ t * f₀ xs + logBarrier g xs := hmin hfeas
  have hsum := sum_le_sum fun i (_ : i ∈ univ) => hstep i
  rw [← mul_sum, sum_sub_distrib] at hsum
  simp only [logBarrier] at hminxs
  have hf : t * f₀ xs ≤ t * ((1 - s) * f₀ x + s * f₀ z) := mul_le_mul_of_nonneg_left hfxs ht
  refine le_of_mul_le_mul_left ?_ hs
  linarith

/-- **Central points are `m / t`-optimal**, Lagrangian form. Let `f₀` and the constraints `g i`
be convex on `S`, `t > 0`, and `x` a strictly feasible minimizer of `t f₀ + φ` over the strictly
feasible points. Then for every `z ∈ S`, `f₀ x - m / t ≤ f₀ z + ∑ i, g i z / (-(t * g i x))`,
where `m` is the number of constraints. The right side is the Lagrangian at the multipliers
`-1 / (t * g i x)`. No differentiability is assumed. -/
theorem centralPath_bound (hf₀ : ConvexOn ℝ S f₀) (hg : ∀ i, ConvexOn ℝ S (g i)) (ht : 0 < t)
    (hx : x ∈ strictFeasibleSet S g)
    (hmin : IsMinOn (fun z => t * f₀ z + logBarrier g z) (strictFeasibleSet S g) x)
    {z : E} (hz : z ∈ S) :
    f₀ x - Fintype.card ι / t ≤ f₀ z + ∑ i, g i z / (-(t * g i x)) := by
  have key := sum_div_sub_one_le hf₀ hg hx hmin ht.le hz
  rw [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one] at key
  have hsum : ∑ i, g i z / (-(t * g i x)) = -(∑ i, g i z / g i x) / t := by
    rw [neg_div, sum_div, ← sum_neg_distrib]
    refine sum_congr rfl fun i _ => ?_
    field_simp [(hx.2 i).ne]
  rw [hsum, sub_le_iff_le_add, add_assoc, ← sub_le_iff_le_add', ← add_div, le_div_iff₀ ht]
  linarith

/-- **Central points are `m / t`-optimal.** Let `f₀` and the constraints `g i` be convex on `S`,
`t > 0`, and `x` a strictly feasible minimizer of `t f₀ + φ` over the strictly feasible points.
Then `f₀ x - m / t ≤ f₀ z` for every feasible `z`, where `m` is the number of constraints. -/
theorem centralPath_sub_le (hf₀ : ConvexOn ℝ S f₀) (hg : ∀ i, ConvexOn ℝ S (g i)) (ht : 0 < t)
    (hx : x ∈ strictFeasibleSet S g)
    (hmin : IsMinOn (fun z => t * f₀ z + logBarrier g z) (strictFeasibleSet S g) x)
    {z : E} (hz : z ∈ S) (hgz : ∀ i, g i z ≤ 0) :
    f₀ x - Fintype.card ι / t ≤ f₀ z := by
  refine (centralPath_bound hf₀ hg ht hx hmin hz).trans (add_le_of_nonpos_right ?_)
  exact sum_nonpos fun i _ =>
    div_nonpos_of_nonpos_of_nonneg (hgz i) (neg_nonneg.2 (mul_neg_of_pos_of_neg ht (hx.2 i)).le)

/-- **The centering gap.** Let `f₀` and the constraints `g i` be convex on `S`, `t ≥ 0`, and `x` a
strictly feasible minimizer of `t f₀ + φ` over the strictly feasible points. For every `μ > 0` and
every strictly feasible `y`, the value of `μ t f₀ + φ` at `x` exceeds its value at `y` by at most
`m (μ - 1 - log μ)`, where `m` is the number of constraints. -/
theorem centering_gap {μ : ℝ} {y : E} (hf₀ : ConvexOn ℝ S f₀) (hg : ∀ i, ConvexOn ℝ S (g i))
    (ht : 0 ≤ t) (hμ : 0 < μ) (hx : x ∈ strictFeasibleSet S g)
    (hmin : IsMinOn (fun z => t * f₀ z + logBarrier g z) (strictFeasibleSet S g) x)
    (hy : y ∈ strictFeasibleSet S g) :
    μ * t * f₀ x + logBarrier g x - (μ * t * f₀ y + logBarrier g y) ≤
      Fintype.card ι * (μ - 1 - Real.log μ) := by
  have key := sum_div_sub_one_le hf₀ hg hx hmin ht hy.1
  rw [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one] at key
  -- Each `log (g i y / g i x) = log (μ * (g i y / g i x)) - log μ` is at most
  -- `μ * (g i y / g i x) - 1 - log μ`.
  have hlog (i : ι) : Real.log (g i y / g i x) ≤ μ * (g i y / g i x) - 1 - Real.log μ := by
    have ha := div_pos_of_neg_of_neg (hy.2 i) (hx.2 i)
    have := Real.log_le_sub_one_of_pos (mul_pos hμ ha)
    rw [Real.log_mul hμ.ne' ha.ne'] at this
    linarith
  have hsum := sum_le_sum fun i (_ : i ∈ univ) => hlog i
  rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, sum_const, sum_const, card_univ,
    nsmul_eq_mul, nsmul_eq_mul, mul_one] at hsum
  have hgap := logBarrier_sub_logBarrier hx.2 hy.2
  linarith [mul_le_mul_of_nonneg_left key hμ.le]

/-- **The outer iterations of the barrier method.** Let `f₀` and the constraints `g i` be convex
on `S`, `t₀ > 0`, `μ > 1` and `ε > 0`, and let `x` be a strictly feasible minimizer of
`μ ^ k t₀ f₀ + φ` over the strictly feasible points, the central point reached after `k`
increases `t ↦ μ t` of the parameter from `t₀`. If `log (m / (ε t₀)) / log μ ≤ k`, where `m` is the
number of constraints, then `f₀ x - f₀ z ≤ ε` for every feasible `z`. -/
theorem centralPath_sub_le_of_log_div_log_le {t₀ μ ε : ℝ} {k : ℕ} (hf₀ : ConvexOn ℝ S f₀)
    (hg : ∀ i, ConvexOn ℝ S (g i)) (ht₀ : 0 < t₀) (hμ : 1 < μ) (hε : 0 < ε)
    (hx : x ∈ strictFeasibleSet S g)
    (hmin : IsMinOn (fun z => μ ^ k * t₀ * f₀ z + logBarrier g z) (strictFeasibleSet S g) x)
    (hk : Real.log (Fintype.card ι / (ε * t₀)) / Real.log μ ≤ k) {z : E} (hz : z ∈ S)
    (hgz : ∀ i, g i z ≤ 0) :
    f₀ x - f₀ z ≤ ε := by
  have htk : 0 < μ ^ k * t₀ := mul_pos (pow_pos (by linarith) k) ht₀
  have hbound := centralPath_sub_le hf₀ hg htk hx hmin hz hgz
  -- It remains to see `m / (μ ^ k t₀) ≤ ε`.
  suffices h : (Fintype.card ι : ℝ) / (μ ^ k * t₀) ≤ ε by linarith
  rcases (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ Fintype.card ι).eq_or_lt with hm | hm
  · rw [← hm, zero_div]
    exact hε.le
  have hεt : 0 < ε * t₀ := mul_pos hε ht₀
  rw [div_le_iff₀ (Real.log_pos hμ), ← Real.log_pow,
    Real.log_le_log_iff (div_pos hm hεt) (pow_pos (by linarith) k), div_le_iff₀ hεt] at hk
  rw [div_le_iff₀ htk]
  linarith

end TauCeti
