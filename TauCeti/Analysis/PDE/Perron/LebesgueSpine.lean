/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Perron.Regular
import Mathlib.MeasureTheory.Constructions.UnitInterval
import TauCeti.Analysis.Convex.Segment
import TauCeti.Analysis.Convex.Topology
import TauCeti.Analysis.InnerProductSpace.Harmonic.Isometry
import TauCeti.Analysis.InnerProductSpace.Laplacian.ParametricIntegral
import TauCeti.Analysis.InnerProductSpace.NormPow

/-!
# Lebesgue's spine: an irregular boundary point in three dimensions

Let `E` be a real inner product space of dimension `3` and `e ∈ E` a unit vector. Lebesgue's
example of an irregular boundary point is built from the Newtonian potential, up to the factor
`4π`, of the segment `[0, e]` carrying the charge density `t` at the point `t e`:

`u(x) = ∫₀¹ t / ‖x - t e‖ dt` (`TauCeti.lebesgueSpinePotential`).

It is smooth and harmonic off the segment (`TauCeti.harmonicOnNhd_lebesgueSpinePotential`), at
most `1` on the lower half-space `⟪x, e⟫ ≤ 0`, where `t ≤ ‖x - t e‖`
(`TauCeti.lebesgueSpinePotential_le_one`), and it tends to `+∞` at every point `t₀ e` of the
segment with `0 < t₀ < 1` (`TauCeti.tendsto_lebesgueSpinePotential_atTop`), since the linear
density is positive there and `∫ dt / ‖x - t e‖` diverges logarithmically. At the end point `0`
the density vanishes, and `u` is not continuous there: it is at most `1` on the lower
half-space, but it tends to `+∞` at points of the segment arbitrarily close to `0`.

For `0 < ρ < 1` and `c > 0` let `Ω` be the set of points of the ball `B(0, ρ)` off the segment
with `u(x) < 1 + c` (`TauCeti.lebesgueSpineDomain`). Its complement in the ball is the set of
points off the segment where `u ≥ 1 + c`, together with the segment; apart from the origin it
lies in the open upper half-space `⟪x, e⟫ > 0`, so `Ω` contains the punctured lower
half-ball (`TauCeti.mem_lebesgueSpineDomain_of_inner_nonpos`), and `0` is a boundary point of
`Ω` (`TauCeti.zero_mem_frontier_lebesgueSpineDomain`). Classically this complement is a thin
cusp around the segment, Lebesgue's spine; the argument below does not use its shape.

**The origin is an irregular boundary point** (`TauCeti.not_isBarrier_lebesgueSpineDomain`): no
function is a barrier at `0` relative to `Ω`. Consequently the Dirichlet problem on `Ω` with the
continuous boundary datum `x ↦ ‖x‖` has no solution harmonic in `Ω` and continuous on its
closure (`TauCeti.not_exists_harmonicOnNhd_lebesgueSpineDomain_eq_norm`), although `Ω` is a
bounded open set whose complement near `0` is contained in a half-space.

## The argument

The function `h = 1 + c - u` is harmonic and nonnegative on `Ω`, at most `1 + c` there, and it
vanishes at every boundary point of `Ω` in the ball other than `0`: such a point lies off the
segment, because `u` blows up at the inner points of the segment, so `u` is continuous there and
equals `1 + c`. Suppose `w` were a barrier at `0`, and let `m > 0` bound `w` below on the part of
the closure at distance at least `ρ / 2` from `0`. For `η > 0` the superharmonic function
`((1 + c) / m) w + η / ‖x‖` lies above `h` on the boundary of `Ω ∖ closedBall 0 r` for small
`r`: near `0` thanks to the term `η / ‖x‖`, near the rest of the frontier because `h` vanishes
there, and far from `0` thanks to `w ≥ m`. The comparison principle and `η → 0` give
`h ≤ ((1 + c) / m) w` on `Ω`. Along the points `-s e`, `s → 0⁺`, which lie in `Ω`, the barrier
tends to `w 0 = 0`, while `h(-s e) ≥ c` since `u ≤ 1` on the lower half-space: a contradiction.

## Main declarations

* `TauCeti.lebesgueSpinePotential`: the potential `u` of the segment `[0, e]` with density `t`.
* `TauCeti.contDiffOn_lebesgueSpinePotential`, `TauCeti.harmonicOnNhd_lebesgueSpinePotential`:
  `u` is smooth, and in dimension `3` harmonic, off the segment.
* `TauCeti.lebesgueSpinePotential_le_one`: `u ≤ 1` on the lower half-space.
* `TauCeti.tendsto_lebesgueSpinePotential_atTop`: `u → +∞` at the inner points of the segment.
* `TauCeti.lebesgueSpineDomain`: the domain `Ω`, with `TauCeti.isOpen_lebesgueSpineDomain`,
  `TauCeti.mem_lebesgueSpineDomain_of_inner_nonpos` and
  `TauCeti.zero_mem_frontier_lebesgueSpineDomain`.
* `TauCeti.not_isBarrier_lebesgueSpineDomain`: `0` is an irregular boundary point of `Ω`.
* `TauCeti.not_exists_harmonicOnNhd_lebesgueSpineDomain_eq_norm`: the Dirichlet problem on `Ω`
  with boundary datum `‖x‖` is not solvable.

## References

* H. Lebesgue, *Sur des cas d'impossibilité du problème de Dirichlet ordinaire*, C. R. Séances
  Soc. Math. France 41 (1913).
* O. D. Kellogg, *Foundations of Potential Theory*, Springer, 1929 (Lebesgue's example of an
  exceptional boundary point).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 2.8 (barriers and regular boundary points).
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace MeasureTheory Metric Set Filter Topology Module
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (e : E)

/-- The Newtonian potential, without the factor `1 / (4π)`, of the segment `[0, e]` carrying the
linear charge density `t` at `t e`: `u(x) = ∫₀¹ t / ‖x - t e‖ dt`. It is the potential of
Lebesgue's example of an irregular boundary point. On the segment the integrand is not
integrable except at `0`, and the value there carries no meaning. -/
def lebesgueSpinePotential (x : E) : ℝ :=
  ∫ t in (0 : ℝ)..1, t * ‖x - t • e‖⁻¹

/-- The defining formula of `TauCeti.lebesgueSpinePotential`. -/
theorem lebesgueSpinePotential_def (x : E) :
    lebesgueSpinePotential e x = ∫ t in (0 : ℝ)..1, t * ‖x - t • e‖⁻¹ := by
  rw [lebesgueSpinePotential]

/-- The domain of Lebesgue's example: the points of the ball `B(0, ρ)` off the segment `[0, e]`
at which the potential `TauCeti.lebesgueSpinePotential` is below `1 + c`. -/
def lebesgueSpineDomain (ρ c : ℝ) : Set E :=
  ball 0 ρ ∩ {x | x ∉ segment ℝ 0 e ∧ lebesgueSpinePotential e x < 1 + c}

variable {e}

@[simp]
theorem mem_lebesgueSpineDomain {ρ c : ℝ} {x : E} :
    x ∈ lebesgueSpineDomain e ρ c ↔
      ‖x‖ < ρ ∧ x ∉ segment ℝ 0 e ∧ lebesgueSpinePotential e x < 1 + c := by
  rw [lebesgueSpineDomain, mem_inter_iff, mem_ball_zero_iff]
  exact Iff.rfl

/-- The origin, an end point of the segment, is not in the domain of Lebesgue's example. -/
private lemma ne_zero_of_mem_lebesgueSpineDomain {ρ c : ℝ} {x : E}
    (hx : x ∈ lebesgueSpineDomain e ρ c) : x ≠ 0 :=
  fun h ↦ (mem_lebesgueSpineDomain.1 hx).2.1 (h ▸ left_mem_segment ℝ 0 e)

/-- Off the segment, `x - t • e` does not vanish for `t ∈ [0, 1]`. -/
private lemma sub_smul_ne_zero {x : E} (hx : x ∉ segment ℝ 0 e) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    x - t • e ≠ 0 :=
  sub_ne_zero.2 fun h ↦ hx (segment_zero_left_eq_image ℝ e ▸ ⟨t, ht, h.symm⟩)

private lemma intervalIntegrable_integrand {x : E} (hx : x ∉ segment ℝ 0 e) :
    IntervalIntegrable (fun t : ℝ ↦ t * ‖x - t • e‖⁻¹) volume 0 1 :=
  (continuousOn_id.mul ((continuous_const.sub (continuous_id.smul
    continuous_const)).norm.continuousOn.inv₀ fun _ ht ↦
      norm_ne_zero_iff.2 (sub_smul_ne_zero hx ht))).intervalIntegrable_of_Icc zero_le_one

variable (e) in
/-- The potential of the segment is nonnegative, its density being nonnegative. -/
theorem lebesgueSpinePotential_nonneg (x : E) : 0 ≤ lebesgueSpinePotential e x :=
  intervalIntegral.integral_nonneg zero_le_one fun _ ht ↦
    mul_nonneg ht.1 (inv_nonneg.2 (norm_nonneg _))

variable (e) in
/-- The potential as an integral over the unit interval with its probability measure, the form
in which the parametric integral lemmas apply. -/
private lemma lebesgueSpinePotential_eq_integral_unitInterval (x : E) :
    lebesgueSpinePotential e x = ∫ y : unitInterval, (y : ℝ) • ‖x - (y : ℝ) • e‖⁻¹ := by
  rw [unitInterval.volume_def,
    integral_subtype_comap measurableSet_Icc fun t : ℝ ↦ t • ‖x - t • e‖⁻¹,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    lebesgueSpinePotential_def]
  simp only [smul_eq_mul]

private lemma isOpen_sub_smul_ne_zero : IsOpen {p : E × ℝ | p.1 - p.2 • e ≠ 0} :=
  isOpen_ne_fun (continuous_fst.sub (continuous_snd.smul continuous_const)) continuous_const

private lemma contDiffOn_inv_norm_sub_smul {n : ℕ∞} :
    ContDiffOn ℝ n (fun p : E × ℝ ↦ ‖p.1 - p.2 • e‖⁻¹) {p | p.1 - p.2 • e ≠ 0} :=
  fun p hp ↦ (((contDiffAt_norm ℝ hp).comp p
    (contDiff_fst.sub (contDiff_snd.smul contDiff_const)).contDiffAt).inv
      (norm_ne_zero_iff.2 hp)).contDiffWithinAt

/-- A nonzero point of the lower half-space `⟪x, e⟫ ≤ 0` lies off the segment `[0, e]`. -/
private lemma notMem_segment_of_inner_nonpos (he : ‖e‖ = 1) {x : E} (hx0 : x ≠ 0)
    (hxe : ⟪x, e⟫ ≤ 0) : x ∉ segment ℝ 0 e := by
  rw [segment_zero_left_eq_image ℝ e]
  rintro ⟨t, ht, rfl⟩
  have : t = 0 := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, he] at hxe
    linarith [ht.1]
  exact hx0 (by simp [this])

/-- On the lower half-space `⟪x, e⟫ ≤ 0` the potential of the segment is at most `1`: there
`t ≤ ‖x - t e‖` for `t ≥ 0`, so the integrand is at most `1`. -/
theorem lebesgueSpinePotential_le_one (he : ‖e‖ = 1) {x : E} (hx0 : x ≠ 0)
    (hxe : ⟪x, e⟫ ≤ 0) : lebesgueSpinePotential e x ≤ 1 := by
  have hxs := notMem_segment_of_inner_nonpos he hx0 hxe
  have hle : ∀ t ∈ Icc (0 : ℝ) 1, t * ‖x - t • e‖⁻¹ ≤ 1 := by
    intro t ht
    rcases ht.1.eq_or_lt with h0 | h0
    · simp [← h0]
    have ht_le : t ≤ ‖x - t • e‖ := by
      have hinner : ⟪t • e - x, e⟫ = t - ⟪x, e⟫ := by
        rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he]
        ring
      have := real_inner_le_norm (t • e - x) e
      rw [hinner, he, mul_one, norm_sub_rev] at this
      linarith
    rw [← div_eq_mul_inv, div_le_one (h0.trans_le ht_le)]
    exact ht_le
  calc lebesgueSpinePotential e x ≤ ∫ _ in (0 : ℝ)..1, (1 : ℝ) :=
        intervalIntegral.integral_mono_on zero_le_one (intervalIntegrable_integrand hxs)
          intervalIntegrable_const hle
    _ = 1 := by simp

/-- With `z = ⟪x, e⟫`, both the distance `‖x - z e‖` from `x` to the line through `e` and
`|z - t₀|` are at most `‖x - t₀ e‖`, by Pythagoras. -/
private lemma norm_sub_inner_smul_le_and_abs_sub_le (he : ‖e‖ = 1) (x : E) (t₀ : ℝ) :
    ‖x - ⟪x, e⟫ • e‖ ≤ ‖x - t₀ • e‖ ∧ |⟪x, e⟫ - t₀| ≤ ‖x - t₀ • e‖ := by
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  refine ⟨?_, ?_⟩
  · have hperp : ⟪x - ⟪x, e⟫ • e, (⟪x, e⟫ - t₀) • e⟫ = 0 := by
      rw [real_inner_smul_right, inner_sub_left, real_inner_smul_left, hee]
      ring
    have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_real hperp
    rw [show x - ⟪x, e⟫ • e + (⟪x, e⟫ - t₀) • e = x - t₀ • e by rw [sub_smul]; abel] at hpyth
    nlinarith [mul_self_nonneg ‖(⟪x, e⟫ - t₀) • e‖, norm_nonneg (x - t₀ • e),
      norm_nonneg (x - ⟪x, e⟫ • e)]
  · have := abs_real_inner_le_norm (x - t₀ • e) e
    rwa [inner_sub_left, real_inner_smul_left, hee, mul_one, he, mul_one] at this

/-- A lower bound for the potential off the segment. Let `z = ⟪x, e⟫` and let `r > 0` be the
distance from `x` to the line through `e`. If `[z, z + a] ⊆ [0, 1]` and `0 ≤ b ≤ z`, the density
is at least `b` on `[z, z + a]` and `‖x - t e‖ ≤ r + (t - z)` there, so the potential at `x` is at
least `b log ((r + a) / r)`. -/
private lemma mul_log_le_lebesgueSpinePotential (he : ‖e‖ = 1) {x : E}
    (hxs : x ∉ segment ℝ 0 e) (hr : 0 < ‖x - ⟪x, e⟫ • e‖) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hbz : b ≤ ⟪x, e⟫) (hza : ⟪x, e⟫ + a ≤ 1) :
    b * Real.log ((‖x - ⟪x, e⟫ • e‖ + a) / ‖x - ⟪x, e⟫ • e‖) ≤ lebesgueSpinePotential e x := by
  set z := ⟪x, e⟫
  set r := ‖x - z • e‖
  have hz : 0 ≤ z := hb.trans hbz
  have hlow : ∀ t ∈ Icc z (z + a), b * (t + (r - z))⁻¹ ≤ t * ‖x - t • e‖⁻¹ := by
    intro t ht
    have hpos : 0 < ‖x - t • e‖ :=
      norm_pos_iff.2 (sub_smul_ne_zero hxs ⟨hz.trans ht.1, ht.2.trans hza⟩)
    have hle : ‖x - t • e‖ ≤ t + (r - z) := by
      rw [show x - t • e = (x - z • e) + (z - t) • e by rw [sub_smul]; abel]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonpos (by linarith [ht.1])]
      linarith
    exact mul_le_mul (hbz.trans ht.1) (inv_anti₀ hpos hle) (inv_nonneg.2 (by linarith [ht.1]))
      (hz.trans ht.1)
  have hint : ∫ t in z..z + a, b * (t + (r - z))⁻¹ = b * Real.log ((r + a) / r) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_add_right (fun s : ℝ ↦ s⁻¹) (r - z),
      show z + (r - z) = r by ring, show z + a + (r - z) = r + a by ring,
      integral_inv_of_pos hr (by linarith)]
  have hcont : ContinuousOn (fun t : ℝ ↦ b * (t + (r - z))⁻¹) (Icc z (z + a)) :=
    continuousOn_const.mul (ContinuousOn.inv₀ (f := fun t : ℝ ↦ t + (r - z)) (by fun_prop)
      fun t ht ↦ (show (0 : ℝ) < t + (r - z) by linarith [ht.1]).ne')
  calc b * Real.log ((r + a) / r) = ∫ t in z..z + a, b * (t + (r - z))⁻¹ := hint.symm
    _ ≤ ∫ t in z..z + a, t * ‖x - t • e‖⁻¹ :=
        intervalIntegral.integral_mono_on (by linarith) (hcont.intervalIntegrable_of_Icc
          (by linarith)) ((intervalIntegrable_integrand hxs).mono_set (by
            rw [uIcc_of_le (by linarith), uIcc_of_le zero_le_one]
            exact Icc_subset_Icc hz hza)) hlow
    _ ≤ lebesgueSpinePotential e x := by
        rw [lebesgueSpinePotential_def]
        refine intervalIntegral.integral_mono_interval hz (by linarith) hza ?_
          (intervalIntegrable_integrand hxs)
        refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht ↦ ?_)
        exact mul_nonneg ht.1.le (inv_nonneg.2 (norm_nonneg _))

/-- **The potential of the segment blows up at its inner points**: for `0 < t₀ < 1`, the
potential tends to `+∞` at `t₀ e` from off the segment. Near `t₀ e` the density is at least
`t₀ / 2`, and with `r` the distance to the line through `e`, the potential is at least
`(t₀ / 2) log ((r + a) / r)` for a fixed `a > 0`. -/
theorem tendsto_lebesgueSpinePotential_atTop (he : ‖e‖ = 1) {t₀ : ℝ} (h0 : 0 < t₀) (h1 : t₀ < 1) :
    Tendsto (lebesgueSpinePotential e) (𝓝[(segment ℝ 0 e)ᶜ] (t₀ • e)) atTop := by
  refine tendsto_atTop.2 fun M ↦ ?_
  set a := min (t₀ / 2) ((1 - t₀) / 2)
  have ha : 0 < a := lt_min (by linarith) (by linarith)
  have ha₁ : a ≤ t₀ / 2 := min_le_left _ _
  have ha₂ : a ≤ (1 - t₀) / 2 := min_le_right _ _
  set δ := min a (a * Real.exp (-(2 * M / t₀)))
  have hδ : 0 < δ := lt_min ha (mul_pos ha (Real.exp_pos _))
  rw [eventually_nhdsWithin_iff]
  filter_upwards [ball_mem_nhds _ hδ] with x hx hxs
  rw [mem_ball, dist_eq_norm] at hx
  obtain ⟨hr_le, hz_le⟩ := norm_sub_inner_smul_le_and_abs_sub_le he x t₀
  set z := ⟪x, e⟫
  set r := ‖x - z • e‖
  have hz := abs_lt.1 (hz_le.trans_lt (hx.trans_le (min_le_left _ _)))
  have hr0 : 0 < r := by
    refine (norm_nonneg _).lt_of_ne fun h ↦ hxs ?_
    rw [eq_comm, norm_eq_zero, sub_eq_zero] at h
    rw [h, segment_zero_left_eq_image ℝ e]
    exact ⟨z, ⟨by linarith, by linarith⟩, rfl⟩
  -- `r < a exp (-2M / t₀)`, so `log ((r + a) / r) ≥ 2M / t₀`.
  have hexp : Real.exp (2 * M / t₀) ≤ (r + a) / r := by
    rw [le_div_iff₀ hr0]
    have hra : r ≤ a * Real.exp (-(2 * M / t₀)) := (hr_le.trans hx.le).trans (min_le_right _ _)
    calc Real.exp (2 * M / t₀) * r ≤ Real.exp (2 * M / t₀) * (a * Real.exp (-(2 * M / t₀))) :=
          mul_le_mul_of_nonneg_left hra (Real.exp_pos _).le
      _ = a := by rw [mul_left_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      _ ≤ r + a := by linarith
  have hlog : 2 * M / t₀ ≤ Real.log ((r + a) / r) :=
    (Real.le_log_iff_exp_le (by positivity)).2 hexp
  calc M = t₀ / 2 * (2 * M / t₀) := by field_simp
    _ ≤ t₀ / 2 * Real.log ((r + a) / r) := mul_le_mul_of_nonneg_left hlog (by linarith)
    _ ≤ lebesgueSpinePotential e x :=
        mul_log_le_lebesgueSpinePotential he hxs hr0 ha (by linarith) (by linarith)
          (by linarith)

variable (e) in
/-- The domain of Lebesgue's example is bounded, being contained in a ball. -/
theorem isBounded_lebesgueSpineDomain (ρ c : ℝ) :
    Bornology.IsBounded (lebesgueSpineDomain e ρ c) :=
  isBounded_ball.subset inter_subset_left

/-- The domain of Lebesgue's example contains the punctured lower half-ball: its complement in
the ball lies in the upper half-space `⟪x, e⟫ > 0`, apart from the origin. -/
theorem mem_lebesgueSpineDomain_of_inner_nonpos (he : ‖e‖ = 1) {ρ c : ℝ} (hc : 0 < c) {x : E}
    (hx : ‖x‖ < ρ) (hx0 : x ≠ 0) (hxe : ⟪x, e⟫ ≤ 0) : x ∈ lebesgueSpineDomain e ρ c := by
  refine mem_lebesgueSpineDomain.2 ⟨hx, notMem_segment_of_inner_nonpos he hx0 hxe, ?_⟩
  linarith [lebesgueSpinePotential_le_one he hx0 hxe]

/-- The points `-s e`, `s ≥ 0`, lie in the lower half-space `⟪x, e⟫ ≤ 0`. -/
private lemma inner_neg_smul_self_nonpos {s : ℝ} (hs : 0 ≤ s) : ⟪(-s) • e, e⟫ ≤ 0 := by
  rw [real_inner_smul_left]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hs) real_inner_self_nonneg

/-- The points `-s e`, `0 < s < ρ`, lie in the domain of Lebesgue's example. -/
private lemma neg_smul_mem_lebesgueSpineDomain (he : ‖e‖ = 1) {ρ c : ℝ} (hc : 0 < c) {s : ℝ}
    (hs : 0 < s) (hsρ : s < ρ) : (-s) • e ∈ lebesgueSpineDomain e ρ c := by
  refine mem_lebesgueSpineDomain_of_inner_nonpos he hc ?_ ?_ ?_
  · rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_neg, abs_of_pos hs]
    exact hsρ
  · exact smul_ne_zero (neg_ne_zero.2 hs.ne') (norm_ne_zero_iff.1 (by rw [he]; exact one_ne_zero))
  · exact inner_neg_smul_self_nonpos hs.le

private lemma tendsto_neg_smul_nhdsWithin (he : ‖e‖ = 1) {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 < c) :
    Tendsto (fun s : ℝ ↦ (-s) • e) (𝓝[>] 0) (𝓝[lebesgueSpineDomain e ρ c] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun s : ℝ ↦ (-s) • e) (𝓝 0) (𝓝 ((-0 : ℝ) • e)) :=
      (continuous_neg.smul continuous_const).tendsto 0
    rw [neg_zero, zero_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsGT hρ] with s hs
    exact neg_smul_mem_lebesgueSpineDomain he hc hs.1 hs.2

/-- Every point of the closure of the domain other than the origin lies off the segment, since
the potential blows up at the other points of the segment in the closed ball of radius
`ρ < 1`. -/
private lemma notMem_segment_of_mem_closure (he : ‖e‖ = 1) {ρ c : ℝ} (hρ1 : ρ < 1) {x : E}
    (hx : x ∈ closure (lebesgueSpineDomain e ρ c)) (hx0 : x ≠ 0) : x ∉ segment ℝ 0 e := by
  intro hxs
  obtain ⟨t₀, ht₀, rfl⟩ := segment_zero_left_eq_image ℝ e ▸ hxs
  have ht₀0 : 0 < t₀ := ht₀.1.lt_of_ne fun h ↦ hx0 (by simp [← h])
  have hnorm : ‖t₀ • e‖ ≤ ρ :=
    mem_closedBall_zero_iff.1 (closure_ball_subset_closedBall
      (closure_mono inter_subset_left hx))
  rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos ht₀0] at hnorm
  have hev := eventually_nhdsWithin_iff.1
    (tendsto_atTop.1 (tendsto_lebesgueSpinePotential_atTop he ht₀0 (hnorm.trans_lt hρ1)) (1 + c))
  obtain ⟨y, hyle, hyΩ⟩ := (hev.and_frequently (mem_closure_iff_frequently.1 hx)).exists
  obtain ⟨-, hys, hylt⟩ := mem_lebesgueSpineDomain.1 hyΩ
  exact (hyle hys).not_gt hylt

variable (e) in
/-- The potential of the segment is smooth off the segment. -/
theorem contDiffOn_lebesgueSpinePotential {n : ℕ∞} :
    ContDiffOn ℝ n (lebesgueSpinePotential e) (segment ℝ 0 e)ᶜ := by
  have h := contDiffOn_integral_smul_of_contDiffOn
    (continuous_subtypeVal.integrable_of_hasCompactSupport (μ := volume) (.of_compactSpace _))
    continuous_subtypeVal (isOpen_sub_smul_ne_zero (e := e))
    (contDiffOn_inv_norm_sub_smul (n := n)) (U := (segment ℝ 0 e)ᶜ)
    fun x hx y ↦ sub_smul_ne_zero hx y.property
  simpa only [← lebesgueSpinePotential_eq_integral_unitInterval] using h

variable (e) in
private lemma continuousAt_lebesgueSpinePotential {x : E} (hx : x ∉ segment ℝ 0 e) :
    ContinuousAt (lebesgueSpinePotential e) x :=
  (contDiffOn_lebesgueSpinePotential e (n := 0)).continuousOn.continuousAt
    ((isCompact_segment ℝ 0 e).isClosed.isOpen_compl.mem_nhds hx)

variable (e) in
/-- The domain of Lebesgue's example is open, the potential being continuous off the segment. -/
theorem isOpen_lebesgueSpineDomain (ρ c : ℝ) : IsOpen (lebesgueSpineDomain e ρ c) := by
  have h := (contDiffOn_lebesgueSpinePotential e (n := 0)).continuousOn.isOpen_inter_preimage
    (isCompact_segment ℝ 0 e).isClosed.isOpen_compl (isOpen_Iio (a := 1 + c))
  exact isOpen_ball.inter h

/-- The origin is a boundary point of the domain of Lebesgue's example. -/
theorem zero_mem_frontier_lebesgueSpineDomain (he : ‖e‖ = 1) {ρ c : ℝ} (hρ : 0 < ρ)
    (hc : 0 < c) : (0 : E) ∈ frontier (lebesgueSpineDomain e ρ c) := by
  rw [(isOpen_lebesgueSpineDomain e ρ c).frontier_eq]
  refine ⟨mem_closure_iff_nhdsWithin_neBot.2 ?_, fun h ↦ ne_zero_of_mem_lebesgueSpineDomain h rfl⟩
  exact (tendsto_neg_smul_nhdsWithin he hρ hc).neBot

/-- At every boundary point of the domain inside the ball other than the origin, the potential
equals `1 + c`. -/
private lemma lebesgueSpinePotential_eq_of_mem_frontier (he : ‖e‖ = 1) {ρ c : ℝ} (hρ1 : ρ < 1)
    {x : E} (hx : x ∈ frontier (lebesgueSpineDomain e ρ c)) (hx0 : x ≠ 0) (hxρ : ‖x‖ < ρ) :
    lebesgueSpinePotential e x = 1 + c := by
  rw [(isOpen_lebesgueSpineDomain e ρ c).frontier_eq] at hx
  have hxs := notMem_segment_of_mem_closure he hρ1 hx.1 hx0
  refine le_antisymm (ContinuousWithinAt.closure_le hx.1
    (continuousAt_lebesgueSpinePotential e hxs).continuousWithinAt continuousWithinAt_const
    fun y hy ↦ (mem_lebesgueSpineDomain.1 hy).2.2.le) ?_
  by_contra! h
  exact hx.2 (mem_lebesgueSpineDomain.2 ⟨hxρ, hxs, h⟩)

variable [FiniteDimensional ℝ E]

/-- In dimension `3`, `x ↦ ‖x - a‖⁻¹` is harmonic away from `a`. -/
private lemma harmonicAt_inv_norm_sub (hE : finrank ℝ E = 3) {x a : E} (hxa : x ≠ a) :
    HarmonicAt (fun y ↦ ‖y - a‖⁻¹) x := by
  have hpow : (fun y : E ↦ ‖y‖ ^ (2 - finrank ℝ E : ℝ)) = fun y ↦ ‖y‖⁻¹ := by
    funext y
    rw [hE]
    norm_num [Real.rpow_neg_one]
  have h := harmonicAt_norm_rpow_two_sub_finrank (sub_ne_zero.2 hxa)
  rw [hpow, sub_eq_add_neg] at h
  simpa only [← sub_eq_add_neg] using
    (harmonicAt_comp_add_right_iff (f := fun y : E ↦ ‖y‖⁻¹) (x := x) (a := -a)).2 h

variable (e) in
/-- In dimension `3` the potential of the segment is harmonic off the segment. -/
theorem harmonicOnNhd_lebesgueSpinePotential (hE : finrank ℝ E = 3) :
    HarmonicOnNhd (lebesgueSpinePotential e) (segment ℝ 0 e)ᶜ := by
  have h := harmonicOnNhd_integral_smul_of_contDiffOn
    (continuous_subtypeVal.integrable_of_hasCompactSupport (μ := volume) (.of_compactSpace _))
    continuous_subtypeVal (isOpen_sub_smul_ne_zero (e := e))
    (contDiffOn_inv_norm_sub_smul (n := 2))
    (isCompact_segment ℝ 0 e).isClosed.isOpen_compl (fun x hx y ↦ sub_smul_ne_zero hx y.property)
    fun y x hx ↦ harmonicAt_inv_norm_sub hE (sub_ne_zero.1 (sub_smul_ne_zero hx y.property))
  simpa only [← lebesgueSpinePotential_eq_integral_unitInterval] using h

/-- In dimension `3`, `x ↦ η ‖x‖⁻¹` is harmonic on every set avoiding the origin. -/
private lemma harmonicOnNhd_const_mul_inv_norm (hE : finrank ℝ E = 3) (η : ℝ) {U : Set E}
    (hU : (0 : E) ∉ U) : HarmonicOnNhd (fun y : E ↦ η * ‖y‖⁻¹) U := fun x hx ↦ by
  have h := (harmonicAt_inv_norm_sub hE (a := 0) (fun h ↦ hU (h ▸ hx))).const_smul (c := η)
  simp only [sub_zero] at h
  exact h

variable [MeasurableSpace E] [BorelSpace E]

/-- At the boundary points of the domain other than the origin, `1 + c - u ≤ ((1 + c) / m) w`
for a barrier `w` at the origin that is at least `m > 0` at distance at least `ρ / 2` from the
origin: inside `ball 0 (ρ / 2)` the left side vanishes, and outside it `w ≥ m`. -/
private lemma sub_lebesgueSpinePotential_le_of_mem_frontier (he : ‖e‖ = 1) {ρ c m : ℝ}
    (hρ1 : ρ < 1) (hc : 0 < c) {w : E → ℝ} (hw : IsBarrier (lebesgueSpineDomain e ρ c) 0 w)
    (hm0 : 0 < m) (hm : ∀ x ∈ closure (lebesgueSpineDomain e ρ c) \ ball 0 (ρ / 2), m ≤ w x)
    {y : E} (hy : y ∈ frontier (lebesgueSpineDomain e ρ c)) (hy0 : y ≠ 0) :
    1 + c - lebesgueSpinePotential e y ≤ (1 + c) / m * w y := by
  have hyc := frontier_subset_closure hy
  by_cases hyρ : y ∈ ball (0 : E) (ρ / 2)
  · rw [mem_ball_zero_iff] at hyρ
    rw [lebesgueSpinePotential_eq_of_mem_frontier he hρ1 hy hy0
      (by linarith [norm_nonneg y]), sub_self]
    exact mul_nonneg (div_nonneg (by linarith) hm0.le) (hw.pos y hyc hy0).le
  · have : 1 + c ≤ (1 + c) / m * w y := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hm0]
      exact mul_le_mul_of_nonneg_left (hm y ⟨hyc, hyρ⟩) (by linarith)
    linarith [lebesgueSpinePotential_nonneg e y]

/-- The boundary inequality of the comparison step of Lebesgue's example, at a point `y ≠ 0` of
the closure of the domain that is either a boundary point or so close to the origin that
`η / ‖y‖ ≥ 1 + c`. -/
private lemma sub_lebesgueSpinePotential_le_add_of_mem_closure {ρ c k η : ℝ} (hc : 0 < c)
    {w : E → ℝ} (hw : IsBarrier (lebesgueSpineDomain e ρ c) 0 w) (hk : 0 ≤ k)
    (hfr : ∀ y ∈ frontier (lebesgueSpineDomain e ρ c), y ≠ 0 →
      1 + c - lebesgueSpinePotential e y ≤ k * w y)
    (hη : 0 < η) {y : E} (hy : y ∈ closure (lebesgueSpineDomain e ρ c)) (hy0 : y ≠ 0)
    (hcase : ‖y‖ ≤ η / (1 + c) ∨ y ∈ frontier (lebesgueSpineDomain e ρ c)) :
    1 + c - lebesgueSpinePotential e y ≤ k * w y + η * ‖y‖⁻¹ := by
  have hwy : 0 ≤ k * w y := mul_nonneg hk (hw.pos y hy hy0).le
  have hηy : 0 ≤ η * ‖y‖⁻¹ := by positivity
  rcases hcase with hyη | hyfr
  · -- Near the origin the term `η / ‖y‖` dominates.
    have : 1 + c ≤ η * ‖y‖⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (norm_pos_iff.2 hy0)]
      rwa [le_div_iff₀ (by linarith), mul_comm] at hyη
    linarith [lebesgueSpinePotential_nonneg e y]
  · linarith [hfr y hyfr hy0]

/-- The comparison step of Lebesgue's example. Let `w` be a barrier at the origin and `k ≥ 0`
with `1 + c - u ≤ k w` at the boundary points of the domain other than the origin. Then
`1 + c - u ≤ k w + η / ‖x‖` on the domain for every `η > 0`: the term `η / ‖x‖`, harmonic in
dimension `3`, dominates near the origin, where the boundary behaviour of `u` is unknown, and
the comparison principle applies on the domain minus a small ball around the origin. -/
private lemma sub_lebesgueSpinePotential_le_add_of_isBarrier (hE : finrank ℝ E = 3)
    (he : ‖e‖ = 1) {ρ c k : ℝ} (hρ1 : ρ < 1) (hc : 0 < c) {w : E → ℝ}
    (hw : IsBarrier (lebesgueSpineDomain e ρ c) 0 w) (hk : 0 ≤ k)
    (hfr : ∀ y ∈ frontier (lebesgueSpineDomain e ρ c), y ≠ 0 →
      1 + c - lebesgueSpinePotential e y ≤ k * w y)
    {x : E} (hx : x ∈ lebesgueSpineDomain e ρ c) {η : ℝ} (hη : 0 < η) :
    1 + c - lebesgueSpinePotential e x ≤ k * w x + η * ‖x‖⁻¹ := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  set Ω := lebesgueSpineDomain e ρ c
  have hΩo : IsOpen Ω := isOpen_lebesgueSpineDomain e ρ c
  have hx0 := ne_zero_of_mem_lebesgueSpineDomain hx
  set r := min (‖x‖ / 2) (η / (1 + c))
  have hr : 0 < r := lt_min (half_pos (norm_pos_iff.2 hx0)) (by positivity)
  set U := Ω ∩ {y : E | r < ‖y‖}
  have hUo : IsOpen U := hΩo.inter (isOpen_lt continuous_const continuous_norm)
  have hclU : closure U ⊆ closure Ω ∩ {y : E | r ≤ ‖y‖} :=
    (closure_inter_subset_inter_closure _ _).trans
      (inter_subset_inter_right _ (closure_lt_subset_le continuous_const continuous_norm))
  have hU0 : ∀ y ∈ closure U, y ≠ 0 := fun y hy h ↦ by
    have : r ≤ ‖y‖ := (hclU hy).2
    rw [h, norm_zero] at this
    linarith
  have hsub : SubharmonicOn (fun y ↦ 1 + c - lebesgueSpinePotential e y) U :=
    ((harmonicOnNhd_const (1 + c)).sub ((harmonicOnNhd_lebesgueSpinePotential e hE).mono
      fun y (hy : y ∈ U) ↦ (mem_lebesgueSpineDomain.1 hy.1).2.1)).subharmonicOn
  have hsubc : ContinuousOn (fun y ↦ 1 + c - lebesgueSpinePotential e y) (closure U) :=
    fun y hy ↦ (continuousAt_const.sub (continuousAt_lebesgueSpinePotential e
      (notMem_segment_of_mem_closure he hρ1 (hclU hy).1 (hU0 y hy)))).continuousWithinAt
  have hsup : SubharmonicOn (-fun y ↦ k * w y + η * ‖y‖⁻¹) U := by
    have h := ((hw.subharmonicOn_neg.mono inter_subset_left).const_smul hk).sub_harmonicOnNhd
      (harmonicOnNhd_const_mul_inv_norm hE η fun h ↦ hU0 0 (subset_closure h) rfl) hUo
    convert h using 1
    funext y
    simp only [Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hsupc : ContinuousOn (fun y ↦ k * w y + η * ‖y‖⁻¹) (closure U) :=
    (continuousOn_const.mul (hw.continuousOn.mono (closure_mono inter_subset_left))).add
      (continuousOn_const.mul (continuous_norm.continuousOn.inv₀ fun y hy ↦
        norm_ne_zero_iff.2 (hU0 y hy)))
  refine hsub.le_of_le_frontier_of_subharmonicOn_neg hUo
    ((isBounded_lebesgueSpineDomain e ρ c).subset inter_subset_left) hsubc hsup hsupc
    (fun y hy ↦ ?_) x
    (subset_closure ⟨hx, (min_le_left _ _).trans_lt (half_lt_self (norm_pos_iff.2 hx0))⟩)
  rw [hUo.frontier_eq] at hy
  refine sub_lebesgueSpinePotential_le_add_of_mem_closure hc hw hk hfr hη (hclU hy.1).1
    (hU0 y hy.1) ?_
  refine (le_or_gt ‖y‖ (η / (1 + c))).imp id fun hyη ↦ ?_
  rw [hΩo.frontier_eq]
  exact ⟨(hclU hy.1).1, fun h ↦ hy.2 ⟨h, (min_le_right _ _).trans_lt hyη⟩⟩

/-- **Lebesgue's spine**: the origin is an irregular boundary point of the domain
`TauCeti.lebesgueSpineDomain e ρ c` in dimension `3`, for `0 < ρ < 1` and `c > 0`. No function
is a barrier at `0` relative to it. -/
theorem not_isBarrier_lebesgueSpineDomain (hE : finrank ℝ E = 3) (he : ‖e‖ = 1) {ρ c : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c) (w : E → ℝ) :
    ¬ IsBarrier (lebesgueSpineDomain e ρ c) 0 w := by
  intro hw
  set Ω := lebesgueSpineDomain e ρ c
  -- On the compact set `closure Ω \ ball 0 (ρ / 2)`, the barrier is at least some `m > 0`.
  obtain ⟨m, hm0, hm⟩ := ((isBounded_lebesgueSpineDomain e ρ c).isCompact_closure.diff
    (isOpen_ball (x := (0 : E)) (ε := ρ / 2))).exists_forall_le'
    (hw.continuousOn.mono sdiff_subset) fun x hx ↦
      hw.pos x hx.1 fun h ↦ hx.2 (by rw [h]; exact mem_ball_self (half_pos hρ0))
  set k := (1 + c) / m
  have hk : 0 ≤ k := div_nonneg (by linarith) hm0.le
  -- Letting `η → 0` in the comparison step gives `1 + c - u ≤ k w` on `Ω`.
  have hmain : ∀ x ∈ Ω, 1 + c - lebesgueSpinePotential e x ≤ k * w x := by
    intro x hx
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 (ne_zero_of_mem_lebesgueSpineDomain hx)
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have := sub_lebesgueSpinePotential_le_add_of_isBarrier hE he hρ1 hc hw hk
      (fun y hy hy0 ↦ sub_lebesgueSpinePotential_le_of_mem_frontier he hρ1 hc hw hm0 hm hy hy0)
      hx (mul_pos hε hxpos)
    rwa [mul_assoc, mul_inv_cancel₀ hxpos.ne', mul_one] at this
  -- Along `-s e` the barrier tends to `w 0 = 0`, while `1 + c - u ≥ c` there.
  have hlim : Tendsto (fun s : ℝ ↦ k * w ((-s) • e)) (𝓝[>] 0) (𝓝 0) := by
    have hwc : Tendsto w (𝓝[Ω] 0) (𝓝 0) := by
      have h := (hw.continuousOn 0 (mem_closure_iff_nhdsWithin_neBot.2
        (tendsto_neg_smul_nhdsWithin he hρ0 hc).neBot)).mono_left
        (nhdsWithin_mono _ subset_closure)
      rwa [hw.apply_self] at h
    simpa using (hwc.comp (tendsto_neg_smul_nhdsWithin he hρ0 hc)).const_mul k
  obtain ⟨s, hsk, hs⟩ := ((hlim.eventually (gt_mem_nhds hc)).and
    (Ioo_mem_nhdsGT hρ0)).exists
  have hsΩ := neg_smul_mem_lebesgueSpineDomain he hc hs.1 hs.2
  have hule : lebesgueSpinePotential e ((-s) • e) ≤ 1 := lebesgueSpinePotential_le_one he
    (ne_zero_of_mem_lebesgueSpineDomain hsΩ) (inner_neg_smul_self_nonpos hs.1.le)
  linarith [hmain _ hsΩ]

/-- **The Dirichlet problem on Lebesgue's spine domain is not solvable**: in dimension `3`, for
`0 < ρ < 1` and `c > 0`, no function harmonic in `TauCeti.lebesgueSpineDomain e ρ c` and
continuous on its closure takes the boundary values `‖x‖`. A solution would be a barrier at the
origin (`InnerProductSpace.HarmonicOnNhd.isBarrier`). -/
theorem not_exists_harmonicOnNhd_lebesgueSpineDomain_eq_norm (hE : finrank ℝ E = 3)
    (he : ‖e‖ = 1) {ρ c : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c) :
    ¬ ∃ v : E → ℝ, HarmonicOnNhd v (lebesgueSpineDomain e ρ c) ∧
      ContinuousOn v (closure (lebesgueSpineDomain e ρ c)) ∧
      ∀ x ∈ frontier (lebesgueSpineDomain e ρ c), v x = ‖x‖ := by
  rintro ⟨v, hv, hvc, hvg⟩
  exact not_isBarrier_lebesgueSpineDomain hE he hρ0 hρ1 hc v
    (hv.isBarrier (isOpen_lebesgueSpineDomain e ρ c) (isBounded_lebesgueSpineDomain e ρ c) hvc
      (zero_mem_frontier_lebesgueSpineDomain he hρ0 hc) fun x hx ↦ by
        rw [hvg x hx, dist_zero_right])

end TauCeti
