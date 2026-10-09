/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.FrechetMean.Basic
public import TauCeti.Topology.MetricSpace.Length
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Fréchet barycenters of two weighted points

For `1 < p < ∞` and `t ∈ [0, 1]`, the `p`-Fréchet barycenters of the law
`(1 - t) δ_x + t δ_y` on a pseudometric space minimize
`z ↦ (1 - t) d(z, x) ^ p + t d(z, y) ^ p`. Writing `a = d(x, z)`, `b = d(z, y)` and
`D = d(x, y)`, the triangle inequality only gives `a + b ≥ D`, and the scalar problem of
minimizing `(1 - t) a ^ p + t b ^ p` subject to `a + b ≥ D` has the unique solution
`a = τ D`, `b = (1 - τ) D`, where

`τ = t ^ (1 / (p - 1)) / ((1 - t) ^ (1 / (p - 1)) + t ^ (1 / (p - 1)))`

is `TauCeti.twoPointBarycenterTime p t`. Consequently a point at distance `τ D` from `x` and
`(1 - τ) D` from `y` is a barycenter; once such a point exists, these distances characterize
the barycenters; and in a geodesic space the barycenters are exactly the points dividing some
geodesic from `x` to `y` at time `τ`. For `p = 2` the time is `t` itself, so the quadratic
barycenter of `(1 - t) δ_x + t δ_y` sits at time `t` of a geodesic.

Applied to a Wasserstein space that is a geodesic space, such as `P_p(ℝ)`, this locates the
barycenter of two laws on a Wasserstein geodesic between them.

## Main definitions

* `TauCeti.twoPointBarycenterTime p t`: the time `τ` above.

## Main statements

* `TauCeti.isFrechetBarycenter_of_dist_eq_twoPointBarycenterTime`: a point at distances
  `τ D` and `(1 - τ) D` from `x` and `y` is a `p`-Fréchet barycenter of `(1 - t) δ_x + t δ_y`.
* `TauCeti.IsFrechetBarycenter.dist_eq_twoPointBarycenterTime`: if some such point exists,
  every barycenter is at these distances.
* `TauCeti.isFrechetBarycenter_iff_dist_eq_twoPointBarycenterTime` and
  `TauCeti.IsGeodesicSegment.isFrechetBarycenter_twoPointBarycenterTime`: the characterization
  in a geodesic space, and the barycenter at time `τ` of every geodesic segment.
* `TauCeti.IsGeodesicSegment.isFrechetBarycenter_two`: the quadratic case, at time `t`.

## References

* M. Agueh and G. Carlier, *Barycenters in the Wasserstein space*, SIAM J. Math. Anal. 43
  (2011), 904--924.
* K.-T. Sturm, *Probability measures on metric spaces of nonpositive curvature*, in *Heat
  Kernels and Analysis on Manifolds, Graphs, and Metric Spaces*, Contemp. Math. 338 (2003),
  357--390.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

/-! ### The barycentric time -/

/-- The **barycentric time** of exponent `p` and weight `t`:
`t ^ (1 / (p - 1)) / ((1 - t) ^ (1 / (p - 1)) + t ^ (1 / (p - 1)))`. For `1 < p` and
`t ∈ [0, 1]`, the `p`-Fréchet barycenters of `(1 - t) δ_x + t δ_y` in a geodesic space are the
points at this time on geodesics from `x` to `y`; see
`TauCeti.isFrechetBarycenter_iff_dist_eq_twoPointBarycenterTime`. -/
def twoPointBarycenterTime (p t : ℝ) : ℝ :=
  t ^ (p - 1)⁻¹ / ((1 - t) ^ (p - 1)⁻¹ + t ^ (p - 1)⁻¹)

/-- The barycentric time, unfolded. -/
theorem twoPointBarycenterTime_def (p t : ℝ) :
    twoPointBarycenterTime p t = t ^ (p - 1)⁻¹ / ((1 - t) ^ (p - 1)⁻¹ + t ^ (p - 1)⁻¹) := by
  rw [twoPointBarycenterTime]

/-- At exponent `2` the barycentric time is the weight itself. -/
@[simp]
theorem twoPointBarycenterTime_two (t : ℝ) : twoPointBarycenterTime 2 t = t := by
  norm_num [twoPointBarycenterTime_def]

/-- Away from the degenerate exponent `1`, the barycentric time of weight `0` is `0`. -/
@[simp]
theorem twoPointBarycenterTime_zero {p : ℝ} (hp : p ≠ 1) : twoPointBarycenterTime p 0 = 0 := by
  simp [twoPointBarycenterTime_def, Real.zero_rpow (inv_ne_zero (sub_ne_zero.2 hp))]

/-- Away from the degenerate exponent `1`, the barycentric time of weight `1` is `1`. -/
@[simp]
theorem twoPointBarycenterTime_one {p : ℝ} (hp : p ≠ 1) : twoPointBarycenterTime p 1 = 1 := by
  simp [twoPointBarycenterTime_def, Real.zero_rpow (inv_ne_zero (sub_ne_zero.2 hp))]

/-- The denominator of the barycentric time is positive for every weight in `[0, 1]`. -/
private theorem rpow_add_rpow_pos (r : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < (1 - t) ^ r + t ^ r := by
  rcases ht.1.eq_or_lt with rfl | ht₀
  · simpa using add_pos_of_pos_of_nonneg zero_lt_one (Real.rpow_nonneg le_rfl r)
  · exact add_pos_of_nonneg_of_pos (Real.rpow_nonneg (sub_nonneg.2 ht.2) r)
      (Real.rpow_pos_of_pos ht₀ r)

/-- The barycentric time of the complementary weight is the complementary time. -/
theorem twoPointBarycenterTime_one_sub (p : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    twoPointBarycenterTime p (1 - t) = 1 - twoPointBarycenterTime p t := by
  have hS := (rpow_add_rpow_pos (p - 1)⁻¹ ht).ne'
  rw [twoPointBarycenterTime_def, twoPointBarycenterTime_def, sub_sub_cancel, add_comm (t ^ _),
    eq_sub_iff_add_eq, ← add_div, div_self hS]

/-- The barycentric time of a weight in `[0, 1]` lies in `[0, 1]`. -/
theorem twoPointBarycenterTime_mem_Icc (p : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    twoPointBarycenterTime p t ∈ Icc (0 : ℝ) 1 := by
  have hS := rpow_add_rpow_pos (p - 1)⁻¹ ht
  rw [twoPointBarycenterTime_def]
  exact ⟨div_nonneg (Real.rpow_nonneg ht.1 _) hS.le, (div_le_one hS).2
    (le_add_of_nonneg_left (Real.rpow_nonneg (sub_nonneg.2 ht.2) _))⟩

/-! ### The scalar minimization problem -/

section Scalar

variable {p t D a b : ℝ}

/-- The first-order condition at the barycentric time: the two weighted derivatives
`(1 - t) a ^ (p - 1)` and `t b ^ (p - 1)` agree at `a = τ D`, `b = (1 - τ) D`. -/
private theorem mul_rpow_sub_one_eq (hp : 1 < p) (ht : t ∈ Icc (0 : ℝ) 1) (hD : 0 ≤ D) :
    (1 - t) * (twoPointBarycenterTime p t * D) ^ (p - 1) =
      t * ((1 - twoPointBarycenterTime p t) * D) ^ (p - 1) := by
  have hS := rpow_add_rpow_pos (p - 1)⁻¹ ht
  have hp₁ : p - 1 ≠ 0 := sub_ne_zero.2 hp.ne'
  have hDS : 0 ≤ D / ((1 - t) ^ (p - 1)⁻¹ + t ^ (p - 1)⁻¹) := div_nonneg hD hS.le
  have hτ : twoPointBarycenterTime p t * D =
      t ^ (p - 1)⁻¹ * (D / ((1 - t) ^ (p - 1)⁻¹ + t ^ (p - 1)⁻¹)) := by
    rw [twoPointBarycenterTime_def]
    ring
  have hτ' : (1 - twoPointBarycenterTime p t) * D =
      (1 - t) ^ (p - 1)⁻¹ * (D / ((1 - t) ^ (p - 1)⁻¹ + t ^ (p - 1)⁻¹)) := by
    rw [← twoPointBarycenterTime_one_sub p ht, twoPointBarycenterTime_def, sub_sub_cancel,
      add_comm (t ^ _)]
    ring
  rw [hτ, hτ', Real.mul_rpow (Real.rpow_nonneg ht.1 _) hDS,
    Real.mul_rpow (Real.rpow_nonneg (sub_nonneg.2 ht.2) _) hDS, Real.rpow_inv_rpow ht.1 hp₁,
    Real.rpow_inv_rpow (sub_nonneg.2 ht.2) hp₁]
  ring

/-- The excess of `(1 - t) a ^ p + t b ^ p` over its value at `a = τ D`, `b = (1 - τ) D`
splits as two weighted tangent-line gaps plus a multiple of the slack `a + b - D`. -/
private theorem mul_rpow_add_mul_rpow_eq (hp : 1 < p) (ht : t ∈ Icc (0 : ℝ) 1) (hD : 0 ≤ D) :
    (1 - t) * a ^ p + t * b ^ p =
      (1 - t) * (twoPointBarycenterTime p t * D) ^ p +
          t * ((1 - twoPointBarycenterTime p t) * D) ^ p +
        (1 - t) * (a ^ p - ((twoPointBarycenterTime p t * D) ^ p +
          p * (twoPointBarycenterTime p t * D) ^ (p - 1) *
            (a - twoPointBarycenterTime p t * D))) +
        t * (b ^ p - (((1 - twoPointBarycenterTime p t) * D) ^ p +
          p * ((1 - twoPointBarycenterTime p t) * D) ^ (p - 1) *
            (b - (1 - twoPointBarycenterTime p t) * D))) +
        p * ((1 - t) * (twoPointBarycenterTime p t * D) ^ (p - 1)) * (a + b - D) := by
  linear_combination p * ((1 - twoPointBarycenterTime p t) * D - b) *
    mul_rpow_sub_one_eq hp ht hD

/-- **The scalar two-point problem.** For `1 < p` and `t ∈ [0, 1]`, if `a, b ≥ 0` and
`a + b ≥ D ≥ 0`, then `(1 - t) a ^ p + t b ^ p` is at least its value at `a = τ D`,
`b = (1 - τ) D`. -/
private theorem mul_rpow_add_mul_rpow_le (hp : 1 < p) (ht : t ∈ Icc (0 : ℝ) 1) (hD : 0 ≤ D)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : D ≤ a + b) :
    (1 - t) * (twoPointBarycenterTime p t * D) ^ p +
        t * ((1 - twoPointBarycenterTime p t) * D) ^ p ≤
      (1 - t) * a ^ p + t * b ^ p := by
  have hτ := twoPointBarycenterTime_mem_Icc p ht
  have ha' := Real.rpow_add_mul_rpow_sub_one_mul_sub_le_rpow hp.le ha (mul_nonneg hτ.1 hD)
  have hb' := Real.rpow_add_mul_rpow_sub_one_mul_sub_le_rpow hp.le hb
    (mul_nonneg (sub_nonneg.2 hτ.2) hD)
  have hslack : 0 ≤ p * ((1 - t) * (twoPointBarycenterTime p t * D) ^ (p - 1)) * (a + b - D) :=
    mul_nonneg (mul_nonneg (by linarith) (mul_nonneg (sub_nonneg.2 ht.2)
      (Real.rpow_nonneg (mul_nonneg hτ.1 hD) _))) (sub_nonneg.2 hab)
  rw [mul_rpow_add_mul_rpow_eq (a := a) (b := b) hp ht hD]
  have := mul_nonneg (sub_nonneg.2 ht.2) (sub_nonneg.2 ha')
  have := mul_nonneg ht.1 (sub_nonneg.2 hb')
  linarith

/-- **The equality case of the scalar two-point problem.** If, in addition to the hypotheses of
`mul_rpow_add_mul_rpow_le`, the triangle inequalities `a ≤ D + b` and `b ≤ D + a` hold and
`(1 - t) a ^ p + t b ^ p` attains the minimum, then `a = τ D` and `b = (1 - τ) D`. -/
private theorem eq_of_mul_rpow_add_mul_rpow_le (hp : 1 < p) (ht : t ∈ Icc (0 : ℝ) 1)
    (hD : 0 ≤ D) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : D ≤ a + b) (ha_le : a ≤ D + b)
    (hb_le : b ≤ D + a)
    (hle : (1 - t) * a ^ p + t * b ^ p ≤
      (1 - t) * (twoPointBarycenterTime p t * D) ^ p +
        t * ((1 - twoPointBarycenterTime p t) * D) ^ p) :
    a = twoPointBarycenterTime p t * D ∧ b = (1 - twoPointBarycenterTime p t) * D := by
  have hp₀ : p ≠ 0 := by linarith
  rcases ht.1.eq_or_lt with rfl | ht₀
  · -- Weight zero: the time is `0`, the minimum is `0`, and `a = 0` forces `b = D`.
    simp only [twoPointBarycenterTime_zero hp.ne', sub_zero, one_mul, zero_mul,
      Real.zero_rpow hp₀, add_zero] at hle ⊢
    have ha₀ : a = 0 := by
      by_contra h
      exact (Real.rpow_pos_of_pos (ha.lt_of_ne' h) p).not_ge hle
    subst ha₀
    exact ⟨rfl, le_antisymm (by linarith) (by linarith)⟩
  rcases ht.2.eq_or_lt with rfl | ht₁
  · -- Weight one: the time is `1`, the minimum is `0`, and `b = 0` forces `a = D`.
    simp only [twoPointBarycenterTime_one hp.ne', sub_self, zero_mul, one_mul,
      Real.zero_rpow hp₀, mul_zero, zero_add] at hle ⊢
    have hb₀ : b = 0 := by
      by_contra h
      exact (Real.rpow_pos_of_pos (hb.lt_of_ne' h) p).not_ge hle
    subst hb₀
    exact ⟨le_antisymm (by linarith) (by linarith), rfl⟩
  -- Interior weight: each weighted tangent-line gap vanishes, so `a` and `b` are the
  -- tangency points.
  have hτ := twoPointBarycenterTime_mem_Icc p ht
  have hτD : 0 ≤ twoPointBarycenterTime p t * D := mul_nonneg hτ.1 hD
  have hτD' : 0 ≤ (1 - twoPointBarycenterTime p t) * D := mul_nonneg (sub_nonneg.2 hτ.2) hD
  have ha' := Real.rpow_add_mul_rpow_sub_one_mul_sub_le_rpow hp.le ha hτD
  have hb' := Real.rpow_add_mul_rpow_sub_one_mul_sub_le_rpow hp.le hb hτD'
  have hslack : 0 ≤ p * ((1 - t) * (twoPointBarycenterTime p t * D) ^ (p - 1)) * (a + b - D) :=
    mul_nonneg (mul_nonneg (by linarith) (mul_nonneg (sub_nonneg.2 ht.2)
      (Real.rpow_nonneg hτD _))) (sub_nonneg.2 hab)
  rw [mul_rpow_add_mul_rpow_eq (a := a) (b := b) hp ht hD] at hle
  have hga := mul_nonneg (sub_nonneg.2 ht₁.le) (sub_nonneg.2 ha')
  have hgb := mul_nonneg ht.1 (sub_nonneg.2 hb')
  constructor
  · by_contra h
    have := mul_pos (sub_pos.2 ht₁)
      (sub_pos.2 (Real.rpow_add_mul_rpow_sub_one_mul_sub_lt_rpow hp ha hτD h))
    linarith
  · by_contra h
    have := mul_pos ht₀ (sub_pos.2 (Real.rpow_add_mul_rpow_sub_one_mul_sub_lt_rpow hp hb hτD' h))
    linarith

end Scalar

/-! ### Barycenters of two weighted points -/

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {p : ℝ≥0∞} {t : ℝ} {x y z : X}

/-- The Fréchet power functional of `(1 - t) δ_x + t δ_y` is the weighted sum of powers of the
distances to `x` and `y`. -/
private theorem frechetPower_ofReal_smul_dirac_add (p : ℝ≥0∞) (ht : t ∈ Icc (0 : ℝ) 1) (x y z : X) :
    frechetPower p (ENNReal.ofReal (1 - t) • Measure.dirac x + ENNReal.ofReal t • Measure.dirac y)
        z =
      ENNReal.ofReal ((1 - t) * dist z x ^ p.toReal + t * dist z y ^ p.toReal) := by
  have hm : Measurable fun w ↦ edist z w ^ p.toReal :=
    (continuous_const.edist continuous_id).measurable.pow_const _
  have hpow (w : X) : edist z w ^ p.toReal = ENNReal.ofReal (dist z w ^ p.toReal) := by
    rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg ENNReal.toReal_nonneg]
  rw [frechetPower_def, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac' _ hm, lintegral_dirac' _ hm, hpow, hpow,
    ENNReal.ofReal_add (mul_nonneg (sub_nonneg.2 ht.2) (by positivity))
      (mul_nonneg ht.1 (by positivity)),
    ENNReal.ofReal_mul (sub_nonneg.2 ht.2), ENNReal.ofReal_mul ht.1, smul_eq_mul, smul_eq_mul]

/-- For `0 < p < ∞`, a point is a `p`-Fréchet barycenter of `(1 - t) δ_x + t δ_y` exactly when it
minimizes the real functional `w ↦ (1 - t) d(w, x) ^ p + t d(w, y) ^ p`. -/
private theorem isFrechetBarycenter_ofReal_smul_dirac_add_iff (hp₀ : p ≠ 0) (hp_top : p ≠ ⊤)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    IsFrechetBarycenter p
        (ENNReal.ofReal (1 - t) • Measure.dirac x + ENNReal.ofReal t • Measure.dirac y) z ↔
      ∀ w, (1 - t) * dist z x ^ p.toReal + t * dist z y ^ p.toReal ≤
        (1 - t) * dist w x ^ p.toReal + t * dist w y ^ p.toReal := by
  have hm (w : X) : AEMeasurable (fun v ↦ edist w v)
      (ENNReal.ofReal (1 - t) • Measure.dirac x + ENNReal.ofReal t • Measure.dirac y) :=
    (continuous_const.edist continuous_id).measurable.aemeasurable
  have hR : frechetRadius p
      (ENNReal.ofReal (1 - t) • Measure.dirac x + ENNReal.ofReal t • Measure.dirac y) z ≠ ⊤ := by
    intro h
    have := frechetRadius_rpow_eq_frechetPower hp₀ hp_top (hm z)
    rw [h, ENNReal.top_rpow_of_pos (ENNReal.toReal_pos hp₀ hp_top),
      frechetPower_ofReal_smul_dirac_add p ht] at this
    exact ENNReal.ofReal_ne_top this.symm
  rw [isFrechetBarycenter_iff_forall_frechetPower_le hp₀ hp_top (hm z) hm, and_iff_right hR]
  refine forall_congr' fun w ↦ ?_
  rw [frechetPower_ofReal_smul_dirac_add p ht, frechetPower_ofReal_smul_dirac_add p ht,
    ENNReal.ofReal_le_ofReal_iff (add_nonneg (mul_nonneg (sub_nonneg.2 ht.2) (by positivity))
      (mul_nonneg ht.1 (by positivity)))]

variable (hp : 1 < p) (hp_top : p ≠ ⊤) (ht : t ∈ Icc (0 : ℝ) 1)
include hp hp_top ht

/-- **A point dividing `x` and `y` at the barycentric time is a barycenter.** For `1 < p < ∞`
and `t ∈ [0, 1]`, a point `z` with `d(x, z) = τ d(x, y)` and `d(z, y) = (1 - τ) d(x, y)`, where
`τ = TauCeti.twoPointBarycenterTime p t`, is a `p`-Fréchet barycenter of `(1 - t) δ_x + t δ_y`.
-/
theorem isFrechetBarycenter_of_dist_eq_twoPointBarycenterTime
    (hxz : dist x z = twoPointBarycenterTime p.toReal t * dist x y)
    (hzy : dist z y = (1 - twoPointBarycenterTime p.toReal t) * dist x y) :
    IsFrechetBarycenter p
      (ENNReal.ofReal (1 - t) • Measure.dirac x + ENNReal.ofReal t • Measure.dirac y) z := by
  have hp₁ : 1 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2 hp
  rw [isFrechetBarycenter_ofReal_smul_dirac_add_iff (by positivity) hp_top ht]
  intro w
  rw [dist_comm z x, hxz, hzy]
  refine mul_rpow_add_mul_rpow_le hp₁ ht dist_nonneg dist_nonneg dist_nonneg ?_
  linarith [dist_triangle x w y, dist_comm x w]

/-- **Barycenters divide `x` and `y` at the barycentric time.** For `1 < p < ∞` and
`t ∈ [0, 1]`, if some point is at distances `τ d(x, y)` from `x` and `(1 - τ) d(x, y)` from `y`,
where `τ = TauCeti.twoPointBarycenterTime p t`, then every `p`-Fréchet barycenter of
`(1 - t) δ_x + t δ_y` is at these distances. -/
theorem IsFrechetBarycenter.dist_eq_twoPointBarycenterTime
    (h : IsFrechetBarycenter p
      (ENNReal.ofReal (1 - t) • Measure.dirac x + ENNReal.ofReal t • Measure.dirac y) z)
    (hw : ∃ w, dist x w = twoPointBarycenterTime p.toReal t * dist x y ∧
      dist w y = (1 - twoPointBarycenterTime p.toReal t) * dist x y) :
    dist x z = twoPointBarycenterTime p.toReal t * dist x y ∧
      dist z y = (1 - twoPointBarycenterTime p.toReal t) * dist x y := by
  have hp₁ : 1 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2 hp
  obtain ⟨w, hxw, hwy⟩ := hw
  have hle := (isFrechetBarycenter_ofReal_smul_dirac_add_iff (by positivity) hp_top ht).1 h w
  rw [dist_comm w x, hxw, hwy] at hle
  rw [dist_comm x z]
  refine eq_of_mul_rpow_add_mul_rpow_le hp₁ ht dist_nonneg dist_nonneg dist_nonneg ?_ ?_ ?_ hle
  · linarith [dist_triangle x z y, dist_comm x z]
  · linarith [dist_triangle z y x, dist_comm x y]
  · linarith [dist_triangle z x y]

/-- **The barycenter of two weighted points on a geodesic segment.** For `1 < p < ∞` and
`t ∈ [0, 1]`, the point at time `τ = TauCeti.twoPointBarycenterTime p t` of a geodesic segment
from `x` to `y` is a `p`-Fréchet barycenter of `(1 - t) δ_x + t δ_y`. -/
theorem IsGeodesicSegment.isFrechetBarycenter_twoPointBarycenterTime {γ : ℝ → X}
    (hγ : IsGeodesicSegment γ x y) :
    IsFrechetBarycenter p
      (ENNReal.ofReal (1 - t) • Measure.dirac x + ENNReal.ofReal t • Measure.dirac y)
      (γ (twoPointBarycenterTime p.toReal t)) :=
  isFrechetBarycenter_of_dist_eq_twoPointBarycenterTime hp hp_top ht
    (hγ.dist_source_apply (twoPointBarycenterTime_mem_Icc _ ht))
    (hγ.dist_apply_target (twoPointBarycenterTime_mem_Icc _ ht))

/-- **Barycenters of two weighted points in a geodesic space.** For `1 < p < ∞` and
`t ∈ [0, 1]`, in a geodesic space a point is a `p`-Fréchet barycenter of `(1 - t) δ_x + t δ_y`
exactly when it is at distance `τ d(x, y)` from `x` and `(1 - τ) d(x, y)` from `y`, where
`τ = TauCeti.twoPointBarycenterTime p t`. -/
theorem isFrechetBarycenter_iff_dist_eq_twoPointBarycenterTime [IsGeodesicSpace X] :
    IsFrechetBarycenter p
        (ENNReal.ofReal (1 - t) • Measure.dirac x + ENNReal.ofReal t • Measure.dirac y) z ↔
      dist x z = twoPointBarycenterTime p.toReal t * dist x y ∧
        dist z y = (1 - twoPointBarycenterTime p.toReal t) * dist x y := by
  refine ⟨fun h ↦ h.dist_eq_twoPointBarycenterTime hp hp_top ht ?_, fun h ↦
    isFrechetBarycenter_of_dist_eq_twoPointBarycenterTime hp hp_top ht h.1 h.2⟩
  obtain ⟨γ, hγ⟩ := IsGeodesicSpace.exists_isGeodesicSegment x y
  exact ⟨_, hγ.dist_source_apply (twoPointBarycenterTime_mem_Icc _ ht),
    hγ.dist_apply_target (twoPointBarycenterTime_mem_Icc _ ht)⟩

omit hp hp_top

/-- **The quadratic barycenter of two weighted points on a geodesic segment.** For
`t ∈ [0, 1]`, the point at time `t` of a geodesic segment from `x` to `y` is a quadratic Fréchet
barycenter of `(1 - t) δ_x + t δ_y`. -/
theorem IsGeodesicSegment.isFrechetBarycenter_two {γ : ℝ → X} (hγ : IsGeodesicSegment γ x y) :
    IsFrechetBarycenter 2
      (ENNReal.ofReal (1 - t) • Measure.dirac x + ENNReal.ofReal t • Measure.dirac y) (γ t) := by
  simpa using hγ.isFrechetBarycenter_twoPointBarycenterTime (p := 2) ENNReal.one_lt_two
    ENNReal.ofNat_ne_top ht

/-- **Quadratic barycenters of two weighted points in a geodesic space.** For `t ∈ [0, 1]`, in a
geodesic space a point is a quadratic Fréchet barycenter of `(1 - t) δ_x + t δ_y` exactly when it
is at distance `t d(x, y)` from `x` and `(1 - t) d(x, y)` from `y`. -/
theorem isFrechetBarycenter_two_iff_dist_eq [IsGeodesicSpace X] :
    IsFrechetBarycenter 2
        (ENNReal.ofReal (1 - t) • Measure.dirac x + ENNReal.ofReal t • Measure.dirac y) z ↔
      dist x z = t * dist x y ∧ dist z y = (1 - t) * dist x y := by
  simpa using isFrechetBarycenter_iff_dist_eq_twoPointBarycenterTime (p := 2) (z := z)
    ENNReal.one_lt_two ENNReal.ofNat_ne_top ht

end TauCeti

end
