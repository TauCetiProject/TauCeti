/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.ArcLength
import TauCeti.Geometry.Manifold.Riemannian.MetricBridge
import TauCeti.Geometry.Manifold.Riemannian.Sphere.Geodesic
import TauCeti.Geometry.Manifold.Riemannian.Sphere.Gradient

/-!
# The Riemannian distance of the round sphere

For the round metric on the unit sphere `Sⁿ` of a real inner product space `E`, the Riemannian
distance between two points `x` and `y` is the angle `∠ x y = arccos ⟪x, y⟫` between them. In
dimension `n = 0` the sphere is two points at infinite distance, so the formula holds there only
for `y ≠ -x`.

* **The angle is a lower bound.** For `0 < c < 1` the function `z ↦ arccos (c ⟪x, z⟫)` is smooth
  on `Sⁿ`, and the length `√(1 - ⟪x, z⟫²)` of the round gradient of `z ↦ ⟪x, z⟫`
  (`TauCeti.norm_mgradient_inner_coe_sphere_sq`) makes its differential have norm at most `1`.
  So the difference of its values at `x` and `y`, which tends to `∠ x y` as `c → 1`, is at most
  the distance (`TauCeti.Manifold.edist_le_mul_riemannianEDist`). The function `arccos ⟪x, ·⟫`
  itself is not differentiable at `±x`, which is why the parameter `c` is needed.
* **The angle is attained.** Unless `y = -x`, the great circle from `x` towards the tangential
  part `y - ⟪x, y⟫ x` of `y` (`TauCeti.sphereGreatCircle`) has unit speed and reaches `y` at the
  time `∠ x y`. For `y = -x` any great circle through `x` reaches `-x` at the time `π`; one exists
  in positive dimension.

## Main results

* `TauCeti.ofReal_angle_le_riemannianEDist_sphere`: the angle is at most the round distance.
* `TauCeti.riemannianEDist_sphere_of_ne_neg`: the round distance between non-antipodal points is
  their angle.
* `TauCeti.riemannianEDist_sphere`: in positive dimension, the round distance is the angle.
* `TauCeti.riemannianEDist_neg_sphere`: in positive dimension, antipodal points are at distance
  `π`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 6
  (the distance of the round sphere).
-/

public section

open Bundle Filter InnerProductGeometry Metric Module Set Topology
open scoped ContDiff Manifold ENNReal

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- For `|c| < 1` and `|s| ≤ 1`, the function `r ↦ arccos (c r)` has derivative
`-c / √(1 - (c s)²)` at `s`. -/
private theorem hasDerivAt_arccos_const_mul {c s : ℝ} (hc : |c| < 1) (hs : |s| ≤ 1) :
    HasDerivAt (fun r ↦ Real.arccos (c * r)) (-(1 / √(1 - (c * s) ^ 2)) * c) s := by
  have hcs : |c * s| < 1 := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg c) hs).trans_lt hc
  rw [abs_lt] at hcs
  have h := (Real.hasDerivAt_arccos hcs.1.ne' hcs.2.ne).comp s ((hasDerivAt_id' s).const_mul c)
  rw [mul_one] at h
  exact h

/-- For `|c| < 1` the function `z ↦ arccos (c ⟪x, z⟫)` is `C¹` on the sphere: its argument stays in
`[-|c|, |c|]`, away from the singular points `±1` of `arccos`. -/
private theorem contMDiff_arccos_mul_inner_coe_sphere {c : ℝ} (hc : |c| < 1)
    (x : sphere (0 : E) 1) :
    ContMDiff (𝓡 n) 𝓘(ℝ) 1 ((fun r ↦ Real.arccos (c * r)) ∘
      fun z : sphere (0 : E) 1 ↦ inner ℝ (x : E) (z : E)) := by
  intro z
  have hcz : |c * inner ℝ (x : E) (z : E)| < 1 := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg c) (abs_le.2 (real_inner_mem_Icc_of_norm_eq_one
      (norm_eq_of_mem_sphere x) (norm_eq_of_mem_sphere z)))).trans_lt hc
  rw [abs_lt] at hcz
  have hφ : ContDiffAt ℝ 1 (fun r ↦ Real.arccos (c * r)) (inner ℝ (x : E) (z : E)) :=
    (Real.contDiffAt_arccos hcz.1.ne' hcz.2.ne).comp _ (contDiffAt_id.const_smul c)
  have hg : ContMDiff (𝓡 n) 𝓘(ℝ) 1 fun z : sphere (0 : E) 1 ↦ inner ℝ (x : E) (z : E) := by
    simpa [Function.comp_def] using
      (innerSL ℝ (x : E)).contMDiff.comp (contMDiff_coe_sphere (n := n))
  exact hφ.contMDiffAt.comp z (hg z)

/-- For `0 < c < 1` the differential of `z ↦ arccos (c ⟪x, z⟫)` on the sphere has norm at most `1`
for the round metric: it is `-c / √(1 - (c s)²)` times the differential of `z ↦ ⟪x, z⟫`, whose
round gradient has length `√(1 - s²)`, where `s = ⟪x, z⟫`. -/
private theorem norm_mvfderiv_arccos_mul_inner_coe_sphere_le {c : ℝ} (hc₀ : 0 < c) (hc₁ : c < 1)
    (x z : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) z) :
    ‖mvfderiv (𝓡 n) ((fun r ↦ Real.arccos (c * r)) ∘
      fun z : sphere (0 : E) 1 ↦ inner ℝ (x : E) (z : E)) z v‖ ≤ ‖v‖ := by
  set g : sphere (0 : E) 1 → ℝ := fun z ↦ inner ℝ (x : E) (z : E)
  have hgz : MDiffAt g z := by
    refine ((innerSL ℝ (x : E)).contMDiff.comp (contMDiff_coe_sphere (n := n) (m := 1)) z)
      |>.mdifferentiableAt one_ne_zero
  have hφ := hasDerivAt_arccos_const_mul (by rwa [abs_of_pos hc₀])
    (abs_le.2 (real_inner_mem_Icc_of_norm_eq_one (norm_eq_of_mem_sphere x)
      (norm_eq_of_mem_sphere z)))
  rw [mvfderiv_scalar_comp hgz hφ.differentiableAt, hφ.deriv, smul_apply,
    ← Manifold.inner_mgradient, norm_smul]
  set s := g z
  set w := Manifold.mgradient (𝓡 n) g z
  have hw : ‖w‖ ^ 2 = 1 - s ^ 2 := by
    simpa [norm_eq_of_mem_sphere] using norm_mgradient_inner_coe_sphere_sq (n := n) (x : E) z
  have hc2 : c ^ 2 < 1 := by nlinarith
  have hcw : c * ‖w‖ ≤ √(1 - (c * s) ^ 2) := by
    rw [← Real.sqrt_sq (mul_nonneg hc₀.le (norm_nonneg w))]
    refine Real.sqrt_le_sqrt ?_
    rw [mul_pow, hw, mul_pow]
    nlinarith
  have hfac : ‖-(1 / √(1 - (c * s) ^ 2)) * c‖ * ‖w‖ ≤ 1 := by
    calc ‖-(1 / √(1 - (c * s) ^ 2)) * c‖ * ‖w‖ = c * ‖w‖ / √(1 - (c * s) ^ 2) := by
          rw [norm_mul, norm_neg, norm_div, norm_one, Real.norm_of_nonneg (Real.sqrt_nonneg _),
            Real.norm_of_nonneg hc₀.le]
          ring
      _ ≤ 1 := div_le_one_of_le₀ hcw (Real.sqrt_nonneg _)
  calc ‖-(1 / √(1 - (c * s) ^ 2)) * c‖ * ‖inner ℝ w v‖
      ≤ ‖-(1 / √(1 - (c * s) ^ 2)) * c‖ * (‖w‖ * ‖v‖) := by
        gcongr
        exact norm_inner_le_norm w v
    _ ≤ ‖v‖ := by
        rw [← mul_assoc]
        exact mul_le_of_le_one_left (norm_nonneg v) hfac

/-- For `0 < c < 1` and points `x, y` of the sphere, `arccos (c ⟪x, y⟫) - arccos c` is at most the
round distance from `x` to `y`: the function `z ↦ arccos (c ⟪x, z⟫)` takes the value `arccos c` at
`x`, and its differential has norm at most `1`. -/
private theorem ofReal_arccos_mul_sub_arccos_le_riemannianEDist_sphere {c : ℝ} (hc₀ : 0 < c)
    (hc₁ : c < 1) (x y : sphere (0 : E) 1) :
    ENNReal.ofReal (Real.arccos (c * inner ℝ (x : E) (y : E)) - Real.arccos c) ≤
      Manifold.riemannianEDist (𝓡 n) x y := by
  have h := Manifold.edist_le_mul_riemannianEDist (I := 𝓡 n) (C := 1)
    (contMDiff_arccos_mul_inner_coe_sphere (by rwa [abs_of_pos hc₀]) x) one_ne_zero
    (fun z v ↦ by
      rw [ENNReal.coe_one, one_mul, ← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (norm_mvfderiv_arccos_mul_inner_coe_sphere_le hc₀ hc₁ x z v))
    x y
  have hx : inner ℝ (x : E) (x : E) = 1 :=
    inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere x)
  rw [ENNReal.coe_one, one_mul, edist_dist, Real.dist_eq, Function.comp_apply,
    Function.comp_apply, hx, mul_one, abs_sub_comm] at h
  exact (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans h

/-- **The angle is at most the round distance.** For any two points `x, y` of the unit sphere, the
angle `∠ x y = arccos ⟪x, y⟫` is at most their Riemannian distance for the round metric. -/
theorem ofReal_angle_le_riemannianEDist_sphere (x y : sphere (0 : E) 1) :
    ENNReal.ofReal (angle (x : E) (y : E)) ≤ Manifold.riemannianEDist (𝓡 n) x y := by
  set s := inner ℝ (x : E) (y : E)
  have hangle : angle (x : E) (y : E) = Real.arccos s := by
    simp [angle, s, norm_eq_of_mem_sphere]
  -- Let `c → 1` from below in `arccos (c s) - arccos c ≤ d(x, y)`.
  have hlim : Tendsto (fun c ↦ ENNReal.ofReal (Real.arccos (c * s) - Real.arccos c))
      (𝓝[<] 1) (𝓝 (ENNReal.ofReal (angle (x : E) (y : E)))) := by
    have hcont : Continuous fun c ↦ ENNReal.ofReal (Real.arccos (c * s) - Real.arccos c) :=
      ENNReal.continuous_ofReal.comp
        ((Real.continuous_arccos.comp (continuous_id.mul continuous_const)).sub
          Real.continuous_arccos)
    have h1 := hcont.tendsto 1
    simp only [one_mul, Real.arccos_one, sub_zero] at h1
    rw [hangle]
    exact h1.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT one_pos] with c hc
  exact ofReal_arccos_mul_sub_arccos_le_riemannianEDist_sphere hc.1 hc.2 x y

/-- If the great circle from `x` in the direction `q` reaches `y` at the time `θ ≥ 0`, the round
distance from `x` to `y` is at most `θ`: great circles have unit speed. -/
private theorem riemannianEDist_sphere_le_of_sphereGreatCircle_eq {x y q : sphere (0 : E) 1}
    (hq : inner ℝ (x : E) (q : E) = 0) {θ : ℝ} (hθ : 0 ≤ θ)
    (hy : sphereGreatCircle x q hq θ = y) :
    Manifold.riemannianEDist (𝓡 n) x y ≤ ENNReal.ofReal θ := by
  calc Manifold.riemannianEDist (𝓡 n) x y
      ≤ Manifold.pathELength (𝓡 n) (sphereGreatCircle x q hq) 0 θ :=
        Manifold.riemannianEDist_le_pathELength
          ((contMDiff_sphereGreatCircle (n := n) x q hq).of_le (by simp)).contMDiffOn
          (sphereGreatCircle_zero x q hq) hy hθ
    _ = ENNReal.ofReal θ := by
        rw [Manifold.pathELength_eq_of_norm_curveVelocity_eq_one fun t _ ↦
          norm_curveVelocity_sphereGreatCircle x q hq t, sub_zero]

/-- **The round distance between non-antipodal points.** If `y ≠ -x`, the Riemannian distance
between the points `x` and `y` of the unit sphere for the round metric is the angle
`∠ x y = arccos ⟪x, y⟫`. This holds in every dimension; in dimension `0` the sphere has the two
points `±x`, and `x` is at distance `0` from itself. -/
theorem riemannianEDist_sphere_of_ne_neg {x y : sphere (0 : E) 1} (h : y ≠ -x) :
    Manifold.riemannianEDist (𝓡 n) x y = ENNReal.ofReal (angle (x : E) (y : E)) := by
  refine le_antisymm ?_ (ofReal_angle_le_riemannianEDist_sphere x y)
  rcases eq_or_ne y x with rfl | hxy
  · rw [Manifold.riemannianEDist_self]
    exact bot_le
  -- The tangential part `w = y - ⟪x, y⟫ x` of `y` at `x` is nonzero, and the great circle from
  -- `x` towards it reaches `y` at the time `∠ x y`.
  set s := inner ℝ (x : E) (y : E)
  set w : E := (y : E) - s • (x : E)
  have hxx : inner ℝ (x : E) (x : E) = 1 :=
    inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere x)
  have hyy : inner ℝ (y : E) (y : E) = 1 :=
    inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere y)
  have hxw : inner ℝ (x : E) w = 0 := by
    simp only [w, inner_sub_right, real_inner_smul_right, hxx, s]
    ring
  have hw2 : ‖w‖ ^ 2 = 1 - s ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [w, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hxx, hyy, real_inner_comm (x : E) (y : E), s]
    ring
  have hw0 : w ≠ 0 := by
    intro hw
    have hs : s ^ 2 = 1 := by nlinarith [hw2, norm_zero (E := E), hw ▸ hw2]
    have hy : (y : E) = s • (x : E) := sub_eq_zero.1 hw
    rcases sq_eq_one_iff.1 hs with h1 | h1
    · exact hxy (Subtype.ext (by rw [hy, h1, one_smul]))
    · exact h (Subtype.ext (by rw [hy, h1, neg_one_smul, coe_neg_sphere]))
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  let q : sphere (0 : E) 1 := ⟨‖w‖⁻¹ • w, by simp [norm_smul, hwpos.ne']⟩
  have hq : inner ℝ (x : E) (q : E) = 0 := by
    simp [q, real_inner_smul_right, hxw]
  refine riemannianEDist_sphere_le_of_sphereGreatCircle_eq hq (angle_nonneg _ _) ?_
  have hangle : angle (x : E) (y : E) = Real.arccos s := by
    simp [angle, s, norm_eq_of_mem_sphere]
  have hs1 : s ∈ Icc (-1) 1 :=
    real_inner_mem_Icc_of_norm_eq_one (norm_eq_of_mem_sphere x) (norm_eq_of_mem_sphere y)
  have hsin : Real.sin (Real.arccos s) = ‖w‖ := by
    rw [Real.sin_arccos, ← hw2, Real.sqrt_sq (norm_nonneg w)]
  ext
  rw [coe_sphereGreatCircle, hangle, Real.cos_arccos hs1.1 hs1.2, hsin]
  simp [q, smul_smul, hwpos.ne', w]

/-- **The round distance is the angle.** In positive dimension, the Riemannian distance between
any two points `x` and `y` of the unit sphere for the round metric is the angle
`∠ x y = arccos ⟪x, y⟫`. In dimension `0` the two points of the sphere are at infinite distance,
while their angle is `π`. -/
theorem riemannianEDist_sphere (hn : n ≠ 0) (x y : sphere (0 : E) 1) :
    Manifold.riemannianEDist (𝓡 n) x y = ENNReal.ofReal (angle (x : E) (y : E)) := by
  rcases ne_or_eq y (-x) with h | rfl
  · exact riemannianEDist_sphere_of_ne_neg h
  refine le_antisymm ?_ (ofReal_angle_le_riemannianEDist_sphere x (-x))
  -- Any great circle through `x` reaches `-x` at the time `π`.
  obtain ⟨q, hq1⟩ := exists_norm_eq_one_mem_orthogonal_singleton (𝕜 := ℝ) (x : E)
    (by rw [(Fact.out : finrank ℝ E = n + 1)]; omega)
  have hq : inner ℝ (x : E) ((⟨q, by simpa using hq1⟩ : sphere (0 : E) 1) : E) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.1 q.property
  rw [coe_neg_sphere, angle_self_neg_of_ne_zero (ne_zero_of_mem_unit_sphere x)]
  refine riemannianEDist_sphere_le_of_sphereGreatCircle_eq hq Real.pi_pos.le ?_
  ext
  simp

/-- **Antipodal points are at distance `π`.** In positive dimension, the round distance from a
point of the unit sphere to its antipode is `π`. -/
theorem riemannianEDist_neg_sphere (hn : n ≠ 0) (x : sphere (0 : E) 1) :
    Manifold.riemannianEDist (𝓡 n) x (-x) = ENNReal.ofReal Real.pi := by
  rw [riemannianEDist_sphere hn, coe_neg_sphere,
    angle_self_neg_of_ne_zero (ne_zero_of_mem_unit_sphere x)]

end TauCeti
