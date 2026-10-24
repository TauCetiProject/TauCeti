/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.BoundedVariation.MinkowskiContent
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The perimeter of a ball

Let `μ` be an additive Haar measure on a finite-dimensional real inner product space `E` of
dimension `n`, and write `ω = μ (ball 0 1)`. A ball of radius `r > 0` has perimeter

`P(ball c r) = n ω r^(n-1) = (n / r) μ (ball c r)`

in the whole space (`TauCeti.perimeter_ball`, `TauCeti.perimeter_ball_eq_ofReal_div_mul`). For
`μ` the volume of `EuclideanSpace ℝ (Fin n)` this is the classical surface area `n ω_n r^(n-1)`
of the sphere of radius `r`, where `ω_n` is the volume of the unit ball. The perimeter only sees a
set up to null sets, so the closed ball has the same perimeter (`TauCeti.perimeter_closedBall`).
In dimension `n ≥ 1` balls satisfy `P(ball c r)^n = n^n ω μ (ball c r)^(n-1)`
(`TauCeti.perimeter_ball_pow`): they attain equality in the isoperimetric inequality
`P(E)^n ≥ n^n ω μ E^(n-1)`, whose constant is fixed by this identity.

The perimeter is computed from its definition by duality. The test vector field
`x ↦ θ x • (x - c) / (r + δ)`, for a smooth bump `θ` equal to one on the ball and supported in
the ball of radius `r + δ`, has norm at most one and constant divergence `n / (r + δ)` on the
ball, which gives the lower bound as `δ → 0`. For the upper bound, the perimeter of the closed
ball is at most its lower outer Minkowski content
(`TauCeti.perimeter_closure_le_liminf_measure_thickening_sdiff_div`). The `ε`-neighbourhood of the
closed ball is the open ball of radius `r + ε`, so this content is the derivative `n r^(n-1) ω`
of `r ↦ r^n ω`.

## Main results

* `TauCeti.perimeter_ball`: `P(ball c r) = n r^(n-1) μ (ball 0 1)` for `r > 0`.
* `TauCeti.perimeter_ball_eq_ofReal_div_mul`: `P(ball c r) = (n / r) μ (ball c r)`.
* `TauCeti.perimeter_closedBall`: the same formula for closed balls.
* `TauCeti.perimeter_ball_pow`: `P(ball c r)^n = n^n μ (ball 0 1) μ (ball c r)^(n-1)`.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapter 12.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Module Set Filter TopologicalSpace TestFunction
open scoped ENNReal NNReal Distributions Topology

variable {E : Type*} [NormedAddCommGroup E] {c : E} {r : ℝ}
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E}

/-- **Lower bound for the perimeter of a ball.** For `r > 0` and `δ > 0`, in dimension `n` the
ball of radius `r` has perimeter at least `(n / (r + δ)) * μ.real (ball c r)`. -/
private theorem ofReal_le_perimeter_ball (hr : 0 < r) {δ : ℝ} (hδ : 0 < δ) :
    ENNReal.ofReal (finrank ℝ E / (r + δ) * μ.real (ball c r)) ≤ perimeter μ ⊤ (ball c r) := by
  -- The test field is `x ↦ θ x • (x - c) / (r + δ)`, where the bump `θ` is one on the ball of
  -- radius `r` and supported in the ball of radius `r + δ`; it is admissible and has divergence
  -- `n / (r + δ)` on the ball.
  let θ : ContDiffBump c := ⟨r, r + δ, hr, by linarith⟩
  have hrδ : 0 < r + δ := by linarith
  let φ : 𝓓(⊤, E) :=
    ⟨fun x => ((r + δ)⁻¹ * θ x) • (x - c),
      (contDiff_const.mul θ.contDiff).smul (contDiff_id.sub contDiff_const),
      θ.hasCompactSupport.mul_left.smul_right, by simp⟩
  have hφ (x : E) : ‖φ x‖ ≤ 1 := by
    simp only [φ, coe_mk]
    rw [norm_smul, Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 hrδ.le) θ.nonneg)]
    by_cases hx : θ x = 0
    · simp [hx]
    have hxc : ‖x - c‖ < r + δ := by
      rw [← dist_eq_norm, ← mem_ball]
      exact θ.support_eq ▸ hx
    calc (r + δ)⁻¹ * θ x * ‖x - c‖ ≤ (r + δ)⁻¹ * 1 * (r + δ) := by
          gcongr
          · exact θ.le_one
    _ = 1 := by field_simp
  -- On the ball the bump is locally one, so the field is locally `x ↦ (x - c) / (r + δ)`.
  have hdiv : ∀ x ∈ ball c r, divergenceCLM φ x = finrank ℝ E / (r + δ) := by
    intro x hx
    have hloc : (φ : E → E) =ᶠ[𝓝 x] fun y => (r + δ)⁻¹ • (y - c) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      simp only [φ, coe_mk]
      rw [θ.one_of_mem_closedBall (ball_subset_closedBall hy), mul_one]
    have hd : HasFDerivAt (fun y => (r + δ)⁻¹ • (y - c))
        ((r + δ)⁻¹ • ContinuousLinearMap.id ℝ E) x :=
      ((hasFDerivAt_id x).sub_const c).const_smul _
    rw [divergenceCLM_apply, hloc.fderiv_eq, hd.fderiv]
    simp [div_eq_inv_mul]
  calc ENNReal.ofReal (finrank ℝ E / (r + δ) * μ.real (ball c r))
      = ENNReal.ofReal (∫ x in ball c r, divergenceCLM φ x ∂μ) := by
        rw [setIntegral_congr_fun measurableSet_ball hdiv, setIntegral_const, smul_eq_mul,
          mul_comm]
    _ ≤ perimeter μ ⊤ (ball c r) := by
        rw [perimeter_eq_iSup measurableSet_ball.nullMeasurableSet]
        exact le_iSup₂_of_le (f := fun (φ : 𝓓(⊤, E)) (_ : ∀ x, ‖φ x‖ ≤ 1) =>
          ENNReal.ofReal (∫ x in ball c r, divergenceCLM φ x ∂μ)) φ hφ le_rfl

variable [μ.IsAddHaarMeasure]

/-- **Upper bound for the perimeter of a ball.** For `r > 0`, in dimension `n` the ball of
radius `r` has perimeter at most `n * r ^ (n - 1) * μ.real (ball 0 1)`. -/
private theorem perimeter_ball_le (hr : 0 < r) :
    perimeter μ ⊤ (ball c r) ≤ ENNReal.ofReal
      (finrank ℝ E * r ^ (finrank ℝ E - 1) * μ.real (ball 0 1)) := by
  -- The closed ball has the same perimeter, and its outer Minkowski content is the derivative
  -- `n r^(n-1) ω` of `r ↦ r^n ω`.
  set n := finrank ℝ E
  set ω := μ.real (ball (0 : E) 1)
  have hshell : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      μ ((thickening ε (closedBall c r) \ closure (closedBall c r)) ∩ (⊤ : Opens E)) /
        ENNReal.ofReal ε = ENNReal.ofReal (ε⁻¹ * (((r + ε) ^ n - r ^ n) * ω)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε : 0 < ε := hε
    rw [thickening_closedBall hε hr.le, closure_closedBall, Opens.coe_top, inter_univ,
      ← ofReal_measureReal (measure_ne_top_of_subset sdiff_subset measure_ball_lt_top.ne),
      measureReal_sdiff (closedBall_subset_ball (by linarith)) measurableSet_closedBall
        measure_ball_lt_top.ne, μ.addHaar_real_ball_of_pos c (by linarith),
      μ.addHaar_real_closedBall c hr.le, ← ENNReal.ofReal_div_of_pos hε, add_comm ε r,
      div_eq_inv_mul, sub_mul]
  have hslope : Tendsto (fun ε : ℝ => ENNReal.ofReal (ε⁻¹ * (((r + ε) ^ n - r ^ n) * ω)))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (n * r ^ (n - 1) * ω))) := by
    refine ENNReal.tendsto_ofReal ?_
    simp_rw [← mul_assoc]
    exact ((hasDerivAt_pow n r).tendsto_slope_zero_right.mul_const ω).congr fun ε => by
      rw [smul_eq_mul]
  calc perimeter μ ⊤ (ball c r)
      = perimeter μ ⊤ (closure (closedBall c r)) := by
        rw [closure_closedBall, perimeter_congr_ae (ae_restrict_of_ae
          (μ.addHaar_closedBall_ae_eq_ball_of_ne_zero c r hr.ne'))]
    _ ≤ liminf (fun ε => μ ((thickening ε (closedBall c r) \ closure (closedBall c r)) ∩
          (⊤ : Opens E)) / ENNReal.ofReal ε) (𝓝[>] 0) :=
        perimeter_closure_le_liminf_measure_thickening_sdiff_div ⊤ _
    _ = ENNReal.ofReal (n * r ^ (n - 1) * ω) := by
        rw [liminf_congr hshell, hslope.liminf_eq]

/-- For `r > 0`, in dimension `n` the ball of radius `r` has perimeter
`n * r ^ (n - 1) * μ.real (ball 0 1)`, as a real number cast to `ℝ≥0∞`. -/
private theorem perimeter_ball_eq_ofReal (hr : 0 < r) :
    perimeter μ ⊤ (ball c r) =
      ENNReal.ofReal (finrank ℝ E * r ^ (finrank ℝ E - 1) * μ.real (ball 0 1)) := by
  refine le_antisymm (perimeter_ball_le hr) (le_of_tendsto (x := 𝓝[>] (0 : ℝ))
    (f := fun δ => ENNReal.ofReal (finrank ℝ E / (r + δ) * μ.real (ball c r))) ?_ ?_)
  · rw [← μ.finrank_div_mul_addHaar_real_ball c hr]
    refine ENNReal.tendsto_ofReal (tendsto_nhdsWithin_of_tendsto_nhds ?_)
    have : ContinuousAt (fun δ : ℝ => (finrank ℝ E : ℝ) / (r + δ) * μ.real (ball c r)) 0 := by
      fun_prop (disch := simpa using hr.ne')
    simpa using this.tendsto
  · filter_upwards [self_mem_nhdsWithin] with δ hδ using ofReal_le_perimeter_ball hr hδ

/-- **The perimeter of a ball.** Against an additive Haar measure `μ` on a space of dimension `n`,
a ball of radius `r > 0` has perimeter `n r^(n-1) μ (ball 0 1)` in the whole space. For the volume
of `EuclideanSpace ℝ (Fin n)` this is the surface area `n ω_n r^(n-1)` of the sphere of
radius `r`. -/
theorem perimeter_ball (hr : 0 < r) :
    perimeter μ ⊤ (ball c r) =
      finrank ℝ E * ENNReal.ofReal (r ^ (finrank ℝ E - 1)) * μ (ball 0 1) := by
  rw [perimeter_ball_eq_ofReal hr, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
    ofReal_measureReal measure_ball_lt_top.ne]

/-- **The perimeter of a ball, normalized by its volume.** A ball of radius `r > 0` has perimeter
`(n / r) μ (ball c r)`, where `n` is the dimension. -/
theorem perimeter_ball_eq_ofReal_div_mul (hr : 0 < r) :
    perimeter μ ⊤ (ball c r) = ENNReal.ofReal (finrank ℝ E / r) * μ (ball c r) := by
  rw [perimeter_ball_eq_ofReal hr, ← μ.finrank_div_mul_addHaar_real_ball c hr,
    ENNReal.ofReal_mul (by positivity), ofReal_measureReal measure_ball_lt_top.ne]

/-- **The perimeter of a closed ball.** A closed ball of radius `r > 0` has the same perimeter
`n r^(n-1) μ (ball 0 1)` as the open ball, since they differ by a null set. -/
theorem perimeter_closedBall (hr : 0 < r) :
    perimeter μ ⊤ (closedBall c r) =
      finrank ℝ E * ENNReal.ofReal (r ^ (finrank ℝ E - 1)) * μ (ball 0 1) := by
  rw [perimeter_congr_ae (ae_restrict_of_ae (μ.addHaar_closedBall_ae_eq_ball_of_ne_zero c r
    hr.ne')), perimeter_ball hr]

/-- **Balls are isoperimetric equality cases.** In dimension `n ≥ 1`, a ball of radius `r > 0`
satisfies `P(ball c r)^n = n^n μ (ball 0 1) μ (ball c r)^(n-1)`, equality in the isoperimetric
inequality `P(E)^n ≥ n^n μ (ball 0 1) μ E^(n-1)`. -/
theorem perimeter_ball_pow (hn : finrank ℝ E ≠ 0) (hr : 0 < r) :
    perimeter μ ⊤ (ball c r) ^ finrank ℝ E =
      finrank ℝ E ^ finrank ℝ E * μ (ball 0 1) * μ (ball c r) ^ (finrank ℝ E - 1) := by
  rw [perimeter_ball hr, μ.addHaar_ball_of_pos c hr]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have h : ENNReal.ofReal (r ^ k) ^ (k + 1) = ENNReal.ofReal (r ^ (k + 1)) ^ k := by
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow (by positivity), ← pow_mul,
      ← pow_mul, mul_comm]
  rw [hk, Nat.succ_sub_one, Nat.succ_eq_add_one, mul_pow, mul_pow, h]
  ring

end TauCeti
