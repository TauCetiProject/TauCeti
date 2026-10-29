/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import TauCeti.Analysis.SpecialFunctions.Beta
public import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.MeasureTheory.Group.Integral

/-!
# The integral and the moments of the Japanese bracket

Mathlib proves that `x ↦ (1 + ‖x‖ ^ 2) ^ (-r / 2)` is integrable on a finite-dimensional real
normed space `V` of dimension `d` as soon as `d < r`
(`integrable_rpow_neg_one_add_norm_sq`). When `V` is moreover a real inner product space, this
file computes the integral against its canonical Lebesgue measure `volume`:

`∫ x : V, (1 + ‖x‖ ^ 2) ^ (-r / 2) = π ^ (d / 2) Γ((r - d) / 2) / Γ(r / 2)`.

Integrating in polar coordinates and substituting `u = ‖x‖ ^ 2` turns the integral into Euler's
second beta integral `∫₀^∞ u ^ (a - 1) (1 + u) ^ (-(a + b)) du = Β(a, b)` with `a = d / 2` and
`b = (r - d) / 2` (`TauCeti.integral_rpow_mul_one_add_rpow`, in the radial form
`TauCeti.integral_rpow_mul_one_add_sq_rpow`). For `r = d + 1` this is the
normalization of the multivariate Cauchy distribution and of the Poisson kernel of a half-space.

More generally, for every additive Haar measure `μ` and every real `p ≥ 0` with `d + p < r`, the
radial moment `∫ x, ‖x‖ ^ p (1 + ‖x‖ ^ 2) ^ (-r / 2) ∂μ` is the beta integral
`d μ(B(0, 1)) Β((d + p) / 2, (r - d - p) / 2) / 2`. The condition `d + p < r` records the decay
needed at infinity, and `p ≥ 0` excludes a singularity at the origin. The value of the integral
above is the case `p = 0`. These formulas are useful for rescaled Euclidean profiles, including
the moments of the Yamabe bubbles.

At the endpoint `p + d = r` the radial moment diverges logarithmically when `d > 0`. For the
rescaled profile `y ↦ 2 t / (t² + ‖y - b‖²)` raised to a natural power `m` with `p + d = 2 m`, the
file computes the moment truncated to a ball `B(b, R)` exactly, as an explicit logarithm minus a
partial logarithmic series, and bounds its distance to the logarithm by a harmonic number.

## Main declarations

* `TauCeti.integrable_rpow_neg_sq_add_norm_sq`: the rescaled bracket
  `x ↦ (c ^ 2 + ‖x‖ ^ 2) ^ (-r / 2)`, `c ≠ 0`, is integrable for every additive Haar measure.
* `TauCeti.integrable_norm_rpow_mul_rpow_neg_one_add_norm_sq`,
  `TauCeti.integral_norm_rpow_mul_rpow_neg_one_add_norm_sq`: integrability and value of the
  radial moments of the Japanese bracket, for every additive Haar measure.
* `TauCeti.sub_two_mul_integral_radial`: an identity between two radial moments of the rescaled
  bracket.
* `TauCeti.integral_pow_mul_div_add_sq_pow`: the radial integral of the truncated logarithmic
  moments.
* `TauCeti.setIntegral_ball_norm_sub_rpow_mul_div_add_norm_sub_sq_pow`,
  `TauCeti.abs_setIntegral_ball_norm_sub_rpow_mul_div_add_norm_sub_sq_pow_sub_mul_log_le`: the
  truncated logarithmic moments of the powers of the rescaled profile, exactly and up to a
  bounded error.
* `TauCeti.integral_rpow_neg_one_add_norm_sq`: the value of the integral on a real inner
  product space, for its canonical Lebesgue measure.
-/

public section

namespace TauCeti

open Filter MeasureTheory Metric Module ProbabilityTheory Real Set Topology

variable {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]

section Integrability

variable [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The rescaled Japanese bracket `x ↦ (c ^ 2 + ‖x‖ ^ 2) ^ (-r / 2)` with `c ≠ 0` is integrable on
a finite-dimensional real normed space of dimension `d < r`, for every additive Haar measure. For
`c = 1` this is Mathlib's `integrable_rpow_neg_one_add_norm_sq`. -/
theorem integrable_rpow_neg_sq_add_norm_sq (μ : Measure V) [μ.IsAddHaarMeasure] {c r : ℝ}
    (hc : c ≠ 0) (hr : (finrank ℝ V : ℝ) < r) :
    Integrable (fun x : V ↦ (c ^ 2 + ‖x‖ ^ 2) ^ (-r / 2)) μ := by
  refine (((integrable_rpow_neg_one_add_norm_sq (μ := μ) hr).comp_smul (inv_ne_zero hc)).const_mul
    ((c ^ 2) ^ (-r / 2))).congr (.of_forall fun x ↦ ?_)
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  beta_reduce
  rw [← Real.mul_rpow (by positivity) (by positivity), norm_smul, mul_pow, norm_inv,
    Real.norm_eq_abs, inv_pow, sq_abs, mul_add, mul_one, mul_inv_cancel_left₀ hc2]

/-- The radial moment `x ↦ ‖x‖ ^ p (1 + ‖x‖ ^ 2) ^ (-r / 2)` of order `p ≥ 0` of the Japanese
bracket is integrable for every additive Haar measure when its decay exponent exceeds
`dim V + p`. -/
theorem integrable_norm_rpow_mul_rpow_neg_one_add_norm_sq (μ : Measure V) [μ.IsAddHaarMeasure]
    {p r : ℝ} (hp : 0 ≤ p) (hr : (finrank ℝ V : ℝ) + p < r) :
    Integrable (fun x : V ↦ ‖x‖ ^ p * (1 + ‖x‖ ^ 2) ^ (-r / 2)) μ := by
  have hmajorant := integrable_rpow_neg_one_add_norm_sq (E := V) (μ := μ)
    (show (finrank ℝ V : ℝ) < r - p by linarith)
  refine hmajorant.mono' (by fun_prop) (.of_forall fun x ↦ ?_)
  have hA : 0 < 1 + ‖x‖ ^ 2 := by positivity
  -- Bound `‖x‖ ^ p = (‖x‖ ^ 2) ^ (p / 2)` by `(1 + ‖x‖ ^ 2) ^ (p / 2)`.
  have hpow : ‖x‖ ^ p ≤ (1 + ‖x‖ ^ 2) ^ (p / 2) := by
    have hsq : ‖x‖ ^ p = (‖x‖ ^ 2) ^ (p / 2) := by
      rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg x), mul_div_cancel₀ p two_ne_zero]
    rw [hsq]
    gcongr
    linarith
  have hexp : p / 2 + -r / 2 = -(r - p) / 2 := by ring
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    ‖x‖ ^ p * (1 + ‖x‖ ^ 2) ^ (-r / 2)
        ≤ (1 + ‖x‖ ^ 2) ^ (p / 2) * (1 + ‖x‖ ^ 2) ^ (-r / 2) := by gcongr
    _ = (1 + ‖x‖ ^ 2) ^ (-(r - p) / 2) := by rw [← Real.rpow_add hA, hexp]

end Integrability

section Moment

variable [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Nontrivial V]

/-- **The radial moments of the Japanese bracket.** On a nontrivial finite-dimensional real normed
space `V` of dimension `d`, for an additive Haar measure `μ` and `0 ≤ p` with `d + p < r`,
`∫ ‖x‖ ^ p (1 + ‖x‖ ^ 2) ^ (-r / 2) ∂μ = d μ(B(0, 1)) Β((d + p) / 2, (r - d - p) / 2) / 2`.
For Lebesgue measure on an inner product space the factor `d μ(B(0, 1))` is the area of the unit
sphere of `V`. -/
theorem integral_norm_rpow_mul_rpow_neg_one_add_norm_sq (μ : Measure V) [μ.IsAddHaarMeasure]
    {p r : ℝ} (hp : 0 ≤ p) (hr : (finrank ℝ V : ℝ) + p < r) :
    ∫ x : V, ‖x‖ ^ p * (1 + ‖x‖ ^ 2) ^ (-r / 2) ∂μ =
      (finrank ℝ V : ℝ) * μ.real (ball (0 : V) 1) *
        (beta (((finrank ℝ V : ℝ) + p) / 2) ((r - finrank ℝ V - p) / 2) / 2) := by
  set d := finrank ℝ V with hd
  have hd0 : 0 < d := finrank_pos
  -- In polar coordinates the moment is the radial beta integral with `s = d + p`.
  have hrad :
      ∫ y in Ioi (0 : ℝ), y ^ (d - 1) • (y ^ p * (1 + y ^ 2) ^ (-r / 2)) =
        beta (((d : ℝ) + p) / 2) ((r - d - p) / 2) / 2 := by
    rw [sub_sub, ← integral_rpow_mul_one_add_sq_rpow (by positivity) hr]
    refine setIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) ↦ ?_
    have hexp : ((d - 1 : ℕ) : ℝ) + p = d + p - 1 := by
      rw [Nat.cast_sub hd0, Nat.cast_one]
      ring
    rw [smul_eq_mul, ← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hy, hexp]
  rw [integral_fun_norm_addHaar μ (fun y : ℝ ↦ y ^ p * (1 + y ^ 2) ^ (-r / 2)), hrad,
    nsmul_eq_mul, smul_eq_mul, mul_assoc]

end Moment

/-- For `n > 2`, the two radial moments of the rescaled Japanese bracket satisfy
`(n - 2) ∫₀^∞ r ^ (n - 1) r² ψ(r) = n t² ∫₀^∞ r ^ (n - 1) ψ(r)`, where
`ψ(r) = (2 t / (t² + r²)) ^ n`. This follows by integrating the derivative of
`r ↦ r ^ n (t² + r²) ψ(r)`, which vanishes at `0` and at infinity. -/
theorem sub_two_mul_integral_radial {n : ℕ} (hn : 2 < n) {t : ℝ} (ht : 0 < t)
    (h₁ : IntegrableOn (fun r : ℝ ↦ r ^ (n - 1) * (2 * t / (t ^ 2 + r ^ 2)) ^ n) (Ioi 0))
    (h₂ : IntegrableOn (fun r : ℝ ↦ r ^ (n - 1) * (r ^ 2 * (2 * t / (t ^ 2 + r ^ 2)) ^ n))
      (Ioi 0)) :
    ((n : ℝ) - 2) * ∫ r in Ioi 0, r ^ (n - 1) * (r ^ 2 * (2 * t / (t ^ 2 + r ^ 2)) ^ n) =
      n * t ^ 2 * ∫ r in Ioi 0, r ^ (n - 1) * (2 * t / (t ^ 2 + r ^ 2)) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [show m + 3 - 1 = m + 2 by omega] at h₁ h₂ ⊢
  have hQ : ∀ r : ℝ, 0 < t ^ 2 + r ^ 2 := fun r ↦ by positivity
  set F : ℝ → ℝ := fun r ↦ r ^ (m + 3) * (t ^ 2 + r ^ 2) * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 3)
  have hderiv : ∀ r ∈ Ici (0 : ℝ), HasDerivAt F
      (((m + 3 : ℕ) : ℝ) * t ^ 2 * (r ^ (m + 2) * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 3)) -
        (((m + 3 : ℕ) : ℝ) - 2) *
          (r ^ (m + 2) * (r ^ 2 * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 3)))) r := by
    intro r _
    have hQr : t ^ 2 + r ^ 2 ≠ 0 := (hQ r).ne'
    have hq : HasDerivAt (fun r : ℝ ↦ t ^ 2 + r ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r).const_add (t ^ 2)
    have hψ : HasDerivAt (fun r : ℝ ↦ (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 3))
        (-(2 * ((m + 3 : ℕ) : ℝ) * r / (t ^ 2 + r ^ 2)) * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 3))
        r := by
      convert ((hasDerivAt_const r (2 * t)).div hq hQr).pow (m + 3) using 1
      simp only [Pi.div_apply, show m + 3 - 1 = m + 2 by omega]
      rw [pow_succ _ (m + 2)]
      generalize (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 2) = X
      field_simp
      ring
    convert ((hasDerivAt_pow (m + 3) r).mul hq).mul hψ using 1
    simp only [Pi.mul_apply, show m + 3 - 1 = m + 2 by omega]
    rw [pow_succ r (m + 2)]
    generalize (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 3) = P
    generalize r ^ (m + 2) = R
    push_cast
    field_simp
    ring
  -- For `r > 0`, `F r = (2 t) ^ (m + 3) (r / (t² + r²)) ^ (m + 1) (r² / (t² + r²))`, which is at
  -- most `(2 t) ^ (m + 3) r⁻¹ ^ (m + 1)`.
  have htend : Tendsto F atTop (𝓝 0) := by
    have hlim : Tendsto (fun r : ℝ ↦ (2 * t) ^ (m + 3) * r⁻¹ ^ (m + 1)) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.pow (m + 1)).const_mul ((2 * t) ^ (m + 3))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      ((eventually_gt_atTop 0).mono fun r hr ↦ by positivity)
      ((eventually_gt_atTop 0).mono fun r hr ↦ ?_)
    · have hF : F r = (2 * t) ^ (m + 3) * (r / (t ^ 2 + r ^ 2)) ^ (m + 1) *
          (r ^ 2 / (t ^ 2 + r ^ 2)) := by
        have := (hQ r).ne'
        simp only [F]
        rw [div_pow, div_pow]
        field_simp
        ring
      have h₁ : r / (t ^ 2 + r ^ 2) ≤ r⁻¹ := by
        rw [div_le_iff₀ (hQ r), inv_mul_eq_div, le_div_iff₀ hr]
        nlinarith [sq_nonneg t]
      have h₂ : r ^ 2 / (t ^ 2 + r ^ 2) ≤ 1 := by
        rw [div_le_one (hQ r)]
        nlinarith [sq_nonneg t]
      rw [hF]
      calc (2 * t) ^ (m + 3) * (r / (t ^ 2 + r ^ 2)) ^ (m + 1) * (r ^ 2 / (t ^ 2 + r ^ 2))
          ≤ (2 * t) ^ (m + 3) * r⁻¹ ^ (m + 1) * 1 := by gcongr
        _ = (2 * t) ^ (m + 3) * r⁻¹ ^ (m + 1) := mul_one _
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    ((h₁.const_mul _).sub (h₂.const_mul _)) htend
  rw [integral_sub (h₁.const_mul _) (h₂.const_mul _), integral_const_mul, integral_const_mul,
    show F 0 = 0 by simp [F], sub_zero] at h
  push_cast at h ⊢
  linarith

section TruncatedMoment

variable [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### Truncated moments at the logarithmic endpoint

For `p + d = 2 m`, the moment `∫ ‖x‖ ^ p (2 t / (t² + ‖x‖²)) ^ m` of the `m`-th power of the
rescaled bracket profile diverges logarithmically when `d > 0`, and the moments truncated to a ball
are computed instead. In polar coordinates about the centre, the integrand is
`r ^ (2 m - 1) (2 t / (t² + r²)) ^ m`. With `w = r² / (t² + r²)`, its antiderivative is
`(2 t) ^ m / 2 (log (t² + r²) - ∑_{k < m - 1} w ^ (k + 1) / (k + 1))`: the derivative of the
partial logarithmic series is a geometric sum in `w`. -/

/-- The radial integral of the truncated profile moments:
`∫_0^R r ^ (2 m + 1) (2 t / (t² + r²)) ^ (m + 1) dr =
2 ^ m t ^ (m + 1) (log (1 + (R / t)²) - ∑_{k < m} w ^ (k + 1) / (k + 1))`, with
`w = R² / (t² + R²)`. -/
theorem integral_pow_mul_div_add_sq_pow {t : ℝ} (ht : t ≠ 0) (m : ℕ) (R : ℝ) :
    ∫ r in (0)..R, r ^ (2 * m + 1) * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 1) =
      2 ^ m * t ^ (m + 1) * (log (1 + (R / t) ^ 2) -
        ∑ k ∈ Finset.range m, (R ^ 2 / (t ^ 2 + R ^ 2)) ^ (k + 1) / (k + 1)) := by
  set G : ℝ → ℝ := fun r ↦ r ^ (2 * m + 1) * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 1) with hG
  set Φ : ℝ → ℝ := fun r ↦ (2 * t) ^ (m + 1) / 2 * (log (t ^ 2 + r ^ 2) -
      ∑ k ∈ Finset.range m, (r ^ 2 / (t ^ 2 + r ^ 2)) ^ (k + 1) / (k + 1)) with hΦ
  have hderiv (r : ℝ) : HasDerivAt Φ (G r) r := by
    have hpos : 0 < t ^ 2 + r ^ 2 := by positivity
    have hq : HasDerivAt (fun r : ℝ ↦ t ^ 2 + r ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r).const_add (t ^ 2)
    have hw : HasDerivAt (fun r : ℝ ↦ r ^ 2 / (t ^ 2 + r ^ 2))
        (2 * r / (t ^ 2 + r ^ 2) * (1 - r ^ 2 / (t ^ 2 + r ^ 2))) r := by
      convert (hasDerivAt_pow 2 r).div hq hpos.ne' using 1
      field_simp
      ring
    have hsum := HasDerivAt.fun_sum (u := Finset.range m) (fun k _ ↦ (hw.pow (k + 1)).div_const
      ((k : ℝ) + 1))
    convert ((hq.log hpos.ne').sub hsum).const_mul ((2 * t) ^ (m + 1) / 2) using 1
    set w := r ^ 2 / (t ^ 2 + r ^ 2) with hw_def
    -- The derivative of the partial logarithmic series telescopes to a geometric sum.
    have hgeom : ∑ k ∈ Finset.range m, (↑(k + 1) : ℝ) * w ^ (k + 1 - 1) *
        (2 * r / (t ^ 2 + r ^ 2) * (1 - w)) / ((k : ℝ) + 1) =
        2 * r / (t ^ 2 + r ^ 2) * (1 - w ^ m) := by
      rw [← geom_sum_mul_neg, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      push_cast
      field_simp
    rw [hgeom, hw_def]
    simp only [hG, div_pow, ← pow_mul]
    field_simp
    ring
  have hcont : Continuous G := by
    rw [hG]
    exact (continuous_pow _).mul ((continuous_const.div (continuous_const.add (continuous_pow 2))
      fun r ↦ (by positivity : (0 : ℝ) < t ^ 2 + r ^ 2).ne').pow _)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ ↦ hderiv r)
    (hcont.intervalIntegrable _ _)]
  have hlog : log (t ^ 2 + R ^ 2) - log (t ^ 2 + 0 ^ 2) = log (1 + (R / t) ^ 2) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  have h0 : ∑ k ∈ Finset.range m, ((0 : ℝ) ^ 2 / (t ^ 2 + 0 ^ 2)) ^ (k + 1) / (k + 1) = 0 :=
    Finset.sum_eq_zero fun k _ ↦ by simp
  simp only [hΦ, h0]
  rw [← hlog]
  ring

/-- **Truncated moments at the logarithmic endpoint.** For an additive Haar measure on a space of
dimension `n`, a natural number `m ≠ 0` and an order `p` with `p + n = 2 m`, the moment of order `p`
of the `m`-th power of the bubble profile `y ↦ 2 t / (t² + ‖y - b‖²)` over the ball `B(b, R)` is
`n |B(0, 1)| 2 ^ (m - 1) t ^ m (log (1 + (R / t)²) - ∑_{k < m - 1} w ^ (k + 1) / (k + 1))`,
with `w = R² / (t² + R²)`. When `V` is nontrivial, the integral over the whole space diverges
logarithmically. -/
theorem setIntegral_ball_norm_sub_rpow_mul_div_add_norm_sub_sq_pow
    (μ : Measure V) [μ.IsAddHaarMeasure] {m : ℕ} (hm : m ≠ 0) {p : ℝ}
    (hp : p + finrank ℝ V = 2 * m) {t : ℝ} (ht : t ≠ 0) {R : ℝ} (hR : 0 ≤ R) (b : V) :
    ∫ x in ball b R, ‖x - b‖ ^ p * (2 * t / (t ^ 2 + ‖x - b‖ ^ 2)) ^ m ∂μ =
      (finrank ℝ V : ℝ) * μ.real (ball (0 : V) 1) * (2 ^ (m - 1) * t ^ m *
        (log (1 + (R / t) ^ 2) -
          ∑ k ∈ Finset.range (m - 1), (R ^ 2 / (t ^ 2 + R ^ 2)) ^ (k + 1) / (k + 1))) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hm
  simp only [Nat.add_sub_cancel]
  set F : ℝ → ℝ := fun r ↦ r ^ p * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 1) with hF
  -- Translate the centre to the origin and pass to polar coordinates.
  have hind : (ball (0 : V) R).indicator (fun y ↦ F ‖y‖) = fun y ↦ (Iio R).indicator F ‖y‖ := by
    ext y
    by_cases hy : ‖y‖ < R
    · rw [indicator_of_mem (mem_ball_zero_iff.2 hy), indicator_of_mem (mem_Iio.2 hy)]
    · rw [indicator_of_notMem (mt mem_ball_zero_iff.1 hy), indicator_of_notMem (mt mem_Iio.1 hy)]
  rcases Nat.eq_zero_or_pos (finrank ℝ V) with hn | hn
  · -- On the zero space the weight `‖x - b‖ ^ p` vanishes identically.
    have : Subsingleton V := finrank_zero_iff.1 hn
    have hp0 : p ≠ 0 := by rw [hn] at hp; push_cast at hp; linarith
    simp [Subsingleton.elim _ (0 : V), Real.zero_rpow hp0, hn]
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) hn
  rw [setIntegral_ball_eq_setIntegral_ball_zero_add]
  simp only [add_sub_cancel_right]
  rw [← integral_indicator measurableSet_ball, hind,
    integral_fun_norm_addHaar μ ((Iio R).indicator F)]
  -- The radial integral is an integral over `(0, R)` of an explicit rational function.
  set G : ℝ → ℝ := fun r ↦ r ^ (2 * m + 1) * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 1) with hG
  have hrad : ∫ r in Ioi (0 : ℝ), r ^ (finrank ℝ V - 1) • (Iio R).indicator F r =
      ∫ r in (0)..R, G r := by
    have heq : EqOn (fun r ↦ r ^ (finrank ℝ V - 1) • (Iio R).indicator F r)
        ((Ioo 0 R).indicator G) (Ioi 0) := by
      intro r (hr : 0 < r)
      dsimp only
      by_cases hrR : r < R
      · rw [indicator_of_mem (mem_Iio.2 hrR),
          indicator_of_mem (show r ∈ Ioo 0 R from ⟨hr, hrR⟩), smul_eq_mul, hF, hG]
        simp only
        rw [← mul_assoc, ← Real.rpow_natCast r (finrank ℝ V - 1), ← Real.rpow_add hr,
          ← Real.rpow_natCast r (2 * m + 1)]
        congr 3
        push_cast [Nat.cast_sub hn] at hp ⊢
        linarith
      · rw [indicator_of_notMem (mt mem_Iio.1 hrR),
          indicator_of_notMem (show r ∉ Ioo 0 R from fun h ↦ hrR h.2), smul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi heq, setIntegral_indicator measurableSet_Ioo,
      inter_eq_right.mpr Ioo_subset_Ioi_self, intervalIntegral.integral_of_le hR,
      integral_Ioc_eq_integral_Ioo]
  rw [hrad, hG, integral_pow_mul_div_add_sq_pow ht]
  simp only [nsmul_eq_mul, smul_eq_mul]
  ring

/-- **Truncated moments at the logarithmic endpoint, with remainder bound.** In the setting of
`TauCeti.setIntegral_ball_norm_sub_rpow_mul_div_add_norm_sub_sq_pow`, the truncated moment
differs from `n |B(0, 1)| 2 ^ (m - 1) t ^ m log (1 + (R / t)²)` by at most
`n |B(0, 1)| 2 ^ (m - 1) t ^ m H_{m - 1}`, where `H_j` is the `j`-th harmonic number. -/
theorem abs_setIntegral_ball_norm_sub_rpow_mul_div_add_norm_sub_sq_pow_sub_mul_log_le
    (μ : Measure V) [μ.IsAddHaarMeasure] {m : ℕ} (hm : m ≠ 0) {p : ℝ}
    (hp : p + finrank ℝ V = 2 * m) {t : ℝ} (ht : 0 < t) {R : ℝ} (hR : 0 ≤ R) (b : V) :
    |∫ x in ball b R, ‖x - b‖ ^ p * (2 * t / (t ^ 2 + ‖x - b‖ ^ 2)) ^ m ∂μ -
        (finrank ℝ V : ℝ) * μ.real (ball (0 : V) 1) * (2 ^ (m - 1) * t ^ m *
          log (1 + (R / t) ^ 2))| ≤
      (finrank ℝ V : ℝ) * μ.real (ball (0 : V) 1) * (2 ^ (m - 1) * t ^ m * harmonic (m - 1)) := by
  rw [setIntegral_ball_norm_sub_rpow_mul_div_add_norm_sub_sq_pow μ hm hp ht.ne' hR b]
  set w := R ^ 2 / (t ^ 2 + R ^ 2)
  have hw₀ : 0 ≤ w := by positivity
  have hw₁ : w ≤ 1 := div_le_one_of_le₀ (by nlinarith) (by positivity)
  set S := ∑ k ∈ Finset.range (m - 1), w ^ (k + 1) / ((k : ℝ) + 1)
  have hS₀ : 0 ≤ S := Finset.sum_nonneg fun k _ ↦ by positivity
  have hSH : S ≤ harmonic (m - 1) := by
    rw [harmonic, Rat.cast_sum]
    refine Finset.sum_le_sum fun k _ ↦ ?_
    rw [div_eq_mul_inv]
    push_cast
    exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ hw₀ hw₁)
  set K := (finrank ℝ V : ℝ) * μ.real (ball (0 : V) 1) * (2 ^ (m - 1) * t ^ m)
  have hK : 0 ≤ K := by positivity
  calc _ = |-(K * S)| := by congr 1; ring
    _ = K * S := by rw [abs_neg, abs_of_nonneg (mul_nonneg hK hS₀)]
    _ ≤ K * harmonic (m - 1) := mul_le_mul_of_nonneg_left hSH hK
    _ = _ := by ring

end TruncatedMoment

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The integral of the Japanese bracket.** On a real inner product space `V` of dimension
`d < r`, `∫ (1 + ‖x‖ ^ 2) ^ (-r / 2) = π ^ (d / 2) Γ((r - d) / 2) / Γ(r / 2)`. -/
theorem integral_rpow_neg_one_add_norm_sq {r : ℝ} (hr : (finrank ℝ V : ℝ) < r) :
    ∫ x : V, (1 + ‖x‖ ^ 2) ^ (-r / 2) =
      π ^ ((finrank ℝ V : ℝ) / 2) * Gamma ((r - finrank ℝ V) / 2) / Gamma (r / 2) := by
  have hr0 : 0 < r := lt_of_le_of_lt (finrank ℝ V).cast_nonneg hr
  rcases subsingleton_or_nontrivial V with hV | hV
  · -- In dimension zero the integral is the value at the only point, of volume one.
    have hvol : volume.real (univ : Set V) = 1 := by
      have h := (stdOrthonormalBasis ℝ V).volume_parallelepiped
      rw [Subsingleton.eq_univ_of_nonempty
        ⟨0, (mem_parallelepiped_iff _ _).2 ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩⟩] at h
      rw [measureReal_def, h, ENNReal.toReal_one]
    have : Unique V := uniqueOfSubsingleton 0
    rw [integral_unique, hvol, finrank_zero_of_subsingleton, Subsingleton.elim (default : V) 0]
    simp [(Gamma_pos_of_pos (half_pos hr0)).ne']
  set d := finrank ℝ V with hd
  have hd0 : 0 < d := finrank_pos
  have hsum : (d : ℝ) / 2 + (r - d) / 2 = r / 2 := by ring
  -- This is the moment of order `0`, a beta integral.
  have hmoment := integral_norm_rpow_mul_rpow_neg_one_add_norm_sq (volume : Measure V)
    le_rfl (p := 0) (r := r) (by rwa [add_zero])
  simp only [Real.rpow_zero, one_mul, add_zero, sub_zero] at hmoment
  have hΓ := Gamma_pos_of_pos (show 0 < (d : ℝ) / 2 by positivity)
  rw [hmoment, volume_real_unitBall, beta, Gamma_add_one (by positivity), hsum, ← hd]
  field_simp

end TauCeti
