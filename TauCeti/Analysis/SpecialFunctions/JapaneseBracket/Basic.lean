/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Analysis.SpecialFunctions.Beta
import TauCeti.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The integral of the Japanese bracket

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

## Main declarations

* `TauCeti.integrable_rpow_neg_sq_add_norm_sq`: the rescaled bracket
  `x ↦ (c ^ 2 + ‖x‖ ^ 2) ^ (-r / 2)`, `c ≠ 0`, is integrable for every additive Haar measure.
* `TauCeti.sub_two_mul_integral_radial`: an identity between two radial moments of the rescaled
  bracket.
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

end Integrability

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
  -- The radial integral is half of Euler's second beta integral, after `u = y ^ 2`.
  have hrad : ∫ y in Ioi (0 : ℝ), y ^ (d - 1) • (1 + y ^ 2) ^ (-r / 2) =
      beta (d / 2) ((r - d) / 2) / 2 := by
    rw [← integral_rpow_mul_one_add_sq_rpow (by positivity) hr]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
    rw [smul_eq_mul, ← Real.rpow_natCast, Nat.cast_sub hd0, Nat.cast_one]
  have hΓ := Gamma_pos_of_pos (show 0 < (d : ℝ) / 2 by positivity)
  rw [integral_fun_norm_addHaar volume (fun t ↦ (1 + t ^ 2) ^ (-r / 2)), hrad, volume_real_unitBall,
    beta, nsmul_eq_mul, smul_eq_mul, Gamma_add_one (by positivity), hsum, ← hd]
  field_simp

end TauCeti
