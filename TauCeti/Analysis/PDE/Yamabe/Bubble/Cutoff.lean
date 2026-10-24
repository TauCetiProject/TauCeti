/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Bubble.SobolevQuotient
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Compactly supported Yamabe bubbles

A fixed continuous cutoff with values in `[0,1]` and equal to one near the centre preserves the
limiting critical mass of a concentrating Euclidean Yamabe bubble. A compactly supported `C¹`
cutoff also preserves its limiting Dirichlet energy, so its Sobolev quotient converges to the
Yamabe constant of the round sphere, in every dimension greater than two.

Every nonempty open set contains a nonnegative smooth compactly supported test function with
positive critical mass and quotient below `Y(Sⁿ) + ε` for any `ε > 0`, as proved by
`TauCeti.Yamabe.exists_contDiff_hasCompactSupport_sobolev_quotient_lt`.

The argument uses the critical and energy moments from
`TauCeti.Analysis.PDE.Yamabe.Bubble.Moments` and the exact sphere quotient from
`TauCeti.Yamabe.conformalCoefficient_mul_integral_norm_fderiv_bubble_sq_eq_sphereYamabeConstant`.
The estimates here use strictly subcritical moments of the bubble densities. They establish
convergence, rather than the optimal dimension-dependent orders of the cutoff errors. No
comparison with a curved metric or manifold Yamabe invariant is asserted.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §3 and §6.
-/

public section

noncomputable section

namespace TauCeti.Yamabe

open Filter InnerProductSpace MeasureTheory Metric Module Real Set Topology
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

private lemma cutoff_critical_mass_error_le (hn : 2 < finrank ℝ E) {χ : E → ℝ}
    (hχ : Continuous χ) (hχrange : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    {b : E} {r : ℝ} (hr : 0 < r) (hχone : ∀ x ∈ ball b r, χ x = 1)
    {t : ℝ} (ht : 0 < t) :
    ‖(∫ x, |χ x * bubble t b x| ^ criticalExponent (finrank ℝ E)) -
      ∫ x, bubble t b x ^ criticalExponent (finrank ℝ E)‖ ≤
      r⁻¹ * ∫ x, ‖x - b‖ * bubble t b x ^ criticalExponent (finrank ℝ E) := by
  have hn' : (2 : ℝ) < finrank ℝ E := by exact_mod_cast hn
  have hp : 0 < criticalExponent (finrank ℝ E) := by
    rw [criticalExponent_def]
    exact div_pos (by positivity) (by linarith)
  have hpower (x : E) :
      |χ x * bubble t b x| ^ criticalExponent (finrank ℝ E) =
        χ x ^ criticalExponent (finrank ℝ E) *
          bubble t b x ^ criticalExponent (finrank ℝ E) := by
    rw [abs_of_nonneg (mul_nonneg (hχrange x).1 (bubble_pos ht b x).le),
      Real.mul_rpow (hχrange x).1 (bubble_pos ht b x).le]
  have hweight (x : E) : χ x ^ criticalExponent (finrank ℝ E) ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.rpow_nonneg (hχrange x).1 _, Real.rpow_le_one (hχrange x).1 (hχrange x).2 hp.le⟩
  have hbase := integrable_bubble_rpow_criticalExponent volume (by omega) hn.ne' ht b
  have hcut : Integrable (fun x ↦ |χ x * bubble t b x| ^ criticalExponent (finrank ℝ E)) := by
    have hw : Continuous (fun x ↦ χ x ^ criticalExponent (finrank ℝ E)) :=
      hχ.rpow_const (fun _ ↦ Or.inr hp.le)
    exact (hbase.bdd_mul hw.aestronglyMeasurable
      (.of_forall fun x ↦ by simpa [Real.norm_of_nonneg (hweight x).1] using (hweight x).2)).congr
        (.of_forall fun x ↦ (hpower x).symm)
  have hm : Integrable (fun x ↦ ‖x - b‖ * bubble t b x ^ criticalExponent (finrank ℝ E)) := by
    simpa using integrable_norm_sub_rpow_mul_bubble_rpow_criticalExponent volume hn.ne'
      (p := 1) (by norm_num) (by linarith) ht b
  rw [← integral_sub hcut hbase, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hm.const_mul r⁻¹) (.of_forall fun x ↦ ?_)
  rw [hpower, ← sub_one_mul, norm_mul,
    Real.norm_of_nonneg (Real.rpow_nonneg (bubble_pos ht b x).le _)]
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (bubble_pos ht b x).le _)
  by_cases hx : x ∈ ball b r
  · simpa [hχone x hx] using mul_nonneg (inv_nonneg.mpr hr.le) (norm_nonneg (x - b))
  · have hx' : r ≤ ‖x - b‖ := by simpa [mem_ball, dist_eq_norm, not_lt] using hx
    have hw : ‖χ x ^ criticalExponent (finrank ℝ E) - 1‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonpos (by linarith [(hweight x).2])]
      linarith [(hweight x).1]
    exact hw.trans ((one_le_inv_mul₀ hr).mpr hx')

/-- The critical mass of a bubble multiplied by a fixed continuous cutoff with values in `[0,1]`
and equal to one near its centre converges to the area of the round sphere. -/
theorem tendsto_integral_cutoff_bubble_rpow_criticalExponent (hn : 2 < finrank ℝ E)
    {χ : E → ℝ} (hχ : Continuous χ) (hχrange : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (b : E) (hχone : χ =ᶠ[𝓝 b] fun _ ↦ 1) :
    Tendsto (fun t : ℝ ↦ ∫ x, |χ x * bubble t b x| ^ criticalExponent (finrank ℝ E))
      (𝓝[>] 0) (𝓝 (roundSphereVolume (finrank ℝ E))) := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hχone
  have hn' : (2 : ℝ) < finrank ℝ E := by exact_mod_cast hn
  have hm : Tendsto (fun t : ℝ ↦ r⁻¹ *
      ∫ x, ‖x - b‖ * bubble t b x ^ criticalExponent (finrank ℝ E))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, Real.rpow_one] using
      (tendsto_integral_norm_sub_rpow_mul_bubble_rpow_criticalExponent volume hn.ne'
        (p := 1) (by norm_num) (by linarith) b).const_mul r⁻¹
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _) _ hm
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht : 0 < t := ht
  rw [← integral_bubble_rpow_criticalExponent_eq_roundSphereVolume (by omega) hn.ne' ht b]
  exact cutoff_critical_mass_error_le hn hχ hχrange hr
    hball ht

omit [MeasurableSpace E] [BorelSpace E] in
private lemma cutoff_bubble_derivative_control (hn : 2 < finrank ℝ E) {χ : E → ℝ}
    {b : E} {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hχderiv : ∀ x, (1 + ‖x - b‖ ^ 2) * ‖fderiv ℝ χ x‖ ≤ M)
    {t : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1) {x : E} (hx : r ≤ ‖x - b‖) :
    bubble t b x * ‖fderiv ℝ χ x‖ ≤
      (M / (((finrank ℝ E : ℝ) - 2) * r)) * ‖fderiv ℝ (bubble t b) x‖ := by
  have hk : 0 < (finrank ℝ E : ℝ) - 2 := by
    have : (2 : ℝ) < finrank ℝ E := by exact_mod_cast hn
    linarith
  have hq : 0 < t ^ 2 + ‖x - b‖ ^ 2 := by positivity
  have hd : ‖fderiv ℝ (bubble t b) x‖ =
      (((finrank ℝ E : ℝ) - 2) / (t ^ 2 + ‖x - b‖ ^ 2) * bubble t b x) * ‖x - b‖ := by
    rw [(hasGradientAt_bubble ht b x).hasFDerivAt.fderiv,
      LinearIsometryEquiv.norm_map, norm_smul, norm_neg,
      Real.norm_of_nonneg (mul_nonneg (div_nonneg hk.le hq.le) (bubble_pos ht b x).le)]
  have hnum : (t ^ 2 + ‖x - b‖ ^ 2) * ‖fderiv ℝ χ x‖ ≤ M := by
    have ht₂ : t ^ 2 ≤ 1 := by nlinarith
    exact (mul_le_mul_of_nonneg_right (by linarith :
      t ^ 2 + ‖x - b‖ ^ 2 ≤ 1 + ‖x - b‖ ^ 2) (norm_nonneg _)).trans (hχderiv x)
  rw [hd]
  rw [show M / (((finrank ℝ E : ℝ) - 2) * r) *
      ((((finrank ℝ E : ℝ) - 2) / (t ^ 2 + ‖x - b‖ ^ 2) * bubble t b x) * ‖x - b‖) =
      M * bubble t b x * ‖x - b‖ / (r * (t ^ 2 + ‖x - b‖ ^ 2)) by field_simp]
  rw [le_div_iff₀ (mul_pos hr hq)]
  calc
    bubble t b x * ‖fderiv ℝ χ x‖ * (r * (t ^ 2 + ‖x - b‖ ^ 2)) =
        bubble t b x * r * ((t ^ 2 + ‖x - b‖ ^ 2) * ‖fderiv ℝ χ x‖) := by ring
    _ ≤ bubble t b x * r * M :=
      mul_le_mul_of_nonneg_left hnum (mul_nonneg (bubble_pos ht b x).le hr.le)
    _ ≤ M * bubble t b x * ‖x - b‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hx (mul_nonneg hM (bubble_pos ht b x).le)]

private lemma cutoff_bubble_energy_error_le (hn : 2 < finrank ℝ E) {χ : E → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hχrange : ∀ x, χ x ∈ Icc (0 : ℝ) 1) {b : E} {r M : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hχone : ∀ x ∈ ball b r, χ x = 1)
    (hχderiv : ∀ x, (1 + ‖x - b‖ ^ 2) * ‖fderiv ℝ χ x‖ ≤ M)
    {t : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1) :
    ‖(∫ x, ‖fderiv ℝ (fun y ↦ χ y * bubble t b y) x‖ ^ 2) -
      ∫ x, ‖fderiv ℝ (bubble t b) x‖ ^ 2‖ ≤
      (((1 + M / (((finrank ℝ E : ℝ) - 2) * r)) ^ 2 + 1) / r ^ (1 / 2 : ℝ)) *
        ∫ x, ‖x - b‖ ^ (1 / 2 : ℝ) * ‖fderiv ℝ (bubble t b) x‖ ^ 2 := by
  have hn' : (2 : ℝ) < finrank ℝ E := by exact_mod_cast hn
  have hk : 0 < (finrank ℝ E : ℝ) - 2 := by linarith
  let K := M / (((finrank ℝ E : ℝ) - 2) * r)
  have hK : 0 ≤ K := div_nonneg hM (mul_nonneg hk.le hr.le)
  -- Compact support gives integrability; outside the region where the cutoff is one,
  -- its extra derivative is controlled by the bubble derivative.
  have hcut : Integrable (fun x ↦ ‖fderiv ℝ (fun y ↦ χ y * bubble t b y) x‖ ^ 2) volume := by
    have hcd : ContDiff ℝ 1 (fun y ↦ χ y * bubble t b y) :=
      hχ.mul (contDiff_bubble ht.ne' b)
    have hcc : HasCompactSupport (fun y ↦ χ y * bubble t b y) := hχc.mul_right
    have hc := (hcd.continuous_fderiv one_ne_zero).norm
    refine ((hc.mul hc).integrable_of_hasCompactSupport (μ := volume)
      ((hcc.fderiv ℝ).norm.mul_right
        (f' := fun x ↦ ‖fderiv ℝ (fun y ↦ χ y * bubble t b y) x‖))).congr
          (.of_forall fun x ↦ ?_)
    simp only [Pi.mul_apply, pow_two]
  have hn₃ : (3 : ℝ) ≤ finrank ℝ E := by exact_mod_cast (show 3 ≤ finrank ℝ E by omega)
  have hm := integrable_norm_sub_rpow_mul_norm_fderiv_bubble_sq volume
    (p := 1 / 2) (by norm_num) (by linarith) ht b
  rw [← integral_sub hcut (integrable_norm_fderiv_bubble_sq volume hn ht b),
    ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hm.const_mul _) (.of_forall fun x ↦ ?_)
  by_cases hx : x ∈ ball b r
  · have hlocal : (fun y ↦ χ y * bubble t b y) =ᶠ[𝓝 x] bubble t b := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      simp [hχone y hy]
    rw [hlocal.fderiv_eq, sub_self, norm_zero]
    positivity
  · have hx' : r ≤ ‖x - b‖ := by simpa [mem_ball, dist_eq_norm, not_lt] using hx
    have hcontrol := cutoff_bubble_derivative_control hn hr hM hχderiv ht ht₁ hx'
    have hnorm : ‖fderiv ℝ (fun y ↦ χ y * bubble t b y) x‖ ≤
        (1 + K) * ‖fderiv ℝ (bubble t b) x‖ := by
      rw [fderiv_fun_mul (hχ.differentiable_one x)
        ((contDiff_bubble (m := 1) ht.ne' b).differentiable_one x)]
      calc
        ‖χ x • fderiv ℝ (bubble t b) x + bubble t b x • fderiv ℝ χ x‖ ≤
            ‖χ x‖ * ‖fderiv ℝ (bubble t b) x‖ + bubble t b x * ‖fderiv ℝ χ x‖ := by
          simpa [norm_smul, Real.norm_of_nonneg (bubble_pos ht b x).le] using
            norm_add_le (χ x • fderiv ℝ (bubble t b) x) (bubble t b x • fderiv ℝ χ x)
        _ ≤ 1 * ‖fderiv ℝ (bubble t b) x‖ + K * ‖fderiv ℝ (bubble t b) x‖ :=
          add_le_add (mul_le_mul_of_nonneg_right
            (by simpa [Real.norm_of_nonneg (hχrange x).1] using (hχrange x).2) (norm_nonneg _))
            hcontrol
        _ = _ := by ring
    have hsquare : ‖fderiv ℝ (fun y ↦ χ y * bubble t b y) x‖ ^ 2 ≤
        (1 + K) ^ 2 * ‖fderiv ℝ (bubble t b) x‖ ^ 2 := by
      simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (by linarith : 0 ≤ 1 + K) (norm_nonneg _))).mpr hnorm
    have habs : ‖‖fderiv ℝ (fun y ↦ χ y * bubble t b y) x‖ ^ 2 -
        ‖fderiv ℝ (bubble t b) x‖ ^ 2‖ ≤
        ((1 + K) ^ 2 + 1) * ‖fderiv ℝ (bubble t b) x‖ ^ 2 := by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [sq_nonneg ‖fderiv ℝ (fun y ↦ χ y * bubble t b y) x‖]
    apply habs.trans
    have hweight : r ^ (1 / 2 : ℝ) ≤ ‖x - b‖ ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hr.le hx' (by norm_num)
    dsimp only [K]
    rw [div_mul_eq_mul_div, le_div_iff₀ (Real.rpow_pos_of_pos hr _)]
    nlinarith [mul_le_mul_of_nonneg_left hweight
      (mul_nonneg (by positivity : 0 ≤ (1 + K) ^ 2 + 1)
        (sq_nonneg ‖fderiv ℝ (bubble t b) x‖))]

/-- The conformal Dirichlet energy of a bubble multiplied by a fixed compactly supported `C¹`
cutoff with values in `[0,1]` and equal to one near the centre converges to
`n (n - 1) |Sⁿ|`, the conformal energy of an uncut bubble, in dimension `n > 2`. -/
theorem tendsto_conformalCoefficient_mul_integral_norm_fderiv_cutoff_bubble_sq
    (hn : 2 < finrank ℝ E) {χ : E → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hχc : HasCompactSupport χ) (hχrange : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (b : E) (hχone : χ =ᶠ[𝓝 b] fun _ ↦ 1) :
    Tendsto (fun t : ℝ ↦ conformalCoefficient (finrank ℝ E) *
      ∫ x, ‖fderiv ℝ (fun y ↦ χ y * bubble t b y) x‖ ^ 2)
      (𝓝[>] 0) (𝓝 ((finrank ℝ E : ℝ) * (finrank ℝ E - 1) *
        roundSphereVolume (finrank ℝ E))) := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hχone
  -- The weighted cutoff derivative is bounded because it has compact support.
  have hcont : Continuous (fun x ↦ (1 + ‖x - b‖ ^ 2) * ‖fderiv ℝ χ x‖) :=
    (continuous_const.add ((continuous_id.sub continuous_const).norm.pow 2)).mul
      (hχ.continuous_fderiv one_ne_zero).norm
  have hcompact : HasCompactSupport (fun x ↦ (1 + ‖x - b‖ ^ 2) * ‖fderiv ℝ χ x‖) :=
    (hχc.fderiv ℝ).norm.mul_left
  obtain ⟨M, hMbound⟩ := hcont.bounded_above_of_compact_support hcompact
  have hM : 0 ≤ M := (norm_nonneg _).trans (hMbound b)
  have hχderiv (x : E) : (1 + ‖x - b‖ ^ 2) * ‖fderiv ℝ χ x‖ ≤ M :=
    (le_abs_self _).trans (hMbound x)
  let C := ((1 + M / (((finrank ℝ E : ℝ) - 2) * r)) ^ 2 + 1) / r ^ (1 / 2 : ℝ)
  have hn₃ : (3 : ℝ) ≤ finrank ℝ E := by exact_mod_cast (show 3 ≤ finrank ℝ E by omega)
  -- The half-moment is finite in every dimension greater than two and decays with the scale.
  have hm : Tendsto (fun t : ℝ ↦ C *
      ∫ x, ‖x - b‖ ^ (1 / 2 : ℝ) * ‖fderiv ℝ (bubble t b) x‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_integral_norm_sub_rpow_mul_norm_fderiv_bubble_sq volume
        (p := 1 / 2) (by norm_num) (by linarith) b).const_mul C
  have hdiff : Tendsto (fun t : ℝ ↦
      (∫ x, ‖fderiv ℝ (fun y ↦ χ y * bubble t b y) x‖ ^ 2) -
        ∫ x, ‖fderiv ℝ (bubble t b) x‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' _ hm
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with t ht ht₁
    exact cutoff_bubble_energy_error_le hn hχ hχc hχrange hr hM hball hχderiv ht ht₁.le
  have hlim := (hdiff.const_mul (conformalCoefficient (finrank ℝ E))).add_const
    ((finrank ℝ E : ℝ) * (finrank ℝ E - 1) * roundSphereVolume (finrank ℝ E))
  simp only [mul_zero, zero_add] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [← conformalCoefficient_mul_integral_norm_fderiv_bubble_sq_eq_roundSphereVolume hn ht b]
  ring

/-- The actual Euclidean Sobolev quotient of a fixed compact cutoff of the concentrating bubble
converges to the Yamabe constant of the round sphere. The cutoff only needs to be `C¹`. -/
theorem tendsto_cutoff_bubble_sobolev_quotient (hn : 2 < finrank ℝ E)
    {χ : E → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hχrange : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (b : E) (hχone : χ =ᶠ[𝓝 b] fun _ ↦ 1) :
    Tendsto (fun t : ℝ ↦
      (conformalCoefficient (finrank ℝ E) *
        ∫ x, ‖fderiv ℝ (fun y ↦ χ y * bubble t b y) x‖ ^ 2) /
      (∫ x, |χ x * bubble t b x| ^ criticalExponent (finrank ℝ E)) ^
        (2 / criticalExponent (finrank ℝ E)))
      (𝓝[>] 0) (𝓝 (sphereYamabeConstant (finrank ℝ E))) := by
  have hmass := tendsto_integral_cutoff_bubble_rpow_criticalExponent hn hχ.continuous
    hχrange b hχone
  have hden := hmass.rpow_const (p := 2 / criticalExponent (finrank ℝ E))
    (Or.inl (roundSphereVolume_pos (finrank ℝ E)).ne')
  have henergy := tendsto_conformalCoefficient_mul_integral_norm_fderiv_cutoff_bubble_sq
    hn hχ hχc hχrange b hχone
  have hlim := henergy.div hden (Real.rpow_pos_of_pos (roundSphereVolume_pos _) _).ne'
  have hp : 2 / criticalExponent (finrank ℝ E) =
      ((finrank ℝ E : ℝ) - 2) / finrank ℝ E := by
    have h₀ : (finrank ℝ E : ℝ) ≠ 0 := by exact_mod_cast (show finrank ℝ E ≠ 0 by omega)
    have h₂ : (finrank ℝ E : ℝ) - 2 ≠ 0 :=
      sub_ne_zero.mpr (by exact_mod_cast hn.ne')
    rw [criticalExponent_def]
    field_simp
  have hc : sphereYamabeConstant (finrank ℝ E) =
      ((finrank ℝ E : ℝ) * (finrank ℝ E - 1) * roundSphereVolume (finrank ℝ E)) /
        roundSphereVolume (finrank ℝ E) ^ (2 / criticalExponent (finrank ℝ E)) := by
    apply (eq_div_iff (Real.rpow_pos_of_pos (roundSphereVolume_pos _) _).ne').2
    rw [hp]
    exact sphereYamabeConstant_mul_roundSphereVolume_rpow (by omega)
  simpa only [Pi.div_apply, ← hc] using hlim

/-- Every nonempty open set in dimension greater than two contains a nonnegative smooth
compactly supported test function with positive critical mass and Sobolev quotient less than
`Y(Sⁿ) + ε`. Thus restricting to compactly supported smooth tests cannot improve the sphere
constant in the Euclidean Sobolev inequality. -/
theorem exists_contDiff_hasCompactSupport_sobolev_quotient_lt (hn : 2 < finrank ℝ E)
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩne : Ω.Nonempty) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : E → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ tsupport u ⊆ Ω ∧
      (∀ x, 0 ≤ u x) ∧ (0 < ∫ x, |u x| ^ criticalExponent (finrank ℝ E)) ∧
      (conformalCoefficient (finrank ℝ E) * ∫ x, ‖fderiv ℝ u x‖ ^ 2) /
        (∫ x, |u x| ^ criticalExponent (finrank ℝ E)) ^
          (2 / criticalExponent (finrank ℝ E)) < sphereYamabeConstant (finrank ℝ E) + ε := by
  obtain ⟨b, hb⟩ := hΩne
  obtain ⟨χ, hχ, hχrange, hχone, hχc, hχΩ⟩ :=
    (isCompact_singleton (x := b)).exists_contDiff_cutoff hΩ (singleton_subset_iff.mpr hb)
  have hχrange' (x : E) : χ x ∈ Icc (0 : ℝ) 1 := hχrange (mem_range_self x)
  have hχone' : χ =ᶠ[𝓝 b] fun _ ↦ 1 := by
    filter_upwards [mem_interior_iff_mem_nhds.mp (hχone (mem_singleton b))] with x hx
    exact hx
  have hm := tendsto_integral_cutoff_bubble_rpow_criticalExponent hn hχ.continuous hχrange' b hχone'
  have hq := tendsto_cutoff_bubble_sobolev_quotient hn (hχ.of_le (by simp)) hχc hχrange' b hχone'
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t ∧
      (0 < ∫ x, |χ x * bubble t b x| ^ criticalExponent (finrank ℝ E)) ∧
      (conformalCoefficient (finrank ℝ E) *
        ∫ x, ‖fderiv ℝ (fun y ↦ χ y * bubble t b y) x‖ ^ 2) /
        (∫ x, |χ x * bubble t b x| ^ criticalExponent (finrank ℝ E)) ^
          (2 / criticalExponent (finrank ℝ E)) < sphereYamabeConstant (finrank ℝ E) + ε := by
    filter_upwards [self_mem_nhdsWithin,
      hm.eventually_const_lt (roundSphereVolume_pos (finrank ℝ E)),
      hq.eventually_lt_const (lt_add_of_pos_right _ hε)] with t ht hmt hqt
    exact ⟨ht, hmt, hqt⟩
  obtain ⟨t, ht, hmt, hqt⟩ := hev.exists
  refine ⟨fun x ↦ χ x * bubble t b x, hχ.mul (contDiff_bubble ht.ne' b), hχc.mul_right,
    tsupport_mul_subset_left.trans hχΩ, fun x ↦ mul_nonneg (hχrange' x).1 (bubble_pos ht b x).le,
    hmt, hqt⟩

end TauCeti.Yamabe
