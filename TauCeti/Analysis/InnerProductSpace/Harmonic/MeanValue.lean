/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.Ball
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Average
import TauCeti.Analysis.Distribution.DuBoisReymond
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import TauCeti.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The mean-value property of harmonic functions

Let `E` be a finite-dimensional real inner product space with an additive Haar measure `μ`, and
let `u : E → F` be harmonic on a neighbourhood of the closed ball `closedBall x₀ R`. This file
proves the **mean-value property**: `u x₀` is the average of `u` over the sphere of radius `R`
about `x₀`, and the average of `u` over the ball of radius `R` about `x₀`,

`⨍ θ ∈ S, u (x₀ + R • θ) ∂μ.toSphere = u x₀` and `⨍ x in ball x₀ R, u x ∂μ = u x₀`.

The sphere of radius `R` about `x₀` is parametrized by the unit sphere `S` through
`θ ↦ x₀ + R • θ`, and carries Mathlib's surface measure `μ.toSphere`, the measure that makes
`μ` the product of the surface and radial measures in polar coordinates. Only the sphere average
needs `E ≠ 0`: in the trivial space the unit sphere is empty, and the integral identities hold
with both sides zero.

## The argument

Write `Φ s = ∫ θ ∈ S, u (s • θ) ∂μ.toSphere` for the sphere integral at radius `s` about the
origin. The classical proof differentiates `Φ` in `s` and evaluates `Φ'` by the divergence theorem
on the ball; the proof here instead shows that the *distributional* derivative of `Φ` on `(0, R)`
vanishes, and then applies the du Bois-Reymond lemma
`ContinuousOn.exists_eqOn_const_Ioo_of_integral_deriv_smul_eq_zero`. No divergence theorem is
needed.

A harmonic function is weakly harmonic
(`InnerProductSpace.HarmonicOnNhd.integral_laplacian_smul_eq_zero`): `∫ Δχ • u ∂μ = 0` for every
test function `χ` supported in the ball. Taking `χ` radial, `χ x = ρ (‖x‖ ^ 2)`, the Laplacian
`Δχ x = 4 ‖x‖² ρ'' (‖x‖²) + 2 n ρ' (‖x‖²)` is radial too (`ContDiff.laplacian_comp_norm_sq`),
and integrating in polar coordinates with the radial variable
outermost (`TauCeti.integral_eq_integral_Ioi_integral_toSphere`) turns the identity into

`∫ s in (0, ∞), s ^ (n - 1) (4 s² ρ'' (s²) + 2 n ρ' (s²)) • Φ s = 0`,

whose weight is `2 (s ^ n ρ' (s ^ 2))'`. Every test function `ψ` on `(0, R)` is of the form
`ψ s = s ^ n ρ' (s ^ 2)` for such a `ρ`, namely the primitive of `t ↦ ψ (√t) / (√t) ^ n`, so
`∫ ψ' • Φ = 0` for all of them, and `Φ` is constant on `(0, R)`. Continuity of `Φ` on `[0, R]`
gives `Φ R = Φ 0 = μ.toSphere(S) • u 0`; integrating the sphere identity over the radii `s < R`, in
polar coordinates once more, gives the ball version.

## Main declarations

* `InnerProductSpace.HarmonicOnNhd.integral_toSphere_eq`,
  `InnerProductSpace.HarmonicOnNhd.average_toSphere_eq`: **the mean-value property on spheres**,
  in integral and in average form.
* `InnerProductSpace.HarmonicOnNhd.setIntegral_ball_eq`,
  `InnerProductSpace.HarmonicOnNhd.setAverage_ball_eq`: **the mean-value property on balls**, in
  integral and in average form.

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.2.2, Theorem 2.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 2.1.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian MeasureTheory Metric Set Filter Topology TopologicalSpace
open scoped Distributions ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {u : E → F} {R : ℝ}

/-- The distributional derivative of the sphere integrals `s ↦ ∫ θ, u (s • θ) ∂μ.toSphere` of a
harmonic function vanishes on `(0, R)`: `∫ ψ' • Φ = 0` for every test function `ψ` on `(0, R)`. -/
private lemma integral_deriv_smul_integral_toSphere_eq_zero {Ω : Opens E}
    (hu : HarmonicOnNhd u Ω) (hΩ : closedBall (0 : E) R ⊆ Ω) (hR : 0 < R) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψs : tsupport ψ ⊆ Ioo 0 R) :
    ∫ s, deriv ψ s • ∫ θ : sphere (0 : E) 1, u (s • (θ : E)) ∂μ.toSphere = 0 := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero (Module.finrank_pos (R := ℝ) (M := E)).ne'
  have hψ0 : ∀ r, r ∉ Ioo (0 : ℝ) R → ψ r = 0 := fun r hr ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hr (hψs h)
  -- The radial profile `σ`, chosen so that `ψ s = s ^ n * σ (s ^ 2)` for `s > 0`.
  set σ : ℝ → ℝ := fun t ↦ ψ (√t) / (√t) ^ Module.finrank ℝ E with hσ_def
  have hσ0 : ∀ t, R ^ 2 ≤ t → σ t = 0 := by
    intro t ht
    have : R ≤ √t := by
      rw [← Real.sqrt_sq hR.le]
      exact Real.sqrt_le_sqrt ht
    simp [hσ_def, hψ0 (√t) fun h ↦ h.2.not_ge this]
  have hσ : ContDiff ℝ ∞ σ := by
    rw [contDiff_iff_contDiffAt]
    intro t
    by_cases ht : √t ∈ tsupport ψ
    · have ht0 : 0 < t := Real.sqrt_pos.mp (hψs ht).1
      exact ((hψ.contDiffAt.comp t (Real.contDiffAt_sqrt ht0.ne')).div
        ((Real.contDiffAt_sqrt ht0.ne').pow _) (pow_ne_zero _ (Real.sqrt_pos.mpr ht0).ne'))
    · have hev : ∀ᶠ s in 𝓝 t, σ s = 0 := by
        have : ∀ᶠ s in 𝓝 t, √s ∉ tsupport ψ :=
          Real.continuous_sqrt.continuousAt.preimage_mem_nhds
            ((isClosed_tsupport ψ).isOpen_compl.mem_nhds ht)
        filter_upwards [this] with s hs
        simp [hσ_def, image_eq_zero_of_notMem_tsupport hs]
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
  have hσc : Continuous σ := hσ.continuous
  -- Its primitive `ρ`, vanishing beyond `R ^ 2`.
  set ρ : ℝ → ℝ := fun t ↦ ∫ s in R ^ 2..t, σ s with hρ_def
  have hρderiv : ∀ t, HasDerivAt ρ (σ t) t := fun t ↦
    intervalIntegral.integral_hasDerivAt_right (hσc.intervalIntegrable _ _)
      (hσc.stronglyMeasurableAtFilter _ _) hσc.continuousAt
  have hρ' : deriv ρ = σ := funext fun t ↦ (hρderiv t).deriv
  have hρ : ContDiff ℝ ∞ ρ :=
    contDiff_infty_iff_deriv.mpr ⟨fun t ↦ (hρderiv t).differentiableAt, hρ' ▸ hσ⟩
  have hρ0 : ∀ t, R ^ 2 ≤ t → ρ t = 0 := by
    intro t ht
    simp only [hρ_def]
    refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun s hs ↦ ?_).trans
      intervalIntegral.integral_zero
    rw [uIcc_of_le ht] at hs
    exact hσ0 s hs.1
  -- The radial test function `χ x = ρ (‖x‖ ^ 2)`, supported in the closed ball.
  have hχ_supp : tsupport (fun x : E ↦ ρ (‖x‖ ^ 2)) ⊆ closedBall (0 : E) R := by
    refine (closure_mono fun x hx ↦ ?_).trans closure_ball_subset_closedBall
    rw [mem_ball_zero_iff]
    by_contra h
    exact hx (hρ0 _ (pow_le_pow_left₀ hR.le (not_lt.mp h) 2))
  let χ : 𝓓(Ω, ℝ) := ⟨fun x ↦ ρ (‖x‖ ^ 2), hρ.comp (contDiff_norm_sq ℝ),
    (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) hχ_supp, hχ_supp.trans hΩ⟩
  have hχ : (χ : E → ℝ) = fun x ↦ ρ (‖x‖ ^ 2) := rfl
  have hΔ : Δ (χ : E → ℝ) = fun x ↦
      4 * ‖x‖ ^ 2 * deriv σ (‖x‖ ^ 2) + 2 * (Module.finrank ℝ E : ℝ) * σ (‖x‖ ^ 2) := by
    funext x
    rw [hχ, (hρ.of_le (by simp)).laplacian_comp_norm_sq, hρ']
  -- Weak harmonicity against `χ`, in polar coordinates.
  have hgreen := hu.integral_laplacian_smul_eq_zero (μ := μ) χ
  have hΔcont : Continuous (Δ (χ : E → ℝ)) := by
    rw [hΔ]
    have hσ' : Continuous (deriv σ) := hσ.continuous_deriv (by simp)
    fun_prop
  have hf_cont : Continuous fun x ↦ Δ (χ : E → ℝ) x • u x :=
    (hΔcont.continuousOn.smul hu.contDiffOn.continuousOn).continuous_of_tsupport_subset Ω.isOpen
      ((tsupport_smul_subset_left _ _).trans
        ((tsupport_laplacian_subset _).trans χ.tsupport_subset))
  have hf_supp : HasCompactSupport fun x ↦ Δ (χ : E → ℝ) x • u x :=
    (HasCompactSupport.intro χ.hasCompactSupport fun x hx ↦
      image_eq_zero_of_notMem_tsupport fun h ↦ hx (tsupport_laplacian_subset _ h)).smul_right
  rw [integral_eq_integral_Ioi_integral_toSphere _
    (hf_cont.integrable_of_hasCompactSupport hf_supp)] at hgreen
  -- On the sphere of radius `s`, the weight is `2 ψ' s`.
  have hinner : ∀ s ∈ Ioi (0 : ℝ), s ^ (Module.finrank ℝ E - 1) •
      ∫ θ : sphere (0 : E) 1, Δ (χ : E → ℝ) (s • (θ : E)) • u (s • (θ : E)) ∂μ.toSphere =
        (2 * deriv ψ s) • ∫ θ : sphere (0 : E) 1, u (s • (θ : E)) ∂μ.toSphere := by
    intro s hs
    have hs : 0 < s := hs
    have hnorm : ∀ θ : sphere (0 : E) 1, ‖s • (θ : E)‖ = s := fun θ ↦ by
      rw [norm_smul, norm_eq_of_mem_sphere θ, mul_one, Real.norm_of_nonneg hs.le]
    have hΔs : ∀ θ : sphere (0 : E) 1, Δ (χ : E → ℝ) (s • (θ : E)) =
        4 * s ^ 2 * deriv σ (s ^ 2) + 2 * (Module.finrank ℝ E : ℝ) * σ (s ^ 2) := fun θ ↦ by
      simp only [hΔ, hnorm]
    simp_rw [hΔs]
    rw [MeasureTheory.integral_smul, smul_smul]
    congr 1
    have hψeq : ψ =ᶠ[𝓝 s] fun r ↦ r ^ Module.finrank ℝ E * σ (r ^ 2) := by
      filter_upwards [Ioi_mem_nhds hs] with r hr
      have hr : 0 < r := hr
      simp only [hσ_def, Real.sqrt_sq hr.le]
      rw [mul_div_cancel₀ _ (pow_ne_zero _ hr.ne')]
    have hd : HasDerivAt (fun r ↦ r ^ Module.finrank ℝ E * σ (r ^ 2))
        ((Module.finrank ℝ E : ℝ) * s ^ (Module.finrank ℝ E - 1) * σ (s ^ 2) +
          s ^ Module.finrank ℝ E * (deriv σ (s ^ 2) * ((2 : ℕ) * s ^ (2 - 1)))) s :=
      (hasDerivAt_pow _ s).mul ((hσ.differentiable (by simp) _).hasDerivAt.comp s
        (hasDerivAt_pow 2 s))
    rw [hψeq.deriv_eq, hd.deriv, hm]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hinner,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs ↦ ?_] at hgreen
  · simp_rw [mul_smul] at hgreen
    rw [MeasureTheory.integral_smul] at hgreen
    exact (smul_eq_zero.mp hgreen).resolve_left two_ne_zero
  · have : deriv ψ s = 0 := by
      by_contra h
      exact hs (hψs (support_deriv_subset h)).1
    simp [this]

/-- The mean-value property on spheres about the origin. -/
private lemma integral_toSphere_eq_of_harmonicOnNhd_zero
    (hu : HarmonicOnNhd u (closedBall (0 : E) R)) (hR : 0 ≤ R) :
    ∫ θ : sphere (0 : E) 1, u (R • (θ : E)) ∂μ.toSphere = μ.toSphere.real univ • u 0 := by
  rcases hR.eq_or_lt with rfl | hR
  · simp [integral_const]
  -- The open set of harmonicity contains the closed ball.
  set Ω : Opens E := ⟨{x | HarmonicAt u x}, isOpen_setOfPred_harmonicAt u⟩ with hΩ_def
  have hΩ : closedBall (0 : E) R ⊆ Ω := fun x hx ↦ hu x hx
  have huΩ : HarmonicOnNhd u Ω := fun x hx ↦ hx
  set Φ : ℝ → F := fun s ↦ ∫ θ : sphere (0 : E) 1, u (s • (θ : E)) ∂μ.toSphere with hΦ_def
  have hΦc : ContinuousOn Φ (Icc 0 R) := hu.contDiffOn.continuousOn.integral_toSphere_smul
  obtain ⟨c, hc⟩ :=
    (hΦc.mono Ioo_subset_Icc_self).exists_eqOn_const_Ioo_of_integral_deriv_smul_eq_zero
      fun ψ hψ hψs ↦ integral_deriv_smul_integral_toSphere_eq_zero huΩ hΩ hR hψ hψs
  have hIcc : EqOn Φ (fun _ ↦ c) (Icc 0 R) :=
    hc.of_subset_closure hΦc continuousOn_const Ioo_subset_Icc_self (by rw [closure_Ioo hR.ne])
  calc Φ R = c := hIcc ⟨hR.le, le_rfl⟩
    _ = Φ 0 := (hIcc ⟨le_rfl, hR.le⟩).symm
    _ = μ.toSphere.real univ • u 0 := by simp [hΦ_def, integral_const]

omit [Nontrivial E] in
/-- **The mean-value property on spheres.** If `u` is harmonic on a neighbourhood of the closed
ball `closedBall x₀ R`, `0 ≤ R`, then the integral of `u` over the sphere of radius `R` about `x₀`,
parametrized by the unit sphere with the surface measure `μ.toSphere`, is the total surface
measure times `u x₀`. (In the trivial space the unit sphere is empty and both sides vanish.) -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.integral_toSphere_eq {x₀ : E}
    (hu : HarmonicOnNhd u (closedBall x₀ R)) (hR : 0 ≤ R) :
    ∫ θ : sphere (0 : E) 1, u (x₀ + R • (θ : E)) ∂μ.toSphere = μ.toSphere.real univ • u x₀ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : IsEmpty (sphere (0 : E) 1) :=
      ⟨fun θ ↦ by simpa [Subsingleton.elim (θ : E) 0] using norm_eq_of_mem_sphere θ⟩
    simp [integral_of_isEmpty, Measure.eq_zero_of_isEmpty]
  have h := integral_toSphere_eq_of_harmonicOnNhd_zero (μ := μ)
    ((harmonicOnNhd_comp_add_right_closedBall_zero_iff x₀ R).mpr hu) hR
  simpa [add_comm] using h

/-- **The mean-value property on spheres, average form.** A function harmonic on a neighbourhood
of the closed ball `closedBall x₀ R`, `0 ≤ R`, in a nontrivial space has value `u x₀` at the
centre equal to its average over the sphere of radius `R` about `x₀`. -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.average_toSphere_eq {x₀ : E}
    (hu : HarmonicOnNhd u (closedBall x₀ R)) (hR : 0 ≤ R) :
    ⨍ θ : sphere (0 : E) 1, u (x₀ + R • (θ : E)) ∂μ.toSphere = u x₀ := by
  have hpos : 0 < μ.toSphere.real univ := by
    rw [Measure.toSphere_real_apply_univ, measureReal_def]
    exact mul_pos (Nat.cast_pos.mpr Module.finrank_pos)
      (ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne)
  rw [average_eq, hu.integral_toSphere_eq hR, smul_smul,
    inv_mul_cancel₀ hpos.ne', one_smul]

/-- The mean-value property on balls about the origin. -/
private lemma setIntegral_ball_eq_of_harmonicOnNhd_zero
    (hu : HarmonicOnNhd u (closedBall (0 : E) R)) (hR : 0 < R) :
    ∫ x in ball (0 : E) R, u x ∂μ = μ.real (ball (0 : E) R) • u 0 := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero (Module.finrank_pos (R := ℝ) (M := E)).ne'
  have hcont : ContinuousOn u (closedBall (0 : E) R) := hu.contDiffOn.continuousOn
  have hint : Integrable ((ball (0 : E) R).indicator u) μ :=
    ((hcont.integrableOn_compact (isCompact_closedBall _ _)).mono_set
      ball_subset_closedBall).integrable_indicator measurableSet_ball
  rw [← integral_indicator measurableSet_ball, integral_eq_integral_Ioi_integral_toSphere _ hint]
  -- The sphere integrals of the truncation: the sphere identity below the radius `R`, zero above.
  have hinner : ∀ s ∈ Ioi (0 : ℝ), s ^ (Module.finrank ℝ E - 1) •
      ∫ θ : sphere (0 : E) 1, (ball (0 : E) R).indicator u (s • (θ : E)) ∂μ.toSphere =
        (Iio R).indicator (fun s ↦ s ^ (Module.finrank ℝ E - 1) • (μ.toSphere.real univ • u 0))
          s := by
    intro s hs
    have hs : 0 < s := hs
    have hmem : ∀ θ : sphere (0 : E) 1, s • (θ : E) ∈ ball (0 : E) R ↔ s < R := fun θ ↦ by
      rw [mem_ball_zero_iff, norm_smul, norm_eq_of_mem_sphere θ, mul_one, Real.norm_of_nonneg hs.le]
    by_cases hsR : s < R
    · rw [indicator_of_mem (mem_Iio.mpr hsR)]
      simp_rw [indicator_of_mem ((hmem _).mpr hsR)]
      rw [integral_toSphere_eq_of_harmonicOnNhd_zero
        (hu.mono (closedBall_subset_closedBall hsR.le)) hs.le]
    · rw [indicator_of_notMem (by simpa using hsR)]
      simp_rw [indicator_of_notMem ((not_congr (hmem _)).mpr hsR)]
      simp
  have hball : μ.real (ball (0 : E) R) = R ^ (m + 1) * μ.real (ball (0 : E) 1) := by
    rw [measureReal_def, Measure.addHaar_ball μ _ hR.le, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), hm, measureReal_def]
  have hsph : μ.toSphere.real univ = ((m : ℝ) + 1) * μ.real (ball (0 : E) 1) := by
    rw [Measure.toSphere_real_apply_univ, hm]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hinner, setIntegral_indicator measurableSet_Iio,
    Ioi_inter_Iio, integral_smul_const, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hR.le, integral_pow, hball, hsph, smul_smul, hm,
    Nat.add_sub_cancel, zero_pow (Nat.succ_ne_zero m), sub_zero]
  congr 1
  field_simp

omit [Nontrivial E] in
/-- **The mean-value property on balls.** If `u` is harmonic on a neighbourhood of the closed
ball `closedBall x₀ R`, then the integral of `u` over the open ball of radius `R` about `x₀` is
the measure of the ball times `u x₀`. (For `R ≤ 0` the ball is empty and both sides vanish.) -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.setIntegral_ball_eq {x₀ : E}
    (hu : HarmonicOnNhd u (closedBall x₀ R)) :
    ∫ x in ball x₀ R, u x ∂μ = μ.real (ball x₀ R) • u x₀ := by
  rcases le_or_gt R 0 with hR | hR
  · simp [ball_eq_empty.mpr hR]
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- In the trivial space `u` is constant, with value `u x₀`.
    rw [setIntegral_congr_fun measurableSet_ball (g := fun _ ↦ u x₀)
      fun x _ ↦ congrArg u (Subsingleton.elim x x₀), setIntegral_const]
  have h := setIntegral_ball_eq_of_harmonicOnNhd_zero (μ := μ)
    ((harmonicOnNhd_comp_add_right_closedBall_zero_iff x₀ R).mpr hu) hR
  rw [zero_add] at h
  rw [Measure.addHaar_real_ball_center, ← h, ← integral_indicator measurableSet_ball,
    ← integral_indicator measurableSet_ball, ← integral_add_right_eq_self _ x₀]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  beta_reduce
  classical
  rw [indicator_apply, indicator_apply]
  simp only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero]

omit [Nontrivial E] in
/-- **The mean-value property on balls, average form.** A function harmonic on a neighbourhood
of the closed ball `closedBall x₀ R`, `0 < R`, has value `u x₀` at the centre equal to its average
over the open ball of radius `R` about `x₀`. -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.setAverage_ball_eq {x₀ : E}
    (hu : HarmonicOnNhd u (closedBall x₀ R)) (hR : 0 < R) :
    ⨍ x in ball x₀ R, u x ∂μ = u x₀ := by
  have hpos : 0 < μ.real (ball x₀ R) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos μ x₀ hR).ne' measure_ball_lt_top.ne
  rw [setAverage_eq, hu.setIntegral_ball_eq, smul_smul,
    inv_mul_cancel₀ hpos.ne', one_smul]

end TauCeti
