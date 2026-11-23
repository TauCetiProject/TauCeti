/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Poisson
public import Mathlib.Analysis.Fourier.AddCircle
import TauCeti.Analysis.Complex.Poisson.Basic
import TauCeti.MeasureTheory.Function.Lp.Integral.BoundedSmul
import TauCeti.MeasureTheory.Integral.Circle.Haar

/-!
# Poisson representation from radial convergence

If the radial dilations of a holomorphic function on a disk converge in `Lᵖ` for `1 ≤ p`
to measurable boundary data, the function is the Poisson integral of those data. We use
normalized Haar measure on the additive circle and allow any positive period.
-/

public section

open Complex Filter MeasureTheory Metric
open scoped ENNReal Topology

/-- The Poisson representation of a holomorphic function from its radial `Lᵖ` boundary limit.
The radial parameter `r` is measured relative to the disk radius `R` and tends to `1` from below. -/
theorem DifferentiableOn.integral_poissonKernel_smul_eq_of_tendsto_eLpNorm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {T : ℝ} [Fact (0 < T)] {c w : ℂ} {R : ℝ} {p : ℝ≥0∞} {f : ℂ → E} {g : AddCircle T → E}
    (hf : DifferentiableOn ℂ f (ball c R)) (hp : 1 ≤ p)
    (hlim : Tendsto (fun r : ℝ ↦ eLpNorm
      (fun t : AddCircle T ↦ f (c + r * (R * (AddCircle.toCircle t : ℂ))) - g t) p
      AddCircle.haarAddCircle) (𝓝[<] 1) (𝓝 0)) (hw : w ∈ ball c R) :
    (∫ t : AddCircle T, poissonKernel c w (R * (AddCircle.toCircle t : ℂ) + c) • g t
      ∂AddCircle.haarAddCircle) = f w := by
  have hR := pos_of_mem_ball hw
  let φ (r : ℝ) (t : AddCircle T) := f (c + r * (R * (AddCircle.toCircle t : ℂ)))
  let k : C(AddCircle T, ℝ) :=
    ⟨fun t ↦ poissonKernel c w (R * (AddCircle.toCircle t : ℂ) + c), by
      apply (TauCeti.continuousOn_poissonKernel (s := sphere c R)
        (Set.disjoint_right.mp sphere_disjoint_ball hw)).comp_continuous (by fun_prop)
      intro t
      simp [mem_sphere_iff_norm, abs_of_pos hR]⟩
  have hnear : ∀ᶠ r : ℝ in 𝓝[<] 1, |r| < 1 := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1)] with r hr
    exact abs_lt.mpr hr
  have hφ : ∀ᶠ r in 𝓝[<] 1, MemLp (φ r) p AddCircle.haarAddCircle := by
    filter_upwards [hnear] with r hr
    have hc : Continuous (φ r) := by
      apply hf.continuousOn.comp_continuous (by fun_prop)
      intro t
      simpa [mem_ball_iff_norm, norm_mul, abs_of_pos hR] using mul_lt_of_lt_one_left hR hr
    exact (hc.memLp_top_of_hasCompactSupport (.of_compactSpace _) _).mono_exponent le_top
  have hg' : MemLp g p AddCircle.haarAddCircle := by
    have hfinite : ∀ᶠ r in 𝓝[<] 1, eLpNorm (φ r - g) p AddCircle.haarAddCircle < ∞ :=
      (tendsto_order.1 hlim).2 ∞ ENNReal.zero_lt_top
    obtain ⟨r, hr, hd⟩ := (hφ.and hfinite).exists
    simpa only [sub_sub_cancel] using hr.sub (memLp_iff.mpr hd)
  have hi := TauCeti.tendsto_integral_smul_of_tendsto_eLpNorm_sub
    (μ := AddCircle.haarAddCircle (T := T)) (W := Set.univ) (k := k) (φ := φ)
    (by simp) (norm_nonneg k) (by simpa using k.continuous.aestronglyMeasurable)
    (Eventually.of_forall fun t ↦ k.norm_coe_le_norm t) hp hφ hg' (by simp) (by simp) hlim
  have hpoint : Tendsto (fun r : ℝ ↦ f (c + r * (w - c))) (𝓝[<] 1) (𝓝 (f w)) := by
    have hc : Continuous (fun r : ℝ ↦ c + (r : ℂ) * (w - c)) := by fun_prop
    apply (hf.continuousOn.continuousAt (isOpen_ball.mem_nhds hw)).tendsto.comp
    simpa [add_sub_cancel] using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  apply tendsto_nhds_unique hi
  apply hpoint.congr'
  filter_upwards [hnear] with r hr
  have havg := hf.circleAverage_poissonKernel_smul_radial (r := (r : ℂ)) (by simpa using hr) hw
  rw [← AddCircle.integral_haarAddCircle_comp_toCircle (T := T) _ c R] at havg
  simpa only [k, ContinuousMap.coe_mk, φ, Pi.smul_apply', add_sub_cancel_right] using havg.symm
