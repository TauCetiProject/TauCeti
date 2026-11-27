/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MellinTransform.TruncatedInversion
public import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.BoundedVariation
import TauCeti.Analysis.Fourier.DirichletJordan
import TauCeti.Analysis.MellinTransform.Basic
import TauCeti.Topology.EMetricSpace.BoundedVariation

/-!
# Dirichlet–Jordan pointwise Mellin inversion

At a positive point where a Mellin-integrable function has bounded variation on a neighbourhood,
the symmetric truncations of its inverse Mellin integral converge to the mean of its one-sided
limits. The change of variables `u = -log x` reverses the side of each limit, and the damping
factor cancels against the real part of the inverse Mellin weight.

## References

* E. C. Titchmarsh, *The Theory of the Riemann Zeta-function*, Chapter III, for truncated
  inversion in the Perron setting.
* `TauCeti.intervalIntegral_cpow_smul_mellin_eq` supplies the finite-height change of variables.
-/

public section

open Complex Filter MeasureTheory Real Set Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem boundedVariationOn_exp_neg_smul_of_mapsTo {f : ℝ → E} {s : Set ℝ}
    (hf : BoundedVariationOn f s) (σ : ℝ) {a b : ℝ}
    (hmap : MapsTo (fun u : ℝ ↦ Real.exp (-u)) (Icc a b) s) :
    BoundedVariationOn (fun u : ℝ ↦ Real.exp (-σ * u) • f (Real.exp (-u))) (Icc a b) := by
  have hanti : StrictAnti (fun u : ℝ ↦ Real.exp (-u)) :=
    fun _ _ h ↦ Real.exp_lt_exp.mpr (neg_lt_neg h)
  have hcomp : BoundedVariationOn (f ∘ fun u : ℝ ↦ Real.exp (-u)) (Icc a b) :=
    ((eVariationOn.comp_le_of_antitoneOn f _ (hanti.antitone.antitoneOn _) hmap).trans_lt
      hf.lt_top).ne
  have hd : ContDiffOn ℝ 1 (fun u : ℝ ↦ Real.exp (-σ * u)) (Icc a b) := by fun_prop
  obtain ⟨K, hK⟩ := hd.exists_lipschitzOnWith one_ne_zero (convex_Icc a b) isCompact_Icc
  exact (hK.comp_boundedVariationOn (mapsTo_id _) (BoundedVariationOn.id_Icc a b)).smul hcomp

private theorem tendsto_exp_neg_at_left_right {x : ℝ} (hx : 0 < x) :
    Tendsto (fun u : ℝ ↦ Real.exp (-u)) (𝓝[<] (-Real.log x)) (𝓝[>] x) ∧
      Tendsto (fun u : ℝ ↦ Real.exp (-u)) (𝓝[>] (-Real.log x)) (𝓝[<] x) := by
  have hval : Real.exp (- -Real.log x) = x := by simp [Real.exp_log hx]
  have hc : Continuous (fun u : ℝ ↦ Real.exp (-u)) := by fun_prop
  have hl : StrictAnti (fun u : ℝ ↦ Real.exp (-u)) := fun _ _ h ↦ Real.exp_lt_exp.mpr (neg_lt_neg h)
  refine ⟨tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩, tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩⟩
  · simpa only [neg_neg, Real.exp_log hx] using (hc.tendsto (-Real.log x)).mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact hval ▸ hl (show u < -Real.log x from hu)
  · simpa only [neg_neg, Real.exp_log hx] using (hc.tendsto (-Real.log x)).mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact hval ▸ hl (show -Real.log x < u from hu)

private theorem exp_smul_oneSidedLimits {f : ℝ → E} {s : Set ℝ}
    (hf : BoundedVariationOn f s) (σ : ℝ) {x : ℝ} (hx : 0 < x) (hxs : x ∈ interior s) :
    let g := fun u : ℝ ↦ Real.exp (-σ * u) • f (Real.exp (-u))
    g.leftLim (-Real.log x) = Real.exp (σ * Real.log x) • f.rightLim x ∧
      g.rightLim (-Real.log x) = Real.exp (σ * Real.log x) • f.leftLim x := by
  have hc : Continuous (fun u : ℝ ↦ Real.exp (-σ * u)) := by fun_prop
  obtain ⟨hl, hr⟩ := tendsto_exp_neg_at_left_right hx
  refine ⟨leftLim_eq_of_tendsto ?_, rightLim_eq_of_tendsto ?_⟩
  · simpa only [Function.comp_apply, neg_mul, mul_neg, neg_neg] using
      hc.continuousWithinAt.tendsto.smul ((hf.tendsto_rightLim_of_mem_interior hxs).comp hl)
  · simpa only [Function.comp_apply, neg_mul, mul_neg, neg_neg] using
      hc.continuousWithinAt.tendsto.smul ((hf.tendsto_leftLim_of_mem_interior hxs).comp hr)

/-- **Pointwise Mellin inversion at a jump.** If `mellin f` converges absolutely on the line
`Re s = σ` and `f` has bounded variation near `x > 0`, the symmetric truncations of the
inverse integral converge to the mean of the two one-sided limits of `f` at `x`. -/
theorem tendsto_truncated_mellinInv (σ : ℝ) {f : ℝ → E} (hf : MellinConvergent f σ)
    {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    (hvar : BoundedVariationOn f (Icc (x - δ) (x + δ))) :
    Tendsto (fun T : ℝ ↦ (1 / (2 * π)) •
      ∫ y in -T..T, (x : ℂ) ^ (-(σ + y * I)) • mellin f (σ + y * I)) atTop
      (𝓝 ((1 / 2 : ℝ) • (f.leftLim x + f.rightLim x))) := by
  let u₀ := -Real.log x
  let g := fun u : ℝ ↦ Real.exp (-σ * u) • f (Real.exp (-u))
  have hgi : Integrable g := by
    simpa only [g, ← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
      Complex.coe_smul] using (mellinConvergent_iff_integrable_exp_smul f σ).mp hf
  have hexp : Continuous (fun u : ℝ ↦ Real.exp (-u)) := by fun_prop
  have hxs : x ∈ interior (Icc (x - δ) (x + δ)) := by
    rw [interior_Icc]
    exact ⟨by linarith, by linarith⟩
  have hs : (fun u : ℝ ↦ Real.exp (-u)) ⁻¹' Icc (x - δ) (x + δ) ∈ 𝓝 u₀ :=
    hexp.continuousAt.preimage_mem_nhds (by simpa [u₀, Real.exp_log hx] using
      (mem_interior_iff_mem_nhds.mp hxs))
  obtain ⟨R, hR, hmap⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hs
  rw [Real.closedBall_eq_Icc] at hmap
  have hgvar : BoundedVariationOn g (Icc (u₀ - R) (u₀ + R)) :=
    boundedVariationOn_exp_neg_smul_of_mapsTo hvar σ hmap
  have hfourier := (hgi.tendsto_intervalIntegral_fourierInv_of_boundedVariationOn hR hgvar)
    |>.comp (tendsto_id.atTop_div_const (by positivity : 0 < 2 * π))
  have h := hfourier.const_smul ((x : ℂ) ^ (-σ : ℂ))
  obtain ⟨hl, hr⟩ := exp_smul_oneSidedLimits hvar σ hx hxs
  have hpow : (x : ℂ) ^ (-σ : ℂ) * (Real.exp (σ * Real.log x) : ℂ) = 1 := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le,
      Complex.ofReal_exp, ← Complex.exp_add]
    push_cast
    ring_nf
    exact Complex.exp_zero
  rw [hl, hr, ← smul_add, add_comm (f.rightLim x), smul_comm (1 / 2 : ℝ),
    ← Complex.coe_smul (Real.exp (σ * Real.log x)), ← mul_smul, hpow, one_smul] at h
  exact h.congr fun T ↦ (intervalIntegral_cpow_smul_mellin_eq f σ hx T).symm

end TauCeti
