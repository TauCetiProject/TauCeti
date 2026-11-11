/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.Convolution
public import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Smooth approximation with uniform control of derivatives

A compactly supported `C^N` function can be approximated by compactly supported smooth
functions, uniformly in every derivative of order at most `N`. The supports of all the
approximants lie in one compact subset of any prescribed open neighborhood of the original
support. On a compact subset of an open domain the same conclusion holds for `C^N` data
without a global support assumption.

In particular, for `N = 2` this supplies smooth approximations of a twice continuously
differentiable function with simultaneous control of its value, gradient and Hessian on a
localized state region. No third derivative of the original function is required.

The construction combines normalized-bump uniform approximation with
`HasCompactSupport.iteratedFDeriv_convolution_right` and the compactly supported extension
`ContDiffOn.exists_contDiff_eventuallyEq_on_isCompact`.

## References

* L. C. Evans, *Partial Differential Equations*, Appendix C.4 (mollifiers).
-/

public section

noncomputable section

open ContinuousLinearMap MeasureTheory Filter Metric Set
open scoped Convolution Topology Pointwise ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : E → F} {N : ℕ∞}

section Measure

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Shrinking normalized-bump mollifications of compactly supported `C^N` data converge
uniformly in each derivative of order at most `N`. -/
theorem HasCompactSupport.tendstoUniformly_iteratedFDeriv_normed_convolution
    (hfc : HasCompactSupport f) (hf : ContDiff ℝ N f)
    {ι : Type*} {l : Filter ι} {ρ : ι → ContDiffBump (0 : E)}
    (hρ : Tendsto (fun i ↦ (ρ i).rOut) l (𝓝 0)) {k : ℕ} (hk : k ≤ N) :
    TendstoUniformly (fun i ↦ iteratedFDeriv ℝ k ((ρ i).normed μ ⋆[lsmul ℝ ℝ, μ] f))
      (iteratedFDeriv ℝ k f) l := by
  simp_rw [hfc.iteratedFDeriv_normed_convolution hf _ hk]
  exact ContDiffBump.tendstoUniformly_normed_convolution hρ
    ((hfc.iteratedFDeriv k).uniformContinuous_of_continuous
      (hf.continuous_iteratedFDeriv (by exact_mod_cast hk)))

end Measure

/-- Compactly supported `C^N` data admit smooth approximants converging uniformly in all
available derivatives, with a common compact support inside any prescribed open neighborhood
of their support. -/
theorem ContDiff.exists_contDiff_hasCompactSupport_tendstoUniformly_iteratedFDeriv
    (hf : ContDiff ℝ N f) (hfc : HasCompactSupport f) {U : Set E}
    (hU : IsOpen U) (hfU : tsupport f ⊆ U) :
    ∃ (g : ℕ → E → F) (K : Set E), IsCompact K ∧ K ⊆ U ∧
      (∀ n, ContDiff ℝ ∞ (g n) ∧ tsupport (g n) ⊆ K) ∧
      ∀ k : ℕ, k ≤ N → TendstoUniformly (fun n ↦ iteratedFDeriv ℝ k (g n))
        (iteratedFDeriv ℝ k f) atTop := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let μ : Measure E := Measure.addHaar
  obtain ⟨δ, hδ, hδU⟩ := hfc.isCompact.exists_cthickening_subset_open hU hfU
  let ρ : ℕ → ContDiffBump (0 : E) := ContDiffBump.shrinking hδ
  let K := closedBall (0 : E) δ + tsupport f
  have hKU : K ⊆ U := by
    simpa only [K, hfc.isCompact.closedBall_add hδ.le, zero_vadd] using hδU
  refine ⟨fun n ↦ (ρ n).normed μ ⋆[lsmul ℝ ℝ, μ] f, K,
    (isCompact_closedBall _ _).add hfc.isCompact, hKU, ?_, ?_⟩
  · intro n
    refine ⟨(ρ n).hasCompactSupport_normed.contDiff_convolution_left _
      (ρ n).contDiff_normed hf.continuous.locallyIntegrable, ?_⟩
    have hρδ : (ρ n).rOut ≤ δ := by
      simpa only [ρ, ContDiffBump.rOut_shrinking] using
        (div_le_self hδ.le (by simp : (1 : ℝ) ≤ n + 1))
    exact (ρ n).tsupport_normed_convolution_subset.trans
      (add_subset_add (closedBall_subset_closedBall hρδ) Subset.rfl)
  · intro k hk
    exact hfc.tendstoUniformly_iteratedFDeriv_normed_convolution hf
      (ContDiffBump.tendsto_rOut_shrinking hδ) hk

/-- On a compact subset of an open domain, `C^N` data have smooth approximants converging
uniformly in every derivative through order `N`. All approximants have support in one compact
subset of the domain. The derivatives of the datum are ordinary, not within derivatives,
since the datum is `C^N` on an open neighborhood. -/
theorem ContDiffOn.exists_contDiff_hasCompactSupport_tendstoUniformlyOn_iteratedFDeriv
    {U K : Set E} (hf : ContDiffOn ℝ N f U) (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) :
    ∃ (g : ℕ → E → F) (L : Set E), IsCompact L ∧ L ⊆ U ∧
      (∀ n, ContDiff ℝ ∞ (g n) ∧ tsupport (g n) ⊆ L) ∧
      ∀ k : ℕ, k ≤ N → TendstoUniformlyOn (fun n ↦ iteratedFDeriv ℝ k (g n))
        (iteratedFDeriv ℝ k f) atTop K := by
  obtain ⟨f₀, hf₀, hfc, hfU, -, heq⟩ :=
    hf.exists_contDiff_eventuallyEq_on_isCompact hK hU hKU
  obtain ⟨g, L, hL, hLU, hg, hlim⟩ :=
    hf₀.exists_contDiff_hasCompactSupport_tendstoUniformly_iteratedFDeriv hfc hU hfU
  refine ⟨g, L, hL, hLU, hg, fun k hk ↦ ?_⟩
  exact (hlim k hk).tendstoUniformlyOn.congr_right fun x hx ↦
    ((heq x hx).iteratedFDeriv ℝ k).eq_of_nhds
