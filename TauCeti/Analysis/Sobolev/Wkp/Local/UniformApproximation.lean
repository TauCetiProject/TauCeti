/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Approximation
public import TauCeti.Analysis.Sobolev.Wkp.Mollification
public import TauCeti.Analysis.Calculus.IteratedGradient

/-!
# Mollifiers of continuous Sobolev functions

Let `u ∈ W^{k+1,p}(Ω)`, `1 ≤ p < ∞`, have a representative `v` that is continuous on `Ω`, and let
`K ⊆ Ω` be compact. Mollifying the zero extension of `v` gives smooth functions `wⱼ` on the whole
space which converge to `v` uniformly on `K`, and whose classical derivatives of order `k + 1`
converge in `Lᵖ(K)` to the highest weak derivative of `u`
(`TauCeti.Wkp.exists_contDiff_tendstoUniformlyOn_tendsto_eLpNorm_iteratedGradientChain_sub`).

Approximation in the Sobolev norm alone does not control the values of the approximants at
individual points, and approximation by an arbitrary sequence of smooth functions need not
converge uniformly. Both modes of convergence are needed to pass a pointwise estimate proved for
classical solutions, such as a maximum principle, to strong solutions: the uniform convergence
transfers the values and boundary values of the solution, and the `Lᵖ` convergence transfers the
equation.

The derivative identity behind the `Lᵖ` convergence is
`TauCeti.Wkp.iteratedGradientChain_normed_convolution_indicator_value`: wherever the support of
the bump stays inside `Ω`, the classical derivatives of the mollified value are the mollified
weak derivatives.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Appendix C.4 and §5.3.1.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open Filter Metric MeasureTheory Set TopologicalSpace
open scoped Convolution ContDiff ENNReal Gradient Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

local instance : (mu.restrict (univ : Set E)).IsAddHaarMeasure := by
  rw [Measure.restrict_univ]
  infer_instance

/-- **Derivatives of a mollified Sobolev function.** Let `u ∈ W^{k+1,p}(Ω)` and let `φ` be a smooth
bump whose closed support ball, centred at any point of the open set `U`, lies in `Ω`. On `U`, the
classical iterated-gradient field of order `k` of the mollified zero extension of the value of `u`
is the mollified zero extension of the highest weak derivative of `u`. -/
theorem iteratedGradientChain_normed_convolution_indicator_value (phi : ContDiffBump (0 : E))
    {U : Set E} (hU : IsOpen U) (hphi : ∀ x ∈ U, closedBall x phi.rOut ⊆ Omega) :
    ∀ (k : ℕ) (u : Wkp mu Omega p (k + 1)) (x : E), x ∈ U →
      iteratedGradientChain
          (phi.normed mu ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu]
            (Omega : Set E).indicator (value (k + 1) u : E → ℝ)) k x =
        (phi.normed mu ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu]
          (Omega : Set E).indicator (iteratedGradient k u : E → IteratedGradient E k)) x := by
  intro k
  induction k with
  | zero =>
      intro u x hx
      rw [iteratedGradientChain_zero]
      apply (InnerProductSpace.toDual ℝ E).injective
      rw [toDual_gradient]
      have hd := (hasFDerivAt_indicator_convolution_normed_value u phi x (hphi x hx)).fderiv
      rw [convolution_flip, convolution_flip] at hd
      rw [hd]
      have hmem := (memLp_indicator_iff_restrict Omega.isOpen.measurableSet.nullMeasurableSet).2
        (Lp.memLp (iteratedGradient 0 u))
      have hi := (phi.hasCompactSupport_normed (μ := mu)).convolutionExists_left
        (ContinuousLinearMap.lsmul ℝ ℝ) phi.continuous_normed
        (hmem.locallyIntegrable Fact.out) x
      -- Passing the Riesz map through the integral identifies the vector convolution's dual.
      symm
      rw [convolution_def]
      refine ((InnerProductSpace.toDual ℝ E).toLinearIsometry.toContinuousLinearMap
        |>.integral_comp_comm hi).symm.trans ?_
      apply integral_congr_ae
      filter_upwards with y
      by_cases hy : x - y ∈ Omega <;> simp [hy, ContinuousLinearMap.lsmul_apply]
  | succ k ih =>
      intro u x hx
      rw [iteratedGradientChain_succ]
      have heq : iteratedGradientChain
          (phi.normed mu ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu]
            (Omega : Set E).indicator (value (k + 1 + 1) u : E → ℝ)) k =ᶠ[𝓝 x]
          phi.normed mu ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu]
            (Omega : Set E).indicator
              (iteratedGradient k (lowerOrder (k + 1) u) : E → IteratedGradient E k) := by
        filter_upwards [hU.mem_nhds hx] with y hy
        simpa only [value_succ (k + 1) u] using ih (lowerOrder (k + 1) u) y hy
      rw [heq.fderiv_eq]
      simpa only [convolution_flip] using
        (hasFDerivAt_indicator_convolution_normed_iteratedGradient k u phi x (hphi x hx)).fderiv

/-- **Mollifiers of a continuous Sobolev function.** Let `1 ≤ p < ∞`, let `u ∈ W^{k+1,p}(Ω)` agree
almost everywhere on `Ω` with a function `v` continuous on `Ω`, and let `K ⊆ Ω` be compact. There
are smooth functions `wⱼ` converging to `v` uniformly on `K`, whose classical iterated-gradient
fields of order `k` converge in `Lᵖ(K)` to the highest weak derivative of `u`. -/
theorem exists_contDiff_tendstoUniformlyOn_tendsto_eLpNorm_iteratedGradientChain_sub
    (hp : p ≠ ⊤) (k : ℕ) (u : Wkp mu Omega p (k + 1)) {v : E → ℝ} (hv : ContinuousOn v Omega)
    (huv : (value (k + 1) u : E → ℝ) =ᵐ[mu.restrict Omega] v) {K : Set E} (hK : IsCompact K)
    (hKΩ : K ⊆ Omega) :
    ∃ w : ℕ → E → ℝ, (∀ j, ContDiff ℝ ∞ (w j)) ∧ TendstoUniformlyOn w v atTop K ∧
      Tendsto (fun j => eLpNorm (fun x => iteratedGradientChain (w j) k x - iteratedGradient k u x)
        p (mu.restrict K)) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open Omega.isOpen hKΩ
  -- Bumps of outer radius `δ / (2 (j + 1))`, mollifying on the `δ / 2`-neighbourhood `U` of `K`.
  let phi : ℕ → ContDiffBump (0 : E) := fun j =>
    ⟨δ / (2 * ((j : ℝ) + 1)) / 2, δ / (2 * ((j : ℝ) + 1)), by positivity,
      half_lt_self (by positivity)⟩
  have hphi : Tendsto (fun j => (phi j).rOut) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := δ / 2)).mul tendsto_one_div_add_atTop_nhds_zero_nat
    rw [mul_zero] at h
    refine h.congr fun j => ?_
    simp only [phi]
    field_simp
  have hphi_le (j : ℕ) : (phi j).rOut ≤ δ / 2 := by
    simp only [phi]
    rw [div_le_div_iff_of_pos_left hδ (by positivity) two_pos]
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  let U : Opens E := ⟨thickening (δ / 2) K, isOpen_thickening⟩
  have hKU : K ⊆ U := self_subset_thickening (by positivity) K
  have hball (j : ℕ) (x : E) (hx : x ∈ U) : closedBall x (phi j).rOut ⊆ cthickening δ K := by
    obtain ⟨z, hz, hxz⟩ := mem_thickening_iff.1 hx
    refine (closedBall_subset_closedBall' ?_).trans (closedBall_subset_cthickening hz δ)
    linarith [hphi_le j]
  have hUΩ : U ≤ Omega := fun x hx =>
    hδΩ (hball 0 x hx (mem_closedBall_self (phi 0).rOut_pos.le))
  -- The mollifiers of `v` are those of the value of `u`.
  have hf : (Omega : Set E).indicator v =ᵐ[mu]
      (Omega : Set E).indicator (value (k + 1) u : E → ℝ) :=
    ((ae_eq_restrict_iff_indicator_ae_eq Omega.isOpen.measurableSet).1 huv).symm
  have hloc : LocallyIntegrable ((Omega : Set E).indicator (value (k + 1) u : E → ℝ)) mu :=
    ((memLp_indicator_iff_restrict Omega.isOpen.measurableSet.nullMeasurableSet).2
      (Lp.memLp _)).locallyIntegrable Fact.out
  let w : ℕ → E → ℝ := fun j =>
    (phi j).normed mu ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu] (Omega : Set E).indicator v
  have hw (j : ℕ) : w j = (phi j).normed mu ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu]
      (Omega : Set E).indicator (value (k + 1) u : E → ℝ) :=
    convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) (EventuallyEq.refl _ _) hf
  refine ⟨w, fun j => ?_, ?_, ?_⟩
  · rw [hw]
    exact (phi j).hasCompactSupport_normed.contDiff_convolution_left _ (phi j).contDiff_normed
      hloc
  · -- `v` is uniformly continuous on the compact neighbourhood `cthickening δ K` of `K`.
    have hC := hK.cthickening (r := δ)
    have hvC := hC.uniformContinuousOn_of_continuous (hv.mono hδΩ)
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨η, hη, hvη⟩ := Metric.uniformContinuousOn_iff.1 hvC (ε / 2) (half_pos hε)
    filter_upwards [hphi.eventually (gt_mem_nhds hη)] with j hj x hx
    have hxC : x ∈ cthickening δ K := self_subset_cthickening K hx
    have hd := (phi j).dist_normed_convolution_le (x₀ := x) (ε := ε / 2)
      (hloc.aestronglyMeasurable.congr hf.symm) fun y hy => by
        have hyC : y ∈ cthickening δ K := hball j x (hKU hx) (ball_subset_closedBall hy)
        rw [indicator_of_mem (hδΩ hyC), indicator_of_mem (hδΩ hxC)]
        exact (hvη y hyC x hxC ((mem_ball.1 hy).trans hj)).le
    rw [indicator_of_mem (hKΩ hx)] at hd
    rw [dist_comm]
    exact hd.trans_lt (half_lt_self hε)
  · have h := Wkp.tendsto_mollified_iteratedGradient hp hUΩ hphi k u
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
      fun j => (eLpNorm_mono_measure _ (Measure.restrict_mono hKU le_rfl)).trans
        (eLpNorm_congr_ae ?_).le
    have he := (normedBumpLp_extendByZero_ae_eq_convolution hp (phi j)
      Omega.isOpen.measurableSet (iteratedGradient k u)).filter_mono
        (ae_mono (Measure.restrict_mono_set mu (subset_univ (U : Set E))))
    simp only [Measure.restrict_univ] at he
    filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul (p := p) (E := IteratedGradient E k) _ _ _, he,
      iteratedGradient_restrictL_ae hUΩ k u, ae_restrict_mem U.isOpen.measurableSet]
      with x h₁ h₂ h₃ hx
    rw [Pi.sub_apply, h₁, h₂, h₃, hw,
      iteratedGradientChain_normed_convolution_indicator_value (phi j) U.isOpen
        (fun y hy => (hball j y hy).trans hδΩ) k u x hx]

end TauCeti.Wkp
