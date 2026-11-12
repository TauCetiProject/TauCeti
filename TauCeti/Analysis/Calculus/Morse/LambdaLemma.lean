/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.SplitModel
import TauCeti.Dynamics.LambdaLemma

/-!
# The λ-lemma for the split hyperbolic flow

The split hyperbolic flow `φ t (x, y) = (e^{-t} x, e^t y)` (`TauCeti.splitQuadraticFlow`) is the
local model of a negative-gradient flow at a nondegenerate critical point: in a Morse chart, after
splitting the coordinates by the sign of the weights, an adapted pseudo-gradient with weights `±1`
reads as this flow. Linear flows with other rates are covered by the general statement. The stable
set of this flow is the contracting factor `y = 0` and its unstable set the expanding factor
`x = 0`.

This file specializes the λ-lemma for linear hyperbolic maps,
`TauCeti.exists_graph_tendstoUniformlyOn_iteratedFDeriv`, to this flow. Let `ψ` be a `C^n` disc,
`n ≥ 1`, through a point `ψ z₀ = (x₀, 0)` of the stable set, transverse to it in the sense that
the derivative of its expanding component at `z₀` is invertible. Then for every radius `R`, the
forward images `φ t (ψ (U))` of any piece of the disc around `z₀` eventually contain the graphs
`{(h t v, v) | ‖v‖ < R}` of maps `h t` on the ball of radius `R` of the unstable set, and the
maps `h t` tend to zero in `C^n` uniformly on that ball
(`TauCeti.exists_splitQuadraticFlow_graph_tendstoUniformlyOn_iteratedFDeriv`). Explicitly,
`h t v = e^{-t} g (e^{-t} v)` for the `C^n` map `g` whose graph is the disc near `(x₀, 0)`.

As a consequence every point of the unstable set is a limit of points of the forward images of the
disc at arbitrarily large times
(`TauCeti.toLp_zero_mem_closure_iUnion_splitQuadraticFlow_image`): the unstable set lies in the
closure of the forward orbit of any disc crossing the stable set transversally. The `C⁰` passage
of transverse discs through the box around the origin is
`TauCeti.tendsto_splitPassage_toLp_smul`.

## Main results

* `TauCeti.exists_splitQuadraticFlow_graph_tendstoUniformlyOn_iteratedFDeriv`: **the λ-lemma** for
  the split hyperbolic flow.
* `TauCeti.toLp_zero_mem_closure_iUnion_splitQuadraticFlow_image`: the unstable set lies in the
  closure of the forward images of a transverse disc.

## References

* J. Palis and W. de Melo, *Geometric Theory of Dynamical Systems*, Springer, 1982, Chapter 2,
  §7 (the λ-lemma).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2 (pseudo-gradients that are linear near the critical points).
-/

public section

open Filter Metric Set Topology
open scoped ContDiff

namespace TauCeti

variable {F Eₛ Eᵤ : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup Eₛ] [NormedSpace ℝ Eₛ] [NormedAddCommGroup Eᵤ] [NormedSpace ℝ Eᵤ]
  {n : ℕ∞ω} {z₀ : F} {ψ : F → WithLp 2 (Eₛ × Eᵤ)} {ψ' : F →L[ℝ] WithLp 2 (Eₛ × Eᵤ)} {U : Set F}

/-- The norm of the contraction `e^{-t} • id` tends to zero as `t → ∞`. -/
private theorem tendsto_norm_exp_neg_smul_id (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Tendsto (fun t : ℝ ↦ ‖Real.exp (-t) • ContinuousLinearMap.id ℝ E‖) atTop (𝓝 0) := by
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun t ↦ ?_)
    (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)
  refine (norm_smul_le (Real.exp (-t)) (ContinuousLinearMap.id ℝ E)).trans ?_
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Function.comp_apply]
  exact mul_le_of_le_one_right (Real.exp_pos _).le ContinuousLinearMap.norm_id_le

/-- The expansion `e^t • id` as a continuous linear automorphism, with inverse `e^{-t} • id`. -/
private noncomputable def expSMul (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℝ) :
    E ≃L[ℝ] E :=
  .equivOfInverse (Real.exp t • ContinuousLinearMap.id ℝ E)
    (Real.exp (-t) • ContinuousLinearMap.id ℝ E)
    (fun v ↦ by simp [smul_smul, ← Real.exp_add]) (fun v ↦ by simp [smul_smul, ← Real.exp_add])

private theorem expSMul_apply (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℝ)
    (v : E) : expSMul E t v = Real.exp t • v := by
  simp [expSMul]

private theorem coe_expSMul_symm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℝ) :
    ((expSMul E t).symm : E →L[ℝ] E) = Real.exp (-t) • ContinuousLinearMap.id ℝ E := by
  simp [expSMul]

/-- **The λ-lemma for the split hyperbolic flow.** Let `ψ` be a `C^n` disc, `n ≥ 1`, through a
point `ψ z₀` of the stable set `y = 0`, transverse to it: the derivative of its expanding
component at `z₀` is invertible. Fix a neighbourhood `U` of `z₀` and a radius `R`. Then there is
a `C^n` map `g` from the expanding factor to the contracting one, with `g 0` the contracting
component of `ψ z₀`, such that

* for all large `t`, the image under the flow at time `t` of the part of the disc over `U`
  contains the graph `{(e^{-t} g (e^{-t} v), v) | ‖v‖ < R}`;
* the maps `v ↦ e^{-t} g (e^{-t} v)` tend to zero in `C^n` uniformly on the ball of radius `R`:
  their derivatives of each order `i ≤ n` tend to zero uniformly as `t → ∞`.

So the forward images of the disc contain discs converging in `C^n` to the ball of radius `R` of
the unstable set `x = 0`. -/
theorem exists_splitQuadraticFlow_graph_tendstoUniformlyOn_iteratedFDeriv
    (hψ : ContDiffAt ℝ n ψ z₀) (hψ' : HasFDerivAt ψ ψ' z₀)
    (hψ'i : (WithLp.sndL 2 ℝ Eₛ Eᵤ ∘L ψ').IsInvertible) (hψ₀ : (ψ z₀).snd = 0) (hn : n ≠ 0)
    (hU : U ∈ 𝓝 z₀) (R : ℝ) :
    ∃ g : Eᵤ → Eₛ, ContDiffAt ℝ n g 0 ∧ g 0 = (ψ z₀).fst ∧
      (∀ᶠ t in atTop, ∀ v ∈ ball (0 : Eᵤ) R, ∃ z ∈ U,
        splitQuadraticFlow t (ψ z) = WithLp.toLp 2 (Real.exp (-t) • g (Real.exp (-t) • v), v)) ∧
      ∀ i : ℕ, i ≤ n → TendstoUniformlyOn
        (fun t v ↦ iteratedFDeriv ℝ i (fun v ↦ Real.exp (-t) • g (Real.exp (-t) • v)) v) 0 atTop
        (ball 0 R) := by
  have hT : Tendsto (fun t ↦ ‖((expSMul Eᵤ t).symm : Eᵤ →L[ℝ] Eᵤ)‖) atTop (𝓝 0) := by
    simpa only [coe_expSMul_symm] using tendsto_norm_exp_neg_smul_id Eᵤ
  obtain ⟨g, hg, hg₀, himage, hconv⟩ := exists_graph_tendstoUniformlyOn_iteratedFDeriv
    (tendsto_norm_exp_neg_smul_id Eₛ) hT
    ((WithLp.fstL 2 ℝ Eₛ Eᵤ).contDiff.contDiffAt.comp z₀ hψ)
    ((WithLp.sndL 2 ℝ Eₛ Eᵤ).contDiff.contDiffAt.comp z₀ hψ)
    ((WithLp.sndL 2 ℝ Eₛ Eᵤ).hasFDerivAt.comp z₀ hψ') hψ'i (by simpa using hψ₀) hn hU R
  -- The graph transform of `S t × T t` is the rescaling `v ↦ e^{-t} g (e^{-t} v)`.
  have htransform : ∀ t : ℝ, (fun v ↦ (Real.exp (-t) • ContinuousLinearMap.id ℝ Eₛ)
      (g ((expSMul Eᵤ t).symm v))) = fun v ↦ Real.exp (-t) • g (Real.exp (-t) • v) := by
    intro t
    funext v
    rw [← ContinuousLinearEquiv.coe_coe, coe_expSMul_symm]
    simp
  refine ⟨g, hg, by simpa using hg₀, ?_, fun i hi ↦ ?_⟩
  · filter_upwards [himage] with t ht v hv
    obtain ⟨z, hzU, hfst, hsnd⟩ := ht v hv
    have h₁ : Real.exp (-t) • (ψ z).fst = Real.exp (-t) • g (Real.exp (-t) • v) := by
      simpa [← congr_fun (htransform t) v] using hfst
    have h₂ : Real.exp t • (ψ z).snd = v := by simpa [expSMul_apply] using hsnd
    exact ⟨z, hzU, by rw [splitQuadraticFlow_apply, h₁, h₂]⟩
  · simpa only [htransform] using hconv i hi

/-- **The unstable set lies in the closure of the forward images of a transverse disc.** Let `ψ`
be a `C^n` disc, `n ≥ 1`, through a point `ψ z₀` of the stable set `y = 0`, with the derivative
at `z₀` of its expanding component invertible. Then every point `(0, v)` of the unstable set is a
limit of points of the images of the part of the disc over any neighbourhood `U` of `z₀` under the
flow at times `t ≥ T₀`, for every `T₀`. -/
theorem toLp_zero_mem_closure_iUnion_splitQuadraticFlow_image
    (hψ : ContDiffAt ℝ n ψ z₀) (hψ' : HasFDerivAt ψ ψ' z₀)
    (hψ'i : (WithLp.sndL 2 ℝ Eₛ Eᵤ ∘L ψ').IsInvertible) (hψ₀ : (ψ z₀).snd = 0) (hn : n ≠ 0)
    (hU : U ∈ 𝓝 z₀) (v : Eᵤ) (T₀ : ℝ) :
    WithLp.toLp 2 ((0 : Eₛ), v) ∈ closure (⋃ t ≥ T₀, splitQuadraticFlow t '' (ψ '' U)) := by
  obtain ⟨g, -, -, himage, hconv⟩ :=
    exists_splitQuadraticFlow_graph_tendstoUniformlyOn_iteratedFDeriv hψ hψ' hψ'i hψ₀ hn hU
      (‖v‖ + 1)
  have hv : v ∈ ball (0 : Eᵤ) (‖v‖ + 1) := by simp
  -- The values of the graph maps at `v` tend to zero.
  have hlim : Tendsto (fun t ↦ Real.exp (-t) • g (Real.exp (-t) • v)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h0 := (hconv 0 (by simp)).tendsto_at hv
    rw [Pi.zero_apply, tendsto_zero_iff_norm_tendsto_zero] at h0
    simpa only [norm_iteratedFDeriv_zero] using h0
  refine mem_closure_of_tendsto
    ((WithLp.prod_continuous_toLp 2 Eₛ Eᵤ).continuousAt.tendsto.comp
      (hlim.prodMk_nhds tendsto_const_nhds)) ?_
  filter_upwards [himage, eventually_ge_atTop T₀] with t ht htT₀
  obtain ⟨z, hzU, hz⟩ := ht v hv
  exact mem_iUnion₂.2 ⟨t, htT₀, ψ z, mem_image_of_mem ψ hzU, hz⟩

end TauCeti
