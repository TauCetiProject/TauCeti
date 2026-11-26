/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Propagator
import TauCeti.MeasureTheory.Integral.DominatedConvergence

/-!
# Joint continuity of the propagator in the times and a parameter

Let `P : ℝ → Z → E →L[𝕜] E` be a family of coefficients on `[a, b]` depending on a parameter
`z` in a subset `U` of a first-countable topological space `Z`, for instance an open subset of
`ℂ`. Suppose that `P(·, z)` is almost everywhere strongly measurable on `[a, b]` for `z ∈ U`, that
`z ↦ P(t, z)` is continuous on `U` for almost every `t ∈ [a, b]`, and that for every compact
`K ⊆ U` the norms `‖P(t, z)‖`, `z ∈ K`, are bounded by one integrable function `m_K(t)`. Then the
propagator `(t, s, z) ↦ N_{P(·, z)}(t, s)` is continuous on `[a, b]² × U` in the operator norm.
This covers holomorphic families on an open subset of `ℂ`, which are in particular continuous in
`z`.

The coefficients `P(·, z)` converge to `P(·, z₀)` in `L¹([a, b])` as `z → z₀` by dominated
convergence along sequences (`TauCeti.tendsto_intervalIntegral_norm_sub_of_dominated`), so the
propagators converge uniformly on `[a, b]²` (`TauCeti.tendstoUniformlyOn_propagator`), and the
limit is continuous on `[a, b]²` (`TauCeti.continuousOn_propagator`).

## Main results

* `TauCeti.continuousOn_propagator_parameter`: joint continuity of `(t, s, z) ↦ N_{P(·, z)}(t, s)`
  on `[a, b]² × U`.

## References

* E. A. Coddington, N. Levinson, *Theory of Ordinary Differential Equations*, Chapter 1, §7.
-/

public section

open MeasureTheory Set Filter Topology

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [CompleteSpace E] {Z : Type*} [TopologicalSpace Z] [FirstCountableTopology Z]
  {P : ℝ → Z → E →L[𝕜] E} {U : Set Z} {a b : ℝ}

/-- **Joint continuity of the propagator in the times and a parameter.** Let `P(·, z)` be almost
everywhere strongly measurable on `[a, b]` for `z ∈ U`, with `z ↦ P(t, z)` continuous on `U` for
almost every `t ∈ [a, b]`, and suppose that for every compact `K ⊆ U` there is an integrable `m_K`
with `‖P(t, z)‖ ≤ m_K(t)` for `z ∈ K` and almost every `t ∈ [a, b]`. Then
`(t, s, z) ↦ N_{P(·, z)}(t, s)` is continuous on `[a, b]² × U` in the operator norm. -/
theorem continuousOn_propagator_parameter
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (fun t ↦ P t z) (volume.restrict (Icc a b)))
    (hcont : ∀ᵐ t, t ∈ Icc a b → ContinuousOn (P t) U)
    (hdom : ∀ K ⊆ U, IsCompact K → ∃ m : ℝ → ℝ, IntegrableOn m (Icc a b) ∧
      ∀ z ∈ K, ∀ᵐ t, t ∈ Icc a b → ‖P t z‖ ≤ m t) :
    ContinuousOn (fun q : (ℝ × ℝ) × Z ↦ propagator (fun t ↦ P t q.2) q.1.1 q.1.2)
      ((Icc a b ×ˢ Icc a b) ×ˢ U) := by
  rintro ⟨p₀, z₀⟩ ⟨hp₀, hz₀⟩
  have hab : a ≤ b := hp₀.1.1.trans hp₀.1.2
  -- Each `P(·, z)`, `z ∈ U`, is integrable: take `K = {z}`.
  have hP (z : Z) (hz : z ∈ U) : IntegrableOn (fun t ↦ P t z) (Icc a b) := by
    obtain ⟨m, hm, hbound⟩ := hdom {z} (singleton_subset_iff.2 hz) isCompact_singleton
    exact hm.mono' (hmeas z hz) ((ae_restrict_iff' measurableSet_Icc).2 (hbound z rfl))
  have hsnd : Tendsto Prod.snd (𝓝[(Icc a b ×ˢ Icc a b) ×ˢ U] (p₀, z₀)) (𝓝[U] z₀) :=
    (continuous_snd.tendsto _).inf (tendsto_principal_principal.2 fun _ hq ↦ hq.2)
  have hfst : Tendsto Prod.fst (𝓝[(Icc a b ×ˢ Icc a b) ×ˢ U] (p₀, z₀))
      (𝓝[Icc a b ×ˢ Icc a b] p₀) :=
    (continuous_fst.tendsto _).inf (tendsto_principal_principal.2 fun _ hq ↦ hq.1)
  have hunif := tendstoUniformlyOn_propagator (Q := fun q : (ℝ × ℝ) × Z ↦ fun t ↦ P t q.2)
    (hP z₀ hz₀) (hsnd.eventually (eventually_mem_nhdsWithin.mono hP))
    ((tendsto_intervalIntegral_norm_sub_of_dominated hab hmeas hcont hdom hz₀).comp hsnd)
  exact hunif.tendsto_comp (continuousOn_propagator (hP z₀ hz₀) p₀ hp₀) hfst

end TauCeti
