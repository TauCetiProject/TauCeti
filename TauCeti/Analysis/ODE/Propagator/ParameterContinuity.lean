/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Propagator
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Joint continuity of the propagator in the times and a parameter

Let `P : ℝ → Z → E →L[𝕜] E` be a family of coefficients on `[a, b]` depending on a parameter
`z` in a subset `U` of a first-countable topological space `Z`, for instance an open subset of
`ℂ`. Suppose that `P(·, z)` is almost everywhere strongly measurable on `[a, b]` for `z ∈ U`, that
`z ↦ P(t, z)` is continuous on `U` for almost every `t ∈ [a, b]`, and that for every compact
`K ⊆ U` the norms `‖P(t, z)‖`, `z ∈ K`, are bounded by one integrable function `m_K(t)`. Then the
propagator `(t, s, z) ↦ N_{P(·, z)}(t, s)` is continuous on `[a, b]² × U` in the operator norm.
These are the hypotheses of DiracScatteringAndNonlinearFourierTransform §1.6, with continuity in
`z` in place of holomorphy.

The coefficients `P(·, z)` converge to `P(·, z₀)` in `L¹([a, b])` as `z → z₀` by dominated
convergence along sequences, so the propagators converge uniformly on `[a, b]²`
(`TauCeti.tendstoUniformlyOn_propagator`), and the limit is continuous on `[a, b]²`
(`TauCeti.continuousOn_propagator`).

## Main results

* `TauCeti.tendsto_integral_norm_sub_of_dominated`: `∫ t in a..b, ‖P(t, z) - P(t, z₀)‖ → 0` as
  `z → z₀` within `U`.
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
  {Z : Type*} [TopologicalSpace Z] [FirstCountableTopology Z]
  {P : ℝ → Z → E →L[𝕜] E} {U : Set Z} {a b : ℝ}

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- **`L¹` continuity of a dominated family of coefficients.** If `P(·, z)` is almost everywhere
strongly measurable on `[a, b]` for `z ∈ U`, `z ↦ P(t, z)` is continuous on `U` for almost every
`t ∈ [a, b]`, and on every compact `K ⊆ U` the norms `‖P(t, z)‖` are bounded by one integrable
function of `t`, then `∫ t in a..b, ‖P(t, z) - P(t, z₀)‖ → 0` as `z → z₀` within `U`. -/
theorem tendsto_integral_norm_sub_of_dominated (hab : a ≤ b)
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (fun t ↦ P t z) (volume.restrict (Icc a b)))
    (hcont : ∀ᵐ t, t ∈ Icc a b → ContinuousOn (P t) U)
    (hdom : ∀ K ⊆ U, IsCompact K → ∃ m : ℝ → ℝ, IntegrableOn m (Icc a b) ∧
      ∀ z ∈ K, ∀ᵐ t, t ∈ Icc a b → ‖P t z‖ ≤ m t) {z₀ : Z} (hz₀ : z₀ ∈ U) :
    Tendsto (fun z ↦ ∫ t in a..b, ‖P t z - P t z₀‖) (𝓝[U] z₀) (𝓝 0) := by
  have hIoc : uIoc a b ⊆ Icc a b := by
    rw [uIoc_of_le hab]
    exact Ioc_subset_Icc_self
  -- Test along a sequence `w → z₀` within `U`; from some `N` on it lies in `U`.
  refine tendsto_iff_seq_tendsto.2 fun w hw ↦ ?_
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hw.eventually self_mem_nhdsWithin)
  set v : ℕ → Z := fun n ↦ w (n + N)
  have hvU (n : ℕ) : v n ∈ U := hN _ (Nat.le_add_left N n)
  have hv : Tendsto v atTop (𝓝 z₀) :=
    (tendsto_nhdsWithin_iff.1 hw).1.comp (tendsto_add_atTop_nat N)
  -- The tail of the sequence with its limit is a compact subset of `U`, so it has one bound.
  obtain ⟨m, hm, hbound⟩ := hdom (insert z₀ (range v))
    (insert_subset hz₀ (range_subset_iff.2 hvU)) hv.isCompact_insert_range
  rw [← tendsto_add_atTop_iff_nat N]
  simpa using intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (F := fun n t ↦ ‖P t (v n) - P t z₀‖) (f := fun _ ↦ (0 : ℝ)) (fun t ↦ m t + m t)
    (Eventually.of_forall fun n ↦ ((hmeas _ (hvU n)).sub (hmeas z₀ hz₀)).norm.mono_measure
      (Measure.restrict_mono hIoc le_rfl))
    (Eventually.of_forall fun n ↦ by
      filter_upwards [hbound (v n) (mem_insert_of_mem _ (mem_range_self n)),
        hbound z₀ (mem_insert _ _)] with t ht ht₀ htI
      rw [norm_norm]
      exact (norm_sub_le _ _).trans (add_le_add (ht (hIoc htI)) (ht₀ (hIoc htI))))
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 (hm.add hm))
    (by
      filter_upwards [hcont] with t ht htI
      exact tendsto_iff_norm_sub_tendsto_zero.1 ((ht (hIoc htI) z₀ hz₀).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hv, Eventually.of_forall hvU⟩)))

variable [CompleteSpace E]

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
    ((tendsto_integral_norm_sub_of_dominated hab hmeas hcont hdom hz₀).comp hsnd)
  exact hunif.tendsto_comp (continuousOn_propagator (hP z₀ hz₀) p₀ hp₀) hfst

end TauCeti
