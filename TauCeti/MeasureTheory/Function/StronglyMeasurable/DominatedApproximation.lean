/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Analysis.Normed.Group.Indicator
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Simple approximation dominated by the pointwise norm

A strongly measurable function admits pointwise convergent simple approximants whose norms are
bounded by its norm at each point. This bound lets the approximants inherit any integrable
majorant of the function. The almost-everywhere versions use a common null set for convergence
and domination. Finite strong measurability gives finite-measure supports for arbitrary measures.

For norm-controlled simple approximation, see Hytönen, van Neerven, Veraar and Weis,
*Analysis in Banach Spaces*, Vol. I, §1.1.
The construction uses `SimpleFunc.eapprox` on the norm and `StronglyMeasurable.approxBounded`
on the normalized vector.
-/

public section

open Filter Function
open scoped ENNReal Topology

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} {f : α → E}

/-- A strongly measurable function is the pointwise limit of simple functions dominated in
norm by the function itself. -/
theorem StronglyMeasurable.exists_simpleFunc_norm_le (hf : StronglyMeasurable f) :
    ∃ s : ℕ → SimpleFunc α E, (∀ n x, ‖s n x‖ ≤ ‖f x‖) ∧
      ∀ x, Tendsto (fun n ↦ s n x) atTop (𝓝 (f x)) := by
  have hdir : StronglyMeasurable (fun x ↦ NormedSpace.normalize (f x)) := by
    simpa only [NormedSpace.normalize, Pi.inv_apply] using hf.norm.inv₀.fun_smul hf
  have hunit (x : α) : ‖NormedSpace.normalize (f x)‖ ≤ 1 := by
    by_cases hx : f x = 0
    · simp [hx]
    · simp [NormedSpace.norm_normalize hx]
  have hnorm : Measurable (fun x ↦ ‖f x‖ₑ) := hf.eNorm
  let r (n : ℕ) := (SimpleFunc.eapprox (fun x ↦ ‖f x‖ₑ) n).map ENNReal.toReal
  refine ⟨fun n ↦ ((r n).pair (hdir.approxBounded 1 n)).map (fun p ↦ p.1 • p.2),
    fun n x ↦ ?_, fun x ↦ ?_⟩
  · have hr₀ : 0 ≤ r n x := ENNReal.toReal_nonneg
    have hr : r n x ≤ ‖f x‖ := by
      simp only [r, SimpleFunc.map_apply, ← toReal_eNorm]
      apply ENNReal.toReal_mono eNorm_ne_top
      rw [← SimpleFunc.iSup_eapprox_apply hnorm x]
      exact le_iSup (fun k ↦ SimpleFunc.eapprox (fun y ↦ ‖f y‖ₑ) k x) n
    simp only [SimpleFunc.map_apply, SimpleFunc.pair_apply, norm_smul, Real.norm_of_nonneg hr₀]
    exact (mul_le_of_le_one_right hr₀ (hdir.norm_approxBounded_le zero_le_one n x)).trans hr
  · have hr : Tendsto (fun n ↦ r n x) atTop (𝓝 ‖f x‖) := by
      simpa only [r, SimpleFunc.map_apply, Function.comp_def, toReal_eNorm] using
        (ENNReal.tendsto_toReal eNorm_ne_top).comp (SimpleFunc.tendsto_eapprox hnorm x)
    simpa only [SimpleFunc.map_apply, SimpleFunc.pair_apply, NormedSpace.norm_smul_normalize] using
      hr.smul (hdir.tendsto_approxBounded_of_norm_le (hunit x))

/-- An a.e. strongly measurable function has simple approximants that converge to it and are
dominated by its norm outside a common null set. -/
theorem AEStronglyMeasurable.exists_simpleFunc_norm_le (hf : AEStronglyMeasurable f μ) :
    ∃ s : ℕ → SimpleFunc α E, ∀ᵐ x ∂μ, (∀ n, ‖s n x‖ ≤ ‖f x‖) ∧
      Tendsto (fun n ↦ s n x) atTop (𝓝 (f x)) := by
  obtain ⟨s, hnorm, hlim⟩ := hf.stronglyMeasurable_mk.exists_simpleFunc_norm_le
  exact ⟨s, hf.ae_eq_mk.mono fun x hx ↦ hx.symm ▸ ⟨fun n ↦ hnorm n x, hlim x⟩⟩

/-- A finitely strongly measurable function has norm-dominated, pointwise convergent simple
approximants of finite-measure support. -/
theorem FinStronglyMeasurable.exists_simpleFunc_norm_le (hf : FinStronglyMeasurable f μ) :
    ∃ s : ℕ → SimpleFunc α E, (∀ n, μ (support (s n)) < ∞) ∧
      (∀ n x, ‖s n x‖ ≤ ‖f x‖) ∧ ∀ x, Tendsto (fun n ↦ s n x) atTop (𝓝 (f x)) := by
  obtain ⟨s, hnorm, hlim⟩ := hf.stronglyMeasurable.exists_simpleFunc_norm_le
  -- The original finite-measure supports eventually contain every point where `f` is nonzero.
  let A (n : ℕ) := support (hf.approx n)
  have hA (n : ℕ) : MeasurableSet (A n) := (hf.approx n).measurableSet_support
  let t (n : ℕ) := (s n).restrict (A n)
  have ht (n : ℕ) (x : α) : ‖t n x‖ ≤ ‖f x‖ := by
    simpa only [t, SimpleFunc.coe_restrict _ (hA n)] using
      (norm_indicator_le_norm_self (s := A n) (s n) x).trans (hnorm n x)
  refine ⟨t, fun n ↦ ?_, ht, fun x ↦ ?_⟩
  · simp only [t, SimpleFunc.coe_restrict _ (hA n), Set.support_indicator]
    exact (measure_mono Set.inter_subset_left).trans_lt (hf.fin_support_approx n)
  · by_cases hx : f x = 0
    · have hz (n : ℕ) : t n x = 0 := by simpa [hx] using ht n x
      simp [hx, hz]
    · apply (hlim x).congr'
      filter_upwards [(hf.tendsto_approx x).eventually_ne hx] with n hn
      have hxA : x ∈ A n := hn
      simp [t, SimpleFunc.coe_restrict _ (hA n), hxA]

/-- An a.e. finitely strongly measurable function has simple approximants of finite-measure
support, with norm domination and convergence outside a common null set. -/
theorem AEFinStronglyMeasurable.exists_simpleFunc_norm_le (hf : AEFinStronglyMeasurable f μ) :
    ∃ s : ℕ → SimpleFunc α E, (∀ n, μ (support (s n)) < ∞) ∧
      ∀ᵐ x ∂μ, (∀ n, ‖s n x‖ ≤ ‖f x‖) ∧ Tendsto (fun n ↦ s n x) atTop (𝓝 (f x)) := by
  obtain ⟨s, hfin, hnorm, hlim⟩ := hf.finStronglyMeasurable_mk.exists_simpleFunc_norm_le
  exact ⟨s, hfin, hf.ae_eq_mk.mono fun x hx ↦ hx.symm ▸ ⟨fun n ↦ hnorm n x, hlim x⟩⟩

end MeasureTheory
