/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.UrysohnsLemma

/-!
# Integrable functions vanishing against continuous functions

If an integrable function `f` on a topological space satisfies `∫ g • f ∂μ = 0` for every bounded
continuous real function `g`, then `f = 0` almost everywhere. This is the form in which uniqueness
theorems for integral transforms are usually applied: one first shows that the integrals of `f`
against a dense family of test functions vanish (for instance trigonometric polynomials on the
circle), extends this by continuity to all bounded continuous functions, and concludes here.

The space only needs indicators of closed sets to be pointwise limits of bounded continuous
functions with values in `[0, 1]` (Mathlib's `HasOuterApproxClosed`, which holds for every
pseudo-metrizable space). Dominated convergence then gives `∫_F f ∂μ = 0` for every closed set
`F`, and Mathlib's `MeasureTheory.ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero` concludes.
No finiteness of `μ` is needed beyond the integrability of `f`.

On a locally compact space that need not be metrizable, for instance a locally compact group,
there are too few bounded continuous functions approximating indicators pointwise, but for a
regular measure the compactly supported continuous functions suffice. Inner regularity
approximates a set `s` of finite measure from inside by a compact set `K`, outer regularity
approximates it from outside by an open set `U`, and Urysohn's lemma gives a compactly supported
continuous function between the indicators of `K` and `U`. Its integral against `f` differs from
`∫_s f` by at most the integral of `‖f‖` over `U \ K`, which is small because `U \ K` has small
measure.

## Main results

* `MeasureTheory.Integrable.ae_eq_zero_of_forall_integral_smul_eq_zero`: an integrable function
  whose integrals against all bounded continuous real functions vanish is zero almost everywhere.
* `MeasureTheory.Integrable.ae_eq_of_forall_integral_smul_eq`: two integrable functions with the
  same integrals against all bounded continuous real functions agree almost everywhere.
* `MeasureTheory.Integrable.ae_eq_zero_of_forall_integral_hasCompactSupport_smul_eq_zero`: for a
  regular measure on a locally compact space, an integrable function whose integrals against all
  compactly supported continuous real functions vanish is zero almost everywhere.
-/

public section

open Filter Set Topology
open scoped BoundedContinuousFunction NNReal

namespace MeasureTheory

variable {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [HasOuterApproxClosed X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f g : X → E}

/-- **Integrable functions are determined by their integrals against bounded continuous
functions.** If `f` is integrable and `∫ x, φ x • f x ∂μ = 0` for every bounded continuous
`φ : X → ℝ`, then `f = 0` almost everywhere. -/
theorem Integrable.ae_eq_zero_of_forall_integral_smul_eq_zero (hf : Integrable f μ)
    (h : ∀ φ : X →ᵇ ℝ, ∫ x, φ x • f x ∂μ = 0) : f =ᵐ[μ] 0 := by
  refine ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero hf fun F hF ↦ ?_
  -- The real-valued versions of the continuous approximations of the indicator of `F`.
  let φ (n : ℕ) : X →ᵇ ℝ :=
    ⟨⟨fun x ↦ hF.apprSeq n x, NNReal.continuous_coe.comp (hF.apprSeq n).continuous⟩,
      (hF.apprSeq n).map_bounded'⟩
  have hφ (n : ℕ) (x : X) : φ n x = hF.apprSeq n x := rfl
  have hlim : Tendsto (fun n ↦ ∫ x, φ n x • f x ∂μ) atTop (𝓝 (∫ x in F, f x ∂μ)) := by
    rw [← integral_indicator hF.measurableSet]
    refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖f x‖)
      (fun n ↦ (φ n).continuous.aestronglyMeasurable.smul hf.aestronglyMeasurable) hf.norm
      (fun n ↦ ae_of_all _ fun x ↦ ?_) (ae_of_all _ fun x ↦ ?_)
    · rw [norm_smul, hφ, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (NNReal.coe_le_one.2 (HasOuterApproxClosed.apprSeq_apply_le_one hF n x))
    · have hx := (NNReal.continuous_coe.tendsto _).comp
        (tendsto_pi_nhds.1 (HasOuterApproxClosed.tendsto_apprSeq hF) x)
      by_cases hxF : x ∈ F
      · simpa [hφ, hxF] using hx.smul_const (f x)
      · simpa [hφ, hxF] using hx.smul_const (f x)
  simp only [h] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- Two integrable functions with the same integrals against every bounded continuous real
function agree almost everywhere. -/
theorem Integrable.ae_eq_of_forall_integral_smul_eq (hf : Integrable f μ) (hg : Integrable g μ)
    (h : ∀ φ : X →ᵇ ℝ, ∫ x, φ x • f x ∂μ = ∫ x, φ x • g x ∂μ) : f =ᵐ[μ] g := by
  have hfg : f - g =ᵐ[μ] 0 :=
    (hf.sub hg).ae_eq_zero_of_forall_integral_smul_eq_zero fun φ ↦ by
      have hφ (u : X → E) (hu : Integrable u μ) : Integrable (fun x ↦ φ x • u x) μ :=
        hu.bdd_smul ‖φ‖ φ.continuous.aestronglyMeasurable
          (ae_of_all _ fun x ↦ φ.norm_coe_le_norm x)
      simp_rw [Pi.sub_apply, smul_sub]
      rw [integral_sub (hφ f hf) (hφ g hg), h, sub_self]
  filter_upwards [hfg] with x hx
  simpa [sub_eq_zero] using hx

section LocallyCompact

variable {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [LocallyCompactSpace X] [RegularSpace X] {μ : Measure X} [μ.Regular]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : X → E}

/-- **Integrable functions are determined by their integrals against compactly supported
continuous functions** for a regular measure on a locally compact space. If `f` is integrable and
`∫ x, φ x • f x ∂μ = 0` for every continuous `φ : X → ℝ` with compact support, then `f = 0` almost
everywhere. No metrizability, σ-compactness or σ-finiteness is assumed, and unlike Mathlib's
`MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported` for measures, neither is the
Hausdorff property. -/
theorem Integrable.ae_eq_zero_of_forall_integral_hasCompactSupport_smul_eq_zero
    (hf : Integrable f μ)
    (h : ∀ φ : X → ℝ, Continuous φ → HasCompactSupport φ → ∫ x, φ x • f x ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  refine hf.ae_eq_zero_of_forall_setIntegral_eq_zero fun s hs hμs ↦
    norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε ↦ ?_)
  -- Sets of measure less than `δ` carry less than `ε` of the integral of `‖f‖`.
  obtain ⟨δ, hδ, hδε⟩ := exists_pos_setLIntegral_lt_of_measure_lt hf.2.ne
    (ENNReal.ofReal_pos.2 hε).ne'
  have hδ₂ : δ / 2 ≠ 0 := (ENNReal.half_pos hδ.ne').ne'
  -- Squeeze `s` between a compact closed set `K` and an open set `U` with `μ (U \ K) < δ`.
  obtain ⟨K, hKs, hK, hKcl, hμKs⟩ := hs.exists_isCompact_isClosed_sdiff_lt hμs.ne hδ₂
  obtain ⟨U, hsU, hU, -, hμU⟩ := hs.exists_isOpen_sdiff_lt hμs.ne hδ₂
  have hμUK : μ (U \ K) < δ := calc
    μ (U \ K) ≤ μ (U \ s) + μ (s \ K) :=
      (measure_mono fun x hx ↦ by by_cases hxs : x ∈ s <;> simp_all).trans (measure_union_le _ _)
    _ < δ / 2 + δ / 2 := ENNReal.add_lt_add hμU hμKs
    _ = δ := ENNReal.add_halves δ
  -- A compactly supported continuous function between the indicators of `K` and `U`.
  obtain ⟨φ, hφK, hφU, hφc, hφ01⟩ := exists_continuous_one_zero_of_isCompact hK
    hU.isClosed_compl (disjoint_compl_right_iff_subset.2 (hKs.trans hsU))
  have hφf : Integrable (fun x ↦ φ x • f x) μ :=
    hf.bdd_smul 1 φ.continuous.aestronglyMeasurable
      (ae_of_all _ fun x ↦ by simpa [abs_of_nonneg (hφ01 x).1] using (hφ01 x).2)
  have hUK : MeasurableSet (U \ K) := hU.measurableSet.diff hKcl.measurableSet
  calc ‖∫ x in s, f x ∂μ‖ = ‖∫ x, (s.indicator (1 : X → ℝ) x - φ x) • f x ∂μ‖ := by
        have hind : (fun x ↦ s.indicator (1 : X → ℝ) x • f x) = s.indicator f := by
          ext x
          by_cases hx : x ∈ s <;> simp [hx]
        have hsf : Integrable (fun x ↦ s.indicator (1 : X → ℝ) x • f x) μ := by
          rw [hind]
          exact (integrable_indicator_iff hs).2 hf.integrableOn
        simp_rw [sub_smul]
        rw [integral_sub hsf hφf, h φ φ.continuous hφc, sub_zero, hind, integral_indicator hs]
    _ ≤ ∫ x, (U \ K).indicator (fun x ↦ ‖f x‖) x ∂μ := by
        refine norm_integral_le_of_norm_le ((integrable_indicator_iff hUK).2 hf.norm.integrableOn)
          (ae_of_all _ fun x ↦ ?_)
        rw [norm_smul]
        by_cases hxK : x ∈ K
        · simp [hKs hxK, hφK hxK, (U \ K).indicator_nonneg (fun _ _ ↦ norm_nonneg _)]
        by_cases hxU : x ∈ U
        · rw [Set.indicator_of_mem (Set.mem_sdiff_of_mem hxU hxK)]
          refine mul_le_of_le_one_left (norm_nonneg _) ?_
          have := hφ01 x
          rw [Real.norm_eq_abs, abs_le]
          by_cases hxs : x ∈ s
          · simp only [hxs, Set.indicator_of_mem, Pi.one_apply, Set.mem_Icc] at this ⊢
            constructor <;> linarith
          · simp only [hxs, not_false_eq_true, Set.indicator_of_notMem, Set.mem_Icc] at this ⊢
            constructor <;> linarith
        · have hxs : x ∉ s := fun h ↦ hxU (hsU h)
          simp [hxs, hxU, hφU hxU]
    _ = ∫ x in U \ K, ‖f x‖ ∂μ := integral_indicator hUK
    _ ≤ 0 + ε := by
        rw [zero_add, integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable.restrict]
        exact (ENNReal.toReal_lt_of_lt_ofReal (hδε _ hμUK)).le

end LocallyCompact

end MeasureTheory
