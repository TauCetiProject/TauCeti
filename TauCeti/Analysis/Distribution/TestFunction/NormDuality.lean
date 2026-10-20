/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.Convolution

/-!
# The local `L¹` norm by duality with test vector fields

Let `Ω` be an open set of a finite-dimensional real normed space `E`, let `F` be a real Hilbert
space, and let `G : E → F →L[ℝ] ℝ` be a field of continuous linear functionals that is locally
integrable on `Ω`. Against an additive Haar measure `μ`,

`∫⁻ x in Ω, ‖G x‖ₑ ∂μ = ⨆ { ∫ G x (φ x) ∂μ | φ ∈ 𝓓(Ω, F), ‖φ x‖ ≤ 1 for all x }`

(`MeasureTheory.LocallyIntegrableOn.iSup_ofReal_integral_apply_eq_setLIntegral_enorm`), with
both sides possibly infinite. The bound of each pairing by `∫_Ω ‖G‖` holds for every measure and
every real normed space `F` (`TestFunction.enorm_integral_apply_le_setLIntegral_enorm`).

This duality identifies a supremum over test vector fields, such as the total variation of a
function on `Ω`, with the integral of a pointwise norm. For a weakly differentiable function it
shows that the total variation is the integral of the norm of the weak derivative.

For the reverse inequality, fix a compact `K ⊆ Ω` and let `g x ∈ F` be the Riesz representative
of `G x`. The unit field `x ↦ ‖g x‖⁻¹ • g x` on `K`, extended by zero, is mollified by normalized
bumps of shrinking support. The mollifications are test vector fields on `Ω` of norm at most one,
they converge almost everywhere by the Lebesgue differentiation theorem, and dominated convergence
turns their pairings with `G` into `∫_K ‖G‖`. An exhaustion of `Ω` by compact sets concludes.

## Main declarations

* `TestFunction.enorm_integral_apply_le_setLIntegral_enorm`: `|∫ G φ| ≤ ∫_Ω ‖G‖` for a test vector
  field `φ` on `Ω` with `‖φ‖ ≤ 1`.
* `MeasureTheory.LocallyIntegrableOn.iSup_ofReal_integral_apply_eq_setLIntegral_enorm`: the
  supremum of the pairings is `∫_Ω ‖G‖`.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.1 (the variation of a Sobolev function).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter Metric Set
open scoped ENNReal Distributions Topology Convolution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  {μ : Measure E} {Ω : Opens E}

namespace TestFunction

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pairing a field of continuous linear functionals `G` with a test vector field on `Ω` of norm
at most one gives at most `∫_Ω ‖G‖`. -/
theorem enorm_integral_apply_le_setLIntegral_enorm [OpensMeasurableSpace E] (φ : 𝓓(Ω, F))
    (hφ : ∀ x, ‖φ x‖ ≤ 1) (G : E → F →L[ℝ] ℝ) :
    ‖∫ x, G x (φ x) ∂μ‖ₑ ≤ ∫⁻ x in Ω, ‖G x‖ₑ ∂μ := by
  rw [← lintegral_indicator Ω.isOpen.measurableSet]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x => ?_)
  by_cases hx : x ∈ (Ω : Set E)
  · rw [Set.indicator_of_mem hx, enorm_le_iff_norm_le]
    exact ((G x).le_opNorm (φ x)).trans (mul_le_of_le_one_right (norm_nonneg _) (hφ x))
  · simp [image_eq_zero_of_notMem_tsupport fun hmem => hx (φ.tsupport_subset hmem)]

end TestFunction

namespace MeasureTheory.LocallyIntegrableOn

variable [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] {G : E → F →L[ℝ] ℝ}

/-- For a compact `K ⊆ Ω`, the integral `∫_K ‖G‖` is bounded by the supremum of the pairings of
`G` with test vector fields on `Ω` of norm at most one. -/
private theorem ofReal_setIntegral_norm_le_iSup (hG : LocallyIntegrableOn G Ω μ) {K : Set E}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ENNReal.ofReal (∫ x in K, ‖G x‖ ∂μ) ≤
      ⨆ (φ : 𝓓(Ω, F)) (_ : ∀ x, ‖φ x‖ ≤ 1), ENNReal.ofReal (∫ x, G x (φ x) ∂μ) := by
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open Ω.isOpen hKΩ
  have hKL : K ⊆ cthickening δ K := self_subset_cthickening K
  have hGL : IntegrableOn G (cthickening δ K) μ :=
    hG.integrableOn_compact_subset hδΩ hK.cthickening
  -- The unit field along the Riesz representative `g` of `G`, extended by zero outside `K`.
  set g : E → F := fun x => (InnerProductSpace.toDual ℝ F).symm (G x) with hg_def
  have hgm : AEStronglyMeasurable g (μ.restrict K) :=
    (InnerProductSpace.toDual ℝ F).symm.continuous.comp_aestronglyMeasurable
      (hGL.aestronglyMeasurable.mono_measure (Measure.restrict_mono hKL le_rfl))
  set σ : E → F := K.indicator fun x => ‖g x‖⁻¹ • g x with hσ_def
  have hunit (x : E) : ‖‖g x‖⁻¹ • g x‖ ≤ 1 := by
    rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_le_one
  have hσ (x : E) : ‖σ x‖ ≤ 1 := by
    by_cases hx : x ∈ K
    · simpa [hσ_def, indicator_of_mem hx] using hunit x
    · simp [hσ_def, hx]
  have hσi : Integrable σ μ := by
    have h : IntegrableOn (fun x => ‖g x‖⁻¹ • g x) K μ :=
      ⟨hgm.norm.aemeasurable.inv.aestronglyMeasurable.smul hgm,
        .restrict_of_bounded (C := 1) hK.measure_lt_top (ae_of_all _ hunit)⟩
    exact h.integrable_indicator hK.measurableSet
  have hGσ (x : E) : G x (σ x) = K.indicator (fun x => ‖G x‖) x := by
    by_cases hx : x ∈ K
    · have hgG : ‖g x‖ = ‖G x‖ := (InnerProductSpace.toDual ℝ F).symm.norm_map (G x)
      have hGg : G x (g x) = ‖g x‖ ^ 2 := by
        rw [← InnerProductSpace.toDual_symm_apply, real_inner_self_eq_norm_sq]
      rw [hσ_def, indicator_of_mem hx, indicator_of_mem hx, map_smul, hGg, ← hgG, smul_eq_mul]
      rcases eq_or_ne ‖g x‖ 0 with h0 | h0
      · simp [h0]
      · field_simp
    · simp [hσ_def, hx]
  -- Normalized bumps with outer radius `δ / (n + 1)` and inner radius half of it.
  let φ : ℕ → ContDiffBump (0 : E) := fun n =>
    ⟨δ / (2 * ((n + 1 : ℕ) : ℝ)), δ / ((n + 1 : ℕ) : ℝ), by positivity,
      div_lt_div_of_pos_left hδ (by positivity)
        (by linarith [(by positivity : (0 : ℝ) < (n + 1 : ℕ))])⟩
  set ψ : ℕ → E → F := fun n => (φ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] σ
    with hψ_def
  have hψs (n : ℕ) : tsupport (ψ n) ⊆ cthickening δ K := by
    have hsupp : Function.support (ψ n) ⊆ thickening (φ n).rOut K := by
      refine (support_convolution_subset _).trans ?_
      rw [(φ n).support_normed_eq, ← ball_add_zero]
      exact add_subset_add_left (support_indicator_subset)
    refine (closure_mono hsupp).trans <| (closure_thickening_subset_cthickening _ _).trans <|
      cthickening_mono ?_ K
    exact div_le_self hδ.le (by simp)
  -- The mollifications are test vector fields on `Ω` of norm at most one.
  let Φ : ℕ → 𝓓(Ω, F) := fun n =>
    ⟨ψ n, (φ n).hasCompactSupport_normed.contDiff_convolution_left _ (φ n).contDiff_normed
        hσi.locallyIntegrable,
      hK.cthickening.of_isClosed_subset (isClosed_tsupport _) (hψs n),
      (hψs n).trans hδΩ⟩
  have hΦψ (n : ℕ) : (Φ n : E → F) = ψ n := TestFunction.coe_mk
  have hΦ (n : ℕ) (x : E) : ‖Φ n x‖ ≤ 1 := by
    simpa [hΦψ] using norm_convolution_lsmul_le_of_forall_norm_le (φ n).support_normed_eq.subset
      (φ n).nonneg_normed (φ n).integral_normed hσi.aestronglyMeasurable fun y _ => hσ y
  -- By the Lebesgue differentiation theorem, they converge to `σ` almost everywhere.
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => ψ n x) atTop (𝓝 (σ x)) := by
    refine ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (K := 2) ?_
      (Eventually.of_forall fun n => ?_) hσi.locallyIntegrable
    · exact (tendsto_const_div_atTop_nhds_zero_nat δ).comp (tendsto_add_atTop_nat 1)
    · dsimp only [φ]
      rw [mul_div_assoc', mul_div_mul_left _ _ two_ne_zero]
  -- By dominated convergence, their pairings with `G` converge to `∫_K ‖G‖`.
  have hint : Tendsto (fun n => ∫ x, G x (Φ n x) ∂μ) atTop (𝓝 (∫ x in K, ‖G x‖ ∂μ)) := by
    have hcompl (n : ℕ) : ∫ x, G x (Φ n x) ∂μ = ∫ x in cthickening δ K, G x (ψ n x) ∂μ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [hΦψ, image_eq_zero_of_notMem_tsupport fun h => hx (hψs n h), map_zero]).symm
    have hK' : ∫ x in K, ‖G x‖ ∂μ = ∫ x in cthickening δ K, G x (σ x) ∂μ := by
      simp_rw [hGσ, setIntegral_indicator hK.measurableSet, inter_eq_right.mpr hKL]
    simp_rw [hcompl, hK']
    refine tendsto_integral_of_dominated_convergence (fun x => ‖G x‖) (fun n => ?_) hGL.norm
      (fun n => ae_of_all _ fun x => ?_) (ae_restrict_of_ae (hlim.mono fun x hx => ?_))
    · exact Continuous.comp_aestronglyMeasurable₂ (g := fun (L : F →L[ℝ] ℝ) v => L v)
        (by fun_prop) hGL.aestronglyMeasurable (Φ n).continuous.aestronglyMeasurable
    · exact ((G x).le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg _) (hΦ n x))
    · exact ((G x).continuous.tendsto _).comp hx
  refine le_of_tendsto' ((ENNReal.continuous_ofReal.tendsto _).comp hint) fun n => ?_
  exact le_iSup₂ (f := fun (φ : 𝓓(Ω, F)) (_ : ∀ x, ‖φ x‖ ≤ 1) =>
    ENNReal.ofReal (∫ x, G x (φ x) ∂μ)) (Φ n) (hΦ n)

/-- **The local `L¹` norm by duality.** For a field `G` of continuous linear functionals on a real
Hilbert space `F` that is locally integrable on `Ω`, against an additive Haar measure,
`∫_Ω ‖G‖` is the supremum of `∫ G x (φ x)` over test vector fields `φ ∈ 𝓓(Ω, F)` with
`‖φ x‖ ≤ 1`. Both sides may be infinite. -/
theorem iSup_ofReal_integral_apply_eq_setLIntegral_enorm (hG : LocallyIntegrableOn G Ω μ) :
    ⨆ (φ : 𝓓(Ω, F)) (_ : ∀ x, ‖φ x‖ ≤ 1), ENNReal.ofReal (∫ x, G x (φ x) ∂μ) =
      ∫⁻ x in Ω, ‖G x‖ₑ ∂μ := by
  refine le_antisymm (iSup₂_le fun φ hφ => ?_) ?_
  · exact (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans <|
      (Real.enorm_eq_ofReal_abs _).symm.trans_le (φ.enorm_integral_apply_le_setLIntegral_enorm hφ G)
  -- Exhaust `Ω` by the increasing compact sets `C n ∩ closedBall 0 n`.
  obtain ⟨C, hCc, hCΩ, hCU, hCm⟩ := Ω.isOpen.exists_iUnion_isClosed
  have hKm : Monotone fun n : ℕ => C n ∩ closedBall (0 : E) n := fun m n hmn =>
    inter_subset_inter (hCm hmn) (closedBall_subset_closedBall (by exact_mod_cast hmn))
  have hKU : ⋃ n : ℕ, C n ∩ closedBall (0 : E) n = Ω := by
    refine Subset.antisymm (iUnion_subset fun n => inter_subset_left.trans (hCΩ n)) fun x hx => ?_
    rw [← hCU, mem_iUnion] at hx
    obtain ⟨m, hm⟩ := hx
    obtain ⟨k, hk⟩ := exists_nat_ge ‖x‖
    exact mem_iUnion.mpr ⟨max m k, hCm (le_max_left m k) hm,
      mem_closedBall_zero_iff.mpr (hk.trans (by exact_mod_cast le_max_right m k))⟩
  have hKc (n : ℕ) : IsCompact (C n ∩ closedBall (0 : E) n) :=
    (isCompact_closedBall 0 _).inter_left (hCc n)
  have hKΩ (n : ℕ) : C n ∩ closedBall (0 : E) n ⊆ Ω := inter_subset_left.trans (hCΩ n)
  calc ∫⁻ x in Ω, ‖G x‖ₑ ∂μ = ∫⁻ x in ⋃ n : ℕ, C n ∩ closedBall (0 : E) n, ‖G x‖ₑ ∂μ := by
        rw [hKU]
    _ = ⨆ n : ℕ, ∫⁻ x in C n ∩ closedBall (0 : E) n, ‖G x‖ₑ ∂μ :=
        setLIntegral_iUnion_of_directed _ hKm.directed_le
    _ ≤ _ := iSup_le fun n => by
        rw [← ofReal_integral_norm_eq_lintegral_enorm
          (hG.integrableOn_compact_subset (hKΩ n) (hKc n))]
        exact hG.ofReal_setIntegral_norm_le_iSup (hKc n) (hKΩ n)

end MeasureTheory.LocallyIntegrableOn
