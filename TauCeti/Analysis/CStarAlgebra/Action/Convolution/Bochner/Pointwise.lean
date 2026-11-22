/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.L1
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import TauCeti.MeasureTheory.Function.Lp.InfiniteSum
import TauCeti.MeasureTheory.Function.Lp.LocallyCompact

/-!
# Pointwise formulas for Bochner `Lᵖ` twisted convolution

On a locally compact topological group `G` with a regular left-invariant Borel measure `μ`,
`TauCeti.Analysis.CStarAlgebra.Action.Convolution.L1` identifies
`Completion (ConvolutionAlgebra α μ)` isometrically with `Lp A 1 μ` via
`ConvolutionAlgebra.completionEquivL1` and defines `CStarAction.convolutionLp` on `Lp A p μ` for
`1 ≤ p < ∞`.

This file derives pointwise almost-everywhere formulas for arbitrary `f ∈ L¹(G, μ; A)` and
`g ∈ Lᵖ(G, μ; A)` (`1 ≤ p < ∞`) by expanding `L¹` and `Lᵖ` classes into absolutely norm-summable
series of compactly supported continuous functions
(`CompactlySupportedContinuousMap.exists_hasSum_toLp`), without assuming second countability of `G`
or σ-finiteness of `μ`. It proves that the twisted convolution integrand
`r ↦ f r * α r (g (r⁻¹ * s))` is Bochner-integrable for almost every `s` and integrates to
`CStarAction.convolutionLp`.

## Main results

* `TauCeti.CStarAction.ae_integrable_convolution_integrand`,
  `TauCeti.CStarAction.convolutionLp_toL1_ae_eq`, `TauCeti.CStarAction.coeFn_convolutionLp`:
  almost-everywhere integrability and pointwise Bochner integral formula for `convolutionLp` at
  any finite `1 ≤ p < ∞`.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016), §§2.5, 3.2.
-/

public section

noncomputable section

open Filter Function MeasureTheory Topology UniformSpace
open scoped CompactlySupported CStarAlgebra ENNReal NNReal

namespace TauCeti.CStarAction

section RegularLeftInvariant

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  (α : CStarAction G A) {μ : Measure G} [μ.IsMulLeftInvariant] [μ.Regular]

private theorem ae_summable_integral_norm_of_summable {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {φ ψ : ℕ → C_c(G, A)}
    (hφ : Summable fun m => ‖CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ m)‖)
    (hψ : Summable fun n => ‖CompactlySupportedContinuousMap.toLp p μ ℂ (ψ n)‖) :
    ∀ᵐ s ∂μ, Summable fun q : ℕ × ℕ =>
      ∫ r, ‖φ q.1 r * α r (ψ q.2 (r⁻¹ * s))‖ ∂μ := by
  have hprod : Summable fun q : ℕ × ℕ =>
      ‖CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ q.1)‖ *
        ‖CompactlySupportedContinuousMap.toLp p μ ℂ (ψ q.2)‖ :=
    Summable.mul_of_nonneg hφ hψ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  let W : ℕ × ℕ → G → ℝ := fun q s => ∫ r, ‖φ q.1 r‖ * ‖ψ q.2 (r⁻¹ * s)‖ ∂μ
  have hW_eLpNorm (q : ℕ × ℕ) :
      eLpNorm (W q) p μ ≤
        ENNReal.ofReal (‖CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ q.1)‖ *
          ‖CompactlySupportedContinuousMap.toLp p μ ℂ (ψ q.2)‖) := by
    have hnc : Continuous fun r => ‖φ q.1 r‖ := (φ q.1).continuous.norm
    have hns : HasCompactSupport fun r => ‖φ q.1 r‖ := (φ q.1).hasCompactSupport.norm
    have hmc : Continuous fun s => ‖ψ q.2 s‖ := (ψ q.2).continuous.norm
    have hms : HasCompactSupport fun s => ‖ψ q.2 s‖ := (ψ q.2).hasCompactSupport.norm
    have hni : Integrable (fun r => ‖φ q.1 r‖) μ := hnc.integrable_of_hasCompactSupport hns
    have hmm : MemLp (fun s => ‖ψ q.2 s‖) p μ := hmc.memLp_of_hasCompactSupport hms
    have hnorm_fn :
        ‖hni.toL1 fun r => ‖φ q.1 r‖‖ =
          ‖CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ q.1)‖ := by
      have hL1 : ‖hni.toL1 fun r => ‖φ q.1 r‖‖ =
          (eLpNorm (fun r => ‖φ q.1 r‖) 1 μ).toReal := by
        simpa only [Lp.norm_def] using
          congrArg ENNReal.toReal (eLpNorm_congr_ae hni.coeFn_toL1)
      rw [hL1, eLpNorm_norm _ ((φ q.1).memLp 1 μ).aestronglyMeasurable,
        CompactlySupportedContinuousMap.norm_toLp]
    have hnorm_gn :
        ‖hmm.toLp fun s => ‖ψ q.2 s‖‖ =
          ‖CompactlySupportedContinuousMap.toLp p μ ℂ (ψ q.2)‖ := by
      rw [Lp.norm_toLp, eLpNorm_norm _ ((ψ q.2).memLp p μ).aestronglyMeasurable,
        CompactlySupportedContinuousMap.norm_toLp]
    calc
      eLpNorm (W q) p μ
          = eLpNorm (Lp.convolutionL μ p hp (hni.toL1 fun r => ‖φ q.1 r‖)
              (hmm.toLp fun s => ‖ψ q.2 s‖)) p μ :=
            eLpNorm_congr_ae (Lp.convolutionL_toLp_ae_eq hnc hns hmc hms).symm
      _ = ENNReal.ofReal ‖Lp.convolutionL μ p hp (hni.toL1 fun r => ‖φ q.1 r‖)
            (hmm.toLp fun s => ‖ψ q.2 s‖)‖ := by
          rw [← Lp.eNorm_def, ← ofReal_norm]
      _ ≤ ENNReal.ofReal (‖hni.toL1 fun r => ‖φ q.1 r‖‖ * ‖hmm.toLp fun s => ‖ψ q.2 s‖‖) :=
          ENNReal.ofReal_le_ofReal (Lp.norm_convolutionL_apply_le _ _)
      _ = ENNReal.ofReal (‖CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ q.1)‖ *
            ‖CompactlySupportedContinuousMap.toLp p μ ℂ (ψ q.2)‖) := by
          rw [hnorm_fn, hnorm_gn]
  have hW_tsum : ∑' q : ℕ × ℕ, eLpNorm (W q) p μ ≠ ∞ := by
    refine lt_top_iff_ne_top.1 ?_
    calc
      ∑' q : ℕ × ℕ, eLpNorm (W q) p μ
          ≤ ∑' q : ℕ × ℕ,
              ENNReal.ofReal (‖CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ q.1)‖ *
                ‖CompactlySupportedContinuousMap.toLp p μ ℂ (ψ q.2)‖) :=
            tsum_le_tsum hW_eLpNorm
      _ = ENNReal.ofReal (∑' q : ℕ × ℕ,
            ‖CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ q.1)‖ *
              ‖CompactlySupportedContinuousMap.toLp p μ ℂ (ψ q.2)‖) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
            hprod]
      _ < ∞ := ENNReal.ofReal_lt_top
  filter_upwards [summable_norm_of_tsum_eLpNorm_ne_top Fact.out hW_tsum] with s hsW
  refine .of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun q => ?_) hsW
  refine (integral_mono (α.integrable_integrand (φ q.1) (ψ q.2) μ s).norm ?_
    fun r => ?_).trans (le_abs_self (W q s))
  · exact (by fun_prop : Continuous fun r => ‖φ q.1 r‖ * ‖ψ q.2 (r⁻¹ * s)‖)
      |>.integrable_of_hasCompactSupport
        ((φ q.1).hasCompactSupport.mono' fun r hr =>
          subset_tsupport _ (mem_support.2 fun h => hr (by simp [h])))
  · simpa [StarAlgEquiv.norm_map] using
      norm_mul_le (φ q.1 r) (α r (ψ q.2 (r⁻¹ * s)))

private theorem ae_hasSum_convolution_of_hasSum_toLp {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {φ ψ : ℕ → C_c(G, A)} {u : Lp A 1 μ} {v : Lp A p μ}
    (hφ_sum : HasSum (fun m => CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ m)) u)
    (hφ_norm : Summable fun m => ‖CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ m)‖)
    (hψ_sum : HasSum (fun n => CompactlySupportedContinuousMap.toLp p μ ℂ (ψ n)) v)
    (hψ_norm : Summable fun n => ‖CompactlySupportedContinuousMap.toLp p μ ℂ (ψ n)‖) :
    ∀ᵐ s ∂μ, HasSum (fun q : ℕ × ℕ => α.convolution μ (φ q.1) (ψ q.2) s)
      (α.convolutionLp μ p hp u v s) := by
  let F : ℕ × ℕ → Lp A p μ := fun q =>
    CompactlySupportedContinuousMap.toLp p μ ℂ (α.convolution μ (φ q.1) (ψ q.2))
  have hF_eq (q : ℕ × ℕ) :
      F q = α.convolutionLp μ p hp (CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ q.1))
        (CompactlySupportedContinuousMap.toLp p μ ℂ (ψ q.2)) :=
    (α.convolutionLp_toLp (φ q.1) (ψ q.2)).symm
  have hF_norm : Summable fun q : ℕ × ℕ => ‖F q‖ := by
    refine .of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_)
      (Summable.mul_of_nonneg hφ_norm hψ_norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))
    rw [hF_eq q]
    exact norm_convolutionLp_apply_le _ _
  have hF_sum : HasSum F (α.convolutionLp μ p hp u v) := by
    have hF_summable : Summable F := .of_norm hF_norm
    have h1 : HasSum (fun m =>
        α.convolutionLp μ p hp (CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ m)) v)
        (α.convolutionLp μ p hp u v) :=
      hφ_sum.map _ ((α.convolutionLp μ p hp).flip v).continuous
    have h2 (m : ℕ) : HasSum (fun n => F (m, n))
        (α.convolutionLp μ p hp (CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ m)) v) := by
      simp_rw [hF_eq]
      exact hψ_sum.map _
        (α.convolutionLp μ p hp (CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ m))).continuous
    have h3 : HasSum (fun m =>
        α.convolutionLp μ p hp (CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ m)) v)
        (∑' q, F q) :=
      hF_summable.hasSum.prod_fiberwise h2
    exact (h1.unique h3).symm ▸ hF_summable.hasSum
  exact (CompactlySupportedContinuousMap.ae_hasSum_of_hasSum_toLp ℂ hF_sum hF_norm).mono
    fun _ hs => hs.1

private theorem ae_integrable_and_convolutionLp_toL1_ae_eq {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {f g : G → A} (hf : Integrable f μ) (hg : MemLp g p μ) :
    ∀ᵐ s ∂μ, Integrable (fun r => f r * α r (g (r⁻¹ * s))) μ ∧
      α.convolutionLp μ p hp (hf.toL1 f) (hg.toLp g) s =
        ∫ r, f r * α r (g (r⁻¹ * s)) ∂μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · have : μ.IsOpenPosMeasure := isOpenPosMeasure_of_mulLeftInvariant_of_regular
    have : μ.IsHaarMeasure := ⟨⟩
    obtain ⟨φ, hφ_sum, hφ_norm⟩ :=
      CompactlySupportedContinuousMap.exists_hasSum_toLp ENNReal.one_ne_top μ ℂ (hf.toL1 f)
    obtain ⟨ψ, hψ_sum, hψ_norm⟩ :=
      CompactlySupportedContinuousMap.exists_hasSum_toLp hp μ ℂ (hg.toLp g)
    have hae_f :
        ∀ᵐ r ∂μ, HasSum (fun m => φ m r) (f r) ∧ Summable fun m => ‖φ m r‖ := by
      filter_upwards [CompactlySupportedContinuousMap.ae_hasSum_of_hasSum_toLp ℂ hφ_sum hφ_norm,
        hf.coeFn_toL1] with r ⟨hr, hnr⟩ hfr
      exact ⟨hfr ▸ hr, hnr⟩
    have hae_g : ∀ᵐ t ∂μ, HasSum (fun n => ψ n t) (g t) ∧ Summable fun n => ‖ψ n t‖ := by
      filter_upwards [CompactlySupportedContinuousMap.ae_hasSum_of_hasSum_toLp ℂ hψ_sum hψ_norm,
        hg.coeFn_toLp] with t ⟨ht, hnt⟩ hgt
      exact ⟨hgt ▸ ht, hnt⟩
    filter_upwards [α.ae_summable_integral_norm_of_summable hp hφ_norm hψ_norm,
      α.ae_hasSum_convolution_of_hasSum_toLp hp hφ_sum hφ_norm hψ_sum hψ_norm]
      with s hh_sum_int hsuv
    let h : ℕ × ℕ → G → A := fun q r => φ q.1 r * α r (ψ q.2 (r⁻¹ * s))
    have hh_int (q : ℕ × ℕ) : Integrable (h q) μ :=
      α.integrable_integrand (φ q.1) (ψ q.2) μ s
    have hae_h : ∀ᵐ r ∂μ, ∑' q : ℕ × ℕ, h q r = f r * α r (g (r⁻¹ * s)) := by
      filter_upwards [hae_f, (Measure.quasiMeasurePreserving_inv_mul_of_regular μ s).ae hae_g]
        with r ⟨hfr, hfnorm⟩ ⟨hgr, hgnorm⟩
      have hαg_sum : HasSum (fun n => α r (ψ n (r⁻¹ * s))) (α r (g (r⁻¹ * s))) :=
        hgr.map (α r) (StarAlgEquiv.isometry (α r)).continuous
      have hmul_summable : Summable fun q : ℕ × ℕ => h q r :=
        .of_norm <| .of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_mul_le _ _)
          (Summable.mul_of_nonneg (f := fun m => ‖φ m r‖)
            (g := fun n => ‖α r (ψ n (r⁻¹ * s))‖) hfnorm
            (by simpa only [StarAlgEquiv.norm_map] using hgnorm)
            (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))
      exact (hfr.mul hαg_sum hmul_summable).tsum_eq
    refine ⟨(integrable_tsum_of_summable_integral_norm hh_int hh_sum_int).congr hae_h, ?_⟩
    have hint_sum := hasSum_integral_of_summable_integral_norm hh_int hh_sum_int
    have hh_eq (q : ℕ × ℕ) : ∫ r, h q r ∂μ = α.convolution μ (φ q.1) (ψ q.2) s := by
      simp [h, α.convolution_apply]
    simp_rw [hh_eq, integral_congr_ae hae_h] at hint_sum
    exact hsuv.unique hint_sum

/-- **Almost-everywhere integrability of the twisted convolution integrand**: for any
Bochner-integrable `f : G → A` and `g ∈ Lᵖ(G, μ; A)` (`1 ≤ p < ∞`) on a locally compact group
with a regular left-invariant measure, `r ↦ f r * α r (g (r⁻¹ * s))` is Bochner-integrable for
almost every `s : G`. -/
theorem ae_integrable_convolution_integrand {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {f g : G → A} (hf : Integrable f μ) (hg : MemLp g p μ) :
    ∀ᵐ s ∂μ, Integrable (fun r => f r * α r (g (r⁻¹ * s))) μ :=
  (α.ae_integrable_and_convolutionLp_toL1_ae_eq hp hf hg).mono fun _ hs => hs.1

/-- **Pointwise formula for twisted `Lᵖ` convolution**: for any Bochner-integrable `f : G → A`
and `g ∈ Lᵖ(G, μ; A)` (`1 ≤ p < ∞`) on a locally compact group with a regular left-invariant
measure, `convolutionLp` of their classes is represented almost everywhere by
`s ↦ ∫ r, f r * α r (g (r⁻¹ * s)) dμ`. -/
theorem convolutionLp_toL1_ae_eq {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ∞} {f g : G → A}
    (hf : Integrable f μ) (hg : MemLp g p μ) :
    α.convolutionLp μ p hp (hf.toL1 f) (hg.toLp g) =ᵐ[μ]
      fun s => ∫ r, f r * α r (g (r⁻¹ * s)) ∂μ :=
  (α.ae_integrable_and_convolutionLp_toL1_ae_eq hp hf hg).mono fun _ hs => hs.2

/-- For arbitrary `u ∈ Lp A 1 μ` and `v ∈ Lp A p μ` (`1 ≤ p < ∞`) on a locally compact group with
a regular left-invariant measure, `convolutionLp` is represented almost everywhere by
`s ↦ ∫ r, u r * α r (v (r⁻¹ * s)) dμ`. -/
theorem coeFn_convolutionLp {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ∞} (u : Lp A 1 μ)
    (v : Lp A p μ) :
    α.convolutionLp μ p hp u v =ᵐ[μ] fun s => ∫ r, u r * α r (v (r⁻¹ * s)) ∂μ := by
  simpa [Lp.ext ((Lp.memLp v).coeFn_toLp)] using
    α.convolutionLp_toL1_ae_eq (L1.integrable_coeFn u) (Lp.memLp v)

end RegularLeftInvariant

end TauCeti.CStarAction
