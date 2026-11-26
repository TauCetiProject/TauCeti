/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.L1
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import TauCeti.Analysis.Normed.Group.Completion
import TauCeti.Analysis.Normed.Module.InfiniteSum
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.DominatedConvergence

/-!
# Pointwise formulas for Bochner `L¹` twisted convolution

On a locally compact topological group `G` with a regular left-invariant Borel measure `μ`,
`TauCeti.Analysis.CStarAlgebra.Action.Convolution.L1` identifies
`Completion (ConvolutionAlgebra α μ)` isometrically with `Lp A 1 μ` via
`ConvolutionAlgebra.completionEquivL1` and defines `CStarAction.convolutionL1` on `Lp A 1 μ`.

This file derives pointwise almost-everywhere formulas for arbitrary Bochner-integrable functions
`f, g : G → A` by expanding `L¹` classes into absolutely norm-summable series of compactly
supported continuous functions (`UniformSpace.Completion.exists_hasSum_coe_of_norm_lt` transported
across `ConvolutionAlgebra.completionEquivL1`), without assuming second countability of `G` or
σ-finiteness of `μ`. It proves that the twisted convolution integrand
`r ↦ f r * α r (g (r⁻¹ * s))` is Bochner-integrable for almost every `s` and integrates to
`CStarAction.convolutionL1`.

## Main results

* `TauCeti.CStarAction.ae_integrable_convolution_integrand`,
  `TauCeti.CStarAction.convolutionL1_toL1_ae_eq`, `TauCeti.CStarAction.coeFn_convolutionL1`:
  almost-everywhere integrability and pointwise Bochner integral formula for `convolutionL1`.

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
  {μ : Measure G} [μ.IsMulLeftInvariant] [μ.Regular]

omit [μ.IsMulLeftInvariant] in
private theorem exists_hasSum_toLp_of_L1 (α : CStarAction G A) (u : Lp A 1 μ) :
    ∃ φ : ℕ → C_c(G, A),
      HasSum (fun n => CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ n)) u ∧
      Summable fun n => ‖CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ n)‖ := by
  let x := (ConvolutionAlgebra.completionEquivL1 α μ).symm u
  obtain ⟨w, hw_sum, hw_norm, -⟩ :=
    Completion.exists_hasSum_coe_of_norm_lt x (lt_add_one ‖x‖)
  refine ⟨fun n => (w n).ofConv, ?_, ?_⟩
  · have hmap := hw_sum.map (ConvolutionAlgebra.completionEquivL1 α μ)
      (ConvolutionAlgebra.completionEquivL1 α μ).continuous
    simpa only [x, Function.comp_def, LinearIsometryEquiv.apply_symm_apply,
      ConvolutionAlgebra.completionEquivL1_coe, ConvolutionAlgebra.toL1_eq_toLp] using hmap
  · simpa only [← ConvolutionAlgebra.toL1_eq_toLp, ← ConvolutionAlgebra.toL1LI_apply,
      LinearIsometry.norm_map] using hw_norm

omit [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G] [μ.IsMulLeftInvariant] in
private theorem ae_hasSum_of_hasSum_toLp {ι : Type*} [Countable ι]
    {ψ : ι → C_c(G, A)} {v : Lp A 1 μ}
    (hsum : HasSum (fun i => CompactlySupportedContinuousMap.toLp 1 μ ℂ (ψ i)) v)
    (hnorm : Summable fun i => ‖CompactlySupportedContinuousMap.toLp 1 μ ℂ (ψ i)‖) :
    ∀ᵐ t ∂μ, HasSum (fun i => ψ i t) (v t) ∧ Summable fun i => ‖ψ i t‖ := by
  have heNorm : ∑' i, ‖CompactlySupportedContinuousMap.toLp 1 μ ℂ (ψ i)‖ₑ ≠ ∞ :=
    tsum_eNorm_ne_top_iff_summable_norm.2 hnorm
  filter_upwards [Lp.hasSum_coeFn_tsum heNorm,
    summable_norm_of_tsum_eLpNorm_ne_top Fact.out (by simpa [Lp.eNorm_def] using heNorm),
    ae_all_iff.2 fun i => CompactlySupportedContinuousMap.coeFn_toLp (p := 1) (μ := μ) ℂ (ψ i)]
    with t ht hnt hcoe
  rw [hsum.tsum_eq] at ht
  simp only [hcoe] at ht hnt
  exact ⟨ht, hnt⟩

variable (α : CStarAction G A)

private theorem ae_summable_integral_norm_of_summable {φ ψ : ℕ → C_c(G, A)}
    (hφ : Summable fun m => ‖CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ m)‖)
    (hψ : Summable fun n => ‖CompactlySupportedContinuousMap.toLp 1 μ ℂ (ψ n)‖) :
    ∀ᵐ s ∂μ, Summable fun q : ℕ × ℕ =>
      ∫ r, ‖φ q.1 r * α r (ψ q.2 (r⁻¹ * s))‖ ∂μ := by
  have hprod : Summable fun q : ℕ × ℕ =>
      ‖CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ q.1)‖ *
        ‖CompactlySupportedContinuousMap.toLp 1 μ ℂ (ψ q.2)‖ :=
    Summable.mul_of_nonneg hφ hψ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  let W : ℕ × ℕ → G → ℝ := fun q s => ∫ r, ‖φ q.1 r‖ * ‖ψ q.2 (r⁻¹ * s)‖ ∂μ
  have hW_eLpNorm (q : ℕ × ℕ) :
      eLpNorm (W q) 1 μ ≤
        ENNReal.ofReal (‖CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ q.1)‖ *
          ‖CompactlySupportedContinuousMap.toLp 1 μ ℂ (ψ q.2)‖) := by
    have hnc : Continuous fun r => ‖φ q.1 r‖ := (φ q.1).continuous.norm
    have hns : HasCompactSupport fun r => ‖φ q.1 r‖ := (φ q.1).hasCompactSupport.norm
    have hmc : Continuous fun s => ‖ψ q.2 s‖ := (ψ q.2).continuous.norm
    have hms : HasCompactSupport fun s => ‖ψ q.2 s‖ := (ψ q.2).hasCompactSupport.norm
    have hni : Integrable (fun r => ‖φ q.1 r‖) μ := hnc.integrable_of_hasCompactSupport hns
    have hmi : Integrable (fun s => ‖ψ q.2 s‖) μ := hmc.integrable_of_hasCompactSupport hms
    have hfn_eq :
        hni.toL1 (fun r => ‖φ q.1 r‖) =
          Lp.normLp (CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ q.1)) := by
      refine Lp.ext ?_
      filter_upwards [hni.coeFn_toL1,
        Lp.coeFn_normLp (CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ q.1)),
        CompactlySupportedContinuousMap.coeFn_toLp (p := 1) (μ := μ) ℂ (φ q.1)]
        with r h₁ h₂ h₃
      rw [h₁, h₂, h₃]
    have hgn_eq :
        hmi.toL1 (fun s => ‖ψ q.2 s‖) =
          Lp.normLp (CompactlySupportedContinuousMap.toLp 1 μ ℂ (ψ q.2)) := by
      refine Lp.ext ?_
      filter_upwards [hmi.coeFn_toL1,
        Lp.coeFn_normLp (CompactlySupportedContinuousMap.toLp 1 μ ℂ (ψ q.2)),
        CompactlySupportedContinuousMap.coeFn_toLp (p := 1) (μ := μ) ℂ (ψ q.2)]
        with s h₁ h₂ h₃
      rw [h₁, h₂, h₃]
    calc
      eLpNorm (W q) 1 μ
          = eLpNorm (Lp.convolutionL μ 1 ENNReal.one_ne_top (hni.toL1 fun r => ‖φ q.1 r‖)
              (hmi.toL1 fun s => ‖ψ q.2 s‖)) 1 μ :=
            eLpNorm_congr_ae (Lp.convolutionL_toL1_ae_eq hnc hns hmc hms).symm
      _ = ENNReal.ofReal ‖Lp.convolutionL μ 1 ENNReal.one_ne_top (hni.toL1 fun r => ‖φ q.1 r‖)
            (hmi.toL1 fun s => ‖ψ q.2 s‖)‖ := by
          rw [← Lp.eNorm_def, ← ofReal_norm]
      _ ≤ ENNReal.ofReal (‖hni.toL1 fun r => ‖φ q.1 r‖‖ * ‖hmi.toL1 fun s => ‖ψ q.2 s‖‖) :=
          ENNReal.ofReal_le_ofReal (Lp.norm_convolutionL_apply_le _ _)
      _ = ENNReal.ofReal (‖CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ q.1)‖ *
            ‖CompactlySupportedContinuousMap.toLp 1 μ ℂ (ψ q.2)‖) := by
          rw [hfn_eq, hgn_eq, Lp.norm_normLp, Lp.norm_normLp]
  have hW_tsum : ∑' q : ℕ × ℕ, eLpNorm (W q) 1 μ ≠ ∞ := by
    refine lt_top_iff_ne_top.1 ?_
    calc
      ∑' q : ℕ × ℕ, eLpNorm (W q) 1 μ
          ≤ ∑' q : ℕ × ℕ,
              ENNReal.ofReal (‖CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ q.1)‖ *
                ‖CompactlySupportedContinuousMap.toLp 1 μ ℂ (ψ q.2)‖) :=
            tsum_le_tsum hW_eLpNorm
      _ = ENNReal.ofReal (∑' q : ℕ × ℕ,
            ‖CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ q.1)‖ *
              ‖CompactlySupportedContinuousMap.toLp 1 μ ℂ (ψ q.2)‖) := by
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

private theorem ae_hasSum_convolution_of_hasSum_toLp {φ ψ : ℕ → C_c(G, A)} {u v : Lp A 1 μ}
    (hφ_sum : HasSum (fun m => CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ m)) u)
    (hφ_norm : Summable fun m => ‖CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ m)‖)
    (hψ_sum : HasSum (fun n => CompactlySupportedContinuousMap.toLp 1 μ ℂ (ψ n)) v)
    (hψ_norm : Summable fun n => ‖CompactlySupportedContinuousMap.toLp 1 μ ℂ (ψ n)‖) :
    ∀ᵐ s ∂μ, HasSum (fun q : ℕ × ℕ => α.convolution μ (φ q.1) (ψ q.2) s)
      (α.convolutionL1 μ u v s) := by
  let F : ℕ × ℕ → Lp A 1 μ := fun q =>
    CompactlySupportedContinuousMap.toLp 1 μ ℂ (α.convolution μ (φ q.1) (ψ q.2))
  have hF_eq (q : ℕ × ℕ) :
      F q = α.convolutionL1 μ (CompactlySupportedContinuousMap.toLp 1 μ ℂ (φ q.1))
        (CompactlySupportedContinuousMap.toLp 1 μ ℂ (ψ q.2)) :=
    (α.convolutionL1_toLp (φ q.1) (ψ q.2)).symm
  have hF_norm : Summable fun q : ℕ × ℕ => ‖F q‖ := by
    refine .of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_)
      (Summable.mul_of_nonneg hφ_norm hψ_norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))
    rw [hF_eq q]
    exact α.norm_convolutionL1_apply_le _ _
  have hF_sum : HasSum F (α.convolutionL1 μ u v) := by
    simpa only [← hF_eq, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply] using
      TauCeti.hasSum_bilinear_of_summable_norm (B := (α.convolutionL1 μ).toLinearMap₁₂)
        (C := 1) (fun x y => by simpa using α.norm_convolutionL1_apply_le x y)
        hφ_sum hψ_sum hφ_norm hψ_norm
  exact (ae_hasSum_of_hasSum_toLp hF_sum hF_norm).mono fun _ hs => hs.1

private theorem ae_integrable_and_convolutionL1_toL1_ae_eq {f g : G → A} (hf : Integrable f μ)
    (hg : Integrable g μ) :
    ∀ᵐ s ∂μ, Integrable (fun r => f r * α r (g (r⁻¹ * s))) μ ∧
      α.convolutionL1 μ (hf.toL1 f) (hg.toL1 g) s = ∫ r, f r * α r (g (r⁻¹ * s)) ∂μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · have : μ.IsOpenPosMeasure := isOpenPosMeasure_of_mulLeftInvariant_of_regular
    have : μ.IsHaarMeasure := ⟨⟩
    obtain ⟨φ, hφ_sum, hφ_norm⟩ := α.exists_hasSum_toLp_of_L1 (hf.toL1 f)
    obtain ⟨ψ, hψ_sum, hψ_norm⟩ := α.exists_hasSum_toLp_of_L1 (hg.toL1 g)
    have hae_f :
        ∀ᵐ r ∂μ, HasSum (fun m => φ m r) (f r) ∧ Summable fun m => ‖φ m r‖ := by
      filter_upwards [ae_hasSum_of_hasSum_toLp hφ_sum hφ_norm, hf.coeFn_toL1]
        with r ⟨hr, hnr⟩ hfr
      exact ⟨hfr ▸ hr, hnr⟩
    have hae_g : ∀ᵐ t ∂μ, HasSum (fun n => ψ n t) (g t) ∧ Summable fun n => ‖ψ n t‖ := by
      filter_upwards [ae_hasSum_of_hasSum_toLp hψ_sum hψ_norm, hg.coeFn_toL1]
        with t ⟨ht, hnt⟩ hgt
      exact ⟨hgt ▸ ht, hnt⟩
    filter_upwards [α.ae_summable_integral_norm_of_summable hφ_norm hψ_norm,
      α.ae_hasSum_convolution_of_hasSum_toLp hφ_sum hφ_norm hψ_sum hψ_norm]
      with s hh_sum_int hsuv
    let h : ℕ × ℕ → G → A := fun q r => φ q.1 r * α r (ψ q.2 (r⁻¹ * s))
    have hh_int (q : ℕ × ℕ) : Integrable (h q) μ :=
      α.integrable_integrand (φ q.1) (ψ q.2) μ s
    have hae_sum : ∀ᵐ r ∂μ, HasSum (fun q : ℕ × ℕ => h q r) (f r * α r (g (r⁻¹ * s))) := by
      filter_upwards [hae_f, (Measure.quasiMeasurePreserving_inv_mul_of_regular μ s).ae hae_g]
        with r ⟨hfr, hfnorm⟩ ⟨hgr, hgnorm⟩
      have hαg_sum : HasSum (fun n => α r (ψ n (r⁻¹ * s))) (α r (g (r⁻¹ * s))) :=
        hgr.map (α r) (StarAlgEquiv.isometry (α r)).continuous
      exact TauCeti.hasSum_bilinear_of_summable_norm
        (B := (ContinuousLinearMap.mul ℂ A).toLinearMap₁₂) (C := 1)
        (fun x y => by simpa using norm_mul_le x y)
        hfr hαg_sum hfnorm (by simpa only [StarAlgEquiv.norm_map] using hgnorm)
    let e : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
    have hint : Integrable (fun r => f r * α r (g (r⁻¹ * s))) μ :=
      TauCeti.integrable_of_hasSum_of_summable_integral_norm (fun n => hh_int (e n))
        (hh_sum_int.comp_injective e.injective) (hae_sum.mono fun _ hr => e.hasSum_iff.2 hr)
    refine ⟨hint, ?_⟩
    have hint_sum := hasSum_integral_of_summable_integral_norm hh_int hh_sum_int
    have hh_eq (q : ℕ × ℕ) : ∫ r, h q r ∂μ = α.convolution μ (φ q.1) (ψ q.2) s := by
      simp [h, α.convolution_apply]
    have hae_tsum : ∀ᵐ r ∂μ, ∑' q : ℕ × ℕ, h q r = f r * α r (g (r⁻¹ * s)) :=
      hae_sum.mono fun _ hr => hr.tsum_eq
    simp_rw [hh_eq, integral_congr_ae hae_tsum] at hint_sum
    exact hsuv.unique hint_sum

/-- **Almost-everywhere integrability of the twisted convolution integrand**: for any
Bochner-integrable `f, g : G → A` on a locally compact group with a regular left-invariant measure,
`r ↦ f r * α r (g (r⁻¹ * s))` is Bochner-integrable for almost every `s : G`. -/
theorem ae_integrable_convolution_integrand {f g : G → A} (hf : Integrable f μ)
    (hg : Integrable g μ) :
    ∀ᵐ s ∂μ, Integrable (fun r => f r * α r (g (r⁻¹ * s))) μ :=
  (α.ae_integrable_and_convolutionL1_toL1_ae_eq hf hg).mono fun _ hs => hs.1

/-- **Pointwise formula for twisted `L¹` convolution**: for any Bochner-integrable `f, g : G → A`
on a locally compact group with a regular left-invariant measure, `convolutionL1` of their classes
is represented almost everywhere by `s ↦ ∫ r, f r * α r (g (r⁻¹ * s)) dμ`. -/
theorem convolutionL1_toL1_ae_eq {f g : G → A} (hf : Integrable f μ) (hg : Integrable g μ) :
    α.convolutionL1 μ (hf.toL1 f) (hg.toL1 g) =ᵐ[μ] fun s => ∫ r, f r * α r (g (r⁻¹ * s)) ∂μ :=
  (α.ae_integrable_and_convolutionL1_toL1_ae_eq hf hg).mono fun _ hs => hs.2

/-- For arbitrary `u, v ∈ Lp A 1 μ` on a locally compact group with a regular left-invariant
measure, `convolutionL1` is represented almost everywhere by
`s ↦ ∫ r, u r * α r (v (r⁻¹ * s)) dμ`. -/
theorem coeFn_convolutionL1 (u v : Lp A 1 μ) :
    α.convolutionL1 μ u v =ᵐ[μ] fun s => ∫ r, u r * α r (v (r⁻¹ * s)) ∂μ := by
  simpa only [Integrable.toL1_coeFn] using
    α.convolutionL1_toL1_ae_eq (L1.integrable_coeFn u) (L1.integrable_coeFn v)

end RegularLeftInvariant

end TauCeti.CStarAction
