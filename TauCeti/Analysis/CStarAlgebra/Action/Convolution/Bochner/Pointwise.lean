/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.MeasureTheory.Integral.DominatedConvergence

/-!
# Pointwise formulas for Bochner `L¹` twisted convolution and involution

On a locally compact topological group `G` with a regular left-invariant Borel measure `μ`,
`TauCeti.Analysis.CStarAlgebra.Action.Convolution.L1` identifies
`Completion (ConvolutionAlgebra α μ)` isometrically with `Lp A 1 μ` via
`ConvolutionAlgebra.completionEquivL1` and defines `CStarAction.convolutionLp` and
`CStarAction.twistedInvolutionL1`.

This file derives pointwise almost-everywhere formulas for arbitrary Bochner-integrable functions
by expanding `L¹` classes into absolutely norm-summable series of compactly supported continuous
functions (`ConvolutionAlgebra.exists_hasSum_toL1`), without assuming second countability of `G`
or σ-finiteness of `μ`. It extends `CStarAction.coeFn_twistedInvolutionL1` from Haar measures to
arbitrary regular left-invariant measures (`μ = 0` included) and proves that for any integrable
`f, g : G → A`, the twisted convolution integrand `r ↦ f r * α r (g (r⁻¹ * s))` is
Bochner-integrable for almost every `s` and integrates to `CStarAction.convolutionLp` at `p = 1`.

## Main results

* `TauCeti.CStarAction.coeFn_twistedInvolutionL1_of_regular`: pointwise almost-everywhere formula
  for `twistedInvolutionL1` without `IsOpenPosMeasure`.
* `TauCeti.CStarAction.ae_integrable_convolution_integrand`,
  `TauCeti.CStarAction.convolutionLp_toL1_ae_eq`, `TauCeti.CStarAction.coeFn_convolutionLp`:
  almost-everywhere integrability and pointwise Bochner integral formula for `convolutionLp` at
  `p = 1`.

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

/-- **Pointwise almost-everywhere formula for `twistedInvolutionL1`**: for every `u ∈ Lp A 1 μ`
and any regular left-invariant measure `μ` (including `μ = 0`),
`(α.twistedInvolutionL1 μ u) s = c(s) • α s (star (u s⁻¹))` almost everywhere. -/
theorem coeFn_twistedInvolutionL1_of_regular (u : Lp A 1 μ) :
    α.twistedInvolutionL1 μ u =ᵐ[μ]
      fun s => ((Measure.modularCharacter s : ℝ) : ℂ) • α s (star (u s⁻¹)) := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp [Filter.EventuallyEq]
  · have : μ.IsOpenPosMeasure := isOpenPosMeasure_of_mulLeftInvariant_of_regular
    have : μ.IsHaarMeasure := ⟨⟩
    filter_upwards [α.coeFn_twistedInvolutionL1 u] with s hs
    simpa [Complex.coe_smul] using hs

omit [LocallyCompactSpace G] in
private theorem ae_hasSum_ofConv_of_hasSum_toL1 {ι : Type*} [Countable ι]
    {φ : ι → ConvolutionAlgebra α μ} {u : Lp A 1 μ}
    (hsum : HasSum (fun i => ConvolutionAlgebra.toL1 (φ i)) u)
    (hnorm : Summable fun i => ‖φ i‖) :
    ∀ᵐ r ∂μ, HasSum (fun i => (φ i).ofConv r) (u r) ∧ Summable fun i => ‖(φ i).ofConv r‖ := by
  have heNorm : ∑' i, ‖ConvolutionAlgebra.toL1 (φ i)‖ₑ ≠ ∞ :=
    ENNReal.tsum_coe_ne_top_iff_summable.2 <| NNReal.summable_coe.1 <| by
      simpa only [coe_nnNorm, ConvolutionAlgebra.norm_toL1] using hnorm
  filter_upwards [hsum.tsum_eq ▸ Lp.hasSum_coeFn_tsum heNorm,
    summable_norm_of_tsum_eLpNorm_ne_top le_rfl (by simpa [Lp.eNorm_def] using heNorm),
    ae_all_iff.2 fun i => (ConvolutionAlgebra.coeFn_toL1 (φ i)).mono fun _ h => h]
    with r hr hnr hcoe
  exact ⟨by simpa only [hcoe] using hr, by simpa only [hcoe] using hnr⟩

omit [LocallyCompactSpace G] in
private theorem eLpNorm_integral_norm_convolution_eq (f g : ConvolutionAlgebra α μ) :
    eLpNorm (fun s => ∫ r, ‖f.ofConv r‖ * ‖g.ofConv (r⁻¹ * s)‖ ∂μ) 1 μ =
      ENNReal.ofReal (‖f‖ * ‖g‖) := by
  let W : G → ℝ := fun s => ∫ r, ‖f.ofConv r‖ * ‖g.ofConv (r⁻¹ * s)‖ ∂μ
  have hsupp : ∀ s r, ‖f.ofConv r‖ * ‖g.ofConv (r⁻¹ * s)‖ ≠ 0 →
      r ∈ tsupport f.ofConv ∧ r⁻¹ * s ∈ tsupport g.ofConv := fun s r hsr =>
    ⟨subset_tsupport _ (mem_support.2 fun h => hsr (by simp [h])),
      subset_tsupport _ (mem_support.2 fun h => hsr (by simp [h]))⟩
  have hcont : Continuous (uncurry fun s r => ‖f.ofConv r‖ * ‖g.ofConv (r⁻¹ * s)‖) := by
    rw [uncurry_def]; fun_prop
  have hWi : Integrable W μ :=
    (continuous_integral_of_compact_support μ f.ofConv.hasCompactSupport hcont
      fun s r h => (hsupp s r h).1).integrable_of_hasCompactSupport
      (hasCompactSupport_integral_of_inv_mul_mem μ f.ofConv.hasCompactSupport
        g.ofConv.hasCompactSupport hsupp)
  have hW_nonneg (s : G) : 0 ≤ W s :=
    integral_nonneg fun r => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [(memLp_one_iff_integrable.2 hWi).eLpNorm_eq_integral_rpow_norm one_ne_zero
    ENNReal.one_ne_top]
  simp only [ENNReal.toReal_one, Real.rpow_one, inv_one, Real.norm_of_nonneg (hW_nonneg _)]
  congr 1
  calc
    ∫ s, W s ∂μ = ∫ r, ∫ s, ‖f.ofConv r‖ * ‖g.ofConv (r⁻¹ * s)‖ ∂μ ∂μ :=
      integral_integral_swap_of_hasCompactSupport hcont
        (hasCompactSupport_uncurry_of_inv_mul_mem f.ofConv.hasCompactSupport
          g.ofConv.hasCompactSupport hsupp)
    _ = ∫ r, ‖f.ofConv r‖ * ∫ s, ‖g.ofConv s‖ ∂μ ∂μ := by
      congr 1 with r
      rw [integral_const_mul, integral_mul_left_eq_self (fun s => ‖g.ofConv s‖) r⁻¹]
    _ = ‖f‖ * ‖g‖ := by
      rw [integral_mul_const, ConvolutionAlgebra.norm_eq_integral_norm,
        ConvolutionAlgebra.norm_eq_integral_norm]

omit [LocallyCompactSpace G] in
private theorem ae_summable_integral_norm_of_summable
    {φ ψ : ℕ → ConvolutionAlgebra α μ} (hφ : Summable fun m => ‖φ m‖)
    (hψ : Summable fun n => ‖ψ n‖) :
    ∀ᵐ s ∂μ, Summable fun p : ℕ × ℕ =>
      ∫ r, ‖(φ p.1).ofConv r * α r ((ψ p.2).ofConv (r⁻¹ * s))‖ ∂μ := by
  have hprod : Summable fun p : ℕ × ℕ => ‖φ p.1‖ * ‖ψ p.2‖ :=
    Summable.mul_of_nonneg (f := fun m => ‖φ m‖) (g := fun n => ‖ψ n‖) hφ hψ
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  let W : ℕ × ℕ → G → ℝ := fun p s => ∫ r, ‖(φ p.1).ofConv r‖ * ‖(ψ p.2).ofConv (r⁻¹ * s)‖ ∂μ
  have hW_tsum : ∑' p : ℕ × ℕ, eLpNorm (W p) 1 μ ≠ ∞ := by
    simp_rw [W, α.eLpNorm_integral_norm_convolution_eq]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      hprod]
    exact ENNReal.ofReal_ne_top
  filter_upwards [summable_norm_of_tsum_eLpNorm_ne_top le_rfl hW_tsum] with s hsW
  refine .of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun p => ?_) hsW
  refine (integral_mono (α.integrable_integrand (φ p.1).ofConv (ψ p.2).ofConv μ s).norm ?_
    fun r => ?_).trans (le_abs_self (W p s))
  · exact (by fun_prop : Continuous fun r => ‖(φ p.1).ofConv r‖ * ‖(ψ p.2).ofConv (r⁻¹ * s)‖)
      |>.integrable_of_hasCompactSupport
        ((φ p.1).ofConv.hasCompactSupport.mono' fun r hr =>
          subset_tsupport _ (mem_support.2 fun h => hr (by simp [h])))
  · simpa [StarAlgEquiv.norm_map] using
      norm_mul_le ((φ p.1).ofConv r) (α r ((ψ p.2).ofConv (r⁻¹ * s)))

private theorem ae_hasSum_ofConv_mul_of_hasSum_toL1
    {φ ψ : ℕ → ConvolutionAlgebra α μ} {u v : Lp A 1 μ}
    (hφ_sum : HasSum (fun m => ConvolutionAlgebra.toL1 (φ m)) u)
    (hφ_norm : Summable fun m => ‖φ m‖)
    (hψ_sum : HasSum (fun n => ConvolutionAlgebra.toL1 (ψ n)) v)
    (hψ_norm : Summable fun n => ‖ψ n‖) :
    ∀ᵐ s ∂μ, HasSum (fun p : ℕ × ℕ => (φ p.1 * ψ p.2).ofConv s)
      (α.convolutionLp μ 1 ENNReal.one_ne_top u v s) := by
  have hsymm {χ : ℕ → ConvolutionAlgebra α μ} {w : Lp A 1 μ}
      (h : HasSum (fun n => ConvolutionAlgebra.toL1 (χ n)) w) :
      HasSum (fun n => (χ n : Completion (ConvolutionAlgebra α μ)))
        ((ConvolutionAlgebra.completionEquivL1 α μ).symm w) := by
    simpa only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      ConvolutionAlgebra.completionEquivL1_symm_toL1] using
      (ConvolutionAlgebra.completionEquivL1 α μ).symm.toLinearIsometry.toContinuousLinearMap.hasSum
        h
  have hxy_norm : Summable fun p : ℕ × ℕ => ‖(φ p.1 * ψ p.2 : ConvolutionAlgebra α μ)‖ :=
    .of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_mul_le _ _)
      (Summable.mul_of_nonneg (f := fun m => ‖φ m‖) (g := fun n => ‖ψ n‖) hφ_norm hψ_norm
        (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))
  have hxy_summable : Summable fun p : ℕ × ℕ =>
      ((φ p.1 * ψ p.2 : ConvolutionAlgebra α μ) : Completion (ConvolutionAlgebra α μ)) :=
    .of_norm (by simpa only [Completion.norm_coe] using hxy_norm)
  have hxy_sum : HasSum (fun p : ℕ × ℕ =>
      ((φ p.1 * ψ p.2 : ConvolutionAlgebra α μ) : Completion (ConvolutionAlgebra α μ)))
      ((ConvolutionAlgebra.completionEquivL1 α μ).symm u *
        (ConvolutionAlgebra.completionEquivL1 α μ).symm v) := by
    simpa only [Completion.coe_mul'] using (hsymm hφ_sum).mul (hsymm hψ_sum)
      (by simpa only [← Completion.coe_mul'] using hxy_summable)
  have huv_sum : HasSum (fun p : ℕ × ℕ => ConvolutionAlgebra.toL1 (φ p.1 * ψ p.2))
      (α.convolutionLp μ 1 ENNReal.one_ne_top u v) := by
    simpa only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      ConvolutionAlgebra.completionEquivL1_coe,
      ← ConvolutionAlgebra.completionEquivL1_symm_convolutionLp,
      LinearIsometryEquiv.apply_symm_apply] using
      (ConvolutionAlgebra.completionEquivL1 α μ).toLinearIsometry.toContinuousLinearMap.hasSum
        hxy_sum
  exact (α.ae_hasSum_ofConv_of_hasSum_toL1 huv_sum hxy_norm).mono fun _ hs => hs.1

private theorem ae_integrable_and_convolutionLp_toL1_ae_eq {f g : G → A}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    ∀ᵐ s ∂μ, Integrable (fun r => f r * α r (g (r⁻¹ * s))) μ ∧
      α.convolutionLp μ 1 ENNReal.one_ne_top (hf.toL1 f) (hg.toL1 g) s =
        ∫ r, f r * α r (g (r⁻¹ * s)) ∂μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · have : μ.IsOpenPosMeasure := isOpenPosMeasure_of_mulLeftInvariant_of_regular
    have : μ.IsHaarMeasure := ⟨⟩
    obtain ⟨φ, hφ_sum, hφ_norm⟩ := ConvolutionAlgebra.exists_hasSum_toL1 α (hf.toL1 f)
    obtain ⟨ψ, hψ_sum, hψ_norm⟩ := ConvolutionAlgebra.exists_hasSum_toL1 α (hg.toL1 g)
    have hae_of {k : G → A} (hk : Integrable k μ) {χ : ℕ → ConvolutionAlgebra α μ}
        (hs : HasSum (fun n => ConvolutionAlgebra.toL1 (χ n)) (hk.toL1 k))
        (hn : Summable fun n => ‖χ n‖) :
        ∀ᵐ t ∂μ, HasSum (fun n => (χ n).ofConv t) (k t) ∧ Summable fun n => ‖(χ n).ofConv t‖ := by
      filter_upwards [α.ae_hasSum_ofConv_of_hasSum_toL1 hs hn, hk.coeFn_toL1] with t ⟨ht, hnt⟩ hkt
      exact ⟨hkt ▸ ht, hnt⟩
    filter_upwards [α.ae_summable_integral_norm_of_summable hφ_norm hψ_norm,
      α.ae_hasSum_ofConv_mul_of_hasSum_toL1 hφ_sum hφ_norm hψ_sum hψ_norm]
      with s hh_sum_int hsuv
    let h : ℕ × ℕ → G → A := fun p r => (φ p.1).ofConv r * α r ((ψ p.2).ofConv (r⁻¹ * s))
    have hh_int (p : ℕ × ℕ) : Integrable (h p) μ :=
      α.integrable_integrand (φ p.1).ofConv (ψ p.2).ofConv μ s
    have hae_h : ∀ᵐ r ∂μ, ∑' p : ℕ × ℕ, h p r = f r * α r (g (r⁻¹ * s)) := by
      filter_upwards [hae_of hf hφ_sum hφ_norm,
        (Measure.quasiMeasurePreserving_inv_mul_of_regular μ s).ae (hae_of hg hψ_sum hψ_norm)]
        with r ⟨hfr, hfnorm⟩ ⟨hgr, hgnorm⟩
      have hαg_sum : HasSum (fun n => α r ((ψ n).ofConv (r⁻¹ * s))) (α r (g (r⁻¹ * s))) :=
        hgr.map (α r) (StarAlgEquiv.isometry (α r)).continuous
      have hmul_summable : Summable fun p : ℕ × ℕ => h p r :=
        .of_norm <| .of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_mul_le _ _)
          (Summable.mul_of_nonneg (f := fun m => ‖(φ m).ofConv r‖)
            (g := fun n => ‖α r ((ψ n).ofConv (r⁻¹ * s))‖) hfnorm
            (by simpa only [StarAlgEquiv.norm_map] using hgnorm)
            (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))
      exact (hfr.mul hαg_sum hmul_summable).tsum_eq
    refine ⟨(integrable_tsum_of_summable_integral_norm hh_int hh_sum_int).congr hae_h, ?_⟩
    have hint_sum := hasSum_integral_of_summable_integral_norm hh_int hh_sum_int
    have hh_eq (p : ℕ × ℕ) : ∫ r, h p r ∂μ = (φ p.1 * ψ p.2).ofConv s := by
      simp [h, ConvolutionAlgebra.ofConv_mul, α.convolution_apply]
    simp_rw [hh_eq, integral_congr_ae hae_h] at hint_sum
    exact hsuv.unique hint_sum

/-- **Almost-everywhere integrability of the twisted convolution integrand**: for any
Bochner-integrable `f, g : G → A` on a locally compact group with a regular left-invariant measure,
`r ↦ f r * α r (g (r⁻¹ * s))` is Bochner-integrable for almost every `s : G`. -/
theorem ae_integrable_convolution_integrand {f g : G → A}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    ∀ᵐ s ∂μ, Integrable (fun r => f r * α r (g (r⁻¹ * s))) μ :=
  (α.ae_integrable_and_convolutionLp_toL1_ae_eq hf hg).mono fun _ hs => hs.1

/-- **Pointwise formula for twisted `L¹` convolution**: for any Bochner-integrable `f, g : G → A`
on a locally compact group with a regular left-invariant measure, `convolutionLp` at `p = 1` of
their `L¹` classes is represented almost everywhere by `s ↦ ∫ r, f r * α r (g (r⁻¹ * s)) dμ`. -/
theorem convolutionLp_toL1_ae_eq {f g : G → A} (hf : Integrable f μ) (hg : Integrable g μ) :
    α.convolutionLp μ 1 ENNReal.one_ne_top (hf.toL1 f) (hg.toL1 g) =ᵐ[μ]
      fun s => ∫ r, f r * α r (g (r⁻¹ * s)) ∂μ :=
  (α.ae_integrable_and_convolutionLp_toL1_ae_eq hf hg).mono fun _ hs => hs.2

/-- For arbitrary `u, v ∈ Lp A 1 μ` on a locally compact group with a regular left-invariant
measure, `convolutionLp` at `p = 1` is represented almost everywhere by
`s ↦ ∫ r, u r * α r (v (r⁻¹ * s)) dμ`. -/
theorem coeFn_convolutionLp (u v : Lp A 1 μ) :
    α.convolutionLp μ 1 ENNReal.one_ne_top u v =ᵐ[μ]
      fun s => ∫ r, u r * α r (v (r⁻¹ * s)) ∂μ := by
  simpa using α.convolutionLp_toL1_ae_eq (L1.integrable_coeFn u) (L1.integrable_coeFn v)

end RegularLeftInvariant

end TauCeti.CStarAction
