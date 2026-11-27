/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.Divisor
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.CanonicalProduct.Quadratic.Basic

/-!
# Paired quadratic divisor product for even entire functions with imaginary zeros

When an even entire function `g` with `g 0 ≠ 0` has all its zeros on the imaginary axis, pairing
opposite roots `±ρ` collapses `TauCeti.divisorProductOne g z` into a product of paired quadratic
factors `1 + z ^ 2 / (Im ρ) ^ 2` over the upper half-plane
(`TauCeti.divisorProductOne_eq_tprod_im_pos`), which can be flattened into a `0`-padded `ℕ`-indexed
sequence (`TauCeti.exists_paired_seq_divisorProductOne`).

## Main results

* `TauCeti.divisorProductOne_eq_tprod_im_pos`: regroups `divisorProductOne g z` over
  `{ρ ∈ d.support | 0 < ρ.im}`.
* `TauCeti.exists_paired_seq_divisorProductOne`: represents `divisorProductOne g` by a nonnegative
  sequence `γ : ℕ → ℝ` with `Summable (fun n ↦ (γ n)⁻¹ ^ 2)`.
-/

public section

open Complex Filter Metric Topology
open scoped BigOperators

namespace TauCeti

/-- Grouping each upper-half-plane zero `ρ` (`Im ρ > 0`) of an even entire function `g` with `-ρ`
rewrites `divisorProductOne g z` as a product over `{ρ ∈ d.support | 0 < ρ.im}`. -/
theorem divisorProductOne_eq_tprod_im_pos {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hg0 : g 0 ≠ 0) (heven : g.Even) (hzeros : ∀ z : ℂ, g z = 0 → z.re = 0)
    (hsum : Summable (fun ρ : (MeromorphicOn.divisor g Set.univ).support ↦
      ((MeromorphicOn.divisor g Set.univ ρ).toNat : ℝ) * ‖(ρ : ℂ)⁻¹‖ ^ 2))
    (z : ℂ) :
    divisorProductOne g z =
      ∏' ρ : {ρ : ℂ | ρ ∈ (MeromorphicOn.divisor g Set.univ).support ∧ 0 < ρ.im},
        (1 + z ^ 2 / (ρ.val.im : ℂ) ^ 2) ^ (MeromorphicOn.divisor g Set.univ ρ.val).toNat := by
  have ha : AnalyticOnNhd ℂ g Set.univ := Complex.analyticOnNhd_univ_iff_differentiable.mpr hg
  have h0_notMem : (0 : ℂ) ∉ (MeromorphicOn.divisor g Set.univ).support :=
    (hg.analyticAt 0).notMem_divisor_support_of_ne_zero hg0
  have hsupp_re : (MeromorphicOn.divisor g Set.univ).support ⊆ {z : ℂ | z.re = 0} :=
    ha.support_divisor_subset fun z _ hz ↦ Set.mem_ofPred.2 (hzeros z hz)
  have hdiv_neg (ρ : ℂ) :
      MeromorphicOn.divisor g Set.univ (-ρ) = MeromorphicOn.divisor g Set.univ ρ :=
    ha.divisor_neg_eq_of_even heven ρ
  rw [divisorProductOne_def]
  generalize MeromorphicOn.divisor g Set.univ = d at h0_notMem hsupp_re hdiv_neg hsum ⊢
  have hsupp_im_ne {ρ : ℂ} (hρ : ρ ∈ d.support) : ρ.im ≠ 0 := fun him ↦ by
    have hρ0 : ρ = 0 := Complex.ext (by simp [Set.mem_ofPred.1 (hsupp_re hρ)]) (by simp [him])
    exact h0_notMem (hρ0 ▸ hρ)
  have hsupp_neg {ρ : ℂ} (hρ : ρ ∈ d.support) : -ρ ∈ d.support := by
    rw [Function.mem_support, hdiv_neg]; exact hρ
  let e := Complex.upperHalfSumEquivOfNegInvariant hsupp_neg hsupp_im_ne
  let F : d.support → ℂ := fun σ ↦ weierstrassFactor 1 ((σ : ℂ)⁻¹ * z) ^ (d σ).toNat
  let Spos : Set ℂ := {ρ : ℂ | ρ ∈ d.support ∧ 0 < ρ.im}
  have hSpos_sub : Spos ⊆ d.support := fun _ h ↦ h.1
  have hsum_pos : Summable (fun ρ : Spos ↦ ((d ρ.val).toNat : ℝ) * ‖(ρ.val)⁻¹‖ ^ 2) :=
    (hsum.comp_injective (Set.inclusion_injective hSpos_sub)).congr fun _ ↦
      by simp only [Function.comp_apply]
  have h1 : Multipliable (fun ρ ↦ F (e (Sum.inl ρ))) := by
    have h := ((Complex.hasProdLocallyUniformlyOn_weierstrassFactor_one_pow
      (fun ρ : Spos ↦ (ρ.val)⁻¹)
      (fun ρ ↦ (d ρ.val).toNat) hsum_pos).hasProd (Set.mem_univ z)).multipliable
    simpa only [F, e, Spos, Complex.coe_upperHalfSumEquivOfNegInvariant_inl] using h
  have h2 : Multipliable (fun ρ ↦ F (e (Sum.inr ρ))) := by
    have hsum_neg : Summable (fun ρ : Spos ↦ ((d ρ.val).toNat : ℝ) * ‖(-(ρ.val))⁻¹‖ ^ 2) := by
      simpa only [inv_neg, norm_neg] using hsum_pos
    have h := ((Complex.hasProdLocallyUniformlyOn_weierstrassFactor_one_pow
      (fun ρ : Spos ↦ (-(ρ.val))⁻¹)
      (fun ρ ↦ (d ρ.val).toNat) hsum_neg).hasProd (Set.mem_univ z)).multipliable
    simpa only [F, e, Spos, Complex.coe_upperHalfSumEquivOfNegInvariant_inr, hdiv_neg] using h
  -- Reindex along `±ρ`, split the sum product, and collapse each pair.
  calc (∏' σ : d.support, F σ)
      = ∏' p, F (e p) := (e.tprod_eq F).symm
    _ = (∏' ρ, F (e (Sum.inl ρ))) * (∏' ρ, F (e (Sum.inr ρ))) := h1.tprod_sum h2
    _ = ∏' ρ, F (e (Sum.inl ρ)) * F (e (Sum.inr ρ)) := (h1.tprod_mul h2).symm
    _ = ∏' ρ : {ρ : ℂ | ρ ∈ d.support ∧ 0 < ρ.im},
          (1 + z ^ 2 / (ρ.val.im : ℂ) ^ 2) ^ (d ρ.val).toNat := by
        refine tprod_congr fun ρ ↦ ?_
        dsimp only [F]
        rw [Complex.coe_upperHalfSumEquivOfNegInvariant_inl,
          Complex.coe_upperHalfSumEquivOfNegInvariant_inr, hdiv_neg]
        exact weierstrassFactor_one_imag_pair (Set.mem_ofPred.1 (hsupp_re ρ.property.1))
          (d ρ.val).toNat z

/-- Every entire even function `g` with `g 0 ≠ 0`, zeros on the imaginary axis, and inverse-square
summable divisor has `divisorProductOne g` represented by a nonnegative sequence `γ : ℕ → ℝ` with
`Summable (fun n ↦ (γ n)⁻¹ ^ 2)`. -/
theorem exists_paired_seq_divisorProductOne {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hg0 : g 0 ≠ 0) (heven : g.Even) (hzeros : ∀ z : ℂ, g z = 0 → z.re = 0)
    (hsum : Summable (fun ρ : (MeromorphicOn.divisor g Set.univ).support ↦
      ((MeromorphicOn.divisor g Set.univ ρ).toNat : ℝ) * ‖(ρ : ℂ)⁻¹‖ ^ 2)) :
    ∃ γ : ℕ → ℝ, (∀ n, 0 ≤ γ n) ∧ Summable (fun n ↦ (γ n)⁻¹ ^ 2) ∧
      ∀ z : ℂ, divisorProductOne g z =
        ∏' n : ℕ, (1 + z ^ 2 / (γ n : ℂ) ^ 2) := by
  have hprod_pos := divisorProductOne_eq_tprod_im_pos hg hg0 heven hzeros hsum
  have hsupp_re : (MeromorphicOn.divisor g Set.univ).support ⊆ {z : ℂ | z.re = 0} :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hg).support_divisor_subset
      fun z _ hz ↦ Set.mem_ofPred.2 (hzeros z hz)
  generalize MeromorphicOn.divisor g Set.univ = d at hprod_pos hsupp_re hsum
  let Spos : Set ℂ := {ρ : ℂ | ρ ∈ d.support ∧ 0 < ρ.im}
  have hSpos_sub : Spos ⊆ d.support := fun _ h ↦ h.1
  have hSpos_sum : Summable (fun ρ : Spos ↦ ((d ρ.val).toNat : ℝ) * (ρ.val.im)⁻¹ ^ 2) := by
    refine (hsum.comp_injective (Set.inclusion_injective hSpos_sub)).congr fun ρ ↦ ?_
    have hnorm : ‖(ρ.val)⁻¹‖ = (ρ.val.im)⁻¹ := by
      rw [norm_inv, ← Complex.abs_im_eq_norm.mpr (Set.mem_ofPred.1 (hsupp_re ρ.property.1)),
        abs_of_pos ρ.property.2]
    dsimp only [Function.comp_apply, Set.inclusion]
    rw [hnorm]
  obtain ⟨γ, hγ_nonneg, hγ_sum, hγ_prod⟩ :=
    exists_nat_seq_tprod_one_add_div_sq (fun ρ : Spos ↦ ρ.property.2) hSpos_sum
  exact ⟨γ, hγ_nonneg, hγ_sum, fun z ↦ (hprod_pos z).trans (hγ_prod z)⟩

end TauCeti
