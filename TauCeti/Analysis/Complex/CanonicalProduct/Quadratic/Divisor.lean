/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.Divisor
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

private theorem re_eq_zero_of_mem_divisor_support {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hzeros : ∀ z : ℂ, g z = 0 → z.re = 0) {ρ : ℂ}
    (hρ : ρ ∈ (MeromorphicOn.divisor g Set.univ).support) : ρ.re = 0 :=
  hzeros ρ ((hg.analyticAt ρ).apply_eq_zero_of_divisor_ne_zero hρ)

/-- Pairing equivalence between `(Σ _ : {ρ ∈ S | 0 < ρ.im}, Bool)` and `S` for a
negation-invariant set `S ⊆ ℂ` with `ρ.im ≠ 0` on `S`, sending `(ρ, true) ↦ ρ` and
`(ρ, false) ↦ -ρ`. -/
private noncomputable def imagPairEquiv {S : Set ℂ} (hneg : ∀ {ρ}, ρ ∈ S → -ρ ∈ S)
    (him : ∀ {ρ}, ρ ∈ S → ρ.im ≠ 0) :
    (Σ _ : {ρ : ℂ | ρ ∈ S ∧ 0 < ρ.im}, Bool) ≃ S :=
  let posSub : {ρ : ℂ | ρ ∈ S ∧ 0 < ρ.im} ≃ {σ : S // 0 < (σ : ℂ).im} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ S) (fun z : ℂ ↦ 0 < z.im)).symm
  let negOnS : S ≃ S :=
    Equiv.subtypeEquiv (Equiv.neg ℂ) fun _ ↦
      ⟨fun h ↦ hneg h, fun h ↦ by simpa using hneg h⟩
  let posToCompl : {σ : S // 0 < (σ : ℂ).im} ≃ {σ : S // ¬ 0 < (σ : ℂ).im} :=
    Equiv.subtypeEquiv negOnS fun σ ↦ by
      simp only [negOnS, Equiv.subtypeEquiv_apply, Equiv.neg_apply, neg_im]
      exact ⟨fun h ↦ not_lt.mpr (neg_nonpos.mpr h.le),
        fun h ↦ lt_of_le_of_ne (neg_nonpos.mp (not_lt.mp h)) (him σ.property).symm⟩
  (Equiv.sigmaEquivProd _ Bool).trans <|
    (Equiv.prodComm _ Bool).trans <|
      (Equiv.boolProdEquivSum _).trans <|
        (Equiv.sumComm _ _).trans <|
          (Equiv.sumCongr posSub (posSub.trans posToCompl)).trans
            (Equiv.sumCompl (fun σ : S ↦ 0 < (σ : ℂ).im))

private theorem imagPairEquiv_true {S : Set ℂ} (hneg : ∀ {ρ}, ρ ∈ S → -ρ ∈ S)
    (him : ∀ {ρ}, ρ ∈ S → ρ.im ≠ 0) (ρ : {ρ : ℂ | ρ ∈ S ∧ 0 < ρ.im}) :
    ((imagPairEquiv hneg him ⟨ρ, true⟩ : S) : ℂ) = ρ :=
  rfl

private theorem imagPairEquiv_false {S : Set ℂ} (hneg : ∀ {ρ}, ρ ∈ S → -ρ ∈ S)
    (him : ∀ {ρ}, ρ ∈ S → ρ.im ≠ 0) (ρ : {ρ : ℂ | ρ ∈ S ∧ 0 < ρ.im}) :
    ((imagPairEquiv hneg him ⟨ρ, false⟩ : S) : ℂ) = -ρ :=
  rfl

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
  have h0_notMem : (0 : ℂ) ∉ (MeromorphicOn.divisor g Set.univ).support :=
    (hg.analyticAt 0).notMem_divisor_support_of_ne_zero hg0
  have hsupp_re {ρ : ℂ} (hρ : ρ ∈ (MeromorphicOn.divisor g Set.univ).support) : ρ.re = 0 :=
    re_eq_zero_of_mem_divisor_support hg hzeros hρ
  have hdiv_neg (ρ : ℂ) :
      MeromorphicOn.divisor g Set.univ (-ρ) = MeromorphicOn.divisor g Set.univ ρ :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hg).divisor_neg_eq_of_even heven ρ
  have hF_mult : Multipliable (fun σ : (MeromorphicOn.divisor g Set.univ).support ↦
      weierstrassFactor 1 ((σ : ℂ)⁻¹ * z) ^ (MeromorphicOn.divisor g Set.univ σ).toNat) :=
    (hasProd_divisorProductOne_support hsum z).multipliable
  rw [divisorProductOne_def]
  generalize MeromorphicOn.divisor g Set.univ = d at h0_notMem hsupp_re hdiv_neg hsum hF_mult ⊢
  have hsupp_im_ne {ρ : ℂ} (hρ : ρ ∈ d.support) : ρ.im ≠ 0 := fun him ↦ by
    have hρ0 : ρ = 0 := Complex.ext (by simp [hsupp_re hρ]) (by simp [him])
    exact h0_notMem (hρ0 ▸ hρ)
  have hsupp_neg {ρ : ℂ} (hρ : ρ ∈ d.support) : -ρ ∈ d.support := by
    rw [Function.mem_support, hdiv_neg]; exact hρ
  let e := imagPairEquiv hsupp_neg hsupp_im_ne
  let F : d.support → ℂ := fun σ ↦ weierstrassFactor 1 ((σ : ℂ)⁻¹ * z) ^ (d σ).toNat
  -- Reindex along `±ρ`, split the sigma product, and collapse each pair.
  calc (∏' σ : d.support, F σ)
      = ∏' p : Σ _ : {ρ : ℂ | ρ ∈ d.support ∧ 0 < ρ.im}, Bool, F (e p) := (e.tprod_eq F).symm
    _ = ∏' ρ : {ρ : ℂ | ρ ∈ d.support ∧ 0 < ρ.im}, ∏' b : Bool, F (e ⟨ρ, b⟩) :=
        Multipliable.tprod_sigma' (fun _ ↦ Multipliable.of_finite) (e.multipliable_iff.mpr hF_mult)
    _ = ∏' ρ : {ρ : ℂ | ρ ∈ d.support ∧ 0 < ρ.im},
          (1 + z ^ 2 / (ρ.val.im : ℂ) ^ 2) ^ (d ρ.val).toNat := by
        refine tprod_congr fun ρ ↦ ?_
        rw [tprod_fintype, Fintype.prod_bool]
        dsimp only [F]
        rw [imagPairEquiv_true, imagPairEquiv_false, hdiv_neg]
        exact weierstrassFactor_one_imag_pair (hsupp_re ρ.property.1) (d ρ.val).toNat z

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
  have hsupp_re {ρ : ℂ} (hρ : ρ ∈ (MeromorphicOn.divisor g Set.univ).support) : ρ.re = 0 :=
    re_eq_zero_of_mem_divisor_support hg hzeros hρ
  generalize MeromorphicOn.divisor g Set.univ = d at hprod_pos hsupp_re hsum
  let Spos : Set ℂ := {ρ : ℂ | ρ ∈ d.support ∧ 0 < ρ.im}
  have hSpos_sub : Spos ⊆ d.support := fun _ h ↦ h.1
  have hSpos_sum : Summable (fun ρ : Spos ↦ ((d ρ.val).toNat : ℝ) * (ρ.val.im)⁻¹ ^ 2) := by
    refine (hsum.comp_injective (Set.inclusion_injective hSpos_sub)).congr fun ρ ↦ ?_
    have hnorm : ‖(ρ.val)⁻¹‖ = (ρ.val.im)⁻¹ := by
      rw [norm_inv, ← Complex.abs_im_eq_norm.mpr (hsupp_re ρ.property.1),
        abs_of_pos ρ.property.2]
    dsimp only [Function.comp_apply, Set.inclusion]
    rw [hnorm]
  obtain ⟨γ, hγ_nonneg, hγ_sum, hγ_prod⟩ :=
    exists_nat_seq_tprod_one_add_div_sq (fun ρ : Spos ↦ ρ.property.2) hSpos_sum
  exact ⟨γ, hγ_nonneg, hγ_sum, fun z ↦ (hprod_pos z).trans (hγ_prod z)⟩

end TauCeti
