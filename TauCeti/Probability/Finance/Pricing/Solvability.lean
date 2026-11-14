/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.Pricing.Operator
public import TauCeti.Probability.Finance.WeightedLogSpot
import TauCeti.Analysis.Holder.Algebra
import TauCeti.Analysis.PDE.Parabolic.Holder.CompSpatial
import TauCeti.Analysis.PDE.Parabolic.Holder.Solvability
import TauCeti.Probability.Finance.Comparison

/-!
# Solvability of the pricing equation in weighted log-spot parabolic Hölder spaces

Let `a = σ² / 2` and let `r` be the short rate on a closed time slab `ℝ × [t₀, t₁]`, `t₀ < t₁`.
In weighted log-spot coordinates `u(y, t) = C(e^y, t) / (1 + e^y)`, the backward pricing operator

`P u = ∂ₜu + a ∂ᵧ²u + (r + a (2 sigmoid y - 1)) ∂ᵧu - r (1 - sigmoid y) u`

acts as a bounded linear map `weightedLogSpotPricingOperatorL` from `C_b^{2+α,1+α/2}(ℝ × [t₀, t₁])`
to `C_b^{α,α/2}(ℝ × [t₀, t₁])`. When `a` is uniformly bounded away from zero (`δ ≤ a` with `0 < δ`)
and `0 < α < 1`, this file proves that the terminal-data map `u ↦ (P u, u(·, t₁))` is an
isomorphism of Banach spaces onto `C_b^{α,α/2}(ℝ × [t₀, t₁]) × C_b^{2,α}(ℝ)`, with uniform
Schauder bounds over horizons `t₁ - t₀ ≤ T₀` and Lipschitz dependence on `(a, r)` in operator norm.

Evaluating the inverse at `(0, g)` solves the homogeneous terminal-value problem `P u = 0`,
`u(·, t₁) = g`, and reconstructing the spot price `C = weightedLogSpotPrice u` via
`C(s, t) = (1 + s) u(log s, t)` yields the unique classical solution of the self-financing pricing
equation

`∂ₜC + σ(s, t)² s² / 2 ∂ₛ²C + r(t) (s ∂ₛC - C) = 0`

on `(0, ∞) × (t₀, t₁)` in the linear-growth class, together with joint continuity of `C` and `∂ₛC`
up to the time endpoints and the uniform linear-growth bound
`|C(s, t)| + |s ∂ₛC(s, t)| ≤ 2 ‖u‖ (1 + s)` controlling both the claim value and its dollar-delta
exposure.

## Main declarations

All financial declarations are in the `TauCeti.Finance` namespace.

* `hasDerivAt_weightedLogSpotPrice_time`, `differentiableAt_weightedLogSpotPrice_time`,
  `deriv_weightedLogSpotPrice_time` and `continuousOn_deriv_weightedLogSpotPrice_spot`: interior
  time differentiability and joint continuity of the spot derivative for `weightedLogSpotPrice u`.
* `pde_weightedLogSpotPrice_eq_mul_weightedLogSpotPricingOperatorL` and
  `pde_weightedLogSpotPrice_eq_mul_weightedLogSpotPricingOperatorL_of_mem_Ioo`: spot-coordinate
  pricing-operator identities on `[t₀, t₁]` and `(t₀, t₁)`.
* `bijective_weightedLogSpotPricingOperatorL_prod_spatialTraceL` and
  `weightedLogSpotTerminalDataCLE`: the Banach-space isomorphism `u ↦ (P u, u(·, t₁))`, with
  `weightedLogSpotTerminalDataCLE_apply`,
  `weightedLogSpotPricingOperatorL_weightedLogSpotTerminalDataCLE_symm_apply`,
  `spatialTrace_weightedLogSpotTerminalDataCLE_symm_apply`,
  `weightedLogSpotTerminalDataCLE_symm_apply_slabMk_right` and
  `abs_weightedLogSpotTerminalDataCLE_symm_apply_le`.
* `exists_norm_weightedLogSpotTerminalDataCLE_symm_le` and
  `exists_norm_weightedLogSpotTerminalDataCLE_symm_sub_le`: uniform Schauder bound and Lipschitz
  dependence on `(a, r)`.
* `memHolder_slab_of_lipschitz_exp_of_holderOnWith`, `logSpotHalfVarianceHolder` and
  `shortRateHolder`: parabolic Hölder coefficient fields built from market volatility `σ(s, t)` and
  time-dependent short rate `r(t)`.
* `eq_weightedLogSpotPrice_of_pde` and `exists_weightedLogSpotPrice_pde_and_unique`: classical
  existence, linear-growth value and dollar-delta bounds, and uniqueness in the linear-growth class
  for the spot-coordinate pricing PDE on `[t₀, t₁]`.

## References

* P. Wilmott, S. Howison, J. Dewynne, *The Mathematics of Financial Derivatives*, Cambridge
  University Press, 1995, §5.4.
* A. Friedman, *Partial Differential Equations of Parabolic Type*, Prentice-Hall, 1964, Chapter 2,
  Section 4 and Chapter 3.
* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section
noncomputable section

open Real Set Filter Topology ContinuousLinearMap
open scoped NNReal ENNReal BoundedContinuousFunction
open TauCeti.ParabolicSpaceTime TauCeti.ParabolicC2HolderSpace

namespace TauCeti.Finance

-- These shortcuts keep instance search shallow for nested line and Euclidean coefficient spaces.
private local instance : NormedAddCommGroup (ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ (ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedAddCommGroup (ℝ →L[ℝ] ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ (ℝ →L[ℝ] ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedAddCommGroup ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance
private local instance : NormedAddCommGroup ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance
private local instance : NormedAddCommGroup (EuclideanSpace ℝ Unit →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ (EuclideanSpace ℝ Unit →L[ℝ] ℝ) := inferInstance
private local instance :
    NormedAddCommGroup (EuclideanSpace ℝ Unit →L[ℝ] EuclideanSpace ℝ Unit →L[ℝ] ℝ) := inferInstance
private local instance :
    NormedSpace ℝ (EuclideanSpace ℝ Unit →L[ℝ] EuclideanSpace ℝ Unit →L[ℝ] ℝ) := inferInstance
private local instance :
    NormedAddCommGroup ((EuclideanSpace ℝ Unit →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance
private local instance :
    NormedSpace ℝ ((EuclideanSpace ℝ Unit →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance
private local instance :
    NormedAddCommGroup ((EuclideanSpace ℝ Unit →L[ℝ] EuclideanSpace ℝ Unit →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  inferInstance
private local instance :
    NormedSpace ℝ ((EuclideanSpace ℝ Unit →L[ℝ] EuclideanSpace ℝ Unit →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  inferInstance

/-! ### Spot-coordinate regularity and pricing-operator identities -/

section SpotRegularity

variable {α : ℝ≥0} {t₀ t₁ : ℝ} {ht : t₀ < t₁}

/-- At an interior time `t ∈ (t₀, t₁)`, the reconstructed spot price `weightedLogSpotPrice u s` has
ordinary time derivative `(1 + s) ∂ₜu(log s, t)`. -/
theorem hasDerivAt_weightedLogSpotPrice_time (u : ParabolicC2HolderSpace α ℝ ℝ ht) (s : ℝ)
    {t : ℝ} (ht' : t ∈ Ioo t₀ t₁) :
    HasDerivAt (weightedLogSpotPrice u s)
      ((1 + s) * timeDerivL u (slabMk (log s) ⟨t, Ioo_subset_Icc_self ht'⟩)) t :=
  (hasDerivWithinAt_weightedLogSpotPrice_time u s ⟨t, Ioo_subset_Icc_self ht'⟩).hasDerivAt
    (Icc_mem_nhds ht'.1 ht'.2)

/-- At an interior time `t ∈ (t₀, t₁)`, `weightedLogSpotPrice u s` is differentiable in time. -/
theorem differentiableAt_weightedLogSpotPrice_time (u : ParabolicC2HolderSpace α ℝ ℝ ht) (s : ℝ)
    {t : ℝ} (ht' : t ∈ Ioo t₀ t₁) :
    DifferentiableAt ℝ (weightedLogSpotPrice u s) t :=
  (hasDerivAt_weightedLogSpotPrice_time u s ht').differentiableAt

/-- At an interior time `t ∈ (t₀, t₁)`, the ordinary time derivative of `weightedLogSpotPrice u s`
equals `(1 + s) ∂ₜu(log s, t)`. -/
theorem deriv_weightedLogSpotPrice_time (u : ParabolicC2HolderSpace α ℝ ℝ ht) (s : ℝ)
    {t : ℝ} (ht' : t ∈ Ioo t₀ t₁) :
    deriv (weightedLogSpotPrice u s) t =
      (1 + s) * timeDerivL u (slabMk (log s) ⟨t, Ioo_subset_Icc_self ht'⟩) :=
  (hasDerivAt_weightedLogSpotPrice_time u s ht').deriv

/-- The spot derivative `(s, t) ↦ ∂ₛC(s, t)` of `C = weightedLogSpotPrice u` is jointly continuous
on `(0, ∞) × [t₀, t₁]`. -/
theorem continuousOn_deriv_weightedLogSpotPrice_spot (u : ParabolicC2HolderSpace α ℝ ℝ ht) :
    ContinuousOn (fun p : ℝ × ℝ ↦ deriv (fun s ↦ weightedLogSpotPrice u s p.2) p.1)
      (Ioi 0 ×ˢ Icc t₀ t₁) := by
  let g : ℝ × ℝ → ℝ := fun p ↦
    timeExtension ht.le u (log p.1) p.2 +
      (1 + p.1) / p.1 * timeExtension ht.le (spatialFDerivL u) (log p.1) p.2 1
  have hu : Continuous fun q : ℝ × ℝ ↦ timeExtension ht.le u q.2 q.1 :=
    continuous_timeExtension ht.le (valueL u).continuous
  have hdu : Continuous fun q : ℝ × ℝ ↦ timeExtension ht.le (spatialFDerivL u) q.2 q.1 1 :=
    (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).continuous.comp
      (continuous_timeExtension ht.le (spatialFDerivL u).continuous)
  have hg : ContinuousOn g (Ioi 0 ×ˢ Icc t₀ t₁) := by
    intro p hp
    have hlog : ContinuousAt (fun q : ℝ × ℝ ↦ (q.2, log q.1)) p :=
      continuous_snd.continuousAt.prodMk
        ((continuousAt_log hp.1.ne').comp continuous_fst.continuousAt)
    exact (ContinuousAt.add (hu.continuousAt.comp hlog)
      (((continuous_const.add continuous_fst).continuousAt.div continuous_fst.continuousAt
        hp.1.ne').mul (hdu.continuousAt.comp hlog))).continuousWithinAt
  refine hg.congr fun p hp ↦ ?_
  rw [deriv_weightedLogSpotPrice_spot u hp.1 ⟨p.2, hp.2⟩]
  have ht1 := timeExtension_of_mem ht.le (valueL u) (log p.1) ⟨p.2, hp.2⟩
  have ht2 := timeExtension_of_mem ht.le (spatialFDerivL u) (log p.1) ⟨p.2, hp.2⟩
  dsimp only [g, Subtype.coe_mk] at *
  rw [ht1, ht2]

/-- Both the reconstructed price and its dollar-delta exposure `s ∂ₛC(s, t)` are controlled by the
parabolic `C^{2+α,1+α/2}` norm of `u`, uniformly on `(0, ∞) × [t₀, t₁]`. -/
theorem abs_weightedLogSpotPrice_add_abs_mul_deriv_le (u : ParabolicC2HolderSpace α ℝ ℝ ht)
    {s : ℝ} (hs : 0 < s) {t : ℝ} (ht' : t ∈ Icc t₀ t₁) :
    |weightedLogSpotPrice u s t| + |s * deriv (fun x ↦ weightedLogSpotPrice u x t) s| ≤
      2 * ‖u‖ * (1 + s) := by
  have h₁ := abs_weightedLogSpotPrice_le u hs.le t
  have h₂ := abs_mul_deriv_weightedLogSpotPrice_le u hs ⟨t, ht'⟩
  have hnorm : ‖valueL u‖ + ‖spatialFDerivL u‖ ≤ ‖u‖ := by
    rw [ParabolicC2HolderSpace.norm_eq, HolderSpace.norm_eq_holderNorm,
      HolderSpace.norm_eq_holderNorm]
    exact le_add_of_nonneg_right (add_nonneg (holderNorm_nonneg _) (holderNorm_nonneg _))
  calc |weightedLogSpotPrice u s t| + |s * deriv (fun x ↦ weightedLogSpotPrice u x t) s|
      ≤ ‖u‖ * (1 + s) + ‖u‖ * (1 + s) :=
        add_le_add h₁ (h₂.trans (mul_le_mul_of_nonneg_right hnorm (by positivity)))
    _ = 2 * ‖u‖ * (1 + s) := by ring

/-- On the closed slab `[t₀, t₁]`, the classical spot pricing operator applied to
`C = weightedLogSpotPrice u` (with within-slab time derivative) equals `(1 + s)` times
`weightedLogSpotPricingOperatorL` evaluated at `(log s, t)`. -/
theorem pde_weightedLogSpotPrice_eq_mul_weightedLogSpotPricingOperatorL (hα : α ≤ 1)
    (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) (u : ParabolicC2HolderSpace α ℝ ℝ ht)
    {s : ℝ} (hs : 0 < s) (t : Icc t₀ t₁) {σ r₀ : ℝ}
    (ha : a (slabMk (log s) t) = σ ^ 2 / 2) (hr : r (slabMk (log s) t) = r₀) :
    derivWithin (weightedLogSpotPrice u s) (Icc t₀ t₁) t +
        σ ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ weightedLogSpotPrice u x t) s +
        r₀ * (s * deriv (fun x ↦ weightedLogSpotPrice u x t) s - weightedLogSpotPrice u s t) =
      (1 + s) * weightedLogSpotPricingOperatorL hα a r u (slabMk (log s) t) := by
  rw [pde_weightedLogSpotPrice u hs t σ r₀, weightedLogSpotPricingOperatorL_apply, space_slabMk,
    ha, hr, sigmoid_def, exp_neg, exp_log hs]
  have hs' : s ≠ 0 := hs.ne'
  have h1s : 1 + s ≠ 0 := by positivity
  have hs1 : s + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- At an interior time `t ∈ (t₀, t₁)`, the classical spot pricing operator applied to
`C = weightedLogSpotPrice u` (with ordinary time derivative) equals `(1 + s)` times
`weightedLogSpotPricingOperatorL` evaluated at `(log s, t)`. -/
theorem pde_weightedLogSpotPrice_eq_mul_weightedLogSpotPricingOperatorL_of_mem_Ioo (hα : α ≤ 1)
    (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) (u : ParabolicC2HolderSpace α ℝ ℝ ht)
    {s : ℝ} (hs : 0 < s) {t : ℝ} (ht' : t ∈ Ioo t₀ t₁) {σ r₀ : ℝ}
    (ha : a (slabMk (log s) ⟨t, Ioo_subset_Icc_self ht'⟩) = σ ^ 2 / 2)
    (hr : r (slabMk (log s) ⟨t, Ioo_subset_Icc_self ht'⟩) = r₀) :
    deriv (weightedLogSpotPrice u s) t +
        σ ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ weightedLogSpotPrice u x t) s +
        r₀ * (s * deriv (fun x ↦ weightedLogSpotPrice u x t) s - weightedLogSpotPrice u s t) =
      (1 + s) * weightedLogSpotPricingOperatorL hα a r u
        (slabMk (log s) ⟨t, Ioo_subset_Icc_self ht'⟩) := by
  have hd : deriv (weightedLogSpotPrice u s) t =
      derivWithin (weightedLogSpotPrice u s) (Icc t₀ t₁) t := by
    rw [deriv_weightedLogSpotPrice_time u s ht',
      derivWithin_weightedLogSpotPrice_time u s ⟨t, Ioo_subset_Icc_self ht'⟩]
  rw [hd]
  exact pde_weightedLogSpotPrice_eq_mul_weightedLogSpotPricingOperatorL hα a r u hs
    ⟨t, Ioo_subset_Icc_self ht'⟩ ha hr

end SpotRegularity

/-! ### The weighted log-spot terminal-data isomorphism -/

section TerminalDataCLE

private def lineToEucl : ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ Unit :=
  (OrthonormalBasis.singleton Unit ℝ).repr

@[simp]
private theorem lineToEucl_apply (x : ℝ) (i : Unit) : lineToEucl x i = x :=
  OrthonormalBasis.singleton_repr x i

@[simp]
private theorem lineToEucl_symm_apply (v : EuclideanSpace ℝ Unit) : lineToEucl.symm v = v () :=
  lineToEucl.injective (by ext i; simp)

private theorem norm_lineToEucl_clm_le :
    ‖(lineToEucl.toContinuousLinearEquiv : ℝ →L[ℝ] EuclideanSpace ℝ Unit)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by
    simpa only [one_mul, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv] using (lineToEucl.norm_map x).le

private theorem norm_lineToEucl_symm_clm_le :
    ‖(lineToEucl.symm.toContinuousLinearEquiv : EuclideanSpace ℝ Unit →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by
    simpa only [one_mul, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv] using (lineToEucl.symm.norm_map x).le

private theorem lipschitzWith_slab_lineToEucl {t₀ t₁ : ℝ} :
    LipschitzWith 1 (slabSpaceMap (a := t₀) (b := t₁) lineToEucl) := by
  simpa only [max_self] using lipschitzWith_slabSpaceMap lineToEucl.lipschitzWith

private theorem lipschitzWith_slab_lineToEucl_symm {t₀ t₁ : ℝ} :
    LipschitzWith 1 (slabSpaceMap (a := t₀) (b := t₁) lineToEucl.symm) := by
  simpa only [max_self] using lipschitzWith_slabSpaceMap lineToEucl.symm.lipschitzWith

private def toEuclSlabCLE {α : ℝ≥0} {t₀ t₁ : ℝ} :
    HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ ≃L[ℝ]
      HolderSpace α (slab (E := EuclideanSpace ℝ Unit) t₀ t₁) ℝ :=
  ContinuousLinearEquiv.equivOfInverse
    (HolderSpace.compLipschitzL _ lipschitzWith_slab_lineToEucl_symm)
    (HolderSpace.compLipschitzL _ lipschitzWith_slab_lineToEucl)
    (fun f ↦ by
      ext p
      rw [HolderSpace.compLipschitzL_apply, HolderSpace.compLipschitzL_apply,
        ← slabMk_space_slabTime p]
      simp)
    (fun g ↦ by
      ext p
      rw [HolderSpace.compLipschitzL_apply, HolderSpace.compLipschitzL_apply,
        ← slabMk_space_slabTime p]
      simp)

@[simp]
private theorem toEuclSlabCLE_apply {α : ℝ≥0} {t₀ t₁ : ℝ}
    (f : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)
    (p : slab (E := EuclideanSpace ℝ Unit) t₀ t₁) :
    toEuclSlabCLE f p = f (slabSpaceMap lineToEucl.symm p) := by
  simp [toEuclSlabCLE]

private theorem norm_toEuclSlabCLE_le {α : ℝ≥0} {t₀ t₁ : ℝ} :
    ‖(toEuclSlabCLE (α := α) (t₀ := t₀) (t₁ := t₁)).toContinuousLinearMap‖ ≤ 1 :=
  HolderSpace.norm_compLipschitzL_le_one lipschitzWith_slab_lineToEucl_symm

private theorem norm_toEuclSlabCLE_apply_le {α : ℝ≥0} {t₀ t₁ : ℝ}
    (f : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) :
    ‖toEuclSlabCLE f‖ ≤ ‖f‖ := by
  simpa only [one_mul, ContinuousLinearEquiv.coe_coe] using
    toEuclSlabCLE.toContinuousLinearMap.le_of_opNorm_le norm_toEuclSlabCLE_le f

private def toEuclCkCLE {α : ℝ≥0} :
    CkHolderSpace 2 α ℝ ℝ ≃L[ℝ] CkHolderSpace 2 α (EuclideanSpace ℝ Unit) ℝ :=
  CkHolderSpace.compLinearCLE lineToEucl.symm.toContinuousLinearEquiv

private theorem norm_toEuclCkCLE_le {α : ℝ≥0} :
    ‖(toEuclCkCLE (α := α)).toContinuousLinearMap‖ ≤ 1 := by
  let eL : EuclideanSpace ℝ Unit →L[ℝ] ℝ := lineToEucl.symm.toContinuousLinearEquiv
  have he : ‖eL‖ ≤ 1 := norm_lineToEucl_symm_clm_le
  have hclm : (toEuclCkCLE (α := α)).toContinuousLinearMap =
      CkHolderSpace.compLinearL (k := 2) (α := α) (F := ℝ) eL := by
    ext g x; simp [toEuclCkCLE, eL]
  rw [hclm]
  refine (CkHolderSpace.norm_compLinearL_le (k := 2) (α := α) (F := ℝ) eL).trans ?_
  have h1 : max 1 ‖eL‖ ≤ 1 := max_le le_rfl he
  have h2 : max 1 (‖eL‖ ^ (α : ℝ)) ≤ 1 :=
    max_le le_rfl ((Real.rpow_le_rpow (norm_nonneg _) he (NNReal.coe_nonneg α)).trans
      (by rw [Real.one_rpow]))
  calc _ ≤ 1 ^ 2 * 1 := mul_le_mul (pow_le_pow_left₀ (by positivity) h1 2) h2
        (by positivity) (by positivity)
    _ = 1 := by norm_num

private def toEuclDataCLE {α : ℝ≥0} {t₀ t₁ : ℝ} :
    (HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) ≃L[ℝ]
      (HolderSpace α (slab (E := EuclideanSpace ℝ Unit) t₀ t₁) ℝ ×
        CkHolderSpace 2 α (EuclideanSpace ℝ Unit) ℝ) :=
  toEuclSlabCLE.prodCongr toEuclCkCLE

private theorem norm_toEuclDataCLE_le {α : ℝ≥0} {t₀ t₁ : ℝ} :
    ‖(toEuclDataCLE (α := α) (t₀ := t₀) (t₁ := t₁)).toContinuousLinearMap‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun d ↦ ?_
  have hd2 : ‖toEuclCkCLE d.2‖ ≤ ‖d.2‖ := by
    simpa only [one_mul, ContinuousLinearEquiv.coe_coe] using
      toEuclCkCLE.toContinuousLinearMap.le_of_opNorm_le norm_toEuclCkCLE_le d.2
  simp only [ContinuousLinearEquiv.coe_coe, toEuclDataCLE, ContinuousLinearEquiv.prodCongr_apply,
    Prod.norm_def, one_mul]
  exact max_le ((norm_toEuclSlabCLE_apply_le d.1).trans (norm_fst_le d))
    (hd2.trans (norm_snd_le d))

private def toEuclC2CLE {α : ℝ≥0} {t₀ t₁ : ℝ} {ht : t₀ < t₁} :
    ParabolicC2HolderSpace α ℝ ℝ ht ≃L[ℝ]
      ParabolicC2HolderSpace α (EuclideanSpace ℝ Unit) ℝ ht :=
  ParabolicC2HolderSpace.compSpatialCLE α ℝ ht lineToEucl.symm.toContinuousLinearEquiv

private theorem toEuclC2CLE_symm_toCLM {α : ℝ≥0} {t₀ t₁ : ℝ} {ht : t₀ < t₁} :
    (toEuclC2CLE (α := α) (ht := ht)).symm.toContinuousLinearMap =
      ParabolicC2HolderSpace.compSpatialL α ℝ ht
        (lineToEucl.toContinuousLinearEquiv : ℝ →L[ℝ] EuclideanSpace ℝ Unit) := by
  ext v p
  simp [toEuclC2CLE]

private theorem norm_toEuclC2CLE_symm_le {α : ℝ≥0} {t₀ t₁ : ℝ} {ht : t₀ < t₁} :
    ‖(toEuclC2CLE (α := α) (ht := ht)).symm.toContinuousLinearMap‖ ≤ 1 := by
  rw [toEuclC2CLE_symm_toCLM]
  exact (ParabolicC2HolderSpace.norm_compSpatialL_le_of_norm_le α ℝ ht le_rfl
    norm_lineToEucl_clm_le).trans (by norm_num)

private def sigmoidHolder {α : ℝ≥0} (hα : α ≤ 1) : HolderSpace α ℝ ℝ :=
  HolderSpace.compLeftL (ContinuousLinearMap.apply ℝ ℝ 1) (logOneAddExpGrad hα)

@[simp]
private theorem sigmoidHolder_apply {α : ℝ≥0} (hα : α ≤ 1) (y : ℝ) :
    sigmoidHolder hα y = sigmoid y := by
  simp [sigmoidHolder]

private def weightedDriftScalar {α : ℝ≥0} {t₀ t₁ : ℝ} (hα : α ≤ 1)
    (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) :
    HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ :=
  r + a * HolderSpace.compSlabSpaceL ((2 : ℝ) • sigmoidHolder hα - 1)

@[simp]
private theorem weightedDriftScalar_apply {α : ℝ≥0} {t₀ t₁ : ℝ} (hα : α ≤ 1)
    (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) (p : slab (E := ℝ) t₀ t₁) :
    weightedDriftScalar hα a r p =
      r p + a p * (2 * sigmoid (p : ParabolicSpaceTime ℝ).space - 1) := by
  simp [weightedDriftScalar]

private def weightedRateScalar {α : ℝ≥0} {t₀ t₁ : ℝ} (hα : α ≤ 1)
    (r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) :
    HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ :=
  -r * HolderSpace.compSlabSpaceL (1 - sigmoidHolder hα)

@[simp]
private theorem weightedRateScalar_apply {α : ℝ≥0} {t₀ t₁ : ℝ} (hα : α ≤ 1)
    (r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) (p : slab (E := ℝ) t₀ t₁) :
    weightedRateScalar hα r p = -r p * (1 - sigmoid (p : ParabolicSpaceTime ℝ).space) := by
  simp [weightedRateScalar]

private theorem norm_compSlabSpaceL_apply_le {α : ℝ≥0} {t₀ t₁ : ℝ} (w : HolderSpace α ℝ ℝ) :
    ‖(HolderSpace.compSlabSpaceL w : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)‖ ≤ ‖w‖ := by
  simpa only [one_mul] using
    (HolderSpace.compSlabSpaceL (α := α) (E := ℝ) (Y := ℝ) (a := t₀) (b := t₁)).le_of_opNorm_le
      HolderSpace.norm_compSlabSpaceL_le_one w

private theorem norm_weightedDriftScalar_le {α : ℝ≥0} {t₀ t₁ : ℝ} (hα : α ≤ 1)
    (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) :
    ‖weightedDriftScalar hα a r‖ ≤
      ‖r‖ + ‖a‖ * ‖((2 : ℝ) • sigmoidHolder hα - 1 : HolderSpace α ℝ ℝ)‖ := by
  set w : HolderSpace α ℝ ℝ := (2 : ℝ) • sigmoidHolder hα - 1
  rw [weightedDriftScalar]
  calc ‖r + a * HolderSpace.compSlabSpaceL w‖
      ≤ ‖r‖ + ‖a * HolderSpace.compSlabSpaceL w‖ := norm_add_le _ _
    _ ≤ ‖r‖ + ‖a‖ * ‖(HolderSpace.compSlabSpaceL w : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)‖ :=
        add_le_add le_rfl (norm_mul_le _ _)
    _ ≤ ‖r‖ + ‖a‖ * ‖w‖ :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_compSlabSpaceL_apply_le w)
          (norm_nonneg a))

private theorem norm_weightedDriftScalar_sub_le {α : ℝ≥0} {t₀ t₁ : ℝ} (hα : α ≤ 1)
    (a a' r r' : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) :
    ‖weightedDriftScalar hα a r - weightedDriftScalar hα a' r'‖ ≤
      ‖r - r'‖ + ‖a - a'‖ * ‖((2 : ℝ) • sigmoidHolder hα - 1 : HolderSpace α ℝ ℝ)‖ := by
  have heq : weightedDriftScalar hα a r - weightedDriftScalar hα a' r' =
      weightedDriftScalar hα (a - a') (r - r') := by
    ext p
    simp only [HolderSpace.sub_apply, weightedDriftScalar_apply]
    ring
  rw [heq]
  exact norm_weightedDriftScalar_le hα (a - a') (r - r')

private theorem norm_weightedRateScalar_le {α : ℝ≥0} {t₀ t₁ : ℝ} (hα : α ≤ 1)
    (r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) :
    ‖weightedRateScalar hα r‖ ≤ ‖r‖ * ‖(1 - sigmoidHolder hα : HolderSpace α ℝ ℝ)‖ := by
  set w : HolderSpace α ℝ ℝ := 1 - sigmoidHolder hα
  rw [weightedRateScalar]
  calc ‖-r * HolderSpace.compSlabSpaceL w‖
      ≤ ‖-r‖ * ‖(HolderSpace.compSlabSpaceL w : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)‖ :=
        norm_mul_le _ _
    _ = ‖r‖ * ‖(HolderSpace.compSlabSpaceL w : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)‖ := by
        rw [norm_neg]
    _ ≤ ‖r‖ * ‖w‖ := mul_le_mul_of_nonneg_left (norm_compSlabSpaceL_apply_le w) (norm_nonneg r)

private theorem norm_weightedRateScalar_sub_le {α : ℝ≥0} {t₀ t₁ : ℝ} (hα : α ≤ 1)
    (r r' : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) :
    ‖weightedRateScalar hα r - weightedRateScalar hα r'‖ ≤
      ‖r - r'‖ * ‖(1 - sigmoidHolder hα : HolderSpace α ℝ ℝ)‖ := by
  have heq : weightedRateScalar hα r - weightedRateScalar hα r' =
      weightedRateScalar hα (r - r') := by
    ext p
    simp only [HolderSpace.sub_apply, weightedRateScalar_apply]
    ring
  rw [heq]
  exact norm_weightedRateScalar_le hα (r - r')

private theorem toQuadraticForm'_unit_ge {δ c : ℝ} (hc : δ ≤ c) (ξ : EuclideanSpace ℝ Unit) :
    δ * ‖ξ‖ ^ 2 ≤ (Matrix.of fun _ _ : Unit ↦ c).toQuadraticForm' ξ := by
  have hnorm : ‖ξ‖ ^ 2 = ξ () ^ 2 := by
    rw [← lineToEucl.symm.norm_map ξ, lineToEucl_symm_apply, Real.norm_eq_abs, sq_abs]
  have hq : (Matrix.of fun _ _ : Unit ↦ c).toQuadraticForm' ξ = c * ξ () ^ 2 := by
    rw [Matrix.toQuadraticForm'_apply]
    simp [dotProduct, Matrix.mulVec]
    ring
  rw [hq, hnorm]
  exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)

private theorem toEuclSlabCLE_elliptic {α : ℝ≥0} {t₀ t₁ δ : ℝ}
    {a : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ} (ha : ∀ p, δ ≤ a p)
    (p : slab (E := EuclideanSpace ℝ Unit) t₀ t₁) (ξ : EuclideanSpace ℝ Unit) :
    δ * ‖ξ‖ ^ 2 ≤ (Matrix.of fun _ _ : Unit ↦ toEuclSlabCLE a p).toQuadraticForm' ξ := by
  rw [toEuclSlabCLE_apply]
  exact toQuadraticForm'_unit_ge (ha _) ξ

private theorem euclideanBackwardParabolicOperatorL_toEuclC2CLE {α : ℝ≥0} {t₀ t₁ : ℝ}
    {ht : t₀ < t₁} (hα : α ≤ 1) (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)
    (u : ParabolicC2HolderSpace α ℝ ℝ ht) :
    euclideanBackwardParabolicOperatorL hα (fun _ _ ↦ toEuclSlabCLE a)
        (fun _ ↦ toEuclSlabCLE (weightedDriftScalar hα a r))
        (toEuclSlabCLE (weightedRateScalar hα r)) (toEuclC2CLE u) =
      toEuclSlabCLE (weightedLogSpotPricingOperatorL hα a r u) := by
  ext p
  have he1 : lineToEucl.symm (EuclideanSpace.single () (1 : ℝ)) = 1 := by simp
  simp only [euclideanBackwardParabolicOperatorL_apply, toEuclC2CLE, compSpatialCLE_apply,
    timeDerivL_compSpatialL, spatialSecondFDerivL_compSpatialL,
    ContinuousLinearMap.bilinearComp_apply, spatialFDerivL_compSpatialL,
    ContinuousLinearMap.comp_apply, compSpatialL_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, he1, Fintype.sum_unique, toEuclSlabCLE_apply,
    weightedDriftScalar_apply, weightedRateScalar_apply, weightedLogSpotPricingOperatorL_apply]
  ring

private theorem prod_toEuclC2CLE_eq {α : ℝ≥0} {t₀ t₁ : ℝ} {ht : t₀ < t₁} (hα : α ≤ 1)
    (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) (u : ParabolicC2HolderSpace α ℝ ℝ ht) :
    ((euclideanBackwardParabolicOperatorL hα (fun _ _ ↦ toEuclSlabCLE a)
        (fun _ ↦ toEuclSlabCLE (weightedDriftScalar hα a r))
        (toEuclSlabCLE (weightedRateScalar hα r))).prod
        (spatialTraceL ⟨t₁, right_mem_Icc.2 ht.le⟩)) (toEuclC2CLE u) =
      toEuclDataCLE (((weightedLogSpotPricingOperatorL hα a r).prod
        (spatialTraceL ⟨t₁, right_mem_Icc.2 ht.le⟩)) u) :=
  Prod.ext (euclideanBackwardParabolicOperatorL_toEuclC2CLE hα a r u)
    (by simp [toEuclC2CLE, toEuclDataCLE, toEuclCkCLE, spatialTraceL_apply])

/-- **Bijectivity of the weighted log-spot terminal-data map.** For `0 < α < 1`, `t₀ < t₁`, and
parabolic Hölder coefficients `a, r` on `ℝ × [t₀, t₁]` with `δ ≤ a` (`0 < δ`), the map
`u ↦ (P u, u(·, t₁))` of the weighted log-spot pricing operator is bijective from
`C_b^{2+α,1+α/2}(ℝ × [t₀, t₁])` onto `C_b^{α,α/2}(ℝ × [t₀, t₁]) × C_b^{2,α}(ℝ)`. -/
theorem bijective_weightedLogSpotPricingOperatorL_prod_spatialTraceL {α : ℝ≥0} {t₀ t₁ : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t₀ < t₁)
    (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) {δ : ℝ} (hδ : 0 < δ) (ha : ∀ p, δ ≤ a p) :
    Function.Bijective ((weightedLogSpotPricingOperatorL (ht := ht) hα₁.le a r).prod
      (spatialTraceL ⟨t₁, right_mem_Icc.2 ht.le⟩)) := by
  let eE := euclideanTerminalDataCLE hα₀ hα₁ ht
    (fun _ _ : Unit ↦ toEuclSlabCLE a)
    (fun _ : Unit ↦ toEuclSlabCLE (weightedDriftScalar hα₁.le a r))
    (toEuclSlabCLE (weightedRateScalar hα₁.le r))
    ⟨δ, hδ, toEuclSlabCLE_elliptic ha⟩
  have hcomp : (⇑toEuclDataCLE ∘ ⇑((weightedLogSpotPricingOperatorL (ht := ht) hα₁.le a r).prod
      (spatialTraceL ⟨t₁, right_mem_Icc.2 ht.le⟩))) =
      ⇑eE ∘ ⇑(toEuclC2CLE (ht := ht)) := by
    funext u
    simp only [Function.comp_apply, eE, euclideanTerminalDataCLE_apply]
    simpa only [ContinuousLinearMap.prod_apply, spatialTraceL_apply] using
      (prod_toEuclC2CLE_eq hα₁.le a r u).symm
  rw [← Function.Bijective.of_comp_iff' toEuclDataCLE.bijective, hcomp]
  exact eE.bijective.comp toEuclC2CLE.bijective

/-- **The weighted log-spot terminal-data isomorphism.** For `0 < α < 1`, `t₀ < t₁`, and parabolic
Hölder coefficients `a, r` on `ℝ × [t₀, t₁]` with `a` uniformly bounded away from zero, the map
`u ↦ (P u, u(·, t₁))` of `weightedLogSpotPricingOperatorL` as an isomorphism of Banach spaces from
`C_b^{2+α,1+α/2}(ℝ × [t₀, t₁])` onto `C_b^{α,α/2}(ℝ × [t₀, t₁]) × C_b^{2,α}(ℝ)`. -/
def weightedLogSpotTerminalDataCLE {α : ℝ≥0} {t₀ t₁ : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)
    (ht : t₀ < t₁) (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)
    (ha : ∃ δ : ℝ, 0 < δ ∧ ∀ p, δ ≤ a p) :
    ParabolicC2HolderSpace α ℝ ℝ ht ≃L[ℝ]
      HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ :=
  have hbij := ha.elim fun _ h ↦
    bijective_weightedLogSpotPricingOperatorL_prod_spatialTraceL hα₀ hα₁ ht a r h.1 h.2
  ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.2 hbij.1)
    (LinearMap.range_eq_top.2 hbij.2)

section WeightedCLEProps

variable {α : ℝ≥0} {t₀ t₁ : ℝ} {hα₀ : 0 < α} {hα₁ : α < 1} {ht : t₀ < t₁}
  {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
  {ha : ∃ δ : ℝ, 0 < δ ∧ ∀ p, δ ≤ a p}

/-- The weighted log-spot terminal-data isomorphism sends `u` to its backward pricing residual
`P u` and its terminal trace `u(·, t₁)`. -/
@[simp]
theorem weightedLogSpotTerminalDataCLE_apply (u : ParabolicC2HolderSpace α ℝ ℝ ht) :
    weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha u =
      (weightedLogSpotPricingOperatorL hα₁.le a r u,
        u.spatialTrace ⟨t₁, right_mem_Icc.2 ht.le⟩) := by
  simp [weightedLogSpotTerminalDataCLE, spatialTraceL_apply]

/-- The solution of the weighted log-spot terminal-value problem with forcing `f` and terminal
datum `g` has backward pricing residual `f`. -/
@[simp]
theorem weightedLogSpotPricingOperatorL_weightedLogSpotTerminalDataCLE_symm_apply
    (d : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) :
    weightedLogSpotPricingOperatorL hα₁.le a r
      ((weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).symm d) = d.1 := by
  have h := (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).apply_symm_apply d
  rw [weightedLogSpotTerminalDataCLE_apply] at h
  exact congrArg Prod.fst h

/-- The solution of the weighted log-spot terminal-value problem with forcing `f` and terminal
datum `g` has terminal trace `g`. -/
@[simp]
theorem spatialTrace_weightedLogSpotTerminalDataCLE_symm_apply
    (d : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) :
    ((weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).symm d).spatialTrace
      ⟨t₁, right_mem_Icc.2 ht.le⟩ = d.2 := by
  have h := (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).apply_symm_apply d
  rw [weightedLogSpotTerminalDataCLE_apply] at h
  exact congrArg Prod.snd h

/-- The solution of the weighted log-spot terminal-value problem with terminal datum `g` takes the
value `g y` at `(y, t₁)`. -/
@[simp]
theorem weightedLogSpotTerminalDataCLE_symm_apply_slabMk_right
    (d : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) (y : ℝ) :
    (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).symm d
      (slabMk y ⟨t₁, right_mem_Icc.2 ht.le⟩) = d.2 y := by
  rw [← spatialTrace_apply, spatialTrace_weightedLogSpotTerminalDataCLE_symm_apply]

/-- **Pointwise exponential bound for the weighted log-spot solution operator.** If `r ≥ -γ` with
`0 ≤ γ`, `|f| ≤ K` and `|g| ≤ M`, then the solution `u` of `P u = f`, `u(·, t₁) = g` satisfies
`|u(y, t)| ≤ exp (γ (t₁ - t)) (M + (t₁ - t) K)`. For a nonnegative short rate, `γ = 0`. -/
theorem abs_weightedLogSpotTerminalDataCLE_symm_apply_le {γ M K : ℝ}
    (hr : ∀ p, -γ ≤ r p) (hγ : 0 ≤ γ)
    (d : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ)
    (hd₁ : ∀ p, |d.1 p| ≤ K) (hd₂ : ∀ y, |d.2 y| ≤ M) (p : slab (E := ℝ) t₀ t₁) :
    |(weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).symm d p| ≤
      Real.exp (γ * (t₁ - slabTime p)) * (M + (t₁ - slabTime p) * K) := by
  obtain ⟨δ, hδ, ha'⟩ := ha
  refine abs_le_exp_mul_mul_add_mul_of_abs_weightedLogSpotPricingOperatorL_le hα₁.le
    (fun q ↦ hδ.le.trans (ha' q)) hr hγ _ ?_ ?_ p
  · intro q
    rw [weightedLogSpotPricingOperatorL_weightedLogSpotTerminalDataCLE_symm_apply]
    exact hd₁ q
  · intro y
    rw [weightedLogSpotTerminalDataCLE_symm_apply_slabMk_right]
    exact hd₂ y

end WeightedCLEProps

private theorem weightedLogSpotTerminalDataCLE_symm_eq {α : ℝ≥0} {t₀ t₁ : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t₀ < t₁)
    (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) {δ : ℝ} (hδ : 0 < δ) (ha : ∀ p, δ ≤ a p) :
    (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ⟨δ, hδ, ha⟩).symm.toContinuousLinearMap =
      (toEuclC2CLE (α := α) (ht := ht)).symm.toContinuousLinearMap ∘L
        (euclideanTerminalDataCLE hα₀ hα₁ ht
          (fun _ _ : Unit ↦ toEuclSlabCLE a)
          (fun _ : Unit ↦ toEuclSlabCLE (weightedDriftScalar hα₁.le a r))
          (toEuclSlabCLE (weightedRateScalar hα₁.le r))
          ⟨δ, hδ, toEuclSlabCLE_elliptic ha⟩).symm.toContinuousLinearMap ∘L
        (toEuclDataCLE (α := α) (t₀ := t₀) (t₁ := t₁)).toContinuousLinearMap := by
  refine ContinuousLinearMap.ext fun d ↦ ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  set eW := weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ⟨δ, hδ, ha⟩
  set eE := euclideanTerminalDataCLE hα₀ hα₁ ht
    (fun _ _ : Unit ↦ toEuclSlabCLE a)
    (fun _ : Unit ↦ toEuclSlabCLE (weightedDriftScalar hα₁.le a r))
    (toEuclSlabCLE (weightedRateScalar hα₁.le r))
    ⟨δ, hδ, toEuclSlabCLE_elliptic ha⟩
  apply eW.injective
  rw [eW.apply_symm_apply]
  apply toEuclDataCLE.injective
  have h1 := prod_toEuclC2CLE_eq hα₁.le a r
    ((toEuclC2CLE (α := α) (ht := ht)).symm (eE.symm (toEuclDataCLE d)))
  rw [ContinuousLinearEquiv.apply_symm_apply] at h1
  have h2 : eE (eE.symm (toEuclDataCLE d)) = toEuclDataCLE d := eE.apply_symm_apply _
  rw [euclideanTerminalDataCLE_apply] at h2
  simp only [eW, weightedLogSpotTerminalDataCLE_apply]
  rw [← spatialTraceL_apply, ← ContinuousLinearMap.prod_apply, ← h1]
  simpa only [ContinuousLinearMap.prod_apply, spatialTraceL_apply] using h2.symm

private def weightedCoeffBound {α : ℝ≥0} (hα : α ≤ 1) (K : ℝ≥0) : ℝ≥0 :=
  K + K * (‖((2 : ℝ) • sigmoidHolder hα - 1 : HolderSpace α ℝ ℝ)‖₊ +
    ‖(1 - sigmoidHolder hα : HolderSpace α ℝ ℝ)‖₊)

private theorem norm_toEuclSlabCLE_coeffs_le {α : ℝ≥0} {t₀ t₁ : ℝ} (hα : α ≤ 1) {K : ℝ≥0}
    {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ} (hak : ‖a‖ ≤ K) (hrk : ‖r‖ ≤ K) :
    (∀ _ _ : Unit, ‖toEuclSlabCLE a‖ ≤ (weightedCoeffBound hα K : ℝ)) ∧
      (∀ _ : Unit, ‖toEuclSlabCLE (weightedDriftScalar hα a r)‖ ≤
        (weightedCoeffBound hα K : ℝ)) ∧
      ‖toEuclSlabCLE (weightedRateScalar hα r)‖ ≤ (weightedCoeffBound hα K : ℝ) := by
  set w₁ : HolderSpace α ℝ ℝ := (2 : ℝ) • sigmoidHolder hα - 1
  set w₀ : HolderSpace α ℝ ℝ := 1 - sigmoidHolder hα
  have hK' : (weightedCoeffBound hα K : ℝ) = K + K * (‖w₁‖ + ‖w₀‖) := by
    simp [weightedCoeffBound, w₁, w₀]
  refine ⟨fun _ _ ↦ (norm_toEuclSlabCLE_apply_le a).trans
      (hak.trans (by exact_mod_cast le_self_add)),
    fun _ ↦ (norm_toEuclSlabCLE_apply_le _).trans ((norm_weightedDriftScalar_le hα a r).trans
      ((add_le_add hrk (mul_le_mul_of_nonneg_right hak (norm_nonneg w₁))).trans
        (by rw [hK']; nlinarith [K.coe_nonneg, norm_nonneg w₀]))),
    (norm_toEuclSlabCLE_apply_le _).trans ((norm_weightedRateScalar_le hα r).trans
      ((mul_le_mul_of_nonneg_right hrk (norm_nonneg w₀)).trans
        (by rw [hK']; nlinarith [K.coe_nonneg, norm_nonneg w₁])))⟩

/-- **Uniform Schauder estimate for the weighted log-spot terminal-value problem.** For `0 < α < 1`,
`0 < δ`, a coefficient bound `K` and a horizon bound `T₀`, the solution operators of the weighted
log-spot terminal-value problems on `ℝ × [t₀, t₁]` with `t₁ - t₀ ≤ T₀`, `δ ≤ a`, `‖a‖ ≤ K` and
`‖r‖ ≤ K` are uniformly bounded in operator norm. -/
theorem exists_norm_weightedLogSpotTerminalDataCLE_symm_le {α : ℝ≥0} (hα₀ : 0 < α) (hα₁ : α < 1)
    {δ : ℝ} (hδ : 0 < δ) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t₀ t₁ : ℝ} (ht : t₀ < t₁), t₁ - t₀ ≤ T₀ →
      ∀ (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) (ha : ∀ p, δ ≤ a p),
        ‖a‖ ≤ K → ‖r‖ ≤ K →
        ‖(weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r
            ⟨δ, hδ, ha⟩).symm.toContinuousLinearMap‖ ≤ C := by
  obtain ⟨C, hC, hest⟩ := exists_norm_euclideanTerminalDataCLE_symm_le (ι := Unit) hα₀ hα₁ hδ
    (weightedCoeffBound hα₁.le K) T₀
  refine ⟨C, hC, fun {t₀ t₁} ht hTT₀ a r ha hak hrk ↦ ?_⟩
  rw [weightedLogSpotTerminalDataCLE_symm_eq hα₀ hα₁ ht a r hδ ha]
  obtain ⟨haE, hbE, hcE⟩ := norm_toEuclSlabCLE_coeffs_le hα₁.le hak hrk
  have hmid := hest ht hTT₀ (fun _ _ ↦ toEuclSlabCLE a)
    (fun _ ↦ toEuclSlabCLE (weightedDriftScalar hα₁.le a r))
    (toEuclSlabCLE (weightedRateScalar hα₁.le r)) (toEuclSlabCLE_elliptic ha) haE hbE hcE
  calc _ ≤ ‖(toEuclC2CLE (α := α) (ht := ht)).symm.toContinuousLinearMap‖ *
          (‖_‖ * ‖(toEuclDataCLE (α := α) (t₀ := t₀) (t₁ := t₁)).toContinuousLinearMap‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (C * 1) := mul_le_mul norm_toEuclC2CLE_symm_le
        (mul_le_mul hmid norm_toEuclDataCLE_le (norm_nonneg _) hC) (by positivity) zero_le_one
    _ = C := by ring

/-- **Lipschitz dependence of the weighted log-spot solution operator on `(a, r)`.** Under the
bounds of `exists_norm_weightedLogSpotTerminalDataCLE_symm_le`, the solution operators for `(a, r)`
and `(a', r')` differ in operator norm by at most `C (‖a - a'‖ + ‖r - r'‖)`. -/
theorem exists_norm_weightedLogSpotTerminalDataCLE_symm_sub_le {α : ℝ≥0} (hα₀ : 0 < α)
    (hα₁ : α < 1) {δ : ℝ} (hδ : 0 < δ) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t₀ t₁ : ℝ} (ht : t₀ < t₁), t₁ - t₀ ≤ T₀ →
      ∀ (a a' r r' : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)
        (ha : ∀ p, δ ≤ a p) (ha' : ∀ p, δ ≤ a' p),
        ‖a‖ ≤ K → ‖r‖ ≤ K → ‖a'‖ ≤ K → ‖r'‖ ≤ K →
        ‖(weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r
            ⟨δ, hδ, ha⟩).symm.toContinuousLinearMap -
          (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a' r'
            ⟨δ, hδ, ha'⟩).symm.toContinuousLinearMap‖ ≤ C * (‖a - a'‖ + ‖r - r'‖) := by
  let C₁ : ℝ≥0 := ‖((2 : ℝ) • sigmoidHolder hα₁.le - 1 : HolderSpace α ℝ ℝ)‖₊
  let C₀ : ℝ≥0 := ‖(1 - sigmoidHolder hα₁.le : HolderSpace α ℝ ℝ)‖₊
  obtain ⟨C, hC, hest⟩ := exists_norm_euclideanTerminalDataCLE_symm_sub_le (ι := Unit) hα₀ hα₁ hδ
    (weightedCoeffBound hα₁.le K) T₀
  refine ⟨C * (1 + C₁ + C₀), by positivity,
    fun {t₀ t₁} ht hTT₀ a a' r r' ha ha' hak hrk hak' hrk' ↦ ?_⟩
  rw [weightedLogSpotTerminalDataCLE_symm_eq hα₀ hα₁ ht a r hδ ha,
    weightedLogSpotTerminalDataCLE_symm_eq hα₀ hα₁ ht a' r' hδ ha',
    ← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.sub_comp]
  obtain ⟨haE, hbE, hcE⟩ := norm_toEuclSlabCLE_coeffs_le hα₁.le hak hrk
  obtain ⟨haE', hbE', hcE'⟩ := norm_toEuclSlabCLE_coeffs_le hα₁.le hak' hrk'
  have hmid := hest ht hTT₀ (fun _ _ ↦ toEuclSlabCLE a) (fun _ _ ↦ toEuclSlabCLE a')
    (fun _ ↦ toEuclSlabCLE (weightedDriftScalar hα₁.le a r))
    (fun _ ↦ toEuclSlabCLE (weightedDriftScalar hα₁.le a' r'))
    (toEuclSlabCLE (weightedRateScalar hα₁.le r)) (toEuclSlabCLE (weightedRateScalar hα₁.le r'))
    (toEuclSlabCLE_elliptic ha) (toEuclSlabCLE_elliptic ha') haE hbE hcE haE' hbE' hcE'
  simp only [Fintype.sum_unique, ← map_sub] at hmid
  have hsum : ‖toEuclSlabCLE (a - a')‖ +
      ‖toEuclSlabCLE (weightedDriftScalar hα₁.le a r - weightedDriftScalar hα₁.le a' r')‖ +
      ‖toEuclSlabCLE (weightedRateScalar hα₁.le r - weightedRateScalar hα₁.le r')‖ ≤
      (1 + (C₁ : ℝ) + C₀) * (‖a - a'‖ + ‖r - r'‖) := by
    have h₁ := norm_toEuclSlabCLE_apply_le (a - a')
    have h₂ : ‖toEuclSlabCLE (weightedDriftScalar hα₁.le a r - weightedDriftScalar hα₁.le a' r')‖ ≤
        ‖r - r'‖ + ‖a - a'‖ * (C₁ : ℝ) :=
      (norm_toEuclSlabCLE_apply_le _).trans (by
        simpa only [C₁, coe_nnNorm] using norm_weightedDriftScalar_sub_le hα₁.le a a' r r')
    have h₃ : ‖toEuclSlabCLE (weightedRateScalar hα₁.le r - weightedRateScalar hα₁.le r')‖ ≤
        ‖r - r'‖ * (C₀ : ℝ) :=
      (norm_toEuclSlabCLE_apply_le _).trans (by
        simpa only [C₀, coe_nnNorm] using norm_weightedRateScalar_sub_le hα₁.le r r')
    nlinarith [norm_nonneg (a - a'), norm_nonneg (r - r'), C₁.coe_nonneg, C₀.coe_nonneg]
  calc _ ≤ 1 * ((C * ((1 + (C₁ : ℝ) + C₀) * (‖a - a'‖ + ‖r - r'‖))) * 1) := by
        refine ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
            (norm_nonneg _))).trans ?_
        exact mul_le_mul norm_toEuclC2CLE_symm_le
          (mul_le_mul (hmid.trans (mul_le_mul_of_nonneg_left hsum hC)) norm_toEuclDataCLE_le
            (norm_nonneg _) (by positivity)) (by positivity) zero_le_one
    _ = C * (1 + C₁ + C₀) * (‖a - a'‖ + ‖r - r'‖) := by ring

end TerminalDataCLE

/-! ### Market coefficient fields -/

section MarketCoefficients

variable {α : ℝ≥0} {t₀ t₁ : ℝ}

/-- If `σ(e^y, t)` is bounded on `ℝ × [t₀, t₁]`, uniformly Lipschitz in `y` for each `t ∈ [t₀, t₁]`,
and uniformly `(α / 2)`-Hölder in `t` on `[t₀, t₁]` for each `y ∈ ℝ`, then `(y, t) ↦ σ(e^y, t)` is
parabolically `α`-Hölder on `slab t₀ t₁` (`α ≤ 1`). -/
theorem memHolder_slab_of_lipschitz_exp_of_holderOnWith (hα : α ≤ 1) {σ : ℝ → ℝ → ℝ}
    {M L H : ℝ≥0} (hbdd : ∀ y, ∀ t ∈ Icc t₀ t₁, |σ (exp y) t| ≤ M)
    (hlip : ∀ t ∈ Icc t₀ t₁, LipschitzWith L (fun y ↦ σ (exp y) t))
    (htime : ∀ y, HolderOnWith H (α / 2) (σ (exp y)) (Icc t₀ t₁)) :
    MemHolder α
      (fun p : slab (E := ℝ) t₀ t₁ ↦ σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p)) := by
  rw [memHolder_slab_iff]
  refine ⟨?_, ?_⟩
  · refine ((spaceEHolderNorm_le_iff (a := t₀) (b := t₁)
        (C := ((L + 2 * M : ℝ≥0) : ℝ≥0∞))).2 fun t x y ↦ ?_).trans_lt ENNReal.coe_lt_top
    have hslice := ((hlip t t.2).lipschitzOnWith (s := univ)).holderOnWith_of_norm_le
      (M := M) (fun z _ ↦ by simpa only [Real.norm_eq_abs] using hbdd z t t.2) hα
    simpa only [slabTime_slabMk, space_slabMk] using hslice x (mem_univ x) y (mem_univ y)
  · refine ((timeEHolderNorm_le_iff (a := t₀) (b := t₁)
        (C := (H : ℝ≥0∞))).2 fun x t s ↦ ?_).trans_lt ENNReal.coe_lt_top
    simpa only [slabTime_slabMk, space_slabMk, Subtype.edist_eq] using htime x t t.2 s s.2

/-- The log-spot half-variance field `a(y, t) = σ(e^y, t)² / 2` as an element of
`HolderSpace α (slab t₀ t₁) ℝ`, built from a bounded parabolically `α`-Hölder volatility
(`0 < α`). -/
def logSpotHalfVarianceHolder (hα₀ : 0 < α) (σ : ℝ → ℝ → ℝ) {M : ℝ}
    (hbdd : ∀ y, ∀ t ∈ Icc t₀ t₁, |σ (exp y) t| ≤ M)
    (hσ : MemHolder α (fun p : slab (E := ℝ) t₀ t₁ ↦
      σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p))) :
    HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ :=
  let f : slab (E := ℝ) t₀ t₁ → ℝ := fun p ↦
    σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p)
  let σB : slab (E := ℝ) t₀ t₁ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup f
    (hσ.holderWith.continuous hα₀) M fun p ↦ by
      simpa only [f, Real.norm_eq_abs] using hbdd _ _ (slabTime p).2
  have hcoe : (σB : slab (E := ℝ) t₀ t₁ → ℝ) = f :=
    BoundedContinuousFunction.coe_ofNormedAddCommGroup _ _ _ _
  (2⁻¹ : ℝ) • (HolderSpace.ofBoundedContinuousFunction σB (hcoe.symm ▸ hσ)) ^ 2

/-- Evaluation of `logSpotHalfVarianceHolder` at a slab point gives `σ(e^y, t)² / 2`. -/
@[simp]
theorem logSpotHalfVarianceHolder_apply (hα₀ : 0 < α) (σ : ℝ → ℝ → ℝ) {M : ℝ}
    (hbdd : ∀ y, ∀ t ∈ Icc t₀ t₁, |σ (exp y) t| ≤ M)
    (hσ : MemHolder α (fun p : slab (E := ℝ) t₀ t₁ ↦
      σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p)))
    (p : slab (E := ℝ) t₀ t₁) :
    logSpotHalfVarianceHolder hα₀ σ hbdd hσ p =
      σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p) ^ 2 / 2 := by
  rw [logSpotHalfVarianceHolder, HolderSpace.smul_apply, HolderSpace.pow_apply,
    HolderSpace.ofBoundedContinuousFunction_apply]
  have hcoe : ∀ q : slab (E := ℝ) t₀ t₁,
      BoundedContinuousFunction.ofNormedAddCommGroup
        (fun p : slab (E := ℝ) t₀ t₁ ↦ σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p))
        (hσ.holderWith.continuous hα₀) M
        (fun p ↦ by simpa only [Real.norm_eq_abs] using hbdd _ _ (slabTime p).2) q =
      σ (exp (q : ParabolicSpaceTime ℝ).space) (slabTime q) :=
    congrFun (BoundedContinuousFunction.coe_ofNormedAddCommGroup _ _ _ _)
  rw [hcoe, smul_eq_mul]
  ring

/-- A time-only short rate `r : ℝ → ℝ` that is `(α / 2)`-Hölder on `[t₀, t₁]` (`0 < α`), promoted
via `HolderSpace.compSlabTimeL` to a space-independent parabolic `α`-Hölder field on
`slab (E := ℝ) t₀ t₁`. -/
def shortRateHolder (hα₀ : 0 < α) (r : ℝ → ℝ) {H : ℝ≥0}
    (hr : HolderOnWith H (α / 2) r (Icc t₀ t₁)) :
    HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ :=
  have hcont : Continuous (fun t : Icc t₀ t₁ ↦ r t) :=
    HolderWith.continuous (C := H) (r := α / 2)
      (fun t s ↦ by simpa only [Subtype.edist_eq] using hr t t.2 s s.2)
      (div_pos hα₀ two_pos)
  let rB : Icc t₀ t₁ →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨fun t ↦ r t, hcont⟩
  HolderSpace.compSlabTimeL <|
    HolderSpace.ofBoundedContinuousFunction rB <|
      HolderWith.memHolder (C := H) fun t s ↦ by
        simp only [rB, BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk]
        simpa only [Subtype.edist_eq] using hr t t.2 s s.2

/-- Evaluation of `shortRateHolder` at a slab point gives `r` at its time coordinate. -/
@[simp]
theorem shortRateHolder_apply (hα₀ : 0 < α) (r : ℝ → ℝ) {H : ℝ≥0}
    (hr : HolderOnWith H (α / 2) r (Icc t₀ t₁)) (p : slab (E := ℝ) t₀ t₁) :
    shortRateHolder hα₀ r hr p = r (slabTime p) := by
  simp only [shortRateHolder, HolderSpace.compSlabTimeL_apply,
    HolderSpace.ofBoundedContinuousFunction_apply, BoundedContinuousFunction.mkOfCompact_apply,
    ContinuousMap.coe_mk]

end MarketCoefficients

/-! ### Classical spot-coordinate pricing PDE existence and uniqueness -/

section SpotPricingPDE

/-- **Uniqueness of classical linear-growth prices on `[t₀, t₁]`.** Let `σ² ≤ Λ` and `|r| ≤ R` on
`(t₀, t₁)`. If `u ∈ C_b^{2+α,1+α/2}(ℝ × [t₀, t₁])` solves `weightedLogSpotPricingOperatorL u = 0`
with terminal payoff `h`, then `weightedLogSpotPrice u` is the unique classical solution of the
spot pricing PDE on `(0, ∞) × [t₀, t₁]` satisfying `|C(s, t)| ≤ A (1 + s)`. -/
theorem eq_weightedLogSpotPrice_of_pde {α : ℝ≥0} {t₀ t₁ : ℝ} {ht : t₀ < t₁} (hα : α ≤ 1)
    {σ : ℝ → ℝ → ℝ} {r h : ℝ → ℝ} {Λ R A : ℝ}
    {a rH : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    (ha_eq : ∀ ⦃s⦄, 0 < s → ∀ t : Icc t₀ t₁, a (slabMk (log s) t) = σ s t ^ 2 / 2)
    (hr_eq : ∀ ⦃s⦄, 0 < s → ∀ t : Icc t₀ t₁, rH (slabMk (log s) t) = r t)
    (hσ : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → σ s t ^ 2 ≤ Λ)
    (hr : ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → |r t| ≤ R)
    (u : ParabolicC2HolderSpace α ℝ ℝ ht)
    (hPu : weightedLogSpotPricingOperatorL hα a rH u = 0)
    (huterm : ∀ y, u (slabMk y ⟨t₁, right_mem_Icc.2 ht.le⟩) = h (exp y) / (1 + exp y))
    {C : ℝ → ℝ → ℝ}
    (hC_cont : ContinuousOn (Function.uncurry C) (Ioi 0 ×ˢ Icc t₀ t₁))
    (hC_growth : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ → |C s t| ≤ A * (1 + s))
    (hC_cd : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → ContDiffAt ℝ 2 (fun x ↦ C x t) s)
    (hC_diff : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → DifferentiableAt ℝ (fun τ ↦ C s τ) t)
    (hC_pde : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ →
      deriv (fun τ ↦ C s τ) t + σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ C x t) s +
        r t * (s * deriv (fun x ↦ C x t) s - C s t) = 0)
    (hC_term : ∀ ⦃s⦄, 0 < s → C s t₁ = h s) :
    ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ → C s t = weightedLogSpotPrice u s t := by
  let W := weightedLogSpotPrice u
  have hshift_Icc {τ : ℝ} (hτ : τ ∈ Icc 0 (t₁ - t₀)) : t₀ + τ ∈ Icc t₀ t₁ :=
    ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hshift_Ioo {τ : ℝ} (hτ : τ ∈ Ioo 0 (t₁ - t₀)) : t₀ + τ ∈ Ioo t₀ t₁ :=
    ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hderiv_shift (F : ℝ → ℝ) {τ : ℝ} (hF : DifferentiableAt ℝ F (t₀ + τ)) :
      deriv (fun τ' ↦ F (t₀ + τ')) τ = deriv F (t₀ + τ) := by
    have hd : HasDerivAt (fun τ' ↦ F (t₀ + τ')) (deriv F (t₀ + τ) * 1) τ :=
      hF.hasDerivAt.comp τ ((hasDerivAt_id' τ).const_add t₀)
    simpa only [mul_one] using hd.deriv
  have heq := eq_of_pde_eq_of_terminal_eq
    (σ := fun s τ ↦ σ s (t₀ + τ)) (r := fun τ ↦ r (t₀ + τ))
    (C₁ := fun s τ ↦ C s (t₀ + τ)) (C₂ := fun s τ ↦ W s (t₀ + τ))
    (T := t₁ - t₀) (Λ := Λ) (R := R) (A := max A 0 + ‖u‖)
    (fun s hs τ hτ ↦ hσ hs (hshift_Ioo hτ))
    (fun τ hτ ↦ hr (hshift_Ioo hτ))
    (hC_cont.comp (f := fun p : ℝ × ℝ ↦ (p.1, t₀ + p.2)) (by fun_prop)
      fun p hp ↦ ⟨hp.1, hshift_Icc hp.2⟩)
    ((continuousOn_weightedLogSpotPrice u).comp (f := fun p : ℝ × ℝ ↦ (p.1, t₀ + p.2))
      (by fun_prop) fun p hp ↦ ⟨hp.1, mem_univ _⟩)
    (fun s hs τ hτ ↦ by
      have h1 := hC_growth hs (hshift_Icc hτ)
      have h2 := abs_weightedLogSpotPrice_le u hs.le (t₀ + τ)
      calc |C s (t₀ + τ) - W s (t₀ + τ)|
          ≤ |C s (t₀ + τ)| + |W s (t₀ + τ)| := abs_sub _ _
        _ ≤ A * (1 + s) + ‖u‖ * (1 + s) := add_le_add h1 h2
        _ ≤ (max A 0 + ‖u‖) * (1 + s) := by nlinarith [le_max_left A 0, hs.le])
    (fun s hs τ hτ ↦ hC_cd hs (hshift_Ioo hτ))
    (fun s hs τ hτ ↦ (contDiffOn_weightedLogSpotPrice u
      ⟨t₀ + τ, Ioo_subset_Icc_self (hshift_Ioo hτ)⟩).contDiffAt (Ioi_mem_nhds hs))
    (fun s hs τ hτ ↦ (hC_diff hs (hshift_Ioo hτ)).comp τ
      (differentiableAt_id.const_add t₀))
    (fun s _ τ hτ ↦ (differentiableAt_weightedLogSpotPrice_time u s (hshift_Ioo hτ)).comp τ
      (differentiableAt_id.const_add t₀))
    (fun s hs τ hτ ↦ by
      have ht' := hshift_Ioo hτ
      rw [hderiv_shift (C s) (hC_diff hs ht'),
        hderiv_shift (W s) (differentiableAt_weightedLogSpotPrice_time u s ht'),
        hC_pde hs ht', pde_weightedLogSpotPrice_eq_mul_weightedLogSpotPricingOperatorL_of_mem_Ioo
          hα a rH u hs ht' (ha_eq hs ⟨t₀ + τ, Ioo_subset_Icc_self ht'⟩)
          (hr_eq hs ⟨t₀ + τ, Ioo_subset_Icc_self ht'⟩),
        hPu, HolderSpace.zero_apply, mul_zero])
    (fun s hs ↦ by
      have ht₁ : t₀ + (t₁ - t₀) = t₁ := by ring
      dsimp only [W]
      rw [ht₁, hC_term hs, weightedLogSpotPrice_terminal u huterm hs])
  intro s hs t ht'
  have h := heq hs (t := t - t₀) ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
  simpa only [add_sub_cancel] using h

/-- **Existence, linear-growth bounds, and uniqueness for the self-financing pricing PDE.**
Let `0 < α < 1`, `t₀ < t₁`, `0 < δ`, let `σ(s, t)` satisfy `δ ≤ σ(s, t)²` and `|σ(e^y, t)| ≤ M`
with `σ(e^y, t)` uniformly Lipschitz in `y` and uniformly `(α / 2)`-Hölder in `t`, let `r` be
`(α / 2)`-Hölder on `[t₀, t₁]`, and let `h` be a terminal payoff whose weighted log-spot profile
`y ↦ h(e^y) / (1 + e^y)` is represented by `g ∈ C_b^{2,α}(ℝ)`. Then there exists a unique
`u ∈ C_b^{2+α,1+α/2}(ℝ × [t₀, t₁])` solving the weighted log-spot terminal-value problem, and its
reconstructed spot price `C = weightedLogSpotPrice u` is the unique classical solution of the
pricing PDE in the linear-growth class, with joint continuity of `C` and `∂ₛC` and linear-growth
bounds on both the price and the dollar-delta exposure. -/
theorem exists_weightedLogSpotPrice_pde_and_unique {α : ℝ≥0} {t₀ t₁ : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t₀ < t₁)
    {σ : ℝ → ℝ → ℝ} {r h : ℝ → ℝ} {δ : ℝ} {M L H H_r : ℝ≥0}
    (hδ : 0 < δ)
    (hσ_low : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ → δ ≤ σ s t ^ 2)
    (hσ_bdd : ∀ y, ∀ t ∈ Icc t₀ t₁, |σ (exp y) t| ≤ M)
    (hσ_lip : ∀ t ∈ Icc t₀ t₁, LipschitzWith L (fun y ↦ σ (exp y) t))
    (hσ_time : ∀ y, HolderOnWith H (α / 2) (σ (exp y)) (Icc t₀ t₁))
    (hr_hol : HolderOnWith H_r (α / 2) r (Icc t₀ t₁))
    (g : CkHolderSpace 2 α ℝ ℝ) (hg : ∀ y, g y = h (exp y) / (1 + exp y)) :
    ∃ u : ParabolicC2HolderSpace α ℝ ℝ ht,
      weightedLogSpotPricingOperatorL hα₁.le
          (logSpotHalfVarianceHolder hα₀ σ hσ_bdd
            (memHolder_slab_of_lipschitz_exp_of_holderOnWith hα₁.le hσ_bdd hσ_lip hσ_time))
          (shortRateHolder hα₀ r hr_hol) u = 0 ∧
      u.spatialTrace ⟨t₁, right_mem_Icc.2 ht.le⟩ = g ∧
      (∀ s > 0, weightedLogSpotPrice u s t₁ = h s) ∧
      ContinuousOn (Function.uncurry (weightedLogSpotPrice u)) (Ioi 0 ×ˢ Icc t₀ t₁) ∧
      ContinuousOn (fun p : ℝ × ℝ ↦ deriv (fun s ↦ weightedLogSpotPrice u s p.2) p.1)
        (Ioi 0 ×ˢ Icc t₀ t₁) ∧
      (∀ s > 0, ∀ t ∈ Icc t₀ t₁,
        ContDiffAt ℝ 2 (fun x ↦ weightedLogSpotPrice u x t) s ∧
          |weightedLogSpotPrice u s t| + |s * deriv (fun x ↦ weightedLogSpotPrice u x t) s| ≤
            2 * ‖u‖ * (1 + s)) ∧
      (∀ s > 0, ∀ t ∈ Ioo t₀ t₁,
        DifferentiableAt ℝ (weightedLogSpotPrice u s) t ∧
          deriv (weightedLogSpotPrice u s) t +
              σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ weightedLogSpotPrice u x t) s +
              r t * (s * deriv (fun x ↦ weightedLogSpotPrice u x t) s -
                weightedLogSpotPrice u s t) = 0) ∧
      ∀ (C : ℝ → ℝ → ℝ) (A : ℝ),
        ContinuousOn (Function.uncurry C) (Ioi 0 ×ˢ Icc t₀ t₁) →
        (∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ → |C s t| ≤ A * (1 + s)) →
        (∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → ContDiffAt ℝ 2 (fun x ↦ C x t) s) →
        (∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → DifferentiableAt ℝ (fun τ ↦ C s τ) t) →
        (∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ →
          deriv (fun τ ↦ C s τ) t + σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ C x t) s +
            r t * (s * deriv (fun x ↦ C x t) s - C s t) = 0) →
        (∀ ⦃s⦄, 0 < s → C s t₁ = h s) →
        ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ → C s t = weightedLogSpotPrice u s t := by
  have hmem := memHolder_slab_of_lipschitz_exp_of_holderOnWith hα₁.le hσ_bdd hσ_lip hσ_time
  let a := logSpotHalfVarianceHolder hα₀ σ hσ_bdd hmem
  let rH := shortRateHolder hα₀ r hr_hol
  have ha : ∀ p, δ / 2 ≤ a p := fun p ↦ by
    rw [logSpotHalfVarianceHolder_apply]
    exact div_le_div_of_nonneg_right (hσ_low (exp_pos _) (slabTime p).2) zero_le_two
  let u := (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a rH ⟨δ / 2, half_pos hδ, ha⟩).symm (0, g)
  have hPu : weightedLogSpotPricingOperatorL hα₁.le a rH u = 0 :=
    weightedLogSpotPricingOperatorL_weightedLogSpotTerminalDataCLE_symm_apply (0, g)
  have htr : u.spatialTrace ⟨t₁, right_mem_Icc.2 ht.le⟩ = g :=
    spatialTrace_weightedLogSpotTerminalDataCLE_symm_apply (0, g)
  have huterm : ∀ y, u (slabMk y ⟨t₁, right_mem_Icc.2 ht.le⟩) = h (exp y) / (1 + exp y) :=
    fun y ↦ by rw [← spatialTrace_apply, htr, hg]
  refine ⟨u, hPu, htr, fun s hs ↦ weightedLogSpotPrice_terminal u huterm hs,
    (continuousOn_weightedLogSpotPrice u).mono (prod_mono_right (subset_univ _)),
    continuousOn_deriv_weightedLogSpotPrice_spot u,
    fun s hs t ht' ↦ ⟨(contDiffOn_weightedLogSpotPrice u ⟨t, ht'⟩).contDiffAt (Ioi_mem_nhds hs),
      abs_weightedLogSpotPrice_add_abs_mul_deriv_le u hs ht'⟩,
    fun s hs t ht' ↦ ⟨differentiableAt_weightedLogSpotPrice_time u s ht', ?_⟩,
    fun C A hCc hCg hCcd hCd hCpde hCt ↦ ?_⟩
  · rw [pde_weightedLogSpotPrice_eq_mul_weightedLogSpotPricingOperatorL_of_mem_Ioo hα₁.le a rH u hs
      ht' (by simp [a, exp_log hs]) (by simp [rH]), hPu, HolderSpace.zero_apply, mul_zero]
  · exact eq_weightedLogSpotPrice_of_pde hα₁.le
      (fun s hs t ↦ by simp [a, exp_log hs]) (fun s _ t ↦ by simp [rH])
      (fun s hs t ht' ↦ by
        have h1 := hσ_bdd (log s) t (Ioo_subset_Icc_self ht')
        rw [exp_log hs] at h1
        exact (sq_abs (σ s t)).symm.trans_le (pow_le_pow_left₀ (abs_nonneg _) h1 2))
      (fun t ht' ↦ by
        simpa only [rH, Real.norm_eq_abs, shortRateHolder_apply, slabTime_slabMk] using
          rH.norm_apply_le (slabMk 0 ⟨t, Ioo_subset_Icc_self ht'⟩))
      u hPu huterm hCc hCg hCcd hCd hCpde hCt

end SpotPricingPDE

end TauCeti.Finance
