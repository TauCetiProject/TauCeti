/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.Pricing.Operator
import TauCeti.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.Matrix.QuadraticBounds
import TauCeti.Analysis.PDE.Parabolic.Holder.CompSpatial
import TauCeti.Analysis.PDE.Parabolic.Holder.Solvability
import TauCeti.Probability.Finance.Comparison
import TauCeti.Topology.MetricSpace.Lipschitz.Basic

/-!
# Solvability of the weighted log-spot and classical pricing terminal-value problems

For `0 < α < 1`, a time horizon `t₀ < t₁`, and coefficient fields `a` and `r` in the bounded
parabolic Hölder space `C_b^{α,α/2}(ℝ × [t₀, t₁])` with `a` uniformly positive (`0 < λ ≤ a`), the
weighted log-spot pricing operator
`P u = ∂ₜu + a ∂ᵧ²u + (r + a (2 sigmoid y - 1)) ∂ᵧu - r (1 - sigmoid y) u`
(`TauCeti.Finance.weightedLogSpotPricingOperatorL`) defines a Banach-space isomorphism
`u ↦ (P u, u(·, t₁))` from `C_b^{2+α,1+α/2}(ℝ × [t₀, t₁])` onto
`C_b^{α,α/2}(ℝ × [t₀, t₁]) × C_b^{2,α}(ℝ)` (`TauCeti.Finance.weightedLogSpotTerminalDataCLE`). Its
inverse is bounded uniformly over horizons `t₁ - t₀ ≤ T₀` and coefficient bounds `‖a‖, ‖r‖ ≤ K`,
and depends Lipschitz continuously on `(a, r)` in operator norm. Specializing to zero forcing
yields the continuous linear terminal solution operator `g ↦ u`
(`TauCeti.Finance.weightedLogSpotTerminalSolutionL`) together with its discounted supremum bound
when the short rate is bounded below.

The second half of the file connects this Banach-space isomorphism to the financial coefficients
and spot-coordinate PDE:
* `halfSqVolatility`, `logSpotRiskNeutralDrift`, and `logSpotVolatilityHolder` assemble parabolic
  Hölder diffusion and drift fields from a local volatility `σ(s, t)` and short rate `r(t)` (paired
  with `HolderSpace.ofHolderTime` for time-dependent rates);
* `weightedLogSpotTerminalPrice` reconstructs the classical linear-growth spot price
  `C(s, t) = (1 + s) u(log s, t)` solving `C_t + σ² s² / 2 C_ss + r (s C_s - C) = 0` in all three
  time-derivative conventions (within `[t₀, t₁]`, within `[t₀, ∞)` before maturity, and ordinary on
  `(t₀, t₁)`), with sharp linear growth in both `C` and `s C_s`;
* `exists_weightedLogSpotPrice_terminal_and_pde` and `eq_weightedLogSpotPrice_of_pde_of_terminal`
  combine existence in weighted log-spot spaces with uniqueness in the classical linear-growth
  class on any horizon `[t₀, t₁]`.

## Reduction to the Euclidean backward terminal-value problem

Identifying `ℝ` isometrically with `EuclideanSpace ℝ Unit` via
`(OrthonormalBasis.singleton Unit ℝ).repr.symm` (`ParabolicC2HolderSpace.compSpatialCLE`)
intertwines `(P u, u(·, t₁))` on `ℝ × [t₀, t₁]` with the general backward terminal-data
isomorphism `ParabolicC2HolderSpace.euclideanTerminalDataCLE` on `ℝ¹ × [t₀, t₁]`. Both spatial
transport equivalences have operator norm at most `1` in each direction and are independent of
`(a, r)`, so the uniform Schauder bound and Lipschitz coefficient dependence transfer directly from
`exists_norm_euclideanTerminalDataCLE_symm_le` and
`exists_norm_euclideanTerminalDataCLE_symm_sub_le`.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Prentice-Hall, 1964, Chapter 2,
  Section 4, and Chapter 3.
* N. V. Krylov, *Lectures on Elliptic and Parabolic Equations in Hölder Spaces*, AMS, 1996,
  Chapter 8.
* A. Lunardi, *Linear and Nonlinear Diffusion Problems*, Cortona lecture notes, 2004, Chapter 4.
* P. Wilmott, S. Howison, J. Dewynne, *The Mathematics of Financial Derivatives*, Cambridge
  University Press, 1995, §5.4.
-/

public section
noncomputable section

open _root_.Real Set Filter Topology

namespace TauCeti.Finance

open ParabolicSpaceTime ContinuousLinearMap ParabolicC2HolderSpace
open scoped NNReal

/-! ### Spatial isometric bridge between `ℝ × [t₀, t₁]` and `ℝ¹ × [t₀, t₁]` -/

section Bridge

private abbrev unitToRealLIE : EuclideanSpace ℝ Unit ≃ₗᵢ[ℝ] ℝ :=
  (OrthonormalBasis.singleton Unit ℝ).repr.symm

private def sigmoidHolder {α : ℝ≥0} (hα : α ≤ 1) : HolderSpace α ℝ ℝ :=
  HolderSpace.compLeftL (apply ℝ ℝ (1 : ℝ)) (logOneAddExpGrad hα)

@[simp] private theorem sigmoidHolder_apply {α : ℝ≥0} (hα : α ≤ 1) (x : ℝ) :
    sigmoidHolder hα x = sigmoid x := by
  simp [sigmoidHolder, HolderSpace.compLeftL_apply, logOneAddExpGrad_apply]

private def weightedFirstScalar {α : ℝ≥0} {t₀ t₁ : ℝ} (hα : α ≤ 1)
    (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ :=
  r + a * ((2 : ℝ) • HolderSpace.compSlabSpaceL (sigmoidHolder hα) - HolderSpace.const 1)

private def weightedZerothScalar {α : ℝ≥0} {t₀ t₁ : ℝ} (hα : α ≤ 1)
    (r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ :=
  -(r * (HolderSpace.const 1 - HolderSpace.compSlabSpaceL (sigmoidHolder hα)))

@[simp] private theorem weightedFirstScalar_apply {α : ℝ≥0} {t₀ t₁ : ℝ} (hα : α ≤ 1)
    (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) (p : slab (E := ℝ) t₀ t₁) :
    weightedFirstScalar hα a r p =
      r p + a p * (2 * sigmoid (p : ParabolicSpaceTime ℝ).space - 1) := by
  simp [weightedFirstScalar]

@[simp] private theorem weightedZerothScalar_apply {α : ℝ≥0} {t₀ t₁ : ℝ} (hα : α ≤ 1)
    (r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) (p : slab (E := ℝ) t₀ t₁) :
    weightedZerothScalar hα r p = -(r p * (1 - sigmoid (p : ParabolicSpaceTime ℝ).space)) := by
  simp [weightedZerothScalar]

private theorem norm_compSlabSpaceL_sigmoidHolder_le {α : ℝ≥0} {t₀ t₁ : ℝ} (hα : α ≤ 1) :
    ‖HolderSpace.compSlabSpaceL (a := t₀) (b := t₁) (sigmoidHolder hα)‖ ≤ 2 := by
  have h₁ : ‖apply ℝ ℝ (1 : ℝ)‖ ≤ 1 :=
    opNorm_le_bound _ zero_le_one fun L ↦ by simpa using L.le_opNorm (1 : ℝ)
  have h₂ : ‖sigmoidHolder hα‖ ≤ 2 :=
    (((HolderSpace.compLeftL (apply ℝ ℝ (1 : ℝ))).le_of_opNorm_le
      ((HolderSpace.norm_compLeftL_le _).trans h₁) _).trans
      (mul_le_mul_of_nonneg_left (norm_logOneAddExpGrad_le hα) zero_le_one)).trans_eq (one_mul 2)
  exact ((HolderSpace.compSlabSpaceL (a := t₀) (b := t₁)).le_of_opNorm_le
    HolderSpace.norm_compSlabSpaceL_le_one _).trans ((one_mul _).trans_le h₂)

private theorem norm_weightedFirstScalar_le {α : ℝ≥0} {t₀ t₁ : ℝ} (hα : α ≤ 1)
    (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) :
    ‖weightedFirstScalar hα a r‖ ≤ ‖r‖ + 5 * ‖a‖ := by
  have hfactor : ‖(2 : ℝ) • HolderSpace.compSlabSpaceL (a := t₀) (b := t₁) (sigmoidHolder hα) -
      HolderSpace.const (1 : ℝ)‖ ≤ 5 :=
    (norm_sub_le _ _).trans (by
      rw [norm_smul, _root_.Real.norm_ofNat]
      linarith [norm_compSlabSpaceL_sigmoidHolder_le (t₀ := t₀) (t₁ := t₁) hα,
        (HolderSpace.norm_const_le (α := α) (X := slab (E := ℝ) t₀ t₁) (1 : ℝ)).trans_eq norm_one])
  exact (norm_add_le _ _).trans (add_le_add le_rfl
    ((norm_mul_le _ _).trans (by nlinarith [norm_nonneg a])))

private theorem norm_weightedZerothScalar_le {α : ℝ≥0} {t₀ t₁ : ℝ} (hα : α ≤ 1)
    (r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) :
    ‖weightedZerothScalar hα r‖ ≤ 3 * ‖r‖ := by
  have hfactor : ‖HolderSpace.const (1 : ℝ) -
      HolderSpace.compSlabSpaceL (a := t₀) (b := t₁) (sigmoidHolder hα)‖ ≤ 3 :=
    (norm_sub_le _ _).trans (by
      linarith [norm_compSlabSpaceL_sigmoidHolder_le (t₀ := t₀) (t₁ := t₁) hα,
        (HolderSpace.norm_const_le (α := α) (X := slab (E := ℝ) t₀ t₁) (1 : ℝ)).trans_eq norm_one])
  rw [weightedZerothScalar, norm_neg]
  exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg r])

private def slabSpaceUnitEquiv (t₀ t₁ : ℝ) :
    slab (E := EuclideanSpace ℝ Unit) t₀ t₁ ≃ᵢ slab (E := ℝ) t₀ t₁ where
  toFun := slabSpaceMap unitToRealLIE
  invFun := slabSpaceMap unitToRealLIE.symm
  left_inv q := by rw [← slabMk_space_slabTime q]; simp
  right_inv p := by rw [← slabMk_space_slabTime p]; simp
  isometry_toFun q₁ q₂ := by
    rw [← slabMk_space_slabTime q₁, ← slabMk_space_slabTime q₂, slabSpaceMap_slabMk,
      slabSpaceMap_slabMk, edist_slabMk, edist_slabMk, unitToRealLIE.isometry.edist_eq]

private def pullbackUnitSlabCLE {α : ℝ≥0} (t₀ t₁ : ℝ) :
    HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ ≃L[ℝ]
      HolderSpace α (slab (E := EuclideanSpace ℝ Unit) t₀ t₁) ℝ :=
  ContinuousLinearEquiv.equivOfInverse
    (HolderSpace.compLipschitzL _ (slabSpaceUnitEquiv t₀ t₁).isometry.lipschitzWith)
    (HolderSpace.compLipschitzL _ (slabSpaceUnitEquiv t₀ t₁).symm.isometry.lipschitzWith)
    (fun f ↦ by ext p; simp) (fun g ↦ by ext q; simp)

@[simp] private theorem pullbackUnitSlabCLE_apply {α : ℝ≥0} (t₀ t₁ : ℝ)
    (f : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) (q : slab (E := EuclideanSpace ℝ Unit) t₀ t₁) :
    pullbackUnitSlabCLE t₀ t₁ f q = f (slabSpaceUnitEquiv t₀ t₁ q) :=
  HolderSpace.compLipschitzL_apply _ _ _

private theorem norm_pullbackUnitSlabCLE_apply_le {α : ℝ≥0} (t₀ t₁ : ℝ)
    (f : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) : ‖pullbackUnitSlabCLE t₀ t₁ f‖ ≤ ‖f‖ := by
  simpa using (pullbackUnitSlabCLE t₀ t₁).toContinuousLinearMap.le_of_opNorm_le
    (HolderSpace.norm_compLipschitzL_le_one (slabSpaceUnitEquiv t₀ t₁).isometry.lipschitzWith) f

private def toUnitC2CLE {α : ℝ≥0} {t₀ t₁ : ℝ} (ht : t₀ < t₁) :
    ParabolicC2HolderSpace α ℝ ℝ ht ≃L[ℝ]
      ParabolicC2HolderSpace α (EuclideanSpace ℝ Unit) ℝ ht :=
  compSpatialCLE α ℝ ht unitToRealLIE.toContinuousLinearEquiv

private theorem norm_toUnitC2CLE_symm_le_one {α : ℝ≥0} {t₀ t₁ : ℝ} (ht : t₀ < t₁) :
    ‖(toUnitC2CLE (α := α) ht).symm.toContinuousLinearMap‖ ≤ 1 := by
  let L : ℝ →L[ℝ] EuclideanSpace ℝ Unit := unitToRealLIE.symm.toContinuousLinearEquiv
  have hnorm : ‖L‖ ≤ 1 := unitToRealLIE.symm.toLinearIsometry.norm_toContinuousLinearMap_le
  rw [show (toUnitC2CLE (α := α) ht).symm.toContinuousLinearMap = compSpatialL α ℝ ht L from
    ContinuousLinearMap.ext fun v ↦ by simp [toUnitC2CLE, L, compSpatialCLE_symm_apply]]
  simpa using norm_compSpatialL_le_of_norm_le α ℝ ht le_rfl hnorm

private def dataUnitBridgeCLE {α : ℝ≥0} (t₀ t₁ : ℝ) :
    (HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) ≃L[ℝ]
      (HolderSpace α (slab (E := EuclideanSpace ℝ Unit) t₀ t₁) ℝ ×
        CkHolderSpace 2 α (EuclideanSpace ℝ Unit) ℝ) :=
  (pullbackUnitSlabCLE t₀ t₁).prodCongr
    (CkHolderSpace.compLinearCLE unitToRealLIE.toContinuousLinearEquiv)

private theorem norm_dataUnitBridgeCLE_le_one {α : ℝ≥0} (t₀ t₁ : ℝ) :
    ‖(dataUnitBridgeCLE (α := α) t₀ t₁).toContinuousLinearMap‖ ≤ 1 := by
  let L : EuclideanSpace ℝ Unit →L[ℝ] ℝ := unitToRealLIE.toContinuousLinearEquiv
  have he : ‖L‖ ≤ 1 := unitToRealLIE.toLinearIsometry.norm_toContinuousLinearMap_le
  have hck : ‖CkHolderSpace.compLinearL (k := 2) (α := α) (F := ℝ) L‖ ≤ 1 :=
    (CkHolderSpace.norm_compLinearL_le L).trans <| by
      rw [max_eq_left he, max_eq_left (_root_.Real.rpow_le_one (norm_nonneg _) he α.coe_nonneg)]
      norm_num
  refine opNorm_le_bound _ zero_le_one fun d ↦ ?_
  rw [one_mul, Prod.norm_def, Prod.norm_def]
  simp only [ContinuousLinearEquiv.coe_coe, dataUnitBridgeCLE,
    ContinuousLinearEquiv.prodCongr_apply, CkHolderSpace.compLinearCLE_apply]
  exact max_le ((norm_pullbackUnitSlabCLE_apply_le t₀ t₁ d.1).trans (le_max_left _ _))
    ((((CkHolderSpace.compLinearL L).le_of_opNorm_le hck d.2).trans_eq (one_mul _)).trans
      (le_max_right _ _))

private theorem norm_comp_unit_bridges_le {α : ℝ≥0} {t₀ t₁ : ℝ} (ht : t₀ < t₁)
    (T : HolderSpace α (slab (E := EuclideanSpace ℝ Unit) t₀ t₁) ℝ ×
        CkHolderSpace 2 α (EuclideanSpace ℝ Unit) ℝ →L[ℝ]
      ParabolicC2HolderSpace α (EuclideanSpace ℝ Unit) ℝ ht) :
    ‖(toUnitC2CLE ht).symm.toContinuousLinearMap ∘L T ∘L
        (dataUnitBridgeCLE t₀ t₁).toContinuousLinearMap‖ ≤ ‖T‖ :=
  (opNorm_comp_le _ _).trans <| (mul_le_of_le_one_left (norm_nonneg _)
    (norm_toUnitC2CLE_symm_le_one ht)).trans <| (opNorm_comp_le _ _).trans <|
    mul_le_of_le_one_right (norm_nonneg _) (norm_dataUnitBridgeCLE_le_one t₀ t₁)

private theorem euclideanBackwardParabolicOperatorL_toUnitC2CLE {α : ℝ≥0} {t₀ t₁ : ℝ}
    (hα : α ≤ 1) (ht : t₀ < t₁) (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)
    (u : ParabolicC2HolderSpace α ℝ ℝ ht) :
    euclideanBackwardParabolicOperatorL hα
        (fun _ _ : Unit ↦ pullbackUnitSlabCLE t₀ t₁ a)
        (fun _ : Unit ↦ pullbackUnitSlabCLE t₀ t₁ (weightedFirstScalar hα a r))
        (pullbackUnitSlabCLE t₀ t₁ (weightedZerothScalar hα r)) (toUnitC2CLE ht u) =
      pullbackUnitSlabCLE t₀ t₁ (weightedLogSpotPricingOperatorL hα a r u) := by
  let eL : EuclideanSpace ℝ Unit →L[ℝ] ℝ := unitToRealLIE.toContinuousLinearEquiv
  have he1 (i : Unit) : eL (EuclideanSpace.single i 1) = 1 := by
    cases i
    exact (OrthonormalBasis.singleton_repr_symm (EuclideanSpace.single () (1 : ℝ))).trans (by simp)
  rw [show toUnitC2CLE ht u = compSpatialL α ℝ ht eL u by
    simp [toUnitC2CLE, compSpatialCLE_apply, eL]]
  ext q
  have hsp : slabSpaceMap eL q = slabSpaceUnitEquiv t₀ t₁ q := rfl
  simp only [euclideanBackwardParabolicOperatorL_apply, Fintype.sum_unique,
    pullbackUnitSlabCLE_apply, weightedLogSpotPricingOperatorL_apply, weightedFirstScalar_apply,
    weightedZerothScalar_apply, timeDerivL_compSpatialL, spatialSecondFDerivL_compSpatialL,
    bilinearComp_apply, spatialFDerivL_compSpatialL, comp_apply, compSpatialL_apply, he1, hsp]
  ring

private theorem spatialTrace_toUnitC2CLE_right {α : ℝ≥0} {t₀ t₁ : ℝ} (ht : t₀ < t₁)
    (u : ParabolicC2HolderSpace α ℝ ℝ ht) :
    (toUnitC2CLE ht u).spatialTrace ⟨t₁, right_mem_Icc.2 ht.le⟩ =
      CkHolderSpace.compLinearCLE unitToRealLIE.toContinuousLinearEquiv
        (u.spatialTrace ⟨t₁, right_mem_Icc.2 ht.le⟩) := by
  simp [toUnitC2CLE, compSpatialCLE_apply, spatialTrace_compSpatialL]

private theorem ellipticity_pullbackUnitSlab {α : ℝ≥0} {t₀ t₁ : ℝ}
    {a : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ} {lam : ℝ} (hlam : ∀ p, lam ≤ a p)
    (q : slab (E := EuclideanSpace ℝ Unit) t₀ t₁) (ξ : EuclideanSpace ℝ Unit) :
    lam * ‖ξ‖ ^ 2 ≤
      (Matrix.of fun _ _ : Unit ↦ pullbackUnitSlabCLE t₀ t₁ a q).toQuadraticForm' ξ := by
  rw [Matrix.toQuadraticForm'_eq_mul_norm_sq]
  exact mul_le_mul_of_nonneg_right (by simpa using hlam _) (sq_nonneg _)

end Bridge

/-! ### Terminal-data Banach isomorphism and uniform Schauder bounds -/

section TerminalDataCLE

variable {α : ℝ≥0} {t₀ t₁ : ℝ}

/-- **The terminal-data isomorphism of the weighted log-spot pricing operator.** For `0 < α < 1`,
`t₀ < t₁`, and coefficients `a, r ∈ C_b^{α,α/2}(ℝ × [t₀, t₁])` with `a` uniformly positive, the
map `u ↦ (P u, u(·, t₁))` as a Banach-space isomorphism onto
`C_b^{α,α/2}(ℝ × [t₀, t₁]) × C_b^{2,α}(ℝ)`. -/
def weightedLogSpotTerminalDataCLE (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t₀ < t₁)
    (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p) :
    ParabolicC2HolderSpace α ℝ ℝ ht ≃L[ℝ]
      HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ :=
  (toUnitC2CLE ht).trans <|
    (euclideanTerminalDataCLE hα₀ hα₁ ht
      (fun _ _ : Unit ↦ pullbackUnitSlabCLE t₀ t₁ a)
      (fun _ : Unit ↦ pullbackUnitSlabCLE t₀ t₁ (weightedFirstScalar hα₁.le a r))
      (pullbackUnitSlabCLE t₀ t₁ (weightedZerothScalar hα₁.le r))
      (ha.elim fun lam h ↦ ⟨lam, h.1, ellipticity_pullbackUnitSlab h.2⟩)).trans
      (dataUnitBridgeCLE t₀ t₁).symm

section TerminalDataEval

variable {hα₀ : 0 < α} {hα₁ : α < 1} {ht : t₀ < t₁}
  {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ} {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p}

@[simp] theorem weightedLogSpotTerminalDataCLE_apply (u : ParabolicC2HolderSpace α ℝ ℝ ht) :
    weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha u =
      (weightedLogSpotPricingOperatorL hα₁.le a r u,
        u.spatialTrace ⟨t₁, right_mem_Icc.2 ht.le⟩) := by
  apply (dataUnitBridgeCLE t₀ t₁).injective
  simp [weightedLogSpotTerminalDataCLE, euclideanBackwardParabolicOperatorL_toUnitC2CLE,
    spatialTrace_toUnitC2CLE_right, dataUnitBridgeCLE]

@[simp] theorem weightedLogSpotPricingOperatorL_weightedLogSpotTerminalDataCLE_symm_apply
    (d : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) :
    weightedLogSpotPricingOperatorL hα₁.le a r
      ((weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).symm d) = d.1 := by
  have h := (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).apply_symm_apply d
  rw [weightedLogSpotTerminalDataCLE_apply] at h; exact congrArg Prod.fst h

@[simp] theorem spatialTrace_weightedLogSpotTerminalDataCLE_symm_apply
    (d : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) :
    ((weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).symm d).spatialTrace
      ⟨t₁, right_mem_Icc.2 ht.le⟩ = d.2 := by
  have h := (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).apply_symm_apply d
  rw [weightedLogSpotTerminalDataCLE_apply] at h; exact congrArg Prod.snd h

@[simp] theorem weightedLogSpotTerminalDataCLE_symm_apply_slabMk_right
    (d : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) (x : ℝ) :
    (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).symm d
      (slabMk x ⟨t₁, right_mem_Icc.2 ht.le⟩) = d.2 x := by
  rw [← spatialTrace_apply, spatialTrace_weightedLogSpotTerminalDataCLE_symm_apply]

end TerminalDataEval

private theorem pullback_unit_coeff_bounds {hα₁ : α < 1} {K : ℝ≥0}
    {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ} (haK : ‖a‖ ≤ K) (hrK : ‖r‖ ≤ K) :
    ‖pullbackUnitSlabCLE t₀ t₁ a‖ ≤ (6 * K : ℝ≥0) ∧
      ‖pullbackUnitSlabCLE t₀ t₁ (weightedFirstScalar hα₁.le a r)‖ ≤ (6 * K : ℝ≥0) ∧
      ‖pullbackUnitSlabCLE t₀ t₁ (weightedZerothScalar hα₁.le r)‖ ≤ (6 * K : ℝ≥0) := by
  push_cast
  have hK : (0 : ℝ) ≤ K := K.coe_nonneg
  exact ⟨(norm_pullbackUnitSlabCLE_apply_le t₀ t₁ a).trans (by linarith),
    (norm_pullbackUnitSlabCLE_apply_le t₀ t₁ _).trans
      ((norm_weightedFirstScalar_le hα₁.le a r).trans (by linarith)),
    (norm_pullbackUnitSlabCLE_apply_le t₀ t₁ _).trans
      ((norm_weightedZerothScalar_le hα₁.le r).trans (by linarith))⟩

/-- **Uniform Schauder bound for the weighted log-spot terminal-value problem.** For `0 < α < 1`,
an ellipticity constant `λ > 0`, a coefficient norm bound `K`, and a horizon bound `T₀`, the
inverse terminal-data operators on `ℝ × [t₀, t₁]` are bounded in operator norm uniformly over all
slabs with `t₁ - t₀ ≤ T₀` and all coefficients `a, r` with `λ ≤ a` and `‖a‖, ‖r‖ ≤ K`. -/
theorem exists_norm_weightedLogSpotTerminalDataCLE_symm_le
    (hα₀ : 0 < α) (hα₁ : α < 1) {lam : ℝ} (hlam : 0 < lam) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t₀ t₁ : ℝ} (ht : t₀ < t₁), t₁ - t₀ ≤ T₀ →
      ∀ (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) (ha : ∀ p, lam ≤ a p),
        ‖a‖ ≤ K → ‖r‖ ≤ K →
        ‖(weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r
            ⟨lam, hlam, ha⟩).symm.toContinuousLinearMap‖ ≤ C := by
  obtain ⟨C, hC, hest⟩ :=
    exists_norm_euclideanTerminalDataCLE_symm_le (ι := Unit) hα₀ hα₁ hlam (6 * K) T₀
  refine ⟨C, hC, fun {t₀ t₁} ht hT₀ a r ha haK hrK ↦ ?_⟩
  obtain ⟨ha', hb', hc'⟩ := pullback_unit_coeff_bounds (hα₁ := hα₁) haK hrK
  let e := (euclideanTerminalDataCLE hα₀ hα₁ ht (fun _ _ ↦ pullbackUnitSlabCLE t₀ t₁ a)
    (fun _ ↦ pullbackUnitSlabCLE t₀ t₁ (weightedFirstScalar hα₁.le a r))
    (pullbackUnitSlabCLE t₀ t₁ (weightedZerothScalar hα₁.le r))
    ⟨lam, hlam, ellipticity_pullbackUnitSlab ha⟩).symm.toContinuousLinearMap
  have hcomp :
      (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ⟨lam, hlam, ha⟩).symm.toContinuousLinearMap =
      (toUnitC2CLE ht).symm.toContinuousLinearMap ∘L e ∘L
        (dataUnitBridgeCLE t₀ t₁).toContinuousLinearMap := rfl
  rw [hcomp]
  exact (norm_comp_unit_bridges_le ht e).trans (hest ht hT₀ _ _ _
    (ellipticity_pullbackUnitSlab ha) (fun _ _ ↦ ha') (fun _ ↦ hb') hc')

private theorem pullback_unit_coeff_sub_bound {hα₁ : α < 1}
    (a a' r r' : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) :
    (∑ _ : Unit, ∑ _ : Unit, ‖pullbackUnitSlabCLE t₀ t₁ a - pullbackUnitSlabCLE t₀ t₁ a'‖) +
        (∑ _ : Unit, ‖pullbackUnitSlabCLE t₀ t₁ (weightedFirstScalar hα₁.le a r) -
            pullbackUnitSlabCLE t₀ t₁ (weightedFirstScalar hα₁.le a' r')‖) +
        ‖pullbackUnitSlabCLE t₀ t₁ (weightedZerothScalar hα₁.le r) -
            pullbackUnitSlabCLE t₀ t₁ (weightedZerothScalar hα₁.le r')‖ ≤
      6 * (‖a - a'‖ + ‖r - r'‖) := by
  simp only [Fintype.sum_unique, ← map_sub]
  have hf : weightedFirstScalar hα₁.le a r - weightedFirstScalar hα₁.le a' r' =
      weightedFirstScalar hα₁.le (a - a') (r - r') := by ext; simp [weightedFirstScalar]; ring
  have hz : weightedZerothScalar hα₁.le r - weightedZerothScalar hα₁.le r' =
      weightedZerothScalar hα₁.le (r - r') := by ext; simp [weightedZerothScalar]; ring
  rw [hf, hz]
  linarith [norm_pullbackUnitSlabCLE_apply_le t₀ t₁ (a - a'),
    (norm_pullbackUnitSlabCLE_apply_le t₀ t₁ _).trans
      (norm_weightedFirstScalar_le hα₁.le (a - a') (r - r')),
    (norm_pullbackUnitSlabCLE_apply_le t₀ t₁ _).trans
      (norm_weightedZerothScalar_le hα₁.le (r - r')),
    norm_nonneg (a - a'), norm_nonneg (r - r')]

/-- **Lipschitz dependence of the weighted terminal-data inverse on `(a, r)`.** Under the uniform
ellipticity, norm, and horizon bounds of `exists_norm_weightedLogSpotTerminalDataCLE_symm_le`, the
solution operators for `(a, r)` and `(a', r')` differ in operator norm by at most
`C (‖a - a'‖ + ‖r - r'‖)`. -/
theorem exists_norm_weightedLogSpotTerminalDataCLE_symm_sub_le
    (hα₀ : 0 < α) (hα₁ : α < 1) {lam : ℝ} (hlam : 0 < lam) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t₀ t₁ : ℝ} (ht : t₀ < t₁), t₁ - t₀ ≤ T₀ →
      ∀ (a a' r r' : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)
        (ha : ∀ p, lam ≤ a p) (ha' : ∀ p, lam ≤ a' p),
        ‖a‖ ≤ K → ‖r‖ ≤ K → ‖a'‖ ≤ K → ‖r'‖ ≤ K →
        ‖(weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r
            ⟨lam, hlam, ha⟩).symm.toContinuousLinearMap -
          (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a' r'
            ⟨lam, hlam, ha'⟩).symm.toContinuousLinearMap‖ ≤
          C * (‖a - a'‖ + ‖r - r'‖) := by
  obtain ⟨C, hC, hest⟩ :=
    exists_norm_euclideanTerminalDataCLE_symm_sub_le (ι := Unit) hα₀ hα₁ hlam (6 * K) T₀
  refine ⟨6 * C, by positivity, fun {t₀ t₁} ht hT₀ a a' r r' ha ha' haK hrK haK' hrK' ↦ ?_⟩
  obtain ⟨ha₁, hb₁, hc₁⟩ := pullback_unit_coeff_bounds (hα₁ := hα₁) haK hrK
  obtain ⟨ha₂, hb₂, hc₂⟩ := pullback_unit_coeff_bounds (hα₁ := hα₁) haK' hrK'
  have h0 := hest ht hT₀ _ _ _ _ _ _ (ellipticity_pullbackUnitSlab ha)
    (ellipticity_pullbackUnitSlab ha') (fun _ _ ↦ ha₁) (fun _ ↦ hb₁) hc₁
    (fun _ _ ↦ ha₂) (fun _ ↦ hb₂) hc₂
  set e := (euclideanTerminalDataCLE hα₀ hα₁ ht (fun _ _ ↦ pullbackUnitSlabCLE t₀ t₁ a)
    (fun _ ↦ pullbackUnitSlabCLE t₀ t₁ (weightedFirstScalar hα₁.le a r))
    (pullbackUnitSlabCLE t₀ t₁ (weightedZerothScalar hα₁.le r))
    ⟨lam, hlam, ellipticity_pullbackUnitSlab ha⟩).symm.toContinuousLinearMap
  set e' := (euclideanTerminalDataCLE hα₀ hα₁ ht (fun _ _ ↦ pullbackUnitSlabCLE t₀ t₁ a')
    (fun _ ↦ pullbackUnitSlabCLE t₀ t₁ (weightedFirstScalar hα₁.le a' r'))
    (pullbackUnitSlabCLE t₀ t₁ (weightedZerothScalar hα₁.le r'))
    ⟨lam, hlam, ellipticity_pullbackUnitSlab ha'⟩).symm.toContinuousLinearMap
  have hsub :
      (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ⟨lam, hlam, ha⟩).symm.toContinuousLinearMap -
        (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a' r'
          ⟨lam, hlam, ha'⟩).symm.toContinuousLinearMap =
      (toUnitC2CLE ht).symm.toContinuousLinearMap ∘L (e - e') ∘L
        (dataUnitBridgeCLE t₀ t₁).toContinuousLinearMap :=
    ContinuousLinearMap.ext fun d ↦ by
      rw [_root_.sub_apply, comp_apply, comp_apply, _root_.sub_apply, map_sub]
      exact congrArg₂ HSub.hSub rfl rfl
  rw [hsub]
  exact (norm_comp_unit_bridges_le ht _).trans <|
    (h0.trans (mul_le_mul_of_nonneg_left
      (pullback_unit_coeff_sub_bound (hα₁ := hα₁) a a' r r') hC)).trans_eq (by ring)

/-! ### The homogeneous terminal-value solution operator -/

/-- **The homogeneous terminal solution operator.** Sends a weighted log-spot terminal datum
`g ∈ C_b^{2,α}(ℝ)` to the unique `u ∈ C_b^{2+α,1+α/2}(ℝ × [t₀, t₁])` solving `P u = 0` with
`u(·, t₁) = g`, as a continuous linear map. -/
def weightedLogSpotTerminalSolutionL (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t₀ < t₁)
    (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p) :
    CkHolderSpace 2 α ℝ ℝ →L[ℝ] ParabolicC2HolderSpace α ℝ ℝ ht :=
  (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inr ℝ (HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) (CkHolderSpace 2 α ℝ ℝ)

section TerminalSolutionEval

variable {hα₀ : 0 < α} {hα₁ : α < 1} {ht : t₀ < t₁}
  {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ} {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p}

theorem weightedLogSpotTerminalSolutionL_apply (g : CkHolderSpace 2 α ℝ ℝ) :
    weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g =
      (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).symm (0, g) := by
  simp [weightedLogSpotTerminalSolutionL]

@[simp] theorem weightedLogSpotPricingOperatorL_weightedLogSpotTerminalSolutionL
    (g : CkHolderSpace 2 α ℝ ℝ) :
    weightedLogSpotPricingOperatorL hα₁.le a r
      (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g) = 0 := by
  rw [weightedLogSpotTerminalSolutionL_apply,
    weightedLogSpotPricingOperatorL_weightedLogSpotTerminalDataCLE_symm_apply]

@[simp] theorem spatialTrace_weightedLogSpotTerminalSolutionL (g : CkHolderSpace 2 α ℝ ℝ) :
    (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g).spatialTrace
      ⟨t₁, right_mem_Icc.2 ht.le⟩ = g := by
  rw [weightedLogSpotTerminalSolutionL_apply,
    spatialTrace_weightedLogSpotTerminalDataCLE_symm_apply]

@[simp] theorem weightedLogSpotTerminalSolutionL_slabMk_right (g : CkHolderSpace 2 α ℝ ℝ) (x : ℝ) :
    weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g
      (slabMk x ⟨t₁, right_mem_Icc.2 ht.le⟩) = g x := by
  rw [weightedLogSpotTerminalSolutionL_apply,
    weightedLogSpotTerminalDataCLE_symm_apply_slabMk_right]

end TerminalSolutionEval

/-- Uniform operator-norm bound on `weightedLogSpotTerminalSolutionL`. -/
theorem exists_norm_weightedLogSpotTerminalSolutionL_le
    (hα₀ : 0 < α) (hα₁ : α < 1) {lam : ℝ} (hlam : 0 < lam) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t₀ t₁ : ℝ} (ht : t₀ < t₁), t₁ - t₀ ≤ T₀ →
      ∀ (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) (ha : ∀ p, lam ≤ a p),
        ‖a‖ ≤ K → ‖r‖ ≤ K →
        ‖weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ⟨lam, hlam, ha⟩‖ ≤ C := by
  obtain ⟨C, hC, hest⟩ := exists_norm_weightedLogSpotTerminalDataCLE_symm_le hα₀ hα₁ hlam K T₀
  refine ⟨C, hC, fun ht hT₀ a r ha haK hrK ↦ opNorm_le_bound _ hC fun g ↦ ?_⟩
  rw [weightedLogSpotTerminalSolutionL_apply]
  simpa [Prod.norm_def] using
    ContinuousLinearMap.le_of_opNorm_le _ (hest ht hT₀ a r ha haK hrK) (0, g)

/-- Lipschitz dependence of `weightedLogSpotTerminalSolutionL` on `(a, r)` in operator norm. -/
theorem exists_norm_weightedLogSpotTerminalSolutionL_sub_le
    (hα₀ : 0 < α) (hα₁ : α < 1) {lam : ℝ} (hlam : 0 < lam) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t₀ t₁ : ℝ} (ht : t₀ < t₁), t₁ - t₀ ≤ T₀ →
      ∀ (a a' r r' : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)
        (ha : ∀ p, lam ≤ a p) (ha' : ∀ p, lam ≤ a' p),
        ‖a‖ ≤ K → ‖r‖ ≤ K → ‖a'‖ ≤ K → ‖r'‖ ≤ K →
        ‖weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ⟨lam, hlam, ha⟩ -
            weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a' r' ⟨lam, hlam, ha'⟩‖ ≤
          C * (‖a - a'‖ + ‖r - r'‖) := by
  obtain ⟨C, hC, hest⟩ := exists_norm_weightedLogSpotTerminalDataCLE_symm_sub_le hα₀ hα₁ hlam K T₀
  refine ⟨C, hC, fun ht hT₀ a a' r r' ha ha' haK hrK haK' hrK' ↦
    opNorm_le_bound _ (mul_nonneg hC (by positivity)) fun g ↦ ?_⟩
  have h := ContinuousLinearMap.le_of_opNorm_le _
    (hest ht hT₀ a a' r r' ha ha' haK hrK haK' hrK') (0, g)
  simpa [_root_.sub_apply, weightedLogSpotTerminalSolutionL_apply, Prod.norm_def,
    max_eq_right (norm_nonneg g)] using h

/-- **Discounted supremum bound for the terminal solution.** When `r ≥ -γ` with `0 ≤ γ` and
`|g y| ≤ M` on `ℝ`, the solution satisfies `|u p| ≤ exp (γ (t₁ - t)) M` on the whole slab. -/
theorem abs_weightedLogSpotTerminalSolutionL_le_exp_mul
    {hα₀ : 0 < α} {hα₁ : α < 1} {ht : t₀ < t₁}
    {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ} {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p}
    {γ M : ℝ} (hr : ∀ p, -γ ≤ r p) (hγ : 0 ≤ γ) {g : CkHolderSpace 2 α ℝ ℝ} (hg : ∀ y, |g y| ≤ M)
    (p : slab (E := ℝ) t₀ t₁) :
    |weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g p| ≤
      exp (γ * (t₁ - slabTime p)) * M := by
  obtain ⟨lam, hlam, hle⟩ := ha
  simpa using abs_le_exp_mul_mul_add_mul_of_abs_weightedLogSpotPricingOperatorL_le hα₁.le
    (fun q ↦ hlam.le.trans (hle q)) hr hγ (M := M) (K := 0)
    (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ⟨lam, hlam, hle⟩ g)
    (fun q ↦ by simp) (fun y ↦ by simpa using hg y) p

end TerminalDataCLE

/-! ### Financial and Feynman-Kac coefficient adapters -/

section Coefficients

section Algebra

variable {α : ℝ≥0} {X : Type*} [MetricSpace X]

/-- Half the squared volatility `(1 / 2) σ²`, built in the Banach algebra `HolderSpace α X ℝ`. -/
def halfSqVolatility (σ : HolderSpace α X ℝ) : HolderSpace α X ℝ := (1 / 2 : ℝ) • (σ * σ)

theorem halfSqVolatility_def (σ : HolderSpace α X ℝ) :
    halfSqVolatility σ = (1 / 2 : ℝ) • (σ * σ) := (rfl)

@[simp] theorem halfSqVolatility_apply (σ : HolderSpace α X ℝ) (x : X) :
    halfSqVolatility σ x = σ x ^ 2 / 2 := by simp [halfSqVolatility_def, sq]; ring

@[simp] theorem halfSqVolatility_zero : halfSqVolatility (0 : HolderSpace α X ℝ) = 0 := by
  simp [halfSqVolatility_def]

@[simp] theorem halfSqVolatility_neg (σ : HolderSpace α X ℝ) :
    halfSqVolatility (-σ) = halfSqVolatility σ := by ext x; simp

theorem norm_halfSqVolatility_le (σ : HolderSpace α X ℝ) :
    ‖halfSqVolatility σ‖ ≤ ‖σ‖ ^ 2 / 2 := by
  rw [halfSqVolatility_def, norm_smul,
    _root_.Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2), sq]
  linarith [norm_mul_le σ σ]

theorem norm_halfSqVolatility_sub_le (σ σ' : HolderSpace α X ℝ) :
    ‖halfSqVolatility σ - halfSqVolatility σ'‖ ≤ (‖σ‖ + ‖σ'‖) / 2 * ‖σ - σ'‖ := by
  rw [show halfSqVolatility σ - halfSqVolatility σ' = (1 / 2 : ℝ) • ((σ + σ') * (σ - σ')) by
    ext x; simp [halfSqVolatility_def]; ring, norm_smul,
    _root_.Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2)]
  linarith [(norm_mul_le (σ + σ') (σ - σ')).trans
    (mul_le_mul_of_nonneg_right (norm_add_le σ σ') (norm_nonneg _))]

theorem div_le_halfSqVolatility_of_le_sq {σ : HolderSpace α X ℝ} {δ : ℝ}
    (hδ : ∀ x, δ ≤ σ x ^ 2) (x : X) : δ / 2 ≤ halfSqVolatility σ x := by
  rw [halfSqVolatility_apply]; linarith [hδ x]

/-- The risk-neutral log-spot drift `r - σ² / 2` in `HolderSpace α X ℝ`. -/
def logSpotRiskNeutralDrift (σ r : HolderSpace α X ℝ) : HolderSpace α X ℝ :=
  r - halfSqVolatility σ

theorem logSpotRiskNeutralDrift_def (σ r : HolderSpace α X ℝ) :
    logSpotRiskNeutralDrift σ r = r - halfSqVolatility σ := (rfl)

@[simp] theorem logSpotRiskNeutralDrift_apply (σ r : HolderSpace α X ℝ) (x : X) :
    logSpotRiskNeutralDrift σ r x = r x - σ x ^ 2 / 2 := by simp [logSpotRiskNeutralDrift_def]

@[simp] theorem logSpotRiskNeutralDrift_zero :
    logSpotRiskNeutralDrift (0 : HolderSpace α X ℝ) 0 = 0 := by simp [logSpotRiskNeutralDrift_def]

theorem norm_logSpotRiskNeutralDrift_le (σ r : HolderSpace α X ℝ) :
    ‖logSpotRiskNeutralDrift σ r‖ ≤ ‖r‖ + ‖σ‖ ^ 2 / 2 :=
  (norm_sub_le _ _).trans (add_le_add le_rfl (norm_halfSqVolatility_le σ))

theorem norm_logSpotRiskNeutralDrift_sub_le (σ σ' r r' : HolderSpace α X ℝ) :
    ‖logSpotRiskNeutralDrift σ r - logSpotRiskNeutralDrift σ' r'‖ ≤
      ‖r - r'‖ + (‖σ‖ + ‖σ'‖) / 2 * ‖σ - σ'‖ := by
  rw [show logSpotRiskNeutralDrift σ r - logSpotRiskNeutralDrift σ' r' =
      (r - r') - (halfSqVolatility σ - halfSqVolatility σ') by
    rw [logSpotRiskNeutralDrift_def, logSpotRiskNeutralDrift_def]; abel]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_halfSqVolatility_sub_le σ σ'))

@[simp] theorem logSpotRiskNeutralDrift_add_halfSqVolatility (σ r : HolderSpace α X ℝ) :
    logSpotRiskNeutralDrift σ r + halfSqVolatility σ = r :=
  sub_add_cancel r (halfSqVolatility σ)

end Algebra

section SlabFields

variable {α : ℝ≥0} {t₀ t₁ : ℝ}

/-- Lift a local volatility `σ : ℝ → ℝ → ℝ` in log-spot coordinates `(y, t) ↦ σ(e^y, t)` to a
bounded parabolic `α`-Hölder field on `ℝ × [t₀, t₁]`. -/
def logSpotVolatilityHolder (hα₀ : 0 < α) (hα₁ : α ≤ 1) {M L Hσ : ℝ≥0} {σ : ℝ → ℝ → ℝ}
    (hM : ∀ y, ∀ t ∈ Icc t₀ t₁, |σ (exp y) t| ≤ M)
    (hL : ∀ t ∈ Icc t₀ t₁, LipschitzWith L (fun y ↦ σ (exp y) t))
    (hH : ∀ y, HolderOnWith Hσ (α / 2) (fun t ↦ σ (exp y) t) (Icc t₀ t₁)) :
    HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ :=
  HolderSpace.ofLipschitzSpaceHolderTime hα₀ hα₁ (f := fun y t ↦ σ (exp y) t)
    (fun y t ht ↦ by simpa only [_root_.Real.norm_eq_abs] using hM y t ht) hL hH

@[simp] theorem logSpotVolatilityHolder_apply (hα₀ : 0 < α) (hα₁ : α ≤ 1) {M L Hσ : ℝ≥0}
    {σ : ℝ → ℝ → ℝ} (hM : ∀ y, ∀ t ∈ Icc t₀ t₁, |σ (exp y) t| ≤ M)
    (hL : ∀ t ∈ Icc t₀ t₁, LipschitzWith L (fun y ↦ σ (exp y) t))
    (hH : ∀ y, HolderOnWith Hσ (α / 2) (fun t ↦ σ (exp y) t) (Icc t₀ t₁))
    (p : slab (E := ℝ) t₀ t₁) :
    logSpotVolatilityHolder hα₀ hα₁ hM hL hH p =
      σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p) := by
  simp [logSpotVolatilityHolder]

theorem norm_logSpotVolatilityHolder_le (hα₀ : 0 < α) (hα₁ : α ≤ 1) {M L Hσ : ℝ≥0}
    {σ : ℝ → ℝ → ℝ} (hM : ∀ y, ∀ t ∈ Icc t₀ t₁, |σ (exp y) t| ≤ M)
    (hL : ∀ t ∈ Icc t₀ t₁, LipschitzWith L (fun y ↦ σ (exp y) t))
    (hH : ∀ y, HolderOnWith Hσ (α / 2) (fun t ↦ σ (exp y) t) (Icc t₀ t₁)) :
    ‖logSpotVolatilityHolder hα₀ hα₁ hM hL hH‖ ≤ 3 * (M : ℝ) + L + Hσ :=
  HolderSpace.norm_ofLipschitzSpaceHolderTime_le hα₀ hα₁ _ hL hH

/-- On any time slice `t ∈ [t₀, t₁]` where `x ↦ σ (slabMk x t)` is bounded by `M` and
`L`-Lipschitz and `r` takes a constant value `r₀`, the spatial slice
`x ↦ logSpotRiskNeutralDrift σ r (slabMk x t)` is `(M * L)`-Lipschitz. -/
theorem lipschitzWith_logSpotRiskNeutralDrift_slabMk {E : Type*} [MetricSpace E]
    {σ r : HolderSpace α (slab (E := E) t₀ t₁) ℝ} {M L : ℝ≥0} {r₀ : ℝ} {t : Icc t₀ t₁}
    (hM : ∀ x, |σ (slabMk x t)| ≤ M) (hL : LipschitzWith L (fun x ↦ σ (slabMk x t)))
    (hr : ∀ x, r (slabMk x t) = r₀) :
    LipschitzWith (M * L) (fun x ↦ logSpotRiskNeutralDrift σ r (slabMk x t)) := by
  simpa only [logSpotRiskNeutralDrift_apply, hr] using lipschitzWith_const_sub_sq_div_two r₀ hM hL

end SlabFields

end Coefficients

/-! ### Classical spot-coordinate solutions and uniqueness -/

section SpotSolutions

variable {α : ℝ≥0} {t₀ t₁ : ℝ} {ht : t₀ < t₁}

/-- **The classical spot-coordinate terminal price.** Reconstructs `C(s, t) = (1 + s) u(log s, t)`
from the weighted log-spot solution `u = weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g`. -/
def weightedLogSpotTerminalPrice (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t₀ < t₁)
    (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p) (g : CkHolderSpace 2 α ℝ ℝ) : ℝ → ℝ → ℝ :=
  weightedLogSpotPrice (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g)

section TerminalPriceLemmas

variable {hα₀ : 0 < α} {hα₁ : α < 1}
  {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ} {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p}

theorem weightedLogSpotTerminalPrice_def (g : CkHolderSpace 2 α ℝ ℝ) :
    weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g =
      weightedLogSpotPrice (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g) := (rfl)

@[simp] theorem weightedLogSpotTerminalPrice_zero :
    weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha 0 = 0 := by
  rw [weightedLogSpotTerminalPrice_def, map_zero, weightedLogSpotPrice_zero]

@[simp] theorem weightedLogSpotTerminalPrice_add (g₁ g₂ : CkHolderSpace 2 α ℝ ℝ) :
    weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha (g₁ + g₂) =
      weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g₁ +
        weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g₂ := by
  simp only [weightedLogSpotTerminalPrice_def, map_add, weightedLogSpotPrice_add]

@[simp] theorem weightedLogSpotTerminalPrice_sub (g₁ g₂ : CkHolderSpace 2 α ℝ ℝ) :
    weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha (g₁ - g₂) =
      weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g₁ -
        weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g₂ := by
  simp only [weightedLogSpotTerminalPrice_def, map_sub, weightedLogSpotPrice_sub]

@[simp] theorem weightedLogSpotTerminalPrice_neg (g : CkHolderSpace 2 α ℝ ℝ) :
    weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha (-g) =
      -weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g := by
  simp only [weightedLogSpotTerminalPrice_def, map_neg, weightedLogSpotPrice_neg]

@[simp] theorem weightedLogSpotTerminalPrice_smul (c : ℝ) (g : CkHolderSpace 2 α ℝ ℝ) :
    weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha (c • g) =
      c • weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g := by
  simp only [weightedLogSpotTerminalPrice_def, map_smul, weightedLogSpotPrice_smul]

@[simp] theorem weightedLogSpotTerminalPrice_of_mem (g : CkHolderSpace 2 α ℝ ℝ)
    (s : ℝ) (t : Icc t₀ t₁) :
    weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g s t =
      (1 + s) * weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g (slabMk (log s) t) := by
  rw [weightedLogSpotTerminalPrice_def, weightedLogSpotPrice_of_mem]

@[simp] theorem weightedLogSpotTerminalPrice_exp_div (g : CkHolderSpace 2 α ℝ ℝ) (y t : ℝ) :
    weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g (exp y) t / (1 + exp y) =
      timeExtension ht.le (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g) y t := by
  rw [weightedLogSpotTerminalPrice_def, weightedLogSpotPrice_exp_div]

theorem weightedLogSpotTerminalPrice_exp_div_of_mem (g : CkHolderSpace 2 α ℝ ℝ)
    (y : ℝ) (t : Icc t₀ t₁) :
    weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g (exp y) t / (1 + exp y) =
      weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g (slabMk y t) := by
  rw [weightedLogSpotTerminalPrice_exp_div, timeExtension_of_mem]

theorem weightedLogSpotTerminalPrice_terminal {g : CkHolderSpace 2 α ℝ ℝ} {h : ℝ → ℝ}
    (hg : ∀ y, g y = h (exp y) / (1 + exp y)) {s : ℝ} (hs : 0 < s) :
    weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g s t₁ = h s :=
  weightedLogSpotPrice_terminal _
    (fun y ↦ by rw [weightedLogSpotTerminalSolutionL_slabMk_right, hg]) hs

/-- `weightedLogSpotTerminalPrice` solves the spot pricing PDE on `(0, ∞) × [t₀, t₁]` with
time derivative within `[t₀, t₁]`. -/
theorem pde_weightedLogSpotTerminalPrice (g : CkHolderSpace 2 α ℝ ℝ) {s : ℝ} (hs : 0 < s)
    (t : Icc t₀ t₁) {σ₀ r₀ : ℝ} (ha₀ : a (slabMk (log s) t) = σ₀ ^ 2 / 2)
    (hr₀ : r (slabMk (log s) t) = r₀) :
    derivWithin (weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g s) (Icc t₀ t₁) t +
        σ₀ ^ 2 * s ^ 2 / 2 *
          deriv (deriv fun x ↦ weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g x t) s +
        r₀ * (s * deriv (fun x ↦ weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g x t) s -
          weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g s t) = 0 := by
  rw [weightedLogSpotTerminalPrice_def,
    pde_weightedLogSpotPrice_eq_mul_weightedLogSpotPricingOperatorL hα₁.le _ hs t ha₀ hr₀,
    weightedLogSpotPricingOperatorL_weightedLogSpotTerminalSolutionL, HolderSpace.zero_apply,
    mul_zero]

/-- `weightedLogSpotTerminalPrice` solves the spot pricing PDE before maturity (`t ∈ [t₀, t₁)`)
with time derivative within `[t₀, ∞)`. -/
theorem pde_weightedLogSpotTerminalPrice_Ici (g : CkHolderSpace 2 α ℝ ℝ) {s t : ℝ} (hs : 0 < s)
    (ht' : t ∈ Ico t₀ t₁) {σ₀ r₀ : ℝ}
    (ha₀ : a (slabMk (log s) ⟨t, Ico_subset_Icc_self ht'⟩) = σ₀ ^ 2 / 2)
    (hr₀ : r (slabMk (log s) ⟨t, Ico_subset_Icc_self ht'⟩) = r₀) :
    derivWithin (weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g s) (Ici t₀) t +
        σ₀ ^ 2 * s ^ 2 / 2 *
          deriv (deriv fun x ↦ weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g x t) s +
        r₀ * (s * deriv (fun x ↦ weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g x t) s -
          weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g s t) = 0 := by
  rw [weightedLogSpotTerminalPrice_def,
    pde_weightedLogSpotPrice_Ici_eq_mul_weightedLogSpotPricingOperatorL hα₁.le _ hs ht' ha₀ hr₀,
    weightedLogSpotPricingOperatorL_weightedLogSpotTerminalSolutionL, HolderSpace.zero_apply,
    mul_zero]

/-- `weightedLogSpotTerminalPrice` solves the spot pricing PDE on the open horizon
`t ∈ (t₀, t₁)` with ordinary time derivative. -/
theorem pde_weightedLogSpotTerminalPrice_Ioo (g : CkHolderSpace 2 α ℝ ℝ) {s t : ℝ} (hs : 0 < s)
    (ht' : t ∈ Ioo t₀ t₁) {σ₀ r₀ : ℝ}
    (ha₀ : a (slabMk (log s) ⟨t, Ioo_subset_Icc_self ht'⟩) = σ₀ ^ 2 / 2)
    (hr₀ : r (slabMk (log s) ⟨t, Ioo_subset_Icc_self ht'⟩) = r₀) :
    deriv (weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g s) t +
        σ₀ ^ 2 * s ^ 2 / 2 *
          deriv (deriv fun x ↦ weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g x t) s +
        r₀ * (s * deriv (fun x ↦ weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g x t) s -
          weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g s t) = 0 := by
  rw [weightedLogSpotTerminalPrice_def,
    pde_weightedLogSpotPrice_Ioo_eq_mul_weightedLogSpotPricingOperatorL hα₁.le _ hs ht' ha₀ hr₀,
    weightedLogSpotPricingOperatorL_weightedLogSpotTerminalSolutionL, HolderSpace.zero_apply,
    mul_zero]

/-- Discounted linear-growth bound on `weightedLogSpotTerminalPrice` when `r ≥ -γ` and
`|g y| ≤ M`. -/
theorem abs_weightedLogSpotTerminalPrice_le_exp_mul_mul {γ M : ℝ} (hr : ∀ p, -γ ≤ r p)
    (hγ : 0 ≤ γ) {g : CkHolderSpace 2 α ℝ ℝ} (hg : ∀ y, |g y| ≤ M) {s : ℝ} (hs : 0 ≤ s)
    (t : Icc t₀ t₁) :
    |weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g s t| ≤
      exp (γ * (t₁ - t)) * M * (1 + s) := by
  rw [weightedLogSpotTerminalPrice_def, weightedLogSpotPrice_of_mem, abs_mul,
    abs_of_pos (by positivity : 0 < 1 + s), mul_comm]
  exact mul_le_mul_of_nonneg_right
    (by simpa using abs_weightedLogSpotTerminalSolutionL_le_exp_mul hr hγ hg (slabMk (log s) t))
    (by positivity)

/-- Combined linear-growth bound on the price and dollar delta of `weightedLogSpotTerminalPrice`,
for all `s ≥ 0` and all `t : ℝ`. -/
theorem abs_weightedLogSpotTerminalPrice_add_abs_mul_deriv_le (g : CkHolderSpace 2 α ℝ ℝ)
    {s : ℝ} (hs : 0 ≤ s) (t : ℝ) :
    |weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g s t| +
        |s * deriv (fun x ↦ weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g x t) s| ≤
      2 * ‖weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g‖ * (1 + s) :=
  abs_weightedLogSpotPrice_add_abs_mul_deriv_le _ hs t

end TerminalPriceLemmas

/-- **Existence of classical linear-growth prices under log-spot coefficient regularity.** Let
`0 < α < 1`, `t₀ < t₁`, `0 < δ`, and let the local volatility `σ(s, t)` satisfy
`δ ≤ σ(s, t)² ≤ Λ` for `s > 0`, `t ∈ [t₀, t₁]`, with `y ↦ σ(e^y, t)` uniformly `L`-Lipschitz and
`t ↦ σ(e^y, t)` uniformly `(α / 2)`-Hölder, and let `r` be `(α / 2)`-Hölder on `[t₀, t₁]`. For
every terminal payoff `h` whose weighted log-spot trace `y ↦ h(e^y) / (1 + e^y)` is represented by
`g ∈ C_b^{2,α}(ℝ)`, there exists `u ∈ C_b^{2+α,1+α/2}(ℝ × [t₀, t₁])` with terminal trace `g` whose
reconstructed price `C = weightedLogSpotPrice u` takes terminal value `h` on `(0, ∞)` and solves
the classical spot pricing PDE in all three time-derivative conventions (within `[t₀, t₁]`, within
`[t₀, ∞)` before maturity, and ordinary on `(t₀, t₁)`). -/
theorem exists_weightedLogSpotPrice_terminal_and_pde
    (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t₀ < t₁) {δ Λ : ℝ} (hδ : 0 < δ)
    {L Hσ Hr : ℝ≥0} {σ : ℝ → ℝ → ℝ} {r h : ℝ → ℝ} {g : CkHolderSpace 2 α ℝ ℝ}
    (hσ_bounds : ∀ s > 0, ∀ t ∈ Icc t₀ t₁, δ ≤ σ s t ^ 2 ∧ σ s t ^ 2 ≤ Λ)
    (hσ_lip : ∀ t ∈ Icc t₀ t₁, LipschitzWith L (fun y ↦ σ (exp y) t))
    (hσ_hold : ∀ y, HolderOnWith Hσ (α / 2) (fun t ↦ σ (exp y) t) (Icc t₀ t₁))
    (hr_hold : HolderOnWith Hr (α / 2) r (Icc t₀ t₁))
    (hg : ∀ y, g y = h (exp y) / (1 + exp y)) :
    ∃ u : ParabolicC2HolderSpace α ℝ ℝ ht,
      (∀ y, u (slabMk y ⟨t₁, right_mem_Icc.2 ht.le⟩) = g y) ∧
      (∀ s > 0, weightedLogSpotPrice u s t₁ = h s) ∧
      (∀ s > 0, ∀ t ∈ Icc t₀ t₁,
        derivWithin (weightedLogSpotPrice u s) (Icc t₀ t₁) t +
          σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ weightedLogSpotPrice u x t) s +
          r t * (s * deriv (fun x ↦ weightedLogSpotPrice u x t) s -
            weightedLogSpotPrice u s t) = 0) ∧
      (∀ s > 0, ∀ t ∈ Ico t₀ t₁,
        derivWithin (weightedLogSpotPrice u s) (Ici t₀) t +
          σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ weightedLogSpotPrice u x t) s +
          r t * (s * deriv (fun x ↦ weightedLogSpotPrice u x t) s -
            weightedLogSpotPrice u s t) = 0) ∧
      (∀ s > 0, ∀ t ∈ Ioo t₀ t₁,
        deriv (weightedLogSpotPrice u s) t +
          σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ weightedLogSpotPrice u x t) s +
          r t * (s * deriv (fun x ↦ weightedLogSpotPrice u x t) s -
            weightedLogSpotPrice u s t) = 0) := by
  let M : ℝ≥0 := ⟨√Λ, _root_.Real.sqrt_nonneg Λ⟩
  have hM (y t : ℝ) (ht' : t ∈ Icc t₀ t₁) : |σ (exp y) t| ≤ M :=
    _root_.Real.abs_le_sqrt (hσ_bounds (exp y) (exp_pos y) t ht').2
  let σH := logSpotVolatilityHolder hα₀ hα₁.le hM hσ_lip hσ_hold
  let a := halfSqVolatility σH
  let rH := HolderSpace.ofHolderTime (E := ℝ) hα₀ hr_hold
  have ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p :=
    ⟨δ / 2, half_pos hδ, div_le_halfSqVolatility_of_le_sq fun p ↦ by
      simpa [σH] using (hσ_bounds _ (exp_pos _) _ (slabTime p).2).1⟩
  exact ⟨weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a rH ha g,
    weightedLogSpotTerminalSolutionL_slabMk_right g,
    fun s hs ↦ weightedLogSpotTerminalPrice_terminal hg hs,
    fun s hs t ht' ↦ pde_weightedLogSpotTerminalPrice g hs ⟨t, ht'⟩
      (by simp [a, σH, exp_log hs]) (by simp [rH]),
    fun s hs t ht' ↦ pde_weightedLogSpotTerminalPrice_Ici g hs ht'
      (by simp [a, σH, exp_log hs]) (by simp [rH]),
    fun s hs t ht' ↦ pde_weightedLogSpotTerminalPrice_Ioo g hs ht'
      (by simp [a, σH, exp_log hs]) (by simp [rH])⟩

/-- **Uniqueness of the reconstructed spot price in the classical linear-growth class.** On
`[t₀, t₁]` with `t₀ < t₁`, for bounded `σ² ≤ Λ` and `|r| ≤ R` on `(t₀, t₁)`, any classical function
`C` of linear growth `|C(s, t)| ≤ A (1 + s)` having the same pricing operator on `(0, ∞) × (t₀, t₁)`
and the same terminal value at `t₁` on `(0, ∞)` as `weightedLogSpotPrice u` agrees with
`weightedLogSpotPrice u` everywhere on `(0, ∞) × [t₀, t₁]`. -/
theorem eq_weightedLogSpotPrice_of_pde_of_terminal {Λ R A : ℝ} {σ : ℝ → ℝ → ℝ} {r : ℝ → ℝ}
    (u : ParabolicC2HolderSpace α ℝ ℝ ht) {C : ℝ → ℝ → ℝ}
    (hσ : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → σ s t ^ 2 ≤ Λ)
    (hr : ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → |r t| ≤ R)
    (hC_cont : ContinuousOn (Function.uncurry C) (Ioi 0 ×ˢ Icc t₀ t₁))
    (hC_growth : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ → |C s t| ≤ A * (1 + s))
    (hC_cd : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → ContDiffAt ℝ 2 (fun x ↦ C x t) s)
    (hC_diff : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → DifferentiableAt ℝ (fun τ ↦ C s τ) t)
    (hpde : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ →
      deriv (fun τ ↦ C s τ) t + σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ C x t) s +
          r t * (s * deriv (fun x ↦ C x t) s - C s t) =
        deriv (weightedLogSpotPrice u s) t +
          σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ weightedLogSpotPrice u x t) s +
          r t * (s * deriv (fun x ↦ weightedLogSpotPrice u x t) s -
            weightedLogSpotPrice u s t))
    (hterm : ∀ ⦃s⦄, 0 < s → C s t₁ = weightedLogSpotPrice u s t₁) :
    ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ → C s t = weightedLogSpotPrice u s t :=
  eq_of_pde_eq_of_terminal_eq (A := |A| + ‖u‖) hσ hr hC_cont
    ((continuousOn_weightedLogSpotPrice u).mono (prod_mono_right (subset_univ _)))
    (fun x hx τ hτ ↦ by
      have h₁ := (hC_growth hx hτ).trans
        (mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity))
      have h₂ := abs_weightedLogSpotPrice_le u hx.le τ
      linarith [abs_sub (C x τ) (weightedLogSpotPrice u x τ)])
    hC_cd
    (fun _ hx _ hτ ↦ (contDiffOn_weightedLogSpotPrice u
      ⟨_, Ioo_subset_Icc_self hτ⟩).contDiffAt (Ioi_mem_nhds hx))
    hC_diff
    (fun x _ _ hτ ↦ differentiableAt_weightedLogSpotPrice_time u x hτ)
    hpde hterm

end SpotSolutions

end TauCeti.Finance
