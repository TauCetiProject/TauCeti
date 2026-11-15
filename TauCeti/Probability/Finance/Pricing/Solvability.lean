/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.Pricing.Operator
public import TauCeti.Probability.Finance.WeightedLogSpot
public import TauCeti.Probability.Finance.Pricing.Integrability
import TauCeti.Analysis.Matrix.QuadraticBounds
import TauCeti.Analysis.PDE.Parabolic.Holder.CompSpatial
import TauCeti.Analysis.PDE.Parabolic.Holder.Solvability
import TauCeti.Probability.Finance.Comparison

/-!
# Solvability of the weighted log-spot and classical pricing terminal-value problems

For `0 < α < 1`, a time horizon `t₀ < t₁`, and coefficient fields `a` and `r` in the bounded
parabolic Hölder space `C_b^{α,α/2}(ℝ × [t₀, t₁])` with `a` uniformly positive (`0 < λ ≤ a`), the
weighted log-spot pricing operator

`P u = ∂ₜu + a ∂ᵧ²u + (r + a (2 sigmoid y - 1)) ∂ᵧu - r (1 - sigmoid y) u`

(`TauCeti.Finance.weightedLogSpotPricingOperatorL`) defines a Banach-space isomorphism

`u ↦ (P u, u(·, t₁))`

from `C_b^{2+α,1+α/2}(ℝ × [t₀, t₁])` onto `C_b^{α,α/2}(ℝ × [t₀, t₁]) × C_b^{2,α}(ℝ)`
(`TauCeti.Finance.weightedLogSpotTerminalDataCLE`). Its inverse is bounded uniformly over
horizons `t₁ - t₀ ≤ T₀` and coefficient bounds `‖a‖, ‖r‖ ≤ K`, and depends Lipschitz continuously
on `(a, r)` in operator norm. Specializing to zero forcing yields the continuous linear terminal
solution operator `g ↦ u` (`TauCeti.Finance.weightedLogSpotTerminalSolutionL`) together with its
discounted supremum bound when the short rate is bounded below.

The second half of the file connects this Banach-space isomorphism to the financial coefficients
and spot-coordinate PDE:

* `halfSqVolatility`, `logSpotRiskNeutralDrift`, `lipschitzWith_logSpotRiskNeutralDrift_slice`,
  `shortRateSlabHolder`, and `logSpotVolatilityHolder` assemble parabolic Hölder diffusion, drift,
  and discount fields from a local volatility `σ(s, t)` and short rate `r(t)`;
* `weightedLogSpotTerminalPrice` reconstructs the classical linear-growth spot price
  `C(s, t) = (1 + s) u(log s, t)` solving `C_t + σ² s² / 2 C_ss + r (s C_s - C) = 0` in all three
  time-derivative conventions (within `[t₀, t₁]`, within `[t₀, ∞)` before maturity, and ordinary on
  `(t₀, t₁)`), with sharp linear growth in both `C` and `s C_s`;
* `memLp_price_path_and_delta_exposure_weightedLogSpotPrice` and
  `integrable_delta_hedge_gains_weightedLogSpotPrice` supply the pathwise time-integrability of the
  delta hedge along any positive continuous stock trajectory;
* `exists_classicalPrice_of_spotCoefficients` and `eq_weightedLogSpotPrice_of_pde_of_terminal`
  combine existence in weighted log-spot spaces with uniqueness in the classical linear-growth
  class on any horizon `[t₀, t₁]`.

## Reduction to the forward Euclidean Cauchy problem

Reversing time via `τ = t₁ - t` (`ParabolicC2HolderSpace.timeReverseLIE`) and identifying `ℝ`
isometrically with `EuclideanSpace ℝ Unit` (`OrthonormalBasis.singleton Unit ℝ`) intertwines the
terminal-data map `(P u, u(·, t₁))` with the initial-data isomorphism
`ParabolicC2HolderSpace.euclideanInitialDataCLE` on `ℝ¹ × [0, t₁ - t₀]`, up to negating the forcing
component. Both bridging equivalences have operator norm at most `1` in each direction and do not
depend on `(a, r)`, so the uniform Schauder bound and Lipschitz coefficient dependence transfer
without loss.

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

open _root_.Real Set Filter Topology MeasureTheory

namespace TauCeti.Finance

open ParabolicSpaceTime ContinuousLinearMap ParabolicC2HolderSpace
open scoped NNReal ENNReal

/-! ### Isometric bridge between `(ℝ, [t₀, t₁])` and `(EuclideanSpace ℝ Unit, [0, t₁ - t₀])` -/

section Bridge

/-- The canonical linear isometric equivalence `EuclideanSpace ℝ Unit ≃ₗᵢ[ℝ] ℝ` sending the unit
basis vector `EuclideanSpace.single () 1` to `1`. -/
private def euclideanUnitLIE : EuclideanSpace ℝ Unit ≃ₗᵢ[ℝ] ℝ :=
  (OrthonormalBasis.singleton Unit ℝ).repr.symm

private theorem euclideanUnitLIE_apply (x : EuclideanSpace ℝ Unit) :
    euclideanUnitLIE x = x () := by
  rw [← OrthonormalBasis.singleton_repr (euclideanUnitLIE x) ()]
  exact congrArg (fun v : EuclideanSpace ℝ Unit ↦ v ()) (euclideanUnitLIE.symm_apply_apply x)

@[simp]
private theorem euclideanUnitLIE_single_one (u : Unit) :
    euclideanUnitLIE (EuclideanSpace.single u (1 : ℝ)) = 1 := by
  rw [euclideanUnitLIE_apply]
  cases u
  simp

private theorem norm_lie_toCLM_le_one {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃ₗᵢ[ℝ] F) :
    ‖(L.toContinuousLinearEquiv : E →L[ℝ] F)‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun x ↦ by simp

private theorem toQuadraticForm'_unit_eq {c : ℝ} (ξ : EuclideanSpace ℝ Unit) :
    (Matrix.of fun _ _ : Unit ↦ c).toQuadraticForm' ξ = c * ‖ξ‖ ^ 2 := by
  have hnorm : ‖ξ‖ = |ξ ()| := by
    rw [← euclideanUnitLIE.norm_map ξ, euclideanUnitLIE_apply, _root_.Real.norm_eq_abs]
  rw [Matrix.toQuadraticForm'_apply, hnorm, sq_abs]
  simp [Matrix.mulVec, dotProduct]
  ring

/-- The sigmoid as a bounded `α`-Hölder scalar function on `ℝ` for `α ≤ 1`. -/
private def sigmoidHolder {α : ℝ≥0} (hα : α ≤ 1) : HolderSpace α ℝ ℝ :=
  HolderSpace.ofBoundedContinuousFunction
    (BoundedContinuousFunction.ofNormedAddCommGroup sigmoid continuous_sigmoid 1 fun x ↦ by
      rw [_root_.Real.norm_eq_abs, abs_of_nonneg (sigmoid_nonneg x)]
      exact sigmoid_le_one x)
    (by simpa using memHolder_iteratedDeriv_sigmoid 0 hα)

@[simp]
private theorem sigmoidHolder_apply {α : ℝ≥0} (hα : α ≤ 1) (x : ℝ) :
    sigmoidHolder hα x = sigmoid x := by
  simp [sigmoidHolder, HolderSpace.ofBoundedContinuousFunction_apply]

/-- The scalar first-order coefficient `r + a (2 sigmoid y - 1)` of the weighted log-spot pricing
operator on `ℝ × [t₀, t₁]`. -/
private def weightedFirstScalar {α : ℝ≥0} {t₀ t₁ : ℝ} (hα : α ≤ 1)
    (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) :
    HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ :=
  r + a * ((2 : ℝ) • HolderSpace.compSlabSpaceL (sigmoidHolder hα) - HolderSpace.const 1)

/-- The scalar zeroth-order coefficient `-r (1 - sigmoid y)` of the weighted log-spot pricing
operator on `ℝ × [t₀, t₁]`. -/
private def weightedZerothScalar {α : ℝ≥0} {t₀ t₁ : ℝ} (hα : α ≤ 1)
    (r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) :
    HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ :=
  -(r * (HolderSpace.const 1 - HolderSpace.compSlabSpaceL (sigmoidHolder hα)))

@[simp]
private theorem weightedFirstScalar_apply {α : ℝ≥0} {t₀ t₁ : ℝ} (hα : α ≤ 1)
    (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) (p : slab (E := ℝ) t₀ t₁) :
    weightedFirstScalar hα a r p =
      r p + a p * (2 * sigmoid (p : ParabolicSpaceTime ℝ).space - 1) := by
  simp [weightedFirstScalar]

@[simp]
private theorem weightedZerothScalar_apply {α : ℝ≥0} {t₀ t₁ : ℝ} (hα : α ≤ 1)
    (r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) (p : slab (E := ℝ) t₀ t₁) :
    weightedZerothScalar hα r p = -(r p * (1 - sigmoid (p : ParabolicSpaceTime ℝ).space)) := by
  simp [weightedZerothScalar]

private theorem norm_weightedFirstScalar_le {α : ℝ≥0} {t₀ t₁ : ℝ} (hα : α ≤ 1)
    (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) :
    ‖weightedFirstScalar hα a r‖ ≤ ‖r‖ + ‖a‖ * (2 * ‖sigmoidHolder hα‖ + 1) := by
  have hsig : ‖HolderSpace.compSlabSpaceL (a := t₀) (b := t₁) (sigmoidHolder hα)‖ ≤
      ‖sigmoidHolder hα‖ := by
    simpa using (HolderSpace.compSlabSpaceL (a := t₀) (b := t₁)).le_of_opNorm_le
      HolderSpace.norm_compSlabSpaceL_le_one (sigmoidHolder hα)
  have hfactor :
      ‖(2 : ℝ) • HolderSpace.compSlabSpaceL (a := t₀) (b := t₁) (sigmoidHolder hα) -
          HolderSpace.const (1 : ℝ)‖ ≤ 2 * ‖sigmoidHolder hα‖ + 1 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, _root_.Real.norm_ofNat]
    exact add_le_add (mul_le_mul_of_nonneg_left hsig zero_le_two)
      ((HolderSpace.norm_const_le (1 : ℝ)).trans_eq norm_one)
  exact (norm_add_le _ _).trans (add_le_add le_rfl
    ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hfactor (norm_nonneg a))))

private theorem norm_weightedFirstScalar_sub_le {α : ℝ≥0} {t₀ t₁ : ℝ} (hα : α ≤ 1)
    (a a' r r' : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) :
    ‖weightedFirstScalar hα a r - weightedFirstScalar hα a' r'‖ ≤
      ‖r - r'‖ + ‖a - a'‖ * (2 * ‖sigmoidHolder hα‖ + 1) := by
  have heq : weightedFirstScalar hα a r - weightedFirstScalar hα a' r' =
      weightedFirstScalar hα (a - a') (r - r') := by
    ext p
    simp [weightedFirstScalar]
    ring
  rw [heq]
  exact norm_weightedFirstScalar_le hα (a - a') (r - r')

private theorem norm_weightedZerothScalar_le {α : ℝ≥0} {t₀ t₁ : ℝ} (hα : α ≤ 1)
    (r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) :
    ‖weightedZerothScalar hα r‖ ≤ ‖r‖ * (1 + ‖sigmoidHolder hα‖) := by
  have hsig : ‖HolderSpace.compSlabSpaceL (a := t₀) (b := t₁) (sigmoidHolder hα)‖ ≤
      ‖sigmoidHolder hα‖ := by
    simpa using (HolderSpace.compSlabSpaceL (a := t₀) (b := t₁)).le_of_opNorm_le
      HolderSpace.norm_compSlabSpaceL_le_one (sigmoidHolder hα)
  have hfactor :
      ‖HolderSpace.const (1 : ℝ) -
          HolderSpace.compSlabSpaceL (a := t₀) (b := t₁) (sigmoidHolder hα)‖ ≤
        1 + ‖sigmoidHolder hα‖ :=
    (norm_sub_le _ _).trans
      (add_le_add ((HolderSpace.norm_const_le (1 : ℝ)).trans_eq norm_one) hsig)
  rw [weightedZerothScalar, norm_neg]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hfactor (norm_nonneg r))

private theorem norm_weightedZerothScalar_sub_le {α : ℝ≥0} {t₀ t₁ : ℝ} (hα : α ≤ 1)
    (r r' : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) :
    ‖weightedZerothScalar hα r - weightedZerothScalar hα r'‖ ≤
      ‖r - r'‖ * (1 + ‖sigmoidHolder hα‖) := by
  have heq : weightedZerothScalar hα r - weightedZerothScalar hα r' =
      weightedZerothScalar hα (r - r') := by
    ext p
    simp [weightedZerothScalar]
    ring
  rw [heq]
  exact norm_weightedZerothScalar_le hα (r - r')

/-- The horizon `t₁ - t₀` of `t₀ < t₁` as a nonnegative real number. -/
private def slabDuration {t₀ t₁ : ℝ} (ht : t₀ < t₁) : ℝ≥0 :=
  ⟨t₁ - t₀, sub_nonneg.2 ht.le⟩

private theorem coe_slabDuration {t₀ t₁ : ℝ} (ht : t₀ < t₁) :
    (slabDuration ht : ℝ) = t₁ - t₀ :=
  rfl

private theorem slabDuration_pos {t₀ t₁ : ℝ} (ht : t₀ < t₁) :
    (0 : ℝ) < slabDuration ht :=
  (sub_self t₁).symm ▸ (coe_slabDuration ht) ▸ sub_lt_sub_left ht t₁

/-- Spatial isometric equivalence between `ℝ¹ × [a, b]` and `ℝ × [a, b]`. -/
private def slabSpaceUnitEquiv (a b : ℝ) :
    slab (E := EuclideanSpace ℝ Unit) a b ≃ᵢ slab (E := ℝ) a b where
  toFun := slabSpaceMap euclideanUnitLIE
  invFun := slabSpaceMap euclideanUnitLIE.symm
  left_inv q := by rw [← slabMk_space_slabTime q]; simp
  right_inv p := by rw [← slabMk_space_slabTime p]; simp
  isometry_toFun q₁ q₂ := by
    rw [← slabMk_space_slabTime q₁, ← slabMk_space_slabTime q₂, slabSpaceMap_slabMk,
      slabSpaceMap_slabMk, edist_slabMk, edist_slabMk, euclideanUnitLIE.isometry.edist_eq]

/-- Isometric equivalence `(x, τ) ↦ (x (), t₁ - τ)` from `ℝ¹ × [0, t₁ - t₀]` onto `ℝ × [t₀, t₁]`. -/
private def toBackwardSlabEquiv {t₀ t₁ : ℝ} (ht : t₀ < t₁) :
    slab (E := EuclideanSpace ℝ Unit) 0 (slabDuration ht) ≃ᵢ slab (E := ℝ) t₀ t₁ :=
  (slabSpaceUnitEquiv 0 (slabDuration ht)).trans
    (slabTimeReverse (a' := 0) (b' := (slabDuration ht : ℝ)) t₁
      (sub_self t₁).symm (coe_slabDuration ht))

private theorem slabTimeReverse_slabSpaceMap_eq {t₀ t₁ : ℝ} (ht : t₀ < t₁)
    (q : slab (E := EuclideanSpace ℝ Unit) 0 (slabDuration ht)) :
    slabTimeReverse (a' := 0) (b' := (slabDuration ht : ℝ)) t₁
      (sub_self t₁).symm (coe_slabDuration ht)
      (slabSpaceMap (euclideanUnitLIE.toContinuousLinearEquiv : EuclideanSpace ℝ Unit →L[ℝ] ℝ) q) =
      toBackwardSlabEquiv ht q :=
  rfl

/-- Pulling parabolic `α`-Hölder functions back along `toBackwardSlabEquiv` is a Banach isomorphism
of norm at most `1` in both directions. -/
private def pullbackSlabCLE {α : ℝ≥0} {t₀ t₁ : ℝ} (ht : t₀ < t₁) :
    HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ ≃L[ℝ]
      HolderSpace α (slab (E := EuclideanSpace ℝ Unit) 0 (slabDuration ht)) ℝ :=
  ContinuousLinearEquiv.equivOfInverse
    (HolderSpace.compLipschitzL _ (toBackwardSlabEquiv ht).isometry.lipschitzWith)
    (HolderSpace.compLipschitzL _ (toBackwardSlabEquiv ht).symm.isometry.lipschitzWith)
    (fun f ↦ by ext p; simp)
    (fun g ↦ by ext q; simp)

@[simp]
private theorem pullbackSlabCLE_apply {α : ℝ≥0} {t₀ t₁ : ℝ} (ht : t₀ < t₁)
    (f : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)
    (q : slab (E := EuclideanSpace ℝ Unit) 0 (slabDuration ht)) :
    pullbackSlabCLE ht f q = f (toBackwardSlabEquiv ht q) :=
  HolderSpace.compLipschitzL_apply _ _ _

private theorem norm_pullbackSlabCLE_le_one {α : ℝ≥0} {t₀ t₁ : ℝ} (ht : t₀ < t₁) :
    ‖(pullbackSlabCLE (α := α) ht).toContinuousLinearMap‖ ≤ 1 :=
  HolderSpace.norm_compLipschitzL_le_one (toBackwardSlabEquiv ht).isometry.lipschitzWith

private theorem norm_pullbackSlabCLE_symm_le_one {α : ℝ≥0} {t₀ t₁ : ℝ} (ht : t₀ < t₁) :
    ‖(pullbackSlabCLE (α := α) ht).symm.toContinuousLinearMap‖ ≤ 1 :=
  HolderSpace.norm_compLipschitzL_le_one (toBackwardSlabEquiv ht).symm.isometry.lipschitzWith

/-- Reversing time and identifying `ℝ` with `EuclideanSpace ℝ Unit` on `ParabolicC2HolderSpace`. -/
private def toForwardEuclideanCLE {α : ℝ≥0} {t₀ t₁ : ℝ} (ht : t₀ < t₁) :
    ParabolicC2HolderSpace α ℝ ℝ ht ≃L[ℝ]
      ParabolicC2HolderSpace α (EuclideanSpace ℝ Unit) ℝ (slabDuration_pos ht) :=
  (timeReverseLIE (α := α) (E := ℝ) (F := ℝ) (hab := ht)
    (a' := 0) (b' := (slabDuration ht : ℝ)) t₁
    (sub_self t₁).symm (coe_slabDuration ht)).toContinuousLinearEquiv.trans
    (compSpatialCLE α ℝ (slabDuration_pos ht) euclideanUnitLIE.toContinuousLinearEquiv)

private theorem norm_toForwardEuclideanCLE_le_one {α : ℝ≥0} {t₀ t₁ : ℝ} (ht : t₀ < t₁) :
    ‖(toForwardEuclideanCLE (α := α) ht).toContinuousLinearMap‖ ≤ 1 := by
  let rev := timeReverseLIE (α := α) (E := ℝ) (F := ℝ) (hab := ht)
    (a' := 0) (b' := (slabDuration ht : ℝ)) t₁ (sub_self t₁).symm (coe_slabDuration ht)
  let sp := compSpatialL α ℝ (slabDuration_pos ht)
    (euclideanUnitLIE.toContinuousLinearEquiv : EuclideanSpace ℝ Unit →L[ℝ] ℝ)
  have hcomp : (toForwardEuclideanCLE (α := α) ht).toContinuousLinearMap =
      sp ∘L rev.toContinuousLinearEquiv.toContinuousLinearMap :=
    ContinuousLinearMap.ext fun u ↦ by
      simp [toForwardEuclideanCLE, rev, sp, compSpatialCLE_apply]
  rw [hcomp]
  have h₁ : ‖sp‖ ≤ 1 := by
    simpa [sp] using norm_compSpatialL_le_of_norm_le α ℝ (slabDuration_pos ht) le_rfl
      (norm_lie_toCLM_le_one euclideanUnitLIE)
  have h₂ : ‖rev.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 :=
    norm_lie_toCLM_le_one rev
  exact (opNorm_comp_le _ _).trans ((mul_le_mul h₁ h₂ (norm_nonneg _) zero_le_one).trans_eq
    (one_mul 1))

private theorem norm_toForwardEuclideanCLE_symm_le_one {α : ℝ≥0} {t₀ t₁ : ℝ} (ht : t₀ < t₁) :
    ‖(toForwardEuclideanCLE (α := α) ht).symm.toContinuousLinearMap‖ ≤ 1 := by
  let rev := timeReverseLIE (α := α) (E := ℝ) (F := ℝ) (hab := ht)
    (a' := 0) (b' := (slabDuration ht : ℝ)) t₁ (sub_self t₁).symm (coe_slabDuration ht)
  let sp := compSpatialL α ℝ (slabDuration_pos ht)
    (euclideanUnitLIE.symm.toContinuousLinearEquiv : ℝ →L[ℝ] EuclideanSpace ℝ Unit)
  have hcomp : (toForwardEuclideanCLE (α := α) ht).symm.toContinuousLinearMap =
      rev.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L sp :=
    ContinuousLinearMap.ext fun v ↦ by
      simp [toForwardEuclideanCLE, rev, sp, compSpatialCLE_symm_apply]
  rw [hcomp]
  have h₁ : ‖rev.symm.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 :=
    norm_lie_toCLM_le_one rev.symm
  have h₂ : ‖sp‖ ≤ 1 := by
    simpa [sp] using norm_compSpatialL_le_of_norm_le α ℝ (slabDuration_pos ht) le_rfl
      (norm_lie_toCLM_le_one euclideanUnitLIE.symm)
  exact (opNorm_comp_le _ _).trans ((mul_le_mul h₁ h₂ (norm_nonneg _) zero_le_one).trans_eq
    (one_mul 1))

/-- Transporting `(forcing, terminal trace)` on `(ℝ, [t₀, t₁])` to `(-forcing, initial trace)` on
`(EuclideanSpace ℝ Unit, [0, t₁ - t₀])`. -/
private def dataBridgeCLE {α : ℝ≥0} {t₀ t₁ : ℝ} (ht : t₀ < t₁) :
    (HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) ≃L[ℝ]
      (HolderSpace α (slab (E := EuclideanSpace ℝ Unit) 0 (slabDuration ht)) ℝ ×
        CkHolderSpace 2 α (EuclideanSpace ℝ Unit) ℝ) :=
  ((pullbackSlabCLE ht).trans (ContinuousLinearEquiv.neg ℝ)).prodCongr
    (CkHolderSpace.compLinearCLE euclideanUnitLIE.toContinuousLinearEquiv)

private theorem norm_dataBridgeCLE_le_one {α : ℝ≥0} {t₀ t₁ : ℝ} (ht : t₀ < t₁) :
    ‖(dataBridgeCLE (α := α) ht).toContinuousLinearMap‖ ≤ 1 := by
  let L : EuclideanSpace ℝ Unit →L[ℝ] ℝ := euclideanUnitLIE.toContinuousLinearEquiv
  have he : ‖L‖ ≤ 1 := norm_lie_toCLM_le_one euclideanUnitLIE
  have hrpow : ‖L‖ ^ (α : ℝ) ≤ 1 :=
    _root_.Real.rpow_le_one (norm_nonneg _) he (NNReal.coe_nonneg α)
  have hck : ‖CkHolderSpace.compLinearL (k := 2) (α := α) (F := ℝ) L‖ ≤ 1 := by
    refine (CkHolderSpace.norm_compLinearL_le L).trans ?_
    rw [max_eq_left he, max_eq_left hrpow]
    norm_num
  refine opNorm_le_bound _ zero_le_one fun d ↦ ?_
  rw [one_mul, Prod.norm_def, Prod.norm_def]
  have h₁ : ‖(dataBridgeCLE ht d).1‖ ≤ ‖d.1‖ := by
    simp only [dataBridgeCLE, ContinuousLinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.neg_apply, norm_neg]
    simpa using (pullbackSlabCLE ht).toContinuousLinearMap.le_of_opNorm_le
      (norm_pullbackSlabCLE_le_one ht) d.1
  have h₂ : ‖(dataBridgeCLE ht d).2‖ ≤ ‖d.2‖ := by
    simp only [dataBridgeCLE, ContinuousLinearEquiv.prodCongr_apply,
      CkHolderSpace.compLinearCLE_apply]
    simpa using (CkHolderSpace.compLinearL L).le_of_opNorm_le hck d.2
  exact max_le (h₁.trans (le_max_left _ _)) (h₂.trans (le_max_right _ _))

private theorem euclideanParabolicOperatorL_toForwardEuclideanCLE {α : ℝ≥0} {t₀ t₁ : ℝ}
    (hα : α ≤ 1) (ht : t₀ < t₁) (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)
    (u : ParabolicC2HolderSpace α ℝ ℝ ht) :
    euclideanParabolicOperatorL hα
        (fun _ _ : Unit ↦ pullbackSlabCLE ht a)
        (fun _ : Unit ↦ pullbackSlabCLE ht (weightedFirstScalar hα a r))
        (pullbackSlabCLE ht (weightedZerothScalar hα r))
        (toForwardEuclideanCLE ht u) =
      -(pullbackSlabCLE ht (weightedLogSpotPricingOperatorL hα a r u)) := by
  let eL : EuclideanSpace ℝ Unit →L[ℝ] ℝ := euclideanUnitLIE.toContinuousLinearEquiv
  have he1 (i : Unit) : eL (EuclideanSpace.single i 1) = 1 := euclideanUnitLIE_single_one i
  let v := timeReverseLIE (α := α) (E := ℝ) (F := ℝ) (hab := ht)
    (a' := 0) (b' := (slabDuration ht : ℝ)) t₁ (sub_self t₁).symm (coe_slabDuration ht) u
  have hfw : toForwardEuclideanCLE ht u = compSpatialL α ℝ (slabDuration_pos ht) eL v := by
    simp [toForwardEuclideanCLE, compSpatialCLE_apply, eL, v]
  rw [hfw]
  ext q
  simp only [euclideanParabolicOperatorL_apply, HolderSpace.neg_apply, Fintype.sum_unique,
    pullbackSlabCLE_apply, weightedLogSpotPricingOperatorL_apply, weightedFirstScalar_apply,
    weightedZerothScalar_apply, timeDerivL_compSpatialL, spatialSecondFDerivL_compSpatialL,
    bilinearComp_apply, spatialFDerivL_compSpatialL, comp_apply, compSpatialL_apply, he1]
  dsimp only [v, eL]
  rw [timeDerivL_timeReverseLIE, spatialSecondFDerivL_timeReverseLIE,
    spatialFDerivL_timeReverseLIE, timeReverseLIE_apply, slabTimeReverse_slabSpaceMap_eq ht q]
  ring

private theorem spatialTrace_toForwardEuclideanCLE_zero {α : ℝ≥0} {t₀ t₁ : ℝ} (ht : t₀ < t₁)
    (u : ParabolicC2HolderSpace α ℝ ℝ ht) :
    (toForwardEuclideanCLE ht u).spatialTrace ⟨0, left_mem_Icc.2 (slabDuration_pos ht).le⟩ =
      CkHolderSpace.compLinearCLE euclideanUnitLIE.toContinuousLinearEquiv
        (u.spatialTrace ⟨t₁, right_mem_Icc.2 ht.le⟩) := by
  simp only [toForwardEuclideanCLE, ContinuousLinearEquiv.trans_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, compSpatialCLE_apply,
    spatialTrace_compSpatialL, CkHolderSpace.compLinearCLE_apply]
  congr 1
  exact spatialTrace_timeReverseLIE_left u

private theorem ellipticity_pullbackSlab {α : ℝ≥0} {t₀ t₁ : ℝ} (ht : t₀ < t₁)
    {a : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ} {lam : ℝ} (hlam : ∀ p, lam ≤ a p)
    (q : slab (E := EuclideanSpace ℝ Unit) 0 (slabDuration ht))
    (ξ : EuclideanSpace ℝ Unit) :
    lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun _ _ : Unit ↦ pullbackSlabCLE ht a q).toQuadraticForm' ξ := by
  rw [toQuadraticForm'_unit_eq, pullbackSlabCLE_apply]
  exact mul_le_mul_of_nonneg_right (hlam _) (sq_nonneg _)

/-- The bridged terminal-data equivalence obtained by conjugating `euclideanInitialDataCLE` by
`toForwardEuclideanCLE` and `dataBridgeCLE`. -/
private def bridgedTerminalDataCLE {α : ℝ≥0} {t₀ t₁ : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)
    (ht : t₀ < t₁) (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p) :
    ParabolicC2HolderSpace α ℝ ℝ ht ≃L[ℝ]
      HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ :=
  (toForwardEuclideanCLE ht).trans <|
    (euclideanInitialDataCLE hα₀ hα₁ (slabDuration_pos ht)
      (fun _ _ : Unit ↦ pullbackSlabCLE ht a)
      (fun _ : Unit ↦ pullbackSlabCLE ht (weightedFirstScalar hα₁.le a r))
      (pullbackSlabCLE ht (weightedZerothScalar hα₁.le r))
      (ha.elim fun lam h ↦ ⟨lam, h.1, ellipticity_pullbackSlab ht h.2⟩)).trans
      (dataBridgeCLE ht).symm

private theorem bridgedTerminalDataCLE_apply {α : ℝ≥0} {t₀ t₁ : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)
    (ht : t₀ < t₁) (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p) (u : ParabolicC2HolderSpace α ℝ ℝ ht) :
    bridgedTerminalDataCLE hα₀ hα₁ ht a r ha u =
      (weightedLogSpotPricingOperatorL hα₁.le a r u,
        u.spatialTrace ⟨t₁, right_mem_Icc.2 ht.le⟩) := by
  apply (dataBridgeCLE ht).injective
  simp only [bridgedTerminalDataCLE, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply, euclideanInitialDataCLE_apply,
    euclideanParabolicOperatorL_toForwardEuclideanCLE, spatialTrace_toForwardEuclideanCLE_zero,
    dataBridgeCLE, ContinuousLinearEquiv.prodCongr_apply,
    ContinuousLinearEquiv.neg_apply]

end Bridge

/-! ### Terminal-data Banach isomorphism and uniform Schauder bounds -/

section TerminalDataCLE

variable {α : ℝ≥0} {t₀ t₁ : ℝ}

/-- **Bijectivity of the weighted log-spot terminal-data map.** For `0 < α < 1`, `t₀ < t₁`, and
parabolic Hölder coefficients `a, r ∈ C_b^{α,α/2}(ℝ × [t₀, t₁])` with `0 < λ ≤ a`, every pair
`(f, g) ∈ C_b^{α,α/2}(ℝ × [t₀, t₁]) × C_b^{2,α}(ℝ)` is the forcing and terminal trace of a unique
`u ∈ C_b^{2+α,1+α/2}(ℝ × [t₀, t₁])`. -/
theorem bijective_weightedLogSpotPricingOperatorL_prod_spatialTraceL
    (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t₀ < t₁)
    (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)
    {lam : ℝ} (hlam : 0 < lam) (ha : ∀ p, lam ≤ a p) :
    Function.Bijective ((weightedLogSpotPricingOperatorL (ht := ht) hα₁.le a r).prod
      (spatialTraceL ⟨t₁, right_mem_Icc.2 ht.le⟩)) := by
  have heq : ⇑((weightedLogSpotPricingOperatorL (ht := ht) hα₁.le a r).prod
      (spatialTraceL ⟨t₁, right_mem_Icc.2 ht.le⟩)) =
      ⇑(bridgedTerminalDataCLE hα₀ hα₁ ht a r ⟨lam, hlam, ha⟩) :=
    funext fun u ↦ by simp [bridgedTerminalDataCLE_apply]
  rw [heq]
  exact (bridgedTerminalDataCLE hα₀ hα₁ ht a r ⟨lam, hlam, ha⟩).bijective

/-- **The terminal-data isomorphism of the weighted log-spot pricing operator.** For `0 < α < 1`,
`t₀ < t₁`, and coefficients `a, r ∈ C_b^{α,α/2}(ℝ × [t₀, t₁])` with `a` uniformly positive, the
map `u ↦ (P u, u(·, t₁))` as a Banach-space isomorphism onto
`C_b^{α,α/2}(ℝ × [t₀, t₁]) × C_b^{2,α}(ℝ)`. -/
def weightedLogSpotTerminalDataCLE (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t₀ < t₁)
    (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p) :
    ParabolicC2HolderSpace α ℝ ℝ ht ≃L[ℝ]
      HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ :=
  have hbij := ha.elim fun _ h ↦
    bijective_weightedLogSpotPricingOperatorL_prod_spatialTraceL hα₀ hα₁ ht a r h.1 h.2
  ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.2 hbij.1)
    (LinearMap.range_eq_top.2 hbij.2)

@[simp]
theorem weightedLogSpotTerminalDataCLE_apply {hα₀ : 0 < α} {hα₁ : α < 1} {ht : t₀ < t₁}
    {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p}
    (u : ParabolicC2HolderSpace α ℝ ℝ ht) :
    weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha u =
      (weightedLogSpotPricingOperatorL hα₁.le a r u,
        u.spatialTrace ⟨t₁, right_mem_Icc.2 ht.le⟩) := by
  dsimp only [weightedLogSpotTerminalDataCLE]
  rw [ContinuousLinearEquiv.coeFn_ofBijective]
  simp only [ContinuousLinearMap.prod_apply, spatialTraceL_apply]

private theorem weightedLogSpotTerminalDataCLE_eq_bridged (hα₀ : 0 < α) (hα₁ : α < 1)
    (ht : t₀ < t₁) (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p) :
    weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha =
      bridgedTerminalDataCLE hα₀ hα₁ ht a r ha :=
  ContinuousLinearEquiv.ext <| funext fun u ↦ by
    rw [weightedLogSpotTerminalDataCLE_apply, bridgedTerminalDataCLE_apply]

@[simp]
theorem weightedLogSpotPricingOperatorL_weightedLogSpotTerminalDataCLE_symm_apply
    {hα₀ : 0 < α} {hα₁ : α < 1} {ht : t₀ < t₁}
    {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p}
    (d : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) :
    weightedLogSpotPricingOperatorL hα₁.le a r
      ((weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).symm d) = d.1 := by
  have h := (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).apply_symm_apply d
  rw [weightedLogSpotTerminalDataCLE_apply] at h
  exact congrArg Prod.fst h

@[simp]
theorem spatialTrace_weightedLogSpotTerminalDataCLE_symm_apply
    {hα₀ : 0 < α} {hα₁ : α < 1} {ht : t₀ < t₁}
    {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p}
    (d : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) :
    ((weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).symm d).spatialTrace
      ⟨t₁, right_mem_Icc.2 ht.le⟩ = d.2 := by
  have h := (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).apply_symm_apply d
  rw [weightedLogSpotTerminalDataCLE_apply] at h
  exact congrArg Prod.snd h

@[simp]
theorem weightedLogSpotTerminalDataCLE_symm_apply_slabMk_right
    {hα₀ : 0 < α} {hα₁ : α < 1} {ht : t₀ < t₁}
    {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p}
    (d : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) (x : ℝ) :
    (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).symm d
      (slabMk x ⟨t₁, right_mem_Icc.2 ht.le⟩) = d.2 x := by
  rw [← spatialTrace_apply, spatialTrace_weightedLogSpotTerminalDataCLE_symm_apply]

private theorem pullback_coeff_bounds {hα₁ : α < 1} {K : ℝ≥0} (ht : t₀ < t₁)
    {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ} (haK : ‖a‖ ≤ K) (hrK : ‖r‖ ≤ K) :
    ‖pullbackSlabCLE ht a‖ ≤ (K * (2 + 2 * ‖sigmoidHolder hα₁.le‖₊) : ℝ≥0) ∧
      ‖pullbackSlabCLE ht (weightedFirstScalar hα₁.le a r)‖ ≤
        (K * (2 + 2 * ‖sigmoidHolder hα₁.le‖₊) : ℝ≥0) ∧
      ‖pullbackSlabCLE ht (weightedZerothScalar hα₁.le r)‖ ≤
        (K * (2 + 2 * ‖sigmoidHolder hα₁.le‖₊) : ℝ≥0) := by
  set S : ℝ := ‖sigmoidHolder hα₁.le‖
  have hpull (f : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) : ‖pullbackSlabCLE ht f‖ ≤ ‖f‖ := by
    simpa using (pullbackSlabCLE ht).toContinuousLinearMap.le_of_opNorm_le
      (norm_pullbackSlabCLE_le_one ht) f
  have hK : (0 : ℝ) ≤ K := K.coe_nonneg
  have hS : 0 ≤ S := norm_nonneg _
  have htarget : ((K * (2 + 2 * ‖sigmoidHolder hα₁.le‖₊) : ℝ≥0) : ℝ) = K * (2 + 2 * S) := by
    push_cast
    rfl
  rw [htarget]
  refine ⟨(hpull a).trans (haK.trans (by nlinarith)),
    (hpull _).trans ((norm_weightedFirstScalar_le hα₁.le a r).trans (by nlinarith)),
    (hpull _).trans ((norm_weightedZerothScalar_le hα₁.le r).trans (by nlinarith))⟩

private theorem norm_weightedLogSpotPricingOperatorL_sub_le (hα : α ≤ 1) (ht : t₀ < t₁)
    (a a' r r' : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) :
    ‖weightedLogSpotPricingOperatorL (ht := ht) hα a' r' -
        weightedLogSpotPricingOperatorL (ht := ht) hα a r‖ ≤
      24 * (2 + 2 * ‖sigmoidHolder hα‖) * (‖a - a'‖ + ‖r - r'‖) := by
  let E₁ := euclideanParabolicOperatorL (ht := slabDuration_pos ht) hα
    (fun _ _ : Unit ↦ pullbackSlabCLE ht a)
    (fun _ : Unit ↦ pullbackSlabCLE ht (weightedFirstScalar hα a r))
    (pullbackSlabCLE ht (weightedZerothScalar hα r))
  let E₂ := euclideanParabolicOperatorL (ht := slabDuration_pos ht) hα
    (fun _ _ : Unit ↦ pullbackSlabCLE ht a')
    (fun _ : Unit ↦ pullbackSlabCLE ht (weightedFirstScalar hα a' r'))
    (pullbackSlabCLE ht (weightedZerothScalar hα r'))
  have hident : weightedLogSpotPricingOperatorL (ht := ht) hα a' r' -
      weightedLogSpotPricingOperatorL (ht := ht) hα a r =
      (pullbackSlabCLE ht).symm.toContinuousLinearMap ∘L (E₁ - E₂) ∘L
        (toForwardEuclideanCLE ht).toContinuousLinearMap := by
    ext u p
    have h₁ := euclideanParabolicOperatorL_toForwardEuclideanCLE hα ht a r u
    have h₂ := euclideanParabolicOperatorL_toForwardEuclideanCLE hα ht a' r' u
    have hsub : E₁ (toForwardEuclideanCLE ht u) - E₂ (toForwardEuclideanCLE ht u) =
        pullbackSlabCLE ht (weightedLogSpotPricingOperatorL hα a' r' u -
          weightedLogSpotPricingOperatorL hα a r u) := by
      dsimp only [E₁, E₂]
      rw [h₁, h₂, map_sub]
      abel
    simp only [comp_apply, _root_.sub_apply, ContinuousLinearEquiv.coe_coe]
    rw [hsub, (pullbackSlabCLE ht).symm_apply_apply, HolderSpace.sub_apply]
  rw [hident]
  have hE : ‖E₁ - E₂‖ ≤ 24 * (2 + 2 * ‖sigmoidHolder hα‖) * (‖a - a'‖ + ‖r - r'‖) := by
    refine (norm_euclideanParabolicOperatorL_sub_le (ht := slabDuration_pos ht) hα
      _ _ _ _ _ _).trans ?_
    have hpull (f : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) : ‖pullbackSlabCLE ht f‖ ≤ ‖f‖ := by
      simpa using (pullbackSlabCLE ht).toContinuousLinearMap.le_of_opNorm_le
        (norm_pullbackSlabCLE_le_one ht) f
    simp only [Fintype.sum_unique, ← map_sub]
    have ha_sub := hpull (a - a')
    have hb_sub := (hpull _).trans (norm_weightedFirstScalar_sub_le hα a a' r r')
    have hc_sub := (hpull _).trans (norm_weightedZerothScalar_sub_le hα r r')
    nlinarith [norm_nonneg (a - a'), norm_nonneg (r - r'), norm_nonneg (sigmoidHolder hα)]
  refine (opNorm_comp_le _ _).trans ?_
  refine (mul_le_mul (norm_pullbackSlabCLE_symm_le_one ht)
    ((opNorm_comp_le _ _).trans
      (mul_le_mul hE (norm_toForwardEuclideanCLE_le_one ht) (norm_nonneg _) (by positivity)))
    (norm_nonneg _) zero_le_one).trans_eq (by ring)

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
  let K' : ℝ≥0 := K * (2 + 2 * ‖sigmoidHolder hα₁.le‖₊)
  obtain ⟨C, hC, hest⟩ :=
    exists_norm_euclideanInitialDataCLE_symm_le (ι := Unit) hα₀ hα₁ hlam K' T₀
  refine ⟨C, hC, fun {t₀ t₁} ht hT₀ a r ha haK hrK ↦ ?_⟩
  rw [weightedLogSpotTerminalDataCLE_eq_bridged]
  obtain ⟨ha', hb', hc'⟩ := pullback_coeff_bounds (hα₁ := hα₁) ht haK hrK
  have hTT₀ : slabDuration ht ≤ T₀ := by exact_mod_cast hT₀
  let eCLE := euclideanInitialDataCLE hα₀ hα₁ (slabDuration_pos ht)
    (fun _ _ : Unit ↦ pullbackSlabCLE ht a)
    (fun _ : Unit ↦ pullbackSlabCLE ht (weightedFirstScalar hα₁.le a r))
    (pullbackSlabCLE ht (weightedZerothScalar hα₁.le r))
    ⟨lam, hlam, ellipticity_pullbackSlab ht ha⟩
  set e := eCLE.symm.toContinuousLinearMap
  have heucl : ‖e‖ ≤ C := hest (slabDuration ht) (slabDuration_pos ht) hTT₀ _ _ _
    (ellipticity_pullbackSlab ht ha) (fun _ _ ↦ ha') (fun _ ↦ hb') hc'
  have hcomp :
      (bridgedTerminalDataCLE hα₀ hα₁ ht a r ⟨lam, hlam, ha⟩).symm.toContinuousLinearMap =
      (toForwardEuclideanCLE ht).symm.toContinuousLinearMap ∘L e ∘L
        (dataBridgeCLE ht).toContinuousLinearMap := rfl
  rw [hcomp]
  exact (opNorm_comp_le _ _).trans <|
    (mul_le_mul (norm_toForwardEuclideanCLE_symm_le_one ht)
      ((opNorm_comp_le _ _).trans
        (mul_le_mul heucl (norm_dataBridgeCLE_le_one ht) (norm_nonneg _) hC))
      (norm_nonneg _) zero_le_one).trans_eq (by ring)

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
  let B : ℝ := 24 * (2 + 2 * ‖sigmoidHolder hα₁.le‖)
  obtain ⟨C, hC, hest⟩ :=
    exists_norm_weightedLogSpotTerminalDataCLE_symm_le hα₀ hα₁ hlam K T₀
  refine ⟨B * C ^ 2, by positivity,
    fun {t₀ t₁} ht hT₀ a a' r r' ha ha' haK hrK haK' hrK' ↦ ?_⟩
  set e := weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ⟨lam, hlam, ha⟩
  set e' := weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a' r' ⟨lam, hlam, ha'⟩
  set δ := ‖a - a'‖ + ‖r - r'‖
  have hres : e.symm.toContinuousLinearMap - e'.symm.toContinuousLinearMap =
      e.symm.toContinuousLinearMap ∘L (e'.toContinuousLinearMap - e.toContinuousLinearMap) ∘L
        e'.symm.toContinuousLinearMap :=
    ContinuousLinearMap.ext fun d ↦ by simp
  have hdiff : ‖e'.toContinuousLinearMap - e.toContinuousLinearMap‖ ≤ B * δ := by
    refine opNorm_le_bound _ (by positivity) fun u ↦ ?_
    have hP := (weightedLogSpotPricingOperatorL hα₁.le a' r' -
      weightedLogSpotPricingOperatorL hα₁.le a r).le_opNorm u
    have hL := norm_weightedLogSpotPricingOperatorL_sub_le hα₁.le ht a a' r r'
    calc ‖(e'.toContinuousLinearMap - e.toContinuousLinearMap) u‖
        = ‖(weightedLogSpotPricingOperatorL hα₁.le a' r' -
            weightedLogSpotPricingOperatorL hα₁.le a r) u‖ := by
          simp [e, e', Prod.norm_def]
      _ ≤ B * δ * ‖u‖ := hP.trans (mul_le_mul_of_nonneg_right hL (norm_nonneg u))
  have h₁ := hest ht hT₀ a r ha haK hrK
  have h₂ := hest ht hT₀ a' r' ha' haK' hrK'
  rw [hres]
  calc _ ≤ ‖e.symm.toContinuousLinearMap‖ *
        (‖e'.toContinuousLinearMap - e.toContinuousLinearMap‖ *
          ‖e'.symm.toContinuousLinearMap‖) :=
        (opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ C * (B * δ * C) := by gcongr
    _ = B * C ^ 2 * δ := by ring

/-! ### The homogeneous terminal-value solution operator -/

/-- **The homogeneous terminal solution operator.** Sends a weighted log-spot terminal datum
`g ∈ C_b^{2,α}(ℝ)` to the unique `u ∈ C_b^{2+α,1+α/2}(ℝ × [t₀, t₁])` solving `P u = 0` with
`u(·, t₁) = g`, as a continuous linear map. -/
def weightedLogSpotTerminalSolutionL (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t₀ < t₁)
    (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p) :
    CkHolderSpace 2 α ℝ ℝ →L[ℝ] ParabolicC2HolderSpace α ℝ ℝ ht :=
  (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inr ℝ (HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) (CkHolderSpace 2 α ℝ ℝ)

theorem weightedLogSpotTerminalSolutionL_apply {hα₀ : 0 < α} {hα₁ : α < 1} {ht : t₀ < t₁}
    {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p} (g : CkHolderSpace 2 α ℝ ℝ) :
    weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g =
      (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).symm (0, g) := by
  simp [weightedLogSpotTerminalSolutionL]

@[simp]
theorem weightedLogSpotPricingOperatorL_weightedLogSpotTerminalSolutionL
    {hα₀ : 0 < α} {hα₁ : α < 1} {ht : t₀ < t₁}
    {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p} (g : CkHolderSpace 2 α ℝ ℝ) :
    weightedLogSpotPricingOperatorL hα₁.le a r
      (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g) = 0 := by
  rw [weightedLogSpotTerminalSolutionL_apply,
    weightedLogSpotPricingOperatorL_weightedLogSpotTerminalDataCLE_symm_apply]

@[simp]
theorem spatialTrace_weightedLogSpotTerminalSolutionL
    {hα₀ : 0 < α} {hα₁ : α < 1} {ht : t₀ < t₁}
    {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p} (g : CkHolderSpace 2 α ℝ ℝ) :
    (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g).spatialTrace
      ⟨t₁, right_mem_Icc.2 ht.le⟩ = g := by
  rw [weightedLogSpotTerminalSolutionL_apply,
    spatialTrace_weightedLogSpotTerminalDataCLE_symm_apply]

@[simp]
theorem weightedLogSpotTerminalSolutionL_slabMk_right
    {hα₀ : 0 < α} {hα₁ : α < 1} {ht : t₀ < t₁}
    {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p} (g : CkHolderSpace 2 α ℝ ℝ) (x : ℝ) :
    weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g
      (slabMk x ⟨t₁, right_mem_Icc.2 ht.le⟩) = g x := by
  rw [weightedLogSpotTerminalSolutionL_apply,
    weightedLogSpotTerminalDataCLE_symm_apply_slabMk_right]

/-- Uniform operator-norm bound on `weightedLogSpotTerminalSolutionL`. -/
theorem exists_norm_weightedLogSpotTerminalSolutionL_le
    (hα₀ : 0 < α) (hα₁ : α < 1) {lam : ℝ} (hlam : 0 < lam) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t₀ t₁ : ℝ} (ht : t₀ < t₁), t₁ - t₀ ≤ T₀ →
      ∀ (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) (ha : ∀ p, lam ≤ a p),
        ‖a‖ ≤ K → ‖r‖ ≤ K →
        ‖weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ⟨lam, hlam, ha⟩‖ ≤ C := by
  obtain ⟨C, hC, hest⟩ :=
    exists_norm_weightedLogSpotTerminalDataCLE_symm_le hα₀ hα₁ hlam K T₀
  refine ⟨C, hC, fun ht hT₀ a r ha haK hrK ↦ ?_⟩
  refine opNorm_le_bound _ hC fun g ↦ ?_
  rw [weightedLogSpotTerminalSolutionL_apply]
  have h := ContinuousLinearMap.le_of_opNorm_le _ (hest ht hT₀ a r ha haK hrK) (0, g)
  simpa [Prod.norm_def] using h

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
  obtain ⟨C, hC, hest⟩ :=
    exists_norm_weightedLogSpotTerminalDataCLE_symm_sub_le hα₀ hα₁ hlam K T₀
  refine ⟨C, hC, fun ht hT₀ a a' r r' ha ha' haK hrK haK' hrK' ↦ ?_⟩
  refine opNorm_le_bound _ (mul_nonneg hC (by positivity)) fun g ↦ ?_
  have h := ContinuousLinearMap.le_of_opNorm_le _
    (hest ht hT₀ a a' r r' ha ha' haK hrK haK' hrK') (0, g)
  rw [_root_.sub_apply, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe,
    Prod.norm_def, norm_zero, max_eq_right (norm_nonneg g)] at h
  rw [_root_.sub_apply, weightedLogSpotTerminalSolutionL_apply,
    weightedLogSpotTerminalSolutionL_apply]
  exact h

/-- **Discounted supremum bound for the terminal solution.** When `r ≥ -γ` with `0 ≤ γ` and
`|g y| ≤ M` on `ℝ`, the solution satisfies `|u p| ≤ exp (γ (t₁ - t)) M` on the whole slab. -/
theorem abs_weightedLogSpotTerminalSolutionL_le_of_rate_ge
    {hα₀ : 0 < α} {hα₁ : α < 1} {ht : t₀ < t₁}
    {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p}
    {γ M : ℝ} (hr : ∀ p, -γ ≤ r p) (hγ : 0 ≤ γ)
    {g : CkHolderSpace 2 α ℝ ℝ} (hg : ∀ y, |g y| ≤ M)
    (p : slab (E := ℝ) t₀ t₁) :
    |weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g p| ≤
      exp (γ * (t₁ - slabTime p)) * M := by
  have ha0 : ∀ q, 0 ≤ a q := by
    obtain ⟨lam, hlam, hle⟩ := ha
    exact fun q ↦ hlam.le.trans (hle q)
  have h := abs_le_exp_mul_mul_add_mul_of_abs_weightedLogSpotPricingOperatorL_le hα₁.le ha0 hr hγ
    (M := M) (K := 0) (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g)
    (fun q ↦ by
      rw [weightedLogSpotPricingOperatorL_weightedLogSpotTerminalSolutionL]
      simp)
    (fun y ↦ by
      rw [weightedLogSpotTerminalSolutionL_slabMk_right]
      exact hg y) p
  simpa using h

end TerminalDataCLE

/-! ### Financial and Feynman-Kac coefficient adapters -/

section Coefficients

section Algebra

variable {α : ℝ≥0} {X : Type*} [MetricSpace X]

/-- Half the squared volatility `(1 / 2) σ²`, built in the Banach algebra `HolderSpace α X ℝ`. -/
def halfSqVolatility (σ : HolderSpace α X ℝ) : HolderSpace α X ℝ :=
  (1 / 2 : ℝ) • (σ * σ)

@[simp]
theorem halfSqVolatility_apply (σ : HolderSpace α X ℝ) (x : X) :
    halfSqVolatility σ x = σ x ^ 2 / 2 := by
  simp [halfSqVolatility, sq]
  ring

theorem norm_halfSqVolatility_le (σ : HolderSpace α X ℝ) :
    ‖halfSqVolatility σ‖ ≤ ‖σ‖ ^ 2 / 2 := by
  rw [halfSqVolatility, norm_smul, _root_.Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2), sq]
  have h := norm_mul_le σ σ
  linarith

theorem norm_halfSqVolatility_sub_le (σ σ' : HolderSpace α X ℝ) :
    ‖halfSqVolatility σ - halfSqVolatility σ'‖ ≤ (‖σ‖ + ‖σ'‖) / 2 * ‖σ - σ'‖ := by
  have halg : halfSqVolatility σ - halfSqVolatility σ' =
      (1 / 2 : ℝ) • ((σ + σ') * (σ - σ')) := by
    ext x
    simp [halfSqVolatility]
    ring
  rw [halg, norm_smul, _root_.Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2)]
  have hmul : ‖(σ + σ') * (σ - σ')‖ ≤ (‖σ‖ + ‖σ'‖) * ‖σ - σ'‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_add_le σ σ') (norm_nonneg _))
  linarith

theorem le_halfSqVolatility_of_sq_ge {σ : HolderSpace α X ℝ} {δ : ℝ}
    (hδ : ∀ x, δ ≤ σ x ^ 2) (x : X) :
    δ / 2 ≤ halfSqVolatility σ x := by
  rw [halfSqVolatility_apply]
  linarith [hδ x]

/-- The risk-neutral log-spot drift `r - σ² / 2` in `HolderSpace α X ℝ`. -/
def logSpotRiskNeutralDrift (σ r : HolderSpace α X ℝ) : HolderSpace α X ℝ :=
  r - halfSqVolatility σ

@[simp]
theorem logSpotRiskNeutralDrift_apply (σ r : HolderSpace α X ℝ) (x : X) :
    logSpotRiskNeutralDrift σ r x = r x - σ x ^ 2 / 2 := by
  simp [logSpotRiskNeutralDrift]

theorem norm_logSpotRiskNeutralDrift_le (σ r : HolderSpace α X ℝ) :
    ‖logSpotRiskNeutralDrift σ r‖ ≤ ‖r‖ + ‖σ‖ ^ 2 / 2 :=
  (norm_sub_le _ _).trans (add_le_add le_rfl (norm_halfSqVolatility_le σ))

@[simp]
theorem logSpotRiskNeutralDrift_add_halfSqVolatility (σ r : HolderSpace α X ℝ) :
    logSpotRiskNeutralDrift σ r + halfSqVolatility σ = r :=
  sub_add_cancel r (halfSqVolatility σ)

end Algebra

/-- On any time slice where `y ↦ σ(e^y, t)` is bounded by `M` and `L`-Lipschitz, the risk-neutral
log-spot SDE drift `y ↦ r₀ - σ(e^y, t)² / 2` is `(M * L)`-Lipschitz. -/
theorem lipschitzWith_logSpotRiskNeutralDrift_slice {σ : ℝ → ℝ → ℝ} {r₀ : ℝ}
    {M L : ℝ≥0} {t : ℝ}
    (hM : ∀ y, |σ (exp y) t| ≤ M)
    (hL : LipschitzWith L (fun y ↦ σ (exp y) t)) :
    LipschitzWith (M * L) (fun y ↦ r₀ - σ (exp y) t ^ 2 / 2) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [_root_.Real.dist_eq, _root_.Real.dist_eq]
  have hring : (r₀ - σ (exp x) t ^ 2 / 2) - (r₀ - σ (exp y) t ^ 2 / 2) =
      -((σ (exp x) t + σ (exp y) t) / 2 * (σ (exp x) t - σ (exp y) t)) := by ring
  have hdist : |(r₀ - σ (exp x) t ^ 2 / 2) - (r₀ - σ (exp y) t ^ 2 / 2)| =
      |σ (exp x) t + σ (exp y) t| / 2 * |σ (exp x) t - σ (exp y) t| := by
    rw [hring, abs_neg, abs_mul, abs_div, abs_of_pos (zero_lt_two : (0 : ℝ) < 2)]
  have hsum : |σ (exp x) t + σ (exp y) t| / 2 ≤ M := by
    linarith [abs_add_le (σ (exp x) t) (σ (exp y) t), hM x, hM y]
  rw [hdist, NNReal.coe_mul, mul_assoc]
  exact mul_le_mul hsum (by simpa [_root_.Real.dist_eq] using hL.dist_le_mul x y)
    (abs_nonneg _) M.coe_nonneg

section SlabFields

variable {α : ℝ≥0} {t₀ t₁ : ℝ}

/-- An `(α / 2)`-Hölder short rate on `[t₀, t₁]` (with `0 < α`) as an element of
`HolderSpace (α / 2) (Icc t₀ t₁) ℝ`. -/
private def shortRateIccHolder (hα : 0 < α) {Hr : ℝ≥0} {r : ℝ → ℝ}
    (hHr : HolderOnWith Hr (α / 2) r (Icc t₀ t₁)) :
    HolderSpace (α / 2) (Icc t₀ t₁) ℝ :=
  let rc : C(Icc t₀ t₁, ℝ) :=
    ⟨fun t ↦ r t, (hHr.continuousOn (by positivity)).comp_continuous continuous_subtype_val
      fun t ↦ t.2⟩
  HolderSpace.ofBoundedContinuousFunction (BoundedContinuousFunction.mkOfCompact rc)
    (HolderWith.memHolder (C := Hr) fun t s ↦ by
      simpa [rc, BoundedContinuousFunction.mkOfCompact_apply, Subtype.edist_eq] using
        hHr t t.2 s s.2)

@[simp]
private theorem shortRateIccHolder_apply (hα : 0 < α) {Hr : ℝ≥0} {r : ℝ → ℝ}
    (hHr : HolderOnWith Hr (α / 2) r (Icc t₀ t₁)) (t : Icc t₀ t₁) :
    shortRateIccHolder hα hHr t = r t := by
  simp [shortRateIccHolder, HolderSpace.ofBoundedContinuousFunction_apply]

/-- Lift an `(α / 2)`-Hölder short rate `r : ℝ → ℝ` on `[t₀, t₁]` (with `0 < α`) to a spatially
constant parabolic `α`-Hölder field on `E × [t₀, t₁]`. -/
def shortRateSlabHolder {E : Type*} [MetricSpace E] (hα : 0 < α) {Hr : ℝ≥0} {r : ℝ → ℝ}
    (hHr : HolderOnWith Hr (α / 2) r (Icc t₀ t₁)) :
    HolderSpace α (slab (E := E) t₀ t₁) ℝ :=
  HolderSpace.compSlabTimeL (shortRateIccHolder hα hHr)

@[simp]
theorem shortRateSlabHolder_apply {E : Type*} [MetricSpace E] (hα : 0 < α) {Hr : ℝ≥0}
    {r : ℝ → ℝ} (hHr : HolderOnWith Hr (α / 2) r (Icc t₀ t₁)) (p : slab (E := E) t₀ t₁) :
    shortRateSlabHolder hα hHr p = r (slabTime p) := by
  simp [shortRateSlabHolder]

theorem norm_shortRateSlabHolder_le {E : Type*} [MetricSpace E] (hα : 0 < α) {R Hr : ℝ≥0}
    {r : ℝ → ℝ} (hR : ∀ t ∈ Icc t₀ t₁, |r t| ≤ R)
    (hHr : HolderOnWith Hr (α / 2) r (Icc t₀ t₁)) :
    ‖shortRateSlabHolder (E := E) hα hHr‖ ≤ (R : ℝ) + Hr := by
  have hf : ‖shortRateIccHolder hα hHr‖ ≤ (R : ℝ) + Hr :=
    HolderSpace.norm_le_of_norm_le_of_holderWith R.coe_nonneg
      (fun t ↦ by simpa [_root_.Real.norm_eq_abs] using hR t t.2)
      (fun t s ↦ by simpa [Subtype.edist_eq] using hHr t t.2 s s.2)
  have hcomp : ‖shortRateSlabHolder (E := E) hα hHr‖ ≤ ‖shortRateIccHolder hα hHr‖ := by
    simpa [shortRateSlabHolder] using (HolderSpace.compSlabTimeL (E := E)).le_of_opNorm_le
      HolderSpace.norm_compSlabTimeL_le_one (shortRateIccHolder hα hHr)
  exact hcomp.trans hf

/-- Lift a local volatility `σ : ℝ → ℝ → ℝ` in log-spot coordinates `(y, t) ↦ σ(e^y, t)` to a
bounded parabolic `α`-Hölder field on `ℝ × [t₀, t₁]`. -/
def logSpotVolatilityHolder (hα₀ : 0 < α) (hα₁ : α ≤ 1) {M L Hσ : ℝ≥0} {σ : ℝ → ℝ → ℝ}
    (hM : ∀ y, ∀ t ∈ Icc t₀ t₁, |σ (exp y) t| ≤ M)
    (hL : ∀ t ∈ Icc t₀ t₁, LipschitzWith L (fun y ↦ σ (exp y) t))
    (hH : ∀ y, HolderOnWith Hσ (α / 2) (fun t ↦ σ (exp y) t) (Icc t₀ t₁)) :
    HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ :=
  HolderSpace.ofLipschitzSpaceHolderTime hα₀ hα₁ (f := fun y t ↦ σ (exp y) t)
    (fun y t ht ↦ by simpa only [_root_.Real.norm_eq_abs] using hM y t ht) hL hH

@[simp]
theorem logSpotVolatilityHolder_apply (hα₀ : 0 < α) (hα₁ : α ≤ 1) {M L Hσ : ℝ≥0}
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

end SlabFields

end Coefficients

/-! ### Classical spot-coordinate solutions, hedge integrability, and uniqueness -/

section SpotSolutions

variable {α : ℝ≥0} {t₀ t₁ : ℝ} {ht : t₀ < t₁}

private theorem sigmoid_log_eq {s : ℝ} (hs : 0 < s) : sigmoid (log s) = s / (1 + s) := by
  rw [sigmoid_def, exp_neg, exp_log hs]
  field_simp
  ring

/-- The classical spot pricing operator applied to `weightedLogSpotPrice u` at `(s, t)` equals
`(1 + s)` times `weightedLogSpotPricingOperatorL` at `(log s, t)`. -/
theorem pde_weightedLogSpotPrice_eq_mul_weightedLogSpotPricingOperatorL
    (hα : α ≤ 1) {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    (u : ParabolicC2HolderSpace α ℝ ℝ ht) {s : ℝ} (hs : 0 < s) (t : Icc t₀ t₁)
    {σ₀ r₀ : ℝ} (ha : a (slabMk (log s) t) = σ₀ ^ 2 / 2)
    (hr : r (slabMk (log s) t) = r₀) :
    derivWithin (weightedLogSpotPrice u s) (Icc t₀ t₁) t +
        σ₀ ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ weightedLogSpotPrice u x t) s +
        r₀ * (s * deriv (fun x ↦ weightedLogSpotPrice u x t) s - weightedLogSpotPrice u s t) =
      (1 + s) * weightedLogSpotPricingOperatorL hα a r u (slabMk (log s) t) := by
  rw [pde_weightedLogSpotPrice u hs t σ₀ r₀, weightedLogSpotPricingOperatorL_apply]
  simp only [space_slabMk, ha, hr, sigmoid_log_eq hs]
  have hs1 : (1 + s) ≠ 0 := by positivity
  have hs1' : (s + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- Pre-maturity (`t ∈ [t₀, t₁)`) version of
`pde_weightedLogSpotPrice_eq_mul_weightedLogSpotPricingOperatorL`, with time derivative within
`[t₀, ∞)`. -/
theorem pde_weightedLogSpotPrice_Ici_eq_mul_weightedLogSpotPricingOperatorL
    (hα : α ≤ 1) {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    (u : ParabolicC2HolderSpace α ℝ ℝ ht) {s t : ℝ} (hs : 0 < s) (ht' : t ∈ Ico t₀ t₁)
    {σ₀ r₀ : ℝ} (ha : a (slabMk (log s) ⟨t, Ico_subset_Icc_self ht'⟩) = σ₀ ^ 2 / 2)
    (hr : r (slabMk (log s) ⟨t, Ico_subset_Icc_self ht'⟩) = r₀) :
    derivWithin (weightedLogSpotPrice u s) (Ici t₀) t +
        σ₀ ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ weightedLogSpotPrice u x t) s +
        r₀ * (s * deriv (fun x ↦ weightedLogSpotPrice u x t) s - weightedLogSpotPrice u s t) =
      (1 + s) * weightedLogSpotPricingOperatorL hα a r u
        (slabMk (log s) ⟨t, Ico_subset_Icc_self ht'⟩) := by
  rw [pde_weightedLogSpotPrice_Ici u hs ht' σ₀ r₀, weightedLogSpotPricingOperatorL_apply]
  simp only [space_slabMk, ha, hr, sigmoid_log_eq hs]
  have hs1 : (1 + s) ≠ 0 := by positivity
  have hs1' : (s + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- Open-horizon (`t ∈ (t₀, t₁)`) version of
`pde_weightedLogSpotPrice_eq_mul_weightedLogSpotPricingOperatorL`, with ordinary time
derivative. -/
theorem pde_weightedLogSpotPrice_Ioo_eq_mul_weightedLogSpotPricingOperatorL
    (hα : α ≤ 1) {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    (u : ParabolicC2HolderSpace α ℝ ℝ ht) {s t : ℝ} (hs : 0 < s) (ht' : t ∈ Ioo t₀ t₁)
    {σ₀ r₀ : ℝ} (ha : a (slabMk (log s) ⟨t, Ioo_subset_Icc_self ht'⟩) = σ₀ ^ 2 / 2)
    (hr : r (slabMk (log s) ⟨t, Ioo_subset_Icc_self ht'⟩) = r₀) :
    deriv (weightedLogSpotPrice u s) t +
        σ₀ ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ weightedLogSpotPrice u x t) s +
        r₀ * (s * deriv (fun x ↦ weightedLogSpotPrice u x t) s - weightedLogSpotPrice u s t) =
      (1 + s) * weightedLogSpotPricingOperatorL hα a r u
        (slabMk (log s) ⟨t, Ioo_subset_Icc_self ht'⟩) := by
  rw [pde_weightedLogSpotPrice_Ioo u hs ht' σ₀ r₀, weightedLogSpotPricingOperatorL_apply]
  simp only [space_slabMk, ha, hr, sigmoid_log_eq hs]
  have hs1 : (1 + s) ≠ 0 := by positivity
  have hs1' : (s + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- **The classical spot-coordinate terminal price.** Reconstructs `C(s, t) = (1 + s) u(log s, t)`
from the weighted log-spot solution `u = weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g`. -/
def weightedLogSpotTerminalPrice (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t₀ < t₁)
    (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p) (g : CkHolderSpace 2 α ℝ ℝ) : ℝ → ℝ → ℝ :=
  weightedLogSpotPrice (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g)

theorem weightedLogSpotTerminalPrice_def {hα₀ : 0 < α} {hα₁ : α < 1}
    {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p} (g : CkHolderSpace 2 α ℝ ℝ) :
    weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g =
      weightedLogSpotPrice (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g) := by
  rfl

@[simp]
theorem weightedLogSpotTerminalPrice_of_mem {hα₀ : 0 < α} {hα₁ : α < 1}
    {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p} (g : CkHolderSpace 2 α ℝ ℝ)
    (s : ℝ) (t : Icc t₀ t₁) :
    weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g s t =
      (1 + s) * weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g (slabMk (log s) t) := by
  rw [weightedLogSpotTerminalPrice_def, weightedLogSpotPrice_of_mem]

@[simp]
theorem weightedLogSpotTerminalPrice_exp_div {hα₀ : 0 < α} {hα₁ : α < 1}
    {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p} (g : CkHolderSpace 2 α ℝ ℝ) (y t : ℝ) :
    weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g (exp y) t / (1 + exp y) =
      timeExtension ht.le (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g) y t := by
  rw [weightedLogSpotTerminalPrice_def, weightedLogSpotPrice_exp_div]

theorem weightedLogSpotTerminalPrice_exp_div_of_mem {hα₀ : 0 < α} {hα₁ : α < 1}
    {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p} (g : CkHolderSpace 2 α ℝ ℝ)
    (y : ℝ) (t : Icc t₀ t₁) :
    weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g (exp y) t / (1 + exp y) =
      weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g (slabMk y t) := by
  rw [weightedLogSpotTerminalPrice_exp_div, timeExtension_of_mem]

theorem weightedLogSpotTerminalPrice_terminal {hα₀ : 0 < α} {hα₁ : α < 1}
    {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p} {g : CkHolderSpace 2 α ℝ ℝ} {h : ℝ → ℝ}
    (hg : ∀ y, g y = h (exp y) / (1 + exp y)) {s : ℝ} (hs : 0 < s) :
    weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g s t₁ = h s :=
  weightedLogSpotPrice_terminal _
    (fun y ↦ by rw [weightedLogSpotTerminalSolutionL_slabMk_right, hg]) hs

/-- `weightedLogSpotTerminalPrice` solves the spot pricing PDE on `(0, ∞) × [t₀, t₁]` with
time derivative within `[t₀, t₁]`. -/
theorem pde_weightedLogSpotTerminalPrice {hα₀ : 0 < α} {hα₁ : α < 1}
    {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p} (g : CkHolderSpace 2 α ℝ ℝ)
    {s : ℝ} (hs : 0 < s) (t : Icc t₀ t₁) {σ₀ r₀ : ℝ}
    (ha₀ : a (slabMk (log s) t) = σ₀ ^ 2 / 2) (hr₀ : r (slabMk (log s) t) = r₀) :
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
theorem pde_weightedLogSpotTerminalPrice_Ici {hα₀ : 0 < α} {hα₁ : α < 1}
    {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p} (g : CkHolderSpace 2 α ℝ ℝ)
    {s t : ℝ} (hs : 0 < s) (ht' : t ∈ Ico t₀ t₁) {σ₀ r₀ : ℝ}
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
theorem pde_weightedLogSpotTerminalPrice_Ioo {hα₀ : 0 < α} {hα₁ : α < 1}
    {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p} (g : CkHolderSpace 2 α ℝ ℝ)
    {s t : ℝ} (hs : 0 < s) (ht' : t ∈ Ioo t₀ t₁) {σ₀ r₀ : ℝ}
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
theorem abs_weightedLogSpotTerminalPrice_le_of_rate_ge {hα₀ : 0 < α} {hα₁ : α < 1}
    {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p}
    {γ M : ℝ} (hr : ∀ p, -γ ≤ r p) (hγ : 0 ≤ γ)
    {g : CkHolderSpace 2 α ℝ ℝ} (hg : ∀ y, |g y| ≤ M)
    {s : ℝ} (hs : 0 ≤ s) (t : Icc t₀ t₁) :
    |weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g s t| ≤
      exp (γ * (t₁ - t)) * M * (1 + s) := by
  rw [weightedLogSpotTerminalPrice_def, weightedLogSpotPrice_of_mem, abs_mul,
    abs_of_pos (by positivity : 0 < 1 + s), mul_comm]
  exact mul_le_mul_of_nonneg_right
    (by simpa using abs_weightedLogSpotTerminalSolutionL_le_of_rate_ge hr hγ hg (slabMk (log s) t))
    (by positivity)

/-- Combined linear-growth bound on the price and dollar delta of `weightedLogSpotTerminalPrice`,
for all `s ≥ 0` and all `t : ℝ`. -/
theorem abs_weightedLogSpotTerminalPrice_add_abs_mul_deriv_le {hα₀ : 0 < α} {hα₁ : α < 1}
    {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p} (g : CkHolderSpace 2 α ℝ ℝ)
    {s : ℝ} (hs : 0 ≤ s) (t : ℝ) :
    |weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g s t| +
        |s * deriv (fun x ↦ weightedLogSpotTerminalPrice hα₀ hα₁ ht a r ha g x t) s| ≤
      2 * ‖weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g‖ * (1 + s) :=
  abs_weightedLogSpotPrice_add_abs_mul_deriv_le _ hs t

/-- Along any positive continuous stock trajectory on `[t₀, t₁]`, both `weightedLogSpotPrice u`
and its dollar delta exposure belong to every `L^q` on `[t₀, t₁)` (including `q = ∞`). -/
theorem memLp_price_path_and_delta_exposure_weightedLogSpotPrice
    (u : ParabolicC2HolderSpace α ℝ ℝ ht) {S : ℝ → ℝ}
    (hS : ContinuousOn S (Icc t₀ t₁)) (hpos : ∀ t ∈ Icc t₀ t₁, 0 < S t) (q : ℝ≥0∞) :
    MemLp (fun t ↦ weightedLogSpotPrice u (S t) t) q (volume.restrict (Ico t₀ t₁)) ∧
      MemLp (fun t ↦ S t * deriv (fun s ↦ weightedLogSpotPrice u s t) (S t)) q
        (volume.restrict (Ico t₀ t₁)) :=
  memLp_price_path_and_delta_exposure_of_growth (A := 2 * ‖u‖) (p := 1)
    ((continuousOn_weightedLogSpotPrice u).mono (prod_mono_right (subset_univ _)))
    ((continuousOn_deriv_weightedLogSpotPrice_spot u).mono (prod_mono_right (subset_univ _)))
    (fun s hs t _ ↦ by
      simpa only [rpow_one] using abs_weightedLogSpotPrice_add_abs_mul_deriv_le u hs.le t)
    hS hpos q

/-- Pathwise time-integrability of the stock drift, stock diffusion, and bond gains of the delta
hedge built from any `u : ParabolicC2HolderSpace α ℝ ℝ ht`. -/
theorem integrable_delta_hedge_gains_weightedLogSpotPrice
    (u : ParabolicC2HolderSpace α ℝ ℝ ht) {S β μ σ r : ℝ → ℝ}
    (hS : ContinuousOn S (Icc t₀ t₁)) (hpos : ∀ t ∈ Icc t₀ t₁, 0 < S t)
    (hμ : IntegrableOn μ (Ico t₀ t₁)) (hσ : MemLp σ 2 (volume.restrict (Ico t₀ t₁)))
    (hr : IntegrableOn r (Ico t₀ t₁))
    (hβ : ∀ᵐ t ∂volume.restrict (Ico t₀ t₁), β t ≠ 0) :
    IntegrableOn (fun t ↦ μ t * S t * deriv (fun s ↦ weightedLogSpotPrice u s t) (S t))
        (Ico t₀ t₁) ∧
      MemLp (fun t ↦ σ t * S t * deriv (fun s ↦ weightedLogSpotPrice u s t) (S t)) 2
        (volume.restrict (Ico t₀ t₁)) ∧
      IntegrableOn (fun t ↦ r t * β t *
        BlackScholes.hedgeBondHolding (fun s ↦ weightedLogSpotPrice u s t) (S t) (β t))
        (Ico t₀ t₁) :=
  integrable_delta_hedge_gains_of_growth (A := 2 * ‖u‖) (p := 1)
    ((continuousOn_weightedLogSpotPrice u).mono (prod_mono_right (subset_univ _)))
    ((continuousOn_deriv_weightedLogSpotPrice_spot u).mono (prod_mono_right (subset_univ _)))
    (fun s hs t _ ↦ by
      simpa only [rpow_one] using abs_weightedLogSpotPrice_add_abs_mul_deriv_le u hs.le t)
    hS hpos hμ hσ hr hβ

/-- **Existence of classical linear-growth prices under log-spot coefficient regularity.** Let
`0 < α < 1`, `t₀ < t₁`, `0 < δ`, and let the local volatility `σ(s, t)` satisfy
`δ ≤ σ(s, t)² ≤ Λ` for `s > 0`, `t ∈ [t₀, t₁]`, with `y ↦ σ(e^y, t)` uniformly `L`-Lipschitz and
`t ↦ σ(e^y, t)` uniformly `(α / 2)`-Hölder, and let `r` be `(α / 2)`-Hölder on `[t₀, t₁]`. For
every terminal payoff `h` whose weighted log-spot trace `y ↦ h(e^y) / (1 + e^y)` is represented by
`g ∈ C_b^{2,α}(ℝ)`, there exists `u ∈ C_b^{2+α,1+α/2}(ℝ × [t₀, t₁])` with terminal trace `g` whose
reconstructed price `C = weightedLogSpotPrice u` takes terminal value `h` on `(0, ∞)` and solves
the classical spot pricing PDE in all three time-derivative conventions (within `[t₀, t₁]`, within
`[t₀, ∞)` before maturity, and ordinary on `(t₀, t₁)`). -/
theorem exists_classicalPrice_of_spotCoefficients
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
  have hM (y : ℝ) (t : ℝ) (ht' : t ∈ Icc t₀ t₁) : |σ (exp y) t| ≤ M :=
    _root_.Real.abs_le_sqrt (hσ_bounds (exp y) (exp_pos y) t ht').2
  let σH := logSpotVolatilityHolder hα₀ hα₁.le hM hσ_lip hσ_hold
  let a := halfSqVolatility σH
  let rH := shortRateSlabHolder (E := ℝ) hα₀ hr_hold
  have ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p :=
    ⟨δ / 2, half_pos hδ, le_halfSqVolatility_of_sq_ge fun p ↦ by
      simpa [σH] using (hσ_bounds _ (exp_pos _) _ (slabTime p).2).1⟩
  refine ⟨weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a rH ha g,
    weightedLogSpotTerminalSolutionL_slabMk_right g,
    fun s hs ↦ weightedLogSpotTerminalPrice_terminal hg hs,
    fun s hs t ht' ↦ pde_weightedLogSpotTerminalPrice g hs ⟨t, ht'⟩
      (by simp [a, σH, exp_log hs]) (by simp [rH]),
    fun s hs t ht' ↦ pde_weightedLogSpotTerminalPrice_Ici g hs ht'
      (by simp [a, σH, exp_log hs]) (by simp [rH]),
    fun s hs t ht' ↦ pde_weightedLogSpotTerminalPrice_Ioo g hs ht'
      (by simp [a, σH, exp_log hs]) (by simp [rH])⟩

private theorem hasDerivAt_shift_time {f : ℝ → ℝ} {t₀ τ : ℝ} (hf : DifferentiableAt ℝ f (t₀ + τ)) :
    HasDerivAt (fun τ' ↦ f (t₀ + τ')) (deriv f (t₀ + τ)) τ :=
  (hf.hasDerivAt.comp τ ((hasDerivAt_id τ).const_add t₀)).congr_deriv (mul_one _)

/-- **Uniqueness of the reconstructed spot price in the classical linear-growth class.** On
`[t₀, t₁]` with `t₀ < t₁`, if `u : ParabolicC2HolderSpace α ℝ ℝ ht` makes `weightedLogSpotPrice u`
solve the spot pricing PDE on `(0, ∞) × (t₀, t₁)` for bounded `σ² ≤ Λ` and `|r| ≤ R`, then any
classical solution `C` of linear growth `|C(s, t)| ≤ A (1 + s)` with the same terminal value at
`t₁` on `(0, ∞)` equals `weightedLogSpotPrice u` everywhere on `(0, ∞) × [t₀, t₁]`. -/
theorem eq_weightedLogSpotPrice_of_pde_of_terminal {Λ R A : ℝ}
    {σ : ℝ → ℝ → ℝ} {r : ℝ → ℝ}
    (u : ParabolicC2HolderSpace α ℝ ℝ ht) {C : ℝ → ℝ → ℝ}
    (hσ : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → σ s t ^ 2 ≤ Λ)
    (hr : ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → |r t| ≤ R)
    (hC_cont : ContinuousOn (Function.uncurry C) (Ioi 0 ×ˢ Icc t₀ t₁))
    (hC_growth : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ → |C s t| ≤ A * (1 + s))
    (hC_cd : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → ContDiffAt ℝ 2 (fun x ↦ C x t) s)
    (hC_diff : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → DifferentiableAt ℝ (fun τ ↦ C s τ) t)
    (hC_pde : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ →
      deriv (fun τ ↦ C s τ) t + σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ C x t) s +
        r t * (s * deriv (fun x ↦ C x t) s - C s t) = 0)
    (hu_pde : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ →
      deriv (weightedLogSpotPrice u s) t +
        σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ weightedLogSpotPrice u x t) s +
        r t * (s * deriv (fun x ↦ weightedLogSpotPrice u x t) s -
          weightedLogSpotPrice u s t) = 0)
    (hterm : ∀ ⦃s⦄, 0 < s → C s t₁ = weightedLogSpotPrice u s t₁) :
    ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ → C s t = weightedLogSpotPrice u s t := by
  intro s hs t ht'
  have hmemIoo {τ : ℝ} (hτ : τ ∈ Ioo 0 (t₁ - t₀)) : t₀ + τ ∈ Ioo t₀ t₁ :=
    ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hmemIcc {τ : ℝ} (hτ : τ ∈ Icc 0 (t₁ - t₀)) : t₀ + τ ∈ Icc t₀ t₁ :=
    ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hkey := eq_of_pde_eq_of_terminal_eq
    (C₁ := fun x τ ↦ C x (t₀ + τ)) (C₂ := fun x τ ↦ weightedLogSpotPrice u x (t₀ + τ))
    (σ := fun x τ ↦ σ x (t₀ + τ)) (r := fun τ ↦ r (t₀ + τ)) (T := t₁ - t₀) (A := |A| + ‖u‖)
    (fun _ hx _ hτ ↦ hσ hx (hmemIoo hτ))
    (fun _ hτ ↦ hr (hmemIoo hτ))
    (hC_cont.comp (continuousOn_fst.prodMk (continuousOn_const.add continuousOn_snd))
      fun p hp ↦ ⟨hp.1, hmemIcc hp.2⟩)
    ((continuousOn_weightedLogSpotPrice u).comp
      (continuousOn_fst.prodMk (continuousOn_const.add continuousOn_snd))
      fun p hp ↦ ⟨hp.1, trivial⟩)
    (fun x hx τ hτ ↦ by
      have h₁ := (hC_growth hx (hmemIcc hτ)).trans
        (mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity))
      have h₂ := abs_weightedLogSpotPrice_le u hx.le (t₀ + τ)
      linarith [abs_sub (C x (t₀ + τ)) (weightedLogSpotPrice u x (t₀ + τ))])
    (fun _ hx _ hτ ↦ hC_cd hx (hmemIoo hτ))
    (fun _ hx _ hτ ↦ (contDiffOn_weightedLogSpotPrice u
      ⟨t₀ + _, Ioo_subset_Icc_self (hmemIoo hτ)⟩).contDiffAt (Ioi_mem_nhds hx))
    (fun _ hx _ hτ ↦ (hasDerivAt_shift_time (hC_diff hx (hmemIoo hτ))).differentiableAt)
    (fun x _ _ hτ ↦ (hasDerivAt_shift_time
      (differentiableAt_weightedLogSpotPrice_time u x (hmemIoo hτ))).differentiableAt)
    (fun x hx τ hτ ↦ by
      rw [(hasDerivAt_shift_time (hC_diff hx (hmemIoo hτ))).deriv,
        (hasDerivAt_shift_time (differentiableAt_weightedLogSpotPrice_time u x (hmemIoo hτ))).deriv]
      exact (hC_pde hx (hmemIoo hτ)).trans (hu_pde hx (hmemIoo hτ)).symm)
    (fun x hx ↦ by simpa [add_sub_cancel] using hterm hx)
    hs ⟨sub_nonneg.2 ht'.1, sub_le_sub_right ht'.2 t₀⟩
  simpa only [add_sub_cancel] using hkey

end SpotSolutions

end TauCeti.Finance
