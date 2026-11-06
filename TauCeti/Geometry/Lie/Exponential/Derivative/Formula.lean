/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.Derivative.Basic
public import TauCeti.Analysis.Normed.Algebra.OneSubExpNegDivSelf.Basic
import TauCeti.Geometry.Lie.Exponential.BCH.Basic
import TauCeti.Geometry.Lie.Adjoint.Exponential.Formula
import TauCeti.Geometry.Lie.Adjoint.Representation.Basic
import TauCeti.Analysis.Normed.Algebra.OneSubExpNegDivSelf.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The differential of the Lie-group exponential

For a finite-dimensional real smooth Lie group, the differential of `lieExp` at `X` is left
translation by `lieExp X` composed with the entire operator series
`oneSubExpNegDivSelf ℝ (ad X)`. This is the everywhere-defined interpretation of
`(1 - exp (-ad X)) / ad X`; no inverse of `ad X` is required.

The source tangent space is identified with left-invariant derivations by
`NormedSpace.fromTangentSpace`. Evaluation at the identity identifies those derivations with the
identity tangent space before applying left translation.

## Main results

* `TauCeti.Lie.hasMFDerivAt_lieExp`: the derivative as a composition of continuous linear maps.
* `TauCeti.Lie.mfderiv_lieExp_apply`: its value on a vector in the Lie algebra.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222 (2015),
  §5.4, Theorem 5.4 and Lemma 5.5, pp. 114–116, for the matrix exponential formula.
-/

public section

noncomputable section

open Set Filter Manifold
open scoped ContDiff Manifold Topology

namespace TauCeti.Lie

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] TauCeti.normedAlgebraRatOfReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G]

section Auxiliary

variable [T2Space G] [BoundarylessManifold I G]

private local instance : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
  finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint

private local instance : CompleteSpace (LeftInvariantDerivation I G) :=
  FiniteDimensional.complete ℝ _

-- Center the exponential at the identity before taking its local logarithm.
private def centeredProduct (X Y : LeftInvariantDerivation I G) : G :=
  (lieExp (I := I) (G := G) X)⁻¹ * lieExp (I := I) (G := G) (X + Y)

private def centeredLog (X Y : LeftInvariantDerivation I G) : LeftInvariantDerivation I G :=
  lieLog (I := I) (centeredProduct (I := I) X Y)

@[simp] private lemma centeredProduct_zero_right (X : LeftInvariantDerivation I G) :
    centeredProduct (I := I) (G := G) X 0 = 1 := by
  simp only [centeredProduct, add_zero, inv_mul_cancel]

@[simp] private lemma centeredLog_zero_right (X : LeftInvariantDerivation I G) :
    centeredLog (I := I) (G := G) X 0 = 0 := by
  simp only [centeredLog, centeredProduct_zero_right, lieLog_one]

private def leftDexp (X : LeftInvariantDerivation I G) :
    LeftInvariantDerivation I G →L[ℝ] LeftInvariantDerivation I G :=
  fderiv ℝ (centeredLog (I := I) (G := G) X) 0

private lemma contMDiff_centeredProduct :
    ContMDiff 𝓘(ℝ, LeftInvariantDerivation I G × LeftInvariantDerivation I G) I ∞
      (Function.uncurry (centeredProduct (I := I) (G := G))) := by
  have hfst : ContMDiff 𝓘(ℝ, LeftInvariantDerivation I G × LeftInvariantDerivation I G)
      𝓘(ℝ, LeftInvariantDerivation I G) ∞
      (fun p : LeftInvariantDerivation I G × LeftInvariantDerivation I G ↦ p.1) :=
    contDiff_fst.contMDiff
  have hadd : ContMDiff 𝓘(ℝ, LeftInvariantDerivation I G × LeftInvariantDerivation I G)
      𝓘(ℝ, LeftInvariantDerivation I G) ∞
      (fun p : LeftInvariantDerivation I G × LeftInvariantDerivation I G ↦ p.1 + p.2) :=
    (contDiff_fst.add contDiff_snd).contMDiff
  exact (((contMDiff_lieExp (I := I) (G := G)).comp hfst).inv).mul
    ((contMDiff_lieExp (I := I) (G := G)).comp hadd)

private lemma contDiffAt_centeredLog (X : LeftInvariantDerivation I G) :
    ContDiffAt ℝ ∞ (Function.uncurry (centeredLog (I := I) (G := G))) (X, 0) := by
  have hl : ContMDiffAt I 𝓘(ℝ, LeftInvariantDerivation I G) ∞ (lieLog (I := I) (G := G))
      (centeredProduct (I := I) (G := G) X 0) := by
    simpa only [centeredProduct_zero_right] using
      contMDiffAt_lieLog_one (I := I) (G := G)
  exact (hl.comp (X, 0) (contMDiff_centeredProduct (I := I) (G := G)).contMDiffAt).contDiffAt

private lemma contDiffAt_leftDexp (X : LeftInvariantDerivation I G) :
    ContDiffAt ℝ ∞ (leftDexp (I := I) (G := G)) X := by
  exact (contDiffAt_centeredLog (I := I) (G := G) X).fderiv
    (f := centeredLog (I := I) (G := G)) (g := fun _ ↦ 0) contDiffAt_const (by simp)

private lemma hasFDerivAt_centeredLog (X : LeftInvariantDerivation I G) :
    HasFDerivAt (centeredLog (I := I) (G := G) X)
      (leftDexp (I := I) (G := G) X) 0 := by
  exact ((contDiffAt_centeredLog (I := I) (G := G) X).comp 0
    (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp) |>.hasFDerivAt

private lemma leftDexp_zero : leftDexp (I := I) (G := G) (0 : LeftInvariantDerivation I G) =
    ContinuousLinearMap.id ℝ (LeftInvariantDerivation I G) := by
  have heq : centeredLog (I := I) (G := G) (0 : LeftInvariantDerivation I G) =ᶠ[𝓝 0] id := by
    filter_upwards [eventually_lieLog_lieExp (I := I) (G := G)] with Y hY
    simpa [centeredLog, centeredProduct] using hY
  have h0 : HasFDerivAt (centeredLog (I := I) (G := G) (0 : LeftInvariantDerivation I G))
      (ContinuousLinearMap.id ℝ (LeftInvariantDerivation I G)) 0 :=
    (hasFDerivAt_id (0 : LeftInvariantDerivation I G)).congr_of_eventuallyEq heq
  exact h0.fderiv

private lemma eventually_exp_centeredLog (X : LeftInvariantDerivation I G) :
    ∀ᶠ Y in 𝓝 (0 : LeftInvariantDerivation I G),
      lieExp (I := I) (centeredLog (I := I) (G := G) X Y) =
        centeredProduct (I := I) X Y := by
  have hp : Continuous (fun Y : LeftInvariantDerivation I G ↦ (X, Y)) :=
    continuous_const.prodMk continuous_id
  have hc := (contMDiff_centeredProduct (I := I) (G := G)).continuous.comp hp
  have ht : Tendsto (centeredProduct (I := I) (G := G) X) (𝓝 0) (𝓝 1) := by
    have h := hc.tendsto (0 : LeftInvariantDerivation I G)
    simp only [Function.comp_def, Function.uncurry_apply_pair, centeredProduct_zero_right] at h
    exact h
  exact ht.eventually (eventually_lieExp_lieLog (I := I) (G := G))

private def variation (X Y : LeftInvariantDerivation I G) (s : ℝ) : LeftInvariantDerivation I G :=
  s • leftDexp (I := I) (G := G) (s • X) Y

private def curveLog (X Y : LeftInvariantDerivation I G) (s r : ℝ) : LeftInvariantDerivation I G :=
  centeredLog (I := I) (G := G) (s • X) (r • (s • Y))

private lemma hasDerivAt_curveLog_zero (X Y : LeftInvariantDerivation I G) (s : ℝ) :
    HasDerivAt (curveLog (I := I) (G := G) X Y s)
      (variation (I := I) (G := G) X Y s) 0 := by
  have h := (hasFDerivAt_centeredLog (I := I) (s • X)).comp_hasDerivAt_of_eq 0
    ((hasDerivAt_id (0 : ℝ)).smul_const (s • Y)) (by simp)
  simp only [Function.comp_def, ContinuousLinearMap.map_smul, one_smul] at h
  exact h

private lemma hasDerivAt_variation_zero (X Y : LeftInvariantDerivation I G) :
    HasDerivAt (variation (I := I) (G := G) X Y) Y 0 := by
  have hc : ContDiffAt ℝ ∞ (fun s : ℝ ↦ leftDexp (I := I) (G := G) (s • X)) 0 :=
    by
    have h0 : ContDiffAt ℝ ∞ (leftDexp (I := I) (G := G)) ((0 : ℝ) • X) := by
      simpa only [zero_smul] using contDiffAt_leftDexp (I := I) (G := G) 0
    exact h0.comp 0 (contDiffAt_id.smul_const X)
  have hv : DifferentiableAt ℝ (fun s : ℝ ↦ leftDexp (I := I) (G := G) (s • X) Y) 0 :=
    (hc.clm_apply contDiffAt_const).differentiableAt (by simp)
  have h := (hasDerivAt_id (0 : ℝ)).smul hv.hasDerivAt
  simp only [id_eq, zero_smul, leftDexp_zero, ContinuousLinearMap.id_apply,
    zero_add, one_smul] at h
  exact h

private lemma eventually_exp_curveLog (X Y : LeftInvariantDerivation I G) (s : ℝ) :
    ∀ᶠ r in 𝓝 (0 : ℝ), lieExp (I := I) (G := G) (curveLog (I := I) X Y s r) =
      centeredProduct (I := I) (G := G) (s • X) (r • (s • Y)) := by
  have ht : Tendsto (fun r : ℝ ↦ r • (s • Y)) (𝓝 0) (𝓝 0) := by
    simpa only [id_eq, zero_smul] using
      (tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 (0 : ℝ)) (𝓝 0)).smul_const (s • Y)
  simpa only [curveLog] using ht.eventually (eventually_exp_centeredLog (I := I) (s • X))

private lemma centeredProduct_add_smul (X Y : LeftInvariantDerivation I G) (s t r : ℝ) :
    centeredProduct (I := I) ((s + t) • X) (r • ((s + t) • Y)) =
      (lieExp (I := I) (s • X))⁻¹ *
        centeredProduct (I := I) (t • X) (r • (t • Y)) * lieExp (I := I) (s • X) *
        centeredProduct (I := I) (s • X) (r • (s • Y)) := by
  have hscale (u : ℝ) : u • X + r • (u • Y) = u • (X + r • Y) := by module
  simp only [centeredProduct, hscale]
  have hsum (Z : LeftInvariantDerivation I G) :
      lieExp (I := I) ((s + t) • Z) = lieExp (I := I) (t • Z) * lieExp (I := I) (s • Z) := by
    rw [add_comm s t, lieExp_add_smul]
  rw [hsum, hsum]
  group

private lemma eventually_curveLog_add (X Y : LeftInvariantDerivation I G) (s t : ℝ) :
    ∀ᶠ r in 𝓝 (0 : ℝ), curveLog (I := I) X Y (s + t) r =
      lieLog (I := I)
        (lieExp (I := I) (TauCeti.Lie.Ad (I := I) ((lieExp (I := I) (s • X))⁻¹)
          (curveLog (I := I) X Y t r)) * lieExp (I := I) (curveLog (I := I) X Y s r)) := by
  filter_upwards [eventually_exp_curveLog (I := I) X Y t,
    eventually_exp_curveLog (I := I) X Y s] with r ht hs
  rw [← TauCeti.Lie.conj_lieExp, ht, hs, inv_inv]
  exact congrArg (lieLog (I := I)) (centeredProduct_add_smul (I := I) X Y s t r)

@[simp] private lemma curveLog_zero (X Y : LeftInvariantDerivation I G) (s : ℝ) :
    curveLog (I := I) X Y s 0 = 0 := by
  simp only [curveLog, zero_smul, centeredLog_zero_right]

-- Differentiating the centered one-parameter subgroup law gives an additive cocycle.
private lemma variation_add (X Y : LeftInvariantDerivation I G) (s t : ℝ) :
    variation (I := I) X Y (s + t) = variation (I := I) X Y s +
      TauCeti.Lie.continuousAdjointRepresentation (I := I) ((lieExp (I := I) (s • X))⁻¹)
        (variation (I := I) X Y t) := by
  let A : LeftInvariantDerivation I G →L[ℝ] LeftInvariantDerivation I G :=
    TauCeti.Lie.continuousAdjointRepresentation (I := I) ((lieExp (I := I) (s • X))⁻¹)
  have ht := hasDerivAt_curveLog_zero (I := I) X Y t
  have hs := hasDerivAt_curveLog_zero (I := I) X Y s
  have hpair := HasDerivAt.prodMk (A.hasFDerivAt.comp_hasDerivAt 0 ht) hs
  have hbch := HasFDerivAt.comp_hasDerivAt_of_eq 0
    (TauCeti.hasFDerivAt_lieLocalBCH_representative (I := I) (G := G)) hpair (by simp)
  have heq : curveLog (I := I) X Y (s + t) =ᶠ[𝓝 0]
      (fun r ↦ lieLog (I := I)
        (lieExp (I := I) (A (curveLog (I := I) X Y t r)) *
          lieExp (I := I) (curveLog (I := I) X Y s r))) := by
    filter_upwards [eventually_curveLog_add (I := I) X Y s t] with r hr
    simpa only [A, TauCeti.Lie.continuousAdjointRepresentation_apply] using hr
  have htotal : HasDerivAt (curveLog (I := I) X Y (s + t))
      (A (variation (I := I) X Y t) + variation (I := I) X Y s) 0 := by
    have h := hbch.congr_of_eventuallyEq heq
    simp only [add_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] at h
    exact h
  exact (hasDerivAt_curveLog_zero (I := I) X Y (s + t)).unique htotal |>.trans (add_comm _ _)

private lemma hasDerivAt_variation (X Y : LeftInvariantDerivation I G) (s : ℝ) :
    HasDerivAt (variation (I := I) X Y)
      (TauCeti.Lie.continuousAdjointRepresentation (I := I) ((lieExp (I := I) (s • X))⁻¹) Y) s := by
  let A : LeftInvariantDerivation I G →L[ℝ] LeftInvariantDerivation I G :=
    TauCeti.Lie.continuousAdjointRepresentation (I := I) ((lieExp (I := I) (s • X))⁻¹)
  have hshift := (hasDerivAt_variation_zero (I := I) X Y).scomp_of_eq s
    ((hasDerivAt_id s).sub_const s) (by simp)
  have h := (A.hasFDerivAt.comp_hasDerivAt s hshift).const_add (variation (I := I) X Y s)
  have heq : variation (I := I) X Y =
      (fun u ↦ variation (I := I) X Y s + A (variation (I := I) X Y (u - s))) := by
    funext u
    simpa only [show s + (u - s) = u by ring] using
      variation_add (I := I) X Y s (u - s)
  rw [heq]
  simp only [Function.comp_def, one_smul, id_eq] at h
  exact h

private lemma contDiff_adjointCurve (X : LeftInvariantDerivation I G) :
    ContDiff ℝ ∞ (fun s : ℝ ↦ TauCeti.Lie.continuousAdjointRepresentation (I := I)
      ((lieExp (I := I) (s • X))⁻¹)) := by
  have hg : ContMDiff 𝓘(ℝ, ℝ) I ∞
      (fun s : ℝ ↦ (lieExp (I := I) (s • X))⁻¹) :=
    ((contMDiff_lieExp (I := I) (G := G)).comp
      (contDiff_id.smul_const X).contMDiff).inv
  exact ((TauCeti.Lie.contMDiff_continuousAdjointRepresentation (I := I) (G := G)).comp hg).contDiff

-- Integrating the cocycle derivative identifies the left-translated differential.
private lemma leftDexp_eq_integral (X : LeftInvariantDerivation I G) :
    leftDexp (I := I) (G := G) X =
      ∫ s in (0 : ℝ)..1, TauCeti.Lie.continuousAdjointRepresentation (I := I)
        ((lieExp (I := I) (s • X))⁻¹) := by
  apply ContinuousLinearMap.ext
  intro Y
  rw [ContinuousLinearMap.intervalIntegral_apply
    ((contDiff_adjointCurve (I := I) X).continuous.intervalIntegrable 0 1)]
  have hint := ((contDiff_adjointCurve (I := I) X).continuous.clm_apply
    (continuous_const : Continuous (fun _ : ℝ ↦ Y))).intervalIntegrable
      (μ := MeasureTheory.volume) 0 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ ↦ hasDerivAt_variation (I := I) X Y s) hint
  simpa [variation] using h.symm

private lemma adjointCurve_eq_exp (X : LeftInvariantDerivation I G) (s : ℝ) :
    TauCeti.Lie.continuousAdjointRepresentation (I := I) ((lieExp (I := I) (s • X))⁻¹) =
      NormedSpace.exp (s • -(LinearMap.toContinuousLinearMap
        (LieAlgebra.ad ℝ (LeftInvariantDerivation I G) X))) := by
  have ha : LinearMap.toContinuousLinearMap
      (LieAlgebra.ad ℝ (LeftInvariantDerivation I G) (-(s • X))) =
      s • -(LinearMap.toContinuousLinearMap (LieAlgebra.ad ℝ (LeftInvariantDerivation I G) X)) := by
    ext Z
    simp [LieAlgebra.ad_apply]
  ext Y
  rw [TauCeti.Lie.continuousAdjointRepresentation_apply, ← lieExp_neg,
    LeftInvariantDerivation.Ad_lieExp_apply, ha]

private lemma leftDexp_eq_quotient (X : LeftInvariantDerivation I G) :
    leftDexp (I := I) (G := G) X =
      oneSubExpNegDivSelf ℝ (LinearMap.toContinuousLinearMap
        (LieAlgebra.ad ℝ (LeftInvariantDerivation I G) X)) := by
  rw [leftDexp_eq_integral, oneSubExpNegDivSelf_eq_integral_exp]
  exact intervalIntegral.integral_congr fun s _ ↦ adjointCurve_eq_exp (I := I) X s

private lemma hasFDerivAt_chart_centeredProduct (X : LeftInvariantDerivation I G) :
    HasFDerivAt
      (fun Y : LeftInvariantDerivation I G ↦ extChartAt I (1 : G) (centeredProduct (I := I) X Y))
      ((leftInvariantDerivationLinearIsometryEquivModelVectorSpace
        (I := I) (G := G)).toContinuousLinearEquiv.toContinuousLinearMap.comp
          (leftDexp (I := I) (G := G) X)) 0 := by
  have hd := hasFDerivAt_centeredLog (I := I) X
  have hz : HasFDerivAt
      (fun Z : LeftInvariantDerivation I G ↦ extChartAt I (1 : G) (lieExp (I := I) Z))
      (leftInvariantDerivationLinearIsometryEquivModelVectorSpace
        (I := I) (G := G)).toContinuousLinearEquiv.toContinuousLinearMap
      (centeredLog (I := I) (G := G) X 0) := by
    simpa only [centeredLog_zero_right] using
      hasFDerivAt_extChartAt_lieExp_zero (I := I) (G := G)
  apply (hz.comp 0 hd).congr_of_eventuallyEq
  filter_upwards [eventually_exp_centeredLog (I := I) X] with Y hY
  exact congrArg (extChartAt I (1 : G)) hY.symm

-- The centered value is 1. Its coordinates use the canonical
-- identity-tangent/model-space equivalence.
private lemma mfderiv_centeredProduct_model (X Y : LeftInvariantDerivation I G) :
    groupLieAlgebraEquivModelVectorSpace (I := I) (G := G)
      (mfderiv 𝓘(ℝ, LeftInvariantDerivation I G) I
        (centeredProduct (I := I) (G := G) X) 0
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : LeftInvariantDerivation I G)).symm Y)) =
      leftInvariantDerivationLinearIsometryEquivModelVectorSpace (I := I) (G := G)
        (leftDexp (I := I) (G := G) X Y) := by
  let u := centeredProduct (I := I) (G := G) X
  let w := (NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : LeftInvariantDerivation I G)).symm Y
  have hp : ContMDiff 𝓘(ℝ, LeftInvariantDerivation I G)
      𝓘(ℝ, LeftInvariantDerivation I G × LeftInvariantDerivation I G) ∞
      (fun Z : LeftInvariantDerivation I G ↦ (X, Z)) :=
    (contDiff_const.prodMk contDiff_id).contMDiff
  have hu := ((contMDiff_centeredProduct (I := I) (G := G)).comp hp).mdifferentiableAt
    (x := 0) (by simp)
  have hu0 : u 0 = 1 := centeredProduct_zero_right X
  have hext : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I (1 : G)) (u 0) := by
    rw [hu0]
    exact mdifferentiableAt_extChartAt (mem_chart_source H (1 : G))
  have hc := (hext.hasMFDerivAt.comp 0 hu.hasMFDerivAt).mfderiv
  rw [mfderiv_eq_fderiv] at hc
  have hcoords := DFunLike.congr_fun hc w
  simp only [w, NormedSpace.fromTangentSpace_symm_apply] at hcoords
  have hFd := DFunLike.congr_fun (hasFDerivAt_chart_centeredProduct (I := I) X).fderiv Y
  have hresult := hcoords.symm.trans hFd
  rw [hu0, mfderiv_extChartAt_self] at hresult
  simp only [ContinuousLinearMap.comp_apply] at hresult
  simp only [groupLieAlgebraEquivModelVectorSpace]
  exact hresult

-- Translation back from the identity gives the differential of the exponential itself.
private lemma mfderiv_lieExp_aux (X : LeftInvariantDerivation I G)
    (v : TangentSpace 𝓘(ℝ, LeftInvariantDerivation I G) X) :
    mfderiv 𝓘(ℝ, LeftInvariantDerivation I G) I (lieExp (I := I) (G := G)) X v =
      mulInvariantVectorField
        (leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint
            (leftDexp (I := I) (G := G) X (NormedSpace.fromTangentSpace (𝕜 := ℝ) X v)))
        (lieExp (I := I) X) := by
  let Y := NormedSpace.fromTangentSpace (𝕜 := ℝ) X v
  let w := (NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : LeftInvariantDerivation I G)).symm Y
  let u := centeredProduct (I := I) (G := G) X
  let f := fun Z : LeftInvariantDerivation I G ↦ (lieExp (I := I) X)⁻¹ * lieExp (I := I) Z
  have hExp := (contMDiff_lieExp (I := I) (G := G)).mdifferentiableAt (x := X) (by simp)
  have hf : MDifferentiableAt 𝓘(ℝ, LeftInvariantDerivation I G) I f X :=
    mdifferentiableAt_mul_left.comp X hExp
  have hadd : HasFDerivAt (fun Z : LeftInvariantDerivation I G ↦ X + Z)
      (ContinuousLinearMap.id ℝ (LeftInvariantDerivation I G)) 0 := by
    exact (hasFDerivAt_id (𝕜 := ℝ) (0 : LeftInvariantDerivation I G)).const_add X
  have haddDiff := hadd.differentiableAt.mdifferentiableAt
  have hshift : mfderiv 𝓘(ℝ, LeftInvariantDerivation I G) 𝓘(ℝ, LeftInvariantDerivation I G)
      (fun Z : LeftInvariantDerivation I G ↦ X + Z) 0 w = v := by
    rw [mfderiv_eq_fderiv, hadd.fderiv]
    simp only [NormedSpace.fromTangentSpace_apply,
      NormedSpace.fromTangentSpace_symm_apply, w, Y]
    -- The normed-space tangent identification preserves the underlying vector.
    rfl
  have hc1 := mfderiv_comp_apply X
    (mdifferentiableAt_mul_left (I := I) (a := (lieExp (I := I) X)⁻¹)) hExp v
  have hc2 := mfderiv_comp_apply_of_eq 0 hf haddDiff (by simp) w
  rw [hshift] at hc2
  have hresult := mfderiv_centeredProduct_model (I := I) X Y
  apply TauCeti.mfderiv_inv_mul_injective (lieExp (I := I) X)
  rw [TauCeti.mfderiv_inv_mul_mulInvariantVectorField]
  let e := groupLieAlgebraEquivModelVectorSpace (I := I) (G := G)
  apply e.injective
  have hmodel : e (mfderiv I I ((lieExp (I := I) X)⁻¹ * ·)
      (lieExp (I := I) X)
        (mfderiv 𝓘(ℝ, LeftInvariantDerivation I G) I (lieExp (I := I) (G := G)) X v)) =
      leftInvariantDerivationLinearIsometryEquivModelVectorSpace (I := I) (G := G)
        (leftDexp (I := I) (G := G) X Y) := by
    calc
      _ = e (mfderiv 𝓘(ℝ, LeftInvariantDerivation I G) I f X v) := congrArg e hc1.symm
      _ = e (mfderiv 𝓘(ℝ, LeftInvariantDerivation I G) I u 0 w) := congrArg e hc2.symm
      _ = _ := hresult
  rw [leftInvariantDerivationLinearIsometryEquivModelVectorSpace_apply] at hmodel
  exact hmodel

end Auxiliary

/-- The differential of the Lie-group exponential is left translation by `lieExp X` composed
with the regularized exponential quotient of `ad X`, under the canonical tangent identifications.
-/
theorem hasMFDerivAt_lieExp (X : LeftInvariantDerivation I G) :
    let _ : T2Space G := I.t2Space_of_lieGroup ∞
    let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
    let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
      finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
    HasMFDerivAt 𝓘(ℝ, LeftInvariantDerivation I G) I (lieExp (I := I) (G := G)) X
      ((mfderiv I I (lieExp (I := I) X * ·) (1 : G)).comp
        ((leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint).toLinearMap.toContinuousLinearMap.comp
          ((oneSubExpNegDivSelf ℝ (LinearMap.toContinuousLinearMap
            (LieAlgebra.ad ℝ (LeftInvariantDerivation I G) X))).comp
              (NormedSpace.fromTangentSpace (𝕜 := ℝ) X).toContinuousLinearMap))) := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  dsimp only
  have hd := (contMDiff_lieExp (I := I) (G := G)).mdifferentiableAt (x := X) (by simp)
  apply hd.hasMFDerivAt.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro v
  have h := mfderiv_lieExp_aux (I := I) X v
  rw [leftDexp_eq_quotient] at h
  rw [mulInvariantVectorField_apply] at h
  -- The translation derivative has codomain at `lieExp X * 1`, whereas the goal is at
  -- `lieExp X`. Both fibres are the model space, but their coercions retain different
  -- universe parameters, so `comp_apply` does not match until the applied maps are exposed.
  change mfderiv 𝓘(ℝ, LeftInvariantDerivation I G) I (lieExp (I := I) (G := G)) X v =
    mfderiv I I (lieExp (I := I) X * ·) (1 : G)
      (leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint
          (oneSubExpNegDivSelf ℝ (LinearMap.toContinuousLinearMap
            (LieAlgebra.ad ℝ (LeftInvariantDerivation I G) X))
              (NormedSpace.fromTangentSpace (𝕜 := ℝ) X v)))
  exact h

/-- On a Lie-algebra vector `Y`, the differential of `lieExp` at `X` is the value at `lieExp X`
of the left-invariant vector field generated by the regularized exponential quotient of `ad X`
applied to `Y`. -/
@[simp]
theorem mfderiv_lieExp_apply (X Y : LeftInvariantDerivation I G) :
    let _ : T2Space G := I.t2Space_of_lieGroup ∞
    let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
    let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
      finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
    mfderiv 𝓘(ℝ, LeftInvariantDerivation I G) I (lieExp (I := I) (G := G)) X
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) X).symm Y) =
      mulInvariantVectorField
        (leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint
            (oneSubExpNegDivSelf ℝ (LinearMap.toContinuousLinearMap
              (LieAlgebra.ad ℝ (LeftInvariantDerivation I G) X)) Y))
        (lieExp (I := I) X) := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  dsimp only
  have h := DFunLike.congr_fun (hasMFDerivAt_lieExp (I := I) X).mfderiv
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ) X).symm Y)
  -- As above, evaluate the composed maps before simplifying the tangent identification.
  change mfderiv 𝓘(ℝ, LeftInvariantDerivation I G) I (lieExp (I := I) (G := G)) X
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) X).symm Y) =
    mulInvariantVectorField
      (leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint
          (oneSubExpNegDivSelf ℝ (LinearMap.toContinuousLinearMap
            (LieAlgebra.ad ℝ (LeftInvariantDerivation I G) X))
              (NormedSpace.fromTangentSpace (𝕜 := ℝ) X
                ((NormedSpace.fromTangentSpace (𝕜 := ℝ) X).symm Y))))
      (lieExp (I := I) X) at h
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h

end TauCeti.Lie
