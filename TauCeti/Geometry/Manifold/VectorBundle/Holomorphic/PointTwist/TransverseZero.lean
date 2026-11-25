/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.LinearDistortion
public import TauCeti.Geometry.Manifold.IsManifold.RestrictScalars
public import TauCeti.Geometry.Manifold.VectorBundle.Holomorphic.PointTwist.EulerClass
public import TauCeti.Geometry.Manifold.VectorBundle.Holomorphic.PointTwist.Negative.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Generic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Linearization

/-!
# Signs of transverse zeros of sections of complex line bundles

Let `σ` be a section of a complex line bundle `L` with fibre `ℂ` over a Riemann surface `X`, and
`x` a zero of `σ`. Read in the chart `φ` of `X` at `x` and the preferred chart of `L` at `x`
(`TauCeti.negPointTwistChartReading`), `σ` is a function of `w = φ z` with real derivative
`D : ℂ →L[ℝ] ℂ` at `φ x`. The zero is *positive* when `D` is close to a complex multiplication,
`‖D - (u ↦ u c)‖ < ‖c‖`, and *negative* when it is close to a conjugate one,
`‖D - (u ↦ conj u c)‖ < ‖c‖`. These are the open conditions under which a zero is untwisted in
`L(-x)`, respectively `L(x)` (`TauCeti.exists_negPointTwist_section_of_hasFDerivAt`,
`TauCeti.exists_pointTwist_section_of_hasFDerivAt`).

This file identifies these signs with the local indices for the canonical orientations of `L` and
`X`: a positive zero has local index `1` and a negative zero local index `-1`
(`TauCeti.sectionIndex_eq_one_of_norm_sub_smulRight_lt`,
`TauCeti.sectionIndex_eq_neg_one_of_norm_sub_smulRight_conjCLE_lt`). Both follow from the local
index being the sign of `det D` (`TauCeti.sectionIndex_eq_sign_det_of_hasFDerivAt_chartAt`) and
the sign of `det D` under each condition (`TauCeti.det_pos_of_norm_sub_smulRight_lt`,
`TauCeti.det_neg_of_norm_sub_smulRight_conjCLE_lt`).

For a compact `X` and a line bundle whose underlying real bundle is smooth, `L` has a smooth
section with finitely many zeros, each transverse
(`TauCeti.exists_contMDiffSection_regular_finite_zero_of_finrank_eq`), so `det D ≠ 0` and each
zero is positive or negative; summing the local indices, the Euler number of `L`, that is
`c₁(L)[X]`, is the number of positive zeros minus the number of negative ones
(`TauCeti.exists_contMDiffSection_complexEulerClass_eq_sum_sign`). This is the input of step 5 of
the proof of the Riemann–Roch formula for real Cauchy–Riemann operators (McDuff–Salamon,
Theorem C.1.10), which twists `L` at these zeros.

## Main results

* `TauCeti.sectionIndex_eq_one_of_norm_sub_smulRight_lt`: a positive zero has local index `1`.
* `TauCeti.sectionIndex_eq_neg_one_of_norm_sub_smulRight_conjCLE_lt`: a negative zero has local
  index `-1`.
* `TauCeti.exists_hasFDerivAt_negPointTwistChartReading_det_ne_zero`: where the linearization of
  a section is surjective, its chart reading has a real derivative of nonzero determinant.
* `TauCeti.exists_contMDiffSection_complexEulerClass_eq_sum_sign`: a smooth section with finitely
  many zeros, each positive or negative, whose signed count is the Euler number of `L`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.1.10.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11 (the Euler class evaluated through the zeros of a section).
-/

public section

noncomputable section

open Bundle Module Set Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
  {L : X → Type} [∀ z, AddCommGroup (L z)] [∀ z, Module ℂ (L z)] [∀ z, Module ℝ (L z)]
  [∀ z, IsScalarTower ℝ ℂ (L z)] [∀ z, TopologicalSpace (L z)]
  [TopologicalSpace (TotalSpace ℂ L)] [FiberBundle ℂ L] [VectorBundle ℂ ℂ L]

local instance instVectorBundleRealTransverseZero : VectorBundle ℝ ℂ L :=
  VectorBundle.restrictScalars ℝ ℂ ℂ L

/-! ### The local index of a positive or negative zero -/

section Index

variable [IsManifold 𝓘(ℂ, ℂ) 1 X] (x : X) {σ : ∀ z, L z}
  (hσ : Continuous fun z ↦ TotalSpace.mk' ℂ z (σ z)) (hσx : σ x = 0) {D : ℂ →L[ℝ] ℂ}
  (hD : HasFDerivAt (negPointTwistChartReading ℂ x σ) D (chartAt ℂ x x)) {c : ℂ}

include hσx hD

/-- **A positive zero has local index one.** Let `σ` be a continuous section of a complex line
bundle `L` with fibre `ℂ` over a Riemann surface `X`, vanishing at `x`. If the real derivative `D`
of the chart reading of `σ` at `φ x`, for the chart `φ` of `X` at `x`, satisfies
`‖D - (u ↦ u c)‖ < ‖c‖`, then the local index of `σ` at `x` is `1`, for the canonical orientations
of `L` and `X`. -/
theorem sectionIndex_eq_one_of_norm_sub_smulRight_lt
    (hDc : ‖D - (ContinuousLinearMap.id ℝ ℂ).smulRight c‖ < ‖c‖) :
    (VectorBundleOrientation.reindex (finCongr (by rw [finrank_self]))
        (VectorBundleOrientation.complex ℂ L)).sectionIndex
        Complex.finrank_real_complex (complexHomologicalOrientation X) hσ x = 1 := by
  have h := det_pos_of_norm_sub_smulRight_lt hDc
  -- `negPointTwistChartReading` is not exposed outside its module, so unfold it by its `_apply`.
  rw [funext (negPointTwistChartReading_apply ℂ x σ)] at hD
  rw [sectionIndex_eq_sign_det_of_hasFDerivAt_chartAt x hσ hσx hD h.ne',
    sign_pos h, SignType.coe_one]

/-- **A negative zero has local index minus one.** Let `σ` be a continuous section of a complex
line bundle `L` with fibre `ℂ` over a Riemann surface `X`, vanishing at `x`. If the real derivative
`D` of the chart reading of `σ` at `φ x`, for the chart `φ` of `X` at `x`, satisfies
`‖D - (u ↦ conj u c)‖ < ‖c‖`, then the local index of `σ` at `x` is `-1`, for the canonical
orientations of `L` and `X`. -/
theorem sectionIndex_eq_neg_one_of_norm_sub_smulRight_conjCLE_lt
    (hDc : ‖D - Complex.conjCLE.toContinuousLinearMap.smulRight c‖ < ‖c‖) :
    (VectorBundleOrientation.reindex (finCongr (by rw [finrank_self]))
        (VectorBundleOrientation.complex ℂ L)).sectionIndex
        Complex.finrank_real_complex (complexHomologicalOrientation X) hσ x = -1 := by
  have h := det_neg_of_norm_sub_smulRight_conjCLE_lt hDc
  -- `negPointTwistChartReading` is not exposed outside its module, so unfold it by its `_apply`.
  rw [funext (negPointTwistChartReading_apply ℂ x σ)] at hD
  rw [sectionIndex_eq_sign_det_of_hasFDerivAt_chartAt x hσ hσx hD h.ne,
    sign_neg h, SignType.coe_neg_one]

end Index

/-! ### The Euler number as a signed count of positive and negative zeros -/

omit [T2Space X] in
/-- **A transverse zero has a chart reading of nonzero Jacobian.** If the linearization of a
section `σ` at `x` is surjective, the chart reading of `σ` at `x` has a real derivative `D` with
`det D ≠ 0`: the linearization is `D` read back into the fibre through the chart of `L` at `x`. -/
theorem exists_hasFDerivAt_negPointTwistChartReading_det_ne_zero {σ : ∀ z, L z} {x : X}
    (hreg : Function.Surjective (sectionLinearization (F := ℂ) 𝓘(ℝ, ℂ) id σ x)) :
    ∃ D : ℂ →L[ℝ] ℂ, HasFDerivAt (negPointTwistChartReading ℂ x σ) D (chartAt ℂ x x) ∧
      D.det ≠ 0 := by
  set e := trivializationAt ℂ L x
  have hxe : x ∈ e.baseSet := mem_baseSet_trivializationAt ℂ L x
  -- The derivative of the reading is the coordinate derivative of `σ` in the chart of `L` at `x`.
  have hD : fderiv ℝ (negPointTwistChartReading ℂ x σ) (chartAt ℂ x x) =
      mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ (e ⟨y, σ y⟩).2) x := by
    rw [funext (negPointTwistChartReading_apply ℂ x σ)]
    exact fderiv_comp_chartAt_symm (E := ℂ) (N := X) (g := fun y ↦ (e ⟨y, σ y⟩).2)
  have hsurj : Function.Surjective (fderiv ℝ (negPointTwistChartReading ℂ x σ) (chartAt ℂ x x)) :=
    fun v ↦ by
      obtain ⟨u, hu⟩ := hreg (e.symmL ℝ x v)
      refine ⟨u, ?_⟩
      have h := congrArg (e.continuousLinearMapAt ℝ x) hu
      rw [sectionLinearization_def, ContinuousLinearMap.comp_apply] at h
      simp only [id_eq] at h
      rwa [e.continuousLinearMapAt_symmL hxe, e.continuousLinearMapAt_symmL hxe, ← hD] at h
  -- A zero derivative is not surjective, so the reading is differentiable.
  have hdiff : DifferentiableAt ℝ (negPointTwistChartReading ℂ x σ) (chartAt ℂ x x) := by
    by_contra h
    obtain ⟨u, hu⟩ := hsurj 1
    simp [fderiv_zero_of_not_differentiableAt h] at hu
  refine ⟨_, hdiff.hasFDerivAt, ?_⟩
  -- A surjective endomorphism of `ℂ` over `ℝ` is invertible, so its determinant is a unit.
  have hbij : Function.Bijective
      (fderiv ℝ (negPointTwistChartReading ℂ x σ) (chartAt ℂ x x) : ℂ →ₗ[ℝ] ℂ) :=
    ⟨LinearMap.injective_iff_surjective.2 hsurj, hsurj⟩
  exact ((LinearMap.isUnit_iff_isUnit_det _).1 ((Module.End.isUnit_iff _).2 hbij)).ne_zero

open Classical in
/-- **The Euler number of a line bundle is the signed count of positive and negative zeros.** Let
`L` be a complex line bundle with fibre `ℂ` over a compact Riemann surface `X`, whose underlying
real bundle is smooth. Then `L` has a smooth section `σ` with finitely many zeros, each positive
(`ε z = false`, the real derivative `D` of the chart reading at `z` satisfies
`‖D - (u ↦ u c)‖ < ‖c‖`) or negative (`ε z = true`, `‖D - (u ↦ conj u c)‖ < ‖c‖`), such that the
Euler class of `L` with its complex orientation, evaluated on the fundamental class of `X`, is the
number of positive zeros minus the number of negative ones. -/
theorem exists_contMDiffSection_complexEulerClass_eq_sum_sign [CompactSpace X]
    [IsManifold 𝓘(ℂ) ∞ X] [ContMDiffVectorBundle ∞ ℂ L 𝓘(ℝ, ℂ)] :
    ∃ (σ : ContMDiffSection 𝓘(ℝ, ℂ) ℂ ∞ L) (hZ : {z | σ z = 0}.Finite) (ε : X → Bool),
      (∀ z, σ z = 0 → ∃ (D : ℂ →L[ℝ] ℂ) (c : ℂ),
        HasFDerivAt (negPointTwistChartReading ℂ z σ) D (chartAt ℂ z z) ∧
          ‖D - (if ε z then Complex.conjCLE.toContinuousLinearMap
            else ContinuousLinearMap.id ℝ ℂ).smulRight c‖ < ‖c‖) ∧
      ((complexHomologicalOrientation X).evalFundamentalClass Complex.finrank_real_complex
          (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id X)
          (complexEulerClass ℂ L (r := 0) (finrank_self ℂ))).down =
        ∑ z ∈ hZ.toFinset, if ε z then -1 else 1 := by
  have : IsManifold 𝓘(ℝ, ℂ) ∞ X := IsManifold.restrictScalars ℝ ‹_›
  obtain ⟨σ, hreg, hZ⟩ := exists_contMDiffSection_regular_finite_zero_of_finrank_eq
    (n := ∞) (X := ℂ) (F := ℂ) (V := L) rfl
  have hσ : Continuous fun z ↦ TotalSpace.mk' ℂ z (σ z) := σ.contMDiff.continuous
  -- At each zero, the sign `ε` of the Jacobian of the chart reading and the matching estimate.
  have hzero : ∀ z, σ z = 0 → ∃ (s : Bool) (D : ℂ →L[ℝ] ℂ) (c : ℂ),
      HasFDerivAt (negPointTwistChartReading ℂ z σ) D (chartAt ℂ z z) ∧
        ‖D - (if s then Complex.conjCLE.toContinuousLinearMap
          else ContinuousLinearMap.id ℝ ℂ).smulRight c‖ < ‖c‖ := fun z hz ↦ by
    obtain ⟨D, hD, hdet⟩ := exists_hasFDerivAt_negPointTwistChartReading_det_ne_zero (hreg z hz)
    rcases hdet.lt_or_gt with h | h
    · obtain ⟨c, hc⟩ := exists_norm_sub_smulRight_conjCLE_lt_of_det_neg h
      exact ⟨true, D, c, hD, hc⟩
    · obtain ⟨c, hc⟩ := exists_norm_sub_smulRight_lt_of_det_pos h
      exact ⟨false, D, c, hD, hc⟩
  choose! ε D c hD hc using hzero
  refine ⟨σ, hZ, ε, fun z hz ↦ ⟨D z, c z, hD z hz, hc z hz⟩, ?_⟩
  rw [complexEulerClass_def,
    VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex _ _ _ hσ _ hZ]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  have hz0 : σ z = 0 := hZ.mem_toFinset.1 hz
  -- The estimate gives the local index `±1`.
  have h := hc z hz0
  cases hε : ε z <;> simp only [hε, Bool.false_eq_true, ite_true, ite_false] at h ⊢
  · exact sectionIndex_eq_one_of_norm_sub_smulRight_lt z hσ hz0 (hD z hz0) h
  · exact sectionIndex_eq_neg_one_of_norm_sub_smulRight_conjCLE_lt z hσ hz0 (hD z hz0) h

end TauCeti
