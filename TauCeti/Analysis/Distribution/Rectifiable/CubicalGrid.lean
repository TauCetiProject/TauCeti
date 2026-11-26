/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Rectifiable.CoordPlane
public import TauCeti.Analysis.Distribution.TestFunction.CubicalGrid
import TauCeti.Algebra.Module.NegOnePowSMul

/-!
# Coordinate boxes and cubical grid chains are integral currents

For an injection `I : Fin k ↪ Fin n`, a point `x ∈ ℝⁿ` and side lengths `r : Fin k → ℝ`, the
oriented current `[[x; I, r]]` of the coordinate box `B = {x + ∑ⱼ sⱼ e_{I j} | 0 ≤ sⱼ ≤ rⱼ}`
(`TauCeti.coordBoxCurrent`) integrates the coefficient `ω_y(e_{I 0}, …, e_{I (k-1)})` of a test
`k`-form over `B` against the Euclidean Hausdorff measure `μHE[k]`
(`TauCeti.coordBoxCurrent_apply_eq_setIntegral`), since the coordinate plane map is an isometry.
So it is the frame current of the multiplicity `1_B` with the constant orthonormal frame
`e_I = (e_{I 0}, …, e_{I (k-1)})` (`TauCeti.coordBoxCurrent_eq_frameCurrent`). The box lies in the
affine plane `x + span e_I`, so this current is integer-rectifiable
(`TauCeti.isIntegerRectifiable_coordBoxCurrent`).

By the cubical boundary formula `TauCeti.coordBoxCurrent_comp_extDerivCLM`, the boundary of a box
with nonnegative sides is an integer combination of boxes of one dimension less, hence again
integer-rectifiable; a box with a negative side is the zero current. So coordinate boxes are
locally integral currents (`TauCeti.isLocallyIntegral_coordBoxCurrent`), and compactly supported
integral currents whenever the box lies in the open set
(`TauCeti.isCompactlySupportedIntegralCurrent_coordBoxCurrent`).

The integral cubical grid chains of side `ε` (`TauCeti.cubicalGridChains`), the integer combinations
of grid cubes onto which the deformation theorem of Federer and Fleming pushes integral currents,
are therefore locally integral currents (`TauCeti.cubicalGridChains_le_locallyIntegralCurrents`).
Their supports are compact, so they are compactly supported integral currents as soon as their
support lies in the open set
(`TauCeti.isCompactlySupportedIntegralCurrent_of_mem_cubicalGridChains`), and always on all of
`ℝⁿ` (`TauCeti.cubicalGridChains_top_le_compactlySupportedIntegralCurrents`).

## Main declarations

* `TauCeti.coordBoxCurrent_apply_eq_setIntegral`, `TauCeti.coordBoxCurrent_eq_frameCurrent`: the
  box current integrates over the box against `μHE[k]`, with multiplicity one and frame `e_I`.
* `TauCeti.isIntegerRectifiable_coordBoxCurrent`, `TauCeti.isLocallyIntegral_coordBoxCurrent`,
  `TauCeti.isCompactlySupportedIntegralCurrent_coordBoxCurrent`: integrality of boxes.
* `TauCeti.isLocallyIntegral_gridCubeCurrent`,
  `TauCeti.cubicalGridChains_le_locallyIntegralCurrents`,
  `TauCeti.isCompactlySupportedIntegralCurrent_of_mem_cubicalGridChains`,
  `TauCeti.cubicalGridChains_top_le_compactlySupportedIntegralCurrents`: integrality of grid
  chains.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.8 (oriented intervals and cubes), §4.1.24 (integral
  currents) and §4.2.6–4.2.9 (the cubical subdivision of `ℝⁿ` and the deformation theorem).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §4 (the deformation theorem).
-/

public section

noncomputable section

open Set TopologicalSpace TestFunction MeasureTheory Distribution WithLp
open scoped Distributions

namespace TauCeti

variable {k n : ℕ}

section CoordBox

/-- The current of a coordinate box integrates the coefficient of a test form on
`e_{I 0}, …, e_{I (k-1)}` over the box, against the Euclidean Hausdorff measure `μHE[k]`. -/
theorem coordBoxCurrent_apply_eq_setIntegral (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (r : Fin k → ℝ) (Ω : Opens (EuclideanSpace ℝ (Fin n)))
    (ω : 𝓓(Ω, EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ)) :
    coordBoxCurrent I x r Ω ω =
      ∫ y in coordPlaneMap I x '' (ofLp ⁻¹' Icc 0 r),
        ω y (fun j ↦ EuclideanSpace.single (I j) 1) ∂μHE[k] := by
  have hf := isometry_coordPlaneMap I x
  -- The coordinate plane map carries Lebesgue measure on `ℝᵏ` to `μHE[k]` on the plane.
  have hμ : MeasurePreserving (coordPlaneMap I x) (volume : Measure (EuclideanSpace ℝ (Fin k)))
      ((μHE[k] : Measure (EuclideanSpace ℝ (Fin n))).restrict (range (coordPlaneMap I x))) :=
    ⟨(coordPlaneMap I x).continuous.measurable, by
      rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hf.map_euclideanHausdorffMeasure]⟩
  have h := hμ.setIntegral_image_emb hf.isClosedEmbedding.measurableEmbedding
    (fun y ↦ ω y fun j ↦ EuclideanSpace.single (I j) 1) (ofLp ⁻¹' Icc 0 r)
  rw [Measure.restrict_restrict (isCompact_coordPlaneMap_image_Icc I x r).isClosed.measurableSet,
    inter_eq_left.2 (image_subset_range _ _)] at h
  rw [h, coordBoxCurrent_apply, ← (PiLp.volume_preserving_toLp (Fin k)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurableEmbedding]
  simp [preimage_preimage]

/-- The indicator function of a coordinate box is locally integrable for `μHE[k]`. -/
theorem locallyIntegrable_indicator_image_coordPlaneMap (I : Fin k ↪ Fin n)
    (x : EuclideanSpace ℝ (Fin n)) (r : Fin k → ℝ) :
    LocallyIntegrable ((coordPlaneMap I x '' (ofLp ⁻¹' Icc 0 r)).indicator
      (1 : EuclideanSpace ℝ (Fin n) → ℝ)) μHE[k] := by
  have h := (locallyIntegrable_indicator_range_coordPlaneMap I x).indicator
    (isCompact_coordPlaneMap_image_Icc I x r).isClosed.measurableSet
  rwa [indicator_indicator, inter_eq_left.2 (image_subset_range _ _)] at h

/-- The current of a coordinate box is the frame current of the box with multiplicity one and the
constant frame `e_{I 0}, …, e_{I (k-1)}`. -/
theorem coordBoxCurrent_eq_frameCurrent (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (r : Fin k → ℝ) (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    coordBoxCurrent I x r Ω =
      frameCurrent ((coordPlaneMap I x '' (ofLp ⁻¹' Icc 0 r)).indicator 1)
        fun _ j ↦ EuclideanSpace.single (I j) 1 := by
  set B := coordPlaneMap I x '' (ofLp ⁻¹' Icc 0 r)
  have hB : MeasurableSet B := (isCompact_coordPlaneMap_image_Icc I x r).isClosed.measurableSet
  have hBi : LocallyIntegrable (B.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ)) μHE[k] :=
    locallyIntegrable_indicator_image_coordPlaneMap I x r
  ext ω
  rw [coordBoxCurrent_apply_eq_setIntegral, frameCurrent_apply
    (τ := fun _ j ↦ EuclideanSpace.single (I j) 1) (hBi.locallyIntegrableOn _)
    measurable_const fun _ _ ↦ EuclideanSpace.orthonormal_single.comp _ I.injective,
    ← integral_indicator hB]
  congr 1
  funext y
  by_cases hy : y ∈ B <;> simp [hy]

/-- **A coordinate box is an integer-rectifiable current**: it is the frame current of the
multiplicity one on the box, which lies in the affine plane `x + span e_I`, with the constant
frame `e_I`. -/
theorem isIntegerRectifiable_coordBoxCurrent (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (r : Fin k → ℝ) (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    IsIntegerRectifiable (coordBoxCurrent I x r Ω) := by
  set B := coordPlaneMap I x '' (ofLp ⁻¹' Icc 0 r)
  have hB : MeasurableSet B := (isCompact_coordPlaneMap_image_Icc I x r).isClosed.measurableSet
  have hcast : (fun y ↦ ((B.indicator (1 : EuclideanSpace ℝ (Fin n) → ℤ) y : ℤ) : ℝ)) =
      B.indicator 1 := by
    funext y
    by_cases hy : y ∈ B <;> simp [hy]
  have hBi : LocallyIntegrable (B.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ)) μHE[k] :=
    locallyIntegrable_indicator_image_coordPlaneMap I x r
  rw [coordBoxCurrent_eq_frameCurrent, ← hcast]
  refine isIntegerRectifiable_frameCurrent_of_sub_mem_span
    (EuclideanSpace.orthonormal_single.comp _ I.injective) x (measurable_one.indicator hB)
    (hcast ▸ hBi.locallyIntegrableOn _) fun y hy ↦ ?_
  obtain ⟨s, -, rfl⟩ := mem_of_indicator_ne_zero hy
  have h0 : coordPlaneMap I x 0 = x := by simp [coordPlaneMap_apply]
  have hs : coordPlaneMap I x s - x = (coordPlaneMap I x).contLinear s := by
    rw [ContinuousAffineMap.coe_contLinear]
    simpa [h0] using ((coordPlaneMap I x).toAffineMap.linear_apply_vsub s 0).symm
  rw [hs]
  exact contLinear_coordPlaneMap_mem_span I x s

/-- **A coordinate box is a locally integral current**: it is integer-rectifiable, and so is its
boundary, an integer combination of boxes of one dimension less. -/
theorem isLocallyIntegral_coordBoxCurrent (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (r : Fin k → ℝ) (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    IsLocallyIntegral (coordBoxCurrent I x r Ω) := by
  cases k with
  | zero => exact isLocallyIntegral_finZero_iff.2 (isIntegerRectifiable_coordBoxCurrent I x r Ω)
  | succ k =>
    refine isLocallyIntegral_succ_iff.2 ⟨isIntegerRectifiable_coordBoxCurrent I x r Ω, ?_⟩
    by_cases hr : 0 ≤ r
    · rw [← mem_integerRectifiableCurrents, coordBoxCurrent_comp_extDerivCLM I x hr]
      refine AddSubgroup.sum_mem _ fun j _ ↦ ?_
      have hsub := sub_mem
        (mem_integerRectifiableCurrents.2 (isIntegerRectifiable_coordBoxCurrent
          (j.succAboveEmb.trans I) (x + EuclideanSpace.single (I j) (r j)) (r ∘ j.succAbove) Ω))
        (mem_integerRectifiableCurrents.2 (isIntegerRectifiable_coordBoxCurrent
          (j.succAboveEmb.trans I) x (r ∘ j.succAbove) Ω))
      exact neg_one_pow_smul_mem hsub _
    · -- A box with a negative side is the zero current.
      simp only [Pi.le_def, Pi.zero_apply, not_forall, not_le] at hr
      obtain ⟨j, hj⟩ := hr
      rw [coordBoxCurrent_eq_zero_of_nonpos I x j hj.le Ω,
        ContinuousLinearMap.zero_comp]
      exact isIntegerRectifiable_zero

/-- **A coordinate box in `Ω` is a compactly supported integral current.** -/
theorem isCompactlySupportedIntegralCurrent_coordBoxCurrent (I : Fin k ↪ Fin n)
    (x : EuclideanSpace ℝ (Fin n)) (r : Fin k → ℝ) {Ω : Opens (EuclideanSpace ℝ (Fin n))}
    (hΩ : coordPlaneMap I x '' (ofLp ⁻¹' Icc 0 r) ⊆ Ω) :
    IsCompactlySupportedIntegralCurrent (coordBoxCurrent I x r Ω) :=
  (isLocallyIntegral_coordBoxCurrent I x r Ω).isCompactlySupportedIntegralCurrent
    (isCompact_dsupport_coordBoxCurrent I x r Ω)
    ((dsupport_coordBoxCurrent_subset I x r Ω).trans hΩ)

end CoordBox

section Grid

/-- A grid cube is a locally integral current. -/
theorem isLocallyIntegral_gridCubeCurrent (ε : ℝ) (I : Fin k ↪ Fin n) (z : Fin n → ℤ)
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) : IsLocallyIntegral (gridCubeCurrent ε I z Ω) := by
  rw [gridCubeCurrent_def]
  exact isLocallyIntegral_coordBoxCurrent _ _ _ Ω

/-- **Grid chains are locally integral currents.** -/
theorem cubicalGridChains_le_locallyIntegralCurrents (ε : ℝ)
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) (k : ℕ) :
    cubicalGridChains ε Ω k ≤ locallyIntegralCurrents Ω k := fun T hT ↦ by
  obtain ⟨a, rfl⟩ := mem_cubicalGridChains_iff.1 hT
  exact sum_mem fun c _ ↦ zsmul_mem
    (mem_locallyIntegralCurrents.2 (isLocallyIntegral_gridCubeCurrent ε c.1 c.2 Ω)) _

/-- A grid chain is a locally integral current. -/
theorem isLocallyIntegral_of_mem_cubicalGridChains {ε : ℝ} {Ω : Opens (EuclideanSpace ℝ (Fin n))}
    {T : 𝓓(Ω, EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ}
    (hT : T ∈ cubicalGridChains ε Ω k) : IsLocallyIntegral T :=
  mem_locallyIntegralCurrents.1 (cubicalGridChains_le_locallyIntegralCurrents ε Ω k hT)

/-- **A grid chain supported in `Ω` is a compactly supported integral current.** -/
theorem isCompactlySupportedIntegralCurrent_of_mem_cubicalGridChains {ε : ℝ}
    {Ω : Opens (EuclideanSpace ℝ (Fin n))}
    {T : 𝓓(Ω, EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ}
    (hT : T ∈ cubicalGridChains ε Ω k) (hΩ : dsupport (T : _ → ℝ) ⊆ Ω) :
    IsCompactlySupportedIntegralCurrent T :=
  (isLocallyIntegral_of_mem_cubicalGridChains hT).isCompactlySupportedIntegralCurrent
    (isCompact_dsupport_of_mem_cubicalGridChains hT) hΩ

/-- **The grid chains of `ℝⁿ` are compactly supported integral currents.** -/
theorem cubicalGridChains_top_le_compactlySupportedIntegralCurrents (ε : ℝ) (k : ℕ) :
    cubicalGridChains ε (⊤ : Opens (EuclideanSpace ℝ (Fin n))) k ≤
      compactlySupportedIntegralCurrents ⊤ k := fun _ hT ↦
  mem_compactlySupportedIntegralCurrents.2
    (isCompactlySupportedIntegralCurrent_of_mem_cubicalGridChains hT (by simp))

end Grid

end TauCeti
