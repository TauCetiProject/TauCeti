/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Determinant
public import TauCeti.Analysis.Normed.Operator.FiniteDimensional
public import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Inscribed ellipsoids of maximal volume

An ellipsoid centred at `0` in a finite-dimensional real inner product space `E` is the image
`T(B)` of the closed unit ball `B` under a linear automorphism `T` of `E`. The volume of `T(B)` is
`|det T|` times that of `B` (`MeasureTheory.Measure.addHaar_image_continuousLinearMap`), so
among the ellipsoids centred at `0` contained in a set `K` the ones of maximal volume are those
maximizing `|det T|`. This file proves that for a compact neighbourhood `K` of `0` such a maximizer
exists and is invertible, and that the linear change of variables by its inverse moves `K` into
**John's position**: the unit ball itself is then an inscribed ellipsoid of maximal volume among the
ellipsoids centred at `0`. Over `ℝ`, for a symmetric convex body `K` this is the John ellipsoid of
`K`, and this is the position in which John's theorem describes the contact points of `K` with the
unit sphere. In a finite-dimensional complex inner product space only complex ellipsoids, the
`ℂ`-linear images `T(B)`, are compared; their real volume factor is `‖det T‖ ^ 2`, so `B` is the
complex ellipsoid of maximal volume in `K`. It is the John ellipsoid of a symmetric convex body `K`
when `K` is moreover circled. In a general finite-dimensional real or complex normed space, `B` has
maximal volume among the linear images of the unit ball contained in `K`.

Existence of the maximizer uses no inner product, so it is stated for linear images of the unit
ball of any finite-dimensional normed space over a complete field: the linear maps sending the unit
ball into a compact set form a compact set (`IsCompact.isCompact_setOfPred_mapsTo`), on which the
continuous function `‖det T‖` attains its maximum, and a neighbourhood of `0` contains a nonzero
multiple of the unit ball. These images are ellipsoids when the norm comes from an inner product.
Over `ℝ` or `ℂ` the unit ball of any finite-dimensional normed space is itself in John's position,
because a linear map sending it into itself has operator norm at most `1`, hence determinant of
norm at most `1` (`ContinuousLinearMap.norm_det_le_opNorm_pow`).

## Main definitions

* `TauCeti.IsJohnPosition 𝕜 K`: the closed unit ball is contained in `K`, and every linear map
  sending the unit ball into `K` has determinant of norm at most `1`.

## Main results

* `IsCompact.exists_isMaxOn_norm_det`: a compact neighbourhood `K` of `0` contains an image `T(B)`
  of the unit ball under a linear equivalence `T` maximizing `‖det T‖` among all linear maps
  sending `B` into `K`.
* `ContinuousLinearEquiv.isJohnPosition_preimage_iff`: the preimage `T⁻¹(K)` is in John's position
  exactly when `T(B)` is contained in `K` and `‖det T‖` is maximal among the linear images of `B`
  contained in `K`.
* `IsCompact.exists_isJohnPosition_preimage`: every compact neighbourhood of `0` is moved into
  John's position by a linear equivalence.
* `TauCeti.isJohnPosition_closedBall`: over an `RCLike` field, the unit ball of a
  finite-dimensional normed space is in John's position.
* `TauCeti.IsJohnPosition.addHaar_image_le`: over `ℝ`, in John's position no linear image of the
  unit ball contained in `K` has larger volume than the unit ball.

## References

* K. Ball, *An Elementary Introduction to Modern Convex Geometry*, Lecture 3.
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §13.1.
-/

public section

open Set Metric Module Filter Topology

namespace TauCeti

section Normed

variable (𝕜 : Type*) {E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- A set `K` is in **John's position** if the closed unit ball `B` is contained in `K` and every
linear map sending `B` into `K` has determinant of norm at most `1`, the determinant of the
identity. In a real inner product space this says that `B` has maximal volume among the ellipsoids
centred at `0` contained in `K`; for a symmetric convex body `K` this makes `B` the John ellipsoid
of `K`. In a complex inner product space it says that `B` has maximal volume among the complex
ellipsoids, the `ℂ`-linear images of `B`, contained in `K`; this is the John ellipsoid when `K` is
moreover circled. In a general real or complex normed space it says that `B` has maximal volume
among the linear images of `B` contained in `K`. -/
structure IsJohnPosition (K : Set E) : Prop where
  /-- The closed unit ball is contained in `K`. -/
  closedBall_subset : closedBall (0 : E) 1 ⊆ K
  /-- Every linear map sending the closed unit ball into `K` has determinant of norm at most
  `1`. -/
  norm_det_le : ∀ S : E →L[𝕜] E, MapsTo S (closedBall 0 1) K → ‖S.det‖ ≤ 1

variable {𝕜}

/-- The preimage of `K` under a linear equivalence `T` is in John's position exactly when the
image of the unit ball under `T` is contained in `K` and `‖det T‖` is maximal among the linear
maps sending the unit ball into `K`. -/
theorem _root_.ContinuousLinearEquiv.isJohnPosition_preimage_iff {K : Set E} (T : E ≃L[𝕜] E) :
    IsJohnPosition 𝕜 (T ⁻¹' K) ↔ MapsTo T (closedBall 0 1) K ∧
      IsMaxOn (fun S : E →L[𝕜] E ↦ ‖S.det‖) {S | MapsTo S (closedBall 0 1) K}
        (T : E →L[𝕜] E) := by
  have hcomp (S : E →L[𝕜] E) :
      ‖((T : E →L[𝕜] E) ∘L S).det‖ = ‖(T : E →L[𝕜] E).det‖ * ‖S.det‖ := by
    rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
      norm_mul]
  have hpos : 0 < ‖(T : E →L[𝕜] E).det‖ := norm_pos_iff.2 <| by
    simpa [ContinuousLinearMap.det] using (T.toLinearEquiv.isUnit_det').ne_zero
  constructor
  · -- `T⁻¹ ∘ S` sends the unit ball into `T⁻¹(K)` whenever `S` sends it into `K`.
    rintro ⟨hB, hdet⟩
    refine ⟨fun x hx ↦ hB hx, isMaxOn_iff.2 fun S hS ↦ ?_⟩
    have h := hdet ((T.symm : E →L[𝕜] E) ∘L S) fun x hx ↦ by simpa using hS hx
    have hS' : (T : E →L[𝕜] E) ∘L ((T.symm : E →L[𝕜] E) ∘L S) = S := by ext; simp
    calc ‖S.det‖ = ‖(T : E →L[𝕜] E).det‖ * ‖((T.symm : E →L[𝕜] E) ∘L S).det‖ := by
          rw [← hcomp, hS']
      _ ≤ ‖(T : E →L[𝕜] E).det‖ := mul_le_of_le_one_right hpos.le h
  · -- `T ∘ S` sends the unit ball into `K` whenever `S` sends it into `T⁻¹(K)`.
    rintro ⟨hT, hmax⟩
    refine ⟨fun x hx ↦ hT hx, fun S hS ↦ ?_⟩
    have h := isMaxOn_iff.1 hmax ((T : E →L[𝕜] E) ∘L S) fun x hx ↦ hS hx
    rw [hcomp] at h
    exact (mul_le_iff_le_one_right hpos).1 h

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

/-- **Existence of an inscribed ellipsoid of maximal volume.** A compact neighbourhood `K` of `0`
in a finite-dimensional normed space over a complete field contains the image of the closed unit
ball under a linear equivalence `T` whose determinant has maximal norm among all linear maps
sending the unit ball into `K`. In an inner product space, `T(B)` has maximal volume among the
`𝕜`-linear images of the unit ball contained in `K`: the ellipsoids centred at `0` when `𝕜 = ℝ`,
and the complex ellipsoids when `𝕜 = ℂ`. -/
theorem _root_.IsCompact.exists_isMaxOn_norm_det {K : Set E} (hK : IsCompact K)
    (hK0 : K ∈ 𝓝 (0 : E)) :
    ∃ T : E ≃L[𝕜] E, MapsTo T (closedBall 0 1) K ∧
      IsMaxOn (fun S : E →L[𝕜] E ↦ ‖S.det‖) {S | MapsTo S (closedBall 0 1) K}
        (T : E →L[𝕜] E) := by
  -- A small nonzero multiple of the identity sends the unit ball into `K`.
  obtain ⟨r, hr, hrK⟩ := Metric.mem_nhds_iff.1 hK0
  obtain ⟨a, ha0, har⟩ := NormedField.exists_norm_lt 𝕜 hr
  have ha : a • ContinuousLinearMap.id 𝕜 E ∈ {S : E →L[𝕜] E | MapsTo S (closedBall 0 1) K} := by
    intro x hx
    apply hrK
    rw [mem_closedBall_zero_iff] at hx
    rw [mem_ball_zero_iff]
    simpa [norm_smul] using (mul_le_of_le_one_right ha0.le hx).trans_lt har
  obtain ⟨T, hT, hmax⟩ :=
    (hK.isCompact_setOfPred_mapsTo (𝕜 := 𝕜) (closedBall_mem_nhds 0 one_pos)).exists_isMaxOn ⟨_, ha⟩
      ContinuousLinearMap.continuous_det.norm.continuousOn
  -- The maximum is at least `‖a‖ ^ dim E > 0`, so the maximizer is invertible.
  have hdet : T.det ≠ 0 := by
    intro h0
    have h := isMaxOn_iff.1 hmax _ ha
    rw [h0, norm_zero] at h
    have : (0 : ℝ) < ‖(a • ContinuousLinearMap.id 𝕜 E).det‖ := by
      simp [ContinuousLinearMap.det, LinearMap.det_smul, norm_pos_iff.1 ha0]
    exact this.not_ge h
  refine ⟨T.toContinuousLinearEquivOfDetNeZero hdet, fun x hx ↦ by simpa using hT hx, ?_⟩
  rwa [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]

/-- **John's position.** Every compact neighbourhood `K` of `0` in a finite-dimensional normed
space over a complete field has a preimage `T⁻¹(K)` under some linear equivalence `T` that is in
John's position. -/
theorem _root_.IsCompact.exists_isJohnPosition_preimage {K : Set E} (hK : IsCompact K)
    (hK0 : K ∈ 𝓝 (0 : E)) : ∃ T : E ≃L[𝕜] E, IsJohnPosition 𝕜 (T ⁻¹' K) := by
  obtain ⟨T, hT, hmax⟩ := hK.exists_isMaxOn_norm_det (𝕜 := 𝕜) hK0
  exact ⟨T, T.isJohnPosition_preimage_iff.2 ⟨hT, hmax⟩⟩

end Normed

section RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Over an `RCLike` field, the closed unit ball of a finite-dimensional normed space is in John's
position. -/
theorem isJohnPosition_closedBall : IsJohnPosition 𝕜 (closedBall (0 : E) 1) := by
  -- A linear map sending the unit ball into itself has operator norm at most `1`, hence
  -- determinant of norm at most `1`.
  refine ⟨subset_rfl, fun S hS ↦ ?_⟩
  have h : ‖S‖ ≤ 1 := ContinuousLinearMap.opNorm_le_of_unit_norm zero_le_one fun x hx ↦
    mem_closedBall_zero_iff.1 <| hS <| mem_closedBall_zero_iff.2 hx.le
  simpa using S.norm_det_le_opNorm_pow.trans (pow_le_one₀ (norm_nonneg S) h)

end RCLike

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure]

/-- Over `ℝ`, if `K` is in John's position then no linear image of the closed unit ball contained
in `K` has larger volume than the closed unit ball, for any additive Haar measure. -/
theorem IsJohnPosition.addHaar_image_le {K : Set E} (hK : IsJohnPosition ℝ K) {S : E →L[ℝ] E}
    (hS : MapsTo S (closedBall 0 1) K) : μ (S '' closedBall 0 1) ≤ μ (closedBall 0 1) := by
  rw [MeasureTheory.Measure.addHaar_image_continuousLinearMap]
  refine mul_le_of_le_one_left zero_le ?_
  rw [ENNReal.ofReal_le_one]
  exact hK.norm_det_le S hS

end Real

end TauCeti
