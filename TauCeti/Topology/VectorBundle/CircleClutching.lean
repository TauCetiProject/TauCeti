/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Moebius
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Trivialization
import TauCeti.Topology.VectorBundle.Coordinates
import TauCeti.Topology.VectorBundle.Orientation.Atlas

/-!
# Vector bundles over the circle clutched by a linear automorphism

For a continuous linear automorphism `A` of a real normed space `F`, the vector bundle
`TauCeti.circleClutchingCore A` over the unit circle is glued from the trivial bundles with fibre
`F` over the two charts of the Möbius line bundle, the circle minus `1` (index `false`) and the
circle minus `-1` (index `true`). The charts overlap in the open upper and lower half-circles; the
transition from the chart `false` to the chart `true` is the identity on the upper half-circle and
`A` on the lower one. This is the bundle over a closed orbit whose fibre comes back to itself
through `A` after one turn, the shape of the normal bundles of the critical circles of a
Morse–Bott function on a mapping torus.

Its orientation local system is read off from `A`:

* The bundle is orientable exactly when `det A > 0`
  (`TauCeti.nonempty_vectorBundleOrientation_circleClutchingCore_iff`): an orientation reads as a
  single orientation of `F` in each chart, and these must agree on the upper half-circle and
  differ by `A` on the lower one.
* Hence the orientation character of the circle, the sign of transport once around it, is the
  sign of `det A` (`TauCeti.coe_freeLoopOrientationCharacter_circleClutchingCore_id`). Read
  through the two charts, transport around a loop from the upper to the lower half-circle and
  back applies `A`, and the general computation of transport in trivializations gives the same
  sign (`TauCeti.coe_orientationCharacter_circleClutchingCore_fromPath_trans`).

The sign of `det A`, not the sign of any larger transition, is what the bundle sees. For
`A = diag(1, -1)` on `ℝ²` the character is `-1`, while for `A = diag(1, -1, -1)` on `ℝ³`, which
adds a line bundle of transition `-1`, it is `1`. On `F = ℝ` the Möbius line bundle
(`TauCeti.moebiusCore`) has the transitions of the clutching by `-1`, and it is not orientable
(`TauCeti.isEmpty_vectorBundleOrientation_moebiusCore`).

## Main definitions

* `TauCeti.circleClutchingCore A`: the vector bundle over the circle clutched by `A`.

## Main results

* `TauCeti.nonempty_vectorBundleOrientation_circleClutchingCore_iff`: the bundle is orientable
  exactly when `det A > 0`.
* `TauCeti.coe_freeLoopOrientationCharacter_circleClutchingCore_id`: its orientation character
  around the circle is the sign of `det A`.
* `TauCeti.coe_orientationCharacter_circleClutchingCore_fromPath_trans`: the same for a based
  loop through the two charts.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §2 and §12.
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §6.2 (orientation local systems of Morse–Bott negative
  bundles).
-/

public section

noncomputable section

open Bundle Filter Module Set
open scoped Topology Real

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The **vector bundle over the circle clutched by `A`**, glued from the trivial bundles with
fibre `F` over the circle minus `1` (chart `false`) and minus `-1` (chart `true`). The transition
from the chart `false` to the chart `true` is the identity on the upper half-circle and `A` on the
lower one; the reverse transition is the identity and `A⁻¹`. -/
def circleClutchingCore (A : F ≃L[ℝ] F) : VectorBundleCore ℝ Circle F Bool where
  baseSet := moebiusBaseSet
  isOpen_baseSet i := by simpa only [moebiusCore_baseSet] using moebiusCore.isOpen_baseSet i
  indexAt z := decide ((z : ℂ) = 1)
  mem_baseSet_at z := by
    by_cases h : (z : ℂ) = 1
    · -- Then `z` lies in the chart `true`, the circle minus `-1`.
      simp only [h, decide_true, mem_moebiusBaseSet, ↓reduceIte]
      norm_num
    · simp [h]
  coordChange i j z := if i = j ∨ 0 < (z : ℂ).im then ContinuousLinearMap.id ℝ F
    else if i then (A.symm : F →L[ℝ] F) else (A : F →L[ℝ] F)
  coordChange_self i _ _ v := by simp
  continuousOn_coordChange i j := by
    by_cases hij : i = j
    · simpa [hij] using continuousOn_const
    · intro z hz
      have hc : Continuous fun w : Circle ↦ (w : ℂ).im :=
        Complex.continuous_im.comp continuous_subtypeVal
      refine ContinuousAt.continuousWithinAt ?_
      -- Off the real axis the transition is locally constant.
      rcases (im_ne_zero_of_mem_moebiusBaseSet hij hz.1 hz.2).lt_or_gt with h | h
      · refine continuousAt_const.congr
          (f := fun _ ↦ if i then (A.symm : F →L[ℝ] F) else (A : F →L[ℝ] F)) ?_
        filter_upwards [hc.continuousAt.eventually (gt_mem_nhds h)] with w hw
        simp [hij, hw.not_gt]
      · refine continuousAt_const.congr (f := fun _ ↦ ContinuousLinearMap.id ℝ F) ?_
        filter_upwards [hc.continuousAt.eventually (lt_mem_nhds h)] with w hw
        simp [hw]
  coordChange_comp i j k z _ v := by
    by_cases h : 0 < (z : ℂ).im
    · simp [h]
    · cases i <;> cases j <;> cases k <;> simp [h]

variable (A : F ≃L[ℝ] F)

/-- The chart domains of the clutched bundle are those of the Möbius line bundle. -/
theorem circleClutchingCore_baseSet (i : Bool) :
    (circleClutchingCore A).baseSet i = moebiusBaseSet i :=
  (rfl)

/-- On the upper half-circle the transitions of the clutched bundle are the identity. -/
theorem circleClutchingCore_coordChange_of_pos (i j : Bool) {z : Circle} (hz : 0 < (z : ℂ).im) :
    (circleClutchingCore A).coordChange i j z = ContinuousLinearMap.id ℝ F := by
  simp [circleClutchingCore, hz]

/-- On the lower half-circle the transition of the clutched bundle from the chart `false` to the
chart `true` is `A`. -/
theorem circleClutchingCore_coordChange_false_true_of_neg {z : Circle} (hz : (z : ℂ).im < 0) :
    (circleClutchingCore A).coordChange false true z = A := by
  simp [circleClutchingCore, hz.not_gt]

/-- On the lower half-circle the transition of the clutched bundle from the chart `true` to the
chart `false` is `A⁻¹`. -/
theorem circleClutchingCore_coordChange_true_false_of_neg {z : Circle} (hz : (z : ℂ).im < 0) :
    (circleClutchingCore A).coordChange true false z = A.symm := by
  simp [circleClutchingCore, hz.not_gt]

variable [FiniteDimensional ℝ F] {ι : Type*} [Fintype ι] (hι : Fintype.card ι = finrank ℝ F)

include hι in
/-- **The clutched bundle is orientable exactly when `det A > 0`.** -/
theorem nonempty_vectorBundleOrientation_circleClutchingCore_iff :
    Nonempty (VectorBundleOrientation F (circleClutchingCore A).Fiber ι) ↔
      0 < (A : F →L[ℝ] F).det := by
  let Z := circleClutchingCore A
  have hA : (A : F →L[ℝ] F).det ≠ 0 := by
    have := (LinearEquiv.det A.toLinearEquiv).ne_zero
    rwa [LinearEquiv.coe_det] at this
  refine ⟨fun ⟨o⟩ ↦ ?_, fun h ↦ ?_⟩
  · -- If `det A < 0`, the transition from the chart `false` to the chart `true` has positive
    -- determinant at `i` and negative determinant at `-i`.
    refine (lt_or_gt_of_ne hA).resolve_left fun hneg ↦ ?_
    let p : Circle := Circle.exp (π / 2)
    let q : Circle := Circle.exp (-(π / 2))
    have hp : 0 < (p : ℂ).im := by simp [p, Circle.coe_exp]
    have hq : (q : ℂ).im < 0 := by simp [q, Circle.coe_exp]
    have : MemTrivializationAtlas (Z.localTriv false) := ⟨⟨false, rfl⟩⟩
    have : MemTrivializationAtlas (Z.localTriv true) := ⟨⟨true, rfl⟩⟩
    have hdet {z : Circle} (hz : (z : ℂ).im ≠ 0) :
        LinearMap.det (((Z.localTriv false).coordChangeL ℝ (Z.localTriv true) z).toLinearEquiv :
          F →ₗ[ℝ] F) = (Z.coordChange false true z).det := by
      rw [← Z.localTriv_coordChangeL ⟨mem_moebiusBaseSet_of_im_ne_zero hz false,
        mem_moebiusBaseSet_of_im_ne_zero hz true⟩]
      rfl
    refine (VectorBundleOrientation.isEmpty_of_det_coordChangeL_pos_of_neg hι
      (Z.localTriv false) (Z.localTriv true) (isPreconnected_moebiusBaseSet false)
      (isPreconnected_moebiusBaseSet true) le_rfl le_rfl
      (mem_moebiusBaseSet_of_im_ne_zero hp.ne' false) (mem_moebiusBaseSet_of_im_ne_zero hp.ne' true)
      (mem_moebiusBaseSet_of_im_ne_zero hq.ne false) (mem_moebiusBaseSet_of_im_ne_zero hq.ne true)
      ?_ ?_).false o
    · rw [hdet hp.ne', circleClutchingCore_coordChange_of_pos A _ _ hp]
      simp [ContinuousLinearMap.det]
    · rwa [hdet hq.ne, circleClutchingCore_coordChange_false_true_of_neg A hq]
  · -- If `det A > 0`, every transition has positive determinant.
    classical
    refine ⟨Z.orientationOfPositiveAtlas
      ((Module.finBasisOfFinrankEq ℝ F hι.symm).reindex (Fintype.equivFin ι).symm).orientation hι
      (S := univ) (fun z ↦ ⟨Z.indexAt z, mem_univ _, Z.mem_baseSet_at z⟩) ?_⟩
    rintro i - j - z -
    by_cases hz : i = j ∨ 0 < (z : ℂ).im
    · simp [Z, circleClutchingCore, hz, ContinuousLinearMap.det]
    · simp only [Z, circleClutchingCore, hz, ↓reduceIte]
      split_ifs
      · rw [ContinuousLinearEquiv.det_coe_symm]
        exact inv_pos.2 h
      · exact h

/-- **The orientation character of the clutched bundle around the circle is the sign of
`det A`.** Transport once around the circle preserves orientations of the fibres exactly when
`det A > 0`, and reverses them exactly when `det A < 0`. -/
theorem coe_freeLoopOrientationCharacter_circleClutchingCore_id :
    (VectorBundleOrientationCover.freeLoopOrientationCharacter F (circleClutchingCore A).Fiber hι
      (ContinuousMap.id Circle) : ℤ) = SignType.sign (A : F →L[ℝ] F).det := by
  -- The character of the identity loop is `1` exactly when the bundle is orientable.
  have key : VectorBundleOrientationCover.freeLoopOrientationCharacter F
      (circleClutchingCore A).Fiber hι (ContinuousMap.id Circle) = 1 ↔
        0 < (A : F →L[ℝ] F).det := by
    rw [VectorBundleOrientationCover.freeLoopOrientationCharacter_eq_one_iff,
      ← nonempty_vectorBundleOrientation_circleClutchingCore_iff A hι,
      VectorBundleOrientation.nonempty_iff_exists_section hι]
    exact ⟨fun ⟨s, hs⟩ ↦ ⟨s, s.continuous, hs⟩, fun ⟨s, hs, hs'⟩ ↦ ⟨⟨s, hs⟩, hs'⟩⟩
  have hA : (A : F →L[ℝ] F).det ≠ 0 := by
    have := (LinearEquiv.det A.toLinearEquiv).ne_zero
    rwa [LinearEquiv.coe_det] at this
  rcases Int.units_eq_one_or (VectorBundleOrientationCover.freeLoopOrientationCharacter F
    (circleClutchingCore A).Fiber hι (ContinuousMap.id Circle)) with h | h <;> rw [h]
  · rw [sign_pos (key.1 h)]
    rfl
  · have hneg : (A : F →L[ℝ] F).det < 0 :=
      (lt_or_gt_of_ne hA).resolve_right fun hpos ↦ absurd ((key.2 hpos).symm.trans h) (by decide)
    rw [sign_neg hneg]
    rfl

/-- **Transport around the circle through the two charts is `A`.** For a loop at a point `p` of
the upper half-circle that runs along a path `γ` in the circle minus `1` to a point `q` of the
lower half-circle and back along a path `γ'` in the circle minus `-1`, the orientation character
is the sign of `det A`. -/
theorem coe_orientationCharacter_circleClutchingCore_fromPath_trans {p q : Circle}
    (hp : 0 < (p : ℂ).im) (hq : (q : ℂ).im < 0) (γ : Path p q) (γ' : Path q p)
    (hγ : ∀ t, γ t ∈ moebiusBaseSet false) (hγ' : ∀ t, γ' t ∈ moebiusBaseSet true) :
    (VectorBundleOrientationCover.orientationCharacter F (circleClutchingCore A).Fiber hι p
      (FundamentalGroup.fromPath (.mk (γ.trans γ'))) : ℤ) =
        SignType.sign (A : F →L[ℝ] F).det := by
  let Z := circleClutchingCore A
  have : MemTrivializationAtlas (Z.localTriv false) := ⟨⟨false, rfl⟩⟩
  have : MemTrivializationAtlas (Z.localTriv true) := ⟨⟨true, rfl⟩⟩
  rw [VectorBundleOrientationCover.coe_orientationCharacter_fromPath_trans hι (Z.localTriv false)
    (Z.localTriv true) γ γ' hγ hγ']
  -- The composite transition is `A` at `q` followed by the identity at `p`.
  have hq' : ((Z.localTriv false).coordChangeL ℝ (Z.localTriv true) q : F →L[ℝ] F) = A := by
    rw [Z.localTriv_coordChangeL ⟨mem_moebiusBaseSet_of_im_ne_zero hq.ne false,
      mem_moebiusBaseSet_of_im_ne_zero hq.ne true⟩,
      circleClutchingCore_coordChange_false_true_of_neg A hq]
  have hp' : ((Z.localTriv true).coordChangeL ℝ (Z.localTriv false) p : F →L[ℝ] F) =
      ContinuousLinearMap.id ℝ F := by
    rw [Z.localTriv_coordChangeL ⟨mem_moebiusBaseSet_of_im_ne_zero hp.ne' true,
      mem_moebiusBaseSet_of_im_ne_zero hp.ne' false⟩,
      circleClutchingCore_coordChange_of_pos A _ _ hp]
  have hM : ((((Z.localTriv false).coordChangeL ℝ (Z.localTriv true) q).trans
      ((Z.localTriv true).coordChangeL ℝ (Z.localTriv false) p)).toLinearEquiv : F →ₗ[ℝ] F) =
        (A : F →L[ℝ] F) := by
    ext v
    exact (DFunLike.congr_fun hp' _).trans (DFunLike.congr_fun hq' v)
  rw [hM]

/-- The **rank-two clutching by `diag(1, -1)`** is not orientable: its orientation character is
`-1`. -/
example :
    (VectorBundleOrientationCover.freeLoopOrientationCharacter (Fin 2 → ℝ)
      (circleClutchingCore (LinearMap.equivOfDetNeZero (Matrix.toLin' (Matrix.diagonal ![1, -1]))
        (by simp [LinearMap.det_toLin', Fin.prod_univ_succ])).toContinuousLinearEquiv).Fiber
      (ι := Fin 2) (by simp) (ContinuousMap.id Circle) : ℤ) = -1 := by
  rw [coe_freeLoopOrientationCharacter_circleClutchingCore_id]
  simp [ContinuousLinearMap.det, LinearMap.det_toLin', Fin.prod_univ_succ]

/-- The **rank-three clutching by `diag(1, -1, -1)`** is orientable: its orientation character is
`1`. -/
example :
    (VectorBundleOrientationCover.freeLoopOrientationCharacter (Fin 3 → ℝ)
      (circleClutchingCore (LinearMap.equivOfDetNeZero
        (Matrix.toLin' (Matrix.diagonal ![1, -1, -1]))
        (by simp [LinearMap.det_toLin', Fin.prod_univ_succ])).toContinuousLinearEquiv).Fiber
      (ι := Fin 3) (by simp) (ContinuousMap.id Circle) : ℤ) = 1 := by
  rw [coe_freeLoopOrientationCharacter_circleClutchingCore_id]
  simp [ContinuousLinearMap.det, LinearMap.det_toLin', Fin.prod_univ_succ]

end TauCeti
