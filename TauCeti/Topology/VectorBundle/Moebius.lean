/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import TauCeti.Analysis.Complex.Circle
public import TauCeti.Topology.VectorBundle.Orientation.Basic

/-!
# The Möbius line bundle over the circle

The Möbius line bundle `moebiusCore` is the real line bundle over the unit circle `Circle` glued
from the trivial lines over the two charts `{z ≠ 1}` (index `false`) and `{z ≠ -1}` (index `true`).
These charts meet in the open upper and lower half-circles, and the transition function is `1` on
the upper half-circle and `-1` on the lower one (`TauCeti.moebiusSign`).

Its transition functions are isometries of `ℝ`, so the norm of `ℝ` on its fibres is continuous on
the total space (`TauCeti.continuous_norm_moebiusCore`): it is a line bundle with a continuous fibre
norm, to which the Thom isomorphism of a line bundle applies. Each chart domain is connected, so an
orientation reads as one orientation of `ℝ` in each chart; the two readings agree on the upper and
disagree on the lower half-circle, so the Möbius line bundle is not orientable
(`TauCeti.isEmpty_vectorBundleOrientation_moebiusCore`). Its Thom pair is computed in
`TauCeti.Topology.VectorBundle.Thom.Moebius`.

## Main definitions

* `TauCeti.moebiusCore`: the Möbius line bundle over the circle.

## Main results

* `TauCeti.continuous_norm_moebiusCore`: the fibre norm is continuous on the total space.
* `TauCeti.isEmpty_vectorBundleOrientation_moebiusCore`: the Möbius line bundle is not orientable.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §2 (the Möbius line bundle).
-/

public section

noncomputable section

open Bundle Filter Module Set
open scoped Topology Real

namespace TauCeti

/-- The transition function of the Möbius line bundle: `1` on the upper half-circle and `-1`
elsewhere. Only its values on the two open half-circles, where the charts overlap, matter. -/
def moebiusSign (z : Circle) : ℝ :=
  if 0 < (z : ℂ).im then 1 else -1

theorem moebiusSign_of_pos {z : Circle} (hz : 0 < (z : ℂ).im) : moebiusSign z = 1 := by
  simp [moebiusSign, hz]

theorem moebiusSign_of_neg {z : Circle} (hz : (z : ℂ).im < 0) : moebiusSign z = -1 := by
  simp [moebiusSign, hz.not_gt]

@[simp]
theorem moebiusSign_mul_self (z : Circle) : moebiusSign z * moebiusSign z = 1 := by
  unfold moebiusSign
  split_ifs <;> norm_num

/-- The transition function is locally constant off the real axis. -/
theorem continuousAt_moebiusSign {z : Circle} (hz : (z : ℂ).im ≠ 0) :
    ContinuousAt moebiusSign z := by
  have hc : Continuous fun w : Circle ↦ (w : ℂ).im :=
    Complex.continuous_im.comp continuous_subtypeVal
  rcases hz.lt_or_gt with h | h
  · refine continuousAt_const.congr (f := fun _ ↦ (-1 : ℝ)) ?_
    filter_upwards [hc.continuousAt.eventually (gt_mem_nhds h)] with w hw
    exact (moebiusSign_of_neg hw).symm
  · refine continuousAt_const.congr (f := fun _ ↦ (1 : ℝ)) ?_
    filter_upwards [hc.continuousAt.eventually (lt_mem_nhds h)] with w hw
    exact (moebiusSign_of_pos hw).symm

/-- The chart domains of the Möbius line bundle: the circle minus `1` for `false`, minus `-1` for
`true`. -/
def moebiusBaseSet (i : Bool) : Set Circle :=
  {z | (z : ℂ) ≠ if i then -1 else 1}

/-- The chart `i` of the Möbius line bundle is the circle minus `-1` for `true` and minus `1` for
`false`. -/
@[simp]
theorem mem_moebiusBaseSet {i : Bool} {z : Circle} :
    z ∈ moebiusBaseSet i ↔ (z : ℂ) ≠ if i then -1 else 1 :=
  Iff.rfl

/-- Two different charts of the Möbius line bundle overlap off the real axis. -/
theorem im_ne_zero_of_mem_moebiusBaseSet {i j : Bool} (hij : i ≠ j) {z : Circle}
    (hi : z ∈ moebiusBaseSet i) (hj : z ∈ moebiusBaseSet j) : (z : ℂ).im ≠ 0 := fun h ↦ by
  rcases (Circle.im_coe_eq_zero_iff z).1 h with rfl | rfl <;> cases i <;> cases j <;> simp_all

/-- The Möbius line bundle over the circle, glued from the trivial lines over the circle minus `1`
(chart `false`) and minus `-1` (chart `true`) by the transition `TauCeti.moebiusSign`: the
identity on the upper half-circle and `-1` on the lower one. -/
def moebiusCore : VectorBundleCore ℝ Circle ℝ Bool where
  baseSet := moebiusBaseSet
  isOpen_baseSet i := isOpen_ne_fun continuous_subtypeVal continuous_const
  indexAt z := decide ((z : ℂ) = 1)
  mem_baseSet_at z := by
    by_cases h : (z : ℂ) = 1
    · -- Then `z` lies in the chart `true`, the circle minus `-1`.
      simp only [h, decide_true, mem_moebiusBaseSet, ↓reduceIte]
      norm_num
    · simp [h]
  coordChange i j z := if i = j then ContinuousLinearMap.id ℝ ℝ else
    moebiusSign z • ContinuousLinearMap.id ℝ ℝ
  coordChange_self i _ _ v := by simp
  continuousOn_coordChange i j := by
    by_cases hij : i = j
    · simpa [hij] using continuousOn_const
    · simp only [hij, ↓reduceIte]
      exact fun z hz ↦ ((continuousAt_moebiusSign
        (im_ne_zero_of_mem_moebiusBaseSet hij hz.1 hz.2)).smul
          continuousAt_const).continuousWithinAt
  coordChange_comp i j k z _ v := by
    cases i <;> cases j <;> cases k <;> simp [← mul_assoc]

/-- The chart domains of the Möbius line bundle are `TauCeti.moebiusBaseSet`. -/
theorem moebiusCore_baseSet (i : Bool) : moebiusCore.baseSet i = moebiusBaseSet i :=
  (rfl)

/-- The base set of the local trivialization `i` of the Möbius line bundle is
`TauCeti.moebiusBaseSet i`. -/
@[simp]
theorem moebiusCore_localTriv_baseSet (i : Bool) :
    (moebiusCore.localTriv i).baseSet = moebiusBaseSet i :=
  (rfl)

/-- The transition function of the Möbius line bundle between different charts is multiplication by
`TauCeti.moebiusSign`. -/
@[simp]
theorem moebiusCore_coordChange (i j : Bool) (z : Circle) :
    moebiusCore.coordChange i j z =
      if i = j then ContinuousLinearMap.id ℝ ℝ else moebiusSign z • ContinuousLinearMap.id ℝ ℝ :=
  (rfl)

/-- The fibres of the Möbius line bundle carry the norm of `ℝ`. -/
instance (z : Circle) : NormedAddCommGroup (moebiusCore.Fiber z) :=
  inferInstanceAs (NormedAddCommGroup ℝ)

instance (z : Circle) : NormedSpace ℝ (moebiusCore.Fiber z) :=
  inferInstanceAs (NormedSpace ℝ ℝ)

/-- The transition functions of the Möbius line bundle preserve the norm of `ℝ`. -/
theorem norm_moebiusCore_coordChange (i j : Bool) (z : Circle) (v : ℝ) :
    ‖moebiusCore.coordChange i j z v‖ = ‖v‖ := by
  rw [moebiusCore_coordChange]
  split_ifs
  · rfl
  · unfold moebiusSign
    split_ifs <;> simp

/-- **The fibre norm of the Möbius line bundle is continuous on the total space**, because its
transition functions are isometries. -/
theorem continuous_norm_moebiusCore :
    Continuous fun v : TotalSpace ℝ moebiusCore.Fiber ↦ ‖v.snd‖ := by
  refine continuous_iff_continuousAt.2 fun v₀ ↦ ?_
  let e := moebiusCore.localTriv (moebiusCore.indexAt v₀.proj)
  have hv₀ : v₀ ∈ e.source :=
    (moebiusCore.mem_localTriv_source _ _).2 (moebiusCore.mem_baseSet_at _)
  -- In the chart at `v₀`, the norm of the second coordinate is the fibre norm.
  refine ((continuous_norm.comp continuous_snd).continuousAt.comp
    (e.continuousOn.continuousAt (e.open_source.mem_nhds hv₀))).congr
      (Eventually.of_forall fun v ↦ ?_)
  simp only [Function.comp_apply, e, VectorBundleCore.localTriv_apply]
  exact norm_moebiusCore_coordChange _ _ _ _

/-- The two chart domains of the Möbius line bundle are connected: each is the circle minus a
point. -/
theorem isPreconnected_moebiusBaseSet (i : Bool) : IsPreconnected (moebiusBaseSet i) := by
  cases i
  · convert (Circle.isPathConnected_compl_singleton 1).isConnected.isPreconnected using 1
    ext z
    simp [Circle.ext_iff]
  · convert (Circle.isPathConnected_compl_singleton (Circle.exp π)).isConnected.isPreconnected
      using 1
    ext z
    simp [Circle.ext_iff, Circle.coe_exp, Complex.exp_pi_mul_I]

/-- The coordinate change of the Möbius line bundle from the chart `true` to the chart `false`, at
a point of their overlap, has determinant the transition function. -/
private theorem det_coordChangeL_moebiusCore {z : Circle} (h₁ : z ∈ moebiusBaseSet true)
    (h₀ : z ∈ moebiusBaseSet false) :
    LinearMap.det (((moebiusCore.localTriv true).coordChangeL ℝ
      (moebiusCore.localTriv false) z).toLinearEquiv : ℝ →ₗ[ℝ] ℝ) = moebiusSign z := by
  rw [LinearMap.det_ring]
  simp only [ContinuousLinearEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe]
  rw [VectorBundleCore.localTriv_coordChange_eq _ _ _ ⟨h₁, h₀⟩]
  simp

/-- **The Möbius line bundle is not orientable.** -/
theorem isEmpty_vectorBundleOrientation_moebiusCore :
    IsEmpty (VectorBundleOrientation ℝ moebiusCore.Fiber (Fin 1)) := by
  have hι : Fintype.card (Fin 1) = finrank ℝ ℝ := by simp
  -- The points `i` and `-i` lie in both charts, on the upper and the lower half-circle.
  let p : Circle := Circle.exp (π / 2)
  let q : Circle := Circle.exp (-(π / 2))
  have hp : 0 < (p : ℂ).im := by simp [p, Circle.coe_exp]
  have hq : (q : ℂ).im < 0 := by simp [q, Circle.coe_exp]
  have hmem {z : Circle} (hz : (z : ℂ).im ≠ 0) (i : Bool) : z ∈ moebiusBaseSet i := by
    intro h
    cases i <;> simp_all
  have : MemTrivializationAtlas (moebiusCore.localTriv false) := ⟨⟨false, rfl⟩⟩
  have : MemTrivializationAtlas (moebiusCore.localTriv true) := ⟨⟨true, rfl⟩⟩
  -- The coordinate change from the chart `true` to the chart `false` is `1` at `p` and `-1` at `q`.
  refine VectorBundleOrientation.isEmpty_of_det_coordChangeL_pos_of_neg hι
    (moebiusCore.localTriv true) (moebiusCore.localTriv false) (isPreconnected_moebiusBaseSet true)
    (isPreconnected_moebiusBaseSet false) le_rfl le_rfl (hmem hp.ne' true) (hmem hp.ne' false)
    (hmem hq.ne true) (hmem hq.ne false) ?_ ?_
  · rw [det_coordChangeL_moebiusCore (hmem hp.ne' true) (hmem hp.ne' false), moebiusSign_of_pos hp]
    exact one_pos
  · rw [det_coordChangeL_moebiusCore (hmem hq.ne true) (hmem hq.ne false), moebiusSign_of_neg hq]
    norm_num

end TauCeti
