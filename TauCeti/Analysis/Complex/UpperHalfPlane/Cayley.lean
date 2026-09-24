/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Bornology.BoundedOperation

/-!
# The Cayley transform of the closed upper half-plane

The Cayley transform `z ↦ (z - i) / (z + i)` carries the open upper half-plane bijectively onto the
open unit disc, and the *closed* upper half-plane `{z | 0 ≤ z.im}` bijectively onto the closed unit
disc with the point `1` removed; the missing point `1` is the limit of the transform at infinity.

This file records these facts for the transform as a map `ℂ → ℂ`, so that a statement about maps
continuous on the closed unit disc and holomorphic inside it can be transported to the closed upper
half-plane. The open-half-plane restriction, centred at an arbitrary point of `ℍ`, is
`UpperHalfPlane.discCoordinate`.

## Main statements

* `TauCeti.norm_sub_I_div_add_I_le_one_iff` and `TauCeti.norm_sub_I_div_add_I_lt_one_iff`: the
  transform lands in the closed (open) unit disc exactly at points of the closed (open) upper
  half-plane.
* `TauCeti.injOn_sub_I_div_add_I`: the transform is injective off its pole `-i`.
* `TauCeti.bijOn_sub_I_div_add_I_upperHalfPlaneSet`: the transform is a bijection from the open
  upper half-plane onto the open unit disc.
* `TauCeti.bijOn_sub_I_div_add_I_im_nonneg`: the transform is a bijection from the closed upper
  half-plane onto the closed unit disc minus `1`.
* `TauCeti.differentiableOn_sub_I_div_add_I`: the transform is holomorphic away from its pole.
* `TauCeti.differentiableOn_sub_I_div_add_I_im_nonneg`: in particular, it is holomorphic on a
  neighbourhood of the closed upper half-plane.
* `TauCeti.tendsto_sub_I_div_add_I_cobounded`: the transform tends to `1` at infinity.

## References

* L. V. Ahlfors, *Complex Analysis*, 3rd ed., McGraw–Hill, 1979, Ch. 3 §3.
-/

public section

open Bornology Complex Filter Metric Set Topology

namespace TauCeti

/-- The denominator of the Cayley transform does not vanish on the closed upper half-plane. -/
theorem add_I_ne_zero_of_im_nonneg {z : ℂ} (hz : 0 ≤ z.im) : z + I ≠ 0 := fun h => by
  have := congrArg Complex.im h
  simp only [add_im, I_im, zero_im] at this
  linarith

/-- The squared distances from `z` to `-i` and to `i` differ by `4 * z.im`. -/
private theorem norm_add_I_sq (z : ℂ) : ‖z + I‖ ^ 2 = ‖z - I‖ ^ 2 + 4 * z.im := by
  simp only [Complex.sq_norm, normSq_apply, add_re, add_im, sub_re, sub_im, I_re, I_im]
  ring

/-- The Cayley transform lies in the closed unit disc exactly on the closed upper half-plane. -/
theorem norm_sub_I_div_add_I_le_one_iff {z : ℂ} (hz : z + I ≠ 0) :
    ‖(z - I) / (z + I)‖ ≤ 1 ↔ 0 ≤ z.im := by
  rw [norm_div, div_le_one (norm_pos_iff.mpr hz), ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    norm_add_I_sq]
  constructor <;> intro h <;> linarith

/-- The Cayley transform lies in the open unit disc exactly on the open upper half-plane. -/
theorem norm_sub_I_div_add_I_lt_one_iff {z : ℂ} (hz : z + I ≠ 0) :
    ‖(z - I) / (z + I)‖ < 1 ↔ 0 < z.im := by
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hz), ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _),
    norm_add_I_sq]
  constructor <;> intro h <;> linarith

/-- The closed-disc criterion in the normal form used by `simp` after `norm_div`. -/
@[simp] theorem norm_sub_I_div_norm_add_I_le_one_iff {z : ℂ} (hz : z + I ≠ 0) :
    ‖z - I‖ / ‖z + I‖ ≤ 1 ↔ 0 ≤ z.im := by
  simpa only [norm_div] using norm_sub_I_div_add_I_le_one_iff hz

/-- The open-disc criterion in the normal form used by `simp` after `norm_div`. -/
@[simp] theorem norm_sub_I_div_norm_add_I_lt_one_iff {z : ℂ} (hz : z + I ≠ 0) :
    ‖z - I‖ / ‖z + I‖ < 1 ↔ 0 < z.im := by
  simpa only [norm_div] using norm_sub_I_div_add_I_lt_one_iff hz

/-- The Cayley transform is injective wherever its denominator does not vanish. -/
theorem injOn_sub_I_div_add_I :
    InjOn (fun z : ℂ => (z - I) / (z + I)) {z | z + I ≠ 0} := by
  intro z hz w hw h
  simp only [mem_ofPred_eq] at hz hw
  rw [div_eq_div_iff hz hw] at h
  have h2 : (2 * I) * (z - w) = 0 := by linear_combination h
  simpa [sub_eq_zero, I_ne_zero] using h2

/-- The inverse Cayley transform `w ↦ i (1 + w) / (1 - w)` is a right inverse of the transform
away from `w = 1`, and its value keeps the denominator `z + i` away from `0`. -/
private theorem sub_I_div_add_I_inverse {w : ℂ} (hw : w ≠ 1) :
    I * (1 + w) / (1 - w) + I ≠ 0 ∧
      (I * (1 + w) / (1 - w) - I) / (I * (1 + w) / (1 - w) + I) = w := by
  have h1 : 1 - w ≠ 0 := sub_ne_zero.mpr hw.symm
  have hden : I * (1 + w) / (1 - w) + I = 2 * I / (1 - w) := by
    field_simp
    ring
  have hnum : I * (1 + w) / (1 - w) - I = 2 * I * w / (1 - w) := by
    field_simp
    ring
  have h2I : (2 : ℂ) * I ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  refine ⟨hden ▸ div_ne_zero h2I h1, ?_⟩
  rw [hden, hnum]
  field_simp

/-- **The Cayley transform of the open upper half-plane.** The map `z ↦ (z - i) / (z + i)` is a
bijection from the open upper half-plane onto the open unit disc. -/
theorem bijOn_sub_I_div_add_I_upperHalfPlaneSet :
    BijOn (fun z : ℂ => (z - I) / (z + I)) UpperHalfPlane.upperHalfPlaneSet
      (ball 0 1) := by
  refine ⟨fun z hz => ?_, injOn_sub_I_div_add_I.mono fun z hz => ?_, fun w hw => ?_⟩
  · exact mem_ball_zero_iff.mpr
      ((norm_sub_I_div_add_I_lt_one_iff (add_I_ne_zero_of_im_nonneg (le_of_lt hz))).mpr hz)
  · exact add_I_ne_zero_of_im_nonneg (le_of_lt hz)
  · have hw1 : w ≠ 1 := by
      rintro rfl
      simp at hw
    obtain ⟨hne, heq⟩ := sub_I_div_add_I_inverse hw1
    refine ⟨_, ?_, heq⟩
    rw [UpperHalfPlane.upperHalfPlaneSet, mem_ofPred_eq, ← norm_sub_I_div_add_I_lt_one_iff hne, heq]
    exact mem_ball_zero_iff.mp hw

/-- **The Cayley transform of the closed upper half-plane.** The map `z ↦ (z - i) / (z + i)` is a
bijection from the closed upper half-plane onto the closed unit disc with the point `1` removed. -/
theorem bijOn_sub_I_div_add_I_im_nonneg :
    BijOn (fun z : ℂ => (z - I) / (z + I)) {z | 0 ≤ z.im} (closedBall 0 1 \ {1}) := by
  refine ⟨fun z hz => ⟨?_, ?_⟩, injOn_sub_I_div_add_I.mono fun z hz =>
    add_I_ne_zero_of_im_nonneg hz, fun w hw => ?_⟩
  · exact mem_closedBall_zero_iff.mpr ((norm_sub_I_div_add_I_le_one_iff
      (add_I_ne_zero_of_im_nonneg hz)).mpr hz)
  · rw [mem_singleton_iff, div_eq_one_iff_eq (add_I_ne_zero_of_im_nonneg hz)]
    intro h
    have := congrArg Complex.im h
    simp only [sub_im, add_im, I_im] at this
    linarith
  · obtain ⟨hne, heq⟩ := sub_I_div_add_I_inverse hw.2
    refine ⟨_, ?_, heq⟩
    rw [mem_ofPred_eq, ← norm_sub_I_div_add_I_le_one_iff hne, heq]
    exact mem_closedBall_zero_iff.mp hw.1

/-- The Cayley transform is complex differentiable away from its pole at `-i`. -/
theorem differentiableOn_sub_I_div_add_I :
    DifferentiableOn ℂ (fun z : ℂ => (z - I) / (z + I)) {z | z + I ≠ 0} :=
  (differentiableOn_id.sub (differentiableOn_const _)).div
    (differentiableOn_id.add (differentiableOn_const _)) fun _ hz => hz

/-- The Cayley transform is complex differentiable at every point of the closed upper half-plane. -/
theorem differentiableOn_sub_I_div_add_I_im_nonneg :
    DifferentiableOn ℂ (fun z : ℂ => (z - I) / (z + I)) {z | 0 ≤ z.im} :=
  differentiableOn_sub_I_div_add_I.mono fun _ hz => add_I_ne_zero_of_im_nonneg hz

/-- The Cayley transform tends to `1` at infinity: the point `1` it omits from the closed disc is
the image of `∞`. -/
theorem tendsto_sub_I_div_add_I_cobounded :
    Tendsto (fun z : ℂ => (z - I) / (z + I)) (cobounded ℂ) (𝓝 1) := by
  have hinv : Tendsto (fun z : ℂ => (z + I)⁻¹) (cobounded ℂ) (𝓝 0) :=
    tendsto_inv₀_cobounded.comp (tendsto_add_const_cobounded I)
  have hlim : Tendsto (fun z : ℂ => 1 - 2 * I * (z + I)⁻¹) (cobounded ℂ) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (hinv.const_mul (2 * I))
  refine hlim.congr' ?_
  filter_upwards [(tendsto_add_const_cobounded I).eventually
    (eventually_ne_cobounded (0 : ℂ))] with z (hz : z + I ≠ 0)
  field_simp
  ring

end TauCeti
