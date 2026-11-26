/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Jon Crall, Claude Opus 5, OpenAI gpt-6.1-sol
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import TauCeti.Analysis.Complex.Cayley.Basic
public import TauCeti.Analysis.Complex.UnitDisc.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
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

The scalar identities, disc bounds and real inverse coordinate are provided by
`Analysis.Complex.Cayley`.

## Main statements

* `TauCeti.one_sub_conj_mul_sub_I_div_add_I_ne_zero`: the denominator of a standard disc
  automorphism does not vanish at a real boundary point in Cayley coordinates.
* `TauCeti.bijOn_sub_I_div_add_I_upperHalfPlaneSet`: the transform is a bijection from the open
  upper half-plane onto the open unit disc.
* `TauCeti.bijOn_I_mul_one_add_div_one_sub_ball`: its inverse `w ↦ i (1 + w) / (1 - w)` is a
  bijection from the open unit disc onto the open upper half-plane.
* `TauCeti.bijOn_sub_I_div_add_I_im_nonneg`: the transform is a bijection from the closed upper
  half-plane onto the closed unit disc minus `1`.
* `TauCeti.bijOn_I_mul_one_add_div_one_sub_closedBall_sdiff`: its inverse is a bijection from the
  closed unit disc minus `1` onto the closed upper half-plane.
* `TauCeti.differentiableOn_sub_I_div_add_I`: the transform is holomorphic away from its pole.
* `TauCeti.differentiableOn_sub_I_div_add_I_im_nonneg`: in particular, it is holomorphic on a
  neighbourhood of the closed upper half-plane.
* `TauCeti.hasDerivAt_I_mul_one_add_div_one_sub`: the derivative of the inverse transform.
* `TauCeti.logDeriv_deriv_I_mul_one_add_div_one_sub`: its pre-Schwarzian.
* `TauCeti.tendsto_sub_I_div_add_I_cobounded`: the transform tends to `1` at infinity.
* `TauCeti.tendsto_I_mul_one_add_div_one_sub_nhdsNE_one`: its inverse tends to infinity at `1`,
  within the closed upper half-plane when approached from the closed disc
  (`TauCeti.tendsto_I_mul_one_add_div_one_sub_nhdsWithin_closedBall_sdiff_one`).
* `TauCeti.contDiffAt_I_mul_sub_div_add` and `TauCeti.contDiffAt_mul_I_sub_div_add_I`: these
  two maps are analytic away from their poles `-ζ` and `-i`.

## References

* L. V. Ahlfors, *Complex Analysis*, 3rd ed., McGraw–Hill, 1979, Ch. 3 §3.
-/

public section

open Bornology Complex Filter Metric Set Topology
open scoped ContDiff

namespace TauCeti

/-- The denominator of a standard disc automorphism does not vanish at the Cayley transform of a
real point. -/
theorem one_sub_conj_mul_sub_I_div_add_I_ne_zero (c : Complex.UnitDisc) (x : ℝ) :
    1 - (starRingEnd ℂ) (c : ℂ) * (((x : ℂ) - I) / ((x : ℂ) + I)) ≠ 0 := by
  intro h
  have hnorm : ‖(c : ℂ)‖ * ‖((x : ℂ) - I) / ((x : ℂ) + I)‖ = 1 := by
    have := congrArg norm (sub_eq_zero.mp h)
    simpa [norm_mul] using this.symm
  rw [norm_div, norm_sub_I_div_norm_add_I_ofReal x, mul_one] at hnorm
  exact (ne_of_lt c.norm_lt_one) hnorm

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
    refine ⟨_, ?_, sub_I_div_add_I_I_mul_one_add_div_one_sub hw1⟩
    rw [UpperHalfPlane.upperHalfPlaneSet, mem_ofPred_eq,
      ← norm_sub_I_div_add_I_lt_one_iff (I_mul_one_add_div_one_sub_add_I_ne_zero hw1),
      sub_I_div_add_I_I_mul_one_add_div_one_sub hw1]
    exact mem_ball_zero_iff.mp hw

/-- **The inverse Cayley transform.** The map `w ↦ i (1 + w) / (1 - w)` is a bijection from the
open unit disc onto the open upper half-plane; it inverts `z ↦ (z - i) / (z + i)`. -/
theorem bijOn_I_mul_one_add_div_one_sub_ball :
    BijOn (fun w : ℂ => I * (1 + w) / (1 - w)) (ball 0 1)
      UpperHalfPlane.upperHalfPlaneSet := by
  refine bijOn_sub_I_div_add_I_upperHalfPlaneSet.symm ⟨fun w hw => ?_, fun z hz => ?_⟩
  · refine sub_I_div_add_I_I_mul_one_add_div_one_sub ?_
    rintro rfl
    simp at hw
  · have hz' := add_I_ne_zero_of_im_nonneg (le_of_lt hz)
    exact I_mul_one_add_sub_I_div_add_I_div_one_sub hz'

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
  · refine ⟨_, ?_, sub_I_div_add_I_I_mul_one_add_div_one_sub hw.2⟩
    rw [mem_ofPred_eq, ← norm_sub_I_div_add_I_le_one_iff
      (I_mul_one_add_div_one_sub_add_I_ne_zero hw.2),
      sub_I_div_add_I_I_mul_one_add_div_one_sub hw.2]
    exact mem_closedBall_zero_iff.mp hw.1

/-- **The inverse Cayley transform on the closed disc.** The map `w ↦ i (1 + w) / (1 - w)` is a
bijection from the closed unit disc with the point `1` removed onto the closed upper half-plane;
it inverts `z ↦ (z - i) / (z + i)`. -/
theorem bijOn_I_mul_one_add_div_one_sub_closedBall_sdiff :
    BijOn (fun w : ℂ => I * (1 + w) / (1 - w)) (closedBall 0 1 \ {1}) {z | 0 ≤ z.im} :=
  bijOn_sub_I_div_add_I_im_nonneg.symm ⟨fun _ hw => sub_I_div_add_I_I_mul_one_add_div_one_sub hw.2,
    fun _ hz => I_mul_one_add_sub_I_div_add_I_div_one_sub (add_I_ne_zero_of_im_nonneg hz)⟩

/-- The Cayley transform is complex differentiable away from its pole at `-i`. -/
theorem differentiableOn_sub_I_div_add_I :
    DifferentiableOn ℂ (fun z : ℂ => (z - I) / (z + I)) {z | z + I ≠ 0} :=
  (differentiableOn_id.sub (differentiableOn_const _)).div
    (differentiableOn_id.add (differentiableOn_const _)) fun _ hz => hz

/-- The Cayley transform is complex differentiable at every point of the closed upper half-plane. -/
theorem differentiableOn_sub_I_div_add_I_im_nonneg :
    DifferentiableOn ℂ (fun z : ℂ => (z - I) / (z + I)) {z | 0 ≤ z.im} :=
  differentiableOn_sub_I_div_add_I.mono fun _ hz => add_I_ne_zero_of_im_nonneg hz

/-- The derivative of the inverse Cayley transform `w ↦ i (1 + w) / (1 - w)` away from its pole
at `1` is `2 i / (1 - w) ^ 2`. -/
theorem hasDerivAt_I_mul_one_add_div_one_sub {w : ℂ} (hw : w ≠ 1) :
    HasDerivAt (fun u : ℂ => I * (1 + u) / (1 - u)) (2 * I / (1 - w) ^ 2) w := by
  have h1 : 1 - w ≠ 0 := sub_ne_zero.mpr hw.symm
  refine ((((hasDerivAt_id w).const_add 1).const_mul I).div
    ((hasDerivAt_id w).const_sub 1) h1).congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-- The inverse Cayley transform tends to infinity as the disc variable tends to its pole `1`. -/
theorem tendsto_I_mul_one_add_div_one_sub_nhdsNE_one :
    Tendsto (fun ζ : ℂ => I * (1 + ζ) / (1 - ζ)) (𝓝[≠] 1) (cobounded ℂ) := by
  have hzero : Tendsto (fun ζ : ℂ => 1 - ζ) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun ζ : ℂ => 1 - ζ) (𝓝[≠] 1) (𝓝 (1 - 1)))
    · exact eventually_nhdsWithin_of_forall fun ζ hζ => sub_ne_zero.mpr (Ne.symm hζ)
  refine ((tendsto_sub_const_cobounded I).comp
    ((tendsto_mul_left_cobounded (mul_ne_zero two_ne_zero I_ne_zero)).comp
      (tendsto_inv₀_nhdsNE_zero.comp hzero))).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ζ hζ
  have hne : 1 - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hζ)
  dsimp only [Function.comp_def]
  field_simp
  ring

/-- The pre-Schwarzian of the inverse Cayley transform is `2 / (1 - ζ)` (at its pole `ζ = 1` both
sides are `0` by convention). -/
theorem logDeriv_deriv_I_mul_one_add_div_one_sub {ζ : ℂ} :
    logDeriv (deriv fun ξ : ℂ => I * (1 + ξ) / (1 - ξ)) ζ = 2 / (1 - ζ) := by
  rcases eq_or_ne ζ 1 with rfl | hζ
  · -- at the pole the map is not differentiable, so its derivative is `0` by convention
    have hnd : ¬ DifferentiableAt ℂ (fun ξ : ℂ => I * (1 + ξ) / (1 - ξ)) 1 := fun hd ↦
      not_continuousAt_of_tendsto tendsto_I_mul_one_add_div_one_sub_nhdsNE_one
        nhdsWithin_le_nhds (disjoint_nhds_cobounded _) hd.continuousAt
    simp [logDeriv_apply, deriv_zero_of_not_differentiableAt hnd]
  have heq : (deriv fun ξ : ℂ => I * (1 + ξ) / (1 - ξ)) =ᶠ[𝓝 ζ]
      fun ξ => 2 * I / (1 - ξ) ^ 2 :=
    eventuallyEq_of_mem (isOpen_ne.mem_nhds hζ) fun _ hξ =>
      (hasDerivAt_I_mul_one_add_div_one_sub hξ).deriv
  have hfun : (fun ξ : ℂ => 2 * I / (1 - ξ) ^ 2) =
      (fun ξ : ℂ => 2 * I * (1 - ξ) ^ (-2 : ℤ)) := by
    funext ξ
    simp [zpow_neg, zpow_ofNat, div_eq_mul_inv]
  rw [(logDeriv_congr_nhds heq).eq_of_nhds, hfun,
    logDeriv_const_mul ζ (2 * I) (mul_ne_zero two_ne_zero I_ne_zero),
    logDeriv_fun_zpow (by fun_prop : DifferentiableAt ℂ (fun ξ : ℂ => 1 - ξ) ζ) (-2),
    logDeriv_apply, deriv_const_sub_id 1]
  ring

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

/-- The inverse Cayley transform tends to infinity within the upper half-plane as the disc
variable tends to the omitted boundary point `1`. -/
theorem tendsto_I_mul_one_add_div_one_sub_nhdsWithin_one :
    Tendsto (fun ζ : ℂ => I * (1 + ζ) / (1 - ζ)) (𝓝[ball 0 1] 1)
      (cobounded ℂ ⊓ 𝓟 UpperHalfPlane.upperHalfPlaneSet) :=
  tendsto_inf.mpr ⟨tendsto_I_mul_one_add_div_one_sub_nhdsNE_one.mono_left
      (nhdsWithin_mono _ fun _ hζ => ne_of_mem_of_not_mem hζ (by simp)),
    tendsto_principal.mpr (eventually_nhdsWithin_of_forall fun _ hζ =>
      bijOn_I_mul_one_add_div_one_sub_ball.mapsTo hζ)⟩

/-- The inverse Cayley transform tends to infinity within the closed upper half-plane as the
variable tends to the omitted boundary point `1` within the closed disc. -/
theorem tendsto_I_mul_one_add_div_one_sub_nhdsWithin_closedBall_sdiff_one :
    Tendsto (fun ζ : ℂ => I * (1 + ζ) / (1 - ζ)) (𝓝[closedBall 0 1 \ {1}] 1)
      (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) :=
  tendsto_inf.mpr ⟨tendsto_I_mul_one_add_div_one_sub_nhdsNE_one.mono_left
      (nhdsWithin_mono _ fun _ hζ => hζ.2),
    tendsto_principal.mpr (eventually_nhdsWithin_of_forall fun _ hζ =>
      bijOn_I_mul_one_add_div_one_sub_closedBall_sdiff.mapsTo hζ)⟩

/-! ### Cayley transforms of the closed unit disc centred at a boundary point -/

/-- The map `z ↦ i (ζ - z) / (ζ + z)` is analytic away from its pole `-ζ`. -/
theorem contDiffAt_I_mul_sub_div_add {n : ℕ∞ω} (ζ : ℂ) {z : ℂ} (hz : ζ + z ≠ 0) :
    ContDiffAt ℂ n (fun z : ℂ ↦ I * (ζ - z) / (ζ + z)) z :=
  (contDiffAt_const.mul (contDiffAt_const.sub contDiffAt_id)).div
    (contDiffAt_const.add contDiffAt_id) hz

/-- The map `w ↦ ζ (i - w) / (w + i)` is analytic away from its pole `-i`. -/
theorem contDiffAt_mul_I_sub_div_add_I {n : ℕ∞ω} (ζ : ℂ) {w : ℂ} (hw : w + I ≠ 0) :
    ContDiffAt ℂ n (fun w : ℂ ↦ ζ * (I - w) / (w + I)) w :=
  (contDiffAt_const.mul (contDiffAt_const.sub contDiffAt_id)).div
    (contDiffAt_id.add contDiffAt_const) hw

end TauCeti
