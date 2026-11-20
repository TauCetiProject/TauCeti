/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ThricePuncturedSphere.EndCoordinate
public import TauCeti.Analysis.Complex.RealChart

/-!
# The truncation of a sphere with moving input ends

A sphere with moving input ends is the Riemann sphere with input punctures at points `c i` of `ℂ`
and an output puncture at `∞`. The input end `i` is the image of the end lift
`z ↦ c i + a i φ₀(z)` of the end of `0` of the thrice-punctured sphere, scaled by `a i ≠ 0`, and
the output end is the end lift `φ_∞` of `∞`. A point with longitudinal coordinate `s` on the input
end `i` lies at distance `‖a i‖ exp (-2πs) / 2` from `c i`
(`TauCeti.ThricePuncturedSphere.norm_add_mul_cylindricalEndLift_sub`).

This file defines the truncation `Σ_R` of such a sphere, cut along the circle `s = R` of every input
end and the circle `s = -R` of the output end. It is the compact domain over which the Floer
energy and curvature integrals of maps from a sphere with moving input ends are taken, and the
sphere minus its punctures is the increasing union of the `Σ_R`, so integrals over it are limits
as `R → ∞`. For centers `0, 1` and scales `1, -1` it is the truncation `S_R` of the
thrice-punctured sphere.

The perturbation data on such a sphere are cut off by `β(±s - 1)` on the ends, so they vanish
where `±s ≤ 1`. The file therefore places the parts `1 ≤ s ≤ R` of the input ends and
`-R ≤ s ≤ -1` of the output end in `Σ_R`, under the hypotheses that the discs
`‖w - c i‖ < ‖a i‖ / 2` are pairwise disjoint and lie in the disc `‖w‖ ≤ 2 exp (2π)`.
Conversely, a point of `Σ_R` close to `c i`, or far from `0`, lies on one of these parts, so `Σ_R`
splits into these end pieces and a core where the cut-off data vanish.

## Main definitions and results

In the namespace `TauCeti.ThricePuncturedSphere`:

* `puncturedSphereTruncation`: the truncation `Σ_R`, with `mem_puncturedSphereTruncation`,
  `isCompact_puncturedSphereTruncation` and `ne_of_mem_puncturedSphereTruncation`. It increases
  with `R` (`puncturedSphereTruncation_mono`), exhausts the sphere minus its punctures
  (`iUnion_puncturedSphereTruncation`), and specializes to the truncation of the thrice-punctured
  sphere (`puncturedSphereTruncation_eq_truncation`).
* `hasDerivAt_add_mul_cylindricalEndLift`: the complex derivative of the end lift of an input end.
* `injOn_add_mul_cylindricalEndLift` and `injOn_realChart_add_mul_cylindricalEndLift`: the end
  lift of an input end is injective on every horizontal strip of height one.
* `add_mul_cylindricalEndLift_mem_puncturedSphereTruncation` and
  `cylindricalEndLift_inf_mem_puncturedSphereTruncation`: the end pieces lie in `Σ_R`.
* `exists_add_mul_cylindricalEndLift_eq`: the converse for the input ends; for the output end it
  is `Puncture.exists_cylindricalEndLift_inf_eq`.
* `add_mul_cylindricalEndLift_ne`: a point with `s > 0` on an input end is no center.
-/

public section

open Set Real Filter
open scoped Topology

namespace TauCeti.ThricePuncturedSphere

open Puncture
open TauCeti.Complex (realChart injOn_realChart)

variable {ι : Type*} {c a : ι → ℂ} {R : ℝ}

/-- For a nonzero scale `a`, the radius `‖a‖ exp (-2π) / 2` of the disc around the center
containing the part `s ≥ 1` of an input end is strictly less than `‖a‖ / 2`. -/
theorem norm_mul_exp_neg_two_pi_div_two_lt {a : ℂ} (ha : a ≠ 0) :
    ‖a‖ * Real.exp (-(2 * π)) / 2 < ‖a‖ / 2 := by
  have := norm_pos_iff.2 ha
  have : Real.exp (-(2 * π)) < 1 := Real.exp_lt_one_iff.2 (by linarith [Real.pi_pos])
  nlinarith

/-- **The truncation of a sphere with moving input ends.** For input ends with centers `c i` and
scales `a i`, the part of the plane cut off along the circle `s = R` of every input end and the
circle `s = -R` of the output end at `∞`: the points at distance at least `‖a i‖ exp (-2πR) / 2`
from every center `c i`, in the disc `‖w‖ ≤ 2 exp (2πR)`. -/
def puncturedSphereTruncation (c a : ι → ℂ) (R : ℝ) : Set ℂ :=
  {w | (∀ i, ‖a i‖ * Real.exp (-(2 * π * R)) / 2 ≤ ‖w - c i‖) ∧ ‖w‖ ≤ 2 * Real.exp (2 * π * R)}

/-- Membership in the truncation `Σ_R` of a sphere with moving input ends. -/
@[simp]
theorem mem_puncturedSphereTruncation {w : ℂ} :
    w ∈ puncturedSphereTruncation c a R ↔
      (∀ i, ‖a i‖ * Real.exp (-(2 * π * R)) / 2 ≤ ‖w - c i‖) ∧ ‖w‖ ≤ 2 * Real.exp (2 * π * R) :=
  Iff.rfl

/-- The truncation of a sphere with moving input ends is compact. -/
theorem isCompact_puncturedSphereTruncation (c a : ι → ℂ) (R : ℝ) :
    IsCompact (puncturedSphereTruncation c a R) := by
  refine (isCompact_closedBall (0 : ℂ) (2 * Real.exp (2 * π * R))).of_isClosed_subset ?_
    fun w hw ↦ by simpa using hw.2
  simp only [puncturedSphereTruncation, ofPred_and, ofPred_forall]
  exact (isClosed_iInter fun i ↦ isClosed_le continuous_const (by fun_prop)).inter
    (isClosed_le (by fun_prop) continuous_const)

/-- The truncations of a sphere with moving input ends increase with the cutoff. -/
theorem puncturedSphereTruncation_mono : Monotone (puncturedSphereTruncation c a) :=
  fun R R' hRR' w hw ↦ ⟨fun i ↦ le_trans (by gcongr) (hw.1 i), hw.2.trans (by gcongr)⟩

/-- For the centers `0, 1` and the scales `1, -1`, the truncation of a sphere with moving input
ends is the truncation `S_R` of the thrice-punctured sphere. -/
@[simp]
theorem puncturedSphereTruncation_eq_truncation (R : ℝ) :
    puncturedSphereTruncation ![0, 1] ![1, -1] R = truncation R := by
  ext w
  simp [truncation_eq, Fin.forall_fin_two, and_assoc]

/-- For nonzero scales, the truncation avoids the centers of the input ends. -/
theorem ne_of_mem_puncturedSphereTruncation {i : ι} (ha : a i ≠ 0) {w : ℂ}
    (hw : w ∈ puncturedSphereTruncation c a R) : w ≠ c i := by
  rintro rfl
  have h := hw.1 i
  have hpos : 0 < ‖a i‖ * Real.exp (-(2 * π * R)) / 2 := by
    have := norm_pos_iff.2 ha
    positivity
  rw [sub_self, norm_zero] at h
  linarith

/-- For finitely many input ends with nonzero scales, the truncations exhaust the sphere minus
its punctures: the plane minus the centers of the input ends. -/
theorem iUnion_puncturedSphereTruncation [Finite ι] (ha : ∀ i, a i ≠ 0) :
    ⋃ R, puncturedSphereTruncation c a R = {w | ∀ i, w ≠ c i} := by
  ext w
  simp only [mem_iUnion, mem_ofPred_eq]
  refine ⟨fun ⟨R, hR⟩ i ↦ ne_of_mem_puncturedSphereTruncation (ha i) hR, fun hw ↦ ?_⟩
  have hexp : Tendsto (fun R : ℝ ↦ 2 * π * R) atTop atTop :=
    tendsto_id.const_mul_atTop Real.two_pi_pos
  -- Near each center the radius `‖a i‖ exp (-2πR) / 2` tends to `0`, and the outer radius
  -- `2 exp (2πR)` tends to `∞`.
  have hin (i : ι) : ∀ᶠ R in atTop, ‖a i‖ * Real.exp (-(2 * π * R)) / 2 ≤ ‖w - c i‖ := by
    have h : Tendsto (fun R : ℝ ↦ ‖a i‖ * Real.exp (-(2 * π * R)) / 2) atTop (𝓝 0) := by
      simpa using ((Real.tendsto_exp_neg_atTop_nhds_zero.comp hexp).const_mul ‖a i‖).div_const 2
    exact (h.eventually (gt_mem_nhds (norm_pos_iff.2 (sub_ne_zero.2 (hw i))))).mono
      fun _ ↦ le_of_lt
  have hout : ∀ᶠ R in atTop, ‖w‖ ≤ 2 * Real.exp (2 * π * R) :=
    ((Real.tendsto_exp_atTop.comp hexp).const_mul_atTop two_pos).eventually_ge_atTop ‖w‖
  obtain ⟨R, hR⟩ := ((eventually_all.2 hin).and hout).exists
  exact ⟨R, hR⟩

/-- A point of the input end with center `c` and scale `a`, at longitudinal coordinate `s`, lies
at distance `‖a‖ exp (-2πs) / 2` from the center. -/
theorem norm_add_mul_cylindricalEndLift_sub (c a z : ℂ) :
    ‖c + a * zero.cylindricalEndLift z - c‖ = ‖a‖ * Real.exp (-(2 * π * z.re)) / 2 := by
  have h := norm_cylindricalEndLift_sub_endCenter zero z
  rw [endCenter_zero, sub_zero, endScale_zero] at h
  rw [add_sub_cancel_left, norm_mul, h]
  norm_num
  ring

/-- The end lift `z ↦ c + a φ₀(z)` of an input end has complex derivative `a φ₀'(z)`. -/
theorem hasDerivAt_add_mul_cylindricalEndLift (c a w : ℂ) :
    HasDerivAt (fun z ↦ c + a * zero.cylindricalEndLift z)
      (a * deriv zero.cylindricalEndLift w) w :=
  ((zero.hasDerivAt_cylindricalEndLift _).differentiableAt.hasDerivAt.const_mul a).const_add c

/-- If the discs `‖w - c i‖ < ‖a i‖ / 2` are pairwise disjoint and lie in the disc
`‖w‖ ≤ 2 exp (2π)`, then the part `1 ≤ s ≤ R` of every input end lies in the truncation `Σ_R`. -/
theorem add_mul_cylindricalEndLift_mem_puncturedSphereTruncation
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {i : ι} {z : ℂ}
    (h₁ : 1 ≤ z.re) (h₂ : z.re ≤ R) :
    c i + a i * zero.cylindricalEndLift z ∈ puncturedSphereTruncation c a R := by
  set w := c i + a i * zero.cylindricalEndLift z
  have hd := norm_add_mul_cylindricalEndLift_sub (c i) (a i) z
  have hπ := Real.pi_pos
  have hR₁ : Real.exp (-(2 * π * R)) ≤ Real.exp (-(2 * π * z.re)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hR₂ : Real.exp (-(2 * π * z.re)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hR₄ : Real.exp (2 * π) ≤ Real.exp (2 * π * R) := Real.exp_le_exp.2 (by nlinarith)
  have hai := norm_nonneg (a i)
  have hdi : ‖w - c i‖ ≤ ‖a i‖ / 2 := by rw [hd]; nlinarith
  refine ⟨fun j ↦ ?_, ?_⟩
  · rcases eq_or_ne j i with rfl | hji
    · rw [hd]
      gcongr
    · have h := hsep hji.symm
      have htri : ‖c i - c j‖ ≤ ‖w - c i‖ + ‖w - c j‖ := by
        simpa [norm_sub_rev] using norm_sub_le (c i - w) (c j - w)
      have : ‖a j‖ * Real.exp (-(2 * π * R)) ≤ ‖a j‖ :=
        mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.2 (by nlinarith))
      linarith
  · have htri : ‖w‖ ≤ ‖c i‖ + ‖w - c i‖ := by simpa using norm_add_le (c i) (w - c i)
    linarith [hout i]

/-- If the discs `‖w - c i‖ < ‖a i‖ / 2` lie in the disc `‖w‖ ≤ 2 exp (2π)`, then the part
`-R ≤ s ≤ -1` of the output end lies in the truncation `Σ_R`. -/
theorem cylindricalEndLift_inf_mem_puncturedSphereTruncation
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {z : ℂ} (h₁ : -R ≤ z.re)
    (h₂ : z.re ≤ -1) :
    inf.cylindricalEndLift z ∈ puncturedSphereTruncation c a R := by
  have hd := norm_cylindricalEndLift_sub_endCenter inf z
  rw [endCenter_inf, sub_zero, endScale_inf, Complex.norm_ofNat] at hd
  have hπ := Real.pi_pos
  have hlow : 2 * Real.exp (2 * π) ≤ ‖inf.cylindricalEndLift z‖ :=
    two_mul_exp_le_norm_cylindricalEndLift_inf (R := 1) (by linarith) |>.trans_eq' (by ring_nf)
  refine ⟨fun i ↦ ?_, ?_⟩
  · have htri : ‖inf.cylindricalEndLift z‖ ≤ ‖c i‖ + ‖inf.cylindricalEndLift z - c i‖ := by
      simpa using norm_add_le (c i) (inf.cylindricalEndLift z - c i)
    have : ‖a i‖ * Real.exp (-(2 * π * R)) ≤ ‖a i‖ :=
      mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.2 (by nlinarith))
    linarith [hout i]
  · rw [hd]
    gcongr
    nlinarith

/-- For a nonzero scale `a`, a point at distance between `‖a‖ exp (-2πR) / 2` and
`‖a‖ exp (-2πr) / 2` from `c` is the image of a point with `r ≤ s ≤ R` and `t ∈ [-1/2, 1/2)` on the
input end with center `c` and scale `a`. -/
theorem exists_add_mul_cylindricalEndLift_eq {r : ℝ} {c a w : ℂ} (ha : a ≠ 0)
    (h₁ : ‖a‖ * Real.exp (-(2 * π * R)) / 2 ≤ ‖w - c‖)
    (h₂ : ‖w - c‖ ≤ ‖a‖ * Real.exp (-(2 * π * r)) / 2) :
    ∃ z : ℂ, z.re ∈ Icc r R ∧ z.im ∈ Ico (-1 / 2 : ℝ) (1 / 2) ∧
      c + a * zero.cylindricalEndLift z = w := by
  have hapos := norm_pos_iff.2 ha
  set ζ := (w - c) / a
  have hζn : ‖ζ‖ = ‖w - c‖ / ‖a‖ := norm_div _ _
  have hζ : ζ ≠ zero.endCenter := by
    rw [endCenter_zero]
    intro h
    rw [h, norm_zero, eq_comm, div_eq_zero_iff] at hζn
    have : 0 < ‖a‖ * Real.exp (-(2 * π * R)) / 2 := by positivity
    rcases hζn with h | h <;> linarith
  refine ⟨zero.endCoord ζ, ⟨?_, ?_⟩, zero.im_endCoord_mem_Ico ζ, ?_⟩
  · refine le_re_endCoord_of_norm_sub_endCenter_le (by decide) hζ ?_
    rw [endCenter_zero, sub_zero, hζn, div_le_iff₀ hapos]
    linarith
  · refine (re_endCoord_le_iff (by decide) hζ).2 ?_
    rw [endCenter_zero, sub_zero, hζn, le_div_iff₀ hapos]
    linarith
  · rw [cylindricalEndLift_endCoord zero hζ, mul_div_cancel₀ _ ha, add_sub_cancel]

/-- If the discs `‖w - c i‖ < ‖a i‖ / 2` are pairwise disjoint, then a point with `s > 0` on an
input end with nonzero scale is not the center of any input end. -/
theorem add_mul_cylindricalEndLift_ne
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖) {i : ι} (ha : a i ≠ 0)
    {z : ℂ} (hz : 0 < z.re) (j : ι) : c i + a i * zero.cylindricalEndLift z ≠ c j := by
  have hd := norm_add_mul_cylindricalEndLift_sub (c i) (a i) z
  have hapos := norm_pos_iff.2 ha
  have hlt : ‖a i‖ * Real.exp (-(2 * π * z.re)) / 2 < ‖a i‖ / 2 := by
    have : Real.exp (-(2 * π * z.re)) < 1 := Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos])
    nlinarith
  intro h
  rcases eq_or_ne j i with rfl | hji
  · rw [h, sub_self, norm_zero] at hd
    have : 0 < ‖a j‖ * Real.exp (-(2 * π * z.re)) / 2 := by positivity
    linarith
  · rw [h] at hd
    have := hsep hji
    linarith [norm_nonneg (a j), norm_sub_rev (c j) (c i)]

/-- The end lift `z ↦ c + a φ₀(z)` of an input end with nonzero scale `a` is injective on every
horizontal strip `t₀ ≤ Im z < t₀ + 1`. -/
theorem injOn_add_mul_cylindricalEndLift {c a : ℂ} (ha : a ≠ 0) (t₀ : ℝ) :
    InjOn (fun z ↦ c + a * zero.cylindricalEndLift z) {z | z.im ∈ Ico t₀ (t₀ + 1)} :=
  fun _ hp _ hq h ↦ zero.injOn_cylindricalEndLift t₀ hp hq <| by
    simpa only [add_right_inj, mul_right_inj' ha] using h

/-- The end lift `z ↦ c + a φ₀(z)` of an input end with nonzero scale `a`, in real coordinates, is
injective on every horizontal strip `S × [t₀, t₀ + 1)`. -/
theorem injOn_realChart_add_mul_cylindricalEndLift {c a : ℂ} (ha : a ≠ 0) {S : Set ℝ} {t₀ : ℝ} :
    InjOn (realChart fun z ↦ c + a * zero.cylindricalEndLift z) (S ×ˢ Ico t₀ (t₀ + 1)) :=
  injOn_realChart <| (injOn_add_mul_cylindricalEndLift ha t₀).mono <| by
    rintro _ ⟨p, hp, rfl⟩
    simpa using hp.2

end TauCeti.ThricePuncturedSphere
