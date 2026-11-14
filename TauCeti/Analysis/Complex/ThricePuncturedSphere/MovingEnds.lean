/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ThricePuncturedSphere.EndCoordinate

/-!
# Truncations of spheres with moving input ends

A sphere with moving input ends has finitely many input punctures `c i` of `ℂ`, with scales `a i`,
and an output puncture at `∞`. In end coordinates `z = s + i t` the input `i` is given by the end
lift `z ↦ c i + a i φ₀(z)` with `φ₀(z) = exp (-2πz) / 2`, and the output by the end lift
`φ_∞(z) = 2 exp (-2πz)` of the thrice-punctured sphere.

The *truncation* `TauCeti.ThricePuncturedSphere.puncturedSphereTruncation c a R` is the closed disc
`‖w‖ ≤ 2 exp (2πR)` with the open discs `‖w - c i‖ < ‖a i‖ exp (-2πR) / 2` removed
(`TauCeti.ThricePuncturedSphere.puncturedSphereTruncation_eq_closedBall_sdiff_iUnion_ball`): the
part of the sphere where `s ≤ R` on every input end and `-s ≤ R` on the output end. It is compact,
increases with `R` and exhausts the punctured plane. For the inputs `0` and `1` with scales `1` and
`-1` it is the truncation of the thrice-punctured sphere
(`TauCeti.ThricePuncturedSphere.puncturedSphereTruncation_eq_truncation`). It contains the bands
`1 ≤ s ≤ R` of the input ends and `-R ≤ s ≤ -1` of the output end, and every point of it near a
puncture comes from such a band
(`TauCeti.ThricePuncturedSphere.exists_add_mul_cylindricalEndLift_zero_eq`,
`TauCeti.ThricePuncturedSphere.exists_cylindricalEndLift_inf_eq`).

## References

* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Sections 9 and 10, on
  families of punctured discs with strip-like ends.
-/

public section

open Set Real Filter Topology

namespace TauCeti.ThricePuncturedSphere

open Puncture

variable {ι : Type*} {c a : ι → ℂ} {R : ℝ}

/-- The **truncation of a sphere with moving input ends** at height `R`: the closed disc
`‖w‖ ≤ 2 exp (2πR)` with the open discs `‖w - c i‖ < ‖a i‖ exp (-2πR) / 2` about the input
punctures removed. In the end coordinates of the input `i` it is bounded by the circle `s = R`, and
in those of the output by the circle `s = -R`. -/
def puncturedSphereTruncation (c a : ι → ℂ) (R : ℝ) : Set ℂ :=
  {w | ‖w‖ ≤ 2 * Real.exp (2 * π * R) ∧ ∀ i, ‖a i‖ * Real.exp (-(2 * π * R)) / 2 ≤ ‖w - c i‖}

@[simp]
theorem mem_puncturedSphereTruncation {w : ℂ} :
    w ∈ puncturedSphereTruncation c a R ↔
      ‖w‖ ≤ 2 * Real.exp (2 * π * R) ∧ ∀ i, ‖a i‖ * Real.exp (-(2 * π * R)) / 2 ≤ ‖w - c i‖ :=
  Iff.rfl

/-- The truncation is a closed disc with finitely many open discs about the input punctures
removed. -/
theorem puncturedSphereTruncation_eq_closedBall_sdiff_iUnion_ball (c a : ι → ℂ) (R : ℝ) :
    puncturedSphereTruncation c a R = Metric.closedBall 0 (2 * Real.exp (2 * π * R)) \
      ⋃ i, Metric.ball (c i) (‖a i‖ * Real.exp (-(2 * π * R)) / 2) := by
  ext w
  simp [dist_eq_norm]

/-- The truncation of the sphere with the input ends `0` and `1`, with scales `1` and `-1`, is the
truncation of the thrice-punctured sphere. -/
theorem puncturedSphereTruncation_eq_truncation (R : ℝ) :
    puncturedSphereTruncation ![0, 1] ![1, -1] R = truncation R := by
  ext w
  simp [truncation_eq, Fin.forall_fin_two]
  tauto

/-- The truncations increase with the height. -/
theorem puncturedSphereTruncation_mono (c a : ι → ℂ) : Monotone (puncturedSphereTruncation c a) :=
  fun R R' hRR' w hw ↦ ⟨hw.1.trans (by gcongr), fun i ↦ le_trans (by gcongr) (hw.2 i)⟩

/-- The truncation is compact. -/
theorem isCompact_puncturedSphereTruncation (c a : ι → ℂ) (R : ℝ) :
    IsCompact (puncturedSphereTruncation c a R) := by
  have hclosed : IsClosed (puncturedSphereTruncation c a R) := by
    simp only [puncturedSphereTruncation, ofPred_and, ofPred_forall]
    exact (isClosed_le continuous_norm continuous_const).inter
      (isClosed_iInter fun i ↦
        isClosed_le continuous_const (continuous_id.sub continuous_const).norm)
  exact (isCompact_closedBall (0 : ℂ) (2 * Real.exp (2 * π * R))).of_isClosed_subset hclosed
    fun w hw ↦ by simpa using hw.1

/-- The truncation avoids the input punctures. -/
theorem ne_of_mem_puncturedSphereTruncation {i : ι} (ha : a i ≠ 0) {w : ℂ}
    (hw : w ∈ puncturedSphereTruncation c a R) : w ≠ c i := by
  rintro rfl
  have h := hw.2 i
  rw [sub_self, norm_zero] at h
  have : 0 < ‖a i‖ * Real.exp (-(2 * π * R)) / 2 := by
    have := norm_pos_iff.2 ha
    positivity
  linarith

/-- The truncations exhaust the plane with the input punctures removed. -/
theorem iUnion_puncturedSphereTruncation [Finite ι] (ha : ∀ i, a i ≠ 0) :
    ⋃ R, puncturedSphereTruncation c a R = {w : ℂ | ∀ i, w ≠ c i} := by
  ext w
  simp only [mem_iUnion, mem_ofPred_eq]
  refine ⟨fun ⟨R, hw⟩ i ↦ ne_of_mem_puncturedSphereTruncation (ha i) hw, fun hw ↦ ?_⟩
  have h2π : Tendsto (fun R : ℝ ↦ 2 * π * R) atTop atTop :=
    tendsto_id.const_mul_atTop (by positivity)
  have hout : ∀ᶠ R in atTop, ‖w‖ ≤ 2 * Real.exp (2 * π * R) :=
    ((Real.tendsto_exp_atTop.comp h2π).const_mul_atTop two_pos).eventually_ge_atTop ‖w‖
  have hin : ∀ᶠ R in atTop, ∀ i, ‖a i‖ * Real.exp (-(2 * π * R)) / 2 ≤ ‖w - c i‖ := by
    refine eventually_all.2 fun i ↦ ?_
    have h : Tendsto (fun R : ℝ ↦ ‖a i‖ * Real.exp (-(2 * π * R)) / 2) atTop (𝓝 0) := by
      simpa using ((Real.tendsto_exp_neg_atTop_nhds_zero.comp h2π).const_mul ‖a i‖).div_const 2
    exact h.eventually (ge_mem_nhds (norm_pos_iff.2 (sub_ne_zero.2 (hw i))))
  exact (hout.and hin).exists

/-- The input end lift `z ↦ c + a φ₀(z)` sends `z` to a point at distance
`‖a‖ exp (-2π Re z) / 2` from its center `c`. -/
theorem norm_add_mul_cylindricalEndLift_zero_sub (c a z : ℂ) :
    ‖c + a * zero.cylindricalEndLift z - c‖ = ‖a‖ * Real.exp (-(2 * π * z.re)) / 2 := by
  have h := norm_cylindricalEndLift_sub_endCenter zero z
  rw [endCenter_zero, sub_zero, endScale_zero] at h
  rw [add_sub_cancel_left, norm_mul, h]
  norm_num
  ring

/-- The image of the band `1 ≤ s ≤ R` of an input end lies in the truncation. -/
theorem add_mul_cylindricalEndLift_zero_mem_puncturedSphereTruncation
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {i : ι} {z : ℂ} (h₁ : 1 ≤ z.re)
    (hR : z.re ≤ R) : c i + a i * zero.cylindricalEndLift z ∈ puncturedSphereTruncation c a R := by
  set w := c i + a i * zero.cylindricalEndLift z
  have hπ := Real.pi_pos
  have hn := norm_add_mul_cylindricalEndLift_zero_sub (c i) (a i) z
  have he₁ : Real.exp (-(2 * π * z.re)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have heR : Real.exp (-(2 * π * R)) ≤ Real.exp (-(2 * π * z.re)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hwi : ‖w - c i‖ ≤ ‖a i‖ / 2 := by
    rw [hn]
    nlinarith [norm_nonneg (a i)]
  refine ⟨?_, fun j => ?_⟩
  · have h₂ : Real.exp (2 * π) ≤ Real.exp (2 * π * R) := Real.exp_le_exp.2 (by nlinarith)
    linarith [hout i, norm_le_norm_add_norm_sub' w (c i)]
  · rcases eq_or_ne j i with rfl | hji
    · rw [hn]
      nlinarith [norm_nonneg (a j)]
    · have h₁ := hsep hji.symm
      have h₂ : ‖c i - c j‖ ≤ ‖w - c i‖ + ‖w - c j‖ := by
        simpa only [dist_eq_norm] using dist_triangle_left (c i) (c j) w
      nlinarith [norm_nonneg (a j)]

/-- The image of the band `-R ≤ s ≤ -1` of the output end lies in the truncation. -/
theorem cylindricalEndLift_inf_mem_puncturedSphereTruncation
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {z : ℂ} (hR : -R ≤ z.re)
    (h₁ : z.re ≤ -1) : inf.cylindricalEndLift z ∈ puncturedSphereTruncation c a R := by
  have hπ := Real.pi_pos
  have hn := norm_cylindricalEndLift_sub_endCenter inf z
  rw [endCenter_inf, sub_zero, endScale_inf, Complex.norm_ofNat] at hn
  have h₂ : Real.exp (2 * π) ≤ Real.exp (-(2 * π * z.re)) := Real.exp_le_exp.2 (by nlinarith)
  refine ⟨?_, fun i => ?_⟩
  · rw [hn]
    have : Real.exp (-(2 * π * z.re)) ≤ Real.exp (2 * π * R) := Real.exp_le_exp.2 (by nlinarith)
    linarith
  · have heR : Real.exp (-(2 * π * R)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have h₃ := norm_sub_norm_le (inf.cylindricalEndLift z) (c i)
    nlinarith [hout i, norm_nonneg (a i)]

/-- A point of the truncation in the disc `‖w - c‖ ≤ ‖a‖ exp (-2π) / 2` of the input end with
center `c` and scale `a` is the image of a point of the rectangle `[1, R] × [-1/2, 1/2)`. -/
theorem exists_add_mul_cylindricalEndLift_zero_eq {c a w : ℂ} (ha : a ≠ 0) {R : ℝ}
    (hw₀ : ‖a‖ * Real.exp (-(2 * π * R)) / 2 ≤ ‖w - c‖)
    (hw₁ : ‖w - c‖ ≤ ‖a‖ * Real.exp (-(2 * π)) / 2) :
    ∃ z : ℂ, (z.re ∈ Icc 1 R ∧ z.im ∈ Ico (-1 / 2 : ℝ) (1 / 2)) ∧
      c + a * zero.cylindricalEndLift z = w := by
  have hna := norm_pos_iff.2 ha
  set w' := (w - c) / a
  have hw' : ‖w'‖ = ‖w - c‖ / ‖a‖ := norm_div _ _
  have hw'₀ : 0 < ‖w'‖ := by
    rw [hw']
    have : 0 < ‖a‖ * Real.exp (-(2 * π * R)) / 2 := by positivity
    exact div_pos (by linarith) hna
  have hw'0 : w' ≠ zero.endCenter := by
    rw [endCenter_zero]
    exact norm_pos_iff.1 hw'₀
  refine ⟨zero.endCoord w', ⟨⟨?_, ?_⟩, zero.im_endCoord_mem_Ico w'⟩, ?_⟩
  · refine le_re_endCoord_of_norm_sub_endCenter_le (by decide) hw'0 ?_
    rw [endCenter_zero, sub_zero, hw', div_le_iff₀ hna, mul_one]
    linarith
  · rw [re_endCoord_le_iff (by decide) hw'0, endCenter_zero, sub_zero, hw', le_div_iff₀ hna]
    linarith
  · rw [zero.cylindricalEndLift_endCoord hw'0, mul_div_cancel₀ _ ha, add_sub_cancel]

/-- A point of the truncation off the disc `‖w‖ < 2 exp (2π)` is the image under the output end
lift of a point of the rectangle `[-R, -1] × [-1/2, 1/2)`. -/
theorem exists_cylindricalEndLift_inf_eq {w : ℂ} {R : ℝ}
    (hw₀ : 2 * Real.exp (2 * π) ≤ ‖w‖) (hw₁ : ‖w‖ ≤ 2 * Real.exp (2 * π * R)) :
    ∃ z : ℂ, (z.re ∈ Icc (-R) (-1) ∧ z.im ∈ Ico (-1 / 2 : ℝ) (1 / 2)) ∧
      inf.cylindricalEndLift z = w := by
  have hR : 0 ≤ R := by
    have h := Real.exp_le_exp.1 (by linarith : Real.exp (2 * π) ≤ Real.exp (2 * π * R))
    nlinarith [Real.pi_pos]
  have hw0 : 0 < ‖w‖ := lt_of_lt_of_le (by positivity) hw₀
  have hw : w ≠ inf.endCenter := by
    rw [endCenter_inf]
    exact norm_pos_iff.1 hw0
  refine ⟨inf.endCoord w, ⟨⟨?_, ?_⟩, inf.im_endCoord_mem_Ico w⟩,
    inf.cylindricalEndLift_endCoord hw⟩
  · linarith [neg_re_endCoord_inf_le hR hw₁]
  · exact re_endCoord_inf_le_neg (by rwa [mul_one])

end TauCeti.ThricePuncturedSphere
