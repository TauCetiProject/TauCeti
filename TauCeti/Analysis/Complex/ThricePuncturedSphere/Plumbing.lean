/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ThricePuncturedSphere.EndCoordinate

/-!
# Plumbing two thrice-punctured spheres along a neck

Composing two pair-of-pants operations glues the negative end at `∞` of one thrice-punctured
sphere `S' = ℂ ∖ {0, 1}` to a positive end `q ∈ {0, 1}` of another copy `S`. With neck length
`L > 0` and the asymptotic markers of the two ends matched, the gluing identifies the point with
end coordinate `z` on the end at `∞` of `S'`, for `-L < Re z < 0`, with the point with end
coordinate `z + L` on the end `q` of `S`, for `0 < Re (z + L) < L`.

Since every end lift is a scaled exponential about its center
(`TauCeti.ThricePuncturedSphere.Puncture.cylindricalEndLift_eq`), this identification is the
restriction of the affine map `ψ_{q,L}(w) = c_q + b_q e^{-2πL} w / 2`
(`TauCeti.ThricePuncturedSphere.Puncture.plumbingMap`), which carries the truncated
part `Re z > -L` of `S'`, in the end coordinate at `∞`, into the part `Re z > 0` of the end `q`
of `S` (`TauCeti.ThricePuncturedSphere.Puncture.re_endCoord_plumbingMap`). The glued surface is
therefore the four-punctured sphere `ℂ ∖ {0, 1, ψ_{q,L}(1)}`: the two inputs of `S'` sit at
`ψ_{q,L}(0) = c_q` and at `ψ_{q,L}(1)`, and the remaining punctures of `S` are unchanged. For
`q = 0` the new puncture is `e^{-2πL}/4`, for `q = 1` it is `1 - e^{-2πL}/4`; as `L → ∞` it
collides with `c_q`, and the four-punctured sphere breaks into the two pairs of pants.

## Main definitions

* `TauCeti.ThricePuncturedSphere.Puncture.plumbingFactor q L`: the factor `b_q e^{-2πL} / 2`.
* `TauCeti.ThricePuncturedSphere.Puncture.plumbingMap q L`: the plumbing map
  `w ↦ c_q + b_q e^{-2πL} w / 2`.

## Main results

* `TauCeti.ThricePuncturedSphere.Puncture.cylindricalEndLift_add_ofReal`: the gluing law: the end
  lift of `q` at `z + L` is the plumbing map applied to the end lift of `∞` at `z`.
* `TauCeti.ThricePuncturedSphere.Puncture.endCoord_plumbingMap`: in end coordinates the plumbing
  map is the translation `z ↦ z + L`, exactly, including the angular coordinate.
* `TauCeti.ThricePuncturedSphere.Puncture.endAngularForm_plumbingMap`: the plumbing map pulls the
  angular form `dt` of the end `q` back to the angular form of the end at `∞`.
* `TauCeti.ThricePuncturedSphere.Puncture.plumbingMap_image_union`: the image of the part
  `Re z > -L` of `S'` and the part `Re z < L` of `S` cover exactly the four-punctured sphere
  `ℂ ∖ {0, 1, ψ_{q,L}(1)}`.
* `TauCeti.ThricePuncturedSphere.Puncture.plumbingMap_image_inter`: the two pieces overlap
  exactly in the image of the neck `-L < Re z < 0`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 10.9, on
  gluing punctured Riemann surfaces along cylindrical ends.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 9, on gluing surfaces with
  strip-like ends with a gluing length.
-/

public noncomputable section

open Set Real

namespace TauCeti.ThricePuncturedSphere.Puncture

/-- The scale factor `b_q e^{-2πL} / 2` of the plumbing map of neck length `L` at the end `q`. -/
def plumbingFactor (q : Puncture) (L : ℝ) : ℂ :=
  q.endScale * Complex.exp (-(2 * (π : ℂ)) * L) / 2

/-- The plumbing map `w ↦ c_q + b_q e^{-2πL} w / 2` of neck length `L` at the end `q`. It sends
the point with end coordinate `z` on the end at `∞` to the point with end coordinate `z + L` on
the end `q` (`cylindricalEndLift_add_ofReal`). -/
def plumbingMap (q : Puncture) (L : ℝ) (w : ℂ) : ℂ :=
  q.endCenter + q.plumbingFactor L * w

theorem plumbingFactor_def (q : Puncture) (L : ℝ) :
    q.plumbingFactor L = q.endScale * Complex.exp (-(2 * (π : ℂ)) * L) / 2 :=
  (rfl)

theorem plumbingMap_apply (q : Puncture) (L : ℝ) (w : ℂ) :
    q.plumbingMap L w = q.endCenter + q.plumbingFactor L * w :=
  (rfl)

theorem plumbingFactor_ne_zero (q : Puncture) (L : ℝ) : q.plumbingFactor L ≠ 0 :=
  div_ne_zero (mul_ne_zero q.endScale_ne_zero (Complex.exp_ne_zero _)) two_ne_zero

/-- The plumbing factor is the end scale times the positive real number `e^{-2πL} / 2`. -/
theorem plumbingFactor_eq_mul_ofReal (q : Puncture) (L : ℝ) :
    q.plumbingFactor L = q.endScale * ((Real.exp (-(2 * π * L)) / 2 : ℝ) : ℂ) := by
  rw [plumbingFactor_def, Complex.ofReal_div, Complex.ofReal_exp]
  push_cast
  ring_nf

/-- The plumbing map scales distances by `‖b_q‖ e^{-2πL} / 2`. -/
theorem norm_plumbingFactor (q : Puncture) (L : ℝ) :
    ‖q.plumbingFactor L‖ = ‖q.endScale‖ * Real.exp (-(2 * π * L)) / 2 := by
  rw [plumbingFactor_eq_mul_ofReal, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), mul_div_assoc]

/-- The first input of the inserted sphere sits at the center of the end it is plumbed into. -/
@[simp]
theorem plumbingMap_zero (q : Puncture) (L : ℝ) : q.plumbingMap L 0 = q.endCenter := by
  rw [plumbingMap_apply, mul_zero, add_zero]

theorem plumbingMap_injective (q : Puncture) (L : ℝ) : Function.Injective (q.plumbingMap L) :=
  fun _ _ h => mul_left_cancel₀ (q.plumbingFactor_ne_zero L) (add_left_cancel h)

/-- The plumbing map is affine with derivative the plumbing factor. -/
theorem hasDerivAt_plumbingMap (q : Puncture) (L : ℝ) (w : ℂ) :
    HasDerivAt (q.plumbingMap L) (q.plumbingFactor L) w := by
  have h := ((hasDerivAt_id w).const_mul (q.plumbingFactor L)).const_add q.endCenter
  rw [mul_one] at h
  exact h

@[simp]
theorem deriv_plumbingMap (q : Puncture) (L : ℝ) (w : ℂ) :
    deriv (q.plumbingMap L) w = q.plumbingFactor L :=
  (q.hasDerivAt_plumbingMap L w).deriv

/-- **The gluing law.** The point with end coordinate `z + L` on the end `q` is the image under
the plumbing map of the point with end coordinate `z` on the end at `∞`. -/
theorem cylindricalEndLift_add_ofReal (q : Puncture) (L : ℝ) (z : ℂ) :
    q.cylindricalEndLift (z + L) = q.plumbingMap L (inf.cylindricalEndLift z) := by
  rw [cylindricalEndLift_eq, cylindricalEndLift_eq, plumbingMap_apply, plumbingFactor_def,
    endCenter_inf, endScale_inf, mul_add, Complex.exp_add]
  ring

/-- The chain rule for the gluing law: the derivative of the end lift of `q` at `z + L` is the
plumbing factor times the derivative of the end lift of `∞` at `z`. -/
theorem deriv_cylindricalEndLift_add_ofReal (q : Puncture) (L : ℝ) (z : ℂ) :
    deriv q.cylindricalEndLift (z + L) =
      q.plumbingFactor L * deriv inf.cylindricalEndLift z := by
  rw [deriv_cylindricalEndLift, deriv_cylindricalEndLift, cylindricalEndLift_add_ofReal,
    plumbingMap_apply, endCenter_inf]
  ring

/-- The plumbing map undone: the point `(w - c_q) / ψ'` is sent to `w`. -/
theorem plumbingMap_sub_endCenter_div (q : Puncture) (L : ℝ) (w : ℂ) :
    q.plumbingMap L ((w - q.endCenter) / q.plumbingFactor L) = w := by
  rw [plumbingMap_apply, mul_div_cancel₀ _ (q.plumbingFactor_ne_zero L), add_sub_cancel]

/-- The plumbing map undone: `(ψ(w) - c_q) / ψ' = w`. -/
@[simp]
theorem plumbingMap_sub_endCenter_div_plumbingFactor (q : Puncture) (L : ℝ) (w : ℂ) :
    (q.plumbingMap L w - q.endCenter) / q.plumbingFactor L = w := by
  rw [plumbingMap_apply, add_sub_cancel_left, mul_div_cancel_left₀ _ (q.plumbingFactor_ne_zero L)]

/-- The plumbing map displaces points from the center of the end by the plumbing factor. -/
private theorem plumbingMap_sub_endCenter_div_endScale (q : Puncture) (L : ℝ) (w : ℂ) :
    (q.plumbingMap L w - q.endCenter) / q.endScale =
      ((Real.exp (-(2 * π * L)) : ℝ) : ℂ) * ((w - inf.endCenter) / inf.endScale) := by
  rw [plumbingMap_apply, add_sub_cancel_left, plumbingFactor_eq_mul_ofReal, endCenter_inf,
    endScale_inf, sub_zero]
  field_simp [q.endScale_ne_zero]
  push_cast
  ring

/-- **The plumbing map in end coordinates.** Away from the puncture at `0`, the end coordinate of
the end `q` at the image of a point is its end coordinate on the end at `∞` plus `L`. No integer
shift of the angular coordinate occurs, since the plumbing factor is a positive multiple of the
end scale. -/
theorem endCoord_plumbingMap (q : Puncture) (L : ℝ) {w : ℂ} (hw : w ≠ 0) :
    q.endCoord (q.plumbingMap L w) = inf.endCoord w + L := by
  have h : (w - inf.endCenter) / inf.endScale ≠ 0 := by simp [hw]
  have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [endCoord_def, endCoord_def, plumbingMap_sub_endCenter_div_endScale,
    Complex.log_ofReal_mul (Real.exp_pos _) h, Real.log_exp]
  field_simp
  push_cast
  ring

/-- The longitudinal coordinate of the end `q` at the image of a point is its longitudinal
coordinate on the end at `∞` plus `L`. -/
theorem re_endCoord_plumbingMap (q : Puncture) (L : ℝ) {w : ℂ} (hw : w ≠ 0) :
    (q.endCoord (q.plumbingMap L w)).re = (inf.endCoord w).re + L := by
  rw [endCoord_plumbingMap q L hw, Complex.add_re, Complex.ofReal_re]

/-- The point `(w - c_q) / ψ'` undoing the plumbing map is not the puncture `0` unless `w` is the
center of the end. -/
theorem sub_endCenter_div_plumbingFactor_ne_zero (q : Puncture) (L : ℝ) {w : ℂ}
    (hw : w ≠ q.endCenter) : (w - q.endCenter) / q.plumbingFactor L ≠ 0 :=
  div_ne_zero (sub_ne_zero.2 hw) (q.plumbingFactor_ne_zero L)

/-- Undoing the plumbing map lowers the longitudinal coordinate by `L`: the end coordinate at `∞`
of `(w - c_q) / ψ'` is that of `w` on the end `q`, minus `L`. -/
theorem re_endCoord_inf_sub_endCenter_div (q : Puncture) (L : ℝ) {w : ℂ}
    (hw : w ≠ q.endCenter) :
    (inf.endCoord ((w - q.endCenter) / q.plumbingFactor L)).re = (q.endCoord w).re - L := by
  have h := re_endCoord_plumbingMap q L (q.sub_endCenter_div_plumbingFactor_ne_zero L hw)
  rw [plumbingMap_sub_endCenter_div] at h
  linarith

/-- **The plumbing map preserves the angular forms.** It pulls the angular form `dt` of the end
`q` back to the angular form `dt` of the end at `∞`. -/
theorem endAngularForm_plumbingMap (q : Puncture) (L : ℝ) (w v : ℂ) :
    q.endAngularForm (q.plumbingMap L w) (deriv (q.plumbingMap L) w * v) =
      inf.endAngularForm w v := by
  have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hc := q.plumbingFactor_ne_zero L
  rw [endAngularForm_apply, endAngularForm_apply, deriv_plumbingMap, plumbingMap_apply,
    add_sub_cancel_left, endCenter_inf, sub_zero]
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · congr 1
    field_simp

/-- **The plumbed four-punctured sphere.** For a positive end `q` and a neck length `L > 0`, the
image under the plumbing map of the part `Re z > -L` of the inserted thrice-punctured sphere,
measured in the end coordinate at `∞`, together with the part `Re z < L` of the receiving one,
measured in the end coordinate of `q`, is the four-punctured sphere `ℂ ∖ {0, 1, ψ_{q,L}(1)}`. -/
theorem plumbingMap_image_union {q : Puncture} (hq : q ≠ inf) {L : ℝ} (hL : 0 < L) :
    q.plumbingMap L '' {w | (w ≠ 0 ∧ w ≠ 1) ∧ -L < (inf.endCoord w).re} ∪
        {w | (w ≠ 0 ∧ w ≠ 1) ∧ (q.endCoord w).re < L} =
      {w | (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1} := by
  ext w
  simp only [mem_union, mem_image, mem_ofPred_eq]
  constructor
  · rintro (⟨w', ⟨⟨hw0, hw1⟩, hw'⟩, rfl⟩ | ⟨hw, hwL⟩)
    · -- The image lies on the part `Re z > 0` of the end `q`, away from both finite punctures.
      refine ⟨q.ne_zero_and_ne_one_of_endSign_mul_re_endCoord_pos ?_,
        (q.plumbingMap_injective L).ne hw1⟩
      rw [endSign_eq_one hq, one_mul, re_endCoord_plumbingMap q L hw0]
      linarith
    · refine ⟨hw, fun h => ?_⟩
      rw [h, re_endCoord_plumbingMap q L one_ne_zero] at hwL
      linarith [re_endCoord_inf_one_pos]
  · rintro ⟨hw, hw1⟩
    rcases lt_or_ge (q.endCoord w).re L with hwL | hwL
    · exact Or.inr ⟨hw, hwL⟩
    · -- Deep in the end `q`, the point is the image of `(w - c_q) / ψ'`.
      have hc : w ≠ q.endCenter :=
        q.ne_endCenter_of_re_endCoord_ne_zero (by linarith : 0 < (q.endCoord w).re).ne'
      have hw' := q.plumbingMap_sub_endCenter_div L w
      refine Or.inl ⟨_, ⟨⟨q.sub_endCenter_div_plumbingFactor_ne_zero L hc,
        fun h => hw1 (by rw [← hw', h])⟩, ?_⟩, hw'⟩
      rw [re_endCoord_inf_sub_endCenter_div q L hc]
      linarith

/-- **The neck of the plumbing.** The two pieces of `plumbingMap_image_union` overlap exactly in
the image of the neck `-L < Re z < 0` of the end at `∞` of the inserted sphere, which is the part
`0 < Re z < L` of the end `q` (`re_endCoord_plumbingMap`). -/
theorem plumbingMap_image_inter {q : Puncture} (hq : q ≠ inf) (L : ℝ) :
    q.plumbingMap L '' {w | (w ≠ 0 ∧ w ≠ 1) ∧ -L < (inf.endCoord w).re} ∩
        {w | (w ≠ 0 ∧ w ≠ 1) ∧ (q.endCoord w).re < L} =
      q.plumbingMap L '' {w | w ≠ 0 ∧ -L < (inf.endCoord w).re ∧ (inf.endCoord w).re < 0} := by
  ext w
  simp only [mem_inter_iff, mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨w', ⟨⟨hw0, -⟩, hw'⟩, rfl⟩, -, hwL⟩
    rw [re_endCoord_plumbingMap q L hw0] at hwL
    exact ⟨w', ⟨hw0, hw', by linarith⟩, rfl⟩
  · rintro ⟨w', ⟨hw0, hw', hw'0⟩, rfl⟩
    -- On the neck `Re z < 0` of the end at `∞` the point is far from `0` and `1`.
    have hinf := inf.ne_zero_and_ne_one_of_endSign_mul_re_endCoord_pos (w := w')
      (by rw [endSign_inf]; linarith)
    have hre := re_endCoord_plumbingMap q L hw0
    refine ⟨⟨w', ⟨hinf, hw'⟩, rfl⟩,
      q.ne_zero_and_ne_one_of_endSign_mul_re_endCoord_pos (by rw [endSign_eq_one hq]; linarith),
      by linarith⟩

end TauCeti.ThricePuncturedSphere.Puncture
