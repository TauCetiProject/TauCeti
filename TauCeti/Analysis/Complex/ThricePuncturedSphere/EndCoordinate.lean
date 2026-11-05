/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ThricePuncturedSphere.CylindricalEnds
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Analysis.SpecialFunctions.Log.DivLeIff
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Logarithmic coordinates on the cylindrical ends of the thrice-punctured sphere

Each end lift `cylindricalEndLift q` of the thrice-punctured sphere is a scaled exponential
`z ↦ c_q + b_q exp (-2πz)` (`Puncture.cylindricalEndLift_eq`), with `(c_q, b_q)` equal to
`(0, 1/2)`, `(1, -1/2)` and `(0, 2)` at `0`, `1` and `∞`. A logarithm inverts it: the end
coordinate `ζ_q(w) = -log ((w - c_q) / b_q) / (2π)` satisfies `cylindricalEndLift q (ζ_q w) = w`
for `w ≠ c_q` (`Puncture.cylindricalEndLift_endCoord`), and recovers a cylinder point `z` up to
an integer multiple of `i` (`Puncture.exists_endCoord_cylindricalEndLift`), so the end lift is
injective on the strip `-1/2 ≤ Im z < 1/2` (`Puncture.injOn_cylindricalEndLift`). Its real part
is the longitudinal coordinate `s`, a smooth function away from `c_q`
(`Puncture.contDiffAt_re_endCoord`). Its imaginary part is the angular coordinate `t`, with values
in `[-1/2, 1/2)` (`Puncture.im_endCoord_mem_Ico`); it jumps by `1` across a ray, so only
period-one functions of it are smooth (`Puncture.contMDiffAt_comp_im_endCoord`). The angular
one-form `dt` of the end is `v ↦ Im (v / (-2π (w - c_q)))` (`Puncture.endAngularForm`), and it
pulls back to `dt` along the end lift (`Puncture.endAngularForm_cylindricalEndLift`).

The ends at `0` and `1` are positive, parameterized by `s > 0`, and the end at `∞` is negative,
parameterized by `s < 0`; `Puncture.endSign` records the sign. Points with positive signed
longitudinal coordinate lie in the standard punctured neighborhood of the puncture
(`Puncture.exists_mem_neighborhood_cylindricalEndLift`), hence in the thrice-punctured sphere
(`Puncture.cylindricalEndLift_ne_zero_and_ne_one`), and the three ends have disjoint images
(`Puncture.cylindricalEndLift_ne_cylindricalEndLift`), so a point has positive signed longitudinal
coordinate on at most one end (`Puncture.endSign_mul_re_endCoord_nonpos`). Bounding all three signed
longitudinal coordinates by `R` cuts out the truncation `S_R` of the thrice-punctured sphere
(`TauCeti.ThricePuncturedSphere.truncation`), a compact set
(`TauCeti.ThricePuncturedSphere.isCompact_truncation`) over which integrals of data on `S` are
taken.

These coordinates are what is needed to install data prescribed on the ends, such as the
Hamiltonian terms `H(t) dt` of Floer perturbation data, as smooth data on the punctured sphere.
See Dusa McDuff and Dietmar Salamon, *J-holomorphic Curves and Symplectic Topology*, Chapter 4,
for the cylindrical end coordinates of a punctured Riemann surface.
-/

public noncomputable section

open Set Real Manifold

namespace TauCeti.ThricePuncturedSphere.Puncture

/-- The sign of an end: `1` at the positive ends at `0` and `1`, parameterized by `s > 0`, and
`-1` at the negative end at `∞`, parameterized by `s < 0`. -/
def endSign : Puncture → ℝ
  | .zero => 1
  | .one => 1
  | .inf => -1

@[simp] theorem endSign_zero : zero.endSign = 1 := (rfl)

@[simp] theorem endSign_one : one.endSign = 1 := (rfl)

@[simp] theorem endSign_inf : inf.endSign = -1 := (rfl)

/-- The sign of an end has absolute value one. -/
@[simp] theorem abs_endSign (q : Puncture) : |q.endSign| = 1 := by
  cases q <;> simp

/-- The sign of an end is `1` or `-1`. -/
theorem endSign_eq_one_or_eq_neg_one (q : Puncture) : q.endSign = 1 ∨ q.endSign = -1 := by
  cases q <;> simp

/-- The center of an end lift: `cylindricalEndLift q z - q.endCenter` is a multiple of
`exp (-2πz)`. It is `0` at the ends at `0` and `∞`, and `1` at the end at `1`. -/
def endCenter : Puncture → ℂ
  | .zero => 0
  | .one => 1
  | .inf => 0

@[simp] theorem endCenter_zero : zero.endCenter = 0 := (rfl)

@[simp] theorem endCenter_one : one.endCenter = 1 := (rfl)

@[simp] theorem endCenter_inf : inf.endCenter = 0 := (rfl)

/-- The scale of an end lift: `cylindricalEndLift q z = q.endCenter + q.endScale * exp (-2πz)`. -/
def endScale : Puncture → ℂ
  | .zero => 1 / 2
  | .one => -(1 / 2)
  | .inf => 2

@[simp] theorem endScale_zero : zero.endScale = 1 / 2 := (rfl)

@[simp] theorem endScale_one : one.endScale = -(1 / 2) := (rfl)

@[simp] theorem endScale_inf : inf.endScale = 2 := (rfl)

/-- The end lifts are nonconstant exponentials. -/
theorem endScale_ne_zero (q : Puncture) : q.endScale ≠ 0 := by
  cases q <;> norm_num

/-- The ends at the finite punctures have scale of norm `1 / 2`. -/
theorem norm_endScale {q : Puncture} (hq : q ≠ inf) : ‖q.endScale‖ = 1 / 2 := by
  cases q <;> simp_all

/-- The ends other than the one at `∞` are positive. -/
theorem endSign_eq_one {q : Puncture} (hq : q ≠ inf) : q.endSign = 1 := by
  cases q <;> simp_all

/-- The end centers are the two finite punctures, so they lie outside the punctured sphere. -/
theorem endCenter_eq_zero_or_eq_one (q : Puncture) : q.endCenter = 0 ∨ q.endCenter = 1 := by
  cases q <;> simp

/-- Points of the thrice-punctured sphere are not end centers. -/
theorem ne_endCenter {w : ℂ} (hw : w ≠ 0 ∧ w ≠ 1) (q : Puncture) : w ≠ q.endCenter := by
  rcases q.endCenter_eq_zero_or_eq_one with h | h <;> rw [h]
  exacts [hw.1, hw.2]

/-- Every end lift is a scaled exponential about its center. -/
theorem cylindricalEndLift_eq (q : Puncture) (z : ℂ) :
    q.cylindricalEndLift z = q.endCenter + q.endScale * Complex.exp (-(2 * (π : ℂ)) * z) := by
  cases q <;> simp <;> ring

/-- In polar form, the end lift traverses the circle of radius `‖b_q‖ exp (-2πs)` about the
center `c_q` of the end clockwise, starting at the argument of the scale `b_q`. -/
theorem cylindricalEndLift_ofReal_add_ofReal_mul_I (q : Puncture) (x t : ℝ) :
    q.cylindricalEndLift (x + t * Complex.I) =
      circleMap q.endCenter (‖q.endScale‖ * Real.exp (-(2 * π * x)))
        (Complex.arg q.endScale - 2 * π * t) := by
  rw [cylindricalEndLift_eq, circleMap]
  congr 1
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I q.endScale]
  push_cast
  simp only [mul_assoc, ← Complex.exp_add]
  ring_nf

/-- The derivative of an end lift at `z` is `-2π` times the displacement of its value from the
center of the end. -/
theorem deriv_cylindricalEndLift (q : Puncture) (z : ℂ) :
    deriv q.cylindricalEndLift z = -(2 * π * (q.cylindricalEndLift z - q.endCenter)) := by
  rw [(q.hasDerivAt_cylindricalEndLift z).deriv]
  cases q <;> simp <;> ring

/-- An end lift never takes the value of the center of its end. -/
theorem cylindricalEndLift_sub_endCenter_ne_zero (q : Puncture) (z : ℂ) :
    q.cylindricalEndLift z - q.endCenter ≠ 0 := by
  rw [cylindricalEndLift_eq, add_sub_cancel_left]
  exact mul_ne_zero q.endScale_ne_zero (Complex.exp_ne_zero _)

/-- The logarithmic end coordinate `ζ_q(w) = -log ((w - c_q) / b_q) / (2π)`. It inverts the end
lift (`cylindricalEndLift_endCoord`); its real part is the longitudinal coordinate and its
imaginary part an angular coordinate, determined by the point only modulo `1`. -/
def endCoord (q : Puncture) (w : ℂ) : ℂ :=
  -Complex.log ((w - q.endCenter) / q.endScale) / (2 * π)

theorem endCoord_def (q : Puncture) (w : ℂ) :
    q.endCoord w = -Complex.log ((w - q.endCenter) / q.endScale) / (2 * π) :=
  (rfl)

/-- The longitudinal coordinate of a point of an end. -/
theorem re_endCoord (q : Puncture) (w : ℂ) :
    (q.endCoord w).re = -Real.log ‖(w - q.endCenter) / q.endScale‖ / (2 * π) := by
  rw [endCoord, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_re,
    Complex.neg_re, Complex.log_re]

/-- The center of an end has longitudinal coordinate `0`, the junk value of the logarithm of
`0`. -/
@[simp]
theorem re_endCoord_endCenter (q : Puncture) : (q.endCoord q.endCenter).re = 0 := by
  simp [re_endCoord]

/-- On the end at `∞` the point `1` has longitudinal coordinate `log 2 / (2π) > 0`. -/
theorem re_endCoord_inf_one_pos : 0 < (inf.endCoord 1).re := by
  rw [re_endCoord, endCenter_inf, endScale_inf, sub_zero]
  have : ‖(1 : ℂ) / 2‖ = 2⁻¹ := by norm_num
  rw [this, Real.log_inv, neg_neg]
  exact div_pos (Real.log_pos one_lt_two) (by positivity)

/-- A point with nonzero longitudinal coordinate is not the center of the end. -/
theorem ne_endCenter_of_re_endCoord_ne_zero (q : Puncture) {w : ℂ}
    (h : (q.endCoord w).re ≠ 0) : w ≠ q.endCenter := by
  rintro rfl
  exact h q.re_endCoord_endCenter

/-- The angular coordinate of a point of an end. -/
theorem im_endCoord (q : Puncture) (w : ℂ) :
    (q.endCoord w).im = -Complex.arg ((w - q.endCenter) / q.endScale) / (2 * π) := by
  rw [endCoord, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_im,
    Complex.neg_im, Complex.log_im]

/-- The end coordinate is a right inverse of the end lift away from the center of the end. -/
theorem cylindricalEndLift_endCoord (q : Puncture) {w : ℂ} (hw : w ≠ q.endCenter) :
    q.cylindricalEndLift (q.endCoord w) = w := by
  have h : (w - q.endCenter) / q.endScale ≠ 0 :=
    div_ne_zero (sub_ne_zero.2 hw) q.endScale_ne_zero
  have hπ : 2 * (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [cylindricalEndLift_eq, endCoord, neg_div, neg_mul_neg, mul_div_cancel₀ _ hπ,
    Complex.exp_log h]
  field_simp [q.endScale_ne_zero]
  ring

/-- The end coordinate recovers a cylinder point from its image under the end lift, up to an
integer shift of the angular coordinate. -/
theorem exists_endCoord_cylindricalEndLift (q : Puncture) (z : ℂ) :
    ∃ k : ℤ, q.endCoord (q.cylindricalEndLift z) = z + k * Complex.I := by
  obtain ⟨n, hn⟩ := Complex.log_exp_exists (-(2 * (π : ℂ)) * z)
  refine ⟨-n, ?_⟩
  have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [endCoord, cylindricalEndLift_eq, add_sub_cancel_left,
    mul_div_cancel_left₀ _ q.endScale_ne_zero, hn]
  field_simp
  push_cast
  ring

/-- The angular coordinate takes values in the period `[-1/2, 1/2)`. -/
theorem im_endCoord_mem_Ico (q : Puncture) (w : ℂ) :
    (q.endCoord w).im ∈ Ico (-1 / 2 : ℝ) (1 / 2) := by
  have h₁ := Complex.neg_pi_lt_arg ((w - q.endCenter) / q.endScale)
  have h₂ := Complex.arg_le_pi ((w - q.endCenter) / q.endScale)
  have hπ := Real.pi_pos
  rw [im_endCoord, mem_Ico, le_div_iff₀ (by positivity), div_lt_iff₀ (by positivity)]
  constructor <;> linarith

/-- An end lift is injective on every horizontal strip of height one whose angular coordinate
ranges over `[-1/2, 1/2)`. -/
theorem injOn_cylindricalEndLift (q : Puncture) :
    InjOn q.cylindricalEndLift {z | z.im ∈ Ico (-1 / 2 : ℝ) (1 / 2)} := by
  intro a ha b hb hab
  replace ha : -1 / 2 ≤ a.im ∧ a.im < 1 / 2 := ha
  replace hb : -1 / 2 ≤ b.im ∧ b.im < 1 / 2 := hb
  rw [cylindricalEndLift_eq, cylindricalEndLift_eq, add_right_inj,
    mul_right_inj' q.endScale_ne_zero] at hab
  have hπ := Real.pi_pos
  have him (z : ℂ) : (-(2 * (π : ℂ)) * z).im = -(2 * π) * z.im := by simp
  have h := Complex.exp_inj_of_neg_pi_lt_of_le_pi (by rw [him]; nlinarith)
    (by rw [him]; nlinarith) (by rw [him]; nlinarith) (by rw [him]; nlinarith) hab
  exact mul_left_cancel₀ (by simp [Real.pi_ne_zero]) h

/-- The longitudinal coordinate is smooth away from the center of the end. -/
theorem contDiffAt_re_endCoord (q : Puncture) {w : ℂ} (hw : w ≠ q.endCenter)
    {n : WithTop ℕ∞} : ContDiffAt ℝ n (fun w => (q.endCoord w).re) w := by
  simp_rw [re_endCoord]
  have h₀ : (w - q.endCenter) / q.endScale ≠ 0 :=
    div_ne_zero (sub_ne_zero.2 hw) q.endScale_ne_zero
  have hu : ContDiffAt ℝ n (fun w : ℂ => (w - q.endCenter) / q.endScale) w :=
    (contDiffAt_id.sub contDiffAt_const).div_const _
  exact ((hu.norm ℝ h₀).log (norm_ne_zero_iff.2 h₀)).neg.div_const _

section Periodic

variable {E G M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smooth family `f t x` of period one in `t`, evaluated at the angular coordinate of an end,
is smooth away from the center of the end, jointly with the parameter `x` in a manifold. The
angular coordinate itself jumps by `1` across a ray; periodicity removes the jump. -/
theorem contMDiffAt_comp_im_endCoord (q : Puncture) {n : WithTop ℕ∞} {f : ℝ → M → F}
    (hf : Function.Periodic f 1)
    (hfs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) n (Function.uncurry f)) {w : ℂ}
    (hw : w ≠ q.endCenter) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, F) n (fun p : ℂ × M => f (q.endCoord p.1).im p.2)
      (w, x) := by
  set u : ℂ → ℂ := fun w => (w - q.endCenter) / q.endScale
  have hu : ContDiffAt ℝ n u w := (contDiffAt_id.sub contDiffAt_const).div_const _
  have h₀ : u w ≠ 0 := div_ne_zero (sub_ne_zero.2 hw) q.endScale_ne_zero
  -- Evaluating `f` at a function of `w` that is smooth at `w` gives a smooth function.
  have hcomp (g : ℂ → ℝ) (hg : ContDiffAt ℝ n g w) :
      ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, F) n (fun p : ℂ × M => f (g p.1) p.2) (w, x) :=
    hfs.contMDiffAt.comp (I' := 𝓘(ℝ, ℝ).prod I) (w, x)
      ((hg.contMDiffAt.comp (w, x) contMDiffAt_fst).prodMk contMDiffAt_snd)
  -- The angular coordinate of a smooth function is smooth where it takes slit-plane values.
  have hlog (g : ℂ → ℂ) (hg : ContDiffAt ℝ n g w) (h : g w ∈ Complex.slitPlane) :
      ContDiffAt ℝ n (fun w => -(Complex.log (g w)).im / (2 * π)) w :=
    (Complex.imCLM.contDiff.contDiffAt.comp w
      (((Complex.contDiffAt_log h).restrict_scalars ℝ).comp w hg)).neg.div_const _
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane h₀ with h | h
  · refine hcomp (fun w => (q.endCoord w).im) ?_
    simp_rw [im_endCoord, ← Complex.log_im]
    exact hlog u hu h
  · -- Near the ray where the angular coordinate jumps, compare with the argument of `-u`.
    refine (hcomp _ ((hlog (fun w => -u w) hu.neg h).add
      (contDiffAt_const (c := (1 / 2 : ℝ))))).congr_of_eventuallyEq ?_
    have hne : ∀ᶠ p : ℂ × M in nhds (w, x), u p.1 ≠ 0 :=
      (hu.continuousAt.comp (f := Prod.fst) (x := (w, x)) continuousAt_fst).eventually_ne h₀
    filter_upwards [hne] with p hp
    obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 (Complex.arg_neg_coe_angle hp)
    have hπ : π ≠ 0 := Real.pi_ne_zero
    simp only [im_endCoord, Complex.log_im]
    rw [← hf.int_mul k (-Complex.arg (-u p.1) / (2 * π) + 1 / 2)]
    congr 1
    field_simp
    linarith

end Periodic

/-- The angular one-form `dt` of an end, as a covector at `w`: `v ↦ Im (v / (-2π (w - c_q)))`,
the imaginary part of the differential of the end coordinate. -/
def endAngularForm (q : Puncture) (w : ℂ) : ℂ →L[ℝ] ℝ :=
  Complex.imCLM ∘L ContinuousLinearMap.mul ℝ ℂ (-(2 * π * (w - q.endCenter)))⁻¹

@[simp]
theorem endAngularForm_apply (q : Puncture) (w v : ℂ) :
    q.endAngularForm w v = ((-(2 * π * (w - q.endCenter)))⁻¹ * v).im :=
  (rfl)

/-- The angular form pulls back to `dt` along the end lift: it sends the image `φ'(z) v` of a
tangent vector `v` of the cylinder to `Im v`. -/
theorem endAngularForm_cylindricalEndLift (q : Puncture) (z v : ℂ) :
    q.endAngularForm (q.cylindricalEndLift z) (deriv q.cylindricalEndLift z * v) = v.im := by
  have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [endAngularForm_apply, deriv_cylindricalEndLift, ← mul_assoc,
    inv_mul_cancel₀ (by simp [hπ, q.cylindricalEndLift_sub_endCenter_ne_zero z]), one_mul]

/-- The angular form is smooth away from the center of the end. -/
theorem contDiffAt_endAngularForm (q : Puncture) {w : ℂ} (hw : w ≠ q.endCenter)
    {n : WithTop ℕ∞} : ContDiffAt ℝ n q.endAngularForm w := by
  have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have h : ContDiffAt ℂ n (fun w : ℂ => (-(2 * π * (w - q.endCenter)))⁻¹) w :=
    (by fun_prop : ContDiffAt ℂ n (fun w : ℂ => -(2 * π * (w - q.endCenter))) w).inv
      (by simp [hπ, sub_eq_zero, hw])
  exact contDiffAt_const.clm_comp
    ((ContinuousLinearMap.mul ℝ ℂ).contDiff.contDiffAt.comp w (h.restrict_scalars ℝ))

/-- A point of an end with positive signed longitudinal coordinate lies in the standard punctured
neighborhood of the puncture. -/
theorem exists_mem_neighborhood_cylindricalEndLift (q : Puncture) {z : ℂ}
    (hz : 0 < q.endSign * z.re) :
    ∃ p ∈ q.neighborhood, (p : ℂ) = q.cylindricalEndLift z := by
  cases q
  · refine ⟨_, (zero.cylindricalEnd
      (⟨z.re, by simpa using hz⟩, (z.im : AddCircle (1 : ℝ)))).2, ?_⟩
    rw [coe_cylindricalEnd_apply_mk zero (by decide)]
    simp [Complex.re_add_im]
  · refine ⟨_, (one.cylindricalEnd
      (⟨z.re, by simpa using hz⟩, (z.im : AddCircle (1 : ℝ)))).2, ?_⟩
    rw [coe_cylindricalEnd_apply_mk one (by decide)]
    simp [Complex.re_add_im]
  · refine ⟨_, (negativeEnd
      (⟨z.re, by simpa using hz⟩, (z.im : AddCircle (1 : ℝ)))).2, ?_⟩
    rw [coe_negativeEnd_apply_mk]
    simp [Complex.re_add_im]

/-- A point of an end with positive signed longitudinal coordinate lies in the thrice-punctured
sphere: it is neither `0` nor `1`. -/
theorem cylindricalEndLift_ne_zero_and_ne_one (q : Puncture) {z : ℂ}
    (hz : 0 < q.endSign * z.re) :
    q.cylindricalEndLift z ≠ 0 ∧ q.cylindricalEndLift z ≠ 1 := by
  obtain ⟨p, -, hp⟩ := q.exists_mem_neighborhood_cylindricalEndLift hz
  rw [← hp]
  exact p.2

/-- A point with positive signed longitudinal coordinate on an end lies in the thrice-punctured
sphere: it is neither `0` nor `1`. -/
theorem ne_zero_and_ne_one_of_endSign_mul_re_endCoord_pos (q : Puncture) {w : ℂ}
    (h : 0 < q.endSign * (q.endCoord w).re) : w ≠ 0 ∧ w ≠ 1 := by
  have hw : w ≠ q.endCenter := q.ne_endCenter_of_re_endCoord_ne_zero fun h' => by simp [h'] at h
  rw [← q.cylindricalEndLift_endCoord hw]
  exact q.cylindricalEndLift_ne_zero_and_ne_one h

/-- Distinct ends have disjoint images on their parts with positive signed longitudinal
coordinate. -/
theorem cylindricalEndLift_ne_cylindricalEndLift {q r : Puncture} (hqr : q ≠ r) {z z' : ℂ}
    (hz : 0 < q.endSign * z.re) (hz' : 0 < r.endSign * z'.re) :
    q.cylindricalEndLift z ≠ r.cylindricalEndLift z' := by
  obtain ⟨p, hp, hpz⟩ := q.exists_mem_neighborhood_cylindricalEndLift hz
  obtain ⟨p', hp', hpz'⟩ := r.exists_mem_neighborhood_cylindricalEndLift hz'
  intro h
  obtain rfl : p = p' := Subtype.ext (hpz.trans (h.trans hpz'.symm))
  exact Set.disjoint_left.1 (pairwise_disjoint_neighborhood hqr) hp hp'

/-- A point with positive signed longitudinal coordinate on one end has nonpositive signed
longitudinal coordinate on every other end. -/
theorem endSign_mul_re_endCoord_nonpos {q r : Puncture} (hqr : q ≠ r) {w : ℂ}
    (h : 0 < q.endSign * (q.endCoord w).re) : r.endSign * (r.endCoord w).re ≤ 0 := by
  by_contra! h'
  have hq : w ≠ q.endCenter := q.ne_endCenter_of_re_endCoord_ne_zero fun h₀ => by simp [h₀] at h
  have hr : w ≠ r.endCenter := r.ne_endCenter_of_re_endCoord_ne_zero fun h₀ => by simp [h₀] at h'
  exact cylindricalEndLift_ne_cylindricalEndLift hqr h h'
    ((q.cylindricalEndLift_endCoord hq).trans (r.cylindricalEndLift_endCoord hr).symm)

end TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.ThricePuncturedSphere

open Puncture

/-- The truncation `S_R` of the thrice-punctured sphere `S = ℂ ∖ {0, 1}`: the points of `S` at
which the signed longitudinal coordinate `±s` of every end is at most `R`. It is `S` with the
parts `±s > R` of its three cylindrical ends removed, and it is compact
(`TauCeti.ThricePuncturedSphere.isCompact_truncation`). -/
def truncation (R : ℝ) : Set ℂ :=
  {w | w ≠ 0 ∧ w ≠ 1 ∧ ∀ q : Puncture, q.endSign * (q.endCoord w).re ≤ R}

@[simp]
theorem mem_truncation {R : ℝ} {w : ℂ} :
    w ∈ truncation R ↔ w ≠ 0 ∧ w ≠ 1 ∧ ∀ q : Puncture, q.endSign * (q.endCoord w).re ≤ R :=
  Iff.rfl

/-- The truncation is cut out by norm inequalities: it is the closed annulus
`exp (-2πR) / 2 ≤ ‖w‖ ≤ 2 exp (2πR)` with the open disc of radius `exp (-2πR) / 2` about `1`
removed. -/
theorem truncation_eq (R : ℝ) :
    truncation R = {w | Real.exp (-(2 * π * R)) / 2 ≤ ‖w‖} ∩
      {w | Real.exp (-(2 * π * R)) / 2 ≤ ‖w - 1‖} ∩
        Metric.closedBall 0 (2 * Real.exp (2 * π * R)) := by
  have he : 0 < Real.exp (-(2 * π * R)) / 2 := by positivity
  ext w
  simp only [mem_truncation, Set.mem_inter_iff, Set.mem_ofPred_eq, Metric.mem_closedBall,
    dist_zero_right]
  -- The longitudinal coordinates of the three ends, in terms of norms.
  have h₀ (hw : w ≠ 0) : zero.endSign * (zero.endCoord w).re ≤ R ↔
      Real.exp (-(2 * π * R)) / 2 ≤ ‖w‖ := by
    rw [endSign_zero, one_mul, re_endCoord, endCenter_zero, endScale_zero, sub_zero,
      Real.neg_log_div_le_iff (by simpa using hw) (by positivity), div_le_iff₀ two_pos]
    simp [mul_comm]
  have h₁ (hw : w ≠ 1) : one.endSign * (one.endCoord w).re ≤ R ↔
      Real.exp (-(2 * π * R)) / 2 ≤ ‖w - 1‖ := by
    rw [endSign_one, one_mul, re_endCoord, endCenter_one, endScale_one,
      Real.neg_log_div_le_iff (by simpa [sub_eq_zero] using hw) (by positivity),
      div_le_iff₀ two_pos]
    simp [mul_comm]
  have h₂ (hw : w ≠ 0) : inf.endSign * (inf.endCoord w).re ≤ R ↔
      ‖w‖ ≤ 2 * Real.exp (2 * π * R) := by
    rw [endSign_inf, neg_one_mul, re_endCoord, endCenter_inf, endScale_inf, sub_zero,
      neg_div, neg_neg, Real.log_div_le_iff (by simpa using hw) (by positivity)]
    simp only [norm_div, Complex.norm_ofNat]
    rw [div_le_iff₀ two_pos, mul_comm]
  constructor
  · rintro ⟨hw₀, hw₁, h⟩
    exact ⟨⟨(h₀ hw₀).1 (h zero), (h₁ hw₁).1 (h one)⟩, (h₂ hw₀).1 (h inf)⟩
  · rintro ⟨⟨ha, hb⟩, hc⟩
    have hw₀ : w ≠ 0 := by
      rintro rfl
      simp only [norm_zero] at ha
      linarith
    have hw₁ : w ≠ 1 := by
      rintro rfl
      simp only [sub_self, norm_zero] at hb
      linarith
    refine ⟨hw₀, hw₁, fun q => ?_⟩
    cases q
    exacts [(h₀ hw₀).2 ha, (h₁ hw₁).2 hb, (h₂ hw₀).2 hc]

/-- For `R ≥ 0`, the points of the disc `‖w‖ ≤ 2 exp (2πR)` outside the truncation `S_R` lie in
the open disc `‖w‖ < 2 exp (2π)`: they are within `exp (-2πR) / 2 ≤ 1 / 2` of `0` or `1`. -/
theorem closedBall_sdiff_truncation_subset_ball {R : ℝ} (hR : 0 ≤ R) :
    Metric.closedBall 0 (2 * Real.exp (2 * π * R)) \ truncation R ⊆
      Metric.ball 0 (2 * Real.exp (2 * π)) := by
  rintro w ⟨hwD, hwT⟩
  have he : Real.exp (-(2 * π * R)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
  have h1 : 1 ≤ Real.exp (2 * π) := Real.one_le_exp (by positivity)
  rw [truncation_eq] at hwT
  have hnorm := norm_sub_norm_le w 1
  rw [norm_one] at hnorm
  rw [mem_ball_zero_iff]
  by_cases h₀ : Real.exp (-(2 * π * R)) / 2 ≤ ‖w‖
  · have h₁ : ‖w - 1‖ < Real.exp (-(2 * π * R)) / 2 := by
      by_contra! h
      exact hwT ⟨⟨h₀, h⟩, hwD⟩
    linarith
  · linarith

/-- The truncation of the thrice-punctured sphere is compact. -/
theorem isCompact_truncation (R : ℝ) : IsCompact (truncation R) := by
  rw [truncation_eq]
  exact (isCompact_closedBall _ _).inter_left
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))))

end TauCeti.ThricePuncturedSphere
