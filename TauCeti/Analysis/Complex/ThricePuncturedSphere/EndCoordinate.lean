/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ThricePuncturedSphere.CylindricalEnds
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import TauCeti.LinearAlgebra.Determinant.Prod
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
(`Puncture.cylindricalEndLift_ne_cylindricalEndLift`).

In the real coordinates `ℝ × ℝ ≃ ℂ` the end lift is the end chart `Puncture.endChart`, the map in
which integrals over the ends are computed. It is periodic in the angular coordinate
(`Puncture.periodic_endChart`), orientation preserving (`Puncture.det_fderiv_endChart_nonneg`),
and injective on the strip `Puncture.endStrip` of points with `±s > 1/2` and `t ∈ [-1/2, 1/2)`
(`Puncture.injOn_endChart`), whose image is the part `±s > 1/2` of the end
(`Puncture.mem_image_endChart`).

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

/-- The sign of an end squares to one. -/
@[simp] theorem endSign_mul_self (q : Puncture) : q.endSign * q.endSign = 1 := by
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

/-- The end coordinate recovers the longitudinal coordinate of a cylinder point exactly. -/
@[simp]
theorem re_endCoord_cylindricalEndLift (q : Puncture) (z : ℂ) :
    (q.endCoord (q.cylindricalEndLift z)).re = z.re := by
  obtain ⟨k, hk⟩ := q.exists_endCoord_cylindricalEndLift z
  simp [hk]

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

section EndChart

/-! ### End charts in real coordinates -/

/-- The end lift of `q`, in the real coordinates `ℝ × ℝ ≃ ℂ`: the point with cylinder coordinates
`(s, t)` is sent to `φ_q(s + i t)`. -/
def endChart (q : Puncture) (z : ℝ × ℝ) : ℝ × ℝ :=
  Complex.equivRealProdCLM (q.cylindricalEndLift (Complex.equivRealProdCLM.symm z))

/-- The part `±s > 1/2`, `t ∈ [-1/2, 1/2)` of the end `q` in its cylinder coordinates. The end
chart is injective on it (`injOn_endChart`), and its image is the part `±s > 1/2` of the end
(`mem_image_endChart`). -/
def endStrip (q : Puncture) : Set (ℝ × ℝ) :=
  {s | 1 / 2 < q.endSign * s} ×ˢ Ico (-1 / 2) (1 / 2)

theorem endChart_def (q : Puncture) (z : ℝ × ℝ) :
    q.endChart z =
      Complex.equivRealProdCLM (q.cylindricalEndLift (Complex.equivRealProdCLM.symm z)) :=
  (rfl)

theorem endStrip_def (q : Puncture) :
    q.endStrip = {s | 1 / 2 < q.endSign * s} ×ˢ Ico (-1 / 2) (1 / 2) :=
  (rfl)

theorem mem_endStrip_iff {q : Puncture} {z : ℝ × ℝ} :
    z ∈ q.endStrip ↔ 1 / 2 < q.endSign * z.1 ∧ z.2 ∈ Ico (-1 / 2 : ℝ) (1 / 2) :=
  Iff.rfl

theorem endSign_mul_pos_of_mem_endStrip {q : Puncture} {z : ℝ × ℝ}
    (hz : z ∈ q.endStrip) : 0 < q.endSign * z.1 := by
  linarith [(mem_endStrip_iff.1 hz).1]

/-- The derivative of the end chart is multiplication by the derivative of the end lift. -/
theorem hasFDerivAt_endChart (q : Puncture) (z : ℝ × ℝ) :
    HasFDerivAt q.endChart
      ((Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ).comp
        (((ContinuousLinearMap.toSpanSingleton ℂ
          (deriv q.cylindricalEndLift (Complex.equivRealProdCLM.symm z))).restrictScalars ℝ).comp
            (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ))) z := by
  have h := ((q.hasDerivAt_cylindricalEndLift
    (Complex.equivRealProdCLM.symm z)).differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ)
  exact Complex.equivRealProdCLM.hasFDerivAt.comp z
    (h.comp z Complex.equivRealProdCLM.symm.hasFDerivAt)

theorem fderiv_endChart_apply (q : Puncture) (z v : ℝ × ℝ) :
    fderiv ℝ q.endChart z v = Complex.equivRealProdCLM
      (deriv q.cylindricalEndLift (Complex.equivRealProdCLM.symm z) *
        Complex.equivRealProdCLM.symm v) := by
  rw [(q.hasFDerivAt_endChart z).fderiv]
  simp [mul_comm]

@[simp]
theorem equivRealProdCLM_symm_endChart (q : Puncture) (z : ℝ × ℝ) :
    Complex.equivRealProdCLM.symm (q.endChart z) =
      q.cylindricalEndLift (Complex.equivRealProdCLM.symm z) := by
  rw [endChart_def, ContinuousLinearEquiv.symm_apply_apply]

/-- The end chart is periodic with period one in the angular coordinate. -/
theorem periodic_endChart (q : Puncture) (s : ℝ) :
    Function.Periodic (fun t : ℝ ↦ q.endChart (s, t)) 1 := by
  intro t
  have h := q.periodic_cylindricalEndLift s t
  simp only [endChart_def, Complex.equivRealProdCLM_symm_apply] at h ⊢
  rw [h]

/-- The end chart is holomorphic, so it preserves orientation: its Jacobian determinant is
`|φ_q'|² ≥ 0`. -/
theorem det_fderiv_endChart_nonneg (q : Puncture) (z : ℝ × ℝ) :
    0 ≤ (fderiv ℝ q.endChart z).det := by
  have h1 : Complex.equivRealProdCLM.symm ((1, 0) : ℝ × ℝ) = 1 := by
    simp [Complex.equivRealProdCLM_symm_apply]
  have hI : Complex.equivRealProdCLM.symm ((0, 1) : ℝ × ℝ) = Complex.I := by
    simp [Complex.equivRealProdCLM_symm_apply]
  rw [ContinuousLinearMap.det, LinearMap.det_finTwoProd]
  simp only [ContinuousLinearMap.coe_coe, fderiv_endChart_apply, h1, hI, mul_one,
    Complex.equivRealProdCLM_apply, Complex.mul_I_re, Complex.mul_I_im]
  nlinarith [sq_nonneg (deriv q.cylindricalEndLift (Complex.equivRealProdCLM.symm z)).re,
    sq_nonneg (deriv q.cylindricalEndLift (Complex.equivRealProdCLM.symm z)).im]

theorem contDiff_endChart (q : Puncture) {n : WithTop ℕ∞} : ContDiff ℝ n q.endChart :=
  Complex.equivRealProdCLM.contDiff.comp
    (((q.contDiff_cylindricalEndLift n).restrict_scalars ℝ).comp
      Complex.equivRealProdCLM.symm.contDiff)

/-- The end chart is injective on the strip `endStrip q`, whose angular coordinate ranges over
one period. -/
theorem injOn_endChart (q : Puncture) : InjOn q.endChart q.endStrip := by
  intro a ha b hb hab
  have h := q.injOn_cylindricalEndLift (by simpa using ha.2) (by simpa using hb.2)
    (Complex.equivRealProdCLM.injective hab)
  exact Complex.equivRealProdCLM.symm.injective h

/-- Every point of `ℂ ∖ {0, 1}` where the end `q` has signed longitudinal coordinate greater than
`1/2` is the image of a point of the strip of that end. -/
theorem mem_image_endChart {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1)
    {q : Puncture} (hq : 1 / 2 < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re) :
    z ∈ q.endChart '' q.endStrip := by
  refine ⟨Complex.equivRealProdCLM (q.endCoord (Complex.equivRealProdCLM.symm z)),
    ⟨by simpa using hq, by simpa using q.im_endCoord_mem_Ico _⟩, ?_⟩
  rw [endChart_def, ContinuousLinearEquiv.symm_apply_apply,
    q.cylindricalEndLift_endCoord (ne_endCenter hz q), ContinuousLinearEquiv.apply_symm_apply]

end EndChart

end TauCeti.ThricePuncturedSphere.Puncture
