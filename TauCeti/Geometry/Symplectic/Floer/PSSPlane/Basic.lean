/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ThricePuncturedSphere.EndCoordinate
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Hamiltonian perturbation data on the planes of the PSS maps

The Piunikhin–Salamon–Schwarz comparison between Morse and Floer complexes counts solutions of
the perturbed Cauchy–Riemann equation `(du - X_K)^{0,1} = 0` on the complex plane `ℂ`, with a
Morse incidence condition at the pole `0` and a cylindrical Floer end at `∞`. There are two
planes (`TauCeti.Floer.PSSPlane`).

* On the *positive* plane the end at `∞` is a positive (input) end, with end coordinates
  `w = exp (2π (s + i t))` for `s → ∞`. Its counts give the map from Floer to Morse chains.
* On the *negative* plane the end at `∞` is a negative (output) end, with end coordinates
  `w = exp (-2π (s + i t))` for `s → -∞`. Its counts give the map from Morse to Floer chains;
  the Floer unit is its count constrained by the fundamental cycle.

Writing `σ = ±1` for the sign of the plane (`PSSPlane.sign`), the end lift is
`z ↦ exp (2π σ z)` (`PSSPlane.endLift`), and the logarithm `ζ(w) = σ log w / (2π)` inverts it
(`PSSPlane.endLift_endCoord`). Unlike an end of a pair of pants, the end lift covers the whole
punctured plane `ℂ ∖ {0}`. The signed longitudinal coordinate `σ s = log ‖w‖ / (2π)` is the same
on both planes (`PSSPlane.sign_mul_re_endCoord`).

From a period-one Hamiltonian `H` this file constructs the perturbation
`TauCeti.Floer.pssPlanePerturbation`, the one-form `β(σ s - 1) H(t) dt` where `β` is the smooth
transition from `0` on `(-∞, 1]` to `1` on `[2, ∞)`:

* `TauCeti.Floer.pssPlanePerturbation_eq_zero_of_norm_le`: it vanishes on the pole disc
  `‖w‖ ≤ exp (2π)`, so near the pole the equation is the unperturbed Cauchy–Riemann equation.
* `TauCeti.Floer.pssPlanePerturbation_eq_smul_endAngularForm`: it is `H(t) dt` on the part
  `σ s ≥ 2` of the end.
* `TauCeti.Floer.contMDiff_pssPlanePerturbation`: it is `C^n` on all of `ℂ × M`, including at
  the pole, for `C^n` Hamiltonians of period one.
* `TauCeti.Floer.pssPlaneEndComponent_one` and `TauCeti.Floer.pssPlaneEndComponent_I`: in end
  coordinates its components are `K_s = 0` and `K_t = β(σ s - 1) H(t)` everywhere on the
  cylinder, so in these coordinates the plane is a continuation cylinder between the zero
  Hamiltonian at the pole and `H` at the end.

## Implementation notes

The angular coordinate of the plane is a multiple of the argument of `w`, which jumps across the
negative real axis, so smoothness uses the periodicity of `H`. Up to sign it is the angular
coordinate of the end at `∞` of the thrice-punctured sphere, whose smoothness statement
`TauCeti.ThricePuncturedSphere.Puncture.contMDiffAt_comp_im_endCoord` is reused.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the chapter on Floer
  homology, on the PSS maps and their perturbation data on the plane.
-/

public noncomputable section

open Set Real Manifold Topology
open TauCeti.ThricePuncturedSphere

namespace TauCeti.Floer

/-- The two planes of the Piunikhin–Salamon–Schwarz comparison. Both are `ℂ` with a Morse pole at
`0` and a cylindrical Floer end at `∞`; on `pos` the end is positive (an input), on `neg` it is
negative (an output). -/
inductive PSSPlane
  | pos
  | neg

namespace PSSPlane

/-- The sign of the Floer end of a plane: `1` for the positive plane, whose end is parameterized
by `s → ∞`, and `-1` for the negative plane, whose end is parameterized by `s → -∞`. -/
def sign : PSSPlane → ℝ
  | pos => 1
  | neg => -1

@[simp] theorem sign_pos : pos.sign = 1 := (rfl)

@[simp] theorem sign_neg : neg.sign = -1 := (rfl)

/-- The sign of a plane squares to one. -/
@[simp]
theorem sign_mul_sign (P : PSSPlane) : P.sign * P.sign = 1 := by
  cases P <;> norm_num

@[simp]
theorem abs_sign (P : PSSPlane) : |P.sign| = 1 := by
  cases P <;> simp

theorem sign_ne_zero (P : PSSPlane) : P.sign ≠ 0 := by
  cases P <;> norm_num

/-- The end lift `z ↦ exp (2π σ z)` of the plane, from the cylinder with coordinate
`z = s + i t` onto the punctured plane. -/
def endLift (P : PSSPlane) (z : ℂ) : ℂ :=
  Complex.exp (2 * π * P.sign * z)

theorem endLift_def (P : PSSPlane) (z : ℂ) :
    P.endLift z = Complex.exp (2 * π * P.sign * z) :=
  (rfl)

/-- The end lift never hits the pole. -/
theorem endLift_ne_zero (P : PSSPlane) (z : ℂ) : P.endLift z ≠ 0 :=
  Complex.exp_ne_zero _

/-- The norm of a point of the end is determined by its signed longitudinal coordinate. -/
theorem norm_endLift (P : PSSPlane) (z : ℂ) :
    ‖P.endLift z‖ = Real.exp (2 * π * (P.sign * z.re)) := by
  rw [endLift, Complex.norm_exp]
  congr 1
  simp [mul_assoc]

theorem hasDerivAt_endLift (P : PSSPlane) (z : ℂ) :
    HasDerivAt P.endLift (2 * π * P.sign * P.endLift z) z := by
  have h := ((hasDerivAt_id z).const_mul (2 * π * P.sign : ℂ)).cexp
  simp only [id_eq, mul_one] at h
  exact h.congr_deriv (mul_comm _ _)

/-- The derivative of the end lift is `2π σ` times the end lift. -/
theorem deriv_endLift (P : PSSPlane) (z : ℂ) :
    deriv P.endLift z = 2 * π * P.sign * P.endLift z :=
  (P.hasDerivAt_endLift z).deriv

/-- The logarithmic end coordinate `ζ(w) = σ log w / (2π)`. Its real part is the longitudinal
coordinate `s` and its imaginary part the angular coordinate `t`, determined by the point only
modulo `1`. -/
def endCoord (P : PSSPlane) (w : ℂ) : ℂ :=
  P.sign * Complex.log w / (2 * π)

theorem endCoord_def (P : PSSPlane) (w : ℂ) :
    P.endCoord w = P.sign * Complex.log w / (2 * π) :=
  (rfl)

/-- The longitudinal coordinate of a point of the plane. -/
theorem re_endCoord (P : PSSPlane) (w : ℂ) :
    (P.endCoord w).re = P.sign * Real.log ‖w‖ / (2 * π) := by
  rw [endCoord, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_re,
    Complex.re_ofReal_mul, Complex.log_re]

/-- The angular coordinate of a point of the plane. -/
theorem im_endCoord (P : PSSPlane) (w : ℂ) :
    (P.endCoord w).im = P.sign * Complex.arg w / (2 * π) := by
  rw [endCoord, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_im,
    Complex.im_ofReal_mul, Complex.log_im]

/-- The signed longitudinal coordinate `σ s = log ‖w‖ / (2π)` does not depend on the plane. -/
@[simp]
theorem sign_mul_re_endCoord (P : PSSPlane) (w : ℂ) :
    P.sign * (P.endCoord w).re = Real.log ‖w‖ / (2 * π) := by
  rw [re_endCoord, mul_div_assoc', ← mul_assoc, sign_mul_sign, one_mul]

/-- The end coordinate is a right inverse of the end lift away from the pole. -/
theorem endLift_endCoord (P : PSSPlane) {w : ℂ} (hw : w ≠ 0) : P.endLift (P.endCoord w) = w := by
  have hπ : 2 * (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hσ : (P.sign : ℂ) * P.sign = 1 := by exact_mod_cast P.sign_mul_sign
  have h : 2 * π * P.sign * (P.sign * Complex.log w / (2 * π)) = Complex.log w :=
    calc 2 * π * P.sign * (P.sign * Complex.log w / (2 * π))
        _ = (P.sign * P.sign) * Complex.log w * ((2 * π) / (2 * π)) := by ring
        _ = Complex.log w := by rw [hσ, div_self hπ, one_mul, mul_one]
  rw [endLift, endCoord, h, Complex.exp_log hw]

/-- The end coordinate recovers a cylinder point from its image under the end lift, up to an
integer shift of the angular coordinate. -/
theorem exists_endCoord_endLift (P : PSSPlane) (z : ℂ) :
    ∃ k : ℤ, P.endCoord (P.endLift z) = z + k * Complex.I := by
  obtain ⟨n, hn⟩ := Complex.log_exp_exists (2 * π * P.sign * z)
  have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  cases P
  · refine ⟨n, ?_⟩
    rw [endCoord, endLift, hn]
    field_simp
    simp only [sign_pos]
    push_cast
    ring
  · refine ⟨-n, ?_⟩
    rw [endCoord, endLift, hn]
    field_simp
    simp only [sign_neg]
    push_cast
    ring

/-- The angular one-form `dt` of the plane, as a covector at `w`: `v ↦ Im (v / (2π σ w))`, the
imaginary part of the differential of the end coordinate. -/
def endAngularForm (P : PSSPlane) (w : ℂ) : ℂ →L[ℝ] ℝ :=
  Complex.imCLM ∘L ContinuousLinearMap.mul ℝ ℂ (2 * π * P.sign * w)⁻¹

@[simp]
theorem endAngularForm_apply (P : PSSPlane) (w v : ℂ) :
    P.endAngularForm w v = ((2 * π * P.sign * w)⁻¹ * v).im :=
  (rfl)

/-- The angular form pulls back to `dt` along the end lift: it sends the image `φ'(z) v` of a
tangent vector `v` of the cylinder to `Im v`. -/
theorem endAngularForm_endLift (P : PSSPlane) (z v : ℂ) :
    P.endAngularForm (P.endLift z) (deriv P.endLift z * v) = v.im := by
  have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hσ : (P.sign : ℂ) ≠ 0 := by exact_mod_cast P.sign_ne_zero
  rw [endAngularForm_apply, deriv_endLift, ← mul_assoc,
    inv_mul_cancel₀ (by simp [hπ, hσ, P.endLift_ne_zero z]), one_mul]

/-- The angular form is smooth away from the pole. -/
theorem contDiffAt_endAngularForm (P : PSSPlane) {w : ℂ} (hw : w ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n P.endAngularForm w := by
  have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hσ : (P.sign : ℂ) ≠ 0 := by exact_mod_cast P.sign_ne_zero
  have h : ContDiffAt ℂ n (fun w : ℂ => (2 * π * P.sign * w)⁻¹) w :=
    (by fun_prop : ContDiffAt ℂ n (fun w : ℂ => 2 * π * P.sign * w) w).inv
      (by simp [hπ, hσ, hw])
  exact contDiffAt_const.clm_comp
    ((ContinuousLinearMap.mul ℝ ℂ).contDiff.contDiffAt.comp w (h.restrict_scalars ℝ))

/-- The longitudinal coordinate is smooth away from the pole. -/
theorem contDiffAt_re_endCoord (P : PSSPlane) {w : ℂ} (hw : w ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fun w => (P.endCoord w).re) w := by
  simp_rw [re_endCoord]
  exact (contDiffAt_const.mul
    ((contDiffAt_id.norm ℝ hw).log (norm_ne_zero_iff.2 hw))).div_const _

/-- The angular coordinate of the plane is that of the end at `∞` of the thrice-punctured sphere,
up to the sign of the plane: the two end lifts differ by the positive factor `2`. -/
private theorem im_endCoord_eq_neg_sign_mul (P : PSSPlane) (w : ℂ) :
    (P.endCoord w).im = -P.sign * (Puncture.inf.endCoord w).im := by
  have h2 : w / 2 = ((1 / 2 : ℝ) : ℂ) * w := by push_cast; ring
  rw [im_endCoord, Puncture.im_endCoord, Puncture.endCenter_inf, Puncture.endScale_inf, sub_zero,
    h2, Complex.arg_real_mul _ (by norm_num)]
  ring

section Periodic

variable {E G M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smooth family `f t x` of period one in `t`, evaluated at the angular coordinate of the plane,
is smooth away from the pole, jointly with the parameter `x` in a manifold. -/
theorem contMDiffAt_comp_im_endCoord (P : PSSPlane) {n : WithTop ℕ∞} {f : ℝ → M → F}
    (hf : Function.Periodic f 1)
    (hfs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) n (Function.uncurry f)) {w : ℂ}
    (hw : w ≠ 0) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, F) n (fun p : ℂ × M => f (P.endCoord p.1).im p.2)
      (w, x) := by
  -- Reflect the period-one family by the sign of the plane, and use the end at `∞`.
  have hg : Function.Periodic (fun t => f (-P.sign * t)) 1 := by
    intro t
    cases P
    · simpa [mul_add, sub_eq_add_neg, add_comm] using hf.sub_eq (-t)
    · simpa [mul_add] using hf t
  have hgs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) n
      (Function.uncurry fun t => f (-P.sign * t)) :=
    hfs.comp ((((contDiff_const.mul contDiff_id).contMDiff).comp contMDiff_fst).prodMk
      contMDiff_snd)
  simp_rw [im_endCoord_eq_neg_sign_mul]
  exact Puncture.inf.contMDiffAt_comp_im_endCoord hg hgs (by simpa using hw) x

end Periodic

end PSSPlane

variable {M : Type*}

/-- The Hamiltonian perturbation one-form on the plane `P` given by a period-one Hamiltonian `H`.
At `w ∈ ℂ` and `x ∈ M` it is the covector `β(σ s(w) - 1) H(t(w), x) dt`, where `(s, t)` are the
end coordinates, `σ` is the sign of the plane, and `β` is the smooth transition from `0` on
`(-∞, 1]` to `1` on `[2, ∞)`. -/
def pssPlanePerturbation (P : PSSPlane) (H : ℝ → M → ℝ) (w : ℂ) (x : M) : ℂ →L[ℝ] ℝ :=
  (smoothTransition (P.sign * (P.endCoord w).re - 1) * H (P.endCoord w).im x) •
    P.endAngularForm w

theorem pssPlanePerturbation_def (P : PSSPlane) (H : ℝ → M → ℝ) (w : ℂ) (x : M) :
    pssPlanePerturbation P H w x =
      (smoothTransition (P.sign * (P.endCoord w).re - 1) * H (P.endCoord w).im x) •
        P.endAngularForm w :=
  (rfl)

variable {P : PSSPlane} {H : ℝ → M → ℝ}

/-- **The perturbation vanishes on the pole disc** `‖w‖ ≤ exp (2π)`, which contains the pole. -/
theorem pssPlanePerturbation_eq_zero_of_norm_le {w : ℂ} (hw : ‖w‖ ≤ Real.exp (2 * π)) (x : M) :
    pssPlanePerturbation P H w x = 0 := by
  rw [pssPlanePerturbation_def, PSSPlane.sign_mul_re_endCoord,
    smoothTransition.zero_of_nonpos, zero_mul, zero_smul]
  rw [sub_nonpos, div_le_one (by positivity)]
  rcases eq_or_ne w 0 with rfl | hw₀
  · simp [Real.pi_pos.le]
  · exact (Real.log_le_iff_le_exp (norm_pos_iff.2 hw₀)).2 hw

/-- The perturbation vanishes identically near every point of the open pole disc
`‖w‖ < exp (2π)`, in particular near the pole. -/
theorem eventually_pssPlanePerturbation_eq_zero {w : ℂ} (hw : ‖w‖ < Real.exp (2 * π)) :
    ∀ᶠ w' in 𝓝 w, ∀ x : M, pssPlanePerturbation P H w' x = 0 := by
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hw] with w' hw' x
  exact pssPlanePerturbation_eq_zero_of_norm_le hw'.le x

/-- **The perturbation on the end.** The pullback of the perturbation along the end lift `φ` is
the continuation datum `β(σ s - 1) H(t) dt`: it sends a tangent vector `v` of the cylinder to
`Im v · β(σ s - 1) H(t)`. -/
theorem pssPlanePerturbation_endLift (hH : Function.Periodic H 1) (z : ℂ) (x : M) (v : ℂ) :
    pssPlanePerturbation P H (P.endLift z) x (deriv P.endLift z * v) =
      v.im * (smoothTransition (P.sign * z.re - 1) * H z.im x) := by
  obtain ⟨k, hk⟩ := P.exists_endCoord_endLift z
  have hp : H (z.im + k) x = H z.im x := by
    simpa using congrFun (hH.int_mul k z.im) x
  rw [pssPlanePerturbation_def, smul_apply, PSSPlane.endAngularForm_endLift,
    hk, smul_eq_mul, mul_comm]
  simp [hp]

/-- **The perturbation is `H(t) dt` far out on the end.** On the part `σ s ≥ 2` of the end, the
pullback of the perturbation along the end lift sends a tangent vector `v` of the cylinder to
`Im v · H(t)`. -/
theorem pssPlanePerturbation_endLift_of_two_le (hH : Function.Periodic H 1) {z : ℂ}
    (hz : 2 ≤ P.sign * z.re) (x : M) (v : ℂ) :
    pssPlanePerturbation P H (P.endLift z) x (deriv P.endLift z * v) = v.im * H z.im x := by
  rw [pssPlanePerturbation_endLift hH, smoothTransition.one_of_one_le (by linarith), one_mul]

/-- **The perturbation is `H(t) dt` far out on the end**, in terms of the angular form: at a point
`w` of the part `σ s ≥ 2` of the end it is the angular form scaled by `H` at the angular
coordinate of `w`. -/
theorem pssPlanePerturbation_eq_smul_endAngularForm {w : ℂ}
    (hw : 2 ≤ P.sign * (P.endCoord w).re) (x : M) :
    pssPlanePerturbation P H w x = H (P.endCoord w).im x • P.endAngularForm w := by
  rw [pssPlanePerturbation_def, smoothTransition.one_of_one_le (by linarith), one_mul]

/-- The component of the perturbation along the tangent vector `v` of the cylinder, in the end
coordinates `z = (s, t)`: the pullback of the perturbation along the end lift `φ`, evaluated at
`s + i t` on `v`. The components `K_s` and `K_t` of the pulled-back datum `K_s ds + K_t dt` are
those along `v = 1` and `v = i`. -/
def pssPlaneEndComponent (P : PSSPlane) (H : ℝ → M → ℝ) (v : ℂ) (z : ℝ × ℝ) (x : M) : ℝ :=
  pssPlanePerturbation P H (P.endLift ⟨z.1, z.2⟩) x (deriv P.endLift ⟨z.1, z.2⟩ * v)

theorem pssPlaneEndComponent_def (P : PSSPlane) (H : ℝ → M → ℝ) (v : ℂ) (z : ℝ × ℝ) (x : M) :
    pssPlaneEndComponent P H v z x =
      pssPlanePerturbation P H (P.endLift ⟨z.1, z.2⟩) x (deriv P.endLift ⟨z.1, z.2⟩ * v) :=
  (rfl)

/-- In end coordinates the `ds` component of the perturbation vanishes everywhere. -/
theorem pssPlaneEndComponent_one (hH : Function.Periodic H 1) :
    pssPlaneEndComponent P H 1 = fun _ _ => 0 := by
  funext z x
  rw [pssPlaneEndComponent_def, pssPlanePerturbation_endLift hH]
  simp

/-- In end coordinates the `dt` component of the perturbation is `β(σ s - 1) H(t)` everywhere. -/
theorem pssPlaneEndComponent_I (hH : Function.Periodic H 1) :
    pssPlaneEndComponent P H Complex.I =
      fun z x => smoothTransition (P.sign * z.1 - 1) * H z.2 x := by
  funext z x
  rw [pssPlaneEndComponent_def, pssPlanePerturbation_endLift hH]
  simp

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- **The perturbation is smooth.** For a Hamiltonian of period one which is `C^n` on `ℝ × M`, the
perturbation is `C^n` on `ℂ × M`, including at the pole, near which it vanishes. -/
theorem contMDiff_pssPlanePerturbation {n : ℕ∞} (hH : Function.Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (Function.uncurry H)) :
    ContMDiff (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℂ × M => pssPlanePerturbation P H p.1 p.2) := by
  rintro ⟨w, x⟩
  rcases eq_or_ne w 0 with rfl | hw
  · -- Near the pole the perturbation vanishes identically.
    have h0 : ‖(0 : ℂ)‖ < Real.exp (2 * π) := by simpa using Real.exp_pos _
    refine (contMDiffAt_const (c := (0 : ℂ →L[ℝ] ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(continuous_fst.tendsto ((0 : ℂ), x)).eventually
      (eventually_pssPlanePerturbation_eq_zero (P := P) (H := H) h0)] with p hp
    exact hp p.2
  · have hβ : ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℝ) n
        (fun p : ℂ × M => smoothTransition (P.sign * (P.endCoord p.1).re - 1)) (w, x) :=
      (smoothTransition.contDiff.contDiffAt.comp w
        ((contDiffAt_const.mul (P.contDiffAt_re_endCoord hw)).sub
          contDiffAt_const)).contMDiffAt.comp (w, x) contMDiffAt_fst
    have hf : ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
        (fun p : ℂ × M => P.endAngularForm p.1) (w, x) :=
      ContMDiffAt.comp (I' := 𝓘(ℝ, ℂ)) (g := P.endAngularForm) _
        (P.contDiffAt_endAngularForm hw).contMDiffAt contMDiffAt_fst
    exact (hβ.smul (P.contMDiffAt_comp_im_endCoord hH hHs hw x)).smul hf

end TauCeti.Floer
