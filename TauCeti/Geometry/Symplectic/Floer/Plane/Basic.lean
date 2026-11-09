/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ThricePuncturedSphere.EndCoordinate
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Hamiltonian perturbation data on the planes of the PSS maps

The Piunikhin–Salamon–Schwarz (PSS) maps between Morse and Hamiltonian Floer theory count
solutions of the perturbed Cauchy–Riemann equation `(du - X_K)^{0,1} = 0` on the complex plane
`ℂ`, with a Morse incidence condition at the pole `0` and a Floer cylindrical end at `∞`. There are
two planes (`TauCeti.Floer.PSSPlane`):

* the *positive* plane, whose end at `∞` is a positive (input) end, with end coordinates
  `w = exp (2π (s + i t))`, so that `s → +∞` at `∞`;
* the *negative* plane, whose end at `∞` is a negative (output) end, with end coordinates
  `w = exp (-2π (s + i t))`, so that `s → -∞` at `∞`.

Writing `ε = ±1` for the sign of the end, the end lift is `φ(z) = exp (2π ε z)`
(`TauCeti.Floer.PSSPlane.cylindricalEndLift`), which is holomorphic and preserves the orientation
`ds ∧ dt`.
It is inverted on `ℂ ∖ {0}` by the end coordinate `ζ(w) = ε log w / (2π)`
(`TauCeti.Floer.PSSPlane.endCoord`), up to an integer shift of the angular coordinate `t`. The
signed longitudinal coordinate is `ε s = log ‖w‖ / (2π)` for both planes
(`TauCeti.Floer.PSSPlane.endSign_mul_re_endCoord`), and the angular one-form `dt` is
`v ↦ Im (v / (2π ε w))` (`TauCeti.Floer.PSSPlane.endAngularForm`). The angular coordinate and the
angular form are those of the end at `0` of the thrice-punctured sphere, up to the sign `-ε`
(`TauCeti.Floer.PSSPlane.im_endCoord_eq_neg_endSign_mul` and
`TauCeti.Floer.PSSPlane.endAngularForm_eq_neg_endSign_smul`).

Given a period-one Hamiltonian `H`, the perturbation `TauCeti.Floer.PSSPlane.perturbation` is
`β(ε s - 1) H(t) dt` in end coordinates, for the smooth transition `β` from `0` on `(-∞, 0]` to
`1` on `[1, ∞)`. The results are:

* `TauCeti.Floer.PSSPlane.perturbation_eq_zero_of_norm_le`: the perturbation vanishes on the
  closed pole disc `‖w‖ ≤ exp (2π)`, where the Morse incidence condition is imposed;
* `TauCeti.Floer.PSSPlane.contMDiff_perturbation`: it is smooth on the whole of `ℂ × M`,
  including across the pole, and its components in the real coordinates `ℝ × ℝ ≃ ℂ` are `C¹`
  for a `C¹` Hamiltonian (`TauCeti.Floer.PSSPlane.contDiff_uncurry_perturbation`);
* `TauCeti.Floer.PSSPlane.perturbation_cylindricalEndLift`: its pullback along the end lift is the
  continuation datum `β(ε s - 1) H(t) dt` at every point of the cylinder;
* `TauCeti.Floer.PSSPlane.perturbation_cylindricalEndLift_of_two_le` and
  `TauCeti.Floer.PSSPlane.perturbation_eq_smul_endAngularForm`: on the part `ε s ≥ 2` of the end
  it is `H(t) dt`, so it agrees there with the Floer datum of the end;
* `TauCeti.Floer.PSSPlane.endComponent_one` and `TauCeti.Floer.PSSPlane.endComponent_I`: its
  components in end coordinates are `K_s = 0` and `K_t = β(ε s - 1) H(t)`.

The angular coordinate is defined only modulo `1`, which is why `H` is required to have period
one. Smoothness across the ray where it jumps reuses the corresponding statement for the end at
`0` of the thrice-punctured sphere, whose angular coordinate is that of the plane up to sign
(`TauCeti.Floer.PSSPlane.im_endCoord_eq_neg_endSign_mul`).

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Chapter 12, on
  Floer homology and the PSS isomorphism.
-/

public noncomputable section

open Set Real Manifold Topology

namespace TauCeti.Floer

/-- The two planes of the Piunikhin–Salamon–Schwarz maps: each is `ℂ`, with its Morse pole at
`0` and a Floer cylindrical end at `∞`, which is a positive (input) end on the positive plane and
a negative (output) end on the negative plane. -/
inductive PSSPlane
  /-- The plane whose Floer end at `∞` is a positive (input) end. -/
  | positive
  /-- The plane whose Floer end at `∞` is a negative (output) end. -/
  | negative
  deriving DecidableEq

namespace PSSPlane

/-! ### End coordinates -/

/-- The sign of the end at `∞`: `1` on the positive plane, parameterized near `∞` by `s > 0`,
and `-1` on the negative plane, parameterized near `∞` by `s < 0`. -/
def endSign : PSSPlane → ℝ
  | positive => 1
  | negative => -1

@[simp] theorem endSign_positive : positive.endSign = 1 := (rfl)

@[simp] theorem endSign_negative : negative.endSign = -1 := (rfl)

@[simp] theorem endSign_mul_endSign (p : PSSPlane) : p.endSign * p.endSign = 1 := by
  cases p <;> norm_num

@[simp] theorem abs_endSign (p : PSSPlane) : |p.endSign| = 1 := by
  cases p <;> norm_num

theorem endSign_ne_zero (p : PSSPlane) : p.endSign ≠ 0 := by
  cases p <;> norm_num

/-- The end lift `z ↦ exp (2π ε z)`, from the cylinder coordinates `z = s + i t` of the end to the
plane. -/
def cylindricalEndLift (p : PSSPlane) (z : ℂ) : ℂ :=
  Complex.exp ((2 * π * p.endSign : ℝ) * z)

theorem cylindricalEndLift_def (p : PSSPlane) (z : ℂ) :
    p.cylindricalEndLift z = Complex.exp ((2 * π * p.endSign : ℝ) * z) :=
  (rfl)

/-- The end lift never takes the value `0`, the pole of the plane. -/
theorem cylindricalEndLift_ne_zero (p : PSSPlane) (z : ℂ) : p.cylindricalEndLift z ≠ 0 :=
  Complex.exp_ne_zero _

/-- The end lift is holomorphic, with derivative `2π ε exp (2π ε z)`. -/
theorem hasDerivAt_cylindricalEndLift (p : PSSPlane) (z : ℂ) :
    HasDerivAt p.cylindricalEndLift ((2 * π * p.endSign : ℝ) * p.cylindricalEndLift z) z := by
  have h := ((hasDerivAt_id z).const_mul ((2 * π * p.endSign : ℝ) : ℂ)).cexp
  simp only [id_eq, mul_one] at h
  rw [cylindricalEndLift_def, mul_comm]
  exact h

theorem deriv_cylindricalEndLift (p : PSSPlane) (z : ℂ) :
    deriv p.cylindricalEndLift z = (2 * π * p.endSign : ℝ) * p.cylindricalEndLift z :=
  (p.hasDerivAt_cylindricalEndLift z).deriv

theorem contDiff_cylindricalEndLift (p : PSSPlane) {n : WithTop ℕ∞} :
    ContDiff ℂ n p.cylindricalEndLift := by
  unfold cylindricalEndLift
  fun_prop

/-- The end lift is periodic with period one in the angular coordinate. -/
theorem periodic_cylindricalEndLift (p : PSSPlane) (s : ℝ) :
    Function.Periodic (fun t : ℝ ↦ p.cylindricalEndLift (s + t * Complex.I)) 1 := by
  intro t
  have h : ((2 * π * p.endSign : ℝ) : ℂ) * ((s : ℂ) + (t + 1 : ℝ) * Complex.I) =
      ((2 * π * p.endSign : ℝ) : ℂ) * ((s : ℂ) + t * Complex.I) +
        (p.endSign : ℂ) * (2 * π * Complex.I) := by
    push_cast
    ring
  simp only [cylindricalEndLift_def, h, Complex.exp_add]
  cases p <;> simp [Complex.exp_neg]

/-- The end coordinate `ζ(w) = ε log w / (2π)`. It inverts the end lift on `ℂ ∖ {0}`
(`cylindricalEndLift_endCoord`); its real part is the longitudinal coordinate `s` and its imaginary
part an angular coordinate `t`, determined by the point only modulo `1`. -/
def endCoord (p : PSSPlane) (w : ℂ) : ℂ :=
  (p.endSign / (2 * π) : ℝ) * Complex.log w

theorem endCoord_def (p : PSSPlane) (w : ℂ) :
    p.endCoord w = (p.endSign / (2 * π) : ℝ) * Complex.log w :=
  (rfl)

/-- The longitudinal coordinate of a point of the plane. -/
theorem re_endCoord (p : PSSPlane) (w : ℂ) :
    (p.endCoord w).re = p.endSign / (2 * π) * Real.log ‖w‖ := by
  rw [endCoord_def, Complex.re_ofReal_mul, Complex.log_re]

/-- The angular coordinate of a point of the plane. -/
theorem im_endCoord (p : PSSPlane) (w : ℂ) :
    (p.endCoord w).im = p.endSign / (2 * π) * Complex.arg w := by
  rw [endCoord_def, Complex.im_ofReal_mul, Complex.log_im]

/-- **The signed longitudinal coordinate is radial.** On both planes `ε s = log ‖w‖ / (2π)`. -/
@[simp]
theorem endSign_mul_re_endCoord (p : PSSPlane) (w : ℂ) :
    p.endSign * (p.endCoord w).re = Real.log ‖w‖ / (2 * π) := by
  rw [re_endCoord, ← mul_assoc, mul_div_assoc', endSign_mul_endSign, one_div_mul_eq_div]

/-- **The signed angular coordinate is the argument.** On both planes `ε t = arg w / (2π)`. -/
@[simp]
theorem endSign_mul_im_endCoord (p : PSSPlane) (w : ℂ) :
    p.endSign * (p.endCoord w).im = Complex.arg w / (2 * π) := by
  rw [im_endCoord, ← mul_assoc, mul_div_assoc', endSign_mul_endSign, one_div_mul_eq_div]

/-- The pole `0` has longitudinal coordinate `0`, the junk value of the logarithm of `0`. -/
@[simp]
theorem endCoord_zero (p : PSSPlane) : p.endCoord 0 = 0 := by
  simp [endCoord_def]

/-- The end coordinate is a right inverse of the end lift away from the pole. -/
theorem cylindricalEndLift_endCoord (p : PSSPlane) {w : ℂ} (hw : w ≠ 0) :
    p.cylindricalEndLift (p.endCoord w) = w := by
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  rw [cylindricalEndLift_def, endCoord_def, ← mul_assoc, ← Complex.ofReal_mul,
    show 2 * π * p.endSign * (p.endSign / (2 * π)) = p.endSign * p.endSign by field_simp,
    endSign_mul_endSign, Complex.ofReal_one, one_mul, Complex.exp_log hw]

/-- The end coordinate recovers a cylinder point from its image under the end lift, up to an
integer shift of the angular coordinate. -/
theorem exists_endCoord_cylindricalEndLift (p : PSSPlane) (z : ℂ) :
    ∃ k : ℤ, p.endCoord (p.cylindricalEndLift z) = z + k * Complex.I := by
  obtain ⟨n, hn⟩ := Complex.log_exp_exists ((2 * π * p.endSign : ℝ) * z)
  have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [endCoord_def, cylindricalEndLift_def, hn]
  cases p
  · refine ⟨n, ?_⟩
    simp only [endSign_positive]
    push_cast
    field_simp
  · refine ⟨-n, ?_⟩
    simp only [endSign_negative]
    push_cast
    field_simp
    ring

/-- The longitudinal coordinate of the image of a cylinder point is its real part. -/
@[simp]
theorem re_endCoord_cylindricalEndLift (p : PSSPlane) (z : ℂ) :
    (p.endCoord (p.cylindricalEndLift z)).re = z.re := by
  obtain ⟨k, hk⟩ := p.exists_endCoord_cylindricalEndLift z
  simp [hk]

/-- The norm of the image of a cylinder point is `exp (2π ε s)`. -/
theorem norm_cylindricalEndLift (p : PSSPlane) (z : ℂ) :
    ‖p.cylindricalEndLift z‖ = Real.exp (2 * π * (p.endSign * z.re)) := by
  rw [cylindricalEndLift_def, Complex.norm_exp, Complex.re_ofReal_mul, mul_assoc]

/-- The longitudinal coordinate is smooth away from the pole. -/
theorem contDiffAt_re_endCoord (p : PSSPlane) {w : ℂ} (hw : w ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fun w ↦ (p.endCoord w).re) w := by
  simp_rw [re_endCoord]
  have hid : ContDiffAt ℝ n (fun w : ℂ ↦ w) w := contDiffAt_id
  exact contDiffAt_const.mul ((hid.norm ℝ hw).log (norm_ne_zero_iff.2 hw))

/-- The angular coordinate of the plane is that of the end at `0` of the thrice-punctured sphere,
up to the sign `-ε`. -/
theorem im_endCoord_eq_neg_endSign_mul (p : PSSPlane) (w : ℂ) :
    (p.endCoord w).im =
      -p.endSign * (ThricePuncturedSphere.Puncture.zero.endCoord w).im := by
  simp [im_endCoord, ThricePuncturedSphere.Puncture.im_endCoord, ← Complex.ofReal_ofNat,
    Complex.arg_mul_real]
  ring

section Periodic

variable {E G M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smooth family `f t x` of period one in `t`, evaluated at the angular coordinate of the
plane, is smooth away from the pole, jointly with the parameter `x` in a manifold. The angular
coordinate itself jumps by `1` across a ray; periodicity removes the jump. -/
theorem contMDiffAt_comp_im_endCoord (p : PSSPlane) {n : WithTop ℕ∞} {f : ℝ → M → F}
    (hf : Function.Periodic f 1)
    (hfs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) n (Function.uncurry f)) {w : ℂ} (hw : w ≠ 0)
    (x : M) :
    ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, F) n (fun q : ℂ × M ↦ f (p.endCoord q.1).im q.2)
      (w, x) := by
  -- Reflecting the angular coordinate by `-ε` preserves periodicity and smoothness.
  set g : ℝ → M → F := fun τ y ↦ f (-p.endSign * τ) y
  have hg : Function.Periodic g 1 := fun τ ↦ by
    funext y
    cases p
    · simp only [g, endSign_positive]
      rw [show -1 * (τ + 1) = -1 * τ - 1 by ring, hf.sub_eq]
    · simp only [g, endSign_negative]
      rw [show -(-1 : ℝ) * (τ + 1) = -(-1) * τ + 1 by ring, hf]
  have hgs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) n (Function.uncurry g) := by
    have hlin : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) n
        (fun q : ℝ × M ↦ (-p.endSign * q.1, q.2)) :=
      ((contDiff_const.mul contDiff_id).contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
    exact hfs.comp hlin
  have h := ThricePuncturedSphere.Puncture.zero.contMDiffAt_comp_im_endCoord hg hgs
    (by simpa using hw) x
  refine h.congr_of_eventuallyEq (.of_forall fun q ↦ ?_)
  simp only [g, im_endCoord_eq_neg_endSign_mul]

end Periodic

/-- The angular one-form `dt` of the end, as a covector at `w`: `v ↦ Im (v / (2π ε w))`, the
imaginary part of the differential of the end coordinate. -/
def endAngularForm (p : PSSPlane) (w : ℂ) : ℂ →L[ℝ] ℝ :=
  Complex.imCLM ∘L ContinuousLinearMap.mul ℝ ℂ (((2 * π * p.endSign : ℝ) : ℂ) * w)⁻¹

theorem endAngularForm_apply (p : PSSPlane) (w v : ℂ) :
    p.endAngularForm w v = ((((2 * π * p.endSign : ℝ) : ℂ) * w)⁻¹ * v).im :=
  (rfl)

/-- The angular form pulls back to `dt` along the end lift: it sends the image `φ'(z) v` of a
tangent vector `v` of the cylinder to `Im v`. -/
@[simp]
theorem endAngularForm_cylindricalEndLift (p : PSSPlane) (z v : ℂ) :
    p.endAngularForm (p.cylindricalEndLift z) (deriv p.cylindricalEndLift z * v) = v.im := by
  have hc : ((2 * π * p.endSign : ℝ) : ℂ) * p.cylindricalEndLift z ≠ 0 :=
    mul_ne_zero (by simp [Real.pi_ne_zero, p.endSign_ne_zero]) (p.cylindricalEndLift_ne_zero z)
  rw [endAngularForm_apply, deriv_cylindricalEndLift, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- The angular form of the plane is that of the end at `0` of the thrice-punctured sphere, up to
the sign `-ε`. -/
theorem endAngularForm_eq_neg_endSign_smul (p : PSSPlane) (w : ℂ) :
    p.endAngularForm w =
      (-p.endSign) • ThricePuncturedSphere.Puncture.zero.endAngularForm w := by
  ext v
  cases p <;> simp [endAngularForm_apply, mul_comm]

/-- The angular form is smooth away from the pole. -/
theorem contDiffAt_endAngularForm (p : PSSPlane) {w : ℂ} (hw : w ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n p.endAngularForm w := by
  have h := (ThricePuncturedSphere.Puncture.zero.contDiffAt_endAngularForm (n := n)
    (by simpa using hw)).const_smul (-p.endSign)
  exact h.congr_of_eventuallyEq (.of_forall p.endAngularForm_eq_neg_endSign_smul)

/-! ### The perturbation -/

variable {M : Type*}

/-- The Hamiltonian perturbation one-form on a PSS plane given by a period-one Hamiltonian `H`.
At `w ∈ ℂ` and `x ∈ M` it is the covector `β(ε s(w) - 1) H(t(w), x) dt`, where `(s, t)` are the
end coordinates of the plane, `ε` is the sign of its end and `β` is the smooth transition from
`0` on `(-∞, 0]` to `1` on `[1, ∞)`. -/
def perturbation (p : PSSPlane) (H : ℝ → M → ℝ) (w : ℂ) (x : M) : ℂ →L[ℝ] ℝ :=
  (smoothTransition (p.endSign * (p.endCoord w).re - 1) * H (p.endCoord w).im x) •
    p.endAngularForm w

theorem perturbation_def (p : PSSPlane) (H : ℝ → M → ℝ) (w : ℂ) (x : M) :
    p.perturbation H w x =
      (smoothTransition (p.endSign * (p.endCoord w).re - 1) * H (p.endCoord w).im x) •
        p.endAngularForm w :=
  (rfl)

variable {p : PSSPlane} {H : ℝ → M → ℝ}

/-- **The perturbation vanishes on the pole disc.** On the closed disc `‖w‖ ≤ exp (2π)` about the
pole, where `ε s ≤ 1`, the perturbation is zero. -/
theorem perturbation_eq_zero_of_norm_le {w : ℂ} (hw : ‖w‖ ≤ Real.exp (2 * π)) (x : M) :
    p.perturbation H w x = 0 := by
  have hlog : Real.log ‖w‖ ≤ 2 * π := by
    rcases (norm_nonneg w).eq_or_lt with h | h
    · rw [← h, Real.log_zero]
      positivity
    · simpa using Real.log_le_log h hw
  have hs : p.endSign * (p.endCoord w).re - 1 ≤ 0 := by
    rw [endSign_mul_re_endCoord, sub_nonpos, div_le_one (by positivity)]
    exact hlog
  rw [perturbation_def, smoothTransition.zero_of_nonpos hs, zero_mul, zero_smul]

/-- Near every point of the open pole disc `‖w‖ < exp (2π)`, the perturbation vanishes
identically. -/
theorem eventually_perturbation_eq_zero {w : ℂ} (hw : ‖w‖ < Real.exp (2 * π)) :
    ∀ᶠ w' in 𝓝 w, ∀ x : M, p.perturbation H w' x = 0 := by
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hw] with w' hw' x
  exact perturbation_eq_zero_of_norm_le (le_of_lt hw') x

/-- **The perturbation on the end.** At every point of the cylinder, the pullback of the
perturbation along the end lift `φ` is the continuation datum `β(ε s - 1) H(t) dt`: it sends a
tangent vector `v` of the cylinder to `Im v · β(ε s - 1) H(t)`. -/
theorem perturbation_cylindricalEndLift (hH : Function.Periodic H 1) (z : ℂ) (x : M) (v : ℂ) :
    p.perturbation H (p.cylindricalEndLift z) x (deriv p.cylindricalEndLift z * v) =
      v.im * (smoothTransition (p.endSign * z.re - 1) * H z.im x) := by
  obtain ⟨k, hk⟩ := p.exists_endCoord_cylindricalEndLift z
  have hp : H (z.im + k) x = H z.im x := by simpa using congrFun (hH.int_mul k z.im) x
  rw [perturbation_def, smul_apply, endAngularForm_cylindricalEndLift,
    re_endCoord_cylindricalEndLift, hk]
  simp [hp, mul_comm]

/-- **The perturbation is `H(t) dt` far out on the end.** On the part `ε s ≥ 2` of the end, the
pullback of the perturbation along the end lift `φ` sends a tangent vector `v` of the cylinder to
`Im v · H(t)`: its `ds` component vanishes and its `dt` component is `H(t)`. -/
theorem perturbation_cylindricalEndLift_of_two_le (hH : Function.Periodic H 1) {z : ℂ}
    (hz : 2 ≤ p.endSign * z.re) (x : M) (v : ℂ) :
    p.perturbation H (p.cylindricalEndLift z) x (deriv p.cylindricalEndLift z * v) =
      v.im * H z.im x := by
  rw [perturbation_cylindricalEndLift hH, smoothTransition.one_of_one_le (by linarith), one_mul]

/-- **The perturbation is `H(t) dt` far out on the end.** At a point `w` of the part `ε s ≥ 2` of
the end, the perturbation is the angular form scaled by `H` at the angular coordinate of `w`. -/
theorem perturbation_eq_smul_endAngularForm {w : ℂ} (hw : 2 ≤ p.endSign * (p.endCoord w).re)
    (x : M) : p.perturbation H w x = H (p.endCoord w).im x • p.endAngularForm w := by
  rw [perturbation_def, smoothTransition.one_of_one_le (by linarith), one_mul]

/-- The perturbation is supported outside the closed pole disc: where it is nonzero,
`exp (2π) < ‖w‖`. -/
theorem exp_lt_norm_of_perturbation_ne_zero {w : ℂ} {x : M} (h : p.perturbation H w x ≠ 0) :
    Real.exp (2 * π) < ‖w‖ :=
  lt_of_not_ge fun hw ↦ h (perturbation_eq_zero_of_norm_le hw x)

/-- The component of the perturbation along the tangent vector `v` of the cylinder, in the end
coordinates `z = (s, t)`: the pullback of the perturbation along the end lift `φ`, evaluated at the
point `s + i t` on `v`. The components `K_s` and `K_t` of the pulled-back datum `K_s ds + K_t dt`
are those along `v = 1` and `v = i`. -/
def endComponent (p : PSSPlane) (H : ℝ → M → ℝ) (v : ℂ) (z : ℝ × ℝ) (x : M) : ℝ :=
  p.perturbation H (p.cylindricalEndLift ⟨z.1, z.2⟩) x (deriv p.cylindricalEndLift ⟨z.1, z.2⟩ * v)

theorem endComponent_def (p : PSSPlane) (H : ℝ → M → ℝ) (v : ℂ) (z : ℝ × ℝ) (x : M) :
    p.endComponent H v z x =
      p.perturbation H (p.cylindricalEndLift ⟨z.1, z.2⟩) x
        (deriv p.cylindricalEndLift ⟨z.1, z.2⟩ * v) :=
  (rfl)

/-- The component of the perturbation along `v` in end coordinates is `Im v · β(ε s - 1) H(t)`. -/
theorem endComponent_eq (hH : Function.Periodic H 1) (v : ℂ) :
    p.endComponent H v = fun z x ↦ v.im * (smoothTransition (p.endSign * z.1 - 1) * H z.2 x) := by
  funext z x
  exact perturbation_cylindricalEndLift hH _ x v

/-- The `ds` component of the perturbation in end coordinates vanishes. -/
@[simp]
theorem endComponent_one : p.endComponent H 1 = fun _ _ ↦ 0 := by
  funext z x
  rw [endComponent_def, perturbation_def, smul_apply, endAngularForm_cylindricalEndLift]
  simp

/-- The `dt` component of the perturbation in end coordinates is `β(ε s - 1) H(t)`. -/
theorem endComponent_I (hH : Function.Periodic H 1) :
    p.endComponent H Complex.I = fun z x ↦ smoothTransition (p.endSign * z.1 - 1) * H z.2 x := by
  simp [endComponent_eq hH]

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- **The perturbation is smooth.** For a Hamiltonian of period one which is `C^n` on `ℝ × M`, the
perturbation is `C^n` on the whole of `ℂ × M`, including across the pole, near which it
vanishes. -/
theorem contMDiff_perturbation {n : ℕ∞} (hH : Function.Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (Function.uncurry H)) :
    ContMDiff (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun q : ℂ × M ↦ p.perturbation H q.1 q.2) := by
  rintro ⟨w, x⟩
  by_cases hw : ‖w‖ < Real.exp (2 * π)
  · -- Near the pole the perturbation vanishes identically.
    refine (contMDiffAt_const (c := (0 : ℂ →L[ℝ] ℝ))).congr_of_eventuallyEq ?_
    have h := (eventually_perturbation_eq_zero (p := p) (H := H) (M := M) hw).prod_inl_nhds x
    filter_upwards [h] with q hq
    exact hq q.2
  · have hw₀ : w ≠ 0 := by
      rintro rfl
      exact hw (by simpa using Real.exp_pos _)
    have hβ : ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℝ) n
        (fun q : ℂ × M ↦ smoothTransition (p.endSign * (p.endCoord q.1).re - 1)) (w, x) :=
      (smoothTransition.contDiff.contDiffAt.comp w
        ((contDiffAt_const.mul (p.contDiffAt_re_endCoord hw₀)).sub
          contDiffAt_const)).contMDiffAt.comp (w, x) contMDiffAt_fst
    have hf : ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
        (fun q : ℂ × M ↦ p.endAngularForm q.1) (w, x) :=
      ContMDiffAt.comp (I' := 𝓘(ℝ, ℂ)) (g := p.endAngularForm) _
        (p.contDiffAt_endAngularForm hw₀).contMDiffAt contMDiffAt_fst
    exact (hβ.smul (p.contMDiffAt_comp_im_endCoord hH hHs hw₀ x)).smul hf

/-- In the real coordinates `ℝ × ℝ ≃ ℂ` of the plane, the component of the perturbation of a PSS
plane along a tangent vector `v` is `C¹` jointly in the domain point and the target point, for a
period-one `C¹` Hamiltonian. -/
theorem contDiff_uncurry_perturbation {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {H : ℝ → V → ℝ} (hH : Function.Periodic H 1) (hHs : ContDiff ℝ 1 (Function.uncurry H))
    (v : ℂ) :
    ContDiff ℝ 1
      (Function.uncurry fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x v) :=
  ((contMDiff_prod_modelWithCornersSelf_iff.1 (contMDiff_perturbation hH
      (contMDiff_prod_modelWithCornersSelf_iff.2 hHs.contMDiff))).contDiff.comp
    ((Complex.equivRealProdCLM.symm.contDiff.comp contDiff_fst).prodMk contDiff_snd)).clm_apply
    contDiff_const

end PSSPlane

end TauCeti.Floer
