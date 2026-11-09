/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Capping
public import TauCeti.Geometry.Symplectic.Floer.Manifold
import TauCeti.Analysis.Complex.ThricePuncturedSphere.Exchange
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
import TauCeti.Geometry.Symplectic.Floer.Pullback

/-!
# Perturbation data on spheres with moving input ends

The associativity of the pair-of-pants product compares the two ways of composing two products,
which are the plumbed four-punctured spheres `TauCeti.Floer.plumbedPerturbation` with the inserted
pair of pants in the input `0` or in the input `1` of the receiving one. As the neck length
grows these two spheres break in the two different ways, and the associativity homotopy counts a
one-parameter family of four-punctured spheres joining them. Along such a family the punctures
move in the plane, and the asymptotic markers of the input ends turn: in the first plumbing the
third input sits at `1` with the end lift `1 - exp (-2πz) / 2`, while in the second it is the
second input of the inserted pair of pants, with the end lift `ψ(1) + g exp (-2πz) / 2` for a
small positive number `g`. This file constructs perturbation data on the spheres of such
families.

An input end is described by a centre `c ∈ ℂ` and a nonzero complex scale `a`: its end lift is
`z ↦ c + a φ₀(z)`, where `φ₀(z) = exp (-2πz) / 2` is the end lift of the input `0` of the
thrice-punctured sphere `S = ℂ ∖ {0, 1}`. The argument of `a` is the direction of its asymptotic
marker. The datum `TauCeti.Floer.inputEndPerturbation H c a` is the pushforward of the positive
plane datum `TauCeti.Floer.positivePlanePerturbation H` along the affine map `w ↦ c + a w`. It is
`β(s - 1) H(t) dt` in the end coordinates `(s, t)` of the end, and it vanishes off the disc of
radius `‖a‖ exp (-2π) / 2` about `c`.

Given finitely many input ends `(c i, a i)` with Hamiltonians `H i` and an output Hamiltonian
`H₀`, the datum `TauCeti.Floer.multiInputPerturbation H H₀ c a` is the sum of the input data and
the negative plane datum `TauCeti.Floer.negativePlanePerturbation H₀` of the output end at `∞`. The
main results are the following.

* `TauCeti.Floer.pairOfPantsPerturbation_eq_multiInputPerturbation`: the pair-of-pants datum is
  the datum with the two input ends `(0, 1)` and `(1, -1)`.
* `TauCeti.Floer.inputEndPerturbation_comp_mul` and
  `TauCeti.Floer.plumbedPerturbation_eq_inputEndPerturbation_add`: an affine pushforward moves an
  input end to an input end, so on the inserted half of a plumbed sphere the two inputs of the
  inserted pair of pants are the input ends `(c_q, f)` and `(ψ(1), -f)`, where `f` is the
  plumbing factor.
* `TauCeti.Floer.multiInputPerturbation_cylindricalEndLift` and
  `TauCeti.Floer.multiInputPerturbation_cylindricalEndLift_inf`: if the closed discs of radius
  `‖a i‖ / 2` about the centres are pairwise disjoint and lie in the closed disc of radius `2`,
  the datum is `H_i(t) dt` far out on every input end and `H₀(t) dt` far out on the output end.
* `TauCeti.Floer.contMDiffAt_multiInputPerturbation`: the datum is jointly smooth in the centres,
  the scales, the domain point off the centres and the target point.
* `TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_multiInputPerturbation_le`: under
  the same separation, the integrated curvature `∫ |R_K|` along any map into a manifold is at most
  `∑ i, B i + B₀`, where `|H i| ≤ B i` and `|H₀| ≤ B₀`. The bound does not depend on the centres
  or the scales, which is the uniform curvature bound needed for compactness along a family.

Joining the two plumbed spheres by a family of such data also needs the neck of each plumbed
sphere to be switched off; that cutoff is not constructed here.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the associativity of the pair-of-pants product.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Section 9, on
  perturbation data over families of punctured surfaces with ends.
-/

public noncomputable section

open Set Real Manifold Topology Function
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture
open TauCeti.Complex (realChart realChart_apply contDiff_realChart realChart_injective)

namespace TauCeti.Floer

variable {M : Type*}

/-! ### One input end -/

/-- The perturbation datum of an input end with centre `c` and scale `a`: the pushforward
`v ↦ K((w - c) / a)(v / a)` of the positive plane datum `K` of `H` along the affine map
`w ↦ c + a w`. Its end lift is `z ↦ c + a exp (-2πz) / 2`, and it vanishes off the disc of radius
`‖a‖ exp (-2π) / 2` about `c`. -/
def inputEndPerturbation (H : ℝ → M → ℝ) (c a : ℂ) (w : ℂ) (x : M) : ℂ →L[ℝ] ℝ :=
  (positivePlanePerturbation H ((w - c) / a) x).comp (ContinuousLinearMap.mul ℝ ℂ a⁻¹)

theorem inputEndPerturbation_def (H : ℝ → M → ℝ) (c a : ℂ) (w : ℂ) (x : M) :
    inputEndPerturbation H c a w x =
      (positivePlanePerturbation H ((w - c) / a) x).comp (ContinuousLinearMap.mul ℝ ℂ a⁻¹) :=
  (rfl)

theorem inputEndPerturbation_apply (H : ℝ → M → ℝ) (c a : ℂ) (w : ℂ) (x : M) (v : ℂ) :
    inputEndPerturbation H c a w x v = positivePlanePerturbation H ((w - c) / a) x (a⁻¹ * v) :=
  (rfl)

/-- The input end with centre `0` and scale `1` is the input end at `0` of the positive plane. -/
@[simp]
theorem inputEndPerturbation_zero_one (H : ℝ → M → ℝ) :
    inputEndPerturbation H 0 1 = positivePlanePerturbation H := by
  funext w x
  ext v
  simp [inputEndPerturbation_apply]

/-- **Affine maps move input ends.** The pushforward of the datum of the input end `(c, a)` along
the affine map `w ↦ c' + f w` is the datum of the input end `(c' + f c, f a)`. -/
theorem inputEndPerturbation_comp_mul (H : ℝ → M → ℝ) (c a c' f : ℂ) (w : ℂ) (x : M) :
    (inputEndPerturbation H c a ((w - c') / f) x).comp (ContinuousLinearMap.mul ℝ ℂ f⁻¹) =
      inputEndPerturbation H (c' + f * c) (f * a) w x := by
  ext v
  rcases eq_or_ne f 0 with rfl | hf
  · simp [inputEndPerturbation_apply]
  rcases eq_or_ne a 0 with rfl | ha
  · simp [inputEndPerturbation_apply]
  · have hw : ((w - c') / f - c) / a = (w - (c' + f * c)) / (f * a) := by
      field_simp
      ring
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
      inputEndPerturbation_apply, hw]
    congr 1
    rw [mul_inv]
    ring

/-- **The input `1` of the pair of pants is an input end.** The pair-of-pants datum whose only
nonzero Hamiltonian is the input Hamiltonian `H` at `1` is the datum of the input end with centre
`1` and scale `-1`. -/
@[simp]
theorem pairOfPantsPerturbation_single_one (H : ℝ → M → ℝ) :
    pairOfPantsPerturbation (Pi.single one H) = inputEndPerturbation H 1 (-1) := by
  funext w x
  ext v
  have h : (w - 1) / -1 = 1 - w := by ring
  rw [pairOfPantsPerturbation_def, Fintype.sum_eq_single one fun q hq => by
    simp [Pi.single_eq_of_ne hq], inputEndPerturbation_apply, h, positivePlanePerturbation_def,
    endCoord_zero_one_sub, endAngularForm_zero_one_sub]
  simp [endSign_eq_one (show one ≠ inf by decide)]
  ring

/-- The input part of the pair-of-pants datum is the sum of the data of the input ends `(0, 1)`
and `(1, -1)`. -/
private theorem pairOfPantsPerturbation_update_inf (H : Puncture → ℝ → M → ℝ) (w : ℂ) (x : M) :
    pairOfPantsPerturbation (update H inf 0) w x =
      inputEndPerturbation (H zero) 0 1 w x + inputEndPerturbation (H one) 1 (-1) w x := by
  have hsplit : update H inf 0 = Pi.single zero (H zero) + Pi.single one (H one) := by
    funext q
    cases q <;> simp
  rw [hsplit, pairOfPantsPerturbation_add, Pi.add_apply, Pi.add_apply,
    pairOfPantsPerturbation_single_zero, pairOfPantsPerturbation_single_one,
    inputEndPerturbation_zero_one]

/-- The datum of an input end vanishes off the disc of radius `‖a‖ exp (-2π) / 2` about its
centre. -/
theorem inputEndPerturbation_eq_zero_of_le_norm {H : ℝ → M → ℝ} {c a w : ℂ}
    (hw : ‖a‖ * (Real.exp (-(2 * π)) / 2) ≤ ‖w - c‖) (x : M) :
    inputEndPerturbation H c a w x = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · ext v
    simp [inputEndPerturbation_apply]
  · rw [inputEndPerturbation_def, positivePlanePerturbation_eq_zero_of_le_norm
      (by rwa [norm_div, le_div_iff₀ (norm_pos_iff.2 ha), mul_comm]) x,
      ContinuousLinearMap.zero_comp]

/-- **The datum on the end.** On the half-plane `Re z > 0`, the pullback of the datum of the input
end `(c, a)` along its end lift `z ↦ c + a φ₀(z)` is `β(s - 1) H(t) dt`: it sends a tangent
vector `v` of the cylinder to `Im v · β(Re z - 1) H(Im z)`. -/
theorem inputEndPerturbation_cylindricalEndLift_of_pos {H : ℝ → M → ℝ} (hH : Periodic H 1)
    {c a : ℂ} (ha : a ≠ 0) {z : ℂ} (hz : 0 < z.re) (x : M) (v : ℂ) :
    inputEndPerturbation H c a (c + a * zero.cylindricalEndLift z) x
        (a * deriv zero.cylindricalEndLift z * v) =
      v.im * (smoothTransition (z.re - 1) * H z.im x) := by
  rw [inputEndPerturbation_apply, add_sub_cancel_left, mul_div_cancel_left₀ _ ha, mul_assoc,
    inv_mul_cancel_left₀ ha, positivePlanePerturbation_cylindricalEndLift_of_pos hH hz]

/-! ### Spheres with several input ends -/

variable {ι : Type*} [Fintype ι]

/-- **The perturbation datum on a sphere with moving input ends.** For input ends with centres
`c i` and scales `a i` carrying the Hamiltonians `H i`, and the output end at `∞` carrying `H₀`,
this is the sum of the data of the input ends (`TauCeti.Floer.inputEndPerturbation`) and the
negative plane datum of `H₀`, whose end at `∞` has the end lift `z ↦ 2 exp (-2πz)`. -/
def multiInputPerturbation (H : ι → ℝ → M → ℝ) (H₀ : ℝ → M → ℝ) (c a : ι → ℂ) (w : ℂ) (x : M) :
    ℂ →L[ℝ] ℝ :=
  ∑ i, inputEndPerturbation (H i) (c i) (a i) w x + negativePlanePerturbation H₀ w x

theorem multiInputPerturbation_def (H : ι → ℝ → M → ℝ) (H₀ : ℝ → M → ℝ) (c a : ι → ℂ) (w : ℂ)
    (x : M) :
    multiInputPerturbation H H₀ c a w x =
      ∑ i, inputEndPerturbation (H i) (c i) (a i) w x + negativePlanePerturbation H₀ w x :=
  (rfl)

/-- **The pair of pants has two input ends.** The pair-of-pants datum of `H` is the datum of the
sphere with the input ends `(0, 1)` and `(1, -1)`, carrying `H₀` and `H₁`, and the output
Hamiltonian `H_∞`. -/
theorem pairOfPantsPerturbation_eq_multiInputPerturbation (H : Puncture → ℝ → M → ℝ) :
    pairOfPantsPerturbation H =
      multiInputPerturbation ![H zero, H one] (H inf) ![0, 1] ![1, -1] := by
  funext w x
  rw [pairOfPantsPerturbation_eq_update_inf_add_negativePlanePerturbation,
    pairOfPantsPerturbation_update_inf, multiInputPerturbation_def, Fin.sum_univ_two]
  simp

/-- **The inputs of an inserted pair of pants are input ends.** On the half `Re z > L/2` of the
end `q` where the plumbed datum is the pushforward of the inserted pair of pants along the
plumbing map `ψ(w) = c_q + f w`, it is the sum of the data of the input ends `(c_q, f)` and
`(ψ(1), -f)`, carrying the two input Hamiltonians of the inserted pair of pants, and of the
pushforward of its output datum. -/
theorem plumbedPerturbation_eq_inputEndPerturbation_add (Ha Hb : Puncture → ℝ → M → ℝ)
    (q : Puncture) (L : ℝ) {w : ℂ} (hw : L / 2 < (q.endCoord w).re) (x : M) :
    plumbedPerturbation Ha Hb q L w x =
      inputEndPerturbation (Ha zero) q.endCenter (q.plumbingFactor L) w x +
        inputEndPerturbation (Ha one) (q.plumbingMap L 1) (-q.plumbingFactor L) w x +
        (negativePlanePerturbation (Ha inf) ((w - q.endCenter) / q.plumbingFactor L) x).comp
          (ContinuousLinearMap.mul ℝ ℂ (q.plumbingFactor L)⁻¹) := by
  rw [plumbedPerturbation_def, ite_eq_left_of_eq_true _ _ (eq_true hw),
    pairOfPantsPerturbation_eq_update_inf_add_negativePlanePerturbation,
    pairOfPantsPerturbation_update_inf, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.add_comp, inputEndPerturbation_comp_mul,
    inputEndPerturbation_comp_mul, plumbingMap_apply]
  simp

variable {H : ι → ℝ → M → ℝ} {H₀ : ℝ → M → ℝ} {c a : ι → ℂ}

/-- The radius `exp (-2π) / 2` of the support of the positive plane datum is less than `1 / 2`. -/
private theorem exp_neg_two_pi_div_two_lt : Real.exp (-(2 * π)) / 2 < 1 / 2 := by
  have : Real.exp (-(2 * π)) < 1 := Real.exp_lt_one_iff.2 (by linarith [Real.pi_pos])
  linarith

/-- The radius `2` of the input region is at most the radius `2 exp (2π)` of the pole disc of the
negative plane. -/
private theorem two_le_two_mul_exp_two_pi : (2 : ℝ) ≤ 2 * Real.exp (2 * π) := by
  nlinarith [Real.one_le_exp (by positivity : (0 : ℝ) ≤ 2 * π)]

/-- Where all input data but the `i`-th vanish and the output datum vanishes, the datum is that of
the `i`-th input end. -/
private theorem multiInputPerturbation_eq_inputEndPerturbation {i : ι} {w : ℂ}
    (hj : ∀ j ≠ i, ‖a j‖ * (Real.exp (-(2 * π)) / 2) ≤ ‖w - c j‖)
    (hw : ‖w‖ ≤ 2 * Real.exp (2 * π)) (x : M) :
    multiInputPerturbation H H₀ c a w x = inputEndPerturbation (H i) (c i) (a i) w x := by
  classical
  rw [multiInputPerturbation_def, negativePlanePerturbation_eq_zero_of_norm_le hw, add_zero,
    Finset.sum_eq_single i (fun j _ hji => inputEndPerturbation_eq_zero_of_le_norm (hj j hji) x)
      (by simp)]

/-- Where all input data vanish, the datum is the negative plane datum of the output end. -/
private theorem multiInputPerturbation_eq_negativePlanePerturbation {w : ℂ}
    (hj : ∀ j, ‖a j‖ * (Real.exp (-(2 * π)) / 2) ≤ ‖w - c j‖) (x : M) :
    multiInputPerturbation H H₀ c a w x = negativePlanePerturbation H₀ w x := by
  simp [multiInputPerturbation_def, inputEndPerturbation_eq_zero_of_le_norm (hj _)]

/-- On the part `Re z > 0` of an input end, the end lift stays in the open disc of radius
`‖a‖ / 2` about the centre. -/
private theorem norm_mul_cylindricalEndLift_lt {a : ℂ} (ha : a ≠ 0) {z : ℂ} (hz : 0 < z.re) :
    ‖a * zero.cylindricalEndLift z‖ < ‖a‖ / 2 := by
  have h := norm_cylindricalEndLift_sub_endCenter zero z
  rw [endCenter_zero, sub_zero, norm_endScale (by decide)] at h
  rw [norm_mul, h, mul_comm (1 / 2 : ℝ), ← mul_assoc, mul_one_div]
  refine div_lt_div_of_pos_right ?_ two_pos
  refine mul_lt_of_lt_one_right (norm_pos_iff.2 ha) ?_
  exact Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos])

/-- **The datum on an input end.** Suppose the closed disc of radius `‖a i‖ / 2` about `c i` is
disjoint from the closed discs of radius `‖a j‖ / 2` about the other centres and lies in the closed
disc of radius `2`. On the half-plane `Re z > 0`, the pullback of the datum along the end lift
`z ↦ c i + a i φ₀(z)` of the input end `i` is `β(s - 1) H_i(t) dt`: it sends a tangent vector `v`
of the cylinder to `Im v · β(Re z - 1) H_i(Im z)`. -/
theorem multiInputPerturbation_cylindricalEndLift_of_pos {i : ι} (hH : Periodic (H i) 1)
    (ha : a i ≠ 0) (hsep : ∀ j ≠ i, ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hin : ‖c i‖ + ‖a i‖ / 2 ≤ 2) {z : ℂ} (hz : 0 < z.re) (x : M) (v : ℂ) :
    multiInputPerturbation H H₀ c a (c i + a i * zero.cylindricalEndLift z) x
        (a i * deriv zero.cylindricalEndLift z * v) =
      v.im * (smoothTransition (z.re - 1) * H i z.im x) := by
  have hr := norm_mul_cylindricalEndLift_lt ha hz
  refine (congrArg (· (a i * deriv zero.cylindricalEndLift z * v))
    (multiInputPerturbation_eq_inputEndPerturbation (i := i) (fun j hj => ?_) ?_ x)).trans
    (inputEndPerturbation_cylindricalEndLift_of_pos hH ha hz x v)
  · -- The other input data vanish near the end of the input `i`.
    have h := norm_sub_norm_le (c i - c j) (c i + a i * zero.cylindricalEndLift z - c j)
    rw [show c i - c j - (c i + a i * zero.cylindricalEndLift z - c j) =
      -(a i * zero.cylindricalEndLift z) by ring, norm_neg] at h
    nlinarith [hsep j hj, exp_neg_two_pi_div_two_lt, norm_nonneg (a j)]
  · -- The output datum vanishes in the closed disc of radius `2`.
    calc ‖c i + a i * zero.cylindricalEndLift z‖
        ≤ ‖c i‖ + ‖a i * zero.cylindricalEndLift z‖ := norm_add_le _ _
      _ ≤ 2 := by linarith
      _ ≤ 2 * Real.exp (2 * π) := two_le_two_mul_exp_two_pi

/-- **The datum is `H_i(t) dt` far out on an input end.** Under the separation hypotheses of
`TauCeti.Floer.multiInputPerturbation_cylindricalEndLift_of_pos`, on the part `s ≥ 2` of the input
end `i` the pullback of the datum along its end lift sends a tangent vector `v` of the cylinder to
`Im v · H_i(Im z)`. -/
theorem multiInputPerturbation_cylindricalEndLift {i : ι} (hH : Periodic (H i) 1)
    (ha : a i ≠ 0) (hsep : ∀ j ≠ i, ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hin : ‖c i‖ + ‖a i‖ / 2 ≤ 2) {z : ℂ} (hz : 2 ≤ z.re) (x : M) (v : ℂ) :
    multiInputPerturbation H H₀ c a (c i + a i * zero.cylindricalEndLift z) x
        (a i * deriv zero.cylindricalEndLift z * v) =
      v.im * H i z.im x := by
  rw [multiInputPerturbation_cylindricalEndLift_of_pos hH ha hsep hin (by linarith),
    smoothTransition.one_of_one_le (by linarith), one_mul]

/-- **The datum on the output end.** If every closed disc of radius `‖a j‖ / 2` about `c j` lies in
the closed disc of radius `2`, then on the half-plane `Re z < 0` the pullback of the datum along
the end lift `φ_∞` of the output end is `β(-s - 1) H₀(t) dt`: it sends a tangent vector `v` of the
cylinder to `Im v · β(-Re z - 1) H₀(Im z)`. -/
theorem multiInputPerturbation_cylindricalEndLift_inf_of_neg (hH₀ : Periodic H₀ 1)
    (hin : ∀ j, ‖c j‖ + ‖a j‖ / 2 ≤ 2) {z : ℂ} (hz : z.re < 0) (x : M) (v : ℂ) :
    multiInputPerturbation H H₀ c a (inf.cylindricalEndLift z) x
        (deriv inf.cylindricalEndLift z * v) =
      v.im * (smoothTransition (-z.re - 1) * H₀ z.im x) := by
  -- The end lift at `∞` stays outside the closed disc of radius `2` on the part `s < 0`.
  have hφ : 2 < ‖inf.cylindricalEndLift z‖ := by
    have h := norm_cylindricalEndLift_sub_endCenter inf z
    rw [endCenter_inf, sub_zero, endScale_inf, Complex.norm_ofNat] at h
    have : 1 < Real.exp (-(2 * π * z.re)) :=
      Real.one_lt_exp_iff.2 (by nlinarith [Real.pi_pos])
    linarith
  rw [multiInputPerturbation_eq_negativePlanePerturbation (fun j => ?_) x,
    negativePlanePerturbation_cylindricalEndLift_of_neg hH₀ hz]
  have h := norm_sub_norm_le (inf.cylindricalEndLift z) (c j)
  nlinarith [hin j, exp_neg_two_pi_div_two_lt, norm_nonneg (a j), norm_nonneg (c j)]

/-- **The datum is `H₀(t) dt` far out on the output end.** If every closed disc of radius
`‖a j‖ / 2` about `c j` lies in the closed disc of radius `2`, then on the part `s ≤ -2` of the
output end the pullback of the datum along its end lift sends a tangent vector `v` of the cylinder
to `Im v · H₀(Im z)`. -/
theorem multiInputPerturbation_cylindricalEndLift_inf (hH₀ : Periodic H₀ 1)
    (hin : ∀ j, ‖c j‖ + ‖a j‖ / 2 ≤ 2) {z : ℂ} (hz : z.re ≤ -2) (x : M) (v : ℂ) :
    multiInputPerturbation H H₀ c a (inf.cylindricalEndLift z) x
        (deriv inf.cylindricalEndLift z * v) =
      v.im * H₀ z.im x := by
  rw [multiInputPerturbation_cylindricalEndLift_inf_of_neg hH₀ hin (by linarith),
    smoothTransition.one_of_one_le (by linarith), one_mul]

/-! ### Smoothness -/

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- **The datum of an input end is smooth in its centre and scale.** For a Hamiltonian of period
one which is `C^n` on `ℝ × M`, the datum of the input end `(c, a)` is `C^n` jointly in the centre,
the nonzero scale, the domain point off the centre and the target point. -/
theorem contMDiffAt_inputEndPerturbation_family {n : ℕ∞} {H : ℝ → M → ℝ} (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry H)) {c a w : ℂ} (ha : a ≠ 0)
    (hw : w ≠ c) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℂ × ℂ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : (ℂ × ℂ) × (ℂ × M) => inputEndPerturbation H p.1.1 p.1.2 p.2.1 p.2.2)
      ((c, a), (w, x)) := by
  have hcoord : ContMDiffAt (𝓘(ℝ, ℂ × ℂ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ) n
      (fun p : (ℂ × ℂ) × (ℂ × M) => (p.2.1 - p.1.1) / p.1.2) ((c, a), (w, x)) := by
    have hg : ContDiffAt ℝ n (fun y : (ℂ × ℂ) × ℂ => (y.2 - y.1.1) / y.1.2) ((c, a), w) :=
      ((contDiffAt_snd.sub (contDiffAt_fst.comp _ contDiffAt_fst)).mul
        ((contDiffAt_inv ℝ ha).comp _ (contDiffAt_snd.comp _ contDiffAt_fst)))
    exact hg.contMDiffAt.comp_of_eq
      (contMDiffAt_fst.prodMk_space (contMDiffAt_fst.comp _ contMDiffAt_snd)) rfl
  -- A covector is pushed forward by composition with multiplication by the inverse scale.
  have hmul : ContMDiffAt (𝓘(ℝ, ℂ × ℂ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℂ) n
      (fun p : (ℂ × ℂ) × (ℂ × M) => ContinuousLinearMap.mul ℝ ℂ (p.1.2)⁻¹) ((c, a), (w, x)) :=
    ((ContinuousLinearMap.mul ℝ ℂ).contDiff.contDiffAt.comp a
      (contDiffAt_inv ℝ ha)).contMDiffAt.comp_of_eq
      (contDiff_snd.contMDiff.contMDiffAt.comp _ contMDiffAt_fst) rfl
  have hw' : (w - c) / a ≠ 0 := div_ne_zero (sub_ne_zero.2 hw) ha
  exact ((contMDiffAt_positivePlanePerturbation hH hHs hw' x).comp ((c, a), (w, x))
    (hcoord.prodMk (contMDiffAt_snd.comp _ contMDiffAt_snd))).clm_comp hmul

/-- The datum of a fixed input end is smooth off its centre. -/
theorem contMDiffAt_inputEndPerturbation {n : ℕ∞} {H : ℝ → M → ℝ} (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry H)) {c a w : ℂ} (ha : a ≠ 0)
    (hw : w ≠ c) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℂ × M => inputEndPerturbation H c a p.1 p.2) (w, x) :=
  (contMDiffAt_inputEndPerturbation_family hH hHs ha hw x).comp (w, x)
    (contMDiffAt_const.prodMk contMDiffAt_id)

/-- **The datum is smooth along families.** For period-one Hamiltonians which are `C^n` on
`ℝ × M`, the datum is `C^n` jointly in the centres, the nonzero scales, the domain point off the
centres and the target point. No separation of the ends is needed. -/
theorem contMDiffAt_multiInputPerturbation {n : ℕ∞} (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (H i))) (hH₀ : Periodic H₀ 1)
    (hH₀s : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry H₀)) (ha : ∀ i, a i ≠ 0) {w : ℂ}
    (hw : ∀ i, w ≠ c i) (x : M) :
    ContMDiffAt (𝓘(ℝ, (ι → ℂ) × (ι → ℂ)).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ((ι → ℂ) × (ι → ℂ)) × (ℂ × M) =>
        multiInputPerturbation H H₀ p.1.1 p.1.2 p.2.1 p.2.2) ((c, a), (w, x)) := by
  -- Each input datum is the smooth datum of one input end composed with the evaluation at `i`.
  have hin (i : ι) : ContMDiffAt (𝓘(ℝ, (ι → ℂ) × (ι → ℂ)).prod (𝓘(ℝ, ℂ).prod I))
      𝓘(ℝ, ℂ →L[ℝ] ℝ) n (fun p : ((ι → ℂ) × (ι → ℂ)) × (ℂ × M) =>
        inputEndPerturbation (H i) (p.1.1 i) (p.1.2 i) p.2.1 p.2.2) ((c, a), (w, x)) := by
    have hev : ContMDiffAt (𝓘(ℝ, (ι → ℂ) × (ι → ℂ)).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ × ℂ) n
        (fun p : ((ι → ℂ) × (ι → ℂ)) × (ℂ × M) => (p.1.1 i, p.1.2 i)) ((c, a), (w, x)) := by
      have hg : ContDiff ℝ n (fun y : (ι → ℂ) × (ι → ℂ) => (y.1 i, y.2 i)) := by fun_prop
      exact hg.contMDiff.contMDiffAt.comp _ contMDiffAt_fst
    exact (contMDiffAt_inputEndPerturbation_family (hH i) (hHs i) (ha i) (hw i) x).comp
      (f := fun p : ((ι → ℂ) × (ι → ℂ)) × (ℂ × M) => ((p.1.1 i, p.1.2 i), p.2)) _
      (hev.prodMk contMDiffAt_snd)
  have hout : ContMDiffAt (𝓘(ℝ, (ι → ℂ) × (ι → ℂ)).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ((ι → ℂ) × (ι → ℂ)) × (ℂ × M) => negativePlanePerturbation H₀ p.2.1 p.2.2)
      ((c, a), (w, x)) :=
    (contMDiff_negativePlanePerturbation hH₀ hH₀s).contMDiffAt.comp _ contMDiffAt_snd
  exact (ContMDiffAt.sum fun i _ => hin i).add hout

end TauCeti.Floer

namespace TauCeti.SmoothTwoForm

open Floer MeasureTheory

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

omit [TopologicalSpace M] in
/-- The pullback of the datum of an input end along its affine chart is the positive plane datum,
in the real coordinates used by `TauCeti.Floer.perturbationPullback`. -/
private theorem perturbationPullback_inputEndPerturbation {H : ℝ → M → ℝ} {c a : ℂ} (ha : a ≠ 0)
    (v : ℂ) (z : ℝ × ℝ) (x : M) :
    perturbationPullback (realChart fun w : ℂ => c + a * w)
        (fun z x ↦ inputEndPerturbation H c a (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ inputEndPerturbation H c a (Complex.equivRealProdCLM.symm z) x Complex.I)
        (Complex.equivRealProdCLM v) z x =
      positivePlanePerturbation H (Complex.equivRealProdCLM.symm z) x v := by
  have hd : HasDerivAt (fun w : ℂ => c + a * w) a (Complex.equivRealProdCLM.symm z) := by
    simpa using ((hasDerivAt_id _).const_mul a).const_add c
  rw [perturbationPullback_realChart (P := inputEndPerturbation H c a) hd,
    ContinuousLinearEquiv.symm_apply_apply,
    inputEndPerturbation_apply, add_sub_cancel_left, mul_div_cancel_left₀ _ ha,
    inv_mul_cancel_left₀ ha]

variable [IsManifold I ⊤ M]

omit [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M] in
/-- The affine chart `w ↦ c + a w` maps the plane minus the pole `0` onto the plane minus the
centre `c`. -/
private theorem univ_subset_image_realChart_affine (c : ℂ) {a : ℂ} (ha : a ≠ 0) :
    univ ⊆ realChart (fun w : ℂ => c + a * w) '' {z | Complex.equivRealProdCLM.symm z ≠ 0} ∪
      {Complex.equivRealProdCLM c} := by
  intro z _
  by_cases hz : Complex.equivRealProdCLM.symm z = c
  · exact Or.inr (by simp [← hz])
  · refine Or.inl ⟨Complex.equivRealProdCLM ((Complex.equivRealProdCLM.symm z - c) / a), ?_, ?_⟩
    · simp only [mem_ofPred_eq, ContinuousLinearEquiv.symm_apply_apply]
      exact div_ne_zero (sub_ne_zero.2 hz) ha
    · apply Complex.equivRealProdCLM.symm.injective
      simp only [realChart_apply, ContinuousLinearEquiv.symm_apply_apply]
      field_simp
      ring

omit [IsManifold I ⊤ M] in
/-- Off the centre, the components of the datum of an input end are differentiable in the domain
point. -/
private theorem differentiableAt_inputEndPerturbation_domain {H : ℝ → M → ℝ} (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {c a : ℂ} (ha : a ≠ 0)
    {z : ℝ × ℝ} (hz : Complex.equivRealProdCLM.symm z ≠ c) (y : M) (v : ℂ) :
    DifferentiableAt ℝ (fun z' ↦ inputEndPerturbation H c a (Complex.equivRealProdCLM.symm z') y v)
      z := by
  have h := (contMDiffAt_inputEndPerturbation hH hHs ha hz y).comp
    (f := fun w : ℂ ↦ (w, y)) _ (contMDiffAt_id.prodMk contMDiffAt_const)
  exact ((h.contDiffAt.differentiableAt one_ne_zero).comp _
    Complex.equivRealProdCLM.symm.differentiableAt).clm_apply (differentiableAt_const v)

omit [IsManifold I ⊤ M] in
/-- Off the centre, the components of the datum of an input end are differentiable in the target
point. -/
private theorem mdifferentiableAt_inputEndPerturbation_target {H : ℝ → M → ℝ}
    (hH : Periodic H 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {c a w : ℂ}
    (ha : a ≠ 0) (hw : w ≠ c) (y : M) (v : ℂ) :
    MDifferentiableAt I 𝓘(ℝ) (fun y ↦ inputEndPerturbation H c a w y v) y :=
  (((contMDiffAt_inputEndPerturbation hH hHs ha hw y).comp (f := fun y : M ↦ (w, y)) y
    (contMDiffAt_const.prodMk contMDiffAt_id)).clm_apply contMDiffAt_const).mdifferentiableAt
    one_ne_zero

/-- **The integrated curvature of one input end.** For a period-one `C¹` Hamiltonian with
`|H| ≤ B` and a nonzero scale `a`, the integral of the curvature `|R_K(z, u(z))|` of the datum of
the input end `(c, a)` over the plane is at most `B`, for every map `u` into the target. -/
theorem lintegral_enorm_hamiltonianCurvature_inputEndPerturbation_le (ω : SmoothTwoForm I M)
    {H : ℝ → M → ℝ} (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {B : ℝ}
    (hB : ∀ t x, |H t x| ≤ B) {c a : ℂ} (ha : a ≠ 0) (u : ℝ × ℝ → M) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ inputEndPerturbation H c a (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ inputEndPerturbation H c a (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ENNReal.ofReal B := by
  set e := Complex.equivRealProdCLM.symm
  set φ := realChart fun w : ℂ => c + a * w
  -- The affine chart maps the plane minus the pole onto the plane minus the centre, and pulls the
  -- datum back to the positive plane datum.
  set S : Set (ℝ × ℝ) := {z | e z ≠ 0}
  have hSm : MeasurableSet S :=
    (measurableSet_singleton 0).compl.preimage e.continuous.measurable
  have hN : volume ({Complex.equivRealProdCLM c} : Set (ℝ × ℝ)) = 0 := by
    rw [Measure.volume_eq_prod]
    exact measure_singleton _
  have hne {w : ℝ × ℝ} (hw : w ∈ S) : e (φ w) ≠ c := by
    simp only [φ, e, realChart_apply, ContinuousLinearEquiv.symm_apply_apply, ne_eq,
      add_eq_left, mul_eq_zero, ha, false_or]
    exact hw
  have hpull (v : ℂ) :
      perturbationPullback φ (fun z x ↦ inputEndPerturbation H c a (e z) x 1)
          (fun z x ↦ inputEndPerturbation H c a (e z) x Complex.I)
          (Complex.equivRealProdCLM v) =
        fun z x ↦ positivePlanePerturbation H (e z) x v :=
    funext fun z ↦ funext fun x ↦ perturbationPullback_inputEndPerturbation ha v z x
  calc _ = ∫⁻ z in univ, ‖ω.hamiltonianCurvature
        (fun z x ↦ inputEndPerturbation H c a (e z) x 1)
        (fun z x ↦ inputEndPerturbation H c a (e z) x Complex.I) z (u z)‖ₑ :=
        (setLIntegral_univ _).symm
    _ ≤ _ := lintegral_mono_set (univ_subset_image_realChart_affine c ha)
    _ ≤ _ := lintegral_union_le _ _ _
    _ = ∫⁻ z in φ '' S, ‖ω.hamiltonianCurvature
        (fun z x ↦ inputEndPerturbation H c a (e z) x 1)
        (fun z x ↦ inputEndPerturbation H c a (e z) x Complex.I) z (u z)‖ₑ := by
        rw [setLIntegral_measure_zero _ _ hN, add_zero]
    _ = ∫⁻ w in S, ‖ω.hamiltonianCurvature
        (fun z x ↦ positivePlanePerturbation H (e z) x 1)
        (fun z x ↦ positivePlanePerturbation H (e z) x Complex.I) w (u (φ w))‖ₑ := by
        rw [ω.lintegral_enorm_hamiltonianCurvature_image hSm
          (realChart_injective (f := fun w : ℂ => c + a * w)
            fun _ _ h ↦ mul_left_cancel₀ ha (add_left_cancel h)).injOn
          (fun w _ ↦ (contDiff_realChart (by fun_prop)).contDiffAt)
          (fun w hw ↦ differentiableAt_inputEndPerturbation_domain hH hHs ha (hne hw) _ 1)
          (fun w hw ↦ differentiableAt_inputEndPerturbation_domain hH hHs ha (hne hw) _ Complex.I)
          (fun w hw ↦ mdifferentiableAt_inputEndPerturbation_target hH hHs ha (hne hw) _ 1)
          (fun w hw ↦ mdifferentiableAt_inputEndPerturbation_target hH hHs ha (hne hw) _
            Complex.I), ← equivRealProdCLM_one, ← equivRealProdCLM_I, hpull 1, hpull Complex.I]
    _ ≤ _ := setLIntegral_le_lintegral _ _
    _ ≤ _ := lintegral_enorm_hamiltonianCurvature_positivePlanePerturbation_le ω hH hHs hB _

variable {ι : Type*} [Fintype ι] {H : ι → ℝ → M → ℝ} {H₀ : ℝ → M → ℝ} {c a : ι → ℂ}

omit [TopologicalSpace M] [IsManifold I ⊤ M] in
/-- Near a point of the open disc of radius `‖a i‖ / 2` about `c i`, the datum is that of the
input end `i`, when the closed discs of radius `‖a j‖ / 2` about the centres are pairwise disjoint
and lie in the closed disc of radius `2`. -/
private theorem eventually_multiInputPerturbation_eq_inputEndPerturbation
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hin : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2) {i : ι} {w : ℂ} (hw : ‖w - c i‖ < ‖a i‖ / 2) :
    ∀ᶠ w' in 𝓝 w, multiInputPerturbation H H₀ c a w' =
      inputEndPerturbation (H i) (c i) (a i) w' := by
  -- The other input data vanish near `w`.
  have hj : ∀ᶠ w' in 𝓝 w, ∀ j, j ≠ i →
      ‖a j‖ * (Real.exp (-(2 * π)) / 2) < ‖w' - c j‖ := by
    refine Filter.eventually_all.2 fun j => ?_
    rcases eq_or_ne j i with rfl | hji
    · exact .of_forall fun _ h => absurd rfl h
    · have h := norm_sub_norm_le (c i - c j) (w - c j)
      rw [show c i - c j - (w - c j) = -(w - c i) by ring, norm_neg] at h
      have hlt : ‖a j‖ * (Real.exp (-(2 * π)) / 2) < ‖w - c j‖ := by
        nlinarith [hsep hji.symm, Floer.exp_neg_two_pi_div_two_lt, norm_nonneg (a j)]
      filter_upwards [(continuous_norm.comp (continuous_id.sub continuous_const)).continuousAt
        |>.eventually (lt_mem_nhds hlt)] with w' hw' _ using hw'
  -- The output datum vanishes near `w`.
  have hout : ∀ᶠ w' in 𝓝 w, ‖w'‖ < 2 * Real.exp (2 * π) := by
    have h : ‖w‖ < 2 * Real.exp (2 * π) := by
      calc ‖w‖ ≤ ‖c i‖ + ‖w - c i‖ := by
            simpa [add_sub_cancel] using norm_add_le (c i) (w - c i)
        _ < 2 := by linarith [hin i]
        _ ≤ 2 * Real.exp (2 * π) := Floer.two_le_two_mul_exp_two_pi
    exact continuous_norm.continuousAt.eventually (gt_mem_nhds h)
  filter_upwards [hj, hout] with w' hw' hw'' using funext fun x =>
    Floer.multiInputPerturbation_eq_inputEndPerturbation (fun j hji => (hw' j hji).le) hw''.le x

omit [Fintype ι] [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M] in
/-- If the scales are nonzero, the plane is covered by the open discs of radius `‖a i‖ / 2` about
the centres and the open set where every input datum vanishes. -/
private theorem univ_subset_iUnion_union_iInter (ha : ∀ i, a i ≠ 0) :
    univ ⊆ (⋃ i, {z : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm z - c i‖ < ‖a i‖ / 2}) ∪
      ⋂ i, {z | ‖a i‖ * (Real.exp (-(2 * π)) / 2) < ‖Complex.equivRealProdCLM.symm z - c i‖} := by
  intro z _
  by_cases h : ∃ i, ‖Complex.equivRealProdCLM.symm z - c i‖ < ‖a i‖ / 2
  · exact Or.inl (mem_iUnion.2 h)
  · push Not at h
    refine Or.inr (mem_iInter.2 fun i => ?_)
    have hpos : 0 < ‖a i‖ := norm_pos_iff.2 (ha i)
    simp only [mem_ofPred_eq]
    nlinarith [h i, Floer.exp_neg_two_pi_div_two_lt]

/-- On the open disc of radius `‖a i‖ / 2` about `c i`, the integrated curvature of the datum is
that of the input end `i`, hence at most `B i`. -/
private theorem setLIntegral_enorm_hamiltonianCurvature_multiInputPerturbation_le_inputEnd
    (ω : SmoothTwoForm I M) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i)))
    {B : ι → ℝ} (hB : ∀ i t x, |H i t x| ≤ B i) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hin : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2) (u : ℝ × ℝ → M) (i : ι) :
    ∫⁻ z in {z : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm z - c i‖ < ‖a i‖ / 2},
      ‖ω.hamiltonianCurvature
        (fun z x ↦ multiInputPerturbation H H₀ c a (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ multiInputPerturbation H H₀ c a (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ENNReal.ofReal (B i) := by
  set e := Complex.equivRealProdCLM.symm
  have hA : IsOpen {z : ℝ × ℝ | ‖e z - c i‖ < ‖a i‖ / 2} :=
    isOpen_lt (e.continuous.sub continuous_const).norm continuous_const
  have hR {z : ℝ × ℝ} (hz : ‖e z - c i‖ < ‖a i‖ / 2) :
      ω.hamiltonianCurvature (fun z x ↦ multiInputPerturbation H H₀ c a (e z) x 1)
        (fun z x ↦ multiInputPerturbation H H₀ c a (e z) x Complex.I) z =
      ω.hamiltonianCurvature (fun z x ↦ inputEndPerturbation (H i) (c i) (a i) (e z) x 1)
        (fun z x ↦ inputEndPerturbation (H i) (c i) (a i) (e z) x Complex.I) z := by
    have hP := (e.continuous.tendsto z).eventually
      (eventually_multiInputPerturbation_eq_inputEndPerturbation (H := H) (H₀ := H₀) hsep hin hz)
    exact ω.hamiltonianCurvature_congr_of_eventuallyEq
      (hP.mono fun z' hz' ↦ funext fun x ↦ by simp only [hz'])
      (hP.mono fun z' hz' ↦ funext fun x ↦ by simp only [hz'])
  calc _ = _ := setLIntegral_congr_fun hA.measurableSet fun z hz => by rw [hR hz]
    _ ≤ _ := setLIntegral_le_lintegral _ _
    _ ≤ _ := lintegral_enorm_hamiltonianCurvature_inputEndPerturbation_le ω (hH i) (hHs i) (hB i)
        (ha i) u

/-- On the open set where every input datum vanishes, the integrated curvature of the datum is that
of the output end, hence at most `B₀`. -/
private theorem setLIntegral_enorm_hamiltonianCurvature_multiInputPerturbation_le_output
    (ω : SmoothTwoForm I M) (hH₀ : Periodic H₀ 1)
    (hH₀s : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H₀)) {B₀ : ℝ}
    (hB₀ : ∀ t x, |H₀ t x| ≤ B₀) (u : ℝ × ℝ → M) :
    ∫⁻ z in ⋂ i, {z | ‖a i‖ * (Real.exp (-(2 * π)) / 2) < ‖Complex.equivRealProdCLM.symm z - c i‖},
      ‖ω.hamiltonianCurvature
        (fun z x ↦ multiInputPerturbation H H₀ c a (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ multiInputPerturbation H H₀ c a (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ENNReal.ofReal B₀ := by
  set e := Complex.equivRealProdCLM.symm
  set U := ⋂ i, {z | ‖a i‖ * (Real.exp (-(2 * π)) / 2) < ‖e z - c i‖}
  have hU : IsOpen U := isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const (e.continuous.sub continuous_const).norm
  have hR {z : ℝ × ℝ} (hz : z ∈ U) :
      ω.hamiltonianCurvature (fun z x ↦ multiInputPerturbation H H₀ c a (e z) x 1)
        (fun z x ↦ multiInputPerturbation H H₀ c a (e z) x Complex.I) z =
      ω.hamiltonianCurvature (fun z x ↦ negativePlanePerturbation H₀ (e z) x 1)
        (fun z x ↦ negativePlanePerturbation H₀ (e z) x Complex.I) z := by
    have hP : ∀ᶠ z' in 𝓝 z, multiInputPerturbation H H₀ c a (e z') =
        negativePlanePerturbation H₀ (e z') := by
      filter_upwards [hU.mem_nhds hz] with z' hz'
      exact funext fun x => Floer.multiInputPerturbation_eq_negativePlanePerturbation
        (fun j => (mem_iInter.1 hz' j).le) x
    exact ω.hamiltonianCurvature_congr_of_eventuallyEq
      (hP.mono fun z' hz' ↦ funext fun x ↦ by simp only [hz'])
      (hP.mono fun z' hz' ↦ funext fun x ↦ by simp only [hz'])
  calc _ = _ := setLIntegral_congr_fun hU.measurableSet fun z hz => by rw [hR hz]
    _ ≤ _ := setLIntegral_le_lintegral _ _
    _ ≤ _ := lintegral_enorm_hamiltonianCurvature_negativePlanePerturbation_le ω hH₀ hH₀s hB₀ u

/-- **The integrated curvature of a sphere with input ends is bounded uniformly.** Let `K` be the
datum `TauCeti.Floer.multiInputPerturbation` of period-one `C¹` Hamiltonians `H i` on the input
ends `(c i, a i)` and `H₀` on the output end, with `|H i| ≤ B i` and `|H₀| ≤ B₀`, and write its
components in the global coordinate `z = s + i t` of `ℂ` as `K_s(z) = K(z)(1)` and
`K_t(z) = K(z)(i)`. Suppose that the scales are nonzero and the closed discs of radius `‖a i‖ / 2`
about the centres are pairwise disjoint and lie in the closed disc of radius `2`. Then for every
map `u` into the target the integral of `|R_K(z, u(z))|` over the plane is at most
`∑ i, B i + B₀`. The bound does not depend on the centres or the scales. -/
theorem lintegral_enorm_hamiltonianCurvature_multiInputPerturbation_le (ω : SmoothTwoForm I M)
    (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i)))
    (hH₀ : Periodic H₀ 1) (hH₀s : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H₀))
    {B : ι → ℝ} {B₀ : ℝ} (hB : ∀ i t x, |H i t x| ≤ B i) (hB₀ : ∀ t x, |H₀ t x| ≤ B₀)
    (ha : ∀ i, a i ≠ 0) (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hin : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2) (u : ℝ × ℝ → M) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ multiInputPerturbation H H₀ c a (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ multiInputPerturbation H H₀ c a (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ∑ i, ENNReal.ofReal (B i) + ENNReal.ofReal B₀ := by
  -- The plane is covered by the open discs of radius `‖a i‖ / 2` about the centres, where the
  -- datum is that of one input end, and the open set where it is that of the output end.
  calc _ = ∫⁻ z in univ, _ := (setLIntegral_univ _).symm
    _ ≤ _ := lintegral_mono_set (univ_subset_iUnion_union_iInter ha)
    _ ≤ _ := lintegral_union_le _ _ _
    _ ≤ _ := add_le_add_left ((lintegral_iUnion_le _ _).trans_eq (tsum_fintype _)) _
    _ ≤ _ := add_le_add (Finset.sum_le_sum fun i _ =>
        setLIntegral_enorm_hamiltonianCurvature_multiInputPerturbation_le_inputEnd ω hH hHs hB ha
          hsep hin u i)
        (setLIntegral_enorm_hamiltonianCurvature_multiInputPerturbation_le_output ω hH₀ hH₀s hB₀ u)

end TauCeti.SmoothTwoForm

namespace TauCeti.SymplecticForm

open Floer MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type*} [Fintype ι] {H : ι → ℝ → V → ℝ} {H₀ : ℝ → V → ℝ} {c a : ι → ℂ}

/-- **The integrated curvature of a sphere with input ends is bounded uniformly.** This is the
vector-space case of
`TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_multiInputPerturbation_le`: for
period-one `C¹` Hamiltonians on a symplectic vector space with `|H i| ≤ B i` and `|H₀| ≤ B₀`,
nonzero scales, and closed discs of radius `‖a i‖ / 2` about the centres that are pairwise
disjoint and lie in the closed disc of radius `2`, the integral of `|R_K(z, u(z))|` over the plane
is at most `∑ i, B i + B₀` for every map `u` into it. -/
theorem lintegral_enorm_hamiltonianCurvature_multiInputPerturbation_le (ω : SymplecticForm V)
    (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 1 (uncurry (H i)))
    (hH₀ : Periodic H₀ 1) (hH₀s : ContDiff ℝ 1 (uncurry H₀))
    {B : ι → ℝ} {B₀ : ℝ} (hB : ∀ i t x, |H i t x| ≤ B i) (hB₀ : ∀ t x, |H₀ t x| ≤ B₀)
    (ha : ∀ i, a i ≠ 0) (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hin : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2) (u : ℝ × ℝ → V) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ multiInputPerturbation H H₀ c a (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ multiInputPerturbation H H₀ c a (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ∑ i, ENNReal.ofReal (B i) + ENNReal.ofReal B₀ := by
  simpa using ω.constSmooth.lintegral_enorm_hamiltonianCurvature_multiInputPerturbation_le hH
    (fun i ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHs i).contMDiff) hH₀
    (contMDiff_prod_modelWithCornersSelf_iff.2 hH₀s.contMDiff) hB hB₀ ha hsep hin u

end TauCeti.SymplecticForm
