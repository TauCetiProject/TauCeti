/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Capping
import TauCeti.Geometry.Symplectic.Floer.Pullback
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Hamiltonian perturbation data on spheres with moving input ends

The associativity of the pair-of-pants product compares the two ways of composing two products.
Both are ends of one family of four-punctured spheres: the inputs sit at moving punctures of
`ℂ`, the output at `∞`, and along the family two inputs collide in one of the two possible ways.
The family needs Hamiltonian perturbation data whose ends move with the punctures. This file
constructs such data for any finite set of input ends.

An input end is given by a center `c` and a nonzero scale `a`: its end lift is
`z ↦ c + a φ₀(z)`, where `φ₀(z) = exp (-2πz) / 2` is the end lift of the input end at `0` of the
pair of pants `ℂ ∖ {0, 1}`. The datum `TauCeti.Floer.inputEndPerturbation c a H` is the pushforward
along the affine map `w ↦ c + a w` of the positive plane datum
`TauCeti.Floer.positivePlanePerturbation H`, the pair-of-pants datum whose only nonzero
Hamiltonian is `H` at the input `0`. In the coordinates `(s, t)` of the moved end it is
`β(s - 1) H(t) dt`, and it vanishes off the disc `‖w - c‖ < ‖a‖ exp (-2π) / 2`. For finitely many
input ends with centers `c i`, scales `a i` and period-one Hamiltonians `H i`, and an output
Hamiltonian `Hout` at `∞`, `TauCeti.Floer.puncturedSpherePerturbation c a H Hout` is the sum of the
input data and the negative plane datum `TauCeti.Floer.negativePlanePerturbation Hout` of the
output end.

Suppose that the discs `‖w - c i‖ < ‖a i‖ / 2` are pairwise disjoint and lie in the disc
`‖w‖ ≤ 2 exp (2π)` on which the output datum vanishes. Then:

* near each input end the datum is that end's datum alone, off the closed supports of the input
  end data it is the output datum, and between the ends it vanishes, all as germs
  (`TauCeti.Floer.puncturedSpherePerturbation_eventuallyEq_inputEndPerturbation`,
  `TauCeti.Floer.puncturedSpherePerturbation_eventuallyEq_negativePlanePerturbation`,
  `TauCeti.Floer.puncturedSpherePerturbation_eventuallyEq_zero`); far out on an input end it is
  `H i(t) dt` (`TauCeti.Floer.puncturedSpherePerturbation_cylindricalEndLift`); far out on the
  output end it is `Hout(t) dt`
  (`TauCeti.Floer.puncturedSpherePerturbation_cylindricalEndLift_inf`);
* it is `C^n` jointly in the centers, the scales, the domain point and the target point, away
  from the punctures (`TauCeti.Floer.contMDiffAt_puncturedSpherePerturbation`), so it is a smooth
  family over any smooth path of configurations; for a fixed configuration and a normed target,
  `TauCeti.Floer.contDiffAt_puncturedSpherePerturbation_prod` is the form in real coordinates,
  and for a fixed configuration and a manifold target the components of the datum in real
  coordinates are `C^n` off the centers
  (`TauCeti.Floer.contMDiffOn_uncurry_puncturedSpherePerturbation_apply`);
* for a symplectic vector space target, its integrated curvature along any map is at most
  `∑ i, sup |H i| + sup |Hout|`, whatever the configuration
  (`TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_puncturedSpherePerturbation_le`),
  and likewise for a manifold target with a two-form
  (`TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_puncturedSpherePerturbation_le`).
  This bound only needs the smaller supports `‖w - c i‖ < ‖a i‖ exp (-2π) / 2` of the input end
  data to be pairwise disjoint and to lie in the disc `‖w‖ ≤ 2 exp (2π)`.

For `R ≥ 1` the truncation `TauCeti.Floer.puncturedSphereTruncation c a R` is the disc
`‖w‖ ≤ 2 exp (2πR)`, bounded by the circle `s = -R` of the output end, with the discs
`‖w - c i‖ < ‖a i‖ exp (-2πR) / 2`, bounded by the circles `s = R` of the input ends, removed. If
the supports `‖w - c i‖ < ‖a i‖ exp (-2π) / 2` of the input end data are pairwise disjoint and lie
in the disc `‖w‖ ≤ 2 exp (2π)`, it contains the closed annulus of each end between its circles
`±s = 1` and `±s = R`
(`TauCeti.Floer.closedBall_sdiff_ball_subset_puncturedSphereTruncation`,
`TauCeti.Floer.closedBall_zero_sdiff_ball_subset_puncturedSphereTruncation`). Off the boundary
circles `±s = 1` of these annuli the datum there is that end's datum, as germs
(`TauCeti.Floer.puncturedSpherePerturbation_eventuallyEq_inputEndPerturbation_of_norm_sub_lt`,
`TauCeti.Floer.puncturedSpherePerturbation_eventuallyEq_negativePlanePerturbation_of_lt_norm`), and
between the annuli it vanishes
(`TauCeti.Floer.puncturedSpherePerturbation_eventuallyEq_zero_of_mem_puncturedSphereTruncation`).

The pair-of-pants datum itself is the case of the inputs `0` and `1` with scales `1` and `-1`
(`TauCeti.Floer.puncturedSpherePerturbation_eq_pairOfPantsPerturbation`), and with one input
switched off it is the case of the single input end of the other input
(`TauCeti.Floer.pairOfPantsPerturbation_update_zero_eq_puncturedSpherePerturbation`).

## References

* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Sections 9 and 10, on
  families of punctured discs with strip-like ends and consistent perturbation data over them.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  Hamiltonian perturbations and their curvature.
-/

public noncomputable section

open Set Real Manifold Topology Function
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

variable {M : Type*}

/-- The factor `exp (-2π)` relating the radius of the support of an input end datum to the radius
of its end disc is less than `1`. -/
private theorem exp_neg_two_pi_lt_one : Real.exp (-(2 * π)) < 1 :=
  Real.exp_lt_one_iff.2 (by linarith [Real.pi_pos])

section InputEnd

variable {H : ℝ → M → ℝ} {c a : ℂ}

/-- The datum of an input end with center `c` and scale `a`: the pushforward
`v ↦ K((w - c) / a)(v / a)` along the affine map `w ↦ c + a w` of the positive plane datum `K` of
`H`, the pair-of-pants datum whose only nonzero Hamiltonian is `H`, at the input `0`. Its end lift
is `z ↦ c + a φ₀(z)`, where `φ₀` is the end lift of the input `0`, and in the coordinates `(s, t)`
of that end lift it is `β(s - 1) H(t) dt` (`inputEndPerturbation_cylindricalEndLift_apply`). -/
def inputEndPerturbation (c a : ℂ) (H : ℝ → M → ℝ) (w : ℂ) (x : M) : ℂ →L[ℝ] ℝ :=
  (positivePlanePerturbation H ((w - c) / a) x).comp (ContinuousLinearMap.mul ℝ ℂ a⁻¹)

theorem inputEndPerturbation_apply (c a : ℂ) (H : ℝ → M → ℝ) (w : ℂ) (x : M) (v : ℂ) :
    inputEndPerturbation c a H w x v =
      positivePlanePerturbation H ((w - c) / a) x (a⁻¹ * v) :=
  (rfl)

/-- The pullback of the input end datum along the affine map `w ↦ c + a w` is the positive plane
datum of `H`. -/
theorem inputEndPerturbation_add_mul (ha : a ≠ 0) (w : ℂ) (x : M) (v : ℂ) :
    inputEndPerturbation c a H (c + a * w) x (a * v) = positivePlanePerturbation H w x v := by
  rw [inputEndPerturbation_apply, add_sub_cancel_left, mul_div_cancel_left₀ _ ha,
    inv_mul_cancel_left₀ ha]

/-- In real coordinates, the pullback of the input end datum along the affine chart `w ↦ c + a w`
is the positive plane datum of `H`. -/
theorem perturbationPullback_realChart_inputEndPerturbation (ha : a ≠ 0) (v : ℝ × ℝ) :
    perturbationPullback (Complex.realChart (c + a * ·))
      (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x Complex.I) v =
      fun w x ↦ positivePlanePerturbation H (Complex.equivRealProdCLM.symm w) x
        (Complex.equivRealProdCLM.symm v) := by
  funext w x
  rw [perturbationPullback_realChart _
    (by simpa using ((hasDerivAt_id _).const_mul a).const_add c), inputEndPerturbation_add_mul ha]

/-- **The support of an input end datum.** It vanishes off the disc
`‖w - c‖ < ‖a‖ exp (-2π) / 2`. -/
theorem inputEndPerturbation_eq_zero_of_le_norm_sub {w : ℂ}
    (hw : ‖a‖ * Real.exp (-(2 * π)) / 2 ≤ ‖w - c‖) (x : M) :
    inputEndPerturbation c a H w x = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · ext v
    simp [inputEndPerturbation_apply]
  · rw [inputEndPerturbation, positivePlanePerturbation_eq_zero_of_le_norm ?_ x,
      ContinuousLinearMap.zero_comp]
    rw [norm_div, le_div_iff₀ (norm_pos_iff.2 ha)]
    linarith

/-- At its center `c`, where the end coordinate takes the junk longitudinal value `0` (from
`Complex.log 0 = 0`), the input end datum is `0`. -/
@[simp]
theorem inputEndPerturbation_self (c a : ℂ) (H : ℝ → M → ℝ) (x : M) :
    inputEndPerturbation c a H c x = 0 := by
  have h : (zero.endCoord 0).re = 0 := by simpa using re_endCoord_endCenter zero
  ext v
  simp [inputEndPerturbation_apply, positivePlanePerturbation_def, h,
    smoothTransition.zero_of_nonpos]

/-- The input end datum of the zero Hamiltonian vanishes. -/
@[simp]
theorem inputEndPerturbation_zero (c a : ℂ) (w : ℂ) (x : M) :
    inputEndPerturbation c a (0 : ℝ → M → ℝ) w x = 0 := by
  ext v
  simp [inputEndPerturbation_apply, positivePlanePerturbation_def]

/-- **Pushing an input end forward along an affine map.** The pushforward
`v ↦ K((w - c₀) / f)(v / f)` of the datum of the input end with center `c` and scale `a` along
`w ↦ c₀ + f w` is the datum of the input end with center `c₀ + f c` and scale `f a`. -/
theorem inputEndPerturbation_sub_div_comp (c₀ f c a : ℂ) (H : ℝ → M → ℝ) (w : ℂ) (x : M) :
    (inputEndPerturbation c a H ((w - c₀) / f) x).comp (ContinuousLinearMap.mul ℝ ℂ f⁻¹) =
      inputEndPerturbation (c₀ + f * c) (f * a) H w x := by
  ext v
  rcases eq_or_ne f 0 with rfl | hf
  · simp [inputEndPerturbation_apply]
  rcases eq_or_ne a 0 with rfl | ha
  · simp [inputEndPerturbation_apply]
  have hw : ((w - c₀) / f - c) / a = (w - (c₀ + f * c)) / (f * a) := by
    field_simp
    ring
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
    inputEndPerturbation_apply, hw, mul_inv, mul_assoc, mul_left_comm a⁻¹]

/-- **The input end datum on its end.** The pullback of the datum along its end lift
`z ↦ c + a φ₀(z)` is the continuation datum `β(s - 1) H(t) dt`. -/
theorem inputEndPerturbation_cylindricalEndLift_apply (hH : Periodic H 1) (ha : a ≠ 0) (z : ℂ)
    (x : M) (v : ℂ) :
    inputEndPerturbation c a H (c + a * zero.cylindricalEndLift z) x
        (a * (deriv zero.cylindricalEndLift z * v)) =
      v.im * (smoothTransition (z.re - 1) * H z.im x) := by
  rw [inputEndPerturbation_add_mul ha, positivePlanePerturbation_cylindricalEndLift_apply hH]

end InputEnd

section Truncation

/-! ### The truncation -/

variable {ι : Type*} {c a : ι → ℂ}

/-- The truncation at height `R` of the sphere with input ends of centers `c i` and scales `a i`
and output end at `∞`: the disc `‖w‖ ≤ 2 exp (2πR)`, bounded by the circle `s = -R` of the output
end, with the discs `‖w - c i‖ < ‖a i‖ exp (-2πR) / 2`, bounded by the circles `s = R` of the input
ends, removed. -/
def puncturedSphereTruncation (c a : ι → ℂ) (R : ℝ) : Set ℂ :=
  Metric.closedBall 0 (2 * Real.exp (2 * π * R)) \
    ⋃ i, Metric.ball (c i) (‖a i‖ * Real.exp (-(2 * π * R)) / 2)

theorem puncturedSphereTruncation_def (c a : ι → ℂ) (R : ℝ) :
    puncturedSphereTruncation c a R =
      Metric.closedBall 0 (2 * Real.exp (2 * π * R)) \
        ⋃ i, Metric.ball (c i) (‖a i‖ * Real.exp (-(2 * π * R)) / 2) :=
  (rfl)

/-- A point lies in the truncation when it lies in the disc bounded by the outer circle and outside
the discs bounded by the inner circles. -/
@[simp]
theorem mem_puncturedSphereTruncation {R : ℝ} {w : ℂ} :
    w ∈ puncturedSphereTruncation c a R ↔
      ‖w‖ ≤ 2 * Real.exp (2 * π * R) ∧
        ∀ i, ‖a i‖ * Real.exp (-(2 * π * R)) / 2 ≤ ‖w - c i‖ := by
  simp [puncturedSphereTruncation, dist_eq_norm]

/-- The truncation is compact: it is a closed disc with open discs removed. -/
theorem isCompact_puncturedSphereTruncation (c a : ι → ℂ) (R : ℝ) :
    IsCompact (puncturedSphereTruncation c a R) :=
  (isCompact_closedBall _ _).diff (isOpen_iUnion fun _ ↦ Metric.isOpen_ball)

/-- The truncation is compact in the real coordinates of `ℂ`. -/
theorem isCompact_preimage_puncturedSphereTruncation (c a : ι → ℂ) (R : ℝ) :
    IsCompact (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R) :=
  Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
    (isCompact_puncturedSphereTruncation c a R)

/-- The truncation avoids the center of every input end of nonzero scale. -/
theorem ne_of_mem_puncturedSphereTruncation {R : ℝ} {w : ℂ}
    (hw : w ∈ puncturedSphereTruncation c a R) {i : ι} (ha : a i ≠ 0) : w ≠ c i := by
  rintro rfl
  have h := (mem_puncturedSphereTruncation.1 hw).2 i
  rw [sub_self, norm_zero] at h
  nlinarith [norm_pos_iff.2 ha, Real.exp_pos (-(2 * π * R))]

/-- If the closed support `‖w - c i‖ ≤ ‖a i‖ exp (-2π) / 2` of the input end datum of `i` meets
those of the other input ends at most on its boundary and lies in the disc `‖w‖ ≤ 2 exp (2π)`,
then the closed annulus about the center `c i` with radii `‖a i‖ exp (-2πR) / 2` and
`‖a i‖ exp (-2π) / 2`, bounded by the circles `s = R` and `s = 1` of the input end `i`, lies in the
truncation, provided `R ≥ 1` or `a i ≠ 0`; in the latter case the annulus is empty unless
`R ≥ 1`. -/
theorem closedBall_sdiff_ball_subset_puncturedSphereTruncation {R : ℝ} {i : ι}
    (hsep : ∀ j, j ≠ i →
      ‖a i‖ * Real.exp (-(2 * π)) / 2 + ‖a j‖ * Real.exp (-(2 * π)) / 2 ≤ ‖c i - c j‖)
    (hout : ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ 2 * Real.exp (2 * π))
    (hR : 1 ≤ R ∨ a i ≠ 0) :
    Metric.closedBall (c i) (‖a i‖ * Real.exp (-(2 * π)) / 2) \
        Metric.ball (c i) (‖a i‖ * Real.exp (-(2 * π * R)) / 2) ⊆
      puncturedSphereTruncation c a R := by
  have hπ := Real.pi_pos
  rintro w ⟨h₂, h₁⟩
  rw [Metric.mem_closedBall, dist_eq_norm] at h₂
  rw [Metric.mem_ball, dist_eq_norm, not_lt] at h₁
  replace hR : 1 ≤ R := hR.elim id fun ha ↦ by
    have h := Real.exp_le_exp.1 (le_of_mul_le_mul_left (by linarith : ‖a i‖ *
      Real.exp (-(2 * π * R)) ≤ ‖a i‖ * Real.exp (-(2 * π))) (norm_pos_iff.2 ha))
    nlinarith
  have heR (j : ι) : ‖a j‖ * Real.exp (-(2 * π * R)) ≤ ‖a j‖ * Real.exp (-(2 * π)) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) (norm_nonneg _)
  have hR' : Real.exp (2 * π) ≤ Real.exp (2 * π * R) := Real.exp_le_exp.2 (by nlinarith)
  refine mem_puncturedSphereTruncation.2 ⟨?_, fun j ↦ ?_⟩
  · linarith [norm_le_norm_add_norm_sub' w (c i)]
  · rcases eq_or_ne j i with rfl | hji
    · exact h₁
    · have := hsep j hji
      have := norm_sub_le_norm_sub_add_norm_sub (c i) w (c j)
      rw [norm_sub_rev (c i) w] at this
      linarith [heR j]

/-- If the closed supports `‖w - c i‖ ≤ ‖a i‖ exp (-2π) / 2` of the input end data lie in the disc
`‖w‖ ≤ 2 exp (2π)`, then the closed annulus about `0` with radii `2 exp (2π)` and `2 exp (2πR)`,
bounded by the circles `s = -1` and `s = -R` of the output end, lies in the truncation. It is empty
unless `R ≥ 1`. -/
theorem closedBall_zero_sdiff_ball_subset_puncturedSphereTruncation {R : ℝ}
    (hout : ∀ i, ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ 2 * Real.exp (2 * π)) :
    Metric.closedBall 0 (2 * Real.exp (2 * π * R)) \ Metric.ball 0 (2 * Real.exp (2 * π)) ⊆
      puncturedSphereTruncation c a R := by
  rintro w ⟨h₂, h₁⟩
  rw [mem_closedBall_zero_iff] at h₂
  rw [mem_ball_zero_iff, not_lt] at h₁
  refine mem_puncturedSphereTruncation.2 ⟨h₂, fun i ↦ ?_⟩
  have hR : 1 ≤ R := by
    have h := Real.exp_le_exp.1 (by linarith : Real.exp (2 * π) ≤ Real.exp (2 * π * R))
    nlinarith [Real.pi_pos]
  have heR : ‖a i‖ * Real.exp (-(2 * π * R)) ≤ ‖a i‖ * Real.exp (-(2 * π)) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])) (norm_nonneg _)
  linarith [norm_sub_norm_le w (c i), hout i]

end Truncation

section Sphere

variable {ι : Type*} [Fintype ι] {c a : ι → ℂ} {H : ι → ℝ → M → ℝ} {Hout : ℝ → M → ℝ}

/-- **The perturbation datum on a sphere with moving input ends.** For input ends with centers
`c i`, scales `a i` and Hamiltonians `H i`, and the output end at `∞` with Hamiltonian
`Hout`, the sum of the input end data `inputEndPerturbation (c i) (a i) (H i)` and of the
negative plane datum of `Hout`. -/
def puncturedSpherePerturbation (c a : ι → ℂ) (H : ι → ℝ → M → ℝ) (Hout : ℝ → M → ℝ) (w : ℂ)
    (x : M) : ℂ →L[ℝ] ℝ :=
  ∑ i, inputEndPerturbation (c i) (a i) (H i) w x + negativePlanePerturbation Hout w x

theorem puncturedSpherePerturbation_def (c a : ι → ℂ) (H : ι → ℝ → M → ℝ) (Hout : ℝ → M → ℝ)
    (w : ℂ) (x : M) :
    puncturedSpherePerturbation c a H Hout w x =
      ∑ i, inputEndPerturbation (c i) (a i) (H i) w x + negativePlanePerturbation Hout w x :=
  (rfl)

/-- **The pair of pants has two input ends.** The pair-of-pants datum is the datum of the input
ends with centers `0` and `1` and scales `1` and `-1`, and of its output Hamiltonian. -/
theorem puncturedSpherePerturbation_eq_pairOfPantsPerturbation (H : Puncture → ℝ → M → ℝ) :
    puncturedSpherePerturbation ![0, 1] ![1, -1] ![H zero, H one] (H inf) =
      pairOfPantsPerturbation H := by
  funext w x
  have h₀ : inputEndPerturbation 0 1 (H zero) w x =
      (smoothTransition (zero.endSign * (zero.endCoord w).re - 1) *
        H zero (zero.endCoord w).im x) • zero.endAngularForm w := by
    ext v
    rw [inputEndPerturbation_apply, sub_zero, div_one, inv_one, one_mul,
      ← pairOfPantsPerturbation_single_zero, pairOfPantsPerturbation_single]
  -- The input end at `1` is the image of the input end at `0` under `w ↦ 1 - w`.
  have hc : zero.endCoord ((w - 1) / -1) = one.endCoord w := by
    rw [endCoord_def, endCoord_def, endCenter_zero, endCenter_one, endScale_zero, endScale_one]
    congr 3
    ring
  have h₁ : inputEndPerturbation 1 (-1) (H one) w x =
      (smoothTransition (one.endSign * (one.endCoord w).re - 1) *
        H one (one.endCoord w).im x) • one.endAngularForm w := by
    ext v
    rw [inputEndPerturbation_apply, ← pairOfPantsPerturbation_single_zero,
      pairOfPantsPerturbation_single, hc]
    simp only [smul_apply, endAngularForm_apply, endSign_zero, endSign_one, endCenter_zero,
      endCenter_one, div_neg, div_one, sub_zero, mul_neg, neg_neg, inv_neg]
    congr 2
    ring
  rw [puncturedSpherePerturbation_def, Fin.sum_univ_two, pairOfPantsPerturbation_def,
    Puncture.sum_univ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [h₀, h₁, negativePlanePerturbation_def, endSign_inf, neg_one_mul]

/-- **A pair of pants with one input switched off has one input end.** With the Hamiltonian of the
input `q` set to zero, the pair-of-pants datum is the datum of the single input end of the other
input `r`, with center `c_r` and scale `2 b_r`, and of the output Hamiltonian. -/
theorem pairOfPantsPerturbation_update_zero_eq_puncturedSpherePerturbation {q r : Puncture}
    (hq : q ≠ inf) (hrq : r ≠ q) (hr : r ≠ inf) (H : Puncture → ℝ → M → ℝ) :
    pairOfPantsPerturbation (update H q 0) =
      puncturedSpherePerturbation ![r.endCenter] ![2 * r.endScale] ![H r] (H inf) := by
  funext w x
  rw [← puncturedSpherePerturbation_eq_pairOfPantsPerturbation, puncturedSpherePerturbation_def,
    puncturedSpherePerturbation_def, Fin.sum_univ_two, Fin.sum_univ_one]
  cases q <;> cases r <;> simp_all

/-- **Off the input ends the datum is the output datum.** At a point outside the supports
`‖w - c i‖ < ‖a i‖ exp (-2π) / 2` of all the input end data, the datum is the negative plane
datum of the output Hamiltonian. -/
theorem puncturedSpherePerturbation_eq_negativePlanePerturbation {w : ℂ}
    (hw : ∀ i, ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ ‖w - c i‖) (x : M) :
    puncturedSpherePerturbation c a H Hout w x = negativePlanePerturbation Hout w x := by
  rw [puncturedSpherePerturbation_def,
    Finset.sum_eq_zero fun i _ => inputEndPerturbation_eq_zero_of_le_norm_sub (hw i) x, zero_add]

/-- **At a point off the supports of the other input ends the datum is that end's datum.** At a
point `w` of the disc `‖w‖ ≤ 2 exp (2π)`, where the output datum vanishes, and outside the
supports `‖w - c j‖ < ‖a j‖ exp (-2π) / 2` of the input end data of all `j ≠ i`, the datum is the
input end datum of `i`. -/
theorem puncturedSpherePerturbation_eq_inputEndPerturbation_of_forall_ne {i : ι} {w : ℂ}
    (hne : ∀ j, j ≠ i → ‖a j‖ * Real.exp (-(2 * π)) / 2 ≤ ‖w - c j‖)
    (hw : ‖w‖ ≤ 2 * Real.exp (2 * π)) (x : M) :
    puncturedSpherePerturbation c a H Hout w x = inputEndPerturbation (c i) (a i) (H i) w x := by
  rw [puncturedSpherePerturbation_def, Finset.sum_eq_single i
    (fun j _ hj => inputEndPerturbation_eq_zero_of_le_norm_sub (hne j hj) x) (by simp),
    negativePlanePerturbation_eq_zero_of_norm_le hw, add_zero]

/-- If discs `‖w - c j‖ < r j` containing the supports of the input end data are pairwise disjoint
and lie in the disc `‖w‖ ≤ 2 exp (2π)`, then on the disc of the input `i` the datum is the input
end datum of `i`. -/
private theorem puncturedSpherePerturbation_eq_inputEndPerturbation_of_norm_sub_lt
    {r : ι → ℝ} (hr : ∀ j, ‖a j‖ * Real.exp (-(2 * π)) / 2 ≤ r j)
    (hsep : Pairwise fun i j => r i + r j ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + r i ≤ 2 * Real.exp (2 * π)) {i : ι} {w : ℂ} (hw : ‖w - c i‖ < r i)
    (x : M) :
    puncturedSpherePerturbation c a H Hout w x = inputEndPerturbation (c i) (a i) (H i) w x := by
  refine puncturedSpherePerturbation_eq_inputEndPerturbation_of_forall_ne (fun j hj => ?_) ?_ x
  · have h₁ := hsep hj
    have h₂ : ‖c j - c i‖ ≤ ‖w - c i‖ + ‖w - c j‖ := by
      simpa using norm_sub_le (w - c i) (w - c j)
    linarith [hr j]
  · calc ‖w‖ ≤ ‖c i‖ + ‖w - c i‖ := by
          simpa using norm_add_le (c i) (w - c i)
      _ ≤ 2 * Real.exp (2 * π) := by linarith [hout i]

/-- **Near an input end the datum is that end's datum.** If the discs `‖w - c j‖ < ‖a j‖ / 2` are
pairwise disjoint and lie in the disc `‖w‖ ≤ 2 exp (2π)`, then on the disc of the input `i` the
datum is the input end datum of `i`. -/
theorem puncturedSpherePerturbation_eq_inputEndPerturbation
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {i : ι} {w : ℂ}
    (hw : ‖w - c i‖ < ‖a i‖ / 2) (x : M) :
    puncturedSpherePerturbation c a H Hout w x = inputEndPerturbation (c i) (a i) (H i) w x :=
  puncturedSpherePerturbation_eq_inputEndPerturbation_of_norm_sub_lt
    (fun j => by nlinarith [norm_nonneg (a j), exp_neg_two_pi_lt_one]) hsep hout hw x

/-- **Near an input end the datum is that end's datum, as germs.** Near a point `w` of the open
disc `‖w‖ < 2 exp (2π)`, where the output datum vanishes, outside the closed supports
`‖w - c j‖ ≤ ‖a j‖ exp (-2π) / 2` of the input end data of all `j ≠ i`, the datum is the input end
datum of `i`. -/
theorem puncturedSpherePerturbation_eventuallyEq_inputEndPerturbation {i : ι} {w : ℂ}
    (hne : ∀ j, j ≠ i → ‖a j‖ * Real.exp (-(2 * π)) / 2 < ‖w - c j‖)
    (hw : ‖w‖ < 2 * Real.exp (2 * π)) :
    puncturedSpherePerturbation c a H Hout =ᶠ[𝓝 w] inputEndPerturbation (c i) (a i) (H i) := by
  have hne' : ∀ᶠ w' in 𝓝 w, ∀ j, j ≠ i → ‖a j‖ * Real.exp (-(2 * π)) / 2 < ‖w' - c j‖ :=
    Filter.eventually_all.2 fun j ↦ by
      by_cases hj : j = i
      · exact Filter.Eventually.of_forall fun _ h ↦ absurd hj h
      · filter_upwards [(isOpen_lt (g := fun w' ↦ ‖w' - c j‖) continuous_const
          (by fun_prop)).mem_nhds (hne j hj)] with w' hw' using fun _ ↦ hw'
  filter_upwards [hne', (isOpen_lt continuous_norm continuous_const).mem_nhds hw] with w' h₁ h₂
  funext x
  exact puncturedSpherePerturbation_eq_inputEndPerturbation_of_forall_ne (fun j hj ↦ (h₁ j hj).le)
    h₂.le x

/-- **Off the input ends the datum is the output datum, as germs.** Near a point outside the
closed supports `‖w - c i‖ ≤ ‖a i‖ exp (-2π) / 2` of all the input end data, the datum is the
negative plane datum of the output Hamiltonian. -/
theorem puncturedSpherePerturbation_eventuallyEq_negativePlanePerturbation {w : ℂ}
    (hw : ∀ i, ‖a i‖ * Real.exp (-(2 * π)) / 2 < ‖w - c i‖) :
    puncturedSpherePerturbation c a H Hout =ᶠ[𝓝 w] negativePlanePerturbation Hout := by
  filter_upwards [Filter.eventually_all.2 fun i ↦
    (isOpen_lt (g := fun w' ↦ ‖w' - c i‖) continuous_const (by fun_prop)).mem_nhds (hw i)]
    with w' hw'
  funext x
  exact puncturedSpherePerturbation_eq_negativePlanePerturbation (fun i ↦ (hw' i).le) x

/-- **Between the ends the datum vanishes, as germs.** Near a point of the open disc
`‖w‖ < 2 exp (2π)` outside the closed supports `‖w - c i‖ ≤ ‖a i‖ exp (-2π) / 2` of all the input
end data, the datum vanishes. -/
theorem puncturedSpherePerturbation_eventuallyEq_zero {w : ℂ}
    (hw : ∀ i, ‖a i‖ * Real.exp (-(2 * π)) / 2 < ‖w - c i‖) (hw' : ‖w‖ < 2 * Real.exp (2 * π)) :
    puncturedSpherePerturbation c a H Hout =ᶠ[𝓝 w] 0 := by
  filter_upwards [puncturedSpherePerturbation_eventuallyEq_negativePlanePerturbation hw,
    (isOpen_lt continuous_norm continuous_const).mem_nhds hw'] with w' hw₁ hw₂
  funext x
  rw [hw₁]
  exact negativePlanePerturbation_eq_zero_of_norm_le hw₂.le x

/-- **On the support of an input end the datum is that end's datum, as germs.** If the closed
support `‖w - c i‖ ≤ ‖a i‖ exp (-2π) / 2` of the input end datum of `i` meets those of the other
input ends at most on its boundary and lies in the disc `‖w‖ ≤ 2 exp (2π)`, then near every point
of the open support of `i` the datum is the input end datum of `i`. -/
theorem puncturedSpherePerturbation_eventuallyEq_inputEndPerturbation_of_norm_sub_lt {i : ι}
    (hsep : ∀ j, j ≠ i →
      ‖a i‖ * Real.exp (-(2 * π)) / 2 + ‖a j‖ * Real.exp (-(2 * π)) / 2 ≤ ‖c i - c j‖)
    (hout : ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ 2 * Real.exp (2 * π)) {w : ℂ}
    (hw : ‖w - c i‖ < ‖a i‖ * Real.exp (-(2 * π)) / 2) :
    puncturedSpherePerturbation c a H Hout =ᶠ[𝓝 w] inputEndPerturbation (c i) (a i) (H i) := by
  refine puncturedSpherePerturbation_eventuallyEq_inputEndPerturbation (fun j hj ↦ ?_)
    (by linarith [norm_le_norm_add_norm_sub' w (c i)])
  have := hsep j hj
  have := norm_sub_le_norm_sub_add_norm_sub (c i) w (c j)
  rw [norm_sub_rev (c i) w] at this
  linarith

/-- **Outside the disc `‖w‖ ≤ 2 exp (2π)` the datum is the output datum, as germs**, provided the
closed supports `‖w - c i‖ ≤ ‖a i‖ exp (-2π) / 2` of the input end data lie in that disc. -/
theorem puncturedSpherePerturbation_eventuallyEq_negativePlanePerturbation_of_lt_norm
    (hout : ∀ i, ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ 2 * Real.exp (2 * π)) {w : ℂ}
    (hw : 2 * Real.exp (2 * π) < ‖w‖) :
    puncturedSpherePerturbation c a H Hout =ᶠ[𝓝 w] negativePlanePerturbation Hout :=
  puncturedSpherePerturbation_eventuallyEq_negativePlanePerturbation fun i ↦ by
    linarith [norm_sub_norm_le w (c i), hout i]

/-- **Between the annuli of the ends the datum vanishes, as germs.** Near a point of the truncation
which lies neither in the closed annulus about any center `c i` with radii `‖a i‖ exp (-2πR) / 2`
and `‖a i‖ exp (-2π) / 2` nor in the closed annulus about `0` with radii `2 exp (2π)` and
`2 exp (2πR)`, the datum vanishes. -/
theorem puncturedSpherePerturbation_eventuallyEq_zero_of_mem_puncturedSphereTruncation {R : ℝ}
    {w : ℂ} (hw : w ∈ puncturedSphereTruncation c a R)
    (hwi : ∀ i, w ∉ Metric.closedBall (c i) (‖a i‖ * Real.exp (-(2 * π)) / 2) \
      Metric.ball (c i) (‖a i‖ * Real.exp (-(2 * π * R)) / 2))
    (hwout : w ∉ Metric.closedBall 0 (2 * Real.exp (2 * π * R)) \
      Metric.ball 0 (2 * Real.exp (2 * π))) :
    puncturedSpherePerturbation c a H Hout =ᶠ[𝓝 w] 0 := by
  have hw' := mem_puncturedSphereTruncation.1 hw
  refine puncturedSpherePerturbation_eventuallyEq_zero (fun i ↦ ?_) ?_
  · by_contra! h
    exact hwi i ⟨mem_closedBall_iff_norm.2 h, fun h' ↦ (mem_ball_iff_norm.1 h').not_ge (hw'.2 i)⟩
  · by_contra! h
    exact hwout ⟨mem_closedBall_zero_iff.2 hw'.1, fun h' ↦ (mem_ball_zero_iff.1 h').not_ge h⟩

/-- **The datum on an input end.** If the discs `‖w - c j‖ < ‖a j‖ / 2` are pairwise disjoint and
lie in the disc `‖w‖ ≤ 2 exp (2π)`, then on the part `s > 0` of the input end `i`, the pullback of
the datum along the end lift `z ↦ c i + a i φ₀(z)` is the continuation datum
`β(s - 1) H i(t) dt`. -/
theorem puncturedSpherePerturbation_cylindricalEndLift_of_pos
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {i : ι} (hH : Periodic (H i) 1)
    (ha : a i ≠ 0) {z : ℂ} (hz : 0 < z.re) (x : M) (v : ℂ) :
    puncturedSpherePerturbation c a H Hout (c i + a i * zero.cylindricalEndLift z) x
        (a i * (deriv zero.cylindricalEndLift z * v)) =
      v.im * (smoothTransition (z.re - 1) * H i z.im x) := by
  have hlt : ‖c i + a i * zero.cylindricalEndLift z - c i‖ < ‖a i‖ / 2 := by
    have h := norm_cylindricalEndLift_sub_endCenter zero z
    rw [endCenter_zero, sub_zero, endScale_zero] at h
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [add_sub_cancel_left, norm_mul, h, h2]
    have : Real.exp (-(2 * π * z.re)) < 1 :=
      Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos])
    nlinarith [norm_pos_iff.2 ha]
  rw [puncturedSpherePerturbation_eq_inputEndPerturbation hsep hout hlt,
    inputEndPerturbation_cylindricalEndLift_apply hH ha]

/-- **The datum is `H i(t) dt` far out on each input end.** Under the hypotheses of
`puncturedSpherePerturbation_cylindricalEndLift_of_pos`, on the part `s ≥ 2` of the input end `i`
the pullback of the datum along its end lift sends a tangent vector `v` of the cylinder to
`Im v · H i(Im z)`. -/
theorem puncturedSpherePerturbation_cylindricalEndLift
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {i : ι} (hH : Periodic (H i) 1)
    (ha : a i ≠ 0) {z : ℂ} (hz : 2 ≤ z.re) (x : M) (v : ℂ) :
    puncturedSpherePerturbation c a H Hout (c i + a i * zero.cylindricalEndLift z) x
        (a i * (deriv zero.cylindricalEndLift z * v)) = v.im * H i z.im x := by
  rw [puncturedSpherePerturbation_cylindricalEndLift_of_pos hsep hout hH ha (by linarith),
    smoothTransition.one_of_one_le (by linarith), one_mul]

/-- **The datum on the output end.** If the discs `‖w - c i‖ < ‖a i‖ / 2` lie in the disc
`‖w‖ ≤ 2 exp (2π)`, then on the part `s ≤ -1` of the output end the pullback of the datum along
the end lift `φ_∞` is the continuation datum `β(-s - 1) Hout(t) dt`. -/
theorem puncturedSpherePerturbation_cylindricalEndLift_inf_of_le
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) (hH : Periodic Hout 1) {z : ℂ}
    (hz : z.re ≤ -1) (x : M) (v : ℂ) :
    puncturedSpherePerturbation c a H Hout (inf.cylindricalEndLift z) x
        (deriv inf.cylindricalEndLift z * v) =
      v.im * (smoothTransition (-z.re - 1) * Hout z.im x) := by
  have hnorm : 2 * Real.exp (2 * π) ≤ ‖inf.cylindricalEndLift z‖ := by
    have h := norm_cylindricalEndLift_sub_endCenter inf z
    rw [endCenter_inf, sub_zero, endScale_inf, Complex.norm_ofNat] at h
    rw [h]
    gcongr
    nlinarith [Real.pi_pos]
  rw [puncturedSpherePerturbation_eq_negativePlanePerturbation fun i => ?_,
    negativePlanePerturbation_cylindricalEndLift_apply hH]
  have h := norm_sub_norm_le (inf.cylindricalEndLift z) (c i)
  nlinarith [hout i, norm_nonneg (a i), exp_neg_two_pi_lt_one]

/-- **The datum is `Hout(t) dt` far out on the output end.** Under the hypothesis of
`puncturedSpherePerturbation_cylindricalEndLift_inf_of_le`, on the part `s ≤ -2` of the output end
the pullback of the datum along `φ_∞` sends a tangent vector `v` of the cylinder to
`Im v · Hout(Im z)`. -/
theorem puncturedSpherePerturbation_cylindricalEndLift_inf
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) (hH : Periodic Hout 1) {z : ℂ}
    (hz : z.re ≤ -2) (x : M) (v : ℂ) :
    puncturedSpherePerturbation c a H Hout (inf.cylindricalEndLift z) x
        (deriv inf.cylindricalEndLift z * v) = v.im * Hout z.im x := by
  rw [puncturedSpherePerturbation_cylindricalEndLift_inf_of_le hout hH (by linarith),
    smoothTransition.one_of_one_le (by linarith), one_mul]

end Sphere

section Smooth

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- **The input end datum is smooth in its center and scale.** For a period-one Hamiltonian of
class `C^n` on `ℝ × M`, the input end datum is `C^n` jointly in the center `c`, the scale `a`, the
domain point `w` and the target point, at every point with `a ≠ 0` and `w ≠ c`. -/
theorem contMDiffAt_inputEndPerturbation {n : ℕ∞} {H : ℝ → M → ℝ} (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry H)) {c a w : ℂ} (ha : a ≠ 0)
    (hw : w ≠ c) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℂ × ℂ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : (ℂ × ℂ) × (ℂ × M) => inputEndPerturbation p.1.1 p.1.2 H p.2.1 p.2.2)
      ((c, a), (w, x)) := by
  have hcoord : ContDiffAt ℝ n (fun q : (ℂ × ℂ) × ℂ => (q.2 - q.1.1) / q.1.2) ((c, a), w) := by
    have h : ContDiffAt ℂ n (fun q : (ℂ × ℂ) × ℂ => (q.2 - q.1.1) / q.1.2) ((c, a), w) := by
      refine ContDiffAt.div (x := ((c, a), w)) (f := fun q : (ℂ × ℂ) × ℂ => q.2 - q.1.1)
        (g := fun q : (ℂ × ℂ) × ℂ => q.1.2) ?_ ?_ ha <;> fun_prop
    exact h.restrict_scalars ℝ
  have hcoordM : ContMDiffAt (𝓘(ℝ, ℂ × ℂ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ) n
      (fun p : (ℂ × ℂ) × (ℂ × M) => (p.2.1 - p.1.1) / p.1.2) ((c, a), (w, x)) :=
    hcoord.contMDiffAt.comp (f := fun p : (ℂ × ℂ) × (ℂ × M) => (p.1, p.2.1)) ((c, a), (w, x))
      (contMDiffAt_fst.prodMk_space (contMDiffAt_fst.comp _ contMDiffAt_snd))
  have hinv : ContDiffAt ℝ n (fun q : ℂ × ℂ => ContinuousLinearMap.mul ℝ ℂ q.2⁻¹) (c, a) :=
    (ContinuousLinearMap.mul ℝ ℂ).contDiff.contDiffAt.comp (c, a)
      ((contDiffAt_inv ℝ ha).comp (c, a) contDiffAt_snd)
  have hmul : ContMDiffAt (𝓘(ℝ, ℂ × ℂ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℂ) n
      (fun p : (ℂ × ℂ) × (ℂ × M) => ContinuousLinearMap.mul ℝ ℂ p.1.2⁻¹) ((c, a), (w, x)) :=
    ContMDiffAt.comp (g := fun q : ℂ × ℂ => ContinuousLinearMap.mul ℝ ℂ q.2⁻¹) (f := Prod.fst)
      ((c, a), (w, x)) hinv.contMDiffAt contMDiffAt_fst
  exact ((contMDiffAt_positivePlanePerturbation hH hHs
    (div_ne_zero (sub_ne_zero.2 hw) ha) x).comp ((c, a), (w, x))
    (hcoordM.prodMk (contMDiffAt_snd.comp _ contMDiffAt_snd))).clm_comp hmul

/-- Off its center, the components of the input end datum of a `C¹` Hamiltonian on a manifold are
differentiable in the domain point. -/
theorem differentiableAt_inputEndPerturbation_domain {H : ℝ → M → ℝ} (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {c a : ℂ} (ha : a ≠ 0) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ c) (x : M) (v : ℂ) :
    DifferentiableAt ℝ
      (fun z' ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z') x v) z := by
  have hK : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1 (fun w ↦ inputEndPerturbation c a H w x)
      (Complex.equivRealProdCLM.symm z) :=
    (contMDiffAt_inputEndPerturbation (n := 1) hH hHs ha hz x).comp
      (f := fun w : ℂ ↦ ((c, a), (w, x))) _
      (contMDiffAt_const.prodMk (contMDiffAt_id.prodMk contMDiffAt_const))
  exact ((hK.contDiffAt.differentiableAt one_ne_zero).comp z
    Complex.equivRealProdCLM.symm.differentiableAt).clm_apply (differentiableAt_const v)

/-- The components of the input end datum of a `C¹` Hamiltonian on a manifold are differentiable
in the target point. -/
theorem mdifferentiableAt_inputEndPerturbation_target {H : ℝ → M → ℝ}
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) (c a w : ℂ) (x : M) (v : ℂ) :
    MDifferentiableAt I 𝓘(ℝ) (fun y ↦ inputEndPerturbation c a H w y v) x := by
  have hHt : MDifferentiableAt I 𝓘(ℝ) (H (zero.endCoord ((w - c) / a)).im) x :=
    (hHs.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt one_ne_zero
  simp only [inputEndPerturbation_apply, positivePlanePerturbation_def, smul_apply, smul_eq_mul]
  exact (((differentiableAt_id (x := H (zero.endCoord ((w - c) / a)).im x)).const_mul
    _).mul_const _).mdifferentiableAt.comp x hHt

variable {ι : Type*} [Fintype ι] {H : ι → ℝ → M → ℝ} {Hout : ℝ → M → ℝ}

/-- **The datum is smooth in the configuration.** For period-one Hamiltonians of class `C^n` on
`ℝ × M`, the perturbation datum is `C^n` jointly in the centers, the scales, the domain point and
the target point, at every configuration with nonzero scales and every domain point other than
the centers. Composing with a smooth path of configurations gives a smooth family of data. -/
theorem contMDiffAt_puncturedSpherePerturbation {n : ℕ∞} (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry Hout)) {c a : ι → ℂ}
    (ha : ∀ i, a i ≠ 0) {w : ℂ} (hw : ∀ i, w ≠ c i) (x : M) :
    ContMDiffAt (𝓘(ℝ, (ι → ℂ) × (ι → ℂ)).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ((ι → ℂ) × (ι → ℂ)) × (ℂ × M) =>
        puncturedSpherePerturbation p.1.1 p.1.2 H Hout p.2.1 p.2.2) ((c, a), (w, x)) := by
  simp only [puncturedSpherePerturbation_def]
  refine (contMDiffAt_finsetSum fun i _ => ?_).add
    ((contMDiff_negativePlanePerturbation hHout hHouts).contMDiffAt.comp _ contMDiffAt_snd)
  -- Evaluating the configuration at `i` is a continuous linear map.
  have hev : ContMDiffAt (𝓘(ℝ, (ι → ℂ) × (ι → ℂ)).prod (𝓘(ℝ, ℂ).prod I))
      (𝓘(ℝ, ℂ × ℂ).prod (𝓘(ℝ, ℂ).prod I)) n
      (fun p : ((ι → ℂ) × (ι → ℂ)) × (ℂ × M) => ((p.1.1 i, p.1.2 i), p.2)) ((c, a), (w, x)) :=
    have hL : ContDiff ℝ n (fun q : (ι → ℂ) × (ι → ℂ) => (q.1 i, q.2 i)) := by fun_prop
    (hL.contMDiff.contMDiffAt.comp _ contMDiffAt_fst).prodMk contMDiffAt_snd
  exact (contMDiffAt_inputEndPerturbation (hH i) (hHs i) (ha i) (hw i) x).comp ((c, a), (w, x))
    hev

/-- **The components of the datum are smooth off the centers.** In the real coordinates
`z = (s, t)` of the domain, for period-one Hamiltonians of class `C^n` and nonzero scales, the
component `(z, x) ↦ K(z)(x)(v)` of the datum is `C^n` jointly in the domain point and the target
point at every domain point other than the centers. -/
theorem contMDiffOn_uncurry_puncturedSpherePerturbation_apply {n : ℕ∞}
    (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry Hout)) {c a : ι → ℂ}
    (ha : ∀ i, a i ≠ 0) (v : ℂ) :
    ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) n
      (uncurry fun z x ↦
        puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x v)
      ({z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} ×ˢ univ) := by
  rintro ⟨z, x⟩ ⟨hz, -⟩
  have h := contMDiffAt_puncturedSpherePerturbation hH hHs hHout hHouts ha
    (w := Complex.equivRealProdCLM.symm z) hz x
  have hφ : ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ, (ι → ℂ) × (ι → ℂ)).prod (𝓘(ℝ, ℂ).prod I)) n
      (fun p : (ℝ × ℝ) × M ↦ ((c, a), (Complex.equivRealProdCLM.symm p.1, p.2))) (z, x) :=
    contMDiffAt_const.prodMk
      ((Complex.equivRealProdCLM.symm.contDiff.contMDiff.contMDiffAt.comp _
        contMDiffAt_fst).prodMk contMDiffAt_snd)
  exact ((h.comp (z, x) hφ).clm_apply contMDiffAt_const).contMDiffWithinAt

end Smooth

section SmoothProd

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- At points other than its center, the input end datum is `C^n` jointly in the domain point and
the target point, for a period-one `C^n` Hamiltonian. -/
theorem contDiffAt_inputEndPerturbation_prod {n : ℕ∞} {H : ℝ → V → ℝ} (hH : Periodic H 1)
    (hHs : ContDiff ℝ n (uncurry H)) {c a w : ℂ} (ha : a ≠ 0) (hw : w ≠ c) (x : V) :
    ContDiffAt ℝ n (fun p : ℂ × V => inputEndPerturbation c a H p.1 p.2) (w, x) := by
  have h := (contMDiffAt_inputEndPerturbation hH
    (contMDiff_prod_modelWithCornersSelf_iff.2 hHs.contMDiff) ha hw x).comp (w, x)
    (f := fun p : ℂ × V => ((c, a), p)) (contMDiffAt_const.prodMk contMDiffAt_id)
  exact (contMDiffAt_prod_modelWithCornersSelf_iff.1 h).contDiffAt

/-- At points other than the centers, the perturbation datum is `C^n` jointly in the domain point
and the target point, for period-one `C^n` Hamiltonians and nonzero scales. -/
theorem contDiffAt_puncturedSpherePerturbation_prod {ι : Type*} [Fintype ι] {n : ℕ∞}
    {H : ι → ℝ → V → ℝ} {Hout : ℝ → V → ℝ} (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContDiff ℝ n (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContDiff ℝ n (uncurry Hout)) {c a : ι → ℂ} (ha : ∀ i, a i ≠ 0) {w : ℂ}
    (hw : ∀ i, w ≠ c i) (x : V) :
    ContDiffAt ℝ n (fun p : ℂ × V => puncturedSpherePerturbation c a H Hout p.1 p.2) (w, x) := by
  have h := (contMDiffAt_puncturedSpherePerturbation hH
    (fun i => contMDiff_prod_modelWithCornersSelf_iff.2 (hHs i).contMDiff) hHout
    (contMDiff_prod_modelWithCornersSelf_iff.2 hHouts.contMDiff) ha hw x).comp (w, x)
    (f := fun p : ℂ × V => ((c, a), p)) (contMDiffAt_const.prodMk contMDiffAt_id)
  exact (contMDiffAt_prod_modelWithCornersSelf_iff.1 h).contDiffAt

end SmoothProd

end TauCeti.Floer

namespace TauCeti.SmoothTwoForm

open Floer MeasureTheory
open TauCeti.Complex (realChart realChart_apply contDiff_realChart realChart_affine_injective)

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

variable {H : ℝ → M → ℝ} {c a : ℂ}

variable [IsManifold I ⊤ M]

/-- On the image under the affine chart of the plane without its origin, the integrated curvature
of the input end datum is that of the positive plane datum of `H`, along the reparametrized map,
for a manifold target. -/
private theorem setLIntegral_image_enorm_hamiltonianCurvature_inputEndPerturbation
    (ω : SmoothTwoForm I M) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) (ha : a ≠ 0) (u : ℝ × ℝ → M) :
    ∫⁻ z in realChart (c + a * ·) '' {z | Complex.equivRealProdCLM.symm z ≠ 0},
      ‖ω.hamiltonianCurvature
        (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ =
      ∫⁻ w in {z | Complex.equivRealProdCLM.symm z ≠ 0}, ‖ω.hamiltonianCurvature
        (fun z x ↦ positivePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positivePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) w
        ((u ∘ realChart (c + a * ·)) w)‖ₑ := by
  set S := {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0}
  have hSm : MeasurableSet S :=
    (measurableSet_singleton 0).compl.preimage Complex.equivRealProdCLM.symm.continuous.measurable
  -- The affine chart maps `S` off the center, where the datum is differentiable.
  have hc {w : ℝ × ℝ} (hw : w ∈ S) :
      Complex.equivRealProdCLM.symm (realChart (c + a * ·) w) ≠ c := by
    rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply]
    exact fun h => hw (by simpa [ha] using h)
  rw [ω.lintegral_enorm_hamiltonianCurvature_image hSm
    (realChart_affine_injective ha).injOn
    (fun w _ ↦ (contDiff_realChart (by fun_prop)).contDiffAt)
    (fun w hw ↦ differentiableAt_inputEndPerturbation_domain hH hHs ha (hc hw) _ 1)
    (fun w hw ↦ differentiableAt_inputEndPerturbation_domain hH hHs ha (hc hw) _ Complex.I)
    (fun w _ ↦ mdifferentiableAt_inputEndPerturbation_target hHs _ _ _ _ 1)
    (fun w _ ↦ mdifferentiableAt_inputEndPerturbation_target hHs _ _ _ _ Complex.I),
    perturbationPullback_realChart_inputEndPerturbation ha,
    perturbationPullback_realChart_inputEndPerturbation ha,
    equivRealProdCLM_symm_stdComplexLineReal, equivRealProdCLM_symm_stdComplexLineImag]
  rfl

/-- **The integrated curvature of an input end datum, for a manifold target.** Let `K` be the
input end datum with center `c` and nonzero scale `a` of a period-one `C¹` Hamiltonian `H` on a
manifold `M` with a two-form `ω`, with `|H| ≤ B`, and write its components in the global
coordinate `z = s + i t` of `ℂ` as `K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)`. Then for every map
`u` into `M`, the integral of `|R_K(z, u(z))|` over the plane is at most `B`, whatever the center
and the scale. -/
theorem lintegral_enorm_hamiltonianCurvature_inputEndPerturbation_le (ω : SmoothTwoForm I M)
    (hH : Periodic H 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) (ha : a ≠ 0)
    {B : ℝ} (hB : ∀ t x, |H t x| ≤ B) (u : ℝ × ℝ → M) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ENNReal.ofReal B := by
  -- The plane is, up to the center `c`, the image under the affine chart of `ℂ ∖ {0}`.
  have hcover : univ ⊆ realChart (c + a * ·) '' {z | Complex.equivRealProdCLM.symm z ≠ 0} ∪
      {Complex.equivRealProdCLM c} := by
    intro z _
    by_cases h : Complex.equivRealProdCLM.symm z = c
    · exact Or.inr (by simp [← h])
    · refine Or.inl ⟨Complex.equivRealProdCLM ((Complex.equivRealProdCLM.symm z - c) / a), ?_, ?_⟩
      · rw [Set.mem_ofPred_eq, ContinuousLinearEquiv.symm_apply_apply]
        exact div_ne_zero (sub_ne_zero.2 h) ha
      · rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply, mul_div_cancel₀ _ ha,
          add_sub_cancel, ContinuousLinearEquiv.apply_symm_apply]
  have hN : volume ({Complex.equivRealProdCLM c} : Set (ℝ × ℝ)) = 0 := by
    rw [Measure.volume_eq_prod]
    exact (Set.toFinite _).measure_zero _
  calc _ = ∫⁻ z in univ, ‖ω.hamiltonianCurvature
        (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ := (setLIntegral_univ _).symm
    _ ≤ _ := lintegral_mono_set hcover
    _ ≤ _ := lintegral_union_le _ _ _
    _ = _ := by rw [setLIntegral_measure_zero _ _ hN, add_zero,
        setLIntegral_image_enorm_hamiltonianCurvature_inputEndPerturbation ω hH hHs ha u]
    _ ≤ _ := setLIntegral_le_lintegral _ _
    _ ≤ _ := ω.lintegral_enorm_hamiltonianCurvature_positivePlanePerturbation_le hH hHs hB
        (u ∘ realChart (c + a * ·))

variable {ι : Type*} [Fintype ι] {c a : ι → ℂ} {H : ι → ℝ → M → ℝ} {Hout : ℝ → M → ℝ}

/-- **The integrated curvature on a sphere with moving input ends is bounded uniformly in the
configuration, for a manifold target.** Let the input ends have period-one `C¹` Hamiltonians `H i`
on a manifold `M` with a two-form `ω`, with `|H i| ≤ B i`, nonzero scales `a i` and centers `c i`,
such that the supports `‖w - c i‖ < ‖a i‖ exp (-2π) / 2` of the input end data are pairwise
disjoint and lie in the disc `‖w‖ ≤ 2 exp (2π)`, and let the output end have a period-one `C¹`
Hamiltonian `Hout` with `|Hout| ≤ Bout`. Write the components of the datum `K` in the global
coordinate `z = s + i t` of `ℂ` as `K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)`. Then for every map
`u` into `M`, the integral of `|R_K(z, u(z))|` over the plane is at most `∑ i, B i + Bout`. -/
theorem lintegral_enorm_hamiltonianCurvature_puncturedSpherePerturbation_le
    (ω : SmoothTwoForm I M) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j =>
      ‖a i‖ * Real.exp (-(2 * π)) / 2 + ‖a j‖ * Real.exp (-(2 * π)) / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ 2 * Real.exp (2 * π)) {B : ι → ℝ}
    {Bout : ℝ} (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout)
    (u : ℝ × ℝ → M) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z)‖ₑ ≤ ∑ i, ENNReal.ofReal (B i) + ENNReal.ofReal Bout := by
  classical
  -- The plane is covered, up to the boundary circles `N` of the supports of the input end data,
  -- by these supports `D i`, on each of which the datum is the datum of that end, and the open
  -- set `O` off them, on which it is the output datum.
  set r : ι → ℝ := fun i ↦ ‖a i‖ * Real.exp (-(2 * π)) / 2
  set f : ℝ × ℝ → ENNReal := fun z ↦ ‖ω.hamiltonianCurvature
    (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
      Complex.I) z (u z)‖ₑ
  set D : ι → Set (ℝ × ℝ) := fun i ↦ {z | ‖Complex.equivRealProdCLM.symm z - c i‖ < r i}
  set O : Set (ℝ × ℝ) := {z | ∀ i, r i < ‖Complex.equivRealProdCLM.symm z - c i‖}
  set N : Set (ℝ × ℝ) :=
    ⋃ i, Complex.equivRealProdCLM.symm ⁻¹' Metric.sphere (c i) (r i)
  have hDo (i : ι) : IsOpen (D i) := isOpen_lt (by fun_prop) continuous_const
  have hOo : IsOpen O := by
    simp only [O, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (by fun_prop)
  have hcover : univ ⊆ ((⋃ i, D i) ∪ O) ∪ N := by
    intro z _
    by_cases h : ∃ i, z ∈ D i
    · exact Or.inl (Or.inl (mem_iUnion.2 h))
    by_cases h' : ∃ i, ‖Complex.equivRealProdCLM.symm z - c i‖ = r i
    · obtain ⟨i, hi⟩ := h'
      exact Or.inr (mem_iUnion.2 ⟨i, by simpa [dist_eq_norm] using hi⟩)
    · exact Or.inl (Or.inr fun i ↦ lt_of_le_of_ne (not_lt.1 (not_exists.1 h i))
        fun hi ↦ h' ⟨i, hi.symm⟩)
  have hN : volume N = 0 := by
    refine measure_iUnion_null fun i ↦ ?_
    have hpre := Complex.volume_preserving_equiv_real_prod.symm.measure_preimage
      (s := Metric.sphere (c i) (r i)) Metric.isClosed_sphere.measurableSet.nullMeasurableSet
    exact hpre.trans (Measure.addHaar_sphere volume (c i) (r i))
  -- Perturbation data that agree on an open set have the same integrated curvature over it.
  have hcongr {U : Set (ℝ × ℝ)} (hU : IsOpen U) {K : ℂ → M → ℂ →L[ℝ] ℝ}
      (hK : ∀ z ∈ U, ∀ x, puncturedSpherePerturbation c a H Hout
        (Complex.equivRealProdCLM.symm z) x = K (Complex.equivRealProdCLM.symm z) x) :
      ∫⁻ z in U, f z = ∫⁻ z in U, ‖ω.hamiltonianCurvature
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)‖ₑ :=
    setLIntegral_congr_fun hU.measurableSet fun z hz ↦ by
      have hev := Filter.eventually_of_mem (hU.mem_nhds hz) hK
      refine congrArg (‖·‖ₑ)
        (congrFun (ω.hamiltonianCurvature_congr_of_eventuallyEq ?_ ?_) (u z)) <;>
      exact hev.mono fun z' hz' ↦ funext fun x ↦ by simp only [hz' x]
  have hD (i : ι) : ∫⁻ z in D i, f z ≤ ENNReal.ofReal (B i) :=
    (hcongr (hDo i) fun z hz x ↦
      puncturedSpherePerturbation_eq_inputEndPerturbation_of_norm_sub_lt
        (r := r) (fun _ ↦ le_rfl) hsep hout hz x).trans_le
      ((setLIntegral_le_lintegral _ _).trans
        (lintegral_enorm_hamiltonianCurvature_inputEndPerturbation_le ω (hH i) (hHs i) (ha i)
          (hB i) u))
  have hO : ∫⁻ z in O, f z ≤ ENNReal.ofReal Bout :=
    (hcongr hOo fun z hz x ↦
      puncturedSpherePerturbation_eq_negativePlanePerturbation (fun i ↦ (hz i).le) x).trans_le
      ((setLIntegral_le_lintegral _ _).trans
        (lintegral_enorm_hamiltonianCurvature_negativePlanePerturbation_le ω hHout hHouts hBout
          u))
  calc ∫⁻ z, f z = ∫⁻ z in univ, f z := (setLIntegral_univ _).symm
    _ ≤ ∫⁻ z in ((⋃ i, D i) ∪ O) ∪ N, f z := lintegral_mono_set hcover
    _ ≤ (∫⁻ z in (⋃ i, D i) ∪ O, f z) + ∫⁻ z in N, f z := lintegral_union_le _ _ _
    _ = ∫⁻ z in (⋃ i, D i) ∪ O, f z := by rw [setLIntegral_measure_zero _ _ hN, add_zero]
    _ ≤ (∫⁻ z in ⋃ i, D i, f z) + ∫⁻ z in O, f z := lintegral_union_le _ _ _
    _ ≤ (∑' i, ∫⁻ z in D i, f z) + ∫⁻ z in O, f z := by
        gcongr
        exact lintegral_iUnion_le _ _
    _ = (∑ i, ∫⁻ z in D i, f z) + ∫⁻ z in O, f z := by rw [tsum_fintype]
    _ ≤ _ := add_le_add (Finset.sum_le_sum fun i _ ↦ hD i) hO

end TauCeti.SmoothTwoForm

namespace TauCeti.SymplecticForm

open Floer MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {H : ℝ → V → ℝ} {c a : ℂ}

variable [FiniteDimensional ℝ V]

/-- **The integrated curvature of an input end datum.** Let `K` be the input end datum with center
`c` and nonzero scale `a` of a period-one `C¹` Hamiltonian `H` with `|H| ≤ B`, with components
`K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`. Then for
every map `u` into the target, the integral of `|R_K(z, u(z))|` over the plane is at most `B`,
whatever the center and the scale. -/
theorem lintegral_enorm_hamiltonianCurvature_inputEndPerturbation_le (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) (ha : a ≠ 0) {B : ℝ}
    (hB : ∀ t x, |H t x| ≤ B) (u : ℝ × ℝ → V) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ENNReal.ofReal B := by
  simpa using ω.constSmooth.lintegral_enorm_hamiltonianCurvature_inputEndPerturbation_le hH
    (contMDiff_prod_modelWithCornersSelf_iff.2 hHs.contMDiff) ha hB u

variable {ι : Type*} [Fintype ι] {c a : ι → ℂ} {H : ι → ℝ → V → ℝ} {Hout : ℝ → V → ℝ}

/-- **The integrated curvature on a sphere with moving input ends is bounded uniformly in the
configuration.** Let the input ends have period-one `C¹` Hamiltonians `H i` with `|H i| ≤ B i`,
nonzero scales `a i` and centers `c i`, such that the supports `‖w - c i‖ < ‖a i‖ exp (-2π) / 2`
of the input end data are pairwise disjoint and lie in the disc `‖w‖ ≤ 2 exp (2π)`, and let the
output end have a period-one `C¹` Hamiltonian `Hout` with `|Hout| ≤ Bout`. Write the components of
the datum `K` in the global coordinate `z = s + i t` of `ℂ` as `K_s(z) = K(z)(1)` and
`K_t(z) = K(z)(i)`. Then for every map `u` into the target, the integral of `|R_K(z, u(z))|` over
the plane is at most `∑ i, B i + Bout`. -/
theorem lintegral_enorm_hamiltonianCurvature_puncturedSpherePerturbation_le
    (ω : SymplecticForm V) (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 1 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j =>
      ‖a i‖ * Real.exp (-(2 * π)) / 2 + ‖a j‖ * Real.exp (-(2 * π)) / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ 2 * Real.exp (2 * π)) {B : ι → ℝ}
    {Bout : ℝ} (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout)
    (u : ℝ × ℝ → V) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z)‖ₑ ≤ ∑ i, ENNReal.ofReal (B i) + ENNReal.ofReal Bout := by
  simpa using ω.constSmooth.lintegral_enorm_hamiltonianCurvature_puncturedSpherePerturbation_le
    hH (fun i ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHs i).contMDiff) hHout
    (contMDiff_prod_modelWithCornersSelf_iff.2 hHouts.contMDiff) ha hsep hout hB hBout u

end TauCeti.SymplecticForm
