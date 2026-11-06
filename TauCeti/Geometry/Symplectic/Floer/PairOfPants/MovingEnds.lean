/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Capping
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
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
along the affine map `w ↦ c + a w` of the pair-of-pants datum whose only nonzero Hamiltonian is
`H` at the input `0`. In the coordinates `(s, t)` of the moved end it is `β(s - 1) H(t) dt`, and it
vanishes off the disc `‖w - c‖ < ‖a‖ exp (-2π) / 2`. For finitely many input ends with centers
`c i`, scales `a i` and period-one Hamiltonians `H i`, and an output Hamiltonian `Hout` at `∞`,
`TauCeti.Floer.puncturedSpherePerturbation c a H Hout` is the sum of the input data and the
negative plane datum `TauCeti.Floer.negativePlanePerturbation Hout` of the output end.

Suppose that the discs `‖w - c i‖ < ‖a i‖ / 2` are pairwise disjoint and lie in the disc
`‖w‖ ≤ 2 exp (2π)` on which the output datum vanishes. Then:

* near each input end the datum is that end's datum alone, and far out on the end it is
  `H i(t) dt` (`TauCeti.Floer.puncturedSpherePerturbation_cylindricalEndLift`); far out on the
  output end it is `Hout(t) dt`
  (`TauCeti.Floer.puncturedSpherePerturbation_cylindricalEndLift_inf`);
* it is `C^n` jointly in the centers, the scales, the domain point and the target point, away
  from the punctures (`TauCeti.Floer.contMDiffAt_puncturedSpherePerturbation`), so it is a smooth
  family over any smooth path of configurations;
* for a symplectic vector space target, its integrated curvature along any map is at most
  `∑ i, sup |H i| + sup |Hout|`, whatever the configuration
  (`TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_puncturedSpherePerturbation_le`).
  This bound only needs the smaller supports `‖w - c i‖ < ‖a i‖ exp (-2π) / 2` of the input end
  data to be pairwise disjoint and to lie in the disc `‖w‖ ≤ 2 exp (2π)`.

The pair-of-pants datum itself is the case of the inputs `0` and `1` with scales `1` and `-1`
(`TauCeti.Floer.puncturedSpherePerturbation_eq_pairOfPantsPerturbation`).

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
`v ↦ K((w - c) / a)(v / a)` along the affine map `w ↦ c + a w` of the pair-of-pants datum `K`
whose only nonzero Hamiltonian is `H`, at the input `0`. Its end lift is `z ↦ c + a φ₀(z)`, where
`φ₀` is the end lift of the input `0`, and in the coordinates `(s, t)` of that end lift it is
`β(s - 1) H(t) dt` (`inputEndPerturbation_cylindricalEndLift_of_pos`). -/
def inputEndPerturbation (c a : ℂ) (H : ℝ → M → ℝ) (w : ℂ) (x : M) : ℂ →L[ℝ] ℝ :=
  (pairOfPantsPerturbation (Pi.single zero H) ((w - c) / a) x).comp
    (ContinuousLinearMap.mul ℝ ℂ a⁻¹)

theorem inputEndPerturbation_apply (c a : ℂ) (H : ℝ → M → ℝ) (w : ℂ) (x : M) (v : ℂ) :
    inputEndPerturbation c a H w x v =
      pairOfPantsPerturbation (Pi.single zero H) ((w - c) / a) x (a⁻¹ * v) :=
  (rfl)

/-- The pullback of the input end datum along the affine map `w ↦ c + a w` is the pair-of-pants
datum of `H` at the input `0`. -/
theorem inputEndPerturbation_add_mul (ha : a ≠ 0) (w : ℂ) (x : M) (v : ℂ) :
    inputEndPerturbation c a H (c + a * w) x (a * v) =
      pairOfPantsPerturbation (Pi.single zero H) w x v := by
  rw [inputEndPerturbation_apply, add_sub_cancel_left, mul_div_cancel_left₀ _ ha,
    inv_mul_cancel_left₀ ha]

/-- **The support of an input end datum.** It vanishes off the disc
`‖w - c‖ < ‖a‖ exp (-2π) / 2`. -/
theorem inputEndPerturbation_eq_zero_of_le_norm_sub {w : ℂ}
    (hw : ‖a‖ * Real.exp (-(2 * π)) / 2 ≤ ‖w - c‖) (x : M) :
    inputEndPerturbation c a H w x = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · ext v
    simp [inputEndPerturbation_apply]
  · rw [inputEndPerturbation, pairOfPantsPerturbation_single_zero_eq_zero_of_le_norm ?_ x,
      ContinuousLinearMap.zero_comp]
    rw [norm_div, le_div_iff₀ (norm_pos_iff.2 ha)]
    linarith

/-- **The input end datum on its end.** On the part `s > 0` of the moved end, the pullback of the
datum along its end lift `z ↦ c + a φ₀(z)` is the continuation datum `β(s - 1) H(t) dt`. -/
theorem inputEndPerturbation_cylindricalEndLift_of_pos (hH : Periodic H 1) (ha : a ≠ 0) {z : ℂ}
    (hz : 0 < z.re) (x : M) (v : ℂ) :
    inputEndPerturbation c a H (c + a * zero.cylindricalEndLift z) x
        (a * (deriv zero.cylindricalEndLift z * v)) =
      v.im * (smoothTransition (z.re - 1) * H z.im x) := by
  rw [inputEndPerturbation_add_mul ha]
  simpa using pairOfPantsPerturbation_cylindricalEndLift_of_pos (H := Pi.single zero H)
    (q := zero) (by simpa using hH) (z := z) (by simpa using hz) x v

end InputEnd

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
      pairOfPantsPerturbation_single]
  -- The input end at `1` is the image of the input end at `0` under `w ↦ 1 - w`.
  have hc : zero.endCoord ((w - 1) / -1) = one.endCoord w := by
    rw [endCoord_def, endCoord_def, endCenter_zero, endCenter_one, endScale_zero, endScale_one]
    congr 3
    ring
  have h₁ : inputEndPerturbation 1 (-1) (H one) w x =
      (smoothTransition (one.endSign * (one.endCoord w).re - 1) *
        H one (one.endCoord w).im x) • one.endAngularForm w := by
    ext v
    rw [inputEndPerturbation_apply, pairOfPantsPerturbation_single, hc]
    simp only [smul_apply, endAngularForm_apply, endSign_zero, endSign_one, endCenter_zero,
      endCenter_one, div_neg, div_one, sub_zero, mul_neg, neg_neg, inv_neg]
    congr 2
    ring
  rw [puncturedSpherePerturbation_def, Fin.sum_univ_two, pairOfPantsPerturbation_def,
    Puncture.sum_univ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [h₀, h₁, negativePlanePerturbation_def, endSign_inf, neg_one_mul]

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
    inputEndPerturbation_cylindricalEndLift_of_pos hH ha hz]

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
    negativePlanePerturbation_cylindricalEndLift_of_neg hH (by linarith)]
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
  rcases lt_or_ge (Real.exp (-(2 * π)) / 2) ‖(w - c) / a‖ with hlt | hle
  · -- Off the support of the datum it vanishes on a neighborhood.
    refine (contMDiffAt_const (c := (0 : ℂ →L[ℝ] ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hcoordM.continuousAt.norm.eventually (lt_mem_nhds hlt)] with p hp
    rw [inputEndPerturbation, pairOfPantsPerturbation_single_zero_eq_zero_of_le_norm hp.le,
      ContinuousLinearMap.zero_comp]
  · -- On its support the rescaled point lies in the pair of pants.
    have hw₀ : (w - c) / a ≠ 0 := div_ne_zero (sub_ne_zero.2 hw) ha
    have hw₁ : (w - c) / a ≠ 1 := by
      intro h
      rw [h, norm_one] at hle
      linarith [exp_neg_two_pi_lt_one]
    have hinv : ContDiffAt ℝ n (fun q : ℂ × ℂ => ContinuousLinearMap.mul ℝ ℂ q.2⁻¹) (c, a) :=
      (ContinuousLinearMap.mul ℝ ℂ).contDiff.contDiffAt.comp (c, a)
        ((contDiffAt_inv ℝ ha).comp (c, a) contDiffAt_snd)
    have hmul : ContMDiffAt (𝓘(ℝ, ℂ × ℂ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℂ) n
        (fun p : (ℂ × ℂ) × (ℂ × M) => ContinuousLinearMap.mul ℝ ℂ p.1.2⁻¹) ((c, a), (w, x)) :=
      ContMDiffAt.comp (g := fun q : ℂ × ℂ => ContinuousLinearMap.mul ℝ ℂ q.2⁻¹) (f := Prod.fst)
        ((c, a), (w, x)) hinv.contMDiffAt contMDiffAt_fst
    -- The family that is `H` at `0` and zero elsewhere is periodic and `C^n` at every end.
    have hP : ∀ r, Periodic ((Pi.single zero H : Puncture → ℝ → M → ℝ) r) 1 :=
      forall_single zero (P := fun f => Periodic f 1) (fun _ => rfl) hH
    have hS : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n
        (uncurry ((Pi.single zero H : Puncture → ℝ → M → ℝ) r)) :=
      forall_single zero (P := fun f => ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry f))
        contMDiff_const hHs
    exact ((contMDiffAt_pairOfPantsPerturbation hP hS ⟨(w - c) / a, hw₀, hw₁⟩ x).comp
      ((c, a), (w, x))
      (hcoordM.prodMk (contMDiffAt_snd.comp _ contMDiffAt_snd))).clm_comp hmul

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

end Smooth

end TauCeti.Floer

namespace TauCeti.SymplecticForm

open Floer MeasureTheory
open TauCeti.Complex (realChart realChart_apply contDiff_realChart realChart_injective)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {H : ℝ → V → ℝ} {c a : ℂ}

/-- At points other than its center, the input end datum of a `C¹` Hamiltonian is differentiable
jointly in the domain and target points. -/
private theorem differentiableAt_inputEndPerturbation (hH : Periodic H 1)
    (hHs : ContDiff ℝ 1 (uncurry H)) (ha : a ≠ 0) {w : ℂ} (hw : w ≠ c) (x : V) :
    DifferentiableAt ℝ (fun p : ℂ × V ↦ inputEndPerturbation c a H p.1 p.2) (w, x) := by
  have hmfd : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ, ℝ) 1 (uncurry H) :=
    contMDiff_prod_modelWithCornersSelf_iff.2 hHs.contMDiff
  have h := (contMDiffAt_inputEndPerturbation (n := 1) hH hmfd ha hw x).comp (w, x)
    (f := fun p : ℂ × V => ((c, a), p)) (contMDiffAt_const.prodMk contMDiffAt_id)
  have h' : ContMDiffAt 𝓘(ℝ, ℂ × V) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × V ↦ inputEndPerturbation c a H p.1 p.2) (w, x) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact h
  exact h'.contDiffAt.differentiableAt one_ne_zero

variable [FiniteDimensional ℝ V]

/-- On the image under the affine chart of the plane without its origin, the integrated curvature
of the input end datum is that of the pair-of-pants datum of `H` at the input `0`, along the
reparametrized map. -/
private theorem setLIntegral_image_enorm_hamiltonianCurvature_inputEndPerturbation
    (ω : SymplecticForm V) (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) (ha : a ≠ 0)
    (u : ℝ × ℝ → V) :
    ∫⁻ z in realChart (c + a * ·) '' {z | Complex.equivRealProdCLM.symm z ≠ 0},
      ‖ω.hamiltonianCurvature
        (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ =
      ∫⁻ w in {z | Complex.equivRealProdCLM.symm z ≠ 0}, ‖ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (Pi.single zero H) (Complex.equivRealProdCLM.symm z)
          x 1)
        (fun z x ↦ pairOfPantsPerturbation (Pi.single zero H) (Complex.equivRealProdCLM.symm z)
          x Complex.I) w ((u ∘ realChart (c + a * ·)) w)‖ₑ := by
  set S := {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0}
  have hSm : MeasurableSet S :=
    (measurableSet_singleton 0).compl.preimage Complex.equivRealProdCLM.symm.continuous.measurable
  -- The affine chart maps `S` off the center, where the datum is differentiable.
  have hdiff {w : ℝ × ℝ} (hw : w ∈ S) (y : V) :
      DifferentiableAt ℝ (fun p : ℂ × V ↦ inputEndPerturbation c a H p.1 p.2)
        (Complex.equivRealProdCLM.symm (realChart (c + a * ·) w), y) := by
    refine differentiableAt_inputEndPerturbation hH hHs ha ?_ y
    rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply]
    exact fun h => hw (by simpa [ha] using h)
  -- The pullback of the datum along the affine chart is the pair-of-pants datum.
  have h₁ : Complex.equivRealProdCLM.symm stdComplexLineReal = 1 := by
    apply Complex.ext <;> simp [stdComplexLineReal_eq]
  have hI : Complex.equivRealProdCLM.symm stdComplexLineImag = Complex.I := by
    apply Complex.ext <;> simp [stdComplexLineImag_eq]
  have hpull (v : ℝ × ℝ) : perturbationPullback (realChart (c + a * ·))
      (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x Complex.I) v =
      fun w x ↦ pairOfPantsPerturbation (Pi.single zero H) (Complex.equivRealProdCLM.symm w) x
        (Complex.equivRealProdCLM.symm v) := by
    funext w x
    rw [perturbationPullback_realChart _
      (by simpa using ((hasDerivAt_id _).const_mul a).const_add c), inputEndPerturbation_add_mul ha]
  rw [ω.lintegral_enorm_hamiltonianCurvature_image hSm
    (realChart_injective fun _ _ h => mul_left_cancel₀ ha (add_left_cancel h)).injOn
    (fun w _ ↦ (contDiff_realChart (by fun_prop)).contDiffAt)
    (fun w hw ↦ differentiableAt_domain_of_differentiableAt (hdiff hw _) 1)
    (fun w hw ↦ differentiableAt_domain_of_differentiableAt (hdiff hw _) Complex.I)
    (fun w hw ↦ differentiableAt_target_of_differentiableAt (hdiff hw _) 1)
    (fun w hw ↦ differentiableAt_target_of_differentiableAt (hdiff hw _) Complex.I), hpull, hpull,
    h₁, hI]
  rfl

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
  have hP := ω.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le
    (forall_single zero (P := fun f => Periodic f 1) (fun _ => rfl) hH)
    (forall_single zero (P := fun f => ContDiff ℝ 1 (uncurry f)) contDiff_const hHs)
    (abs_single_le zero hB) (u ∘ realChart (c + a * ·))
  rw [Fintype.sum_eq_single zero fun r hr => by simp [Pi.single_eq_of_ne hr],
    Pi.single_eq_same] at hP
  calc _ = ∫⁻ z in univ, ‖ω.hamiltonianCurvature
        (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ := (setLIntegral_univ _).symm
    _ ≤ _ := lintegral_mono_set hcover
    _ ≤ _ := lintegral_union_le _ _ _
    _ = _ := by rw [setLIntegral_measure_zero _ _ hN, add_zero,
        setLIntegral_image_enorm_hamiltonianCurvature_inputEndPerturbation ω hH hHs
          ha u]
    _ ≤ _ := setLIntegral_le_lintegral _ _
    _ ≤ _ := hP

variable {ι : Type*} [Fintype ι] {c a : ι → ℂ} {H : ι → ℝ → V → ℝ} {Hout : ℝ → V → ℝ}

/-- On an open set where the datum of the sphere is a datum `P`, the integrated curvatures of the
two data agree. -/
private theorem setLIntegral_enorm_hamiltonianCurvature_puncturedSpherePerturbation_eq
    (ω : SymplecticForm V) {U : Set (ℝ × ℝ)} (hU : IsOpen U) {P : ℂ → V → ℂ →L[ℝ] ℝ}
    (hP : ∀ z ∈ U, ∀ x, puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
      = P (Complex.equivRealProdCLM.symm z) x) (u : ℝ × ℝ → V) :
    ∫⁻ z in U, ‖ω.hamiltonianCurvature
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z)‖ₑ =
      ∫⁻ z in U, ‖ω.hamiltonianCurvature
        (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)‖ₑ := by
  refine setLIntegral_congr_fun hU.measurableSet fun z hz ↦ ?_
  have hev : ∀ᶠ z' in 𝓝 z, ∀ x, puncturedSpherePerturbation c a H Hout
      (Complex.equivRealProdCLM.symm z') x = P (Complex.equivRealProdCLM.symm z') x := by
    filter_upwards [hU.mem_nhds hz] with z' hz'
    exact hP z' hz'
  rw [ω.hamiltonianCurvature_congr_of_eventuallyEq
    (hev.mono fun z' h ↦ funext fun x ↦ by rw [h x])
    (hev.mono fun z' h ↦ funext fun x ↦ by rw [h x])]

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
  have hD (i : ι) : ∫⁻ z in D i, f z ≤ ENNReal.ofReal (B i) := by
    rw [setLIntegral_enorm_hamiltonianCurvature_puncturedSpherePerturbation_eq ω (hDo i)
      fun z hz x ↦ puncturedSpherePerturbation_eq_inputEndPerturbation_of_norm_sub_lt
        (r := r) (fun _ ↦ le_rfl) hsep hout hz x]
    exact (setLIntegral_le_lintegral _ _).trans
      (lintegral_enorm_hamiltonianCurvature_inputEndPerturbation_le ω (hH i) (hHs i) (ha i)
        (hB i) u)
  have hO : ∫⁻ z in O, f z ≤ ENNReal.ofReal Bout := by
    rw [setLIntegral_enorm_hamiltonianCurvature_puncturedSpherePerturbation_eq ω hOo
      fun z hz x ↦ puncturedSpherePerturbation_eq_negativePlanePerturbation (fun i ↦ (hz i).le) x]
    exact (setLIntegral_le_lintegral _ _).trans
      (lintegral_enorm_hamiltonianCurvature_negativePlanePerturbation_le ω hHout hHouts hBout u)
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

end TauCeti.SymplecticForm
