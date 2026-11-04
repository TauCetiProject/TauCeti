/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Action
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.MeasureTheory.Integral.Annulus
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The energy of a pair of pants in terms of the actions of its ends

Let `K` be the pair-of-pants perturbation `TauCeti.Floer.pairOfPantsPerturbation` of period-one
Hamiltonians `H_q` on the three ends of `S = ℂ ∖ {0, 1}`, for a finite-dimensional symplectic
vector space target `(V, ω)`. For a map `u` on `S` and `R ≥ 0`, the *end loop*
`TauCeti.Floer.pairOfPantsEndLoop u q R` is the loop `t ↦ u(φ_q(±R + i t))` along the circle
`±s = R` of the end `q`, where `φ_q` is the end lift and `±` the sign of the end. This file
rewrites the energy identity on the truncated pair of pants
(`TauCeti.SymplecticForm.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation`) in terms
of the Hamiltonian actions `A_H(x) = a(x) + ∫₀¹ H(t, x(t)) dt` of these loops
(`TauCeti.SymplecticForm.hamiltonianAction`), and passes to the limit `R → ∞`.

The symplectic area of `u` over the truncation `S_R` is the signed sum `∑ q, ±a(x_q)` of the loop
areas of its end loops (`SymplecticForm.integral_symplecticForm_fderiv_truncation`). This is
Stokes' formula for the primitive `λₓ(v) = ½ ω(x, v)` on `S_R`, the closed annulus
`r ≤ ‖w‖ ≤ ρ` with the open disc of radius `r` about `1` removed. The end lifts traverse the
three boundary circles clockwise, which accounts for the signs. To apply the annulus formula
`TauCeti.SymplecticForm.integral_fderiv_apply_annulus`, `u` is first multiplied by a smooth
cutoff that vanishes near `1` and equals `1` near `S_R` (`TauCeti.exists_contDiffAt_cutoff_ball`);
the cut-off map is then smooth on the whole annulus. Its area over the removed disc, split off by
`TauCeti.setIntegral_diff_ball_add_annulus_add_ball`, is computed by the annulus formula about
`1`, whose inner boundary term vanishes.

Hence, for `R ≥ 2`, where the perturbation is `H_q(t) dt` along the boundary circles,

`∫_{S_R} E(u) = A_{H₀}(x₀) + A_{H₁}(x₁) - A_{H_∞}(x_∞) - ∫_{S_R} R_K(u)`

(`integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_sum_hamiltonianAction`).
The actions are those of the end loops capped by the cones `r x(t)`, the canonical caps in a
vector space, so no class `A` of spheres appears. If the energy density of `u` is nonnegative, as
it is for solutions of the Floer equation `(du - X_K)^{0,1} = 0` with respect to almost complex
structures tamed by `ω` (`TauCeti.SymplecticForm.floerEnergyDensity_nonneg`), the end
Hamiltonians are bounded, and the actions of the end loops converge to `A_q`, then the energy of
`u` over all of `S` is

`E(u) = A₀ + A₁ - A_∞ - ∫_S R_K(u)`

(`SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsPerturbation_eq`). With the curvature
bound `∫_S |R_K| ≤ B₀ + B₁ + B_∞` for `|H_q| ≤ B_q`, nonnegativity of the energy gives the action
bound `A_∞ ≤ A₀ + A₁ + B₀ + B₁ + B_∞`
(`SymplecticForm.hamiltonianAction_pairOfPantsEndLoop_inf_le_of_tendsto`), and already
`A_{H_∞}(x_∞) ≤ A_{H₀}(x₀) + A_{H₁}(x₁) + B₀ + B₁ + B_∞` for the end loops at every `R ≥ 2`
(`SymplecticForm.hamiltonianAction_pairOfPantsEndLoop_inf_le`). Thus a map with nonnegative
energy density from inputs of actions `A₀, A₁` to an output of action `A_∞` can exist only when
`A_∞ ≤ A₀ + A₁ + C` with `C = B₀ + B₁ + B_∞`. This is the shape of the support hypothesis
`F₀ ≤ F₁ + F₂ + C` of `TauCeti.NovikovModule.kernelProduct`, with the actions as filtrations.

## Main definitions

* `TauCeti.Floer.pairOfPantsEndLoop u q R`: the loop of `u` along the circle `±s = R` of the
  end `q`.
  It has period one (`TauCeti.Floer.periodic_pairOfPantsEndLoop`).

## Main results

* `SymplecticForm.integral_symplecticForm_fderiv_truncation`: the symplectic area over the
  truncation is the signed sum of the loop areas of the end loops.
* `integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_sum_hamiltonianAction`:
  the energy identity on the truncation in terms of the actions of the end loops.
* `SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsPerturbation_eq`: for bounded end
  Hamiltonians, the energy of a map with nonnegative energy density whose end-loop actions
  converge to `A_q` is `A₀ + A₁ - A_∞ - ∫_S R_K`.
* `SymplecticForm.hamiltonianAction_pairOfPantsEndLoop_inf_le`,
  `SymplecticForm.hamiltonianAction_pairOfPantsEndLoop_inf_le_of_tendsto`: the action bound for
  the output end.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the energy estimate for the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity with Hamiltonian perturbations.
-/

public section

open Set Real Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology

namespace TauCeti

namespace Floer

variable {V : Type*}

/-- The end loop `t ↦ u(φ_q(±R + i t))` of a map `u : ℝ × ℝ → V` on the thrice-punctured sphere,
in real coordinates, along the circle at signed longitudinal coordinate `±s = R` of the end `q`.
Here `φ_q` is the end lift `TauCeti.ThricePuncturedSphere.Puncture.cylindricalEndLift q` and `±`
is the sign of the end. The loop has period one, and for `R ≥ 0` its circle is a boundary circle
of the truncation `TauCeti.ThricePuncturedSphere.truncation R`. -/
noncomputable def pairOfPantsEndLoop (u : ℝ × ℝ → V) (q : Puncture) (R : ℝ) : ℝ → V :=
  fun t ↦ u (Complex.equivRealProdCLM (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))

@[simp]
theorem pairOfPantsEndLoop_apply (u : ℝ × ℝ → V) (q : Puncture) (R t : ℝ) :
    pairOfPantsEndLoop u q R t =
      u (Complex.equivRealProdCLM (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))) :=
  (rfl)

/-- The end loop has period one. -/
theorem periodic_pairOfPantsEndLoop (u : ℝ × ℝ → V) (q : Puncture) (R : ℝ) :
    Periodic (pairOfPantsEndLoop u q R) 1 := fun t ↦ by
  simp only [pairOfPantsEndLoop_apply, periodic_cylindricalEndLift q (q.endSign * R) t]

end Floer

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {H : Puncture → ℝ → V → ℝ}

section Area

/-- Twice the integral of the primitive `λₓ(v) = ½ ω(x, v)` along the image under `v` of the
counterclockwise circle of center `c` and radius `s`, that is `∫ ω(v, ∂_θ v) dθ`, as in
`TauCeti.SymplecticForm.integral_fderiv_apply_annulus`. -/
private noncomputable def circleTerm (ω : SymplecticForm V) (v : ℂ → V) (c : ℂ) (s : ℝ) : ℝ :=
  ∫ θ in -π..π, ω (v (circleMap c s θ)) (deriv (fun θ ↦ v (circleMap c s θ)) θ)

/-- The circle term only depends on the values of the map on the circle. -/
private theorem circleTerm_congr (ω : SymplecticForm V) {v v' : ℂ → V} {c : ℂ} {s : ℝ}
    (h : ∀ θ, v (circleMap c s θ) = v' (circleMap c s θ)) :
    circleTerm ω v c s = circleTerm ω v' c s := by
  simp only [circleTerm, h]

/-- The radii `r = exp (-2πR) / 2` and `ρ = 2 exp (2πR)` of the boundary circles of the
truncation satisfy `0 < r ≤ 1/2` and `2 ≤ ρ` for `R ≥ 0`. -/
private theorem radii_bounds {R : ℝ} (hR : 0 ≤ R) :
    0 < Real.exp (-(2 * π * R)) / 2 ∧ Real.exp (-(2 * π * R)) / 2 ≤ 1 / 2 ∧
      2 ≤ 2 * Real.exp (2 * π * R) := by
  have h₁ : Real.exp (-(2 * π * R)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [pi_pos])
  have h₂ : 1 ≤ Real.exp (2 * π * R) := Real.one_le_exp (by positivity)
  exact ⟨by positivity, by linarith, by linarith⟩

/-- **The end loops as circles.** For `R ≥ 0` and a map `v` that is `C²` on `S`, the loop area
of the end loop of `v` at the end `q` is minus half the circle term of `v` on the circle of radius
`r = exp (-2πR) / 2` about `0` or `1`, or of radius `ρ = 2 exp (2πR)` about `0`. -/
private theorem loopArea_cylindricalEndLift_eq (ω : SymplecticForm V) {v : ℂ → V}
    (hv : ∀ w : ℂ, w ≠ 0 → w ≠ 1 → ContDiffAt ℝ 2 v w) {R : ℝ} (hR : 0 ≤ R) :
    ω.loopArea (fun t ↦ v (zero.cylindricalEndLift (↑(zero.endSign * R) + ↑t * Complex.I))) =
        -(1 / 2) * circleTerm ω v 0 (Real.exp (-(2 * π * R)) / 2) ∧
      ω.loopArea (fun t ↦ v (one.cylindricalEndLift (↑(one.endSign * R) + ↑t * Complex.I))) =
        -(1 / 2) * circleTerm ω v 1 (Real.exp (-(2 * π * R)) / 2) ∧
      ω.loopArea (fun t ↦ v (inf.cylindricalEndLift (↑(inf.endSign * R) + ↑t * Complex.I))) =
        -(1 / 2) * circleTerm ω v 0 (2 * Real.exp (2 * π * R)) := by
  have h₀ (t : ℝ) : zero.cylindricalEndLift (↑(zero.endSign * R) + ↑t * Complex.I) =
      circleMap 0 (Real.exp (-(2 * π * R)) / 2) (0 - 2 * π * t) := by
    rw [endSign_zero, one_mul, cylindricalEndLift_zero_eq_circleMap, zero_sub]
  have h₁ (t : ℝ) : one.cylindricalEndLift (↑(one.endSign * R) + ↑t * Complex.I) =
      circleMap 1 (Real.exp (-(2 * π * R)) / 2) (π - 2 * π * t) := by
    rw [endSign_one, one_mul, cylindricalEndLift_one_eq_circleMap]
  have hinf (t : ℝ) : inf.cylindricalEndLift (↑(inf.endSign * R) + ↑t * Complex.I) =
      circleMap 0 (2 * Real.exp (2 * π * R)) (0 - 2 * π * t) := by
    rw [endSign_inf, cylindricalEndLift_inf_eq_circleMap, zero_sub, neg_one_mul, mul_neg,
      neg_neg]
  obtain ⟨hr, hr₂, hρ⟩ := radii_bounds hR
  set r : ℝ := Real.exp (-(2 * π * R)) / 2
  set ρ : ℝ := 2 * Real.exp (2 * π * R)
  have hdiff {c : ℂ} {s : ℝ} (hc : ∀ θ, 0 < ‖circleMap c s θ‖ ∧ 0 < ‖circleMap c s θ - 1‖)
      (θ : ℝ) : DifferentiableAt ℝ v (circleMap c s θ) :=
    (hv _ (norm_pos_iff.1 (hc θ).1) (sub_ne_zero.1 (norm_pos_iff.1 (hc θ).2))).differentiableAt
      (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · simp only [h₀]
    refine ω.loopArea_circleMap_sub_two_pi_mul 0 r 0 (hdiff fun θ ↦ ?_)
    have h := mem_sphere_iff_norm.1 (circleMap_mem_sphere 0 hr.le θ)
    rw [sub_zero] at h
    exact ⟨by linarith,
      by linarith [norm_le_norm_add_norm_sub (circleMap 0 r θ) 1, norm_one (α := ℂ)]⟩
  · simp only [h₁]
    refine ω.loopArea_circleMap_sub_two_pi_mul 1 r π (hdiff fun θ ↦ ?_)
    have h := mem_sphere_iff_norm.1 (circleMap_mem_sphere 1 hr.le θ)
    exact ⟨by linarith [norm_le_norm_add_norm_sub (circleMap 1 r θ) 1, norm_one (α := ℂ)],
      by linarith⟩
  · simp only [hinf]
    refine ω.loopArea_circleMap_sub_two_pi_mul 0 ρ 0 (hdiff fun θ ↦ ?_)
    have h := mem_sphere_iff_norm.1 (circleMap_mem_sphere 0 (by linarith : 0 ≤ ρ) θ)
    rw [sub_zero] at h
    exact ⟨by linarith, by linarith [norm_sub_norm_le (circleMap 0 ρ θ) 1, norm_one (α := ℂ)]⟩

variable [FiniteDimensional ℝ V]

/-- **The symplectic area of the truncated pair of pants, in complex coordinates.** -/
private theorem integral_truncation_complex (ω : SymplecticForm V) {v : ℂ → V}
    (hv : ∀ w : ℂ, w ≠ 0 → w ≠ 1 → ContDiffAt ℝ 2 v w) {R : ℝ} (hR : 0 ≤ R) :
    ∫ w in truncation R, ω (fderiv ℝ v w 1) (fderiv ℝ v w Complex.I) =
      ∑ q : Puncture, q.endSign * ω.loopArea
        (fun t ↦ v (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))) := by
  obtain ⟨hloop₀, hloop₁, hloopinf⟩ := loopArea_cylindricalEndLift_eq ω hv hR
  obtain ⟨hr, hr₂, hρ⟩ := radii_bounds hR
  set r : ℝ := Real.exp (-(2 * π * R)) / 2
  set ρ : ℝ := 2 * Real.exp (2 * π * R)
  have hT (w : ℂ) : w ∈ truncation R ↔ (r ≤ ‖w‖ ∧ r ≤ ‖w - 1‖) ∧ ‖w‖ ≤ ρ := by
    rw [truncation_eq]
    simp [r, ρ]
  -- Cut `v` off near `1`; the cut-off map agrees with `v` on the three boundary circles of the
  -- truncation and vanishes on the circle of radius `r / 4` about `1`.
  obtain ⟨vc, hvc', hvc₀', hvcv'⟩ :=
    exists_contDiffAt_cutoff_ball (n := 2) (b := 3 * r / 4) v 1 (by positivity : 0 < r / 2)
      (by linarith)
  have hvc₀ (w : ℂ) (hw : ‖w - 1‖ < r / 2) : vc =ᶠ[𝓝 w] 0 := hvc₀' w (by rwa [dist_eq_norm])
  have hvcv (w : ℂ) (hw : 3 * r / 4 < ‖w - 1‖) : vc =ᶠ[𝓝 w] v :=
    hvcv' w (by rwa [dist_eq_norm])
  have hvc (w : ℂ) (hw : w ≠ 0) : ContDiffAt ℝ 2 vc w := by
    by_cases hw₁ : w = 1
    · subst hw₁
      exact contDiffAt_const.congr_of_eventuallyEq (hvc₀ 1 (by simp; linarith))
    · exact hvc' w (hv w hw hw₁)
  have hvceq {c : ℂ} {s : ℝ} (hc : ∀ θ, 3 * r / 4 < ‖circleMap c s θ - 1‖) :
      circleTerm ω vc c s = circleTerm ω v c s :=
    circleTerm_congr ω fun θ ↦ (hvcv _ (hc θ)).eq_of_nhds
  have hC₀ : circleTerm ω vc 0 r = circleTerm ω v 0 r := hvceq fun θ ↦ by
    have h := mem_sphere_iff_norm.1 (circleMap_mem_sphere 0 hr.le θ)
    rw [sub_zero] at h
    linarith [norm_le_norm_add_norm_sub (circleMap 0 r θ) 1, norm_one (α := ℂ)]
  have hCρ : circleTerm ω vc 0 ρ = circleTerm ω v 0 ρ := hvceq fun θ ↦ by
    have h := mem_sphere_iff_norm.1 (circleMap_mem_sphere 0 (by linarith : 0 ≤ ρ) θ)
    rw [sub_zero] at h
    linarith [norm_sub_norm_le (circleMap 0 ρ θ) 1, norm_one (α := ℂ)]
  have hC₁ : circleTerm ω vc 1 r = circleTerm ω v 1 r := hvceq fun θ ↦ by
    rw [mem_sphere_iff_norm.1 (circleMap_mem_sphere 1 hr.le θ)]
    linarith
  have hCin : circleTerm ω vc 1 (r / 4) = 0 := by
    have hz (θ : ℝ) : vc (circleMap 1 (r / 4) θ) = 0 :=
      (hvc₀ _ (by
        rw [mem_sphere_iff_norm.1 (circleMap_mem_sphere 1 (by positivity) θ)]; linarith)).eq_of_nhds
    simp [circleTerm, hz]
  -- Stokes' formula on the annulus `r ≤ ‖w‖ ≤ ρ` and on the annulus `r / 4 ≤ ‖w - 1‖ ≤ r`.
  set f : ℂ → ℝ := fun w ↦ ω (fderiv ℝ vc w 1) (fderiv ℝ vc w Complex.I)
  have hne {w : ℂ} (hw : r ≤ ‖w - 0‖) : w ≠ 0 := norm_pos_iff.1 (by rw [← sub_zero w]; linarith)
  have hA : ∫ w in {w | r ≤ ‖w - 0‖ ∧ ‖w - 0‖ ≤ ρ}, f w =
      (1 / 2 : ℝ) * (circleTerm ω vc 0 ρ - circleTerm ω vc 0 r) :=
    ω.integral_fderiv_apply_annulus 0 hr (by linarith) fun w hw ↦ hvc w (hne hw.1)
  have hD : ∫ w in {w | r / 4 ≤ ‖w - 1‖ ∧ ‖w - 1‖ ≤ r}, f w =
      (1 / 2 : ℝ) * (circleTerm ω vc 1 r - circleTerm ω vc 1 (r / 4)) :=
    ω.integral_fderiv_apply_annulus 1 (by positivity) (by linarith) fun w hw ↦
      hvc w (norm_pos_iff.1
        (by linarith [norm_le_norm_add_norm_sub w 1, norm_one (α := ℂ), hw.2]))
  -- The area density of the cut-off map is integrable on the annulus about `0`, vanishes on the
  -- disc of radius `r / 4` about `1`, and is that of `v` on the truncation.
  have hfA : IntegrableOn f {w | r ≤ ‖w - 0‖ ∧ ‖w - 0‖ ≤ ρ} := by
    have hAc : IsCompact {w : ℂ | r ≤ ‖w - 0‖ ∧ ‖w - 0‖ ≤ ρ} :=
      Metric.isCompact_of_isClosed_isBounded
        ((isClosed_le continuous_const (continuous_norm.comp (continuous_sub_right 0))).inter
          (isClosed_le (continuous_norm.comp (continuous_sub_right 0)) continuous_const))
        ((Metric.isBounded_closedBall (x := (0 : ℂ)) (r := ρ)).subset fun w hw ↦ by
          simpa [dist_eq_norm] using hw.2)
    refine ContinuousOn.integrableOn_compact hAc ?_
    have hdf {w : ℂ} (hw : r ≤ ‖w - 0‖) : ContinuousAt (fderiv ℝ vc) w :=
      ((hvc w (hne hw)).fderiv_right (m := 1) (by norm_num)).continuousAt
    exact ω.continuousOn_apply_comp
      (fun w hw ↦ ((hdf hw.1).clm_apply continuousAt_const).continuousWithinAt)
      (fun w hw ↦ ((hdf hw.1).clm_apply continuousAt_const).continuousWithinAt)
  have hball : ∫ w in Metric.ball 1 (r / 4), f w = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun w hw ↦ ?_
    rw [Metric.mem_ball, dist_eq_norm] at hw
    simp [f, (hvc₀ w (by linarith)).fderiv_eq (𝕜 := ℝ)]
  have htrunc : ∫ w in truncation R, ω (fderiv ℝ v w 1) (fderiv ℝ v w Complex.I) =
      ∫ w in truncation R, f w := by
    refine setIntegral_congr_fun (isCompact_truncation R).isClosed.measurableSet fun w hw ↦ ?_
    simp only [f, (hvcv w (by linarith [((hT w).1 hw).1.2])).fderiv_eq (𝕜 := ℝ)]
  -- Split the annulus about `0` into the truncation, the annulus `r / 4 ≤ ‖w - 1‖ ≤ r` and the
  -- disc of radius `r / 4` about `1`.
  have hsub : Metric.closedBall (1 : ℂ) r ⊆ {w | r ≤ ‖w - 0‖ ∧ ‖w - 0‖ ≤ ρ} := fun w hw ↦ by
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    rw [mem_ofPred_eq, sub_zero]
    exact ⟨by linarith [norm_le_norm_add_norm_sub w 1, norm_one (α := ℂ)],
      by linarith [norm_sub_norm_le w 1, norm_one (α := ℂ)]⟩
  have hTeq : {w : ℂ | r ≤ ‖w - 0‖ ∧ ‖w - 0‖ ≤ ρ} \ Metric.ball 1 r = truncation R := by
    ext w
    rw [hT, Set.mem_sdiff, mem_ofPred_eq, Metric.mem_ball, dist_eq_norm, not_lt, sub_zero]
    tauto
  have hsplit :=
    setIntegral_diff_ball_add_annulus_add_ball volume (s := r / 4) (by linarith) hsub hfA
  rw [hTeq] at hsplit
  rw [htrunc, Puncture.sum_univ, hloop₀, hloop₁, hloopinf, endSign_zero, endSign_one, endSign_inf]
  linarith

/-- **The symplectic area of the truncated pair of pants.** Let `u` be `C²` on the
thrice-punctured sphere `S = ℂ ∖ {0, 1}`, in real coordinates. For `R ≥ 0` the symplectic area of
`u` over the truncation `S_R` is the signed sum over the three ends of the loop areas of its end
loops at `±s = R`, with the sign `+` on the input ends `0`, `1` and `-` on the output end `∞`:

`∫_{S_R} u^*ω = a(x₀) + a(x₁) - a(x_∞)`. -/
theorem integral_symplecticForm_fderiv_truncation (ω : SymplecticForm V) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {R : ℝ} (hR : 0 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R,
        ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) =
      ∑ q, q.endSign * ω.loopArea (pairOfPantsEndLoop u q R) := by
  have hmem {w : ℂ} (h₀ : w ≠ 0) (h₁ : w ≠ 1) :
      Complex.equivRealProdCLM w ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1} := by
    simp only [mem_ofPred_eq, ContinuousLinearEquiv.symm_apply_apply]
    exact ⟨h₀, h₁⟩
  have hdu {w : ℂ} (h₀ : w ≠ 0) (h₁ : w ≠ 1) : ContDiffAt ℝ 2 u (Complex.equivRealProdCLM w) :=
    hu.contDiffAt (isOpen_equivRealProdCLM_symm_ne_zero_and_ne_one.mem_nhds (hmem h₀ h₁))
  have hv (w : ℂ) (h₀ : w ≠ 0) (h₁ : w ≠ 1) : ContDiffAt ℝ 2 (u ∘ Complex.equivRealProdCLM) w :=
    (hdu h₀ h₁).comp w Complex.equivRealProdCLM.contDiff.contDiffAt
  -- Change variables along the measure-preserving identification `ℂ ≃ ℝ × ℝ`.
  have hpre : Complex.measurableEquivRealProd ⁻¹'
      (Complex.equivRealProdCLM.symm ⁻¹' truncation R) = truncation R := by
    ext w
    simp [Complex.measurableEquivRealProd_apply, Complex.equivRealProdCLM_symm_apply]
  rw [← Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding, hpre]
  convert integral_truncation_complex ω hv hR using 1
  · refine setIntegral_congr_fun (isCompact_truncation R).isClosed.measurableSet fun w hw ↦ ?_
    have hd := ((hdu (mem_truncation.1 hw).1 (mem_truncation.1 hw).2.1).differentiableAt
      (by norm_num)).hasFDerivAt.comp w Complex.equivRealProdCLM.hasFDerivAt
    simp only [hd.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      Complex.equivRealProdCLM_apply, Complex.measurableEquivRealProd_apply, Complex.one_re,
      Complex.one_im, Complex.I_re, Complex.I_im, stdComplexLineReal_eq, stdComplexLineImag_eq]
  · simp only [comp_apply, ← pairOfPantsEndLoop_apply]

end Area

section Energy

variable [FiniteDimensional ℝ V]

/-- **The energy identity on the truncated pair of pants, in terms of actions.** Let `K` be the
pair-of-pants perturbation of period-one `C¹` Hamiltonians `H_q` on the three ends of
`S = ℂ ∖ {0, 1}`, with components `K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global
coordinate `z = s + i t`, and let `u` be `C²` on `S`. For `R ≥ 2` the Floer energy of `u` over the
truncation `S_R` is the signed sum of the Hamiltonian actions of its end loops at `±s = R`, minus
the integrated curvature:

`∫_{S_R} E(u) = A_{H₀}(x₀) + A_{H₁}(x₁) - A_{H_∞}(x_∞) - ∫_{S_R} R_K(u)`. -/
theorem integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_sum_hamiltonianAction
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {R : ℝ} (hR : 2 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      ∑ q, q.endSign * ω.hamiltonianAction (H q) (pairOfPantsEndLoop u q R) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  rw [integral_floerEnergyDensity_pairOfPantsPerturbation_truncation ω hH hHs
      (hu.of_le one_le_two) (by linarith),
    integral_symplecticForm_fderiv_truncation ω hu (by linarith),
    smoothTransition.one_of_one_le (by linarith), one_mul]
  simp only [hamiltonianAction_def, pairOfPantsEndLoop_apply, mul_add, Finset.sum_add_distrib]

/-- **The action bound for the output end at a finite truncation.** Under the hypotheses of
`integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_sum_hamiltonianAction`, if
the Floer energy density of `u` is nonnegative on `S`, as it is for solutions of the Floer
equation with respect to almost complex structures tamed by `ω`, and the end Hamiltonians are
bounded, `|H_q| ≤ B_q`, then for every `R ≥ 2` the action of the output end loop is at most the
sum of the actions of the input end loops plus `B₀ + B₁ + B_∞`. -/
theorem hamiltonianAction_pairOfPantsEndLoop_inf_le (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    (hE : ∀ z, Complex.equivRealProdCLM.symm z ≠ 0 → Complex.equivRealProdCLM.symm z ≠ 1 →
      0 ≤ ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z)
    {R : ℝ} (hR : 2 ≤ R) :
    ω.hamiltonianAction (H inf) (pairOfPantsEndLoop u inf R) ≤
      ω.hamiltonianAction (H zero) (pairOfPantsEndLoop u zero R) +
        ω.hamiltonianAction (H one) (pairOfPantsEndLoop u one R) + ∑ q, B q := by
  have h := abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_le ω hH hHs hB
    (hu.of_le one_le_two) (by linarith : (1 : ℝ) ≤ R)
  rw [integral_symplecticForm_fderiv_truncation ω hu (by linarith),
    smoothTransition.one_of_one_le (by linarith), one_mul] at h
  have hnonneg := setIntegral_nonneg (μ := volume)
    ((isCompact_truncation R).isClosed.preimage
      Complex.equivRealProdCLM.symm.continuous).measurableSet
    fun z hz ↦ hE z (mem_truncation.1 hz).1 (mem_truncation.1 hz).2.1
  rw [Puncture.sum_univ, Puncture.sum_univ] at h
  simp only [hamiltonianAction_def, pairOfPantsEndLoop_apply, endSign_zero, endSign_one,
    endSign_inf] at h ⊢
  linarith [(abs_le.1 h).2]

/-- **The energy of a pair of pants.** Under the hypotheses of
`integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_sum_hamiltonianAction`,
suppose that the Floer energy density of `u` is nonnegative on `S`, as it is for solutions of the
Floer equation with respect to almost complex structures tamed by `ω`, and that the end
Hamiltonians are bounded. If the actions of the end loops of `u` converge to `A_q` as `R → ∞`,
then the Floer energy of `u` over `S` is

`E(u) = A₀ + A₁ - A_∞ - ∫_S R_K(u)`. -/
theorem lintegral_floerEnergyDensity_pairOfPantsPerturbation_eq (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    (hE : ∀ z, Complex.equivRealProdCLM.symm z ≠ 0 → Complex.equivRealProdCLM.symm z ≠ 1 →
      0 ≤ ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z)
    {A : Puncture → ℝ}
    (hA : ∀ q, Tendsto (fun R ↦ ω.hamiltonianAction (H q) (pairOfPantsEndLoop u q R)) atTop
      (𝓝 (A q))) :
    ∫⁻ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1},
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z) =
      ENNReal.ofReal (∑ q, q.endSign * A q -
        ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
            Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z)) := by
  set S := {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
    Complex.equivRealProdCLM.symm z ≠ 1}
  set T : ℝ → Set (ℝ × ℝ) := fun R ↦ Complex.equivRealProdCLM.symm ⁻¹' truncation R
  set E := ω.floerEnergyDensity
    (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
  set κ := fun z ↦ ω.hamiltonianCurvature
    (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)
  have hTm (R : ℝ) : MeasurableSet (T R) :=
    ((isCompact_truncation R).isClosed.preimage
      Complex.equivRealProdCLM.symm.continuous).measurableSet
  have hmono : Monotone T := fun _ _ h ↦ preimage_mono (truncation_mono h)
  have hunion : ⋃ R, T R = S := by
    simp only [T, ← preimage_iUnion, iUnion_truncation]
    rfl
  have hTS (R : ℝ) : T R ⊆ S := hunion ▸ subset_iUnion T R
  have hSo : IsOpen S := isOpen_equivRealProdCLM_symm_ne_zero_and_ne_one
  -- The curvature is integrable on `S`, so its integrals over the truncations converge.
  have hκ : IntegrableOn κ S := by
    refine ⟨(ω.continuousOn_hamiltonianCurvature_comp hSo hu.continuousOn
      (contDiffOn_pairOfPantsPerturbation hH hHs 1)
      (contDiffOn_pairOfPantsPerturbation hH hHs Complex.I)).aestronglyMeasurable
      hSo.measurableSet, ?_⟩
    refine ((setLIntegral_le_lintegral _ _).trans
      (lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le ω hH hHs hB u)).trans_lt ?_
    exact ENNReal.sum_lt_top.2 fun q _ ↦ ENNReal.ofReal_lt_top
  have hκlim : Tendsto (fun R ↦ ∫ z in T R, κ z) atTop (𝓝 (∫ z in S, κ z)) := by
    have h := tendsto_setIntegral_of_monotone hTm hmono (hunion ▸ hκ)
    rwa [hunion] at h
  -- The energies over the truncations converge to the right side.
  have hElim : Tendsto (fun R ↦ ∫ z in T R, E z) atTop
      (𝓝 (∑ q, q.endSign * A q - ∫ z in S, κ z)) := by
    refine ((tendsto_finsetSum _ fun q _ ↦ (hA q).const_mul q.endSign).sub hκlim).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with R hR
    exact (integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_sum_hamiltonianAction
      ω hH hHs hu hR).symm
  -- They also converge to the energy over `S`, by monotone convergence.
  have hlim : Tendsto (fun R ↦ ∫⁻ z in T R, ENNReal.ofReal (E z)) atTop
      (𝓝 (∫⁻ z in S, ENNReal.ofReal (E z))) := by
    have h := tendsto_measure_iUnion_atTop
      (μ := volume.withDensity fun z ↦ ENNReal.ofReal (E z)) hmono
    rw [hunion, withDensity_apply _ hSo.measurableSet] at h
    simpa only [comp_def, withDensity_apply _ (hTm _)] using h
  refine tendsto_nhds_unique hlim (((ENNReal.continuous_ofReal.tendsto _).comp hElim).congr' ?_)
  filter_upwards with R
  have hint := (integrableOn_truncation_pairOfPantsPerturbation ω hH hHs
    (hu.of_le one_le_two) R).1
  exact ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem (hTm R) fun z hz ↦ hE z (hTS R hz).1 (hTS R hz).2)

/-- **The action bound for the output end.** Under the hypotheses of
`TauCeti.SymplecticForm.hamiltonianAction_pairOfPantsEndLoop_inf_le`, if the actions of the end
loops of `u` converge to `A_q` as `R → ∞`, then `A_∞ ≤ A₀ + A₁ + B₀ + B₁ + B_∞`. This has the
shape of the support hypothesis `F₀ ≤ F₁ + F₂ + C` of `TauCeti.NovikovModule.kernelProduct`, with
the actions as filtrations and `C = B₀ + B₁ + B_∞`. -/
theorem hamiltonianAction_pairOfPantsEndLoop_inf_le_of_tendsto (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    (hE : ∀ z, Complex.equivRealProdCLM.symm z ≠ 0 → Complex.equivRealProdCLM.symm z ≠ 1 →
      0 ≤ ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z)
    {A : Puncture → ℝ}
    (hA : ∀ q, Tendsto (fun R ↦ ω.hamiltonianAction (H q) (pairOfPantsEndLoop u q R)) atTop
      (𝓝 (A q))) :
    A inf ≤ A zero + A one + ∑ q, B q := by
  refine le_of_tendsto_of_tendsto (hA inf) (((hA zero).add (hA one)).add_const _) ?_
  filter_upwards [eventually_ge_atTop 2] with R hR
  exact hamiltonianAction_pairOfPantsEndLoop_inf_le ω hH hHs hB hu hE hR

end Energy

end SymplecticForm

end TauCeti
