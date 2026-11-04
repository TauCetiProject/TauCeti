/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Action
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The action form of the energy identity on the truncated pair of pants

The energy identity for pairs of pants reads `E = A₁ + A₂ - A₀ + ω(A) - ∫ R_K`, where `Aᵢ` is the
action of the asymptotic orbit at the end `i` with its cap. For a symplectic vector space target
every loop has the unique cap class of the cone over it, the class `A` vanishes, and the action is
`A_H(x) = a(x) + ∫₀¹ H(t, x(t)) dt` with the loop area `a(x) = ½ ∫₀¹ ω(x, x') dt`
(`TauCeti.SymplecticForm.hamiltonianAction`). This file proves this form of the identity on the
truncation `S_R` of the thrice-punctured sphere `S = ℂ ∖ {0, 1}`, where every signed longitudinal
end coordinate is at most `R`.

The truncation is the closed disc of radius `2 exp (2πR)` about `0` with the open discs of radius
`exp (-2πR) / 2` about `0` and `1` removed
(`TauCeti.ThricePuncturedSphere.truncation_eq_closedBall_diff`). Its three boundary circles are
the loops `x_q^R(t) = u(φ_q(±R + i t))` of a map `u` along the three ends, where `φ_q` is the end
lift of `q` (`TauCeti.ThricePuncturedSphere.Puncture.cylindricalEndLift_zero_endSign_mul_add`
and its analogues at `1` and `∞`). Stokes' formula on a disc with holes
(`TauCeti.SymplecticForm.integral_fderiv_apply_closedBall_diff_iUnion_ball`) therefore computes the
symplectic area of a `C²` map `u` on `S` as the signed sum of loop areas

`∫_{S_R} u^*ω = a(x_0^R) + a(x_1^R) - a(x_∞^R)`

(`TauCeti.SymplecticForm.integral_symplecticForm_fderiv_truncation_eq_sum_loopArea`). The signs
record that the loops at the input ends `0` and `1` run clockwise around their holes, which is
the boundary orientation of `S_R`, while the loop at the output end `∞` runs clockwise around the
outer circle, against it.

Combined with the energy identity on the truncation
(`TauCeti.SymplecticForm.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation`), for
`R ≥ 2`, where the perturbation is `H_q(t) dt` along the boundary circles, this gives

`∫_{S_R} E = A_{H_0}(x_0^R) + A_{H_1}(x_1^R) - A_{H_∞}(x_∞^R) - ∫_{S_R} R_K(u)`

(`SymplecticForm.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_sum_sub`). With
the curvature bound `∫ |R_K| ≤ B₀ + B₁ + B_∞` for Hamiltonians bounded by `B_q`, the energy differs
from this signed sum of actions by at most `B₀ + B₁ + B_∞`, uniformly in `R`
(`SymplecticForm.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_sum_le`).
For a solution of the Floer equation with tame almost complex structures the energy is
nonnegative, so the output action is bounded by the input actions:

`A_{H_∞}(x_∞^R) ≤ A_{H_0}(x_0^R) + A_{H_1}(x_1^R) + B₀ + B₁ + B_∞`

(`TauCeti.SymplecticForm.hamiltonianAction_inf_le_of_isComplexLinearMap`). This is the action
estimate behind the lower support bound of pair-of-pants coefficients, here for a target whose
caps are unique.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity and action estimates for Floer solutions.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the energy estimate for the pair-of-pants product.
-/

public section

open Set Real Function MeasureTheory TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The symplectic area of the truncated pair of pants.** Let `u` be `C²` on the
thrice-punctured sphere `S = ℂ ∖ {0, 1}`, in the real coordinates `ℝ × ℝ ≃ ℂ`. For `R > 0`, the
symplectic area of `u` over the truncation `S_R` is the signed sum of the loop areas of its loops
`x_q^R(t) = u(φ_q(±R + i t))` along the boundary circles of the three ends:

`∫_{S_R} u^*ω = a(x_0^R) + a(x_1^R) - a(x_∞^R)`,

with the sign `+` on the input ends `0` and `1` and `-` on the output end `∞`. -/
theorem integral_symplecticForm_fderiv_truncation_eq_sum_loopArea [FiniteDimensional ℝ V]
    (ω : SymplecticForm V) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {R : ℝ} (hR : 0 < R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R,
        ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) =
      ∑ q : Puncture, q.endSign * ω.loopArea (fun t ↦ u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) := by
  set e := Complex.equivRealProdCLM
  set v : ℂ → V := u ∘ e with hv_def
  set r := 2 * Real.exp (2 * π * R)
  set ρ := Real.exp (-(2 * π * R)) / 2
  set c : Fin 2 → ℂ := ![0, 1]
  -- `v` is `C²` on `S`.
  have hopen : IsOpen {z : ℝ × ℝ | e.symm z ≠ 0 ∧ e.symm z ≠ 1} :=
    (isOpen_ne.inter isOpen_ne).preimage e.symm.continuous
  have hv {w : ℂ} (hw : w ≠ 0 ∧ w ≠ 1) : ContDiffAt ℝ 2 v w :=
    (hu.contDiffAt (hopen.mem_nhds (by simpa using hw))).comp w e.contDiff.contDiffAt
  -- The area integral, in the complex coordinate.
  have hfderiv (z : ℝ × ℝ) (w : ℂ) :
      fderiv ℝ v (e.symm z) w = fderiv ℝ u z (e w) := by
    rw [e.comp_right_fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      e.apply_symm_apply]
  have hchange : (∫ z in e.symm ⁻¹' truncation R,
        ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) =
      ∫ w in truncation R, ω (fderiv ℝ v w 1) (fderiv ℝ v w Complex.I) := by
    have hcoe : ⇑Complex.measurableEquivRealProd.symm = e.symm := by
      funext p
      apply Complex.ext <;> simp [e]
    have h := (Complex.volume_preserving_equiv_real_prod.symm).setIntegral_preimage_emb
      (MeasurableEquiv.measurableEmbedding _)
      (fun w ↦ ω (fderiv ℝ v w 1) (fderiv ℝ v w Complex.I)) (truncation R)
    rw [hcoe] at h
    rw [← h]
    refine setIntegral_congr_fun ((isCompact_truncation R).isClosed.measurableSet.preimage
      e.symm.continuous.measurable) fun z _ ↦ ?_
    rw [hfderiv, hfderiv]
    simp [e, stdComplexLineReal, stdComplexLineImag]
  -- Stokes' formula on the disc with two holes.
  have hρ : 0 < ρ := by positivity
  have hρ_lt : ρ < 1 / 2 := by
    have : Real.exp (-(2 * π * R)) < 1 := Real.exp_lt_one_iff.2 (by nlinarith [pi_pos])
    simp only [ρ]
    linarith
  have hr : 2 ≤ r := by
    have : 1 ≤ Real.exp (2 * π * R) := Real.one_le_exp (by positivity)
    simp only [r]
    linarith
  have hc (i : Fin 2) : ‖c i‖ ≤ 1 := by fin_cases i <;> simp [c]
  have hsub (i : Fin 2) : Metric.closedBall (c i) ρ ⊆ Metric.ball 0 r := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    rw [Metric.mem_ball, dist_zero_right]
    calc ‖w‖ = ‖(w - c i) + c i‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - c i‖ + ‖c i‖ := norm_add_le _ _
      _ < r := by linarith [hc i]
  have hdisj : Pairwise fun i j : Fin 2 ↦
      Disjoint (Metric.closedBall (c i) ρ) (Metric.closedBall (c j) ρ) := by
    intro i j hij
    refine Metric.closedBall_disjoint_closedBall ?_
    fin_cases i <;> fin_cases j <;> simp_all [c, dist_eq_norm] <;> linarith
  have htrunc : truncation R = Metric.closedBall 0 r \ ⋃ i, Metric.ball (c i) ρ := by
    rw [truncation_eq_closedBall_diff]
    simp [c, r, ρ, Set.ext_iff, Fin.exists_fin_two]
  have hvS : ∀ w ∈ Metric.closedBall 0 r \ ⋃ i, Metric.ball (c i) ρ, ContDiffAt ℝ 2 v w := by
    intro w hw
    rw [← htrunc] at hw
    exact hv ⟨(mem_truncation.1 hw).1, (mem_truncation.1 hw).2.1⟩
  have hstokes := ω.integral_fderiv_apply_closedBall_diff_iUnion_ball (by positivity)
    (fun _ ↦ hρ) hsub hdisj hvS
  -- The boundary circles are the loops of the three ends.
  have hloop (c₀ : ℂ) (s θ₀ : ℝ) := ω.loopArea_comp_sub_two_pi_mul
    (γ := fun θ ↦ v (circleMap c₀ s θ)) ((periodic_circleMap c₀ s).comp v) θ₀
  have hx₀ : (fun t : ℝ ↦ u (e (zero.cylindricalEndLift (↑(zero.endSign * R) + ↑t * Complex.I)))) =
      fun t ↦ v (circleMap 0 ρ (0 - 2 * π * t)) := by
    funext t
    rw [cylindricalEndLift_zero_endSign_mul_add, hv_def, comp_apply, zero_sub]
  have hx₁ : (fun t : ℝ ↦ u (e (one.cylindricalEndLift (↑(one.endSign * R) + ↑t * Complex.I)))) =
      fun t ↦ v (circleMap 1 ρ (π - 2 * π * t)) := by
    funext t
    rw [cylindricalEndLift_one_endSign_mul_add, hv_def, comp_apply]
  have hx_inf : (fun t : ℝ ↦ u (e (inf.cylindricalEndLift (↑(inf.endSign * R) + ↑t * Complex.I)))) =
      fun t ↦ v (circleMap 0 r (0 - 2 * π * t)) := by
    funext t
    rw [cylindricalEndLift_inf_endSign_mul_add, hv_def, comp_apply, zero_sub]
  rw [hchange, htrunc, hstokes, Fin.sum_univ_two, Puncture.sum_univ, hx₀, hx₁,
    hx_inf, hloop, hloop, hloop]
  simp only [c, Matrix.cons_val_zero, Matrix.cons_val_one, endSign_zero, endSign_one, endSign_inf]
  ring

variable [FiniteDimensional ℝ V] {H : Puncture → ℝ → V → ℝ}

/-- **The energy identity on the truncated pair of pants, in action form.** Let `K` be the
pair-of-pants perturbation of period-one `C¹` Hamiltonians `H_q` on the three ends of
`S = ℂ ∖ {0, 1}`, and let `u` be `C²` on `S`. For `R ≥ 2` the Floer energy of `u` over the
truncation `S_R` is the signed sum of the actions of its loops `x_q^R(t) = u(φ_q(±R + i t))`,
minus the integrated curvature:

`∫_{S_R} E = A_{H_0}(x_0^R) + A_{H_1}(x_1^R) - A_{H_∞}(x_∞^R) - ∫_{S_R} R_K(u)`. -/
theorem integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_sum_sub
    (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {R : ℝ} (hR : 2 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∑ q : Puncture, q.endSign * ω.hamiltonianAction (H q) (fun t ↦ u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  rw [ω.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation hH hHs (hu.of_le one_le_two)
    (by linarith), smoothTransition.one_of_one_le (by linarith), one_mul,
    ω.integral_symplecticForm_fderiv_truncation_eq_sum_loopArea hu (by linarith)]
  simp only [hamiltonianAction_def, mul_add, Finset.sum_add_distrib]

/-- **The action bound on the truncated pair of pants.** If the end Hamiltonians are bounded,
`|H_q| ≤ B_q`, then for every `R ≥ 2` the Floer energy over the truncation `S_R` differs from the
signed sum `A_{H_0}(x_0^R) + A_{H_1}(x_1^R) - A_{H_∞}(x_∞^R)` of the actions of the boundary loops
by at most `B₀ + B₁ + B_∞`, uniformly in `R`. -/
theorem abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_sum_le
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {R : ℝ} (hR : 2 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      ∑ q : Puncture, q.endSign * ω.hamiltonianAction (H q) (fun t ↦ u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))| ≤ ∑ q, B q := by
  have h := ω.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_le hH hHs hB
    (hu.of_le one_le_two) (by linarith : (1 : ℝ) ≤ R)
  rw [smoothTransition.one_of_one_le (by linarith), one_mul,
    ω.integral_symplecticForm_fderiv_truncation_eq_sum_loopArea hu (by linarith)] at h
  simp only [hamiltonianAction_def, mul_add, Finset.sum_add_distrib]
  convert h using 2
  ring

/-- **The output action of a Floer pair of pants is bounded by its input actions.** Let `u` be
`C²` on `S = ℂ ∖ {0, 1}` and solve the Floer equation `(du - X_K)^{0,1} = 0` on the truncation
`S_R`, `R ≥ 2`, for the pair-of-pants perturbation `K` of Hamiltonians bounded by `|H_q| ≤ B_q`
and almost complex structures `J z` tamed by `ω`. Since the energy is nonnegative, the action of
its loop at the output end is at most the sum of the actions of its loops at the input ends, up to
the curvature constant:

`A_{H_∞}(x_∞^R) ≤ A_{H_0}(x_0^R) + A_{H_1}(x_1^R) + B₀ + B₁ + B_∞`. -/
theorem hamiltonianAction_inf_le_of_isComplexLinearMap (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {R : ℝ} (hR : 2 ≤ R) {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.Tames (J z))
    (hfloer : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V)) :
    ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
        (inf.cylindricalEndLift (↑(inf.endSign * R) + ↑t * Complex.I)))) ≤
      ω.hamiltonianAction (H zero) (fun t ↦ u (Complex.equivRealProdCLM
          (zero.cylindricalEndLift (↑(zero.endSign * R) + ↑t * Complex.I)))) +
        ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
          (one.cylindricalEndLift (↑(one.endSign * R) + ↑t * Complex.I)))) + ∑ q, B q := by
  have hT : MeasurableSet (Complex.equivRealProdCLM.symm ⁻¹' truncation R) :=
    (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
      (isCompact_truncation R)).isClosed.measurableSet
  have hE := setIntegral_nonneg (μ := volume) hT fun z hz ↦
    ω.floerEnergyDensity_nonneg (hJ z hz) (hfloer z hz)
  have h := (abs_le.1
    (ω.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_sum_le
      hH hHs hB hu hR)).2
  rw [Puncture.sum_univ] at h
  simp only [endSign_zero, endSign_one, endSign_inf] at h ⊢
  linarith

end SymplecticForm

end TauCeti
