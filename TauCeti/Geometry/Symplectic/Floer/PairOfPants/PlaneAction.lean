/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Action
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Capping
import TauCeti.Geometry.Symplectic.Area.PuncturedDisc
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The energy of a negative PSS plane in terms of the action of its end

Let `K` be the perturbation `TauCeti.Floer.negativePlanePerturbation H` of the negative PSS plane
with period-one output Hamiltonian `H`, on a symplectic vector space `(V, ω)`. It vanishes on the
pole disc and is `H(t) dt` on the part `-s ≥ 2` of the end at `∞`, whose end lift is
`φ(z) = 2 exp (-2πz)`. For a map `u` which is `C²` on the plane, write `ℓ_R(t) = u(φ(-R + i t))`
for its loop along the circle `-s = R` of the end; this circle bounds the disc
`D_R = {‖w‖ ≤ 2 exp (2πR)}`. This file rewrites the energy identity of the negative plane on
discs (`SymplecticForm.integral_floerEnergyDensity_negativePlanePerturbation_closedBall`) with the
Hamiltonian action `A_H(x) = a(x) + ∫₀¹ H(t, x(t)) dt`
(`TauCeti.SymplecticForm.hamiltonianAction`): for `R ≥ 2`,

`∫_{D_R} E = -A_H(ℓ_R) - ∫_ℂ R_K(u)`

(`integral_floerEnergyDensity_negativePlanePerturbation_closedBall_eq_neg_hamiltonianAction`). The
symplectic area of `u` over `D_R` is minus the loop area of `ℓ_R`, by Stokes' formula on a disc
(`SymplecticForm.integral_symplecticForm_fderiv_closedBall_eq_neg_loopArea`): the end coordinate
`t` runs clockwise around the circle. The curvature integral over `D_R` is the curvature integral
over the whole plane, because the curvature vanishes on the part `-s > 2` of the end.

For a solution of the Floer equation `(du - X_K)^{0,1} = 0` with almost complex structures tamed
by `ω` the energy density is nonnegative, so if `|H| ≤ B` the action of every end loop satisfies
`A_H(ℓ_R) ≤ B` for `R ≥ 2` (`SymplecticForm.hamiltonianAction_le_of_negativePlanePerturbation`).
If the actions `A_H(ℓ_R)` converge to `a` as `R → ∞`, the energy of the solution over the whole
plane is

`E(u) = -a - ∫_ℂ R_K(u)`

(`SymplecticForm.lintegral_floerEnergyDensity_negativePlanePerturbation_eq`), hence at most
`B - a`, and `a ≤ B` (`SymplecticForm.le_of_tendsto_hamiltonianAction_negativePlanePerturbation`).
On a vector space target the plane itself is the cap of its output orbit, so these are the action
and energy bounds of the negative planes counted by the Piunikhin–Salamon–Schwarz map: the outputs
of such planes have action at most `B`, and the energy of a plane with output action `a` is at
most `B - a`.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  energy of the perturbed planes of the PSS maps.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity for Hamiltonian perturbations.
-/

public section

open Set Real Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : ℝ → V → ℝ}

/-- The discs of the negative plane, in real coordinates, are measurable. -/
private theorem measurableSet_preimage_closedBall (R : ℝ) :
    MeasurableSet (Complex.equivRealProdCLM.symm ⁻¹'
      Metric.closedBall 0 (2 * Real.exp (2 * π * R))) :=
  (Metric.isClosed_closedBall.preimage Complex.equivRealProdCLM.symm.continuous).measurableSet

/-- **Stokes' formula on the discs of the negative plane.** For a `C²` map `u`, the symplectic
area of `u` over the disc `‖w‖ ≤ 2 exp (2πR)` bounded by the circle `-s = R` of the end at `∞` is
minus the loop area of the loop `t ↦ u(φ(-R + i t))`, where `φ(z) = 2 exp (-2πz)` is the end
lift: the end coordinate `t` runs clockwise around the circle. -/
theorem integral_symplecticForm_fderiv_closedBall_eq_neg_loopArea (ω : SymplecticForm V)
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 2 u) (R : ℝ) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (2 * Real.exp (2 * π * R)),
        ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) =
      -ω.loopArea
        (fun t ↦ u (Complex.equivRealProdCLM (inf.cylindricalEndLift (-R + t * Complex.I)))) := by
  set b := 2 * Real.exp (2 * π * R)
  set v : ℂ → V := u ∘ Complex.equivRealProdCLM
  -- Stokes' formula for `v` on the disc of radius `b` in `ℂ`.
  have h := ω.integral_fderiv_apply_closedBall (u := v) (b := b) 0
    (mul_pos two_pos (Real.exp_pos _)) fun z _ ↦
      (hu.comp Complex.equivRealProdCLM.contDiff).contDiffAt
  have h₁ : Complex.equivRealProdCLM 1 = stdComplexLineReal := by
    rw [← equivRealProdCLM_symm_stdComplexLineReal, ContinuousLinearEquiv.apply_symm_apply]
  have hI : Complex.equivRealProdCLM Complex.I = stdComplexLineImag := by
    rw [← equivRealProdCLM_symm_stdComplexLineImag, ContinuousLinearEquiv.apply_symm_apply]
  simp only [v, ContinuousLinearEquiv.comp_right_fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, h₁, hI] at h
  -- The boundary loop is the circle traversed backwards.
  have hg : Periodic (fun θ ↦ v (circleMap 0 b θ)) (2 * π) := fun θ ↦ by
    simp only [periodic_circleMap 0 b θ]
  have hloop := ω.loopArea_comp_sub_mul hg 0
  simp only [v, Function.comp_apply] at hloop
  have hℓ : (fun t : ℝ ↦ u (Complex.equivRealProdCLM (inf.cylindricalEndLift (-R + t * Complex.I))))
      = fun t ↦ u (Complex.equivRealProdCLM (circleMap 0 b (0 - 2 * π * t))) :=
    funext fun t ↦ by
      rw [← Complex.ofReal_neg, cylindricalEndLift_ofReal_add_ofReal_mul_I, endCenter_inf,
        endScale_inf, Complex.norm_two, Complex.ofNat_arg, mul_neg, neg_neg]
  -- Transport the integral to `ℂ`.
  have hpre : Complex.measurableEquivRealProd ⁻¹'
      (Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 b) = Metric.closedBall 0 b := by
    ext w
    simp [Complex.measurableEquivRealProd]
  rw [← Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding _ _, hpre, hℓ, hloop, neg_neg]
  simpa only [Complex.measurableEquivRealProd_apply, Complex.equivRealProdCLM_apply,
    Function.comp_apply] using h

/-- Far out on the end at `∞`, off the disc `‖w‖ ≤ 2 exp (2πR)` for some `R ≥ 2`, the negative
plane perturbation is cylindrical and its curvature vanishes. -/
private theorem hamiltonianCurvature_negativePlanePerturbation_eq_zero (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {R : ℝ} (hR : 2 ≤ R) {z : ℝ × ℝ}
    (hz : z ∉ Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (2 * Real.exp (2 * π * R)))
    (x : V) :
    ω.hamiltonianCurvature
      (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z x = 0 := by
  set w := Complex.equivRealProdCLM.symm z
  have hw : 2 * Real.exp (2 * π * R) < ‖w‖ := by
    simpa only [mem_preimage, Metric.mem_closedBall, dist_zero_right, not_le] using hz
  have h₁ : 1 ≤ Real.exp (2 * π * R) := Real.one_le_exp (by positivity)
  have hw₀ : w ≠ 0 := fun h ↦ by
    rw [h, norm_zero] at hw
    linarith
  have hw₁ : w ≠ 1 := fun h ↦ by
    rw [h, norm_one] at hw
    linarith
  -- The point lies on the part `-s > 2` of the end.
  have hs : 2 < inf.endSign * (inf.endCoord w).re := by
    rw [endSign_inf, re_endCoord, endCenter_inf, endScale_inf, sub_zero, neg_one_mul, neg_div,
      neg_neg, lt_div_iff₀ (by positivity), norm_div, Complex.norm_ofNat,
      Real.lt_log_iff_exp_lt (by positivity), lt_div_iff₀ (by norm_num)]
    have : Real.exp (2 * (2 * π)) ≤ Real.exp (2 * π * R) :=
      Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
    linarith
  have hH' (q : Puncture) : Periodic ((Pi.single inf H : Puncture → ℝ → V → ℝ) q) 1 := by
    rcases eq_or_ne q inf with rfl | hq
    · simpa using hH
    · rw [Pi.single_eq_of_ne hq]
      exact fun _ ↦ rfl
  have hHs' (q : Puncture) :
      ContDiff ℝ 1 (uncurry ((Pi.single inf H : Puncture → ℝ → V → ℝ) q)) := by
    rcases eq_or_ne q inf with rfl | hq
    · simpa using hHs
    · rw [Pi.single_eq_of_ne hq]
      exact contDiff_const
  have h := ω.hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt hH' hHs'
    ⟨hw₀, hw₁⟩ hs x
  rwa [pairOfPantsPerturbation_single_inf] at h

/-- For `R ≥ 2`, the curvature integral over the disc `‖w‖ ≤ 2 exp (2πR)` is the curvature
integral over the whole plane. -/
private theorem setIntegral_closedBall_hamiltonianCurvature (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) (u : ℝ × ℝ → V) {R : ℝ} (hR : 2 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (2 * Real.exp (2 * π * R)),
        ω.hamiltonianCurvature
          (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) =
      ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦
    hamiltonianCurvature_negativePlanePerturbation_eq_zero ω hH hHs hR hz (u z)

/-- The integrated curvature of the negative plane perturbation is at most `B` in absolute value,
if `|H| ≤ B`. -/
private theorem abs_integral_hamiltonianCurvature_le (ω : SymplecticForm V) (hH : Periodic H 1)
    (hHs : ContDiff ℝ 1 (uncurry H)) {B : ℝ} (hB : ∀ t x, |H t x| ≤ B) (u : ℝ × ℝ → V) :
    |∫ z, ω.hamiltonianCurvature
        (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)| ≤ B := by
  rw [← ENNReal.ofReal_le_ofReal_iff ((abs_nonneg _).trans (hB 0 0)),
    ← Real.enorm_eq_ofReal_abs]
  exact (enorm_integral_le_lintegral_enorm _).trans
    (lintegral_enorm_hamiltonianCurvature_negativePlanePerturbation_le ω hH hHs hB u)

/-- **The energy identity on discs of the negative plane, in terms of the action.** Let `K` be
the negative plane perturbation of a period-one `C¹` Hamiltonian `H`, with components
`K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`, and let
`u` be a `C²` map. For `R ≥ 2`, the Floer energy of `u` over the disc `‖w‖ ≤ 2 exp (2πR)` bounded
by the circle `-s = R` of the end is minus the Hamiltonian action of the loop
`ℓ_R(t) = u(φ(-R + i t))` along that circle, minus the integrated curvature over the plane:

`∫_{D_R} E = -A_H(ℓ_R) - ∫_ℂ R_K(u)`. -/
theorem integral_floerEnergyDensity_negativePlanePerturbation_closedBall_eq_neg_hamiltonianAction
    (ω : SymplecticForm V) (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {u : ℝ × ℝ → V}
    (hu : ContDiff ℝ 2 u) {R : ℝ} (hR : 2 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (2 * Real.exp (2 * π * R)),
        ω.floerEnergyDensity
          (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
      -ω.hamiltonianAction H
          (fun t ↦ u (Complex.equivRealProdCLM (inf.cylindricalEndLift (-R + t * Complex.I)))) -
        ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  rw [integral_floerEnergyDensity_negativePlanePerturbation_closedBall ω hH hHs
      (hu.of_le one_le_two) (by linarith),
    integral_symplecticForm_fderiv_closedBall_eq_neg_loopArea ω hu,
    smoothTransition.one_of_one_le (by linarith), one_mul,
    setIntegral_closedBall_hamiltonianCurvature ω hH hHs u hR, hamiltonianAction_def]
  ring

/-- **The energy and the action on discs of the negative plane.** If `|H| ≤ B`, then for every
`R ≥ 2` the Floer energy of a `C²` map `u` over the disc `‖w‖ ≤ 2 exp (2πR)` differs from minus
the action of its boundary loop `ℓ_R` by at most `B`, uniformly in `R`. -/
theorem abs_integral_floerEnergyDensity_negativePlanePerturbation_closedBall_add_le
    (ω : SymplecticForm V) (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {B : ℝ}
    (hB : ∀ t x, |H t x| ≤ B) {u : ℝ × ℝ → V} (hu : ContDiff ℝ 2 u) {R : ℝ} (hR : 2 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (2 * Real.exp (2 * π * R)),
        ω.floerEnergyDensity
          (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z) +
      ω.hamiltonianAction H
        (fun t ↦ u (Complex.equivRealProdCLM (inf.cylindricalEndLift (-R + t * Complex.I))))| ≤
      B := by
  rw [integral_floerEnergyDensity_negativePlanePerturbation_closedBall_eq_neg_hamiltonianAction ω
      hH hHs hu hR,
    show ∀ x y : ℝ, -x - y + x = -y from fun _ _ ↦ by ring, abs_neg]
  exact abs_integral_hamiltonianCurvature_le ω hH hHs hB u

/-- **The action bound for negative planes.** Let `K` be the negative plane perturbation of a
period-one `C¹` Hamiltonian `H` with `|H| ≤ B`, and let `u` be a `C²` map which solves the Floer
equation `(du - X_K)^{0,1} = 0` on the disc `‖w‖ ≤ 2 exp (2πR)`, `R ≥ 2`, for almost complex
structures `J(z)` tamed by `ω`. Then the action of its loop `ℓ_R(t) = u(φ(-R + i t))` along the
boundary circle is at most `B`. No convergence of the actions as `R → ∞` is assumed. -/
theorem hamiltonianAction_le_of_negativePlanePerturbation (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {B : ℝ} (hB : ∀ t x, |H t x| ≤ B)
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 2 u) {R : ℝ} (hR : 2 ≤ R)
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (2 * Real.exp (2 * π * R)),
      ω.Tames (J z))
    (hfloer : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹'
        Metric.closedBall 0 (2 * Real.exp (2 * π * R)),
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V)) :
    ω.hamiltonianAction H
        (fun t ↦ u (Complex.equivRealProdCLM (inf.cylindricalEndLift (-R + t * Complex.I)))) ≤
      B := by
  -- The energy over the disc is nonnegative.
  have hE := setIntegral_nonneg (μ := volume) (measurableSet_preimage_closedBall R) fun z hz ↦
    ω.floerEnergyDensity_nonneg (hJ z hz) (hfloer z hz)
  have h := (abs_le.1
    (abs_integral_floerEnergyDensity_negativePlanePerturbation_closedBall_add_le ω hH hHs hB hu
      hR)).2
  linarith

/-- **The energy of a negative plane.** Let `K` be the negative plane perturbation of a
period-one `C¹` Hamiltonian `H`, and let `u` be a `C²` map which solves the Floer equation
`(du - X_K)^{0,1} = 0` on the plane for almost complex structures `J(z)` tamed by `ω`. If the
actions of the loops `ℓ_R(t) = u(φ(-R + i t))` along the circles `-s = R` of the end converge to
`a` as `R → ∞`, then the energy of `u` is

`E(u) = -a - ∫_ℂ R_K(u)`. -/
theorem lintegral_floerEnergyDensity_negativePlanePerturbation_eq (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {u : ℝ × ℝ → V} (hu : ContDiff ℝ 2 u)
    {J : ℝ × ℝ → AlmostComplexStructure V} (hJ : ∀ z, ω.Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv
        (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    {a : ℝ} (ha : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction H
      (fun t ↦ u (Complex.equivRealProdCLM (inf.cylindricalEndLift (-R + t * Complex.I)))))
      atTop (𝓝 a)) :
    ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) =
      ENNReal.ofReal (-a - ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)) := by
  -- Exhaust the plane by the discs `D_(n+2)`.
  set T : ℕ → Set (ℝ × ℝ) := fun n ↦
    Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (2 * Real.exp (2 * π * (n + 2)))
  have hmono : Monotone T := fun m n hmn ↦ preimage_mono (Metric.closedBall_subset_closedBall
    (by gcongr))
  have hunion : ⋃ n, T n = univ := by
    refine eq_univ_of_forall fun z ↦ mem_iUnion.2 ?_
    obtain ⟨n, hn⟩ := exists_nat_ge ‖Complex.equivRealProdCLM.symm z‖
    refine ⟨n, ?_⟩
    have h := Real.add_one_le_exp (2 * π * (n + 2))
    simp only [T, mem_preimage, Metric.mem_closedBall, dist_zero_right]
    nlinarith [Real.two_le_pi, n.cast_nonneg (α := ℝ)]
  -- The energy density is continuous, hence integrable on each disc.
  have hcont : Continuous (ω.floerEnergyDensity
      (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u) :=
    continuousOn_univ.1 (ω.continuousOn_floerEnergyDensity isOpen_univ
      (hu.of_le one_le_two).contDiffOn
      (by simpa using (contDiff_negativePlanePerturbation_apply hH hHs 1).contDiffOn)
      (by simpa using (contDiff_negativePlanePerturbation_apply hH hHs Complex.I).contDiffOn))
  have hE (n : ℕ) : ∫⁻ z in T n, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      u z) = ENNReal.ofReal (∫ z in T n, ω.floerEnergyDensity
      (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      u z) :=
    (ofReal_integral_eq_lintegral_ofReal
      (hcont.continuousOn.integrableOn_compact
        (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
          (isCompact_closedBall _ _)))
      (ae_restrict_of_forall_mem (measurableSet_preimage_closedBall _) fun z _ ↦
        ω.floerEnergyDensity_nonneg (hJ z) (hfloer z))).symm
  have hlim : Tendsto (fun n ↦ ∫⁻ z in T n, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      u z)) atTop (𝓝 (∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z))) := by
    rw [← setLIntegral_univ, ← hunion, setLIntegral_iUnion_of_directed _ hmono.directed_le]
    exact tendsto_atTop_iSup fun m n hmn ↦
      lintegral_mono' (Measure.restrict_mono (hmono hmn) le_rfl) le_rfl
  refine tendsto_nhds_unique hlim ?_
  simp only [hE]
  have hn : Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  refine (ENNReal.continuous_ofReal.tendsto _).comp
    (((ha.comp hn).neg.sub_const _).congr fun n ↦ ?_)
  exact (integral_floerEnergyDensity_negativePlanePerturbation_closedBall_eq_neg_hamiltonianAction ω
    hH hHs hu (R := n + 2) (by linarith [n.cast_nonneg (α := ℝ)])).symm

/-- **The energy bound for a negative plane.** Under the hypotheses of
`SymplecticForm.lintegral_floerEnergyDensity_negativePlanePerturbation_eq`, if moreover
`|H| ≤ B`, then the energy of `u` is at most `B - a`. -/
theorem lintegral_floerEnergyDensity_negativePlanePerturbation_le (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {B : ℝ} (hB : ∀ t x, |H t x| ≤ B)
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 2 u)
    {J : ℝ × ℝ → AlmostComplexStructure V} (hJ : ∀ z, ω.Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv
        (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    {a : ℝ} (ha : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction H
      (fun t ↦ u (Complex.equivRealProdCLM (inf.cylindricalEndLift (-R + t * Complex.I)))))
      atTop (𝓝 a)) :
    ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≤ ENNReal.ofReal (B - a) := by
  rw [lintegral_floerEnergyDensity_negativePlanePerturbation_eq ω hH hHs hu hJ hfloer ha]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith [neg_abs_le (∫ z, ω.hamiltonianCurvature
      (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z)), abs_integral_hamiltonianCurvature_le ω hH hHs hB u]

/-- **The output action bound for a negative plane.** Let `K` be the negative plane perturbation
of a period-one `C¹` Hamiltonian `H` with `|H| ≤ B`, and let `u` be a `C²` solution of the Floer
equation `(du - X_K)^{0,1} = 0` on the plane for almost complex structures tamed by `ω`. If the
actions of its end loops `ℓ_R` converge to `a` as `R → ∞`, then `a ≤ B`. This is the limit of
`SymplecticForm.hamiltonianAction_le_of_negativePlanePerturbation`. -/
theorem le_of_tendsto_hamiltonianAction_negativePlanePerturbation (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {B : ℝ} (hB : ∀ t x, |H t x| ≤ B)
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 2 u)
    {J : ℝ × ℝ → AlmostComplexStructure V} (hJ : ∀ z, ω.Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv
        (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    {a : ℝ} (ha : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction H
      (fun t ↦ u (Complex.equivRealProdCLM (inf.cylindricalEndLift (-R + t * Complex.I)))))
      atTop (𝓝 a)) :
    a ≤ B :=
  le_of_tendsto ha <| eventually_atTop.2 ⟨2, fun _ hR ↦
    hamiltonianAction_le_of_negativePlanePerturbation ω hH hHs hB hu hR (fun z _ ↦ hJ z)
      fun z _ ↦ hfloer z⟩

end TauCeti.SymplecticForm
