/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds
import TauCeti.Analysis.Calculus.ContDiff.Cutoff
import TauCeti.Analysis.Complex.RealChart
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Symplectic.Floer.Pullback
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

/-!
# The energy identity on spheres with moving input ends

The associativity of the pair-of-pants product compares the two ways of composing two products
through a family of four-punctured spheres, on which the inputs sit at moving punctures of `ℂ` and
the output at `∞`. The perturbation datum of such a sphere is
`K = TauCeti.Floer.puncturedSpherePerturbation c a H Hout`: near the input `i` it is the input end
datum with center `c i` and scale `a i`, whose end lift is `z ↦ c i + a i φ₀(z)` for the end lift
`φ₀(z) = exp (-2πz) / 2` of the input end at `0` of the pair of pants, and near `∞` it is the
negative plane datum of `Hout`. Its integrated curvature is bounded uniformly in the configuration
(`TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_puncturedSpherePerturbation_le`).
This file proves the energy identity of such a sphere, for a symplectic vector space target
`(V, ω)`.

The *truncation* `TauCeti.Floer.puncturedSphereTruncation c a R` at height `R` is the closed disc
`‖w‖ ≤ 2 exp (2πR)` with the open discs `‖w - c i‖ < ‖a i‖ exp (-2πR) / 2` removed. Its boundary
circles are the circles `s = R` of the input ends and the circle `s = -R` of the output end. For
the input ends of the pair of pants it is the truncation `S_R` of the pair of pants
(`TauCeti.Floer.puncturedSphereTruncation_pairOfPants`). Suppose that the discs
`‖w - c i‖ < ‖a i‖ / 2` are pairwise disjoint and lie in the disc `‖w‖ ≤ 2 exp (2π)`, the hypotheses
under which the input end data do not interact. For a map `u` which is `C¹` on `ℂ ∖ {c i}` and
`R ≥ 2`,

`∫ E = ∫ u^*ω + ∑ i, ∫₀¹ H i(t, ℓ_i(t)) dt - ∫₀¹ Hout(t, ℓ_∞(t)) dt - ∫ R_K(u)`

over the truncation
(`TauCeti.SymplecticForm.integral_floerEnergyDensity_puncturedSpherePerturbation_truncation`), with
the boundary loops `ℓ_i(t) = u(c i + a i φ₀(R + i t))` and `ℓ_∞(t) = u(φ_∞(-R + i t))`. With the
curvature bound, the energy therefore differs from the symplectic area plus the Hamiltonian
boundary terms by at most `∑ i, B i + Bout` when `|H i| ≤ B i` and `|Hout| ≤ Bout`, uniformly in
the height and in the configuration of the input ends
(`SymplecticForm.abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le`).
This is the energy identity `E = ∫ u^*ω + ∫_∂ K(u) - ∫ R_K` in the form that does not use
exactness of `ω`. Turning the area into the loop areas of the boundary circles needs Stokes'
formula on a disc with several holes, which is not treated here.

The proof treats the ends one at a time. By the pointwise energy identity, the energy minus the
area plus the curvature is the integral of the exterior derivative of the pulled-back one-form
`K(u)`, which is additive in the datum. The datum of the input `i` vanishes off the annulus between
its circles `s = 1` and `s = R`, so only that annulus contributes to it. Along `w ↦ c i + a i w`
the datum pulls back to the positive plane datum, a pair-of-pants datum with a single input
Hamiltonian, and the energy identity of the truncated pair of pants
(`SymplecticForm.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation`) computes the
contribution, after cutting the map off away from the other centers. The output end is treated in
the same way, without a change of coordinates.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the associativity of the pair-of-pants product and its energy estimates.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Sections 8 and 9, on
  perturbation data over families of punctured surfaces and their energy.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity for Hamiltonian perturbations.
-/

public section

open Set Real Function MeasureTheory Filter Metric TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology Manifold
open TauCeti.Complex (realChart realChart_apply contDiff_realChart)

namespace TauCeti.Floer

variable {ι : Type*}

/-- The **truncation** of the sphere with input ends of centers `c i` and scales `a i` at height
`R`: the closed disc `‖w‖ ≤ 2 exp (2πR)`, bounded by the circle `s = -R` of the output end at `∞`,
with the open discs `‖w - c i‖ < ‖a i‖ exp (-2πR) / 2` removed, which are bounded by the circles
`s = R` of the input ends. -/
noncomputable def puncturedSphereTruncation (c a : ι → ℂ) (R : ℝ) : Set ℂ :=
  closedBall 0 (2 * Real.exp (2 * π * R)) \
    ⋃ i, ball (c i) (‖a i‖ * Real.exp (-(2 * π * R)) / 2)

@[simp]
theorem mem_puncturedSphereTruncation {c a : ι → ℂ} {R : ℝ} {w : ℂ} :
    w ∈ puncturedSphereTruncation c a R ↔
      ‖w‖ ≤ 2 * Real.exp (2 * π * R) ∧
        ∀ i, ‖a i‖ * Real.exp (-(2 * π * R)) / 2 ≤ ‖w - c i‖ := by
  simp [puncturedSphereTruncation, dist_eq_norm]

theorem isCompact_puncturedSphereTruncation (c a : ι → ℂ) (R : ℝ) :
    IsCompact (puncturedSphereTruncation c a R) :=
  (isCompact_closedBall _ _).diff (isOpen_iUnion fun _ ↦ isOpen_ball)

/-- For the input ends of the pair of pants, with centers `0` and `1` and scales `1` and `-1`, the
truncation is the truncation `S_R` of the pair of pants. -/
theorem puncturedSphereTruncation_pairOfPants (R : ℝ) :
    puncturedSphereTruncation ![(0 : ℂ), 1] ![1, -1] R = truncation R := by
  ext w
  rw [mem_puncturedSphereTruncation, truncation_eq]
  simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    norm_one, norm_neg, one_mul, sub_zero, mem_inter_iff, mem_ofPred_eq, mem_closedBall,
    dist_zero_right]
  tauto

end TauCeti.Floer

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### The boundary term of a perturbation datum

For a datum `P` on a domain `D`, the Floer energy minus the symplectic area plus the integrated
curvature is the integral over `D` of the exterior derivative `∂_s (K_t(u)) - ∂_t (K_s(u))` of the
pulled-back one-form `K(u)`. It is additive in the datum and only sees the datum where it is
nonzero, which lets the ends of a sphere with moving input ends be treated one at a time. -/

/-- The exterior derivative `∂_s (K_t(u)) - ∂_t (K_s(u))` of the pulled-back one-form of `P`. -/
private noncomputable def boundaryDensity (P : ℂ → V → ℂ →L[ℝ] ℝ) (u : ℝ × ℝ → V)
    (z : ℝ × ℝ) : ℝ :=
  fderiv ℝ (fun w ↦ P (Complex.equivRealProdCLM.symm w) (u w) Complex.I) z stdComplexLineReal -
    fderiv ℝ (fun w ↦ P (Complex.equivRealProdCLM.symm w) (u w) 1) z stdComplexLineImag

variable {P : ℂ → V → ℂ →L[ℝ] ℝ} {u : ℝ × ℝ → V} {U D T : Set (ℝ × ℝ)}

private theorem contDiffOn_comp_graph (hu : ContDiffOn ℝ 1 u U) (v : ℂ)
    (hP : ContDiffOn ℝ 1 (uncurry fun z x ↦ P (Complex.equivRealProdCLM.symm z) x v)
      (U ×ˢ univ)) :
    ContDiffOn ℝ 1 (fun w ↦ P (Complex.equivRealProdCLM.symm w) (u w) v) U :=
  hP.comp (contDiffOn_id.prodMk hu) fun _ hz ↦ ⟨hz, mem_univ _⟩

private theorem continuousOn_boundaryDensity (hU : IsOpen U) (hu : ContDiffOn ℝ 1 u U)
    (hP : ∀ v, ContDiffOn ℝ 1 (uncurry fun z x ↦ P (Complex.equivRealProdCLM.symm z) x v)
      (U ×ˢ univ)) :
    ContinuousOn (boundaryDensity P u) U :=
  (((contDiffOn_comp_graph hu _ (hP Complex.I)).continuousOn_fderiv_of_isOpen hU
      le_rfl).clm_apply continuousOn_const).sub
    (((contDiffOn_comp_graph hu _ (hP 1)).continuousOn_fderiv_of_isOpen hU
      le_rfl).clm_apply continuousOn_const)

/-- A datum which is `C¹` in the domain and target points at the points of `U` is `C¹` in the real
coordinates of the domain. -/
private theorem contDiffOn_uncurry_of_contDiffAt
    (h : ∀ z ∈ U, ∀ x, ContDiffAt ℝ 1 (fun p : ℂ × V ↦ P p.1 p.2)
      (Complex.equivRealProdCLM.symm z, x)) (v : ℂ) :
    ContDiffOn ℝ 1 (uncurry fun z x ↦ P (Complex.equivRealProdCLM.symm z) x v) (U ×ˢ univ) := by
  rintro ⟨z, x⟩ ⟨hz, -⟩
  exact (((h z hz x).comp (z, x) ((Complex.equivRealProdCLM.symm.contDiff.comp
    contDiff_fst).prodMk contDiff_snd).contDiffAt).clm_apply contDiffAt_const).contDiffWithinAt

/-- In real coordinates, a map of the plane carries the preimage of a set to the preimage of its
image. -/
private theorem preimage_image_eq_image_realChart (f : ℂ → ℂ) (A : Set ℂ) :
    Complex.equivRealProdCLM.symm ⁻¹' (f '' A) =
      realChart f '' (Complex.equivRealProdCLM.symm ⁻¹' A) := by
  ext z
  constructor
  · rintro ⟨w, hw, hwz⟩
    refine ⟨Complex.equivRealProdCLM w,
      by rwa [mem_preimage, ContinuousLinearEquiv.symm_apply_apply], ?_⟩
    rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply, hwz,
      ContinuousLinearEquiv.apply_symm_apply]
  · rintro ⟨w, hw, rfl⟩
    exact ⟨_, hw, by rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply]⟩

/-- The image of an annulus about `0` under `w ↦ c + a w` is the annulus about `c` scaled by
`‖a‖`. -/
private theorem mem_image_affine_iff {c a w : ℂ} (ha : a ≠ 0) {r ρ : ℝ} :
    w ∈ (fun w ↦ c + a * w) '' {w : ℂ | r ≤ ‖w‖ ∧ ‖w‖ ≤ ρ} ↔
      ‖a‖ * r ≤ ‖w - c‖ ∧ ‖w - c‖ ≤ ‖a‖ * ρ := by
  have ha' : 0 < ‖a‖ := norm_pos_iff.2 ha
  constructor
  · rintro ⟨w', ⟨h₁, h₂⟩, rfl⟩
    rw [add_sub_cancel_left, norm_mul]
    exact ⟨by gcongr, by gcongr⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨(w - c) / a, ⟨?_, ?_⟩, by field_simp; ring⟩
    · rw [norm_div, le_div_iff₀ ha']
      linarith
    · rw [norm_div, div_le_iff₀ ha']
      linarith

variable [FiniteDimensional ℝ V]

/-- The Floer energy minus the symplectic area plus the integrated curvature over `D`, for the
datum `P` written in the real coordinates of `ℂ`. -/
private noncomputable def energyDefect (ω : SymplecticForm V) (P : ℂ → V → ℂ →L[ℝ] ℝ)
    (u : ℝ × ℝ → V) (D : Set (ℝ × ℝ)) : ℝ :=
  (∫ z in D, ω.floerEnergyDensity (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x Complex.I) u z) -
    (∫ z in D, ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) +
    ∫ z in D, ω.hamiltonianCurvature (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)

/-- The energy defect over a compact set is the integral of the boundary density. -/
private theorem energyDefect_eq_integral (ω : SymplecticForm V) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 1 u U)
    (hP : ∀ v, ContDiffOn ℝ 1 (uncurry fun z x ↦ P (Complex.equivRealProdCLM.symm z) x v)
      (U ×ˢ univ)) (hD : IsCompact D) (hDU : D ⊆ U) :
    energyDefect ω P u D = ∫ z in D, boundaryDensity P u z := by
  have hint (f : ℝ × ℝ → ℝ) (hf : ContinuousOn f U) : IntegrableOn f D :=
    (hf.mono hDU).integrableOn_compact hD
  have hdu := hu.continuousOn_fderiv_of_isOpen hU le_rfl
  have hE := hint _ (ω.continuousOn_floerEnergyDensity hU hu (hP 1) (hP Complex.I))
  have harea := hint (fun z ↦ ω (fderiv ℝ u z stdComplexLineReal)
    (fderiv ℝ u z stdComplexLineImag)) (ω.continuousOn_apply_comp
      (hdu.clm_apply continuousOn_const) (hdu.clm_apply continuousOn_const))
  have hcurv := hint _
    (ω.continuousOn_hamiltonianCurvature_comp hU hu.continuousOn (hP 1) (hP Complex.I))
  have e₁ := integral_sub hE harea
  have e₂ := integral_add (hE.sub harea) hcurv
  simp only [Pi.sub_apply] at e₂
  rw [energyDefect, ← e₁, ← e₂]
  refine setIntegral_congr_fun hD.measurableSet fun z hz ↦ ?_
  have hmem : (z, u z) ∈ U ×ˢ (univ : Set V) := ⟨hDU hz, mem_univ _⟩
  have hdiff (v : ℂ) := ((hP v).differentiableOn one_ne_zero _ hmem).differentiableAt
    ((hU.prod isOpen_univ).mem_nhds hmem)
  rw [ω.floerEnergyDensity_eq ((hu.differentiableOn one_ne_zero z (hDU hz)).differentiableAt
    (hU.mem_nhds (hDU hz))) (hdiff 1) (hdiff Complex.I), boundaryDensity]
  ring

/-- **The energy defect is additive in the datum.** -/
private theorem energyDefect_sum (ω : SymplecticForm V) {κ : Type*} [Fintype κ]
    {P : κ → ℂ → V → ℂ →L[ℝ] ℝ} (hU : IsOpen U) (hu : ContDiffOn ℝ 1 u U)
    (hP : ∀ k v, ContDiffOn ℝ 1 (uncurry fun z x ↦ P k (Complex.equivRealProdCLM.symm z) x v)
      (U ×ˢ univ)) (hD : IsCompact D) (hDU : D ⊆ U) :
    energyDefect ω (fun w x ↦ ∑ k, P k w x) u D = ∑ k, energyDefect ω (P k) u D := by
  have hsum (v : ℂ) : ContDiffOn ℝ 1
      (uncurry fun z x ↦ (∑ k, P k (Complex.equivRealProdCLM.symm z) x) v) (U ×ˢ univ) := by
    have h : (uncurry fun z x ↦ (∑ k, P k (Complex.equivRealProdCLM.symm z) x) v) =
        fun p ↦ ∑ k, uncurry (fun z x ↦ P k (Complex.equivRealProdCLM.symm z) x v) p := by
      funext p
      simp [uncurry]
    rw [h]
    exact ContDiffOn.sum fun k _ ↦ hP k v
  rw [energyDefect_eq_integral ω hU hu hsum hD hDU]
  simp_rw [energyDefect_eq_integral ω hU hu (hP _) hD hDU]
  rw [← integral_finsetSum _ fun k _ ↦
    ((continuousOn_boundaryDensity hU hu (hP k)).mono hDU).integrableOn_compact hD]
  refine setIntegral_congr_fun hD.measurableSet fun z hz ↦ ?_
  have hdiff (k : κ) (v : ℂ) : DifferentiableAt ℝ
      (fun w ↦ P k (Complex.equivRealProdCLM.symm w) (u w) v) z :=
    ((contDiffOn_comp_graph hu v (hP k v)).differentiableOn one_ne_zero z
      (hDU hz)).differentiableAt (hU.mem_nhds (hDU hz))
  have hfun (v : ℂ) : (fun w ↦ (∑ k, P k (Complex.equivRealProdCLM.symm w) (u w)) v) =
      fun w ↦ ∑ k, P k (Complex.equivRealProdCLM.symm w) (u w) v := by
    funext w
    simp
  simp only [boundaryDensity, hfun]
  rw [fderiv_fun_sum fun k _ ↦ hdiff k Complex.I, fderiv_fun_sum fun k _ ↦ hdiff k 1]
  simp [Finset.sum_sub_distrib]

/-- **The energy defect only sees the datum where it is nonzero.** If `P` vanishes near every
point of `D \ T`, the energy defect over `D` is the energy defect over `T`. -/
private theorem energyDefect_eq_of_subset (ω : SymplecticForm V) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 1 u U)
    (hP : ∀ v, ContDiffOn ℝ 1 (uncurry fun z x ↦ P (Complex.equivRealProdCLM.symm z) x v)
      (U ×ˢ univ)) (hD : IsCompact D) (hDU : D ⊆ U) (hTD : T ⊆ D)
    (hPD : ∀ z ∈ D \ T, ∀ᶠ z' in 𝓝 z, P (Complex.equivRealProdCLM.symm z') = fun _ ↦ 0) :
    energyDefect ω P u D = energyDefect ω P u T :=
  ω.integral_floerEnergyDensity_sub_add_eq_of_eventuallyEq_zero hU hu (hP 1) (hP Complex.I) hD
    hDU hTD (fun z hz ↦ (hPD z hz).mono fun z' h ↦ by funext x; simp [h])
    (fun z hz ↦ (hPD z hz).mono fun z' h ↦ by funext x; simp [h])

/-- **The energy defect only sees the map near the domain.** -/
private theorem energyDefect_congr (ω : SymplecticForm V) {u' : ℝ × ℝ → V}
    (hD : MeasurableSet D) (h : ∀ z ∈ D, u' =ᶠ[𝓝 z] u) :
    energyDefect ω P u' D = energyDefect ω P u D := by
  rw [energyDefect, energyDefect]
  congr 1
  · congr 1
    · exact setIntegral_congr_fun hD fun z hz ↦
        ω.floerEnergyDensity_congr_of_eventuallyEq _ _ (h z hz)
    · exact setIntegral_congr_fun hD fun z hz ↦ by simp only [(h z hz).fderiv_eq]
  · exact setIntegral_congr_fun hD fun z hz ↦ by simp only [(h z hz).eq_of_nhds]

/-! ### The energy defect of the plane data on annuli -/

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
private theorem exp_neg_two_pi_lt_half : Real.exp (-(2 * π)) < 1 / 2 := by
  have h₁ : Real.exp (-(2 * π)) * Real.exp (2 * π) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  nlinarith [Real.add_one_le_exp (2 * π), Real.two_le_pi, Real.exp_pos (-(2 * π))]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
private theorem exp_neg_two_pi_mul_le {R : ℝ} (hR : 1 ≤ R) :
    Real.exp (-(2 * π * R)) ≤ Real.exp (-(2 * π)) :=
  Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])

/-- The annulus `exp (-2πR) / 2 ≤ ‖w‖ ≤ exp (-2π) / 2` of the input end at `0` of the pair of
pants, between its circles `s = R` and `s = 1`. -/
private noncomputable def endAnnulus (R : ℝ) : Set ℂ :=
  {w | Real.exp (-(2 * π * R)) / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ Real.exp (-(2 * π)) / 2}

/-- The annulus `2 exp (2π) ≤ ‖w‖ ≤ 2 exp (2πR)` of the output end at `∞` of the pair of pants,
between its circles `s = -1` and `s = -R`. -/
private noncomputable def outerAnnulus (R : ℝ) : Set ℂ :=
  {w | 2 * Real.exp (2 * π) ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * Real.exp (2 * π * R)}

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
private theorem measurableSet_preimage_endAnnulus {R : ℝ} :
    MeasurableSet (Complex.equivRealProdCLM.symm ⁻¹' endAnnulus R) :=
  (((isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const)).preimage
      Complex.equivRealProdCLM.symm.continuous).measurableSet

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
private theorem measurableSet_preimage_outerAnnulus {R : ℝ} :
    MeasurableSet (Complex.equivRealProdCLM.symm ⁻¹' outerAnnulus R) :=
  (((isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const)).preimage
      Complex.equivRealProdCLM.symm.continuous).measurableSet

/-- The positive plane datum is the input end datum with center `0` and scale `1`. -/
private theorem positivePlanePerturbation_eq_inputEndPerturbation {M : Type*} (H : ℝ → M → ℝ) :
    positivePlanePerturbation H = inputEndPerturbation 0 1 H := by
  funext w x
  ext v
  simp [inputEndPerturbation_apply]

omit [FiniteDimensional ℝ V] in
private theorem contDiffOn_uncurry_positivePlanePerturbation {H : ℝ → V → ℝ} (hH : Periodic H 1)
    (hHs : ContDiff ℝ 1 (uncurry H)) (v : ℂ) :
    ContDiffOn ℝ 1
      (uncurry fun z x ↦ positivePlanePerturbation H (Complex.equivRealProdCLM.symm z) x v)
      (thricePuncturedSphereReal ×ˢ univ) := by
  rw [positivePlanePerturbation_eq_inputEndPerturbation]
  exact contDiffOn_uncurry_of_contDiffAt (fun z hz x ↦ contDiffAt_inputEndPerturbation_prod
    (n := 1) hH hHs one_ne_zero (mem_thricePuncturedSphereReal_iff.1 hz).1 x) v

/-- Near a point outside the closed disc `‖w‖ ≤ exp (-2π) / 2`, the positive plane datum
vanishes. -/
private theorem eventually_positivePlanePerturbation_eq_zero {M : Type*} {H : ℝ → M → ℝ}
    {z : ℝ × ℝ}
    (hz : Real.exp (-(2 * π)) / 2 < ‖Complex.equivRealProdCLM.symm z‖) :
    ∀ᶠ z' in 𝓝 z, positivePlanePerturbation H (Complex.equivRealProdCLM.symm z') = fun _ ↦ 0 := by
  have hc : Continuous fun z : ℝ × ℝ ↦ ‖Complex.equivRealProdCLM.symm z‖ := by fun_prop
  filter_upwards [hc.continuousAt.eventually (lt_mem_nhds hz)] with z' hz'
  exact funext (positivePlanePerturbation_eq_zero_of_le_norm hz'.le)

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- A period-one Hamiltonian at one end and zero at the others. -/
private theorem periodic_single {q₀ : Puncture} {G : ℝ → V → ℝ} (hG : Periodic G 1)
    (q : Puncture) : Periodic ((Pi.single q₀ G : Puncture → ℝ → V → ℝ) q) 1 := by
  rcases eq_or_ne q q₀ with rfl | h
  · simpa using hG
  · rw [Pi.single_eq_of_ne h]
    exact fun _ ↦ rfl

omit [FiniteDimensional ℝ V] in
private theorem contDiff_uncurry_single {q₀ : Puncture} {G : ℝ → V → ℝ}
    (hG : ContDiff ℝ 1 (uncurry G)) (q : Puncture) :
    ContDiff ℝ 1 (uncurry ((Pi.single q₀ G : Puncture → ℝ → V → ℝ) q)) := by
  rcases eq_or_ne q q₀ with rfl | h
  · simpa using hG
  · rw [Pi.single_eq_of_ne h]
    exact contDiff_const

/-- **The energy defect of the positive plane datum over an annulus.** For a map `v` which is `C¹`
on `S = ℂ ∖ {0, 1}` and `R ≥ 2`, the energy defect of the positive plane datum of `H` over the
annulus `endAnnulus R` is the Hamiltonian term `∫₀¹ H(t, v(φ₀(R + i t))) dt`
of its inner boundary circle. -/
private theorem energyDefect_positivePlanePerturbation_annulus (ω : SymplecticForm V)
    {H : ℝ → V → ℝ} (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {v : ℝ × ℝ → V}
    (hv : ContDiffOn ℝ 1 v thricePuncturedSphereReal) {R : ℝ} (hR : 2 ≤ R) :
    energyDefect ω (positivePlanePerturbation H) v
        (Complex.equivRealProdCLM.symm ⁻¹' endAnnulus R) =
      ∫ t in (0 : ℝ)..1, H t (v (Complex.equivRealProdCLM
        (zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) := by
  have hexp := exp_neg_two_pi_lt_half
  have hexpR := exp_neg_two_pi_mul_le (by linarith : 1 ≤ R)
  have hexp' : 1 ≤ Real.exp (2 * π * R) := Real.one_le_exp (by nlinarith [Real.pi_pos])
  have hD : IsCompact (Complex.equivRealProdCLM.symm ⁻¹' truncation R) :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_truncation R)
  -- Enlarge the annulus to the truncation `S_R`, off which the datum vanishes.
  rw [← energyDefect_eq_of_subset ω isOpen_thricePuncturedSphereReal hv
    (contDiffOn_uncurry_positivePlanePerturbation hH hHs) hD
    (preimage_truncation_subset_thricePuncturedSphereReal R) ?sub ?vanish]
  case sub =>
    intro z ⟨h₁, h₂⟩
    rw [mem_preimage, truncation_eq]
    refine ⟨⟨h₁, ?_⟩, ?_⟩
    · have := norm_sub_norm_le (1 : ℂ) (Complex.equivRealProdCLM.symm z)
      rw [norm_one, norm_sub_rev] at this
      rw [mem_ofPred_eq]
      linarith
    · rw [mem_closedBall, dist_zero_right]
      linarith
  case vanish =>
    rintro z ⟨hz, hzA⟩
    refine eventually_positivePlanePerturbation_eq_zero (not_le.1 fun h ↦ hzA ⟨?_, h⟩)
    rw [mem_preimage, truncation_eq] at hz
    exact hz.1.1
  -- The positive plane datum is the pair-of-pants datum with a single input Hamiltonian.
  have h := ω.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation
    (periodic_single (q₀ := zero) hH) (contDiff_uncurry_single hHs) hv (by linarith : 1 ≤ R)
  rw [pairOfPantsPerturbation_single_zero] at h
  rw [energyDefect, h, Fintype.sum_eq_single zero fun q hq ↦ by
    simp [Pi.single_eq_of_ne hq], smoothTransition.one_of_one_le (by linarith)]
  simp only [endSign_zero, one_mul, Pi.single_eq_same]
  ring

/-! ### Changes of coordinates along affine maps -/

private theorem hasDerivAt_affine (c a w : ℂ) : HasDerivAt (fun w ↦ c + a * w) a w := by
  simpa using ((hasDerivAt_id w).const_mul a).const_add c

private theorem det_fderiv_realChart_affine_nonneg (c a : ℂ) (w : ℝ × ℝ) :
    0 ≤ (fderiv ℝ (realChart fun w ↦ c + a * w) w).det := by
  rw [(TauCeti.Complex.hasFDerivAt_realChart (hasDerivAt_affine c a _)).fderiv]
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_apply,
    Complex.normSq_nonneg]

private theorem contDiff_realChart_affine (c a : ℂ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (realChart fun w ↦ c + a * w) :=
  contDiff_realChart (by fun_prop)

/-- The symplectic area density transforms as a two-form under orientation-preserving changes of
coordinates. -/
private theorem integral_symplecticForm_fderiv_image (ω : SymplecticForm V)
    {φ : ℝ × ℝ → ℝ × ℝ} {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hinj : InjOn φ s)
    (hφ : ∀ w ∈ s, DifferentiableAt ℝ φ w) (hdet : ∀ w ∈ s, 0 ≤ (fderiv ℝ φ w).det)
    (hu : ∀ w ∈ s, DifferentiableAt ℝ u (φ w)) :
    ∫ z in φ '' s, ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) =
      ∫ w in s, ω (fderiv ℝ (u ∘ φ) w stdComplexLineReal)
        (fderiv ℝ (u ∘ φ) w stdComplexLineImag) := by
  have h := ω.integral_floerEnergyDensity_image (Ks := fun _ _ ↦ 0) (Kt := fun _ _ ↦ 0) hs hinj
    hφ hdet hu (fun _ _ ↦ differentiableAt_const _) (fun _ _ ↦ differentiableAt_const _)
  have hpull (v : ℝ × ℝ) : perturbationPullback φ (fun _ _ ↦ (0 : ℝ)) (fun _ _ ↦ 0) v =
      fun (_ : ℝ × ℝ) (_ : V) ↦ 0 := by
    funext w x
    simp [perturbationPullback_apply]
  simpa only [hpull, floerEnergyDensity_zero] using h

/-- **The energy defect of an input end datum is that of the positive plane datum in the
coordinates of its end.** Along `g(w) = c + a w`, the input end datum with center `c` and scale `a`
pulls back to the positive plane datum. -/
private theorem energyDefect_inputEndPerturbation_image (ω : SymplecticForm V) {c a : ℂ}
    (ha : a ≠ 0) {H : ℝ → V → ℝ} (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H))
    (hU : IsOpen U) (hu : ContDiffOn ℝ 1 u U) (hUc : ∀ z ∈ U, Complex.equivRealProdCLM.symm z ≠ c)
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    (hsU : ∀ w ∈ s, realChart (fun w ↦ c + a * w) w ∈ U) :
    energyDefect ω (inputEndPerturbation c a H) u (realChart (fun w ↦ c + a * w) '' s) =
      energyDefect ω (positivePlanePerturbation H) (u ∘ realChart fun w ↦ c + a * w) s := by
  have hP := contDiffOn_uncurry_of_contDiffAt (U := U) (P := inputEndPerturbation c a H)
    fun z hz x ↦ contDiffAt_inputEndPerturbation_prod (n := 1) hH hHs ha (hUc z hz) x
  have hdiff {w : ℝ × ℝ} (hw : w ∈ s) (v : ℂ) (y : V) :=
    ((hP v).differentiableOn one_ne_zero (realChart (fun w ↦ c + a * w) w, y)
      ⟨hsU w hw, mem_univ y⟩).differentiableAt
      ((hU.prod isOpen_univ).mem_nhds ⟨hsU w hw, mem_univ y⟩)
  have hdom {w : ℝ × ℝ} (hw : w ∈ s) (v : ℂ) : DifferentiableAt ℝ
      (fun z ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z)
        (u (realChart (fun w ↦ c + a * w) w)) v) (realChart (fun w ↦ c + a * w) w) :=
    DifferentiableAt.comp (f := fun z : ℝ × ℝ ↦ (z, u (realChart (fun w ↦ c + a * w) w)))
      (realChart (fun w ↦ c + a * w) w) (hdiff hw v _)
      (differentiableAt_id.prodMk (differentiableAt_const _))
  have htgt {w : ℝ × ℝ} (hw : w ∈ s) (v : ℂ) : DifferentiableAt ℝ
      (fun x ↦ inputEndPerturbation c a H
        (Complex.equivRealProdCLM.symm (realChart (fun w ↦ c + a * w) w)) x v)
      (u (realChart (fun w ↦ c + a * w) w)) :=
    DifferentiableAt.comp (f := fun x : V ↦ (realChart (fun w ↦ c + a * w) w, x))
      (u (realChart (fun w ↦ c + a * w) w)) (hdiff hw v _)
      ((differentiableAt_const _).prodMk differentiableAt_id)
  have hinj : InjOn (realChart fun w ↦ c + a * w) s :=
    (TauCeti.Complex.realChart_injective fun w w' h ↦ by simpa [ha] using h).injOn
  have hφ (w : ℝ × ℝ) : DifferentiableAt ℝ (realChart fun w ↦ c + a * w) w :=
    (contDiff_realChart_affine c a (n := 1)).differentiable one_ne_zero w
  have hpull (v : ℝ × ℝ) : perturbationPullback (realChart fun w ↦ c + a * w)
      (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x Complex.I) v =
        fun w x ↦ positivePlanePerturbation H (Complex.equivRealProdCLM.symm w) x
          (Complex.equivRealProdCLM.symm v) := by
    funext w x
    rw [perturbationPullback_realChart _ (hasDerivAt_affine c a _), inputEndPerturbation_add_mul ha]
  have hpR := hpull stdComplexLineReal
  have hpI := hpull stdComplexLineImag
  simp only [equivRealProdCLM_symm_stdComplexLineReal] at hpR
  simp only [equivRealProdCLM_symm_stdComplexLineImag] at hpI
  rw [energyDefect, energyDefect,
    ω.integral_floerEnergyDensity_image hs hinj (fun w _ ↦ hφ w)
      (fun w _ ↦ det_fderiv_realChart_affine_nonneg c a w)
      (fun w hw ↦ (hu.differentiableOn one_ne_zero _ (hsU w hw)).differentiableAt
        (hU.mem_nhds (hsU w hw)))
      (fun w hw ↦ htgt hw 1) (fun w hw ↦ htgt hw Complex.I),
    integral_symplecticForm_fderiv_image ω hs hinj (fun w _ ↦ hφ w)
      (fun w _ ↦ det_fderiv_realChart_affine_nonneg c a w)
      (fun w hw ↦ (hu.differentiableOn one_ne_zero _ (hsU w hw)).differentiableAt
        (hU.mem_nhds (hsU w hw))),
    ω.integral_hamiltonianCurvature_image hs hinj
      (fun w _ ↦ (contDiff_realChart_affine c a).contDiffAt)
      (fun w _ ↦ det_fderiv_realChart_affine_nonneg c a w)
      (fun w hw ↦ hdom hw 1) (fun w hw ↦ hdom hw Complex.I),
    hpR, hpI]
  rfl

/-! ### The energy defects of the ends -/

section Ends

variable {ι : Type*} {c a : ι → ℂ} {H : ι → ℝ → V → ℝ} {Hout : ℝ → V → ℝ} {R : ℝ}

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
private theorem isOpen_setOf_forall_ne [Finite ι] (c : ι → ℂ) :
    IsOpen {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} := by
  simp only [ofPred_forall]
  exact isOpen_iInter_of_finite fun i ↦
    isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
private theorem preimage_puncturedSphereTruncation_subset (ha : ∀ i, a i ≠ 0) :
    Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R ⊆
      {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} := by
  intro z hz i hzi
  have h := (mem_puncturedSphereTruncation.1 hz).2 i
  rw [hzi, sub_self, norm_zero] at h
  have : 0 < ‖a i‖ * Real.exp (-(2 * π * R)) / 2 := by
    have := norm_pos_iff.2 (ha i)
    positivity
  linarith

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
private theorem isCompact_preimage_puncturedSphereTruncation (c a : ι → ℂ) (R : ℝ) :
    IsCompact (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R) :=
  Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
    (isCompact_puncturedSphereTruncation c a R)

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The annulus of the input end `i` lies in the truncation. -/
private theorem image_endAnnulus_subset (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) (hR : 1 ≤ R) (i : ι) :
    (fun w ↦ c i + a i * w) '' endAnnulus R ⊆ puncturedSphereTruncation c a R := by
  have hexp₁ := exp_neg_two_pi_lt_half.le
  have hexpR := exp_neg_two_pi_mul_le hR
  have hexpR' : Real.exp (2 * π) ≤ Real.exp (2 * π * R) :=
    Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
  intro w hw
  obtain ⟨h₁, h₂⟩ := (mem_image_affine_iff (ha i)).1 hw
  refine mem_puncturedSphereTruncation.2 ⟨?_, fun j ↦ ?_⟩
  · have := norm_sub_norm_le w (c i)
    nlinarith [hout i, norm_nonneg (a i)]
  · rcases eq_or_ne j i with rfl | hji
    · linarith
    · have h₃ := hsep hji.symm
      have h₄ : ‖c i - c j‖ ≤ ‖w - c j‖ + ‖w - c i‖ := by
        simpa using norm_sub_le (w - c j) (w - c i)
      nlinarith [norm_nonneg (a i), norm_nonneg (a j), Real.exp_pos (-(2 * π * R))]

/-- **Localizing an input end.** Over the truncation, the energy defect of the datum of the input
end `i` is its energy defect over the annulus of that end, off which the datum vanishes. -/
private theorem energyDefect_inputEndPerturbation_eq_image [Finite ι] (ω : SymplecticForm V)
    (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 1 (uncurry (H i))) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π))
    (hu : ContDiffOn ℝ 1 u {z | ∀ j, Complex.equivRealProdCLM.symm z ≠ c j}) (hR : 1 ≤ R)
    (i : ι) :
    energyDefect ω (inputEndPerturbation (c i) (a i) (H i)) u
        (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R) =
      energyDefect ω (inputEndPerturbation (c i) (a i) (H i)) u
        (Complex.equivRealProdCLM.symm ⁻¹' ((fun w ↦ c i + a i * w) '' endAnnulus R)) := by
  refine energyDefect_eq_of_subset ω (isOpen_setOf_forall_ne c) hu
    (contDiffOn_uncurry_of_contDiffAt fun z hz x ↦
      contDiffAt_inputEndPerturbation_prod (n := 1) (hH i) (hHs i) (ha i) (hz i) x)
    (isCompact_preimage_puncturedSphereTruncation c a R)
    (preimage_puncturedSphereTruncation_subset ha)
    (preimage_mono (image_endAnnulus_subset ha hsep hout hR i)) fun z ⟨hz, hzT⟩ ↦ ?_
  have hlow := (mem_puncturedSphereTruncation.1 hz).2 i
  have hlt : ‖a i‖ * Real.exp (-(2 * π)) / 2 < ‖Complex.equivRealProdCLM.symm z - c i‖ := by
    by_contra! hle
    exact hzT ((mem_image_affine_iff (ha i)).2 ⟨by linarith, by linarith⟩)
  have hc : Continuous fun z : ℝ × ℝ ↦ ‖Complex.equivRealProdCLM.symm z - c i‖ := by fun_prop
  filter_upwards [hc.continuousAt.eventually (lt_mem_nhds hlt)] with z' hz'
  exact funext (inputEndPerturbation_eq_zero_of_le_norm_sub hz'.le)

/-- A cutoff which is `1` on the disc `‖w‖ ≤ 1/4` and `0` off the disc `‖w‖ < 1/2`. In the
coordinates of an input end, the latter disc contains no other center. -/
private noncomputable def innerBump : ContDiffBump (0 : ℂ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

omit [FiniteDimensional ℝ V] in
private theorem innerBump_smul_eventuallyEq {v : ℝ × ℝ → V} {z : ℝ × ℝ}
    (hz : ‖Complex.equivRealProdCLM.symm z‖ < 1 / 4) :
    (fun w ↦ innerBump (Complex.equivRealProdCLM.symm w) • v w) =ᶠ[𝓝 z] v := by
  have hnorm : Continuous fun z : ℝ × ℝ ↦ ‖Complex.equivRealProdCLM.symm z‖ := by fun_prop
  filter_upwards [hnorm.continuousAt.eventually (gt_mem_nhds hz)] with z' hz'
  rw [innerBump.one_of_mem_closedBall (by
    rw [mem_closedBall, dist_zero_right]
    exact hz'.le), one_smul]

omit [FiniteDimensional ℝ V] in
/-- In the coordinates `w ↦ c i + a i w` of the input end `i`, the map `u` cut off by `innerBump`
is `C¹` on the pair of pants. -/
private theorem contDiffOn_innerBump_smul [Finite ι] (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hu : ContDiffOn ℝ 1 u {z | ∀ j, Complex.equivRealProdCLM.symm z ≠ c j}) (i : ι) :
    ContDiffOn ℝ 1 (fun w ↦ innerBump (Complex.equivRealProdCLM.symm w) •
      u (realChart (fun w ↦ c i + a i * w) w)) thricePuncturedSphereReal := by
  have hnorm : Continuous fun z : ℝ × ℝ ↦ ‖Complex.equivRealProdCLM.symm z‖ := by fun_prop
  refine contDiffOn_smul_of_eventuallyEq_zero (W := realChart (fun w ↦ c i + a i * w) ⁻¹'
    {z | ∀ j, Complex.equivRealProdCLM.symm z ≠ c j})
    ((isOpen_setOf_forall_ne c).preimage
      (contDiff_realChart_affine (c i) (a i) (n := 0)).continuous)
    (fun z _ ↦ (innerBump.contDiff.comp Complex.equivRealProdCLM.symm.contDiff).contDiffAt)
    (hu.comp (contDiff_realChart_affine (c i) (a i)).contDiffOn (mapsTo_preimage _ _))
    fun z hz hzW ↦ ?_
  -- A point which `w ↦ c i + a i w` sends to another center has norm greater than `1/2`.
  obtain ⟨j, hj⟩ : ∃ j, c i + a i * Complex.equivRealProdCLM.symm z = c j := by
    by_contra! h
    exact hzW fun j ↦ by
      rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply]
      exact h j
  have hji : j ≠ i := by
    rintro rfl
    have h0 : a j * Complex.equivRealProdCLM.symm z = 0 := by linear_combination hj
    exact (mem_thricePuncturedSphereReal_iff.1 hz).1 ((mul_eq_zero.1 h0).resolve_left (ha j))
  have hgt : 1 / 2 < ‖Complex.equivRealProdCLM.symm z‖ := by
    have h₁ := hsep hji.symm
    have h₂ : ‖c i - c j‖ = ‖a i‖ * ‖Complex.equivRealProdCLM.symm z‖ := by
      rw [← norm_mul, ← hj, sub_add_cancel_left, norm_neg]
    have := norm_pos_iff.2 (ha i)
    have := norm_pos_iff.2 (ha j)
    nlinarith
  filter_upwards [hnorm.continuousAt.eventually (lt_mem_nhds hgt)] with z' hz'
  exact innerBump.zero_of_le_dist (by rw [dist_zero_right]; exact hz'.le)

/-- **The energy defect of an input end.** Over the truncation of the sphere with moving input
ends, the energy defect of the datum of the input end `i` is the Hamiltonian term
`∫₀¹ H i(t, u(c i + a i φ₀(R + i t))) dt` of its boundary circle `s = R`. -/
private theorem energyDefect_inputEndPerturbation [Finite ι] (ω : SymplecticForm V)
    (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 1 (uncurry (H i))) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π))
    (hu : ContDiffOn ℝ 1 u {z | ∀ j, Complex.equivRealProdCLM.symm z ≠ c j}) (hR : 2 ≤ R)
    (i : ι) :
    energyDefect ω (inputEndPerturbation (c i) (a i) (H i)) u
        (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R) =
      ∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
        (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) := by
  -- Localize to the annulus of the end, and change coordinates along `w ↦ c i + a i w`.
  rw [energyDefect_inputEndPerturbation_eq_image ω hH hHs ha hsep hout hu (by linarith) i,
    preimage_image_eq_image_realChart, energyDefect_inputEndPerturbation_image ω (ha i) (hH i)
      (hHs i) (isOpen_setOf_forall_ne c) hu (fun z hz ↦ hz i) measurableSet_preimage_endAnnulus
      fun w hw ↦ preimage_puncturedSphereTruncation_subset ha (by
        rw [mem_preimage, realChart_apply, ContinuousLinearEquiv.symm_apply_apply]
        exact image_endAnnulus_subset ha hsep hout (by linarith) i ⟨_, hw, rfl⟩)]
  -- Cut `u ∘ g` off outside the disc `‖w‖ < 1/2`, and compute on the pair of pants.
  rw [Function.comp_def, ← energyDefect_congr ω measurableSet_preimage_endAnnulus fun z hz ↦
      innerBump_smul_eventuallyEq (by linarith [hz.2, exp_neg_two_pi_lt_half]),
    energyDefect_positivePlanePerturbation_annulus ω (hH i) (hHs i)
      (contDiffOn_innerBump_smul ha hsep hu i) hR]
  -- On the boundary circle `s = R` the cutoff is `1`.
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  have hlift : ‖zero.cylindricalEndLift (↑R + ↑t * Complex.I)‖ ≤ 1 / 4 := by
    have h := norm_cylindricalEndLift_sub_endCenter zero (↑R + ↑t * Complex.I)
    rw [endCenter_zero, sub_zero, endScale_zero] at h
    have hre : (↑R + ↑t * Complex.I : ℂ).re = R := by simp
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [h, hre, h2]
    linarith [exp_neg_two_pi_mul_le (by linarith : 1 ≤ R), exp_neg_two_pi_lt_half]
  simp only [ContinuousLinearEquiv.symm_apply_apply, realChart_apply,
    innerBump.one_of_mem_closedBall (by rw [mem_closedBall, dist_zero_right]; exact hlift),
    one_smul]

omit [FiniteDimensional ℝ V] in
private theorem contDiffOn_uncurry_negativePlanePerturbation (hHout : Periodic Hout 1)
    (hHouts : ContDiff ℝ 1 (uncurry Hout)) (W : Set (ℝ × ℝ)) (v : ℂ) :
    ContDiffOn ℝ 1
      (uncurry fun z x ↦ negativePlanePerturbation Hout (Complex.equivRealProdCLM.symm z) x v)
      (W ×ˢ univ) := by
  have h := contMDiff_prod_modelWithCornersSelf_iff.1
    (contMDiff_negativePlanePerturbation (n := 1) hHout
      (contMDiff_prod_modelWithCornersSelf_iff.2 hHouts.contMDiff))
  exact contDiffOn_uncurry_of_contDiffAt (fun z _ x ↦ (contMDiff_iff_contDiff.1 h).contDiffAt) v

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Near a point of the open disc `‖w‖ < 2 exp (2π)`, the output datum vanishes. -/
private theorem eventually_negativePlanePerturbation_eq_zero {M : Type*} {Hout : ℝ → M → ℝ}
    {z : ℝ × ℝ} (hz : ‖Complex.equivRealProdCLM.symm z‖ < 2 * Real.exp (2 * π)) :
    ∀ᶠ z' in 𝓝 z, negativePlanePerturbation Hout (Complex.equivRealProdCLM.symm z') =
      fun _ ↦ 0 := by
  have hnorm : Continuous fun z : ℝ × ℝ ↦ ‖Complex.equivRealProdCLM.symm z‖ := by fun_prop
  filter_upwards [hnorm.continuousAt.eventually (gt_mem_nhds hz)] with z' hz'
  exact funext (negativePlanePerturbation_eq_zero_of_norm_le hz'.le)

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Points of norm at least `2 exp (2π)` are at distance at least `‖a j‖ / 2` from each center. -/
private theorem div_two_le_norm_sub (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π))
    {w : ℂ} (hw : 2 * Real.exp (2 * π) ≤ ‖w‖) (j : ι) : ‖a j‖ / 2 ≤ ‖w - c j‖ := by
  have := norm_sub_norm_le w (c j)
  linarith [hout j]

/-- **Localizing the output end.** Over the truncation, the energy defect of the output datum is
its energy defect over the outer annulus `2 exp (2π) ≤ ‖w‖ ≤ 2 exp (2πR)`, off which it
vanishes. -/
private theorem energyDefect_negativePlanePerturbation_eq_outerAnnulus [Finite ι]
    (ω : SymplecticForm V) (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 1 (uncurry Hout))
    (ha : ∀ i, a i ≠ 0)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π))
    (hu : ContDiffOn ℝ 1 u {z | ∀ j, Complex.equivRealProdCLM.symm z ≠ c j}) (hR : 1 ≤ R) :
    energyDefect ω (negativePlanePerturbation Hout) u
        (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R) =
      energyDefect ω (negativePlanePerturbation Hout) u
        (Complex.equivRealProdCLM.symm ⁻¹' outerAnnulus R) := by
  have hexpR : Real.exp (-(2 * π * R)) ≤ 1 :=
    (exp_neg_two_pi_mul_le hR).trans exp_neg_two_pi_lt_half.le |>.trans (by norm_num)
  refine energyDefect_eq_of_subset ω (isOpen_setOf_forall_ne c) hu
    (contDiffOn_uncurry_negativePlanePerturbation hHout hHouts _)
    (isCompact_preimage_puncturedSphereTruncation c a R)
    (preimage_puncturedSphereTruncation_subset ha)
    (fun z hz ↦ mem_puncturedSphereTruncation.2 ⟨hz.2, fun j ↦ by
      nlinarith [div_two_le_norm_sub hout hz.1 j, norm_nonneg (a j),
        Real.exp_pos (-(2 * π * R))]⟩)
    fun z ⟨hz, hzA⟩ ↦ eventually_negativePlanePerturbation_eq_zero
      (not_le.1 fun h ↦ hzA ⟨h, (mem_puncturedSphereTruncation.1 hz).1⟩)

/-- A cutoff which is `1` on the disc `‖w - c‖ ≤ ‖a‖ / 8` and `0` off the disc
`‖w - c‖ < ‖a‖ / 4`. -/
private noncomputable def centerBump (c a : ℂ) (ha : a ≠ 0) : ContDiffBump c :=
  ⟨‖a‖ / 8, ‖a‖ / 4, by have := norm_pos_iff.2 ha; positivity,
    by have := norm_pos_iff.2 ha; linarith⟩

omit [FiniteDimensional ℝ V] in
/-- Away from the discs `‖w - c j‖ ≤ ‖a j‖ / 4`, the map cut off near the centers agrees with
`u`. -/
private theorem centerBump_smul_eventuallyEq [Fintype ι] (ha : ∀ i, a i ≠ 0) {z : ℝ × ℝ}
    (hz : ∀ j, ‖a j‖ / 4 < ‖Complex.equivRealProdCLM.symm z - c j‖) :
    (fun z ↦ (∏ j, (1 - centerBump (c j) (a j) (ha j) (Complex.equivRealProdCLM.symm z))) • u z)
      =ᶠ[𝓝 z] u := by
  have hdist {j : ι} : Continuous fun z : ℝ × ℝ ↦ ‖Complex.equivRealProdCLM.symm z - c j‖ := by
    fun_prop
  filter_upwards [eventually_all.2 fun j ↦ hdist.continuousAt.eventually (lt_mem_nhds (hz j))]
    with z' hz'
  rw [Finset.prod_eq_one fun j _ ↦ by
    rw [(centerBump (c j) (a j) (ha j)).zero_of_le_dist (by
      rw [dist_eq_norm]
      exact (hz' j).le), sub_zero], one_smul]

omit [FiniteDimensional ℝ V] in
/-- The map cut off near the centers is `C¹` on the pair of pants. -/
private theorem contDiffOn_centerBump_smul [Fintype ι] (ha : ∀ i, a i ≠ 0)
    (hu : ContDiffOn ℝ 1 u {z | ∀ j, Complex.equivRealProdCLM.symm z ≠ c j}) :
    ContDiffOn ℝ 1
      (fun z ↦ (∏ j, (1 - centerBump (c j) (a j) (ha j) (Complex.equivRealProdCLM.symm z))) • u z)
      thricePuncturedSphereReal := by
  refine contDiffOn_smul_of_eventuallyEq_zero (isOpen_setOf_forall_ne c)
    (fun z _ ↦ contDiffAt_prod fun j _ ↦ contDiffAt_const.sub
      ((centerBump (c j) (a j) (ha j)).contDiff.comp
        Complex.equivRealProdCLM.symm.contDiff).contDiffAt) hu fun z _ hzW ↦ ?_
  obtain ⟨j, hj⟩ : ∃ j, Complex.equivRealProdCLM.symm z = c j := by
    by_contra! h
    exact hzW h
  have hlt : ‖Complex.equivRealProdCLM.symm z - c j‖ < ‖a j‖ / 8 := by
    rw [hj, sub_self, norm_zero]
    have := norm_pos_iff.2 (ha j)
    positivity
  have hdist : Continuous fun z : ℝ × ℝ ↦ ‖Complex.equivRealProdCLM.symm z - c j‖ := by fun_prop
  filter_upwards [hdist.continuousAt.eventually (gt_mem_nhds hlt)] with z' hz'
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by
    rw [(centerBump (c j) (a j) (ha j)).one_of_mem_closedBall (by
      rw [mem_closedBall, dist_eq_norm]
      exact hz'.le), sub_self])

/-- **The energy defect of the negative plane datum over the outer annulus.** For a map `v` which
is `C¹` on `S = ℂ ∖ {0, 1}` and `R ≥ 2`, the energy defect of the negative plane datum of `Hout`
over the annulus `2 exp (2π) ≤ ‖w‖ ≤ 2 exp (2πR)` is minus the Hamiltonian term
`∫₀¹ Hout(t, v(φ_∞(-R + i t))) dt` of its outer boundary circle. -/
private theorem energyDefect_negativePlanePerturbation_outerAnnulus (ω : SymplecticForm V)
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 1 (uncurry Hout)) {v : ℝ × ℝ → V}
    (hv : ContDiffOn ℝ 1 v thricePuncturedSphereReal) (hR : 2 ≤ R) :
    energyDefect ω (negativePlanePerturbation Hout) v
        (Complex.equivRealProdCLM.symm ⁻¹' outerAnnulus R) =
      -∫ t in (0 : ℝ)..1, Hout t (v (Complex.equivRealProdCLM
        (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) := by
  have hexpR : Real.exp (-(2 * π * R)) ≤ 1 :=
    (exp_neg_two_pi_mul_le (by linarith)).trans exp_neg_two_pi_lt_half.le |>.trans (by norm_num)
  have hexp₁ : 1 ≤ Real.exp (2 * π) := Real.one_le_exp (by nlinarith [Real.pi_pos])
  have hD : IsCompact (Complex.equivRealProdCLM.symm ⁻¹' truncation R) :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_truncation R)
  -- Enlarge the outer annulus to the truncation `S_R` of the pair of pants.
  rw [← energyDefect_eq_of_subset ω isOpen_thricePuncturedSphereReal hv
    (contDiffOn_uncurry_negativePlanePerturbation hHout hHouts _) hD
    (preimage_truncation_subset_thricePuncturedSphereReal R) ?sub
    fun z ⟨hz, hzA⟩ ↦ eventually_negativePlanePerturbation_eq_zero (not_le.1 fun h ↦ hzA ⟨h, by
      rw [mem_preimage, truncation_eq] at hz
      simpa using hz.2⟩)]
  case sub =>
    intro z ⟨h₁, h₂⟩
    rw [mem_preimage, truncation_eq]
    have := norm_sub_norm_le (Complex.equivRealProdCLM.symm z) 1
    rw [norm_one] at this
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [mem_ofPred_eq]
      linarith
    · rw [mem_ofPred_eq]
      linarith
    · rw [mem_closedBall, dist_zero_right]
      exact h₂
  -- The output datum is the pair-of-pants datum with a single output Hamiltonian.
  have h := ω.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation
    (periodic_single (q₀ := inf) hHout) (contDiff_uncurry_single hHouts) hv (by linarith : 1 ≤ R)
  rw [pairOfPantsPerturbation_single_inf] at h
  rw [energyDefect, h, Fintype.sum_eq_single inf fun q hq ↦ by
    simp [Pi.single_eq_of_ne hq], smoothTransition.one_of_one_le (by linarith)]
  simp only [endSign_inf, neg_one_mul, Pi.single_eq_same]
  ring

/-- **The energy defect of the output end.** Over the truncation of the sphere with moving input
ends, the energy defect of the output datum is minus the Hamiltonian term
`∫₀¹ Hout(t, u(φ_∞(-R + i t))) dt` of the boundary circle `s = -R`. -/
private theorem energyDefect_negativePlanePerturbation [Finite ι] (ω : SymplecticForm V)
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π))
    (hu : ContDiffOn ℝ 1 u {z | ∀ j, Complex.equivRealProdCLM.symm z ≠ c j}) (hR : 2 ≤ R) :
    energyDefect ω (negativePlanePerturbation Hout) u
        (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R) =
      -∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
        (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) := by
  have := Fintype.ofFinite ι
  have hexp₁ : 1 ≤ Real.exp (2 * π) := Real.one_le_exp (by nlinarith [Real.pi_pos])
  -- Points of the outer annulus are away from the discs about the centers.
  have hfar {w : ℂ} (hw : 2 * Real.exp (2 * π) ≤ ‖w‖) (j : ι) : ‖a j‖ / 4 < ‖w - c j‖ := by
    have := norm_pos_iff.2 (ha j)
    linarith [div_two_le_norm_sub hout hw j]
  -- Localize to the outer annulus, cut `u` off near the centers, and compute on the pair of
  -- pants.
  rw [energyDefect_negativePlanePerturbation_eq_outerAnnulus ω hHout hHouts ha hout hu
      (by linarith),
    ← energyDefect_congr ω measurableSet_preimage_outerAnnulus fun z hz ↦
      centerBump_smul_eventuallyEq ha fun j ↦ hfar hz.1 j,
    energyDefect_negativePlanePerturbation_outerAnnulus ω hHout hHouts
      (contDiffOn_centerBump_smul ha hu) hR]
  -- On the boundary circle `s = -R` the cutoff is `1`.
  congr 1
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  have h := norm_cylindricalEndLift_sub_endCenter inf (↑(-R) + ↑t * Complex.I)
  rw [endCenter_inf, sub_zero, endScale_inf, Complex.norm_ofNat] at h
  have hre : (↑(-R) + ↑t * Complex.I : ℂ).re = -R := by simp
  rw [hre, neg_mul_eq_mul_neg, neg_neg] at h
  have hexpR' : Real.exp (2 * π) ≤ Real.exp (2 * π * R) :=
    Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
  rw [(centerBump_smul_eventuallyEq ha fun j ↦ hfar (by
    rw [ContinuousLinearEquiv.symm_apply_apply, h]
    linarith) j).eq_of_nhds]

/-! ### The energy identity -/

/-- **The energy identity on a sphere with moving input ends.** Let the input ends have centers
`c i`, nonzero scales `a i` and period-one `C¹` Hamiltonians `H i`, with the discs
`‖w - c i‖ < ‖a i‖ / 2` pairwise disjoint and contained in the disc `‖w‖ ≤ 2 exp (2π)`, and let the
output end at `∞` have a period-one `C¹` Hamiltonian `Hout`. Let `u` be `C¹` on `ℂ ∖ {c i}`, in
real coordinates, and `R ≥ 2`. Then over the truncation at height `R`, the Floer energy of `u` for
the datum `K` is the symplectic area of `u`, plus the Hamiltonian boundary terms of the input
circles `s = R`, minus that of the output circle `s = -R`, minus the integrated curvature:

`∫ E = ∫ u^*ω + ∑ i, ∫₀¹ H i(t, ℓ_i(t)) dt - ∫₀¹ Hout(t, ℓ_∞(t)) dt - ∫ R_K(u)`,

for the boundary loops `ℓ_i(t) = u(c i + a i φ₀(R + i t))` and `ℓ_∞(t) = u(φ_∞(-R + i t))`. -/
theorem integral_floerEnergyDensity_puncturedSpherePerturbation_truncation [Fintype ι]
    (ω : SymplecticForm V) (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 1 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π))
    (hu : ContDiffOn ℝ 1 u {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}) (hR : 2 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
        ω.floerEnergyDensity
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
            Complex.I) u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) +
        ((∑ i, ∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
            (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
          ∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
            (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
          ω.hamiltonianCurvature
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
              Complex.I) z (u z) := by
  -- The datum is the sum of the output datum and of the input end data.
  let piece : Option ι → ℂ → V → ℂ →L[ℝ] ℝ := fun k ↦
    k.elim (negativePlanePerturbation Hout) fun i ↦ inputEndPerturbation (c i) (a i) (H i)
  have hK : puncturedSpherePerturbation c a H Hout = fun w x ↦ ∑ k, piece k w x := by
    funext w x
    rw [puncturedSpherePerturbation_def, Fintype.sum_option, add_comm]
    rfl
  have hP (k : Option ι) (v : ℂ) : ContDiffOn ℝ 1
      (uncurry fun z x ↦ piece k (Complex.equivRealProdCLM.symm z) x v)
      ({z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} ×ˢ univ) := by
    cases k with
    | none => exact contDiffOn_uncurry_negativePlanePerturbation hHout hHouts _ v
    | some i =>
      exact contDiffOn_uncurry_of_contDiffAt
        (U := {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}) (fun z hz x ↦
          contDiffAt_inputEndPerturbation_prod (n := 1) (hH i) (hHs i) (ha i) (hz i) x) v
  have h := energyDefect_sum ω (isOpen_setOf_forall_ne c) hu hP
    (isCompact_preimage_puncturedSphereTruncation c a R)
    (preimage_puncturedSphereTruncation_subset ha)
  rw [← hK, Fintype.sum_option] at h
  simp only [piece, Option.elim_none, Option.elim_some,
    energyDefect_negativePlanePerturbation ω hHout hHouts ha hout hu hR,
    energyDefect_inputEndPerturbation ω hH hHs ha hsep hout hu hR] at h
  rw [energyDefect] at h
  linarith

/-- **The energy bound on a sphere with moving input ends.** Under the hypotheses of
`SymplecticForm.integral_floerEnergyDensity_puncturedSpherePerturbation_truncation`, if moreover
`|H i| ≤ B i` and `|Hout| ≤ Bout`, then the Floer energy over the truncation differs from the
symplectic area plus the Hamiltonian boundary terms by at most `∑ i, B i + Bout`, uniformly in the
height `R` and in the configuration of the input ends. -/
theorem abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le
    [Fintype ι] (ω : SymplecticForm V) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContDiff ℝ 1 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {B : ι → ℝ} {Bout : ℝ}
    (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout)
    (hu : ContDiffOn ℝ 1 u {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}) (hR : 2 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
        ω.floerEnergyDensity
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
            Complex.I) u z) -
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) -
        ((∑ i, ∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
            (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
          ∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
            (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))))| ≤ ∑ i, B i + Bout := by
  have hring : ∀ A S C : ℝ, A + S - C - A - S = -C := fun _ _ _ ↦ by ring
  rw [integral_floerEnergyDensity_puncturedSpherePerturbation_truncation ω hH hHs hHout hHouts ha
    hsep hout hu hR, hring, abs_neg]
  have hB₀ (i : ι) : 0 ≤ B i := (abs_nonneg _).trans (hB i 0 0)
  have hBout₀ : 0 ≤ Bout := (abs_nonneg _).trans (hBout 0 0)
  have hexp : Real.exp (-(2 * π)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
  have hsupp (i : ι) : ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ ‖a i‖ / 2 := by
    nlinarith [norm_nonneg (a i)]
  rw [← ENNReal.ofReal_le_ofReal_iff (add_nonneg (Finset.sum_nonneg fun i _ ↦ hB₀ i) hBout₀),
    ← Real.enorm_eq_ofReal_abs, ENNReal.ofReal_add (Finset.sum_nonneg fun i _ ↦ hB₀ i) hBout₀,
    ENNReal.ofReal_sum_of_nonneg fun i _ ↦ hB₀ i]
  exact (enorm_integral_le_lintegral_enorm _).trans ((setLIntegral_le_lintegral _ _).trans
    (ω.lintegral_enorm_hamiltonianCurvature_puncturedSpherePerturbation_le hH hHs hHout hHouts ha
      (fun i j hij ↦ by linarith [hsep hij, hsupp i, hsupp j])
      (fun i ↦ by linarith [hout i, hsupp i]) hB hBout u))

end Ends

end TauCeti.SymplecticForm
