/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Basic
public import TauCeti.Geometry.Symplectic.Floer.Pullback
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-!
# The integrated curvature of the pair-of-pants perturbation

The energy identity `E = A₁ + A₂ - A₀ + ω(A) - ∫ R_K` for pairs of pants turns a bound
`∫_S sup_X |R_K| ≤ C` on the curvature of the perturbation datum `K` into the lower bound on the
valuation of product coefficients and the upper bound on the energy of the curves they count.
This file computes such a constant `C` for the perturbation
`TauCeti.Floer.pairOfPantsPerturbation` built from period-one Hamiltonians `H_q` on the three ends
of the thrice-punctured sphere `S = ℂ ∖ {0, 1}`, for a symplectic vector space target `V`.

In the coordinates `(s, t)` of the end `q` the perturbation is `β(±s) H_q(t) dt` with the cutoff
`β(±s) = smoothTransition (±s - 1)`
(`TauCeti.Floer.pairOfPantsPerturbation_cylindricalEndLift_of_pos`), so its curvature there is the
continuation curvature `±β'(±s - 1) H_q(t)`
(`SymplecticForm.hamiltonianCurvature_pairOfPantsEndComponent`), and the perturbation vanishes
off the parts `±s > 1` of the ends. Since the curvature is a two-form
(`SymplecticForm.hamiltonianCurvature_perturbationPullback`), its absolute integral over
`S` is the sum over the three ends of the integrals of `β'(±s - 1) |H_q(t)|` over half-cylinders,
and the cutoff has total increase `∫ β' = 1`. Hence, if `|H_q| ≤ B_q`, then

`∫_S |R_K(z, u(z))| dz ≤ B₀ + B₁ + B_∞`

for every map `u : S → V`, measurable or not
(`SymplecticForm.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le`). The curvature
is computed in the global coordinate `z = s + i t` of `S ⊆ ℂ`, in which the `ds` and `dt`
components of `K` are its values on the tangent vectors `1` and `i`.

## Main results

* `TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le`: the
  integrated curvature of the pair-of-pants perturbation along any map is at most the sum of
  bounds for the three end Hamiltonians.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the resulting energy bounds.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 8, on perturbation data on
  surfaces with strip-like ends and their energy.
-/

public section

open Set Real Function MeasureTheory Filter Manifold TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology

namespace TauCeti

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {H : Puncture → ℝ → V → ℝ}

/-- The end lift of `q`, in the real coordinates `ℝ × ℝ ≃ ℂ`. -/
private noncomputable def endChart (q : Puncture) (z : ℝ × ℝ) : ℝ × ℝ :=
  Complex.equivRealProdCLM (q.cylindricalEndLift (Complex.equivRealProdCLM.symm z))

/-- The part `±s > 1/2`, `t ∈ [-1/2, 1/2)` of the end `q` in its cylinder coordinates. It
contains the support of the curvature of the end, and the end lift is injective on it. -/
private noncomputable def endStrip (q : Puncture) : Set (ℝ × ℝ) :=
  {s | 1 / 2 < q.endSign * s} ×ˢ Ico (-1 / 2) (1 / 2)

private theorem endSign_mul_pos_of_mem_endStrip {q : Puncture} {z : ℝ × ℝ}
    (hz : z ∈ endStrip q) : 0 < q.endSign * z.1 := by
  have h : 1 / 2 < q.endSign * z.1 := hz.1
  linarith

/-- The perturbation is `C¹` jointly in the domain point of `S` and the target point. -/
private theorem contDiffAt_pairOfPantsPerturbation_prod (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {w : ℂ} (hw : w ≠ 0 ∧ w ≠ 1) (x : V) :
    ContDiffAt ℝ 1 (fun p : ℂ × V => pairOfPantsPerturbation H p.1 p.2) (w, x) := by
  have hHs' : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ, ℝ) 1 (uncurry (H q)) := fun q => by
    have h := (hHs q).contMDiff
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
    exact h
  have h := contMDiffAt_pairOfPantsPerturbation (n := 1) hH hHs' ⟨w, hw⟩ x
  have h' : ContMDiffAt 𝓘(ℝ, ℂ × V) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × V => pairOfPantsPerturbation H p.1 p.2) (w, x) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact h
  exact h'.contDiffAt

/-- The components of the perturbation in real coordinates are differentiable in the domain
point, at points of `S`. -/
private theorem differentiableAt_pairOfPantsPerturbation_domain (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1)
    (x : V) (v : ℂ) :
    DifferentiableAt ℝ
      (fun z' => pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z') x v) z := by
  have hK := (contDiffAt_pairOfPantsPerturbation_prod hH hHs hz x).differentiableAt one_ne_zero
  exact (hK.comp z (Complex.equivRealProdCLM.symm.differentiableAt.prodMk
    (differentiableAt_const x))).clm_apply (differentiableAt_const v)

/-- The components of the perturbation are differentiable in the target point, at points
of `S`. -/
private theorem differentiableAt_pairOfPantsPerturbation_target (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {w : ℂ} (hw : w ≠ 0 ∧ w ≠ 1) (x : V) (v : ℂ) :
    DifferentiableAt ℝ (fun y => pairOfPantsPerturbation H w y v) x := by
  have hK := (contDiffAt_pairOfPantsPerturbation_prod hH hHs hw x).differentiableAt one_ne_zero
  exact (hK.comp x ((differentiableAt_const w).prodMk differentiableAt_id)).clm_apply
    (differentiableAt_const v)

/-- The derivative of the end chart is multiplication by the derivative of the end lift. -/
private theorem hasFDerivAt_endChart (q : Puncture) (z : ℝ × ℝ) :
    HasFDerivAt (endChart q)
      ((Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ).comp
        (((ContinuousLinearMap.toSpanSingleton ℂ
          (deriv q.cylindricalEndLift (Complex.equivRealProdCLM.symm z))).restrictScalars ℝ).comp
            (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ))) z := by
  have h := ((q.hasDerivAt_cylindricalEndLift
    (Complex.equivRealProdCLM.symm z)).differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ)
  exact Complex.equivRealProdCLM.hasFDerivAt.comp z
    (h.comp z Complex.equivRealProdCLM.symm.hasFDerivAt)

private theorem fderiv_endChart_apply (q : Puncture) (z v : ℝ × ℝ) :
    fderiv ℝ (endChart q) z v = Complex.equivRealProdCLM
      (deriv q.cylindricalEndLift (Complex.equivRealProdCLM.symm z) *
        Complex.equivRealProdCLM.symm v) := by
  rw [(hasFDerivAt_endChart q z).fderiv]
  simp [mul_comm]

private theorem contDiff_endChart (q : Puncture) : ContDiff ℝ 2 (endChart q) := by
  exact Complex.equivRealProdCLM.contDiff.comp
    (((q.contDiff_cylindricalEndLift 2).restrict_scalars ℝ).comp
      Complex.equivRealProdCLM.symm.contDiff)

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- The pullback of the perturbation along the end chart of `q`, evaluated on a tangent vector
`v`, is its component `TauCeti.Floer.pairOfPantsEndComponent` along `v` in the end coordinates. -/
private theorem perturbationPullback_endChart (q : Puncture) (v : ℝ × ℝ) :
    perturbationPullback (endChart q)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) v =
      pairOfPantsEndComponent H q (Complex.equivRealProdCLM.symm v) := by
  -- A real-linear functional `L` on `ℂ` satisfies `L w = Re w · L 1 + Im w · L i`.
  have hL (L : ℂ →L[ℝ] ℝ) (w : ℂ) :
      (Complex.equivRealProdCLM w).1 * L 1 + (Complex.equivRealProdCLM w).2 * L Complex.I =
        L w := by
    have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by simp
    conv_rhs => rw [hw]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    simp
  funext z x
  rw [perturbationPullback_apply, fderiv_endChart_apply, endChart,
    ContinuousLinearEquiv.symm_apply_apply, hL, pairOfPantsEndComponent_def]
  rfl

variable [FiniteDimensional ℝ V]

/-- **The curvature in the coordinates of an end.** On the end `q`, where `±s > 0`, the curvature
of the pulled-back perturbation `β(±s) H_q(t) dt` is `±β'(±s - 1) H_q(t)`. -/
private theorem hamiltonianCurvature_perturbationPullback_endChart (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {q : Puncture}
    {z : ℝ × ℝ} (hz : 0 < q.endSign * z.1) (x : V) :
    ω.hamiltonianCurvature
        (perturbationPullback (endChart q)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          stdComplexLineReal)
        (perturbationPullback (endChart q)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          stdComplexLineImag) z x =
      q.endSign * deriv smoothTransition (q.endSign * z.1 - 1) * H q z.2 x := by
  have hHt : DifferentiableAt ℝ (fun t ↦ H q t x) z.2 :=
    DifferentiableAt.comp (g := uncurry (H q)) (f := fun t : ℝ ↦ (t, x)) z.2
      ((hHs q).differentiable one_ne_zero (z.2, x))
      (differentiableAt_id.prodMk (differentiableAt_const x))
  have h₁ : Complex.equivRealProdCLM.symm stdComplexLineReal = 1 := by
    apply Complex.ext <;> simp [stdComplexLineReal_eq]
  have hI : Complex.equivRealProdCLM.symm stdComplexLineImag = Complex.I := by
    apply Complex.ext <;> simp [stdComplexLineImag_eq]
  rw [perturbationPullback_endChart, perturbationPullback_endChart, h₁, hI,
    ω.hamiltonianCurvature_pairOfPantsEndComponent (hH q) hz hHt]

/-- **The curvature is supported on the ends.** At a point of `S` where the signed longitudinal
coordinate of every end is less than `1`, the perturbation vanishes nearby, and so does its
curvature. -/
private theorem hamiltonianCurvature_pairOfPantsPerturbation_eq_zero (ω : SymplecticForm V)
    {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1)
    (h : ∀ q : Puncture, q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re < 1)
    (x : V) :
    ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z x = 0 := by
  have hev : ∀ᶠ z' in 𝓝 z, ∀ q : Puncture,
      q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z')).re < 1 := by
    refine Filter.eventually_all.2 fun q ↦ ?_
    have hc : ContinuousAt
        (fun z' ↦ q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z')).re) z :=
      continuousAt_const.mul
        (((q.contDiffAt_re_endCoord (ne_endCenter hz q) (n := 0)).continuousAt).comp
          Complex.equivRealProdCLM.symm.continuous.continuousAt)
    exact hc.eventually (gt_mem_nhds (h q))
  have hK : ∀ᶠ z' in 𝓝 z, ∀ y, pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z') y = 0 :=
    hev.mono fun z' hz' y ↦ by
      rw [pairOfPantsPerturbation_def]
      refine Finset.sum_eq_zero fun q _ ↦ ?_
      rw [smoothTransition.zero_of_nonpos (by linarith [hz' q]), zero_mul, zero_smul]
  rw [ω.hamiltonianCurvature_congr_of_eventuallyEq (Ks' := fun _ _ ↦ 0) (Kt' := fun _ _ ↦ 0)
    (hK.mono fun z' hz' ↦ funext fun y ↦ by simp [hz' y])
    (hK.mono fun z' hz' ↦ funext fun y ↦ by simp [hz' y]), hamiltonianCurvature_zero_left]
  simp

/-- The end lift is injective on the strip `endStrip q`, whose angular coordinate ranges over one
period. -/
private theorem injOn_endChart (q : Puncture) : InjOn (endChart q) (endStrip q) := by
  intro a ha b hb hab
  have h := q.injOn_cylindricalEndLift (by simpa using ha.2) (by simpa using hb.2)
    (Complex.equivRealProdCLM.injective hab)
  exact Complex.equivRealProdCLM.symm.injective h

/-- Every point of `S` where some end has signed longitudinal coordinate greater than `1/2` is the
image of a point of that end's strip. -/
private theorem mem_image_endChart {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1)
    {q : Puncture} (hq : 1 / 2 < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re) :
    z ∈ endChart q '' endStrip q := by
  refine ⟨Complex.equivRealProdCLM (q.endCoord (Complex.equivRealProdCLM.symm z)),
    ⟨by simpa using hq, by simpa using q.im_endCoord_mem_Ico _⟩, ?_⟩
  rw [endChart, ContinuousLinearEquiv.symm_apply_apply,
    q.cylindricalEndLift_endCoord (ne_endCenter hz q), ContinuousLinearEquiv.apply_symm_apply]

/-- The cutoff of an end has total increase one along the end. -/
private theorem lintegral_deriv_smoothTransition_endSign (q : Puncture) :
    ∫⁻ s, ENNReal.ofReal (deriv smoothTransition (q.endSign * s - 1)) = 1 := by
  have h₁ : ∫⁻ s, ENNReal.ofReal (deriv smoothTransition (s - 1)) = 1 := by
    rw [lintegral_sub_right_eq_self (fun s ↦ ENNReal.ofReal (deriv smoothTransition s)) 1,
      ← ofReal_integral_eq_lintegral_ofReal smoothTransition.integrable_deriv
        (ae_of_all _ fun _ ↦ smoothTransition.monotone.deriv_nonneg),
      smoothTransition.integral_deriv, ENNReal.ofReal_one]
  cases q
  · simpa using h₁
  · simpa using h₁
  · convert smoothTransition.lintegral_ofReal_mul_deriv (-1) one_pos using 4 with s
    simp only [endSign_inf, one_mul]
    ring_nf

/-- The curvature of the perturbation over the image of the strip of the end `q` is at most a
bound `B_q` for the Hamiltonian of that end. -/
private theorem setLIntegral_image_endChart_le (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (u : ℝ × ℝ → V) (q : Puncture) :
    ∫⁻ z in endChart q '' endStrip q, ‖ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ENNReal.ofReal (B q) := by
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hmeas : MeasurableSet (endStrip q) :=
    (measurableSet_lt measurable_const (measurable_const.mul measurable_id)).prod measurableSet_Ico
  have hψ : ∀ s, 0 ≤ deriv smoothTransition s := fun _ ↦ smoothTransition.monotone.deriv_nonneg
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hmeas
    (fun z _ ↦ (hasFDerivAt_endChart q z).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    (injOn_endChart q)]
  calc _ ≤ ∫⁻ z in endStrip q,
        ENNReal.ofReal (deriv smoothTransition (q.endSign * z.1 - 1)) * ENNReal.ofReal (B q) := by
        refine setLIntegral_mono' hmeas fun z hz ↦ ?_
        have hz' := endSign_mul_pos_of_mem_endStrip hz
        have hS : Complex.equivRealProdCLM.symm (endChart q z) ≠ 0 ∧
            Complex.equivRealProdCLM.symm (endChart q z) ≠ 1 := by
          rw [endChart, ContinuousLinearEquiv.symm_apply_apply]
          exact cylindricalEndLift_ne_zero_and_ne_one q (by simpa using hz')
        -- The curvature is a two-form, and in the coordinates of the end it is `±β' H_q`.
        have key := ω.hamiltonianCurvature_perturbationPullback (φ := endChart q) (w := z)
          (Ks := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (Kt := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          (x := u (endChart q z)) ((contDiff_endChart q).contDiffAt)
          (differentiableAt_pairOfPantsPerturbation_domain hH hHs hS _ 1)
          (differentiableAt_pairOfPantsPerturbation_domain hH hHs hS _ Complex.I)
          (differentiableAt_pairOfPantsPerturbation_target hH hHs hS _ 1)
          (differentiableAt_pairOfPantsPerturbation_target hH hHs hS _ Complex.I)
        rw [hamiltonianCurvature_perturbationPullback_endChart ω hH hHs hz'] at key
        rw [← Real.enorm_eq_ofReal_abs, ← enorm_mul, ← key, Real.enorm_eq_ofReal_abs, abs_mul,
          abs_mul, abs_endSign, abs_of_nonneg (hψ _), one_mul, ← ENNReal.ofReal_mul (hψ _)]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hB q _ _) (hψ _))
    _ = ∫⁻ s in {s | 1 / 2 < q.endSign * s},
        ENNReal.ofReal (deriv smoothTransition (q.endSign * s - 1)) * ENNReal.ofReal (B q) := by
        have hm : Measurable fun z : ℝ × ℝ ↦
            ENNReal.ofReal (deriv smoothTransition (q.endSign * z.1 - 1)) * ENNReal.ofReal (B q) :=
          (ENNReal.continuous_ofReal.comp
            (((smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl).comp
              (by fun_prop))).measurable.mul_const _
        have hvol : volume (Ico (-1 / 2 : ℝ) (1 / 2)) = 1 := by
          rw [Real.volume_Ico]
          norm_num
        rw [Measure.volume_eq_prod, endStrip, setLIntegral_prod _ hm.aemeasurable]
        simp only [setLIntegral_const, hvol, mul_one]
    _ ≤ ∫⁻ s, ENNReal.ofReal (deriv smoothTransition (q.endSign * s - 1)) * ENNReal.ofReal (B q) :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (B q) := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
          lintegral_deriv_smoothTransition_endSign, one_mul]

/-- **The integrated curvature of the pair-of-pants perturbation.** Let `K` be the pair-of-pants
perturbation of period-one `C¹` Hamiltonians `H_q` on the three ends of `S = ℂ ∖ {0, 1}`, with
`|H_q| ≤ B_q`, and write its components in the global coordinate `z = s + i t` of `ℂ` as
`K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)`. Then for every map `u` into the target, the integral
of `|R_K(z, u(z))|` over the plane is at most `B₀ + B₁ + B_∞`. -/
theorem lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (u : ℝ × ℝ → V) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ∑ q, ENNReal.ofReal (B q) := by
  set N : Set (ℝ × ℝ) := {Complex.equivRealProdCLM 0, Complex.equivRealProdCLM 1}
  have hN : volume N = 0 := by
    rw [Measure.volume_eq_prod]
    exact (Set.toFinite N).measure_zero _
  -- Off the two punctures, the curvature is supported in the images of the strips of the ends.
  have hsupp : support (fun z ↦ ‖ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z)‖ₑ) ⊆ (⋃ q, endChart q '' endStrip q) ∪ N := by
    intro z hz
    by_cases h₀ : Complex.equivRealProdCLM.symm z = 0
    · exact Or.inr (Or.inl ((Complex.equivRealProdCLM.apply_symm_apply z).symm.trans
        (congrArg _ h₀)))
    by_cases h₁ : Complex.equivRealProdCLM.symm z = 1
    · exact Or.inr (Or.inr ((Complex.equivRealProdCLM.apply_symm_apply z).symm.trans
        (congrArg _ h₁)))
    by_cases hq : ∃ q : Puncture,
        1 / 2 < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re
    · obtain ⟨q, hq⟩ := hq
      exact Or.inl (mem_iUnion.2 ⟨q, mem_image_endChart ⟨h₀, h₁⟩ hq⟩)
    · simp only [not_exists, not_lt] at hq
      refine absurd ?_ hz
      simp [hamiltonianCurvature_pairOfPantsPerturbation_eq_zero ω ⟨h₀, h₁⟩
        (fun q ↦ (hq q).trans_lt (by norm_num))]
  calc _ = ∫⁻ z in (⋃ q, endChart q '' endStrip q) ∪ N, ‖ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z)‖ₑ := (setLIntegral_eq_of_support_subset hsupp).symm
    _ ≤ _ := lintegral_union_le _ _ _
    _ = _ := by rw [setLIntegral_measure_zero _ _ hN, add_zero]
    _ ≤ _ := lintegral_iUnion_le _ _
    _ = _ := tsum_fintype _
    _ ≤ _ := Finset.sum_le_sum fun q _ ↦ setLIntegral_image_endChart_le ω hH hHs hB u q

end SymplecticForm

end TauCeti
