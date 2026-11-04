/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.EndChart
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The integrated curvature and the energy identity of the pair-of-pants perturbation

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

The same decomposition of `S` into its core, where `K` vanishes, and the three ends integrates
the energy identity over the truncation `S_R` of `S`
(`TauCeti.ThricePuncturedSphere.truncation`), where every `±s ≤ R`. On each end the rectangle
identity `TauCeti.SymplecticForm.integral_floerEnergyDensity` applies in cylinder coordinates; the
boundary terms along the angular sides cancel by periodicity, and those on the circles `±s = 1`
vanish with the cutoff. For a map `u` which is `C¹` on `S` and `R ≥ 1` this gives

`∫_{S_R} E = ∫_{S_R} u^*ω + β(R - 1) ∑ q, ±∫₀¹ H_q(t, u(φ_q(±R + i t))) dt - ∫_{S_R} R_K(u)`,

with the sign `+` on the input ends `0`, `1` and `-` on the output end `∞`. With the curvature
bound, the energy over `S_R` therefore differs from the area plus the Hamiltonian boundary terms by
at most `B₀ + B₁ + B_∞`, uniformly in `R`.

## Main results

* `TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le`: the
  integrated curvature of the pair-of-pants perturbation along any map is at most the sum of
  bounds for the three end Hamiltonians.
* `SymplecticForm.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation`: the energy
  identity on the truncated pair of pants.
* `SymplecticForm.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_le`: the
  resulting energy bound, uniform in the truncation.

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

/-- The components of the perturbation in real coordinates are differentiable in the domain
point, at points of `S`. -/
private theorem differentiableAt_pairOfPantsPerturbation_domain (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
    (x : V) (v : ℂ) :
    DifferentiableAt ℝ
      (fun z' => pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z') x v) z := by
  exact ((contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz x v).differentiableAt
    one_ne_zero).comp (f := fun z' : ℝ × ℝ ↦ (z', x)) z
      (differentiableAt_id.prodMk (differentiableAt_const x))

/-- The components of the perturbation are differentiable in the target point, at points
of `S`. -/
private theorem differentiableAt_pairOfPantsPerturbation_target (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
    (x : V) (v : ℂ) :
    DifferentiableAt ℝ (fun y => pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) y v)
      x := by
  have hK := (contDiffAt_pairOfPantsPerturbation_prod hH hHs
    (mem_thricePuncturedSphereReal_iff.1 hz) x).differentiableAt one_ne_zero
  exact (hK.comp x ((differentiableAt_const _).prodMk differentiableAt_id)).clm_apply
    (differentiableAt_const v)

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
  rw [perturbationPullback_endChart, perturbationPullback_endChart,
    equivRealProdCLM_symm_stdComplexLineReal, equivRealProdCLM_symm_stdComplexLineImag,
    ω.hamiltonianCurvature_pairOfPantsEndComponent (hH q) hz hHt]

/-- **The curvature is supported on the ends.** At a point of `S` where the signed longitudinal
coordinate of every end is less than `1`, the perturbation vanishes nearby, and so does its
curvature. -/
private theorem hamiltonianCurvature_pairOfPantsPerturbation_eq_zero (ω : SymplecticForm V)
    {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
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
        (((q.contDiffAt_re_endCoord (ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hz) q)
          (n := 0)).continuousAt).comp
          Complex.equivRealProdCLM.symm.continuous.continuousAt)
    exact hc.eventually (gt_mem_nhds (h q))
  have hK : ∀ᶠ z' in 𝓝 z, ∀ y, pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z') y = 0 :=
    hev.mono fun z' hz' y ↦ pairOfPantsPerturbation_eq_zero_of_forall_le (fun q ↦ (hz' q).le) y
  rw [ω.hamiltonianCurvature_congr_of_eventuallyEq (Ks' := fun _ _ ↦ 0) (Kt' := fun _ _ ↦ 0)
    (hK.mono fun z' hz' ↦ funext fun y ↦ by simp [hz' y])
    (hK.mono fun z' hz' ↦ funext fun y ↦ by simp [hz' y]), hamiltonianCurvature_zero_left]
  simp


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
  have hmeas := measurableSet_endStrip q
  have hψ : ∀ s, 0 ≤ deriv smoothTransition s := fun _ ↦ smoothTransition.monotone.deriv_nonneg
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hmeas
    (fun z _ ↦ (hasFDerivAt_endChart q z).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    (injOn_endChart q)]
  calc _ ≤ ∫⁻ z in endStrip q,
        ENNReal.ofReal (deriv smoothTransition (q.endSign * z.1 - 1)) * ENNReal.ofReal (B q) := by
        refine setLIntegral_mono' hmeas fun z hz ↦ ?_
        have hz' := endSign_mul_pos_of_mem_endStrip hz
        have hS := endChart_mem_thricePuncturedSphereReal hz'
        -- The curvature is a two-form, and in the coordinates of the end it is `±β' H_q`.
        have key := ω.hamiltonianCurvature_perturbationPullback (φ := endChart q) (w := z)
          (Ks := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (Kt := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          (x := u (endChart q z)) ((contDiff_endChart q 2).contDiffAt)
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
        rw [Measure.volume_eq_prod, endStrip_def, setLIntegral_prod _ hm.aemeasurable]
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
    have hS : z ∈ thricePuncturedSphereReal := mem_thricePuncturedSphereReal_iff.2 ⟨h₀, h₁⟩
    by_cases hq : ∃ q : Puncture,
        1 / 2 < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re
    · obtain ⟨q, hq⟩ := hq
      exact Or.inl (mem_iUnion.2 ⟨q, mem_image_endChart hS hq⟩)
    · simp only [not_exists, not_lt] at hq
      refine absurd ?_ hz
      simp [hamiltonianCurvature_pairOfPantsPerturbation_eq_zero ω hS
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

/-! ### The energy identity on the truncated pair of pants -/

/-- The part `1 ≤ ±s ≤ R`, `t ∈ [-1/2, 1/2)` of the end `q` in its cylinder coordinates: the
collar and the cylindrical part of the end inside the truncation `S_R`, over one period. -/
private noncomputable def endPiece (q : Puncture) (R : ℝ) : Set (ℝ × ℝ) :=
  {s | 1 ≤ q.endSign * s ∧ q.endSign * s ≤ R} ×ˢ Ico (-1 / 2) (1 / 2)

/-- The end pieces lie in the truncation. -/
private theorem image_endPiece_subset (q : Puncture) {R : ℝ} (hR : 1 ≤ R) :
    endChart q '' endPiece q R ⊆ Complex.equivRealProdCLM.symm ⁻¹' truncation R := by
  rintro _ ⟨z, hz, rfl⟩
  have hz' : (1 ≤ q.endSign * z.1 ∧ q.endSign * z.1 ≤ R) ∧ z.2 ∈ Ico (-1 / 2 : ℝ) (1 / 2) := hz
  have hz₀ : 0 < q.endSign * z.1 := by linarith [hz'.1.1]
  have hS := mem_thricePuncturedSphereReal_iff.1 (endChart_mem_thricePuncturedSphereReal hz₀)
  refine mem_truncation.2 ⟨hS.1, hS.2, fun r => ?_⟩
  by_cases hr : q = r
  · subst hr
    rw [re_endCoord_endChart]
    exact hz'.1.2
  · have h := endSign_mul_re_endCoord_nonpos hr (w := Complex.equivRealProdCLM.symm (endChart q z))
      (by rwa [re_endCoord_endChart])
    linarith

/-- A point of the truncation on the part `±s ≥ 1` of the end `q` lies in its end piece. -/
private theorem mem_image_endPiece {R : ℝ} {z : ℝ × ℝ}
    (hz : z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R) {q : Puncture}
    (hq : 1 ≤ q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re) :
    z ∈ endChart q '' endPiece q R := by
  obtain ⟨hz₀, hz₁, hzR⟩ := mem_truncation.1 hz
  refine ⟨Complex.equivRealProdCLM (q.endCoord (Complex.equivRealProdCLM.symm z)),
    (⟨⟨by simpa using hq, by simpa using hzR q⟩, by simpa using q.im_endCoord_mem_Ico _⟩ :
      _ ∧ _), ?_⟩
  rw [endChart_apply, ContinuousLinearEquiv.symm_apply_apply,
    q.cylindricalEndLift_endCoord (ne_endCenter ⟨hz₀, hz₁⟩ q),
    ContinuousLinearEquiv.apply_symm_apply]

/-- The end pieces of distinct ends are disjoint. -/
private theorem disjoint_image_endPiece {R : ℝ} {q r : Puncture} (hqr : q ≠ r) :
    Disjoint (endChart q '' endPiece q R) (endChart r '' endPiece r R) := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
  have ha' : 1 ≤ q.endSign * a.1 := ha.1.1
  have hb' : 1 ≤ r.endSign * b.1 := hb.1.1
  have h := congrArg Complex.equivRealProdCLM.symm hab
  rw [equivRealProdCLM_symm_endChart, equivRealProdCLM_symm_endChart] at h
  exact cylindricalEndLift_ne_cylindricalEndLift hqr (z := Complex.equivRealProdCLM.symm a)
    (z' := Complex.equivRealProdCLM.symm b) (by simp; linarith) (by simp; linarith) h.symm

omit [FiniteDimensional ℝ V] in
/-- The components of the perturbation in real coordinates are `C¹` jointly in the domain point
of `S` and the target point. -/
private theorem contDiffOn_pairOfPantsPerturbation (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (v : ℂ) :
    ContDiffOn ℝ 1
      (uncurry fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x v)
      (thricePuncturedSphereReal ×ˢ univ) := by
  rintro ⟨z, x⟩ ⟨hz, -⟩
  exact (contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz x v).contDiffWithinAt

/-- **The energy identity over a rectangle of an end.** Over the image in `S` of a rectangle
`[a₁, b₁] × [-1/2, 1/2)` of the part `±s > 1/2` of the end `q`, the Floer energy is the
symplectic area, plus the integrals of the Hamiltonian term `β(±s - 1) H_q(t)` over the outgoing
boundary circle minus the incoming one, minus the integrated curvature. -/
private theorem integral_floerEnergyDensity_image_endChart (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u thricePuncturedSphereReal)
    {q : Puncture} {a₁ b₁ : ℝ} (hab : a₁ ≤ b₁) (ha : 1 / 2 < q.endSign * a₁)
    (hb : 1 / 2 < q.endSign * b₁) :
    ∫ z in endChart q '' (Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2)), ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in endChart q '' (Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2)),
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) +
        ((∫ t in (-1 / 2 : ℝ)..1 / 2,
            smoothTransition (q.endSign * b₁ - 1) * H q t (u (endChart q (b₁, t)))) -
          ∫ t in (-1 / 2 : ℝ)..1 / 2,
            smoothTransition (q.endSign * a₁ - 1) * H q t (u (endChart q (a₁, t)))) -
        ∫ z in endChart q '' (Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2)), ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  set s : Set (ℝ × ℝ) := Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2)
  set U : Set (ℝ × ℝ) := {z | 1 / 2 < q.endSign * z.1}
  have hUo : IsOpen U := isOpen_lt continuous_const (continuous_const.mul continuous_fst)
  -- The rectangle lies in the part `±s > 1/2` of the end.
  have hU₁ {z : ℝ × ℝ} (hz : z.1 ∈ Icc a₁ b₁) : 1 / 2 < q.endSign * z.1 := by
    obtain ⟨h₁, h₂⟩ := hz
    rcases endSign_eq_one_or_eq_neg_one q with h | h <;> rw [h] at ha hb ⊢ <;> linarith
  have hIccU : Icc ((a₁, -1 / 2) : ℝ × ℝ) (b₁, 1 / 2) ⊆ U := fun z hz => hU₁ (by
    rw [Icc_prod_eq] at hz
    exact hz.1)
  have hsU : s ⊆ U := fun z hz => hIccU (by
    rw [Icc_prod_eq]
    exact ⟨hz.1, Ico_subset_Icc_self hz.2⟩)
  have hpos {z : ℝ × ℝ} (hz : z ∈ U) : 0 < q.endSign * z.1 := by
    have h : 1 / 2 < q.endSign * z.1 := hz
    linarith
  have hS {z : ℝ × ℝ} (hz : z ∈ U) := endChart_mem_thricePuncturedSphereReal (hpos hz)
  have hmeas : MeasurableSet s := measurableSet_Icc.prod measurableSet_Ico
  have hinj : InjOn (endChart q) s :=
    (injOn_endChart q).mono fun z hz => mem_endStrip_iff.2 ⟨hsU hz, hz.2⟩
  have hφ (w : ℝ × ℝ) : DifferentiableAt ℝ (endChart q) w :=
    (hasFDerivAt_endChart q w).differentiableAt
  have hud {w : ℝ × ℝ} (hw : w ∈ U) : DifferentiableAt ℝ u (endChart q w) :=
    (hu.differentiableOn one_ne_zero _ (hS hw)).differentiableAt
      (isOpen_thricePuncturedSphereReal.mem_nhds (hS hw))
  -- Change variables to the cylinder coordinates of the end, in each of the three integrals.
  have harea := ω.integral_floerEnergyDensity_image (Ks := fun _ _ ↦ 0) (Kt := fun _ _ ↦ 0)
    hmeas hinj (fun w _ => hφ w) (fun w _ => det_fderiv_endChart_nonneg q w)
    (fun w hw => hud (hsU hw)) (fun _ _ => differentiableAt_const _)
    (fun _ _ => differentiableAt_const _)
  have h₀ (v : ℝ × ℝ) : perturbationPullback (endChart q) (fun (_ : ℝ × ℝ) (_ : V) ↦ (0 : ℝ))
      (fun _ _ ↦ 0) v = fun _ _ ↦ 0 := by
    funext w x
    simp [perturbationPullback_apply]
  simp only [h₀, floerEnergyDensity_zero] at harea
  rw [harea, ω.integral_floerEnergyDensity_image hmeas hinj (fun w _ => hφ w)
      (fun w _ => det_fderiv_endChart_nonneg q w) (fun w hw => hud (hsU hw))
      (fun w hw => differentiableAt_pairOfPantsPerturbation_target hH hHs (hS (hsU hw)) _ 1)
      (fun w hw => differentiableAt_pairOfPantsPerturbation_target hH hHs (hS (hsU hw)) _ _),
    ω.integral_hamiltonianCurvature_image hmeas hinj
      (fun w _ => (contDiff_endChart q 2).contDiffAt)
      (fun w _ => det_fderiv_endChart_nonneg q w)
      (fun w hw => differentiableAt_pairOfPantsPerturbation_domain hH hHs (hS (hsU hw)) _ 1)
      (fun w hw => differentiableAt_pairOfPantsPerturbation_domain hH hHs (hS (hsU hw)) _ _)
      (fun w hw => differentiableAt_pairOfPantsPerturbation_target hH hHs (hS (hsU hw)) _ 1)
      (fun w hw => differentiableAt_pairOfPantsPerturbation_target hH hHs (hS (hsU hw)) _ _),
    perturbationPullback_endChart, perturbationPullback_endChart,
    equivRealProdCLM_symm_stdComplexLineReal, equivRealProdCLM_symm_stdComplexLineImag]
  -- The half-open strip and the closed rectangle differ by a null set.
  have hae : s =ᵐ[volume] Icc ((a₁, -1 / 2) : ℝ × ℝ) (b₁, 1 / 2) := by
    rw [Icc_prod_eq, Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq (ae_eq_refl _) Ico_ae_eq_Icc
  simp only [setIntegral_congr_set hae]
  -- In the cylinder coordinates the datum is `β(±s - 1) H_q(t) dt`: apply the energy identity on
  -- the rectangle.
  have hu' : ContDiffOn ℝ 1 (u ∘ endChart q) U :=
    hu.comp (contDiff_endChart q 1).contDiffOn fun w hw => hS hw
  have hKs : ContDiffOn ℝ 1 (uncurry (pairOfPantsEndComponent H q 1)) (U ×ˢ univ) :=
    (contDiffOn_const (c := (0 : ℝ))).congr fun p hp =>
      pairOfPantsEndComponent_one_of_pos (hH q) (hpos hp.1) p.2
  have hβH : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V =>
      smoothTransition (q.endSign * p.1.1 - 1) * H q p.1.2 p.2 :=
    (smoothTransition.contDiff.comp (f := fun p : (ℝ × ℝ) × V => q.endSign * p.1.1 - 1)
      (by fun_prop)).mul ((hHs q).comp (f := fun p : (ℝ × ℝ) × V => (p.1.2, p.2)) (by fun_prop))
  have hKt : ContDiffOn ℝ 1 (uncurry (pairOfPantsEndComponent H q Complex.I)) (U ×ˢ univ) :=
    hβH.contDiffOn.congr fun p hp => pairOfPantsEndComponent_I_of_pos (hH q) (hpos hp.1) p.2
  have hrect := ω.integral_floerEnergyDensity hUo hu' hKs hKt
    (Prod.mk_le_mk.2 ⟨hab, by norm_num⟩) hIccU
  simp only [Function.comp_apply] at hrect
  rw [hrect]
  -- The `ds` components vanish, and the `dt` components are `β(±s - 1) H_q(t)`.
  have hs₀ (c : ℝ) : ∫ s in a₁..b₁, pairOfPantsEndComponent H q 1 (s, c) (u (endChart q (s, c))) =
      0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => 0) fun s hs => ?_,
      intervalIntegral.integral_zero]
    rw [uIcc_of_le hab] at hs
    exact pairOfPantsEndComponent_one_of_pos (hH q) (hpos (hU₁ (z := (s, c)) hs)) _
  have ht {c : ℝ} (hc : 1 / 2 < q.endSign * c) :
      ∫ t in (-1 / 2 : ℝ)..1 / 2,
          pairOfPantsEndComponent H q Complex.I (c, t) (u (endChart q (c, t))) =
        ∫ t in (-1 / 2 : ℝ)..1 / 2,
          smoothTransition (q.endSign * c - 1) * H q t (u (endChart q (c, t))) :=
    intervalIntegral.integral_congr fun t _ =>
      pairOfPantsEndComponent_I_of_pos (hH q) (by linarith : 0 < q.endSign * c) _
  rw [hs₀, hs₀, ht ha, ht hb]
  ring

/-- **The energy identity on an end piece.** Over the end piece `1 ≤ ±s ≤ R` of the end `q`, the
Floer energy is the symplectic area, plus `±β(R - 1)` times the integral of `H_q(t)` over the
boundary circle `±s = R`, minus the integrated curvature. -/
private theorem integral_floerEnergyDensity_image_endPiece (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u thricePuncturedSphereReal)
    {R : ℝ} (hR : 1 ≤ R) (q : Puncture) :
    ∫ z in endChart q '' endPiece q R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in endChart q '' endPiece q R,
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) +
        smoothTransition (R - 1) *
          (q.endSign * ∫ t in (-1 / 2 : ℝ)..1 / 2, H q t (u (endChart q (q.endSign * R, t)))) -
        ∫ z in endChart q '' endPiece q R, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  rcases endSign_eq_one_or_eq_neg_one q with h | h
  · have hpiece : endPiece q R = Icc 1 R ×ˢ Ico (-1 / 2) (1 / 2) := by
      ext ⟨s, t⟩
      simp [endPiece, h]
    rw [hpiece, integral_floerEnergyDensity_image_endChart ω hH hHs hu hR
      (by rw [h]; norm_num) (by rw [h]; linarith)]
    simp only [h, one_mul, sub_self, smoothTransition.zero, zero_mul,
      intervalIntegral.integral_zero, sub_zero, intervalIntegral.integral_const_mul]
  · have hpiece : endPiece q R = Icc (-R) (-1) ×ˢ Ico (-1 / 2) (1 / 2) := by
      ext ⟨s, t⟩
      simp only [endPiece, h, mem_prod, mem_ofPred_eq, mem_Icc]
      constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃⟩ <;> exact ⟨⟨by linarith, by linarith⟩, h₃⟩
    rw [hpiece, integral_floerEnergyDensity_image_endChart ω hH hHs hu (by linarith)
      (by rw [h]; linarith) (by rw [h]; norm_num)]
    simp only [h, neg_mul, one_mul, neg_neg, sub_self, smoothTransition.zero, zero_mul,
      intervalIntegral.integral_zero, zero_sub, intervalIntegral.integral_const_mul]
    ring

/-- The Floer energy density, the symplectic area density and the curvature of the pair-of-pants
perturbation, along a map that is `C¹` on `S`, are integrable over every truncation. -/
private theorem integrableOn_truncation (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u thricePuncturedSphereReal) (R : ℝ) :
    IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        (Complex.equivRealProdCLM.symm ⁻¹' truncation R) ∧
      IntegrableOn (fun z ↦ ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag))
        (Complex.equivRealProdCLM.symm ⁻¹' truncation R) ∧
      IntegrableOn (fun z ↦ ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z))
        (Complex.equivRealProdCLM.symm ⁻¹' truncation R) := by
  have hT : IsCompact (Complex.equivRealProdCLM.symm ⁻¹' truncation R) :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_truncation R)
  have hTS : Complex.equivRealProdCLM.symm ⁻¹' truncation R ⊆ thricePuncturedSphereReal :=
    fun z hz =>
      mem_thricePuncturedSphereReal_iff.2 ⟨(mem_truncation.1 hz).1, (mem_truncation.1 hz).2.1⟩
  have hKs := contDiffOn_pairOfPantsPerturbation hH hHs 1
  have hKt := contDiffOn_pairOfPantsPerturbation hH hHs Complex.I
  have hdu := hu.continuousOn_fderiv_of_isOpen isOpen_thricePuncturedSphereReal le_rfl
  refine ⟨?_, ?_, ?_⟩
  · exact ((ω.continuousOn_floerEnergyDensity isOpen_thricePuncturedSphereReal hu hKs hKt).mono
      hTS).integrableOn_compact hT
  · exact ((ω.continuousOn_apply_comp (hdu.clm_apply continuousOn_const)
      (hdu.clm_apply continuousOn_const)).mono hTS).integrableOn_compact hT
  · exact ((ω.continuousOn_hamiltonianCurvature_comp isOpen_thricePuncturedSphereReal
      hu.continuousOn hKs hKt).mono hTS).integrableOn_compact hT

/-- **The energy identity on the truncated pair of pants.** Let `K` be the pair-of-pants
perturbation of period-one `C¹` Hamiltonians `H_q` on the three ends of `S = ℂ ∖ {0, 1}`, with
components `K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`,
and let `u` be a map which is `C¹` on `S`. For `R ≥ 1`, over the truncation `S_R` of `S` the Floer
energy of `u` is its symplectic area, plus `β(R - 1)` times the signed sum over the three ends of
the integrals of `H_q(t)` along the boundary circles `±s = R`, minus the integrated curvature:

`∫_{S_R} E = ∫_{S_R} u^*ω + β(R - 1) ∑ q, ±∫₀¹ H_q(t, u(φ_q(±R + i t))) dt - ∫_{S_R} R_K(u)`.

Here `φ_q` is the end lift of `q`, the sign is `+` on the input ends `0` and `1` and `-` on the
output end `∞`, and `β = smoothTransition` is the cutoff of the perturbation, so `β(R - 1) = 1`
for `R ≥ 2`. -/
theorem integral_floerEnergyDensity_pairOfPantsPerturbation_truncation (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u thricePuncturedSphereReal)
    {R : ℝ} (hR : 1 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R,
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) +
        smoothTransition (R - 1) * (∑ q, q.endSign * ∫ t in (0 : ℝ)..1,
          H q t (u (Complex.equivRealProdCLM
            (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  set T := Complex.equivRealProdCLM.symm ⁻¹' truncation R
  set A : Puncture → Set (ℝ × ℝ) := fun q => endChart q '' endPiece q R
  set C := T \ ⋃ q, A q
  obtain ⟨hE, harea, hcurv⟩ := integrableOn_truncation ω hH hHs hu R
  -- The truncation is the disjoint union of its core `C`, where every `±s < 1`, and the three
  -- end pieces.
  have hTm : MeasurableSet T :=
    (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
      (isCompact_truncation R)).isClosed.measurableSet
  have hAm (q : Puncture) : MeasurableSet (A q) :=
    measurable_image_of_fderivWithin
      ((measurableSet_le measurable_const (measurable_const.mul measurable_id)).inter
        (measurableSet_le (measurable_const.mul measurable_id) measurable_const) |>.prod
        measurableSet_Ico)
      (fun w _ => (hasFDerivAt_endChart q w).hasFDerivWithinAt)
      ((injOn_endChart q).mono fun z hz => by
        have h : 1 ≤ q.endSign * z.1 := hz.1.1
        exact mem_endStrip_iff.2 ⟨by linarith, hz.2⟩)
  have hAT (q : Puncture) : A q ⊆ T := image_endPiece_subset q hR
  have hAd : Pairwise (Disjoint on A) := fun q r hqr => disjoint_image_endPiece hqr
  have hsplit (f : ℝ × ℝ → ℝ) (hf : IntegrableOn f T) :
      ∫ z in T, f z = (∫ z in C, f z) + ∑ q, ∫ z in A q, f z := by
    have hTC : T = C ∪ ⋃ q, A q := (sdiff_union_of_subset (iUnion_subset hAT)).symm
    conv_lhs => rw [hTC]
    rw [setIntegral_union disjoint_sdiff_left (MeasurableSet.iUnion hAm)
      (hf.mono_set sdiff_subset) (hf.mono_set (iUnion_subset hAT)),
      integral_iUnion_fintype hAm hAd fun q => hf.mono_set (hAT q)]
  -- On the core the perturbation vanishes nearby, so the energy is the area and the curvature
  -- vanishes.
  have hcore {z : ℝ × ℝ} (hz : z ∈ C) :
      ∀ q : Puncture, q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re < 1 := by
    intro q
    by_contra! h
    exact hz.2 (mem_iUnion.2 ⟨q, mem_image_endPiece hz.1 h⟩)
  have hCm : MeasurableSet C := hTm.diff (MeasurableSet.iUnion hAm)
  have hCE : ∫ z in C, ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      ∫ z in C, ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) := by
    refine setIntegral_congr_fun hCm fun z hz => ?_
    have hK : pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) = fun _ => 0 :=
      funext (pairOfPantsPerturbation_eq_zero_of_forall_le fun q ↦ (hcore hz q).le)
    simp [floerEnergyDensity_def, perturbedFDeriv_apply_stdComplexLineReal,
      perturbedFDeriv_apply_stdComplexLineImag, hK]
  have hCR : ∫ z in C, ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun z hz =>
      hamiltonianCurvature_pairOfPantsPerturbation_eq_zero ω
        (mem_thricePuncturedSphereReal_iff.2
          ⟨(mem_truncation.1 hz.1).1, (mem_truncation.1 hz.1).2.1⟩)
        (hcore hz) _
  -- The boundary circles: by periodicity, integrate over `[0, 1]` instead of `[-1/2, 1/2]`.
  have hcircle (q : Puncture) :
      ∫ t in (-1 / 2 : ℝ)..1 / 2, H q t (u (endChart q (q.endSign * R, t))) =
        ∫ t in (0 : ℝ)..1, H q t (u (Complex.equivRealProdCLM
          (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) := by
    have hper : Periodic (fun t : ℝ => H q t (u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) 1 := fun t => by
      simp only [q.periodic_cylindricalEndLift (q.endSign * R) t, hH q t]
    have h := Function.Periodic.intervalIntegral_add_eq hper (-1 / 2) 0
    norm_num at h
    simp only [endChart_apply, Complex.equivRealProdCLM_symm_apply]
    convert h using 1 <;> norm_num
  rw [hsplit _ hE, hsplit _ harea, hsplit _ hcurv, hCE, hCR,
    Finset.sum_congr rfl fun q _ => integral_floerEnergyDensity_image_endPiece ω hH hHs hu hR q,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [hcircle]
  ring

/-- **The energy bound on the truncated pair of pants.** If the end Hamiltonians are bounded,
`|H_q| ≤ B_q`, then for every `R ≥ 1` the Floer energy over the truncation `S_R` differs from the
symplectic area plus the Hamiltonian boundary terms by at most `B₀ + B₁ + B_∞`, uniformly in `R`.
-/
theorem abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_le
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u thricePuncturedSphereReal)
    {R : ℝ} (hR : 1 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R,
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) -
        smoothTransition (R - 1) * (∑ q, q.endSign * ∫ t in (0 : ℝ)..1,
          H q t (u (Complex.equivRealProdCLM
            (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))))| ≤ ∑ q, B q := by
  have hsub (a b c : ℝ) : a + b - c - a - b = -c := by ring
  rw [integral_floerEnergyDensity_pairOfPantsPerturbation_truncation ω hH hHs hu hR, hsub,
    abs_neg]
  have hB₀ (q : Puncture) : 0 ≤ B q := (abs_nonneg _).trans (hB q 0 0)
  rw [← ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun q _ => hB₀ q),
    ← Real.enorm_eq_ofReal_abs, ENNReal.ofReal_sum_of_nonneg fun q _ => hB₀ q]
  exact (enorm_integral_le_lintegral_enorm _).trans ((setLIntegral_le_lintegral _ _).trans
    (lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le ω hH hHs hB u))

end SymplecticForm

end TauCeti
