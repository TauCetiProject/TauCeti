/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.CoreChart
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Complex.CircleMap
import TauCeti.Geometry.Manifold.ContMDiff.Fract
import TauCeti.MeasureTheory.Integral.Circle.Integral
import TauCeti.MeasureTheory.Integral.PolarCoord
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Topology.MetricSpace.Annulus
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The truncated pair of pants through charts ending at its end loops

For `R ≥ 0` the truncation `S_R = TauCeti.ThricePuncturedSphere.truncation R` of the pair of pants
`S = ℂ ∖ {0, 1}` is the truncation `S₀` at the height `0` together with the annuli of its three
cylindrical ends between the heights `0` and `R`. The energy identity of a Floer pair of pants is
read off on `S_R` through the loops of a map `u` along the circles of the ends at the height `R`,
parametrized by the end charts `TauCeti.Floer.endChart`: the action terms of the inputs at
`t ↦ u (endChart q (R, t))` and of the output at `t ↦ u (endChart ∞ (-R, t))`. This file presents
`S_R` by charts whose boundary circles run through exactly these end loops, and computes the
integral of a two-form over `u` along each of them, so that the topological term `∫_{S_R} u^* φ`
becomes a sum of integrals over `u` composed with these charts, to whose boundary loops caps of the
end loops can be glued.

* **The end annuli.** The end chart of the end `q` on `[a, b] × [0, 1]`, for heights `a ≤ b` in
  the end, sweeps the closed annulus about the center `c_q` of the end between the radii
  `‖b_q‖ exp (-2π b)` and `‖b_q‖ exp (-2π a)`. The end lift is holomorphic, so the end chart
  preserves orientation, and the integral of `φ` over `u ∘ endChart q` is the integral of `u^* φ`
  over that annulus (`TauCeti.Floer.rectangleIntegral_comp_endChart`). The proof computes the
  Jacobian `4π² ρ²` of the end chart and passes to polar coordinates about `c_q`.
* **The output chart.** The core chart `TauCeti.Floer.pairOfPantsCoreChart` ends at the output
  circle `‖w‖ = 2`, run through at the speed of the angle about `1/2`, while the end loop of the
  output at the height `0` runs through the same circle at constant speed from the point `2`. A
  *turn* within the output circle joins the two parametrizations: the point of the output circle
  on the ray from `1/2` at the angle `θ` has the angle `θ + arg (ρ_out θ + exp (-iθ) / 2)` about
  `0`, for the outer radius `ρ_out = TauCeti.Floer.pairOfPantsOuterRadius`, and the turn
  interpolates this angle linearly to the angle `-2π t` of the end loop. It factors through the
  output circle, a curve, so it has no area (`TauCeti.rectangleIntegral_comp_eq_zero`). The
  **output chart** `TauCeti.Floer.pairOfPantsOutputChart R` is the core chart followed by the turn
  and by the annulus of the output end out to the height `R`. It is a smooth cylinder chart from
  the collared concatenation of the end loops of the inputs at the height `0`
  (`TauCeti.Floer.pairOfPantsOutputChart_mk_zero`) to the end loop of the output at the height `R`
  (`TauCeti.Floer.pairOfPantsOutputChart_mk_one`), so that `u` composed with it is a cylinder for
  every `C²` map `u` (`TauCeti.Floer.isLoopCylinder_comp_pairOfPantsOutputChart`). The integral of
  `φ` over it is minus the integral of `u^* φ` over `S₀` and the annulus `2 ≤ ‖w‖ ≤ 2 exp (2πR)`
  (`TauCeti.Floer.rectangleIntegral_comp_pairOfPantsOutputChart`).
* **The area of `S_R`.** Consequently the integral of `u^* φ` over `S_R` is the sum of the
  integrals over `u ∘ endChart 0` and `u ∘ endChart 1` on `[0, R] × [0, 1]` minus the integral over
  `u` composed with the output chart
  (`TauCeti.Floer.setIntegral_truncation_eq_rectangleIntegral`): the pieces meet only along circles,
  which are null sets.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the pair-of-pants product and the energy of its solutions.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on
  capped orbits and the action of glued caps.
-/

public section

open Set Real Function MeasureTheory Manifold TauCeti.ThricePuncturedSphere
open scoped Interval

namespace TauCeti.Floer

variable {E HM M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### The annuli of the ends -/

/-- The radius `‖b_q‖ exp (-2π x)` of the circle of the end `q` at the height `x`, about the
center of the end. -/
private noncomputable def endRadius (q : Puncture) (x : ℝ) : ℝ :=
  ‖q.endScale‖ * Real.exp (-(2 * π * x))

private theorem endRadius_pos (q : Puncture) (x : ℝ) : 0 < endRadius q x :=
  mul_pos (norm_pos_iff.2 q.endScale_ne_zero) (Real.exp_pos _)

/-- The circle of the output end at the height `0` is the output circle `‖w‖ = 2`. -/
private theorem endRadius_inf_zero : endRadius .inf 0 = 2 := by simp [endRadius]

private theorem endRadius_le_endRadius_iff (q : Puncture) {x y : ℝ} :
    endRadius q x ≤ endRadius q y ↔ y ≤ x := by
  rw [endRadius, endRadius, mul_le_mul_iff_right₀ (norm_pos_iff.2 q.endScale_ne_zero),
    Real.exp_le_exp, neg_le_neg_iff, mul_le_mul_iff_right₀ Real.two_pi_pos]

/-- Every positive radius is the radius of the circle of the end at some height. -/
private theorem endRadius_neg_log_div (q : Puncture) {r : ℝ} (hr : 0 < r) :
    endRadius q (-Real.log (r / ‖q.endScale‖) / (2 * π)) = r := by
  have hb := norm_pos_iff.2 q.endScale_ne_zero
  rw [endRadius, mul_div_cancel₀ _ Real.two_pi_pos.ne', neg_neg,
    Real.exp_log (div_pos hr hb), mul_div_cancel₀ _ hb.ne']

private theorem hasDerivAt_endRadius (q : Puncture) (x : ℝ) :
    HasDerivAt (endRadius q) (-(2 * π) * endRadius q x) x := by
  have h := ((hasDerivAt_id x).const_mul (-(2 * π))).exp.const_mul ‖q.endScale‖
  convert h using 1
  · funext y
    simp [endRadius, neg_mul]
  · simp only [endRadius, id, mul_one, neg_mul]
    ring

/-- In complex coordinates the end chart runs clockwise around the circle of radius
`endRadius q x` about the center of the end. -/
private theorem equivRealProdCLM_symm_endChart_mk (q : Puncture) (x t : ℝ) :
    Complex.equivRealProdCLM.symm (endChart q (x, t)) =
      circleMap q.endCenter (endRadius q x) (Complex.arg q.endScale - 2 * π * t) := by
  rw [equivRealProdCLM_symm_endChart, Complex.equivRealProdCLM_symm_apply,
    Puncture.cylindricalEndLift_ofReal_add_ofReal_mul_I, endRadius]

/-- The Jacobian determinant of the end chart at the height `x` is `4π² endRadius q x ²`. -/
private theorem det_fderiv_endChart_eq_endRadius (q : Puncture) (z : ℝ × ℝ) :
    (fderiv ℝ (endChart q) z).det = 4 * π ^ 2 * endRadius q z.1 ^ 2 := by
  rw [det_fderiv_endChart, equivRealProdCLM_symm_endChart_mk,
    norm_circleMap_sub_center _ (endRadius_pos q _).le]

/-- A height between two heights of the end `q` with `±x ≥ 0` has `±x ≥ 0`. -/
private theorem endSign_mul_nonneg_of_mem_uIcc {q : Puncture} {a b x : ℝ}
    (ha : 0 ≤ q.endSign * a) (hb : 0 ≤ q.endSign * b) (hx : x ∈ [[a, b]]) :
    0 ≤ q.endSign * x := by
  rcases mem_uIcc.1 hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
    cases q <;> simp only [Puncture.endSign_zero, Puncture.endSign_one, Puncture.endSign_inf,
      one_mul, neg_one_mul, neg_nonneg] at ha hb ⊢ <;> linarith

/-- The point of the circle of the end `q` at the height `x` at the angle `θ` about the center of
the end is a point of the end chart. -/
private theorem equivRealProdCLM_circleMap_endRadius (q : Puncture) (x θ : ℝ) :
    Complex.equivRealProdCLM (circleMap q.endCenter (endRadius q x) θ) =
      endChart q (x, (Complex.arg q.endScale - θ) / (2 * π)) := by
  rw [← Complex.equivRealProdCLM.apply_symm_apply (endChart q _),
    equivRealProdCLM_symm_endChart_mk]
  congr 2
  field_simp
  ring

/-- **The pullback along a reparametrized end chart.** Along `(x, t) ↦ u (φ_q (σ x + i t))`, the
pullback of a two-form on the coordinate vectors is `σ' (x)` times the Jacobian
`4π² endRadius q (σ x)²` of the end chart times the pullback along `u` at the image point. -/
private theorem mpullback_comp_endChart_prodMap_apply (φ : RoughForm I M F 2) {u : ℝ × ℝ → M}
    (q : Puncture) {σ : ℝ → ℝ} {σ' x : ℝ} (hσ : HasDerivAt σ σ' x) (t : ℝ)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (endChart q (σ x, t))) :
    mpullback 𝓘(ℝ, ℝ × ℝ) I (u ∘ endChart q ∘ Prod.map σ id) φ (x, t) ![(1, 0), (0, 1)] =
      (σ' * (4 * π ^ 2 * endRadius q (σ x) ^ 2)) •
        mpullback 𝓘(ℝ, ℝ × ℝ) I u φ (endChart q (σ x, t)) ![(1, 0), (0, 1)] := by
  have hL : HasFDerivAt (endChart q) (fderiv ℝ (endChart q) (σ x, t)) (σ x, t) :=
    ((contDiff_endChart q 1).differentiable one_ne_zero _).hasFDerivAt
  rw [← Function.comp_assoc, mpullback_comp_prodMap_apply φ hσ (hasDerivAt_id t)
      (hu.comp _ hL.differentiableAt.mdifferentiableAt), id,
    mpullback_comp_apply_eq_det_smul φ hL hu, det_fderiv_endChart_eq_endRadius, smul_smul,
    mul_one]

variable [IsManifold I 1 M]

/-- **Polar coordinates on an annulus of the pair of pants.** For a map `u` which is `C¹` on `S` and
an annulus `r₁ ≤ ‖w - c‖ ≤ r₂` in `S`, the integral of `u^* φ` over the annulus is the integral
in the radius of `r` times the integral of `u^* φ` around the circle of radius `r`. -/
private theorem integral_annulus_eq_intervalIntegral {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 0 φ) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {c : ℂ} {r₁ r₂ : ℝ}
    (h₀ : 0 ≤ r₁) (h₁₂ : r₁ ≤ r₂)
    (hS : ∀ r ∈ Icc r₁ r₂, ∀ θ, Complex.equivRealProdCLM (circleMap c r θ) ∈
      thricePuncturedSphereReal) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' {w | r₁ ≤ ‖w - c‖ ∧ ‖w - c‖ ≤ r₂},
        φ (u z) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (1, 0), mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (0, 1)] =
      ∫ r in r₁..r₂, r • ∫ θ in -π..π,
        φ (u (Complex.equivRealProdCLM (circleMap c r θ)))
          ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u (Complex.equivRealProdCLM (circleMap c r θ)) (1, 0),
            mfderiv 𝓘(ℝ, ℝ × ℝ) I u (Complex.equivRealProdCLM (circleMap c r θ)) (0, 1)] := by
  set f : ℝ × ℝ → F :=
    fun z ↦ φ (u z) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (1, 0), mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (0, 1)]
  have hf : ContinuousOn f thricePuncturedSphereReal :=
    hφ.continuousOn_apply_mfderiv isOpen_thricePuncturedSphereReal hu _ _
  set A := {w : ℂ | r₁ ≤ ‖w - c‖ ∧ ‖w - c‖ ≤ r₂}
  -- Every point of the annulus is a point of one of its circles, so the annulus lies in `S`.
  have hA : MapsTo Complex.equivRealProdCLM A thricePuncturedSphereReal := fun w hw ↦ by
    have h := hS ‖w - c‖ hw (Complex.arg (w - c))
    rwa [circleMap, Complex.norm_mul_exp_arg_mul_I, add_sub_cancel] at h
  rw [Complex.setIntegral_preimage_equivRealProdCLM_symm]
  exact integral_annulus_eq_integral_circleMap h₀ h₁₂
    ((hf.comp Complex.equivRealProdCLM.continuous.continuousOn hA).integrableOn_compact
      (isCompact_setOf_le_norm_sub_le c r₁ r₂))

/-- The integral of a function continuous on `S` around the circles of radius `r` about `c` is
continuous in `r` on a set of radii whose circles lie in `S`. -/
private theorem continuousOn_intervalIntegral_circleMap {f : ℝ × ℝ → F}
    (hf : ContinuousOn f thricePuncturedSphereReal) {c : ℂ} {K : Set ℝ}
    (hK : ∀ r ∈ K, ∀ θ, Complex.equivRealProdCLM (circleMap c r θ) ∈ thricePuncturedSphereReal) :
    ContinuousOn (fun r ↦ ∫ θ in -π..π, f (Complex.equivRealProdCLM (circleMap c r θ))) K := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (r : K) θ ↦ f (Complex.equivRealProdCLM (circleMap c r θ))) ?_ (-π) π
  exact hf.comp_continuous (Complex.equivRealProdCLM.continuous.comp
    ((continuous_circleMap_uncurry c).comp (continuous_subtypeVal.prodMap continuous_id)))
    fun p ↦ hK p.1 p.1.property p.2

/-- The derivative `-2π endRadius q (σ x) σ' (x)` of the radius along a `C¹` reparametrization
`σ` of the heights is continuous. -/
private theorem continuous_mul_endRadius_mul_deriv (q : Puncture) {σ : ℝ → ℝ}
    (hσ : ContDiff ℝ 1 σ) : Continuous fun x ↦ -(2 * π) * endRadius q (σ x) * deriv σ x := by
  have := hσ.continuous_deriv le_rfl
  have := hσ.continuous
  unfold endRadius
  fun_prop

/-- **The integral along a reparametrized end chart, in the radius.** Let `u` be `C¹` on `S` and
`σ` a `C¹` reparametrization of the heights with `±σ ≥ 0` on `[a, b]`, so that the circles of the
end `q` at the heights `σ x` lie in the end. The integral of `φ` over
`(x, t) ↦ u (φ_q (σ x + i t))` on `[a, b] × [0, 1]` is the integral, between the radii of the
circles at the heights `σ b` and `σ a`, of `r` times the integral of `u^* φ` around the circle of
radius `r`. -/
private theorem rectangleIntegral_comp_endChart_prodMap {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 0 φ) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) (q : Puncture) {σ : ℝ → ℝ}
    (hσ : ContDiff ℝ 1 σ) {a b : ℝ} (hσS : ∀ x ∈ [[a, b]], 0 ≤ q.endSign * σ x) :
    rectangleIntegral φ (u ∘ endChart q ∘ Prod.map σ id) (a, 0) (b, 1) =
      ∫ r in endRadius q (σ b)..endRadius q (σ a), r • ∫ θ in -π..π,
        φ (u (Complex.equivRealProdCLM (circleMap q.endCenter r θ)))
          ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u (Complex.equivRealProdCLM (circleMap q.endCenter r θ)) (1, 0),
            mfderiv 𝓘(ℝ, ℝ × ℝ) I u (Complex.equivRealProdCLM (circleMap q.endCenter r θ))
              (0, 1)] := by
  set c := q.endCenter
  set α := Complex.arg q.endScale
  set f : ℝ × ℝ → F :=
    fun z ↦ φ (u z) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (1, 0), mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (0, 1)]
  have hf : ContinuousOn f thricePuncturedSphereReal :=
    hφ.continuousOn_apply_mfderiv isOpen_thricePuncturedSphereReal hu _ _
  -- The integral of `u^* φ` around the circle of radius `r`.
  set A : ℝ → F := fun r ↦ ∫ θ in -π..π, f (Complex.equivRealProdCLM (circleMap c r θ))
  set F₀ : ℝ → ℝ := fun x ↦ endRadius q (σ x)
  have hσd (x : ℝ) : HasDerivAt σ (deriv σ x) x :=
    (hσ.differentiable one_ne_zero x).hasDerivAt
  have hF₀ (x : ℝ) : HasDerivAt F₀ (-(2 * π) * endRadius q (σ x) * deriv σ x) x :=
    (hasDerivAt_endRadius q (σ x)).comp x (hσd x)
  have hmem {x : ℝ} (hx : x ∈ [[a, b]]) (t : ℝ) :
      endChart q (σ x, t) ∈ thricePuncturedSphereReal :=
    endChart_mem_thricePuncturedSphereReal (z := (σ x, t)) (hσS x hx)
  -- On the rectangle the integrand is `σ' · 4π² ρ²` times `u^* φ` on the circle of radius `ρ`.
  have hpt {x : ℝ} (hx : x ∈ [[a, b]]) (t : ℝ) :
      mpullback 𝓘(ℝ, ℝ × ℝ) I (u ∘ endChart q ∘ Prod.map σ id) φ (x, t) ![(1, 0), (0, 1)] =
        (deriv σ x * (4 * π ^ 2 * F₀ x ^ 2)) •
          f (Complex.equivRealProdCLM (circleMap c (F₀ x) (α - 2 * π * t))) := by
    rw [mpullback_comp_endChart_prodMap_apply φ q (hσd x) t ((hu.contMDiffAt
        (isOpen_thricePuncturedSphereReal.mem_nhds (hmem hx t))).mdifferentiableAt one_ne_zero),
      ← equivRealProdCLM_symm_endChart_mk, ContinuousLinearEquiv.apply_symm_apply]
    exact congrArg _ (mpullback_apply_pair u φ _ _ _)
  -- Integrating over `t` gives `σ' · 2π ρ²` times the integral `A ρ` around the circle.
  have hinner {x : ℝ} (hx : x ∈ [[a, b]]) :
      ∫ t in (0 : ℝ)..1,
        mpullback 𝓘(ℝ, ℝ × ℝ) I (u ∘ endChart q ∘ Prod.map σ id) φ (x, t) ![(1, 0), (0, 1)] =
        (-(2 * π) * endRadius q (σ x) * deriv σ x) • (-(F₀ x • A (F₀ x))) := by
    rw [intervalIntegral.integral_congr fun t _ ↦ hpt hx t, intervalIntegral.integral_smul,
      intervalIntegral_circleMap_sub_mul (g := fun w ↦ f (Complex.equivRealProdCLM w)), smul_smul,
      smul_neg, smul_smul, ← neg_smul]
    congr 1
    field_simp
    ring
  -- The integrals around the circles depend continuously on the radius.
  have hA : ContinuousOn (fun r ↦ -(r • A r)) (F₀ '' [[a, b]]) := by
    refine (continuousOn_id.smul (continuousOn_intervalIntegral_circleMap hf fun r hr θ ↦ ?_)).neg
    obtain ⟨x, hx, rfl⟩ := hr
    rw [equivRealProdCLM_circleMap_endRadius]
    exact hmem hx _
  have hsub := intervalIntegral.integral_deriv_smul_comp' (fun x _ ↦ hF₀ x)
    (continuous_mul_endRadius_mul_deriv q hσ).continuousOn hA
  simp only [Function.comp_def] at hsub
  rw [rectangleIntegral_def, intervalIntegral.integral_congr fun x hx ↦ hinner hx, hsub,
    intervalIntegral.integral_neg, ← intervalIntegral.integral_symm]

/-- The circles of the end `q` between the heights `a` and `b` with `±a, ±b ≥ 0` lie in `S`. -/
private theorem equivRealProdCLM_circleMap_mem_of_mem_Icc {q : Puncture} {a b : ℝ}
    (ha : 0 ≤ q.endSign * a) (hb : 0 ≤ q.endSign * b) {r : ℝ}
    (hr : r ∈ Icc (endRadius q (max a b)) (endRadius q (min a b))) (θ : ℝ) :
    Complex.equivRealProdCLM (circleMap q.endCenter r θ) ∈ thricePuncturedSphereReal := by
  set x := -Real.log (r / ‖q.endScale‖) / (2 * π)
  have hx := endRadius_neg_log_div q ((endRadius_pos q _).trans_le hr.1)
  have hmem : x ∈ [[a, b]] :=
    ⟨(endRadius_le_endRadius_iff q).1 (by rw [hx]; exact hr.2),
      (endRadius_le_endRadius_iff q).1 (by rw [hx]; exact hr.1)⟩
  have h := endChart_mem_thricePuncturedSphereReal
    (z := (x, (Complex.arg q.endScale - θ) / (2 * π))) (endSign_mul_nonneg_of_mem_uIcc ha hb hmem)
  rwa [← equivRealProdCLM_circleMap_endRadius, hx] at h

/-- **The integral over an end annulus.** Let `u` be a map of the pair of pants which is `C¹` on
`S` and `a ≤ b` two heights of the end `q` with `±a, ±b ≥ 0`. The integral of `φ` over `u`
composed with the end chart on `[a, b] × [0, 1]` is the integral of `u^* φ` over the closed annulus
of the end between the heights `a` and `b`, of radii `‖b_q‖ exp (-2π b) ≤ ‖w - c_q‖ ≤
‖b_q‖ exp (-2π a)` about the center `c_q` of the end. The end lift is holomorphic, so the end
chart preserves orientation. -/
theorem rectangleIntegral_comp_endChart {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 0 φ)
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (q : Puncture) {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ q.endSign * a) (hb : 0 ≤ q.endSign * b) :
    rectangleIntegral φ (u ∘ endChart q) (a, 0) (b, 1) =
      ∫ z in Complex.equivRealProdCLM.symm ⁻¹'
          {w | ‖q.endScale‖ * Real.exp (-(2 * π * b)) ≤ ‖w - q.endCenter‖ ∧
            ‖w - q.endCenter‖ ≤ ‖q.endScale‖ * Real.exp (-(2 * π * a))},
        φ (u z) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (1, 0), mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (0, 1)] := by
  have h := rectangleIntegral_comp_endChart_prodMap hφ hu q (σ := id) contDiff_id
    fun x hx ↦ endSign_mul_nonneg_of_mem_uIcc ha hb hx
  rw [Prod.map_id, Function.comp_id, id, id] at h
  rw [h, ← endRadius, ← endRadius, integral_annulus_eq_intervalIntegral hφ hu
    (endRadius_pos q b).le ((endRadius_le_endRadius_iff q).2 hab) fun r hr θ ↦
      equivRealProdCLM_circleMap_mem_of_mem_Icc ha hb (by rwa [max_eq_right hab,
        min_eq_left hab]) θ]

/-! ### Turning the output circle of the core into the end loop of the output -/

/-- The point at the angle `θ` of the output circle `‖w‖ = 2`, in real coordinates. -/
private noncomputable def outputCirclePoint (θ : ℝ) : ℝ × ℝ :=
  Complex.equivRealProdCLM (circleMap 0 2 θ)

private theorem contDiff_outputCirclePoint {n : ℕ∞} : ContDiff ℝ n outputCirclePoint :=
  Complex.equivRealProdCLM.contDiff.comp (contDiff_circleMap 0 2)

private theorem periodic_outputCirclePoint : Periodic outputCirclePoint (2 * π) := fun θ ↦ by
  simp only [outputCirclePoint, periodic_circleMap 0 2 θ]

private theorem outputCirclePoint_mem (θ : ℝ) :
    outputCirclePoint θ ∈ thricePuncturedSphereReal := by
  have h := endChart_mem_thricePuncturedSphereReal (q := .inf)
    (z := (0, (Complex.arg Puncture.inf.endScale - θ) / (2 * π))) (by simp)
  rwa [← equivRealProdCLM_circleMap_endRadius, endRadius_inf_zero, Puncture.endCenter_inf] at h

/-- The end loop of the output at the height `0` runs clockwise around the output circle. -/
private theorem endChart_inf_mk_zero (t : ℝ) :
    endChart .inf (0, t) = outputCirclePoint (-(2 * π * t)) := by
  rw [← Complex.equivRealProdCLM.apply_symm_apply (endChart _ _),
    equivRealProdCLM_symm_endChart_mk, outputCirclePoint, Puncture.endCenter_inf,
    endRadius_inf_zero]
  simp

/-- The angle by which the point of the output circle on the ray from `1/2` at the angle `θ` is
ahead of `θ`, seen from `0`: the argument of `ρ_out θ + exp (-iθ) / 2` for the outer radius
`ρ_out = pairOfPantsOuterRadius`, which lies in the right half-plane. -/
private noncomputable def turnOffset (θ : ℝ) : ℝ :=
  Complex.arg (pairOfPantsOuterRadius θ + Complex.exp (-(θ * Complex.I)) / 2)

private theorem re_pos_turnOffset (θ : ℝ) :
    0 < ((pairOfPantsOuterRadius θ : ℂ) + Complex.exp (-(θ * Complex.I)) / 2).re := by
  have h₁ := one_lt_pairOfPantsOuterRadius θ
  have h₂ := Real.neg_one_le_cos θ
  rw [← neg_mul, ← Complex.ofReal_neg, Complex.add_re, Complex.ofReal_re, Complex.div_ofNat_re,
    Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  linarith

private theorem contDiff_turnOffset {n : ℕ∞} : ContDiff ℝ n turnOffset := by
  refine contDiff_iff_contDiffAt.2 fun θ ↦ ?_
  have hR := contDiff_pairOfPantsOuterRadius (n := n)
  refine (Complex.contDiffAt_arg (Or.inl (re_pos_turnOffset θ))).comp θ ?_
  refine ContDiff.contDiffAt ?_
  have he : ContDiff ℝ n fun θ : ℝ ↦ Complex.exp (-(θ * Complex.I)) :=
    (Complex.contDiff_exp (𝕜 := ℝ)).comp
      (Complex.ofRealCLM.contDiff.mul contDiff_const).neg
  exact (Complex.ofRealCLM.contDiff.comp hR).add (he.div_const 2)

private theorem turnOffset_sub_two_pi (θ : ℝ) : turnOffset (θ - 2 * π) = turnOffset θ := by
  rw [turnOffset, turnOffset, ← pairOfPantsOuterRadius_add_two_pi (θ - 2 * π), sub_add_cancel]
  have h : -(((θ - 2 * π : ℝ) : ℂ) * Complex.I) = -(θ * Complex.I) + 2 * π * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_periodic]

/-- **The output circle seen from `0` and from `1/2`.** The point of the output circle at the angle
`θ + turnOffset θ` about `0` is the point at the outer radius on the ray from `1/2` at the angle
`θ`. -/
private theorem outputCirclePoint_add_turnOffset (θ : ℝ) :
    outputCirclePoint (θ + turnOffset θ) =
      Complex.equivRealProdCLM (circleMap (1 / 2) (pairOfPantsOuterRadius θ) θ) := by
  set w : ℂ := pairOfPantsOuterRadius θ + Complex.exp (-(θ * Complex.I)) / 2
  have hw :
      w = Complex.exp (-(θ * Complex.I)) * circleMap (1 / 2) (pairOfPantsOuterRadius θ) θ := by
    rw [circleMap, mul_add, mul_left_comm, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero,
      mul_one]
    ring
  have hnorm : ‖w‖ = 2 := by
    rw [hw, norm_mul, ← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, one_mul,
      norm_circleMap_half_pairOfPantsOuterRadius]
  rw [outputCirclePoint]
  congr 1
  calc circleMap 0 2 (θ + turnOffset θ)
      = Complex.exp (θ * Complex.I) * (‖w‖ * Complex.exp (Complex.arg w * Complex.I)) := by
        rw [hnorm, circleMap, turnOffset]
        push_cast
        rw [add_mul, Complex.exp_add]
        ring
    _ = Complex.exp (θ * Complex.I) * w := by rw [Complex.norm_mul_exp_arg_mul_I]
    _ = circleMap (1 / 2) (pairOfPantsOuterRadius θ) θ := by
        rw [hw, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]

/-- The angle about `1/2` along the output loop of the core chart, for parameters `t ∈ [0, 1]`:
`-π/2 - π r` on the first lobe and `-3π/2 - π r` on the second, at the lobe parameters `r` of the
loopwise concatenation. -/
private noncomputable def turnAngle (x : ℝ) : ℝ :=
  -(π / 2) - π * (Real.smoothTransition (6 * x - 1) + Real.smoothTransition (6 * x - 4))

/-- The phase of the turn: from the angle about `0` of the output loop of the core chart at
`s = 0` to the angle `-2π t` of the end loop of the output at `s = 1`. -/
private noncomputable def turnPhase (z : ℝ × ℝ) : ℝ :=
  (1 - Real.smoothTransition z.1) * (turnAngle z.2 + turnOffset (turnAngle z.2)) +
    Real.smoothTransition z.1 * -(2 * π * z.2)

private theorem contDiff_turnPhase {n : ℕ∞} : ContDiff ℝ n turnPhase := by
  have hA : ContDiff ℝ n turnAngle := by unfold turnAngle; fun_prop
  unfold turnPhase
  have := contDiff_turnOffset (n := n)
  fun_prop

private theorem turnAngle_add_one {x : ℝ} (h₁ : -(1 / 6) ≤ x) (h₂ : x ≤ 0) :
    turnAngle (x + 1) = turnAngle x - 2 * π := by
  simp only [turnAngle]
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring

/-- Just below `t = 0` the phase drops by `2π` over a period, so the turn is periodic. -/
private theorem turnPhase_add_one (s : ℝ) {x : ℝ} (h₁ : -(1 / 6) ≤ x) (h₂ : x ≤ 0) :
    turnPhase (s, x + 1) = turnPhase (s, x) - 2 * π := by
  simp only [turnPhase, turnAngle_add_one h₁ h₂, turnOffset_sub_two_pi]
  ring

/-- **The turn**: a cylinder in the output circle from the output loop of the core chart to the
end loop of the output at the height `0`, through the phases `turnPhase`. -/
private noncomputable def turnChart (z : ℝ × ℝ) : ℝ × ℝ :=
  outputCirclePoint (turnPhase (z.1, Int.fract z.2))

private theorem contDiff_turnChart {n : ℕ∞} : ContDiff ℝ n turnChart := by
  have hG : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) n (outputCirclePoint ∘ turnPhase) :=
    (contDiff_outputCirclePoint.comp contDiff_turnPhase).contMDiff
  refine contMDiff_iff_contDiff.1 <| contMDiff_prod_modelWithCornersSelf_iff.1 <|
    (contMDiff_prod_modelWithCornersSelf_iff.2 hG).comp_fract_snd (ε := 1 / 6) (by norm_num)
      fun s t ht₀ ht₁ ↦ ?_
  simp only [Function.comp_apply, turnPhase_add_one s (by linarith) ht₁.le,
    periodic_outputCirclePoint.sub_eq]

private theorem turnChart_apply_add_one (s t : ℝ) : turnChart (s, t + 1) = turnChart (s, t) := by
  simp only [turnChart, Int.fract_add_one]

private theorem turnChart_mem (z : ℝ × ℝ) : turnChart z ∈ thricePuncturedSphereReal :=
  outputCirclePoint_mem _

/-- At `s = 1` the turn runs through the end loop of the output at the height `0`. -/
private theorem turnChart_mk_one (t : ℝ) : turnChart (1, t) = endChart .inf (0, t) := by
  rw [turnChart, endChart_inf_mk_zero]
  simp only [turnPhase, Real.smoothTransition.one, sub_self, zero_mul, zero_add, one_mul]
  have h : -(2 * π * t) = -(2 * π * Int.fract t) - (⌊t⌋ : ℝ) * (2 * π) := by
    linear_combination (2 * π) * Int.fract_add_floor t
  rw [h, periodic_outputCirclePoint.sub_int_mul_eq]

private theorem cos_neg_pi_div_two_sub (y : ℝ) : Real.cos (-(π / 2) - y) = -Real.sin y := by
  rw [Real.cos_sub, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring

/-- **The start of the turn.** At `s = 0` the turn runs through the output loop of the core
chart. -/
private theorem turnChart_mk_zero (t : ℝ) : turnChart (0, t) = pairOfPantsCoreChart (1, t) := by
  -- Both loops have period one, so it suffices to compare them on `[0, 1)`.
  have hper : Periodic (fun t ↦ pairOfPantsCoreChart (1, t)) 1 :=
    fun t ↦ pairOfPantsCoreChart_apply_add_one 1 t
  have hfr : pairOfPantsCoreChart (1, t) = pairOfPantsCoreChart (1, Int.fract t) := by
    rw [← Int.self_sub_floor, ← mul_one (⌊t⌋ : ℝ)]
    exact (hper.sub_int_mul_eq ⌊t⌋).symm
  rw [hfr, turnChart]
  set x := Int.fract t
  have hx₀ : 0 ≤ x := Int.fract_nonneg t
  have hx₁ : x < 1 := Int.fract_lt_one t
  simp only [turnPhase, Real.smoothTransition.zero, sub_zero, one_mul, zero_mul, add_zero]
  rw [outputCirclePoint_add_turnOffset, pairOfPantsCoreChart_mk_one]
  rcases le_or_gt x (1 / 2) with hx | hx
  · -- On the first lobe the angle about `1/2` is `-π/2 - π r`.
    rw [loopwiseTrans_of_le _ _ (z := (1, x)) hx₀ hx]
    have hA : turnAngle x = -(π / 2) - π * Real.smoothTransition (6 * x - 1) := by
      rw [turnAngle, Real.smoothTransition.zero_of_nonpos (by linarith : 6 * x - 4 ≤ 0), add_zero]
    dsimp only
    rw [hA, pairOfPantsOuterRadius_def, cos_neg_pi_div_two_sub, neg_neg, neg_sq]
  · -- On the second lobe it is `-3π/2 - π r`.
    rw [loopwiseTrans_of_lt _ _ (z := (1, x)) hx hx₁]
    have hA : turnAngle x = -(3 * π / 2) - π * Real.smoothTransition (6 * x - 4) := by
      rw [turnAngle, Real.smoothTransition.one_of_one_le (by linarith)]
      ring
    have hcos : Real.cos (-(3 * π / 2) - π * Real.smoothTransition (6 * x - 4)) =
        Real.sin (π * Real.smoothTransition (6 * x - 4)) := by
      rw [show -(3 * π / 2) - π * Real.smoothTransition (6 * x - 4) =
          -(π / 2) - π * Real.smoothTransition (6 * x - 4) - π by ring, Real.cos_sub_pi,
        cos_neg_pi_div_two_sub, neg_neg]
    dsimp only
    rw [hA, pairOfPantsOuterRadius_def, hcos]

omit [IsManifold I 1 M] in
/-- **The turn has no area.** It factors through the output circle, a curve. -/
private theorem rectangleIntegral_comp_turnChart (φ : RoughForm I M F 2) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) :
    rectangleIntegral φ (u ∘ turnChart) (0, 0) (1, 1) = 0 := by
  have hγ : MDifferentiable 𝓘(ℝ, ℝ) I (u ∘ outputCirclePoint) :=
    (hu.comp_contMDiff contDiff_outputCirclePoint.contMDiff outputCirclePoint_mem).mdifferentiable
      one_ne_zero
  -- On the unit square the turn is the output circle composed with the phase.
  have hcongr : rectangleIntegral φ (u ∘ turnChart) (0, 0) (1, 1) =
      rectangleIntegral φ ((u ∘ outputCirclePoint) ∘ turnPhase) (0, 0) (1, 1) := by
    refine rectangleIntegral_congr fun z hz ↦ ?_
    obtain ⟨s, t⟩ := z
    simp only [uIcc_of_le zero_le_one, mem_prod, mem_Icc] at hz
    simp only [Function.comp_apply, turnChart]
    rcases hz.2.2.lt_or_eq with h | h
    · rw [Int.fract_eq_self.2 ⟨hz.2.1, h⟩]
    · rw [h, Int.fract_one, ← zero_add (1 : ℝ), turnPhase_add_one _ (by norm_num) le_rfl,
        periodic_outputCirclePoint.sub_eq]
  rw [hcongr]
  exact rectangleIntegral_comp_eq_zero φ hγ (contDiff_turnPhase (n := 1).differentiable
    one_ne_zero) _ _

/-! ### The output chart -/

/-- The annulus of the output end from the height `0` out to the height `R` (the first coordinate
`-R` of the end chart), swept by the circles of the end at the first coordinates `-R β(s)` of the
end chart, for the smooth transition `β`. -/
private noncomputable def outputAnnulus (R : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  endChart .inf (-(R * Real.smoothTransition z.1), z.2)

private theorem outputAnnulus_eq_comp (R : ℝ) :
    outputAnnulus R = endChart .inf ∘ Prod.map (fun s ↦ -(R * Real.smoothTransition s)) id :=
  (rfl)

private theorem contDiff_outputAnnulus (R : ℝ) {n : ℕ∞} : ContDiff ℝ n (outputAnnulus R) := by
  rw [outputAnnulus_eq_comp]
  exact (contDiff_endChart _ _).comp
    ((contDiff_const.mul Real.smoothTransition.contDiff).neg.prodMap contDiff_id)

private theorem endSign_inf_mul_neg_mul_smoothTransition_nonneg {R : ℝ} (hR : 0 ≤ R) (s : ℝ) :
    0 ≤ Puncture.inf.endSign * -(R * Real.smoothTransition s) := by
  rw [Puncture.endSign_inf, neg_one_mul, neg_neg]
  exact mul_nonneg hR (Real.smoothTransition.nonneg s)

private theorem outputAnnulus_apply_add_one (R s t : ℝ) :
    outputAnnulus R (s, t + 1) = outputAnnulus R (s, t) :=
  endChart_add_one _ _ _

private theorem outputAnnulus_mem {R : ℝ} (hR : 0 ≤ R) (z : ℝ × ℝ) :
    outputAnnulus R z ∈ thricePuncturedSphereReal :=
  endChart_mem_thricePuncturedSphereReal (endSign_inf_mul_neg_mul_smoothTransition_nonneg hR z.1)

/-- **The integral over the output annulus.** It is minus the integral of `u^* φ` over the
annulus `2 ≤ ‖w‖ ≤ 2 exp (2πR)`: the annulus is swept outwards, against the orientation of the
end chart. -/
private theorem rectangleIntegral_comp_outputAnnulus {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 0 φ) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {R : ℝ} (hR : 0 ≤ R) :
    rectangleIntegral φ (u ∘ outputAnnulus R) (0, 0) (1, 1) =
      -∫ z in Complex.equivRealProdCLM.symm ⁻¹' {w | 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * Real.exp (2 * π * R)},
        φ (u z) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (1, 0), mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (0, 1)] := by
  have hσ : ContDiff ℝ 1 fun s ↦ -(R * Real.smoothTransition s) :=
    (contDiff_const.mul Real.smoothTransition.contDiff).neg
  have hrad (x : ℝ) : endRadius .inf x = 2 * Real.exp (-(2 * π * x)) := by
    simp [endRadius]
  have h₁ : endRadius .inf (-R) = 2 * Real.exp (2 * π * R) := by
    rw [hrad, mul_neg, neg_neg]
  have hset : {w : ℂ | 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * Real.exp (2 * π * R)} =
      {w | endRadius .inf 0 ≤ ‖w - Puncture.inf.endCenter‖ ∧
        ‖w - Puncture.inf.endCenter‖ ≤ endRadius .inf (-R)} := by
    simp [endRadius_inf_zero, h₁]
  have hR₀ : endRadius .inf 0 ≤ endRadius .inf (-R) :=
    (endRadius_le_endRadius_iff _).2 (by linarith)
  rw [outputAnnulus_eq_comp,
    rectangleIntegral_comp_endChart_prodMap hφ hu .inf hσ fun s _ ↦
      endSign_inf_mul_neg_mul_smoothTransition_nonneg hR s, hset,
    integral_annulus_eq_intervalIntegral hφ hu (endRadius_pos _ _).le hR₀ fun r hr θ ↦
      equivRealProdCLM_circleMap_mem_of_mem_Icc (a := -R) (b := 0) (by simp [hR]) (by simp)
        (by rwa [max_eq_right (by linarith), min_eq_left (by linarith)]) θ,
    intervalIntegral.integral_symm]
  simp [Real.smoothTransition.zero, Real.smoothTransition.one]

/-- **The output chart** of the truncation `S_R` of the pair of pants, for `R ≥ 0`: the core chart
`TauCeti.Floer.pairOfPantsCoreChart`, from the input circles at the height `0` to the output circle
`‖w‖ = 2`, followed by a turn within that circle onto the end loop of the output at the height `0`,
and by the annulus of the output end out to the circle `‖w‖ = 2 exp (2πR)` at the height `R`. It
is a smooth cylinder chart (`TauCeti.Floer.contDiff_pairOfPantsOutputChart`,
`TauCeti.Floer.pairOfPantsOutputChart_apply_add_one`) from the collared concatenation of the end
loops of the inputs at the height `0` (`TauCeti.Floer.pairOfPantsOutputChart_mk_zero`) to the end
loop of the output at the height `R`, in the parametrization of the end chart
(`TauCeti.Floer.pairOfPantsOutputChart_mk_one`). -/
noncomputable def pairOfPantsOutputChart (R : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  rectangleTrans pairOfPantsCoreChart (rectangleTrans turnChart (outputAnnulus R))

private theorem pairOfPantsCoreChart_mk_one_eq_turnChart (R t : ℝ) :
    pairOfPantsCoreChart (1, t) = rectangleTrans turnChart (outputAnnulus R) (0, t) := by
  rw [rectangleTrans_apply_zero, turnChart_mk_zero]

private theorem turnChart_mk_one_eq_outputAnnulus (R t : ℝ) :
    turnChart (1, t) = outputAnnulus R (0, t) := by
  rw [turnChart_mk_one, outputAnnulus, Real.smoothTransition.zero, mul_zero, neg_zero]

/-- The output chart is smooth. -/
theorem contDiff_pairOfPantsOutputChart (R : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (pairOfPantsOutputChart R) :=
  contMDiff_iff_contDiff.1 <| contMDiff_rectangleTrans contDiff_pairOfPantsCoreChart.contMDiff
    (contMDiff_rectangleTrans contDiff_turnChart.contMDiff (contDiff_outputAnnulus R).contMDiff
      (turnChart_mk_one_eq_outputAnnulus R)) (pairOfPantsCoreChart_mk_one_eq_turnChart R)

/-- The output chart is `1`-periodic in its second coordinate. -/
@[simp]
theorem pairOfPantsOutputChart_apply_add_one (R s t : ℝ) :
    pairOfPantsOutputChart R (s, t + 1) = pairOfPantsOutputChart R (s, t) :=
  rectangleTrans_apply_add_snd (fun z ↦ pairOfPantsCoreChart_apply_add_one z.1 z.2)
    (rectangleTrans_apply_add_snd (fun z ↦ turnChart_apply_add_one z.1 z.2)
      fun z ↦ outputAnnulus_apply_add_one R z.1 z.2) (s, t)

/-- **The input loop of the output chart.** For `s = 0` the output chart runs through the
collared concatenation of the end charts of the input ends `0` and `1` at the height `0`. -/
theorem pairOfPantsOutputChart_mk_zero (R t : ℝ) :
    pairOfPantsOutputChart R (0, t) = loopwiseTrans (fun z ↦ endChart Puncture.zero (0, z.2))
      (fun z ↦ endChart Puncture.one (0, z.2)) (0, t) := by
  rw [pairOfPantsOutputChart, rectangleTrans_apply_zero, pairOfPantsCoreChart_mk_zero]

/-- **The output loop of the output chart.** For `s = 1` the output chart runs through the end
loop of the output at the height `R`, the circle `‖w‖ = 2 exp (2πR)`. -/
theorem pairOfPantsOutputChart_mk_one (R t : ℝ) :
    pairOfPantsOutputChart R (1, t) = endChart Puncture.inf (-R, t) := by
  rw [pairOfPantsOutputChart, rectangleTrans_apply_one, rectangleTrans_apply_one, outputAnnulus,
    Real.smoothTransition.one, mul_one]

/-- For `R ≥ 0` the output chart lies in the pair of pants `S`. -/
theorem pairOfPantsOutputChart_mem_thricePuncturedSphereReal {R : ℝ} (hR : 0 ≤ R)
    (z : ℝ × ℝ) : pairOfPantsOutputChart R z ∈ thricePuncturedSphereReal :=
  rectangleTrans_mem pairOfPantsCoreChart_mem_thricePuncturedSphereReal
    (rectangleTrans_mem turnChart_mem (outputAnnulus_mem hR)) z

/-- **The area of the output chart.** For `R ≥ 0`, a continuous two-form `φ` and a map `u` of the
pair of pants which is `C¹` on `S`, the integral of `φ` over `u` composed with the output chart is
minus the integral of `u^* φ` over the truncation `S₀` at the height `0` and the annulus
`2 ≤ ‖w‖ ≤ 2 exp (2πR)` of the output end. The turn within the output circle has no area. -/
theorem rectangleIntegral_comp_pairOfPantsOutputChart {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 0 φ) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {R : ℝ} (hR : 0 ≤ R) :
    rectangleIntegral φ (u ∘ pairOfPantsOutputChart R) (0, 0) (1, 1) =
      -((∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation 0,
          φ (u z) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (1, 0), mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (0, 1)]) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹'
            {w | 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * Real.exp (2 * π * R)},
          φ (u z) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (1, 0), mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (0, 1)]) := by
  have hc := hu.comp_contMDiff contDiff_pairOfPantsCoreChart.contMDiff
    pairOfPantsCoreChart_mem_thricePuncturedSphereReal
  have hT := hu.comp_contMDiff contDiff_turnChart.contMDiff turnChart_mem
  have hA := hu.comp_contMDiff (contDiff_outputAnnulus R).contMDiff (outputAnnulus_mem hR)
  have hTA : ∀ t, (u ∘ turnChart) (1, t) = (u ∘ outputAnnulus R) (0, t) := fun t ↦ by
    rw [Function.comp_apply, Function.comp_apply, turnChart_mk_one_eq_outputAnnulus R]
  have hcTA : ∀ t, (u ∘ pairOfPantsCoreChart) (1, t) =
      rectangleTrans (u ∘ turnChart) (u ∘ outputAnnulus R) (0, t) := fun t ↦ by
    rw [rectangleTrans_apply_zero, Function.comp_apply, Function.comp_apply, turnChart_mk_zero]
  have hsplit : u ∘ pairOfPantsOutputChart R = rectangleTrans (u ∘ pairOfPantsCoreChart)
      (rectangleTrans (u ∘ turnChart) (u ∘ outputAnnulus R)) := by
    funext z
    rw [Function.comp_apply, pairOfPantsOutputChart, apply_rectangleTrans u]
    exact congrArg (fun v ↦ rectangleTrans _ v z) (funext fun w ↦ apply_rectangleTrans u _ _ w)
  rw [hsplit, rectangleIntegral_rectangleTrans hφ hc (contMDiff_rectangleTrans hT hA hTA) hcTA,
    rectangleIntegral_rectangleTrans hφ hT hA hTA, rectangleIntegral_comp_turnChart φ hu,
    rectangleIntegral_comp_pairOfPantsCoreChart hφ hu,
    rectangleIntegral_comp_outputAnnulus hφ hu hR,
    zero_add, neg_add]

omit [IsManifold I 1 M] in
/-- **The output chart as a cylinder.** For `R ≥ 0` and a map `u` of the pair of pants which is
`C²` on `S`, the composite of `u` with the output chart is a cylinder from the collared
concatenation of the loops of `u` along the circles of the input ends `0` and `1` at the
height `0` to the loop of `u` along the circle of the output end at the height `R`, in the
parametrization of the end chart. -/
theorem isLoopCylinder_comp_pairOfPantsOutputChart {R : ℝ} (hR : 0 ≤ R) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 2 u thricePuncturedSphereReal) :
    IsLoopCylinder I (u ∘ pairOfPantsOutputChart R)
      (fun t ↦ loopwiseTrans (fun z ↦ u (endChart Puncture.zero (0, z.2)))
        (fun z ↦ u (endChart Puncture.one (0, z.2))) (0, t))
      fun t ↦ u (endChart Puncture.inf (-R, t)) where
  contMDiff := hu.comp_contMDiff (contDiff_pairOfPantsOutputChart R).contMDiff
    (pairOfPantsOutputChart_mem_thricePuncturedSphereReal hR)
  apply_add_one z := by
    simp only [Function.comp_apply, pairOfPantsOutputChart_apply_add_one]
  apply_zero t := by
    rw [Function.comp_apply, pairOfPantsOutputChart_mk_zero, apply_loopwiseTrans u]
    simp only [Function.comp_def]
  apply_one t := by
    rw [Function.comp_apply, pairOfPantsOutputChart_mk_one]

/-! ### The truncation as the core and three annuli -/

/-- The norms of `w` and `1` differ by at most `‖w - 1‖`. -/
private theorem le_norm_sub_one (w : ℂ) :
    ‖w‖ - 1 ≤ ‖w - 1‖ ∧ 1 - ‖w‖ ≤ ‖w - 1‖ :=
  ⟨by simpa using norm_sub_norm_le w 1, by simpa [norm_sub_rev] using norm_sub_norm_le (1 : ℂ) w⟩

/-- For `R ≥ 0`, the truncation `S_R` is the truncation `S₀` together with the annuli of the three
ends between the heights `0` and `R`. -/
private theorem truncation_eq_union {R : ℝ} (hR : 0 ≤ R) :
    truncation R = ((truncation 0 ∪ {w | 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * Real.exp (2 * π * R)}) ∪
      {w | Real.exp (-(2 * π * R)) / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 1 / 2}) ∪
        {w | Real.exp (-(2 * π * R)) / 2 ≤ ‖w - 1‖ ∧ ‖w - 1‖ ≤ 1 / 2} := by
  have he : Real.exp (-(2 * π * R)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
  have he' : 1 ≤ Real.exp (2 * π * R) := Real.one_le_exp_iff.2 (by nlinarith [Real.pi_pos])
  ext w
  obtain ⟨h₁, h₂⟩ := le_norm_sub_one w
  simp only [truncation_eq, mul_zero, neg_zero, Real.exp_zero, mul_one, mem_union, mem_inter_iff,
    mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨⟨ha, hb⟩, hc⟩
    by_cases h₃ : 2 < ‖w‖
    · exact .inl (.inl (.inr ⟨h₃.le, hc⟩))
    by_cases h₄ : ‖w‖ < 1 / 2
    · exact .inl (.inr ⟨ha, h₄.le⟩)
    by_cases h₅ : ‖w - 1‖ < 1 / 2
    · exact .inr ⟨hb, h₅.le⟩
    exact .inl (.inl (.inl ⟨⟨by linarith, by linarith⟩, by linarith⟩))
  · rintro (((⟨⟨ha, hb⟩, hc⟩ | ⟨ha, hb⟩) | ⟨ha, hb⟩) | ⟨ha, hb⟩)
    · exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
    · exact ⟨⟨by linarith, by linarith⟩, hb⟩
    · exact ⟨⟨ha, by linarith⟩, by linarith⟩
    · exact ⟨⟨by linarith, ha⟩, by linarith⟩

/-- **The integral over the truncation, piece by piece.** For `R ≥ 0` and a function integrable
on `S_R`, its integral over `S_R` is the sum of its integrals over the annuli of the inputs, over
`S₀` and over the annulus of the output; the pieces meet only along the circles `‖w‖ = 2`,
`‖w‖ = 1/2` and `‖w - 1‖ = 1/2`. -/
private theorem setIntegral_truncation_eq_add {g : ℂ → F} {R : ℝ} (hR : 0 ≤ R)
    (hint : IntegrableOn g (truncation R)) :
    ∫ w in truncation R, g w =
      (∫ w in {w : ℂ | Real.exp (-(2 * π * R)) / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 1 / 2}, g w) +
        (∫ w in {w : ℂ | Real.exp (-(2 * π * R)) / 2 ≤ ‖w - 1‖ ∧ ‖w - 1‖ ≤ 1 / 2}, g w) +
          ((∫ w in truncation 0, g w) +
            ∫ w in {w : ℂ | 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * Real.exp (2 * π * R)}, g w) := by
  rw [truncation_eq_union hR] at hint ⊢
  have hm (c : ℂ) (a b : ℝ) : NullMeasurableSet {w : ℂ | a ≤ ‖w - c‖ ∧ ‖w - c‖ ≤ b} volume :=
    (isCompact_setOf_le_norm_sub_le c a b).isClosed.measurableSet.nullMeasurableSet
  have hm₀ (a b : ℝ) : NullMeasurableSet {w : ℂ | a ≤ ‖w‖ ∧ ‖w‖ ≤ b} volume := by
    simpa using hm 0 a b
  rw [setIntegral_union₀ ?_ (hm 1 _ _) (hint.mono_set subset_union_left)
      (hint.mono_set subset_union_right),
    setIntegral_union₀ ?_ (hm₀ _ _) (hint.mono_set (subset_union_left.trans subset_union_left))
      (hint.mono_set (subset_union_right.trans subset_union_left)),
    setIntegral_union₀ ?_ (hm₀ _ _)
      (hint.mono_set (subset_union_left.trans (subset_union_left.trans subset_union_left)))
      (hint.mono_set (subset_union_right.trans (subset_union_left.trans subset_union_left)))]
  · abel
  · refine measure_mono_null (fun w ⟨hw₁, hw₂, _⟩ ↦ ?_) (Measure.addHaar_sphere volume (0 : ℂ) 2)
    rw [truncation_eq] at hw₁
    simp only [mem_inter_iff, mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right, mul_zero,
      Real.exp_zero, mul_one] at hw₁
    simp only [mem_sphere_zero_iff_norm]
    linarith [hw₁.2]
  · refine measure_mono_null (fun w ⟨hw₁, _, hw₂⟩ ↦ ?_)
      (Measure.addHaar_sphere volume (0 : ℂ) (1 / 2))
    simp only [mem_sphere_zero_iff_norm]
    rcases hw₁ with hw₁ | hw₁
    · rw [truncation_eq] at hw₁
      simp only [mem_inter_iff, mem_ofPred_eq, mul_zero, neg_zero, Real.exp_zero] at hw₁
      linarith [hw₁.1.1]
    · linarith [hw₁.1]
  · refine measure_mono_null (fun w ⟨hw₁, _, hw₂⟩ ↦ ?_)
      (Measure.addHaar_sphere volume (1 : ℂ) (1 / 2))
    rw [mem_sphere_iff_norm]
    obtain ⟨h₁, h₂⟩ := le_norm_sub_one w
    rcases hw₁ with (hw₁ | hw₁) | hw₁
    · rw [truncation_eq] at hw₁
      simp only [mem_inter_iff, mem_ofPred_eq, mul_zero, neg_zero, Real.exp_zero] at hw₁
      linarith [hw₁.1.2]
    · linarith [hw₁.1]
    · linarith [hw₁.2]

/-- **The area of the truncated pair of pants through its charts.** For `R ≥ 0`, a continuous
two-form `φ` and a map `u` of the pair of pants which is `C¹` on `S`, the integral of `u^* φ` over
the truncation `S_R` is the sum of the integrals of `φ` over `u` along the end charts of the two
inputs between the heights `0` and `R`, minus the integral over `u` composed with the output chart
`TauCeti.Floer.pairOfPantsOutputChart R`. The boundary circles of each chart run through the end
loops at the heights `0` and `R`, and for `u` of class `C²` the composite of `u` with the output
chart is a cylinder (`TauCeti.Floer.isLoopCylinder_comp_pairOfPantsOutputChart`). -/
theorem setIntegral_truncation_eq_rectangleIntegral {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 0 φ) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {R : ℝ} (hR : 0 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R,
        φ (u z) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (1, 0), mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (0, 1)] =
      rectangleIntegral φ (u ∘ endChart Puncture.zero) (0, 0) (R, 1) +
        rectangleIntegral φ (u ∘ endChart Puncture.one) (0, 0) (R, 1) -
          rectangleIntegral φ (u ∘ pairOfPantsOutputChart R) (0, 0) (1, 1) := by
  set f : ℝ × ℝ → F :=
    fun z ↦ φ (u z) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (1, 0), mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (0, 1)]
  -- The annuli of the input ends, normalized.
  have hZ : {w : ℂ | ‖Puncture.zero.endScale‖ * Real.exp (-(2 * π * R)) ≤
      ‖w - Puncture.zero.endCenter‖ ∧ ‖w - Puncture.zero.endCenter‖ ≤
        ‖Puncture.zero.endScale‖ * Real.exp (-(2 * π * 0))} =
      {w | Real.exp (-(2 * π * R)) / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 1 / 2} := by
    ext w
    simp [div_eq_inv_mul]
  have hO : {w : ℂ | ‖Puncture.one.endScale‖ * Real.exp (-(2 * π * R)) ≤
      ‖w - Puncture.one.endCenter‖ ∧ ‖w - Puncture.one.endCenter‖ ≤
        ‖Puncture.one.endScale‖ * Real.exp (-(2 * π * 0))} =
      {w | Real.exp (-(2 * π * R)) / 2 ≤ ‖w - 1‖ ∧ ‖w - 1‖ ≤ 1 / 2} := by
    ext w
    simp [div_eq_inv_mul]
  rw [rectangleIntegral_comp_endChart hφ hu .zero hR (by simp) (by simp [hR]),
    rectangleIntegral_comp_endChart hφ hu .one hR (by simp) (by simp [hR]),
    rectangleIntegral_comp_pairOfPantsOutputChart hφ hu hR, sub_neg_eq_add, hZ, hO]
  simp only [Complex.setIntegral_preimage_equivRealProdCLM_symm]
  refine setIntegral_truncation_eq_add hR ?_
  -- `u^* φ` is continuous on the compact truncation `S_R`.
  refine ContinuousOn.integrableOn_compact (isCompact_truncation R) ?_
  refine (hφ.continuousOn_apply_mfderiv isOpen_thricePuncturedSphereReal hu _ _).comp
    Complex.equivRealProdCLM.continuous.continuousOn fun w hw ↦ ?_
  rw [mem_thricePuncturedSphereReal_iff, ContinuousLinearEquiv.symm_apply_apply]
  exact truncation_subset R hw

end TauCeti.Floer
