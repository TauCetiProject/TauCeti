/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Stokes
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.Geometry.Symplectic.Liouville.Linear
import TauCeti.Analysis.Calculus.ContDiff.ContinuousAlternatingMap
import TauCeti.Analysis.Calculus.ContDiff.Differentiable
import TauCeti.Analysis.Calculus.TangentCone.Basic
import TauCeti.Analysis.Complex.ReImTopology

/-!
# Green's formula for bilinear pairings on rectangles, annuli and half-annuli

Let `u : ℝ × ℝ → V` be a `C²` map near a closed rectangle `R = [a₁, b₁] × [a₂, b₂]` and let `B` be
a continuous bilinear map. Writing `∂s u` and `∂t u` for the derivatives of `u` in the directions
`(1, 0)` and `(0, 1)`,

`∫_R (B (∂s u) (∂t u) - B (∂t u) (∂s u)) = ∮_{∂R} B (u) (du)`,

where the right-hand side is the integral over the positively oriented boundary of `R`, written
out as four interval integrals. This is Green's theorem for the pullback along `u` of the one-form
`x ↦ B x`, whose exterior derivative is the constant two-form `(v, w) ↦ B v w - B w v`.
The rectangle and annulus formulas below are `TauCeti.integral_extDeriv_prod_Icc` and
`TauCeti.integral_extDeriv_annulus` applied to the pullback along `u` of the one-form `x ↦ B x`.
The half-annulus formula is `TauCeti.integral_upperHalfAnnulus_eq_of_extDeriv_eq` applied to the
one-form `B u (Du)` built from the derivative `Du` of `u` within the closed half-plane, which
agrees with that pullback off the diameter.

For a compactly supported map on the whole plane the boundary terms are absent and the integral
vanishes (`TauCeti.integral_bilinear_fderiv_apply_comm`). With boundary, this is the formula that
expresses the symplectic area of a map from a rectangle into an exact symplectic vector space by
integrals of a primitive along its four sides.

For positive inner radius, neither the map nor its derivatives need be regular on the inner disc.
At zero inner radius the inner boundary integral vanishes, giving Green's formula on a disc.

On a closed upper half-annulus the map need only be `C²` up to the diameter, with its derivatives
taken within the closed half-plane; the boundary consists of the two half-circles and the two
segments of the diameter. This is the form used for maps on half-discs with boundary conditions
on the real axis.

## Main results

* `ContinuousLinearMap.integral_bilinear_fderiv_sub_prod_Icc`: Green's formula above, over
  `Set.Icc a b` for points `a ≤ b` of `ℝ × ℝ`.
* `ContinuousLinearMap.integral_bilinear_fderiv_sub_annulus`: the corresponding formula on a
  translated annulus of nonnegative inner radius, with outer minus inner circle boundary terms.
* `ContinuousLinearMap.integral_bilinear_fderivWithin_sub_upperHalfAnnulus`: the formula on a
  closed upper half-annulus, for a map that is `C²` up to the diameter.
-/

public section

namespace TauCeti

open MeasureTheory Set Complex Filter
open scoped Real Topology

variable {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

private noncomputable def bilinearPullbackOneForm (B : V →L[ℝ] V →L[ℝ] W) (u : E → V) :
    E → E [⋀^Fin 1]→L[ℝ] W :=
  fun z ↦ (ContinuousLinearMap.liouvilleFormCLM ((2 : ℝ) • B) (u z)).compContinuousLinearMap
    (fderiv ℝ u z)

private theorem contDiffAt_bilinearPullbackOneForm
    (B : V →L[ℝ] V →L[ℝ] W) {u : E → V} {z : E} (hu : ContDiffAt ℝ 2 u z) :
    ContDiffAt ℝ 1 (bilinearPullbackOneForm B u) z := by
  exact hu.differentialForm_pullback
    (ContinuousLinearMap.liouvilleFormCLM ((2 : ℝ) • B)).contDiff.contDiffAt

private theorem extDeriv_bilinearPullbackOneForm_apply
    (B : V →L[ℝ] V →L[ℝ] W) {u : E → V} {z : E} (hu : ContDiffAt ℝ 2 u z) (v w : E) :
    extDeriv (bilinearPullbackOneForm B u) z ![v, w] =
      B (fderiv ℝ u z v) (fderiv ℝ u z w) - B (fderiv ℝ u z w) (fderiv ℝ u z v) := by
  have h := congrArg (fun A ↦ A ![v, w])
    (extDeriv_pullback
      (ω := ContinuousLinearMap.liouvilleFormCLM ((2 : ℝ) • B))
      (ContinuousLinearMap.liouvilleFormCLM ((2 : ℝ) • B)).differentiableAt
      hu (by norm_num))
  have hvec : (fun i ↦ fderiv ℝ u z (![v, w] i)) =
      ![fderiv ℝ u z v, fderiv ℝ u z w] := by
    funext i
    fin_cases i <;> rfl
  unfold bilinearPullbackOneForm
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def,
    hvec, ContinuousLinearMap.extDeriv_liouvilleFormCLM_apply] at h
  simpa [← smul_sub, smul_smul] using h

/-- **Green's formula for a bilinear pairing of partial derivatives.** If `u` is `C²` at every
point of the rectangle `Icc a b ⊆ ℝ × ℝ` and `B` is a continuous bilinear map, the integral over
the rectangle of `B (∂s u) (∂t u) - B (∂t u) (∂s u)` is the integral of the one-form `B u (du)`
over the positively oriented boundary: the right side minus the left side of
`t ↦ B u (∂t u)`, minus the top side minus the bottom side of `s ↦ B u (∂s u)`. -/
theorem _root_.ContinuousLinearMap.integral_bilinear_fderiv_sub_prod_Icc
    (B : V →L[ℝ] V →L[ℝ] W) {u : ℝ × ℝ → V} {a b : ℝ × ℝ} (hle : a ≤ b)
    (hu : ∀ z ∈ Icc a b, ContDiffAt ℝ 2 u z) :
    ∫ z in Icc a b, (B (fderiv ℝ u z (1, 0)) (fderiv ℝ u z (0, 1)) -
        B (fderiv ℝ u z (0, 1)) (fderiv ℝ u z (1, 0))) =
      ((∫ t in a.2..b.2, B (u (b.1, t)) (fderiv ℝ u (b.1, t) (0, 1))) -
          ∫ t in a.2..b.2, B (u (a.1, t)) (fderiv ℝ u (a.1, t) (0, 1))) -
        ((∫ s in a.1..b.1, B (u (s, b.2)) (fderiv ℝ u (s, b.2) (1, 0))) -
          ∫ s in a.1..b.1, B (u (s, a.2)) (fderiv ℝ u (s, a.2) (1, 0))) := by
  have h := integral_extDeriv_prod_Icc hle
    (fun z hz ↦ contDiffAt_bilinearPullbackOneForm B (hu z hz))
  rw [setIntegral_congr_fun measurableSet_Icc
    (fun z hz ↦ extDeriv_bilinearPullbackOneForm_apply B (hu z hz) _ _)] at h
  simpa [bilinearPullbackOneForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def, smul_smul] using h

/-- **Green's formula on a closed annulus.** For a `C²` map near the annulus of radii
`0 ≤ a ≤ b`, the integral of the alternating part of a bilinear pairing of its derivatives equals
the outer circle integral of `B u du` minus the inner circle integral. Both circles are
parametrized counterclockwise; their difference gives the boundary orientation. -/
theorem _root_.ContinuousLinearMap.integral_bilinear_fderiv_sub_annulus
    (B : V →L[ℝ] V →L[ℝ] W) {u : ℂ → V} (z₀ : ℂ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hu : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ContDiffAt ℝ 2 u z) :
    ∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b},
      (B (fderiv ℝ u z 1) (fderiv ℝ u z I) -
        B (fderiv ℝ u z I) (fderiv ℝ u z 1)) =
      (∫ θ in -π..π, B (u (circleMap z₀ b θ))
        (fderiv ℝ u (circleMap z₀ b θ) (circleMap 0 b θ * I))) -
      (∫ θ in -π..π, B (u (circleMap z₀ a θ))
        (fderiv ℝ u (circleMap z₀ a θ) (circleMap 0 a θ * I))) := by
  have h := integral_extDeriv_annulus z₀ ha hab
    (fun z hz ↦ contDiffAt_bilinearPullbackOneForm B (hu z hz))
  have hmeas : MeasurableSet {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} := by
    measurability
  rw [setIntegral_congr_fun hmeas
    (fun z hz ↦ extDeriv_bilinearPullbackOneForm_apply B (hu z hz) _ _)] at h
  simpa [bilinearPullbackOneForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def, smul_smul] using h

/-- **Green's formula on a closed upper half-annulus.** Let `S` be the closed upper half
`{z | z₀.im ≤ z.im}` of the annulus of radii `0 ≤ a ≤ b` about `z₀`, contained in an open set `O`,
and let `u` be `C²` on `{z | z₀.im ≤ z.im} ∩ O`, up to the line `z.im = z₀.im`, with derivative
`Du` taken within the closed half-plane. The integral over `S` of the alternating part
`B (Du 1) (Du I) - B (Du I) (Du 1)` of a bilinear pairing is the integral of `B u (Du)` over the
positively oriented boundary of `S`: the outer minus the inner half-circle, both from the angle
`0` to `π`, plus the two segments of the diameter, both towards increasing real part. -/
theorem _root_.ContinuousLinearMap.integral_bilinear_fderivWithin_sub_upperHalfAnnulus
    (B : V →L[ℝ] V →L[ℝ] W) {u : ℂ → V} (z₀ : ℂ) {a b : ℝ} {O : Set ℂ} (hO : IsOpen O)
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hSO : {z : ℂ | z₀.im ≤ z.im ∧ a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} ⊆ O)
    (hu : ContDiffOn ℝ 2 u ({z : ℂ | z₀.im ≤ z.im} ∩ O)) :
    ∫ z in {z : ℂ | z₀.im ≤ z.im ∧ a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b},
      (B (fderivWithin ℝ u {z | z₀.im ≤ z.im} z 1) (fderivWithin ℝ u {z | z₀.im ≤ z.im} z I) -
        B (fderivWithin ℝ u {z | z₀.im ≤ z.im} z I) (fderivWithin ℝ u {z | z₀.im ≤ z.im} z 1)) =
      (∫ θ in 0..π, B (u (circleMap z₀ b θ))
        (fderivWithin ℝ u {z | z₀.im ≤ z.im} (circleMap z₀ b θ) (circleMap 0 b θ * I))) -
      (∫ θ in 0..π, B (u (circleMap z₀ a θ))
        (fderivWithin ℝ u {z | z₀.im ≤ z.im} (circleMap z₀ a θ) (circleMap 0 a θ * I))) +
      (∫ r in a..b, B (u (z₀ + r)) (fderivWithin ℝ u {z | z₀.im ≤ z.im} (z₀ + r) 1)) +
      ∫ r in a..b, B (u (z₀ - r)) (fderivWithin ℝ u {z | z₀.im ≤ z.im} (z₀ - r) 1) := by
  set H : Set ℂ := {z | z₀.im ≤ z.im}
  set S : Set ℂ := {z : ℂ | z₀.im ≤ z.im ∧ a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}
  set Du := fderivWithin ℝ u H
  have hSHO : S ⊆ H ∩ O := fun z hz ↦ ⟨hz.1, hSO hz⟩
  have hDu : ContinuousOn Du S :=
    (hu.continuousOn_fderivWithin_of_inter (uniqueDiffOn_setOfPred_le_im _) hO
      (by norm_num)).mono hSHO
  -- The one-form `B u (Du)`, built from one-sided derivatives.
  let ω : ℂ → ℂ [⋀^Fin 1]→L[ℝ] W := fun z ↦
    (ContinuousLinearMap.liouvilleFormCLM ((2 : ℝ) • B) (u z)).compContinuousLinearMap (Du z)
  have hCLM := ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM
    (𝕜 := ℝ) (E := ℂ) (F := V) (G := W) (ι := Fin 1) 1 (by simp)
  have hω : ContinuousOn ω S :=
    (hCLM.continuous.comp_continuousOn hDu).clm_apply
      ((ContinuousLinearMap.liouvilleFormCLM _).continuous.comp_continuousOn
        (hu.continuousOn.mono hSHO))
  have hdω : ContinuousOn (fun z ↦ B (Du z 1) (Du z I) - B (Du z I) (Du z 1)) S :=
    ((B.continuous.comp_continuousOn (hDu.clm_apply continuousOn_const)).clm_apply
      (hDu.clm_apply continuousOn_const)).sub
      ((B.continuous.comp_continuousOn (hDu.clm_apply continuousOn_const)).clm_apply
        (hDu.clm_apply continuousOn_const))
  -- Away from the diameter, `ω` is the two-sided pullback form.
  have hd (z : ℂ) (h₁ : z₀.im < z.im) (h₂ : a < ‖z - z₀‖) (h₃ : ‖z - z₀‖ < b) :
      DifferentiableAt ℝ ω z ∧
        extDeriv ω z ![1, I] = B (Du z 1) (Du z I) - B (Du z I) (Du z 1) := by
    have hzO : z ∈ O := hSO ⟨h₁.le, h₂.le, h₃.le⟩
    have hopen : IsOpen {w : ℂ | z₀.im < w.im} := isOpen_lt continuous_const continuous_im
    have hH (w : ℂ) (hw : z₀.im < w.im) : H ∈ 𝓝 w := setOfPred_le_im_mem_nhds hw
    have hu2 : ContDiffAt ℝ 2 u z :=
      hu.contDiffAt (Filter.inter_mem (hH z h₁) (hO.mem_nhds hzO))
    have heq : ω =ᶠ[𝓝 z] bilinearPullbackOneForm B u := by
      filter_upwards [hopen.mem_nhds h₁] with w hw
      simp only [ω, bilinearPullbackOneForm, Du, fderivWithin_of_mem_nhds (hH w hw)]
    refine ⟨((contDiffAt_bilinearPullbackOneForm B hu2).differentiableAt
      one_ne_zero).congr_of_eventuallyEq heq, ?_⟩
    rw [heq.extDeriv_eq, extDeriv_bilinearPullbackOneForm_apply B hu2]
    simp only [Du, fderivWithin_of_mem_nhds (hH z h₁)]
  have h := integral_upperHalfAnnulus_eq_of_extDeriv_eq z₀ ha hab hω hdω hd
  simpa [ω, ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def,
    smul_smul] using h

end TauCeti
