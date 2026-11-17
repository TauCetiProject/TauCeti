/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Stokes
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.Geometry.Symplectic.Liouville.Linear

/-!
# Green's formula for bilinear pairings on rectangles, annuli and annular sectors

Let `u : ℝ × ℝ → V` be a `C²` map near a closed rectangle `R = [a₁, b₁] × [a₂, b₂]` and let `B` be
a continuous bilinear map. Writing `∂s u` and `∂t u` for the derivatives of `u` in the directions
`(1, 0)` and `(0, 1)`,

`∫_R (B (∂s u) (∂t u) - B (∂t u) (∂s u)) = ∮_{∂R} B (u) (du)`,

where the right-hand side is the integral over the positively oriented boundary of `R`, written
out as four interval integrals. This is Green's theorem for the pullback along `u` of the one-form
`x ↦ B x`, whose exterior derivative is the constant two-form `(v, w) ↦ B v w - B w v`.
The formulas below are `TauCeti.integral_extDeriv_prod_Icc`,
`TauCeti.integral_extDeriv_annulus` and `TauCeti.integral_extDeriv_annularSector` applied to the
pullback along `u` of the one-form `x ↦ B x`.

For a compactly supported map on the whole plane the boundary terms are absent and the integral
vanishes (`TauCeti.integral_bilinear_fderiv_apply_comm`). With boundary, this is the formula that
expresses the symplectic area of a map from a rectangle into an exact symplectic vector space by
integrals of a primitive along its four sides.

For positive inner radius, neither the map nor its derivatives need be regular on the inner disc.
At zero inner radius the inner boundary integral vanishes, giving Green's formula on a disc.

## Main results

* `ContinuousLinearMap.integral_bilinear_fderiv_sub_prod_Icc`: Green's formula above, over
  `Set.Icc a b` for points `a ≤ b` of `ℝ × ℝ`.
* `ContinuousLinearMap.integral_bilinear_fderiv_sub_annulus`: the corresponding formula on a
  translated annulus of nonnegative inner radius, with outer minus inner circle boundary terms.
* `ContinuousLinearMap.integral_bilinear_fderiv_sub_annularSector`: the formula on an annular
  sector, with two arcs and two radial edges as boundary terms.
-/

public section

namespace TauCeti

open MeasureTheory Set Complex
open scoped Real

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

/-- **Green's formula on an annular sector.** For a map that is `C²` on the image of the closed
polar rectangle `[a, b] × [c, d]` under `(r, θ) ↦ circleMap z₀ r θ`, with `[c, d] ⊆ [-π, π]`, the
integral over the points `z` with `a ≤ ‖z - z₀‖ ≤ b` whose argument about `z₀` lies in `[c, d]` of
the alternating part of a bilinear pairing of its derivatives is the integral of `B u du` over the
positively oriented boundary: the outer arc minus the inner arc, both counterclockwise, minus the
radial edge at angle `d` plus the radial edge at angle `c`, both traversed outward. The domain of
integration, defined through `Complex.arg`, can miss a null subset of the closed sector: the ray
at angle `-π` and the centre `z₀`. -/
theorem _root_.ContinuousLinearMap.integral_bilinear_fderiv_sub_annularSector
    (B : V →L[ℝ] V →L[ℝ] W) {u : ℂ → V} (z₀ : ℂ) {a b c d : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hc : -π ≤ c) (hcd : c ≤ d) (hd : d ≤ π)
    (hu : ∀ r ∈ Icc a b, ∀ θ ∈ Icc c d, ContDiffAt ℝ 2 u (circleMap z₀ r θ)) :
    ∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b ∧ arg (z - z₀) ∈ Icc c d},
      (B (fderiv ℝ u z 1) (fderiv ℝ u z I) -
        B (fderiv ℝ u z I) (fderiv ℝ u z 1)) =
      ((∫ θ in c..d, B (u (circleMap z₀ b θ))
          (fderiv ℝ u (circleMap z₀ b θ) (circleMap 0 b θ * I))) -
        ∫ θ in c..d, B (u (circleMap z₀ a θ))
          (fderiv ℝ u (circleMap z₀ a θ) (circleMap 0 a θ * I))) -
      ((∫ r in a..b, B (u (circleMap z₀ r d)) (fderiv ℝ u (circleMap z₀ r d) (exp (d * I)))) -
        ∫ r in a..b, B (u (circleMap z₀ r c)) (fderiv ℝ u (circleMap z₀ r c) (exp (c * I)))) := by
  have h := integral_extDeriv_annularSector z₀ ha hab hc hcd hd
    (fun r hr θ hθ ↦ contDiffAt_bilinearPullbackOneForm B (hu r hr θ hθ))
  have hmeas := measurableSet_annularSector z₀ a b c d
  -- Every point of the sector is `circleMap z₀ ‖z - z₀‖ (arg (z - z₀))`.
  have hsector (z : ℂ)
      (hz : z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b ∧ arg (z - z₀) ∈ Icc c d}) :
      ContDiffAt ℝ 2 u z := by
    have hz' : circleMap z₀ ‖z - z₀‖ (arg (z - z₀)) = z := by
      simp [circleMap, norm_mul_exp_arg_mul_I]
    exact hz' ▸ hu _ ⟨hz.1, hz.2.1⟩ _ hz.2.2
  rw [setIntegral_congr_fun hmeas
    (fun z hz ↦ extDeriv_bilinearPullbackOneForm_apply B (hsector z hz) _ _)] at h
  simpa [bilinearPullbackOneForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def, smul_smul] using h

end TauCeti
