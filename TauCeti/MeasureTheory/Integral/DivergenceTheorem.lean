/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import TauCeti.MeasureTheory.Integral.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.Analysis.Calculus.Bilinear

/-!
# Green's formula for bilinear pairings on rectangles and annuli

Let `u : ℝ × ℝ → V` be a `C²` map near a closed rectangle `R = [a₁, b₁] × [a₂, b₂]` and let `B` be
a continuous bilinear map. Writing `∂s u` and `∂t u` for the derivatives of `u` in the directions
`(1, 0)` and `(0, 1)`,

`∫_R (B (∂s u) (∂t u) - B (∂t u) (∂s u)) = ∮_{∂R} B (u) (du)`,

where the right-hand side is the integral over the positively oriented boundary of `R`, written
out as four interval integrals. This is Green's theorem for the pullback along `u` of the one-form
`x ↦ B x`, whose exterior derivative is the constant two-form `(v, w) ↦ B v w - B w v`. It is
obtained from Mathlib's divergence theorem on a rectangle
(`MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_of_le`) applied to the vector field
`(B u (∂t u), -B u (∂s u))`, whose divergence is the integrand above once the mixed second
derivatives of `u` cancel by symmetry; the derivatives of the two components are
`ContinuousLinearMap.hasFDerivAt_bilinear_fderiv_apply`.

For a compactly supported map on the whole plane the boundary terms are absent and the integral
vanishes (`TauCeti.integral_bilinear_fderiv_apply_comm`). With boundary, this is the formula that
expresses the symplectic area of a map from a rectangle into an exact symplectic vector space by
integrals of a primitive along its four sides.

The annular form applies the rectangle formula to the polar pullback. Its angular seam terms
cancel, and the radial Jacobian converts the interior integral to the annulus. Neither the map
nor its derivatives need be defined regularly on the inner disc.

## Main results

* `ContinuousLinearMap.integral_bilinear_fderiv_sub_prod_Icc`: Green's formula above, over
  `Set.Icc a b` for points `a ≤ b` of `ℝ × ℝ`.
* `ContinuousLinearMap.integral_bilinear_fderiv_sub_annulus`: the corresponding formula on a
  translated annulus of positive inner radius, with outer minus inner circle boundary terms.
-/

public section

namespace TauCeti

open MeasureTheory Set Complex
open scoped Real

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

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
  have hfd : ∀ z ∈ Icc a b, HasFDerivAt (fun y ↦ B (u y) (fderiv ℝ u y (0, 1)))
      (fderiv ℝ (fun y ↦ B (u y) (fderiv ℝ u y (0, 1))) z) z := fun z hz ↦
    (B.hasFDerivAt_bilinear_fderiv_apply (hu z hz) _).differentiableAt.hasFDerivAt
  have hgd : ∀ z ∈ Icc a b, HasFDerivAt (fun y ↦ -B (u y) (fderiv ℝ u y (1, 0)))
      (fderiv ℝ (fun y ↦ -B (u y) (fderiv ℝ u y (1, 0))) z) z := fun z hz ↦
    (B.hasFDerivAt_bilinear_fderiv_apply (hu z hz) _).neg.differentiableAt.hasFDerivAt
  have hIoo : Ioo a.1 b.1 ×ˢ Ioo a.2 b.2 ⊆ Icc a b := by
    rw [Icc_prod_eq]
    exact prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  -- on the rectangle the divergence of the vector field is the integrand: the mixed partials cancel
  have hdiv : EqOn (fun z ↦ fderiv ℝ (fun y ↦ B (u y) (fderiv ℝ u y (0, 1))) z (1, 0) +
        fderiv ℝ (fun y ↦ -B (u y) (fderiv ℝ u y (1, 0))) z (0, 1))
      (fun z ↦ B (fderiv ℝ u z (1, 0)) (fderiv ℝ u z (0, 1)) -
        B (fderiv ℝ u z (0, 1)) (fderiv ℝ u z (1, 0))) (Icc a b) := by
    intro z hz
    have hsymm := ((hu z hz).isSymmSndFDerivAt (by simp)).eq (1, 0) (0, 1)
    have hg : fderiv ℝ (fun y ↦ -B (u y) (fderiv ℝ u y (1, 0))) z =
        -(B.precompR (ℝ × ℝ) (u z) ((fderiv ℝ (fderiv ℝ u) z).flip (1, 0)) +
          B.precompL (ℝ × ℝ) (fderiv ℝ u z) (fderiv ℝ u z (1, 0))) :=
      (B.hasFDerivAt_bilinear_fderiv_apply (hu z hz) _).neg.fderiv
    simp only [(B.hasFDerivAt_bilinear_fderiv_apply (hu z hz) _).fderiv, hg]
    simp [hsymm]
    abel
  have hcont : ContinuousOn (fun z ↦ B (fderiv ℝ u z (1, 0)) (fderiv ℝ u z (0, 1)) -
      B (fderiv ℝ u z (0, 1)) (fderiv ℝ u z (1, 0))) (Icc a b) := fun z hz ↦ by
    have hdu := (hu z hz).continuousAt_fderiv (by norm_num)
    exact (((B.continuous.continuousAt.comp (hdu.clm_apply continuousAt_const)).clm_apply
      (hdu.clm_apply continuousAt_const)).sub
      ((B.continuous.continuousAt.comp (hdu.clm_apply continuousAt_const)).clm_apply
        (hdu.clm_apply continuousAt_const))).continuousWithinAt
  have hgreen := integral_divergence_prod_Icc_of_hasFDerivAt_of_le _ _ _ _ a b hle
    (fun z hz ↦ (hfd z hz).continuousAt.continuousWithinAt)
    (fun z hz ↦ (hgd z hz).continuousAt.continuousWithinAt)
    (fun z hz ↦ hfd z (hIoo hz)) (fun z hz ↦ hgd z (hIoo hz))
    ((hcont.integrableOn_compact isCompact_Icc).congr_fun hdiv.symm measurableSet_Icc)
  rw [setIntegral_congr_fun measurableSet_Icc hdiv] at hgreen
  rw [hgreen, intervalIntegral.integral_neg, intervalIntegral.integral_neg]
  abel

/-- **Green's formula on a closed annulus.** For a `C²` map near the annulus of positive radii
`a ≤ b`, the integral of the alternating part of a bilinear pairing of its derivatives equals
the outer circle integral of `B u du` minus the inner circle integral. Both circles are
parametrized counterclockwise; their difference gives the boundary orientation. -/
theorem _root_.ContinuousLinearMap.integral_bilinear_fderiv_sub_annulus
    (B : V →L[ℝ] V →L[ℝ] W) {u : ℂ → V} (z₀ : ℂ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hu : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ContDiffAt ℝ 2 u z) :
    ∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b},
      (B (fderiv ℝ u z 1) (fderiv ℝ u z I) -
        B (fderiv ℝ u z I) (fderiv ℝ u z 1)) =
      (∫ θ in -π..π, B (u (circleMap z₀ b θ))
        (fderiv ℝ u (circleMap z₀ b θ) (circleMap 0 b θ * I))) -
      (∫ θ in -π..π, B (u (circleMap z₀ a θ))
        (fderiv ℝ u (circleMap z₀ a θ) (circleMap 0 a θ * I))) := by
  let P : ℝ × ℝ → ℂ := fun p ↦ z₀ + Complex.polarCoord.symm p
  let v := u ∘ P
  have hP : ContDiff ℝ 2 P := by
    simp only [P, Complex.polarCoord_symm_apply, ← Complex.ofRealCLM_apply]
    fun_prop
  have hπ : (-π : ℝ) ≤ π := by linarith [Real.pi_pos]
  have hmem : ∀ p ∈ Icc (a, -π) (b, π),
      P p ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} := by
    intro p hp
    simp only [mem_Icc, Prod.le_def] at hp
    simpa only [mem_ofPred_eq, P, add_sub_cancel_left, Complex.norm_polarCoord_symm,
      abs_of_nonneg (le_trans ha.le hp.1.1)] using And.intro hp.1.1 hp.2.1
  have hv : ∀ p ∈ Icc (a, -π) (b, π), ContDiffAt ℝ 2 v p :=
    fun p hp ↦ (hu _ (hmem p hp)).comp p hP.contDiffAt
  -- Apply rectangular Green to the polar pullback.
  have hgreen := B.integral_bilinear_fderiv_sub_prod_Icc
    (a := (a, -π)) (b := (b, π)) ⟨hab, by linarith [Real.pi_pos]⟩ hv
  -- Mathlib supplies the polar derivative; compose it with the derivative of `u`.
  have hd : ∀ p ∈ Icc (a, -π) (b, π), fderiv ℝ v p =
      (fderiv ℝ u (P p)).comp
        (Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp (fderivPolarCoordSymm p)) :=
    fun p hp ↦ ((hu _ (hmem p hp)).differentiableAt (by norm_num)).hasFDerivAt.comp p
      (hasFDerivAt_add_polarCoord_symm p z₀) |>.fderiv
  have hdr : ∀ p ∈ Icc (a, -π) (b, π), fderiv ℝ v p (1, 0) =
      fderiv ℝ u (P p) (Complex.exp (p.2 * I)) := by
    intro p hp
    simp only [hd p hp, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      equivRealProd_symm_fderivPolarCoordSymm_apply_one_zero]
  have hdt : ∀ p ∈ Icc (a, -π) (b, π), fderiv ℝ v p (0, 1) =
      fderiv ℝ u (P p) (circleMap 0 p.1 p.2 * I) := by
    intro p hp
    simp only [hd p hp, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      equivRealProd_symm_fderivPolarCoordSymm_apply_zero_one]
  -- The alternating pairing has exactly the radial Jacobian of polar integration.
  have harea : (∫ p in Icc (a, -π) (b, π),
      B (fderiv ℝ v p (1, 0)) (fderiv ℝ v p (0, 1)) -
        B (fderiv ℝ v p (0, 1)) (fderiv ℝ v p (1, 0))) =
      ∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b},
        B (fderiv ℝ u z 1) (fderiv ℝ u z I) - B (fderiv ℝ u z I) (fderiv ℝ u z 1) := by
    rw [← Complex.integral_comp_polarCoord_symm_Icc _ z₀ ha]
    exact setIntegral_congr_fun measurableSet_Icc fun p hp ↦ by
      rw [hdr p hp, hdt p hp]
      exact B.apply_exp_circleMap_sub_swap (fderiv ℝ u (P p)) p.1 p.2
  have hPc (r θ : ℝ) : P (r, θ) = circleMap z₀ r θ := by
    simp [P, Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]
  -- The radial edges of the rectangle give the two circle integrals.
  have hcircle (r : ℝ) (hr : r ∈ Icc a b) :
      (∫ θ in -π..π, B (v (r, θ)) (fderiv ℝ v (r, θ) (0, 1))) =
        ∫ θ in -π..π, B (u (circleMap z₀ r θ))
          (fderiv ℝ u (circleMap z₀ r θ) (circleMap 0 r θ * I)) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    have hθ' : -π ≤ θ ∧ θ ≤ π := by
      simpa only [uIcc_of_le hπ, mem_Icc] using hθ
    simp only [hdt (r, θ) ⟨⟨hr.1, hθ'.1⟩, ⟨hr.2, hθ'.2⟩⟩]
    simp [v, hPc]
  -- At the angular seam the map and its radial derivative agree, so these edges cancel.
  have hseam : (∫ r in a..b, B (v (r, π)) (fderiv ℝ v (r, π) (1, 0))) =
      ∫ r in a..b, B (v (r, -π)) (fderiv ℝ v (r, -π) (1, 0)) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : a ≤ r ∧ r ≤ b := by simpa only [uIcc_of_le hab, mem_Icc] using hr
    simp only [hdr (r, π) ⟨⟨hr'.1, by linarith [Real.pi_pos]⟩, ⟨hr'.2, le_rfl⟩⟩,
      hdr (r, -π) ⟨⟨hr'.1, le_rfl⟩, ⟨hr'.2, by linarith [Real.pi_pos]⟩⟩]
    simp [v, P, Complex.polarCoord_symm_apply, Complex.exp_mul_I]
  rw [harea, hcircle b ⟨hab, le_rfl⟩, hcircle a ⟨le_rfl, hab⟩,
    hseam, sub_self, sub_zero] at hgreen
  exact hgreen

end TauCeti
