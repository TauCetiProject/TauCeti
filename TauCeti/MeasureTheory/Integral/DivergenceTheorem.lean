/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import TauCeti.Analysis.Calculus.Bilinear

/-!
# Green's formula for a bilinear pairing of partial derivatives on a rectangle

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
`TauCeti.hasFDerivAt_bilinear_fderiv_apply`.

For a compactly supported map on the whole plane the boundary terms are absent and the integral
vanishes (`TauCeti.integral_bilinear_fderiv_apply_comm`). With boundary, this is the formula that
expresses the symplectic area of a map from a rectangle into an exact symplectic vector space by
integrals of a primitive along its four sides.

## Main results

* `TauCeti.integral_bilinear_fderiv_sub_prod_Icc`: Green's formula above, over `Set.Icc a b` for
  points `a ≤ b` of `ℝ × ℝ`.
-/

public section

namespace TauCeti

open MeasureTheory Set

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **Green's formula for a bilinear pairing of partial derivatives.** If `u` is `C²` at every
point of the rectangle `Icc a b ⊆ ℝ × ℝ` and `B` is a continuous bilinear map, the integral over
the rectangle of `B (∂s u) (∂t u) - B (∂t u) (∂s u)` is the integral of the one-form `B u (du)`
over the positively oriented boundary: the right side minus the left side of
`t ↦ B u (∂t u)`, minus the top side minus the bottom side of `s ↦ B u (∂s u)`. -/
theorem integral_bilinear_fderiv_sub_prod_Icc (B : V →L[ℝ] V →L[ℝ] W)
    {u : ℝ × ℝ → V} {a b : ℝ × ℝ} (hle : a ≤ b) (hu : ∀ z ∈ Icc a b, ContDiffAt ℝ 2 u z) :
    ∫ z in Icc a b, (B (fderiv ℝ u z (1, 0)) (fderiv ℝ u z (0, 1)) -
        B (fderiv ℝ u z (0, 1)) (fderiv ℝ u z (1, 0))) =
      ((∫ t in a.2..b.2, B (u (b.1, t)) (fderiv ℝ u (b.1, t) (0, 1))) -
          ∫ t in a.2..b.2, B (u (a.1, t)) (fderiv ℝ u (a.1, t) (0, 1))) -
        ((∫ s in a.1..b.1, B (u (s, b.2)) (fderiv ℝ u (s, b.2) (1, 0))) -
          ∫ s in a.1..b.1, B (u (s, a.2)) (fderiv ℝ u (s, a.2) (1, 0))) := by
  have hfd : ∀ z ∈ Icc a b, HasFDerivAt (fun y ↦ B (u y) (fderiv ℝ u y (0, 1)))
      (fderiv ℝ (fun y ↦ B (u y) (fderiv ℝ u y (0, 1))) z) z := fun z hz ↦
    (hasFDerivAt_bilinear_fderiv_apply B (hu z hz) _).differentiableAt.hasFDerivAt
  have hgd : ∀ z ∈ Icc a b, HasFDerivAt (fun y ↦ -B (u y) (fderiv ℝ u y (1, 0)))
      (fderiv ℝ (fun y ↦ -B (u y) (fderiv ℝ u y (1, 0))) z) z := fun z hz ↦
    (hasFDerivAt_bilinear_fderiv_apply B (hu z hz) _).neg.differentiableAt.hasFDerivAt
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
      (hasFDerivAt_bilinear_fderiv_apply B (hu z hz) _).neg.fderiv
    simp only [(hasFDerivAt_bilinear_fderiv_apply B (hu z hz) _).fderiv, hg]
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

end TauCeti
