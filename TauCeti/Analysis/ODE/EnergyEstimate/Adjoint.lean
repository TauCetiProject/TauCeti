/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.EnergyEstimate.Global

/-!
# The formal adjoint of a trajectory operator

For a continuous family of symmetric operators `A(s)`, integration by parts identifies the
formal adjoint of the trajectory operator

`D_A u = u' + A u`

with `D_A^* v = -v' + A v`.  This file proves the identity on compactly supported continuously
differentiable paths.  It also proves the same global and tail coercive estimates for the formal
adjoint that are available for `D_A` itself.

The adjoint estimates are the cokernel input for the Fredholm property of the Sobolev realization
of `D_A`: after identifying vectors orthogonal to its range with weak solutions of the adjoint
equation, the estimates control those solutions by the same compact error used for the kernel.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*,
  2nd ed., Appendix A.1.
* M. Schwarz, *Morse Homology*, Chapter 2.
-/

public section

namespace TauCeti

open MeasureTheory Filter Set
open scoped InnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {A : ℝ → E →L[ℝ] E} {u v : ℝ → E}

/-- **Formal-adjoint identity for a trajectory operator.** When `u` has compact support, the
`L²` pairing of `u' + A u` with a `C¹` path `v` equals the pairing of `u` with `-v' + A v`
whenever the coefficient operators are symmetric. -/
theorem integral_inner_deriv_add_apply_eq_integral_inner_neg_deriv_add_apply
    (hA : Continuous A) (hsym : ∀ s, (A s).toLinearMap.IsSymmetric)
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hcu : HasCompactSupport u) :
    (∫ s, ⟪deriv u s + A s (u s), v s⟫_ℝ) =
      ∫ s, ⟪u s, -deriv v s + A s (v s)⟫_ℝ := by
  have hduv : Integrable (fun s ↦ ⟪deriv u s, v s⟫_ℝ) :=
    (hu.continuous_deriv_one.inner hv.continuous).integrable_of_hasCompactSupport <|
      hcu.deriv.mono fun s hs hdu ↦ hs (by simp [hdu])
  have hudv : Integrable (fun s ↦ ⟪u s, deriv v s⟫_ℝ) :=
    (hu.continuous.inner hv.continuous_deriv_one).integrable_of_hasCompactSupport <|
      hcu.mono fun s hs hus ↦ hs (by simp [hus])
  have hAuv : Integrable (fun s ↦ ⟪u s, A s (v s)⟫_ℝ) :=
    (hu.continuous.inner (hA.clm_apply hv.continuous)).integrable_of_hasCompactSupport <|
      hcu.mono fun s hs hus ↦ hs (by simp [hus])
  have hibp : (∫ s, ⟪u s, deriv v s⟫_ℝ) = -∫ s, ⟪deriv u s, v s⟫_ℝ :=
    integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable (L := innerSL ℝ)
      (fun s _ ↦ (hu.differentiable one_ne_zero s).hasDerivAt)
      (fun s _ ↦ (hv.differentiable one_ne_zero s).hasDerivAt) hudv hduv
      ((hu.continuous.inner hv.continuous).integrable_of_hasCompactSupport <|
        hcu.mono fun s hs hus ↦ hs (by simp [hus]))
  simp only [inner_add_left, inner_add_right, inner_neg_right, (hsym _).apply_clm]
  rw [integral_add hduv hAuv, integral_add (f := fun s ↦ -⟪u s, deriv v s⟫_ℝ) hudv.neg hAuv,
    integral_neg, hibp, neg_neg]

/-- The hypotheses of the forward trajectory estimates on the coefficient family `A` transfer to
the negated family `-A`. -/
theorem neg_trajectory_hypotheses
    (hA : ContDiff ℝ 1 A) (hsym : ∀ s, (A s).toLinearMap.IsSymmetric)
    {Aminus Aplus : E →L[ℝ] E} {α : ℝ}
    (hminus : ∀ w, α * ‖w‖ ≤ ‖Aminus w‖) (hplus : ∀ w, α * ‖w‖ ≤ ‖Aplus w‖)
    (hdbot : Tendsto (deriv A) atBot (nhds 0)) (hdtop : Tendsto (deriv A) atTop (nhds 0)) :
    ContDiff ℝ 1 (-A) ∧ (∀ s, ((-A) s).toLinearMap.IsSymmetric) ∧
      (∀ w, α * ‖w‖ ≤ ‖(-Aminus) w‖) ∧ (∀ w, α * ‖w‖ ≤ ‖(-Aplus) w‖) ∧
      Tendsto (deriv (-A)) atBot (nhds 0) ∧ Tendsto (deriv (-A)) atTop (nhds 0) :=
  ⟨hA.neg, fun s ↦ by simpa using LinearMap.IsSymmetric.zero.sub (hsym s),
    by simpa using hminus, by simpa using hplus,
    by simpa [deriv.neg'] using hdbot.neg, by simpa [deriv.neg'] using hdtop.neg⟩

/-- The operator `d/ds - A(s)` applied to `w` has the same norm as `-d/ds + A(s)`. -/
private theorem norm_deriv_add_neg_apply (w : ℝ → E) (s : ℝ) :
    ‖deriv w s + (-A) s (w s)‖ = ‖-deriv w s + A s (w s)‖ := by
  rw [← norm_neg]
  simp [add_comm]

/-- **Global coercivity for the formal adjoint.** Under the asymptotic hypotheses for a symmetric
coefficient family, `-d/ds + A(s)` satisfies a global estimate with a compact-interval `L²` error.
The constants are independent of the compactly supported `C¹` path. -/
theorem exists_pos_nonneg_forall_integral_norm_neg_deriv_add_sq_add_mul_integral_norm_sq_le
    (hA : ContDiff ℝ 1 A) (hsym : ∀ s, (A s).toLinearMap.IsSymmetric)
    {Aminus Aplus : E →L[ℝ] E} {α : ℝ} (hα : 0 < α)
    (hminus : ∀ w, α * ‖w‖ ≤ ‖Aminus w‖) (hplus : ∀ w, α * ‖w‖ ≤ ‖Aplus w‖)
    (hbot : Tendsto A atBot (nhds Aminus)) (htop : Tendsto A atTop (nhds Aplus))
    (hdbot : Tendsto (deriv A) atBot (nhds 0)) (hdtop : Tendsto (deriv A) atTop (nhds 0)) :
    ∃ R > 0, ∃ C ≥ 0, ∀ (w : ℝ → E), ContDiff ℝ 1 w → HasCompactSupport w →
      (∫ s, ‖deriv w s‖ ^ 2) + (α ^ 2 / 2) * (∫ s, ‖w s‖ ^ 2) ≤
        (∫ s, ‖-deriv w s + A s (w s)‖ ^ 2) + C * ∫ s in Icc (-R) R, ‖w s‖ ^ 2 := by
  obtain ⟨hB, hBsym, hBminus, hBplus, hdBbot, hdBtop⟩ :=
    neg_trajectory_hypotheses hA hsym hminus hplus hdbot hdtop
  obtain ⟨R, hR, C, hC, hest⟩ :=
    exists_pos_nonneg_forall_integral_norm_deriv_sq_add_mul_integral_norm_sq_le
      hB hBsym hα hBminus hBplus hbot.neg htop.neg hdBbot hdBtop
  exact ⟨R, hR, C, hC, fun w hw hcw ↦ by
    simpa only [norm_deriv_add_neg_apply] using hest w hw hcw⟩

/-- **Coercivity at infinity for the formal adjoint.** Under the asymptotic hypotheses for a
symmetric coefficient family, `-d/ds + A(s)` controls the `L²` value and derivative of every
compactly supported `C¹` path supported outside one fixed compact interval. -/
theorem exists_pos_forall_integral_norm_neg_deriv_add_sq_add_mul_integral_norm_sq_le
    (hA : ContDiff ℝ 1 A) (hsym : ∀ s, (A s).toLinearMap.IsSymmetric)
    {Aminus Aplus : E →L[ℝ] E} {α : ℝ} (hα : 0 < α)
    (hminus : ∀ w, α * ‖w‖ ≤ ‖Aminus w‖) (hplus : ∀ w, α * ‖w‖ ≤ ‖Aplus w‖)
    (hbot : Tendsto A atBot (nhds Aminus)) (htop : Tendsto A atTop (nhds Aplus))
    (hdbot : Tendsto (deriv A) atBot (nhds 0)) (hdtop : Tendsto (deriv A) atTop (nhds 0)) :
    ∃ R > 0, ∀ (w : ℝ → E), ContDiff ℝ 1 w → HasCompactSupport w →
      Function.support w ⊆ {s | R ≤ |s|} →
      (∫ s, ‖deriv w s‖ ^ 2) + (α ^ 2 / 2) * (∫ s, ‖w s‖ ^ 2) ≤
        ∫ s, ‖-deriv w s + A s (w s)‖ ^ 2 := by
  obtain ⟨hB, hBsym, hBminus, hBplus, hdBbot, hdBtop⟩ :=
    neg_trajectory_hypotheses hA hsym hminus hplus hdbot hdtop
  obtain ⟨R, hR, hest⟩ :=
    exists_pos_forall_integral_norm_deriv_sq_add_mul_integral_norm_sq_le
      hB hBsym hα hBminus hBplus hbot.neg htop.neg hdBbot hdBtop
  exact ⟨R, hR, fun w hw hcw hsupport ↦ by
    simpa only [norm_deriv_add_neg_apply] using hest w hw hcw hsupport⟩

end TauCeti

end
