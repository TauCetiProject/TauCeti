/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LeadingEigenvector.Basic
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.SinTheta.Corollaries
public import TauCeti.Analysis.InnerProductSpace.UnitVector

/-!
# Davis–Kahan for the leading eigenvector

Let `Σ` and `P` be self-adjoint operators on a finite-dimensional real inner product space, and
let `θ` be a unit eigenvector of `Σ`, `Σ θ = γ θ`, with `⟪u, Σ u⟫ ≤ (γ - ν) ‖u‖²` for every
`u ⟂ θ`, so that `γ` is the largest eigenvalue of `Σ` and the gap to the rest of the spectrum is
at least `ν > 0`. If `‖P‖ < ν / 2`, the largest eigenvalue of `Σ + P` is simple: `Σ + P` has a
leading unit eigenvector `θ̂`, unique up to sign, and with the sign chosen so that
`⟪θ̂, θ⟫ ≥ 0`,

  `‖θ̂ - θ‖ ≤ √2 ‖P θ - ⟪θ, P θ⟫ θ‖ / (ν - 2 ‖P‖)`.

The quadratic form of `Σ + P` is at most `(γ - ν + ‖P‖) ‖u‖²` on `θ^⟂`, while the largest
eigenvalue of `Σ + P` is at least `⟪θ, (Σ + P) θ⟫ ≥ γ - ‖P‖`. So every eigenvalue of `Σ + P`
carried by `θ̂^⟂` is at most `γ - ν + ‖P‖`, which gives simplicity, and the residual
Davis–Kahan `sin Θ` theorem for the trial vector `θ` with `m = ⟪θ, (Σ + P) θ⟫` and
`δ = ν - 2 ‖P‖` bounds the sine of the angle between `θ̂` and `θ` by the residual
`(Σ + P) θ - m θ = P θ - ⟪θ, P θ⟫ θ`. For unit vectors with nonnegative inner product the
chord is at most `√2` times the sine.

## Main results

* `IsSelfAdjoint.leading_eigenvector_perturbation`: Davis–Kahan for the leading eigenvector.

## References

* M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge
  University Press, 2019, Theorem 8.5, whose bound has `2` in place of `√2`.
* C. Davis, W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. **7** (1970), 1–46.
* The main theorem is adapted from lean-CKSD (<https://github.com/bjbraams/lean-CKSD>),
  `CKSD/Nonparametric/HighDimensional/EigenvectorPerturbation.lean`,
  `exists_eigenvector_norm_sub_le_of_rayleigh_gap` (with constant `2`).
-/

public section

open scoped RealInnerProductSpace

namespace IsSelfAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Davis–Kahan for the leading eigenvector** (Wainwright, Thm 8.5, with the sharper
constant `√2`). If `θ` is a unit eigenvector of the self-adjoint `Σ` for `γ`, the quadratic form
of `Σ` on `θ^⟂` is at most `γ - ν`, and the self-adjoint perturbation `P` has `‖P‖ < ν / 2`,
then `Σ + P` has a leading unit eigenvector `θ̂` with `⟪θ̂, θ⟫ ≥ 0`, unique up to sign, and
`‖θ̂ - θ‖ ≤ √2 ‖P θ - ⟪θ, P θ⟫ θ‖ / (ν - 2 ‖P‖)`. No separate hypothesis `0 < ν` is needed:
it follows from `‖P‖ < ν / 2`. -/
theorem leading_eigenvector_perturbation {Sig P : E →L[ℝ] E} (hSig : IsSelfAdjoint Sig)
    (hP : IsSelfAdjoint P) {θ : E} (hθ : ‖θ‖ = 1) {γ ν : ℝ} (hγ : Sig θ = γ • θ)
    (hgap : ∀ u, ⟪u, θ⟫ = 0 → ⟪u, Sig u⟫ ≤ (γ - ν) * ‖u‖ ^ 2) (hPν : ‖P‖ < ν / 2) :
    ∃ θh, ((Sig + P : E →L[ℝ] E) : E →ₗ[ℝ] E).IsLeadingUnitEigenvector θh ∧ 0 ≤ ⟪θh, θ⟫ ∧
      (∀ u, ((Sig + P : E →L[ℝ] E) : E →ₗ[ℝ] E).IsLeadingUnitEigenvector u →
        u = θh ∨ u = -θh) ∧
      ‖θh - θ‖ ≤ √2 * ‖P θ - ⟪θ, P θ⟫ • θ‖ / (ν - 2 * ‖P‖) := by
  set A : E →L[ℝ] E := Sig + P
  have hA : (A : E →ₗ[ℝ] E).IsSymmetric := (hSig.add hP).isSymmetric
  have hPq (u : E) : |⟪u, P u⟫| ≤ ‖P‖ * ‖u‖ ^ 2 := by
    calc |⟪u, P u⟫| ≤ ‖u‖ * ‖P u‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖u‖ * (‖P‖ * ‖u‖) := by gcongr; exact P.le_opNorm u
      _ = ‖P‖ * ‖u‖ ^ 2 := by ring
  have hAq (u : E) : ⟪u, A u⟫ = ⟪u, Sig u⟫ + ⟪u, P u⟫ := by
    simp [A, inner_add_right]
  have hperp (u : E) (hu : ⟪u, θ⟫ = 0) : ⟪u, (A : E →ₗ[ℝ] E) u⟫ ≤ (γ - ν + ‖P‖) * ‖u‖ ^ 2 := by
    have := (abs_le.mp (hPq u)).2
    have := hgap u hu
    simp only [ContinuousLinearMap.coe_coe, hAq]
    linarith
  have hm : ⟪θ, A θ⟫ = γ + ⟪θ, P θ⟫ := by
    rw [hAq, hγ, inner_smul_right, real_inner_self_eq_norm_sq, hθ, one_pow, mul_one]
  have hmlow : γ - ‖P‖ ≤ ⟪θ, A θ⟫ := by
    have := (abs_le.mp (hPq θ)).1
    rw [hθ, one_pow, mul_one] at this
    linarith
  have : Nontrivial E := ⟨⟨θ, 0, by rintro rfl; simp at hθ⟩⟩
  -- a leading unit eigenvector, with the sign chosen so that `⟪θh, θ⟫ ≥ 0`
  obtain ⟨θh, hθh, hsign⟩ : ∃ θh, (A : E →ₗ[ℝ] E).IsLeadingUnitEigenvector θh ∧ 0 ≤ ⟪θh, θ⟫ := by
    obtain ⟨w, hw⟩ := (A : E →ₗ[ℝ] E).exists_isLeadingUnitEigenvector
    rcases le_total 0 ⟪w, θ⟫ with h | h
    · exact ⟨w, hw, h⟩
    · exact ⟨-w, hw.neg, by rw [inner_neg_left]; linarith⟩
  have hb : γ - ‖P‖ ≤ ⟪θh, A θh⟫ :=
    hmlow.trans (by simpa [hθ] using hθh.inner_self_apply_le θ)
  -- every eigenvalue of `A` carried by `θh^⟂` is at most `γ - ν + ‖P‖`
  have hev := fun {y : E} ↦ hθh.le_of_apply_eq_smul hperp (y := y)
  refine ⟨θh, hθh, hsign, fun u hu ↦ hθh.eq_or_eq_neg hA (fun y hy hAy ↦ ?_) hu, ?_⟩
  · by_contra hy0
    have := hev hy0 hy hAy
    simp only [ContinuousLinearMap.coe_coe] at this
    linarith
  -- the residual `sin Θ` bound for the trial vector `θ`
  have hsin := hA.mul_norm_sub_inner_smul_le_norm_apply_sub_smul hθh.norm_eq_one
    (hθh.apply_eq_smul hA) (m := ⟪θ, A θ⟫) (δ := ν - 2 * ‖P‖)
    (fun hy0 hy μ hAy ↦ by
      rw [RCLike.ofReal_real_eq_id, id] at hAy
      linarith [hev hy0 hy hAy]) θ
  simp only [RCLike.ofReal_real_eq_id, id] at hsin
  have hres : A θ - ⟪θ, A θ⟫ • θ = P θ - ⟪θ, P θ⟫ • θ := by
    rw [hm, add_apply, hγ, add_smul]
    abel
  rw [hres] at hsin
  rw [norm_sub_rev, mul_div_assoc]
  refine (TauCeti.norm_sub_le_sqrt_two_mul_norm_sub_inner_smul hθh.norm_eq_one hθ hsign).trans ?_
  gcongr
  rw [le_div_iff₀ (by linarith)]
  linarith

end IsSelfAdjoint
