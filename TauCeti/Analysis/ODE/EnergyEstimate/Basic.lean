/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Energy estimates for a first-order operator on the line

For a continuously differentiable family of operators `A(s)` on a real inner product
space, symmetric wherever the path is nonzero, integration by parts gives

`∫ ‖u' + A u‖² = ∫ ‖u'‖² + ∫ ‖A u‖² - ∫ ⟪u, A' u⟫`.

We prove this identity for compactly supported `C¹` paths, without a finite-dimensionality or
completeness assumption on the target. A spectral gap for `A` and a small upper bound on the
quadratic form of `A'` give a coercive estimate. A second integration by parts, against a `C¹`
family `S(s)` of symmetric operators, gives

`∫ ⟪S (u' + A u), u⟫ = ∫ ⟪S A u, u⟫ - ½ ∫ ⟪S' u, u⟫`

for any continuous family `A`, with no symmetry of `A` assumed. Global estimates with an interior
error and coercivity outside a compact interval are developed in `EnergyEstimate.Global`. These
estimates for bounded coefficients are inputs to the Fredholm property
of `d/ds + A(s)`; they do not assert surjectivity or the Fredholm property, nor treat unbounded
transverse operators on a strip.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Appendix A (first-order Fredholm operators).
* M. Schwarz, *Morse Homology*, Chapter 2 (linearized trajectory operators).
-/

public section

namespace TauCeti

open MeasureTheory Filter Set
open scoped InnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {A : ℝ → E →L[ℝ] E} {u : ℝ → E}

/-- The squared coefficient norm and coefficient-derivative quadratic form are integrable
along a compactly supported continuous path. -/
theorem integrable_norm_apply_sq_and_inner_deriv_apply (hA : ContDiff ℝ 1 A) (hu : Continuous u)
    (hc : HasCompactSupport u) :
    Integrable (fun s ↦ ‖A s (u s)‖ ^ 2) ∧
      Integrable (fun s ↦ ⟪u s, deriv A s (u s)⟫_ℝ) := by
  have hAu : HasCompactSupport (fun s ↦ A s (u s)) :=
    hc.mono (fun s hs hu0 ↦ hs (by simp [hu0]))
  have hcorr : HasCompactSupport (fun s ↦ ⟪u s, deriv A s (u s)⟫_ℝ) :=
    hc.mono (fun s hs hu0 ↦ hs (by simp [hu0]))
  have hcA : HasCompactSupport (fun s ↦ ‖A s (u s)‖ ^ 2) :=
    hAu.norm.comp_left (g := fun x : ℝ ↦ x ^ 2) (by norm_num)
  have hiA : Integrable (fun s ↦ ‖A s (u s)‖ ^ 2) :=
    ((hA.continuous.clm_apply hu).norm.pow 2).integrable_of_hasCompactSupport hcA
  have hiCorr : Integrable (fun s ↦ ⟪u s, deriv A s (u s)⟫_ℝ) :=
    Continuous.integrable_of_hasCompactSupport
      (hu.inner (hA.continuous_deriv_one.clm_apply hu)) hcorr
  exact ⟨hiA, hiCorr⟩

/-- The energy identity for `d/ds + A(s)`. The coefficient derivative contributes with a minus
sign. Symmetry is needed only on the support of the path, and is not assumed separately for the
coefficient derivative. -/
theorem integral_norm_deriv_add_sq_eq (hA : ContDiff ℝ 1 A)
    (hsym : ∀ s ∈ Function.support u, (A s).toLinearMap.IsSymmetric) (hu : ContDiff ℝ 1 u)
    (hc : HasCompactSupport u) :
    (∫ s, ‖deriv u s + A s (u s)‖ ^ 2) =
      (∫ s, ‖deriv u s‖ ^ 2) + (∫ s, ‖A s (u s)‖ ^ 2) -
        ∫ s, ⟪u s, deriv A s (u s)⟫_ℝ := by
  -- Compact support makes every term in the integration-by-parts identity integrable.
  obtain ⟨hiA, hiCorr⟩ := integrable_norm_apply_sq_and_inner_deriv_apply hA hu.continuous hc
  have hpot : HasCompactSupport (fun s ↦ ⟪u s, A s (u s)⟫_ℝ) :=
    hc.mono (fun s hs hu0 ↦ hs (by simp [hu0]))
  have hcross : HasCompactSupport (fun s ↦ ⟪deriv u s, A s (u s)⟫_ℝ) :=
    hc.mono (fun s hs hu0 ↦ hs (by simp [hu0]))
  have hcD : HasCompactSupport (fun s ↦ ‖deriv u s‖ ^ 2) :=
    hc.deriv.norm.comp_left (g := fun x : ℝ ↦ x ^ 2) (by norm_num)
  have hiD : Integrable (fun s ↦ ‖deriv u s‖ ^ 2) :=
    (hu.continuous_deriv_one.norm.pow 2).integrable_of_hasCompactSupport hcD
  have hiCross : Integrable (fun s ↦ ⟪deriv u s, A s (u s)⟫_ℝ) :=
    Continuous.integrable_of_hasCompactSupport
      (hu.continuous_deriv_one.inner (hA.continuous.clm_apply hu.continuous)) hcross
  -- Differentiate the potential `⟪u, A u⟫`, then integrate its derivative over the line.
  have hder (s : ℝ) : HasDerivAt (fun s ↦ ⟪u s, A s (u s)⟫_ℝ)
      (2 * ⟪deriv u s, A s (u s)⟫_ℝ + ⟪u s, deriv A s (u s)⟫_ℝ) s := by
    convert (hu.differentiable one_ne_zero s).hasDerivAt.inner ℝ
      ((hA.differentiable one_ne_zero s).hasDerivAt.clm_apply
        (hu.differentiable one_ne_zero s).hasDerivAt) using 1
    simp only [inner_add_right]
    by_cases hs : u s = 0
    · simp [hs]
    · rw [← (hsym s hs).apply_clm (u s) (deriv u s),
        real_inner_comm (A s (u s)) (deriv u s)]
      ring
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hder
    ((hiCross.const_mul 2).add hiCorr)
    ((hu.inner ℝ (hA.clm_apply hu)).continuous.integrable_of_hasCompactSupport hpot)
  rw [integral_add (hiCross.const_mul 2) hiCorr, integral_const_mul] at hzero
  have hexpand : (∫ s, ‖deriv u s + A s (u s)‖ ^ 2) =
      (∫ s, ‖deriv u s‖ ^ 2) + 2 * (∫ s, ⟪deriv u s, A s (u s)⟫_ℝ) +
        ∫ s, ‖A s (u s)‖ ^ 2 := by
    simp only [norm_add_sq_real]
    have hiSum : Integrable (fun s ↦ ‖deriv u s‖ ^ 2 + 2 * ⟪deriv u s, A s (u s)⟫_ℝ) :=
      hiD.add (hiCross.const_mul 2)
    rw [integral_add hiSum hiA, integral_add hiD (hiCross.const_mul 2), integral_const_mul]
  linarith

/-- The integrand `⟪T w, u⟫` is integrable when `T` and `w` are continuous and `u` is a compactly
supported continuous path. -/
theorem integrable_inner_apply_of_hasCompactSupport {T : ℝ → E →L[ℝ] E} {w : ℝ → E}
    (hT : Continuous T) (hw : Continuous w) (hu : Continuous u) (hc : HasCompactSupport u) :
    Integrable fun s ↦ ⟪T s (w s), u s⟫_ℝ :=
  ((hT.clm_apply hw).inner hu).integrable_of_hasCompactSupport
    (hc.mono fun s hs hu0 ↦ hs (by simp [hu0]))

omit [InnerProductSpace ℝ E] in
/-- The squared norm of a compactly supported continuous path is integrable. -/
theorem integrable_norm_sq_of_hasCompactSupport {w : ℝ → E} (hw : Continuous w)
    (hc : HasCompactSupport w) : Integrable fun s ↦ ‖w s‖ ^ 2 := by
  have hcs : HasCompactSupport fun s ↦ ‖w s‖ ^ 2 :=
    hc.norm.comp_left (g := fun x : ℝ ↦ x ^ 2) (by norm_num)
  exact (hw.norm.pow 2).integrable_of_hasCompactSupport hcs

/-- **Integration by parts against a family of quadratic forms.** For a `C¹` family `S` of
symmetric operators, a continuous family `A` and a compactly supported `C¹` path `u`,

`∫ ⟪S (u' + A u), u⟫ = ∫ ⟪S A u, u⟫ - ½ ∫ ⟪S' u, u⟫`. -/
theorem integral_inner_apply_deriv_add_eq {S : ℝ → E →L[ℝ] E} (hS : ContDiff ℝ 1 S)
    (hsym : ∀ s, (S s : E →ₗ[ℝ] E).IsSymmetric) (hA : Continuous A) (hu : ContDiff ℝ 1 u)
    (hc : HasCompactSupport u) :
    ∫ s, ⟪S s (deriv u s + A s (u s)), u s⟫_ℝ =
      (∫ s, ⟪S s (A s (u s)), u s⟫_ℝ) - (∫ s, ⟪deriv S s (u s), u s⟫_ℝ) / 2 := by
  have hiD := integrable_inner_apply_of_hasCompactSupport hS.continuous hu.continuous_deriv_one
    hu.continuous hc
  have hiA := integrable_inner_apply_of_hasCompactSupport hS.continuous
    (hA.clm_apply hu.continuous) hu.continuous hc
  have hiS := integrable_inner_apply_of_hasCompactSupport hS.continuous_deriv_one hu.continuous
    hu.continuous hc
  have hiq := integrable_inner_apply_of_hasCompactSupport hS.continuous hu.continuous
    hu.continuous hc
  have hder (s : ℝ) : HasDerivAt (fun s ↦ ⟪S s (u s), u s⟫_ℝ)
      (⟪deriv S s (u s), u s⟫_ℝ + 2 * ⟪S s (deriv u s), u s⟫_ℝ) s := by
    have hus := (hu.differentiable one_ne_zero s).hasDerivAt
    convert ((hS.differentiable one_ne_zero s).hasDerivAt.clm_apply hus).inner ℝ hus using 1
    rw [inner_add_left, (hsym s).apply_clm (u s) (deriv u s),
      real_inner_comm (S s (deriv u s)) (u s)]
    ring
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hder (hiS.add (hiD.const_mul 2)) hiq
  rw [integral_add hiS (hiD.const_mul 2), integral_const_mul] at hzero
  simp only [map_add, inner_add_left]
  rw [integral_add hiD hiA]
  linarith

/-- A spectral gap and a bound on the coefficient derivative give a coercive estimate for a
compactly supported path. Symmetry and both bounds need hold only where the path is nonzero.
The estimate is useful when `β < α²`, but is valid without that extra hypothesis. -/
theorem integral_norm_deriv_sq_add_mul_integral_norm_sq_le (hA : ContDiff ℝ 1 A)
    (hsym : ∀ s ∈ Function.support u, (A s).toLinearMap.IsSymmetric) (hu : ContDiff ℝ 1 u)
    (hc : HasCompactSupport u) {α β : ℝ} (hα : 0 ≤ α)
    (hgap : ∀ s ∈ Function.support u, α * ‖u s‖ ≤ ‖A s (u s)‖)
    (hsmall : ∀ s ∈ Function.support u, ⟪u s, deriv A s (u s)⟫_ℝ ≤ β * ‖u s‖ ^ 2) :
    (∫ s, ‖deriv u s‖ ^ 2) + (α ^ 2 - β) * (∫ s, ‖u s‖ ^ 2) ≤
      ∫ s, ‖deriv u s + A s (u s)‖ ^ 2 := by
  obtain ⟨hiA, hiCorr⟩ := integrable_norm_apply_sq_and_inner_deriv_apply hA hu.continuous hc
  have hcu : HasCompactSupport (fun s ↦ ‖u s‖ ^ 2) :=
    hc.norm.comp_left (g := fun x : ℝ ↦ x ^ 2) (by norm_num)
  have hiu : Integrable (fun s ↦ ‖u s‖ ^ 2) :=
    (hu.continuous.norm.pow 2).integrable_of_hasCompactSupport hcu
  have h₁ : α ^ 2 * (∫ s, ‖u s‖ ^ 2) ≤ ∫ s, ‖A s (u s)‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono (hiu.const_mul _) hiA
    intro s
    by_cases hs : u s = 0
    · simp only [hs, map_zero, norm_zero, zero_pow two_ne_zero, mul_zero, le_refl]
    · simpa only [mul_pow] using
        pow_le_pow_left₀ (mul_nonneg hα (norm_nonneg _)) (hgap s hs) 2
  have h₂ : (∫ s, ⟪u s, deriv A s (u s)⟫_ℝ) ≤ β * ∫ s, ‖u s‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono hiCorr (hiu.const_mul _)
    intro s
    by_cases hs : u s = 0
    · simp only [hs, inner_zero_left, norm_zero, zero_pow two_ne_zero, mul_zero, le_refl]
    · exact hsmall s hs
  rw [integral_norm_deriv_add_sq_eq hA hsym hu hc]
  nlinarith

end TauCeti
