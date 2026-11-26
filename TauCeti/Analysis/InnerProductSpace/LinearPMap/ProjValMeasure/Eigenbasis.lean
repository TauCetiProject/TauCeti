/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Diagonal
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.ProjValMeasure.Basic
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Compact
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic
import TauCeti.Analysis.InnerProductSpace.LinearPMap.Eigenbasis
import TauCeti.LinearAlgebra.LinearPMap.Basic
import TauCeti.MeasureTheory.Measure.ResolventTransform.Inversion

/-!
# Spectral integrals in an eigenbasis and anticommutation

This file provides eigenvector, diagonalization, and anticommutation laws for the bounded
spectral integral `(A.spectralPVM hA).integral`:

* `LinearPMap.spectralPVM_integral_apply_of_apply_eq_smul`: on an eigenvector of `A` with real
  eigenvalue `r`, `(A.spectralPVM hA).integral g` acts as multiplication by `g r`.
* `LinearPMap.spectralPVM_integral_eq_diagonal`: in any orthonormal eigenbasis of `A`,
  `(A.spectralPVM hA).integral g` is diagonal with entries `g (lam i)`.
* `LinearPMap.spectralPVM_integral_apply_of_anticommute` and
  `LinearPMap.mul_spectralPVM_integral_of_anticommute`: any bounded operator preserving `D(A)` and
  anticommuting with `A` anticommutes with `(A.spectralPVM hA).integral g` for odd `g`.
-/

public section

noncomputable section

open Complex MeasureTheory TauCeti
open scoped _root_.ENNReal InnerProductSpace _root_.lp

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

private theorem spectralPVM_diag_eq_smul_dirac (hA : IsSelfAdjoint A) (x : A.domain) {r : ℝ}
    (hx : A x = (r : ℂ) • (x : H)) :
    (A.spectralPVM hA).diag (x : H) = ENNReal.ofReal (‖(x : H)‖ ^ 2) • Measure.dirac r := by
  have : IsFiniteMeasure (ENNReal.ofReal (‖(x : H)‖ ^ 2) • Measure.dirac r) := ⟨by simp⟩
  refine Measure.ext_of_resolventTransform fun z hz ↦ ?_
  have hzA : z ∈ A.resolventSet := hA.mem_resolventSet_of_im_ne_zero hz.ne'
  have hkernel (μ : Measure ℝ) :
      MeasureTheory.resolventTransform μ z = -∫ s : ℝ, (z - s)⁻¹ ∂μ := by
    rw [MeasureTheory.resolventTransform_apply, ← MeasureTheory.integral_neg]
    congr 1 with s
    rw [_root_.resolvent, Ring.inverse_eq_inv', ← inv_neg, neg_sub, Complex.coe_algebraMap]
  calc
    MeasureTheory.resolventTransform ((A.spectralPVM hA).diag (x : H)) z
      = -⟪(x : H), A.resolvent z x⟫_ℂ := by
        rw [hkernel, hA.inner_resolvent_apply_eq_integral hzA (x : H)]
    _ = -((z - r)⁻¹ * ((‖(x : H)‖ : ℂ) ^ 2)) := by
        rw [resolvent_apply_of_apply_eq_smul hzA x hx, inner_smul_right,
          inner_self_eq_norm_sq_to_K]
        simp
    _ = MeasureTheory.resolventTransform (ENNReal.ofReal (‖(x : H)‖ ^ 2) • Measure.dirac r) z := by
        rw [hkernel, MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal (sq_nonneg _),
          Complex.real_smul, MeasureTheory.integral_dirac _ r, mul_comm, Complex.ofReal_pow]

/-- On an eigenvector of `A` with real eigenvalue `r`, `(A.spectralPVM hA).integral g` acts as
scalar multiplication by `g r`. -/
theorem spectralPVM_integral_apply_of_apply_eq_smul (hA : IsSelfAdjoint A)
    (g : BoundedBorelFunction ℝ) (x : A.domain) {r : ℝ} (hx : A x = (r : ℂ) • (x : H)) :
    (A.spectralPVM hA).integral g (x : H) = g r • (x : H) := by
  have halg : g r • (x : H) =
      ((A.spectralPVM hA).integral (algebraMap ℂ (BoundedBorelFunction ℝ) (g r))) (x : H) := by
    simp [Algebra.algebraMap_eq_smul_one]
  rw [← sub_eq_zero, halg, ← _root_.sub_apply, ← _root_.map_sub,
    ProjValMeasure.integral_apply_eq_zero_iff]
  rw [Filter.EventuallyEq, Filter.eventually_iff, MeasureTheory.mem_ae_iff,
    spectralPVM_diag_eq_smul_dirac hA x hx, _root_.smul_apply, smul_eq_mul,
    MeasureTheory.Measure.dirac_apply, Set.indicator_of_notMem (by simp)]
  simp

/-- Characterization of `(A.spectralPVM hA).integral` in any orthonormal eigenbasis of `A`. -/
theorem spectralPVM_integral_eq_diagonal (hA : IsSelfAdjoint A)
    {ι : Type*} (b : HilbertBasis ι ℂ H) {lam : ι → ℝ}
    (hb : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = (lam i : ℂ) • b i)
    (g : BoundedBorelFunction ℝ) (m : ℓ^∞(ι, ℂ)) (hm : ∀ i, m i = g (lam i)) :
    (A.spectralPVM hA).integral g = b.diagonal m := by
  refine b.ext_inner_apply b fun i j ↦ ?_
  obtain ⟨hj, hAj⟩ := hb j
  rw [spectralPVM_integral_apply_of_apply_eq_smul hA g ⟨_, hj⟩ hAj, b.diagonal_apply_self, hm j]

/-- If a bounded operator `γ` preserves `D(A)` and anticommutes with `A` on `D(A)`, then on an
eigenvector `x` of `A` with real eigenvalue `r`,
`(A.spectralPVM hA).integral g (γ x) = g (-r) • γ x`. -/
theorem spectralPVM_integral_apply_of_anticommute (hA : IsSelfAdjoint A)
    {γ : H →L[ℂ] H} (hγdom : ∀ x ∈ A.domain, γ x ∈ A.domain)
    (hγA : ∀ x : A.domain, γ (A x) = -A ⟨γ x, hγdom x x.property⟩)
    (g : BoundedBorelFunction ℝ) (x : A.domain) {r : ℝ} (hx : A x = (r : ℂ) • (x : H)) :
    (A.spectralPVM hA).integral g (γ x) = g (-r) • γ x := by
  have hγeig := apply_eq_neg_smul_of_anticommute hγdom hγA x hx
  rw [← Complex.ofReal_neg] at hγeig
  exact spectralPVM_integral_apply_of_apply_eq_smul hA g ⟨γ x, hγdom x x.property⟩ hγeig

/-- **Anticommutation with odd functions.** If a bounded operator `γ` preserves the domain of `A`
and anticommutes with `A` on `D(A)`, then `γ` anticommutes with `(A.spectralPVM hA).integral g` for
every bounded Borel odd function `g`. -/
theorem mul_spectralPVM_integral_of_anticommute (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent)
    {γ : H →L[ℂ] H} (hγdom : ∀ x ∈ A.domain, γ x ∈ A.domain)
    (hγA : ∀ x : A.domain, γ (A x) = -A ⟨γ x, hγdom x x.property⟩)
    (g : BoundedBorelFunction ℝ) (hodd : ∀ t, g (-t) = -g t) :
    γ * (A.spectralPVM hA).integral g = -((A.spectralPVM hA).integral g * γ) := by
  obtain ⟨_, b, lam, hb⟩ := hA.exists_hilbertBasis_forall_apply_eq_smul_of_hasCompactResolvent h
  refine b.ext_inner_apply b fun i j ↦ ?_
  obtain ⟨hj, hAj⟩ := hb j
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, _root_.neg_apply]
  rw [spectralPVM_integral_apply_of_apply_eq_smul hA g ⟨_, hj⟩ hAj,
    spectralPVM_integral_apply_of_anticommute hA hγdom hγA g ⟨_, hj⟩ hAj,
    hodd, _root_.map_smul, _root_.neg_smul, neg_neg]

end LinearPMap
