/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.ApproximationProperty.Basic
public import TauCeti.Analysis.Normed.Module.Complexification
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Approximation properties and complexification

A real normed space and its Taylor-norm complexification have the same approximation
properties. In particular, the bound in the bounded approximation property is unchanged,
so the metric approximation property is preserved and reflected. Completeness is not needed.

Real finite-rank approximants extend by complexification, with exactly the same operator
norm. Conversely, compress complex approximants to the real space by the real inclusion
and real-part projection. Both compression maps are contractions. Finite rank in the
reverse direction uses the finite degree of the scalar extension ℂ/ℝ.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 1.

The complexification and its exact operator-norm comparison are those of
`TauCeti.Complexification` and `ContinuousLinearMap.norm_complexify`.
-/

public section

open Set
open TauCeti Complexification
open scoped NNReal

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace TauCeti

private theorem complexify_error_lt (T : X →L[ℝ] X) (z : Complexification X)
    {ε : ℝ} (hre : ‖T z.re - z.re‖ < ε / 2) (him : ‖T z.im - z.im‖ < ε / 2) :
    ‖T.complexify z - z‖ < ε := by
  have h := norm_le_norm_re_add_norm_im (T.complexify z - z)
  simp only [sub_re, sub_im, ContinuousLinearMap.complexify_apply_re,
    ContinuousLinearMap.complexify_apply_im] at h
  linarith

private theorem exists_real_approximation (T : Complexification X →L[ℂ] Complexification X)
    (hT : T.toLinearMap.HasFiniteRange) {K : Set X} {ε : ℝ}
    (herr : ∀ x ∈ K, ‖T (ofReal x) - ofReal x‖ < ε) :
    ∃ S : X →L[ℝ] X, S.toLinearMap.HasFiniteRange ∧ ‖S‖ ≤ ‖T‖ ∧
      ∀ x ∈ K, ‖S x - x‖ < ε := by
  let i := (ofRealLI X).toContinuousLinearMap
  have hfinite : (T.restrictScalars ℝ).toLinearMap.HasFiniteRange := by
    simpa only [LinearMap.HasFiniteRange, ContinuousLinearMap.coe_restrictScalars,
      LinearMap.range_restrictScalars] using (hT.fg_range.restrictScalars (R := ℝ))
  refine ⟨(reCLM X).comp ((T.restrictScalars ℝ).comp i),
    (hfinite.comp_right i.toLinearMap).comp_left (reCLM X).toLinearMap, ?_, fun x hx ↦ ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    intro x
    calc
      ‖(reCLM X).comp ((T.restrictScalars ℝ).comp i) x‖ = ‖(T (i x)).re‖ := by simp
      _ ≤ ‖T (i x)‖ := norm_re_le _
      _ ≤ ‖T‖ * ‖i x‖ := T.le_opNorm _
      _ = ‖T‖ * ‖x‖ := by simp [i]
  · calc
      ‖(reCLM X).comp ((T.restrictScalars ℝ).comp i) x - x‖ =
          ‖(T (ofReal x) - ofReal x).re‖ := by simp [i]
      _ ≤ ‖T (ofReal x) - ofReal x‖ := norm_re_le _
      _ < ε := herr x hx

/-- The approximation property passes from a real space to its complexification. -/
theorem HasApproximationProperty.complexification (h : HasApproximationProperty ℝ X) :
    HasApproximationProperty ℂ (Complexification X) := by
  rw [hasApproximationProperty_iff] at h ⊢
  intro K hK ε hε
  obtain ⟨T, hT, herr⟩ := h (reCLM X '' K ∪ imCLM X '' K)
    ((hK.image (reCLM X).continuous).union (hK.image (imCLM X).continuous))
    (ε / 2) (by positivity)
  exact ⟨T.complexify, T.hasFiniteRange_complexify hT, fun z hz ↦
    complexify_error_lt T z (herr _ (Or.inl ⟨z, hz, reCLM_apply z⟩))
      (herr _ (Or.inr ⟨z, hz, imCLM_apply z⟩))⟩

/-- Complex approximation of the complexification implies real approximation of the
original space. -/
theorem HasApproximationProperty.of_complexification
    (h : HasApproximationProperty ℂ (Complexification X)) : HasApproximationProperty ℝ X := by
  rw [hasApproximationProperty_iff] at h ⊢
  intro K hK ε hε
  obtain ⟨T, hT, herr⟩ := h (ofRealLI X '' K)
    (hK.image (ofRealLI X).continuous) ε hε
  obtain ⟨S, hS, -, herror⟩ := exists_real_approximation T hT
    (fun x hx ↦ by simpa using herr _ (mem_image_of_mem (ofRealLI X) hx))
  exact ⟨S, hS, herror⟩

/-- A real normed space has AP if and only if its Taylor-norm complexification does. -/
@[simp]
theorem hasApproximationProperty_complexification_iff :
    HasApproximationProperty ℂ (Complexification X) ↔ HasApproximationProperty ℝ X :=
  ⟨HasApproximationProperty.of_complexification, HasApproximationProperty.complexification⟩

/-- Complexification preserves a prescribed bound for finite-rank approximation. -/
theorem HasBoundedApproximationPropertyWith.complexification {C : ℝ≥0}
    (h : HasBoundedApproximationPropertyWith ℝ X C) :
    HasBoundedApproximationPropertyWith ℂ (Complexification X) C := by
  rw [hasBoundedApproximationPropertyWith_iff] at h ⊢
  intro K hK ε hε
  obtain ⟨T, hT, hnorm, herr⟩ := h (reCLM X '' K ∪ imCLM X '' K)
    ((hK.image (reCLM X).continuous).union (hK.image (imCLM X).continuous))
    (ε / 2) (by positivity)
  refine ⟨T.complexify, T.hasFiniteRange_complexify hT, ?_, fun z hz ↦
    complexify_error_lt T z (herr _ (Or.inl ⟨z, hz, reCLM_apply z⟩))
      (herr _ (Or.inr ⟨z, hz, imCLM_apply z⟩))⟩
  simpa only [ContinuousLinearMap.norm_complexify] using hnorm

/-- Compression to the real part reflects the approximation bound without loss. -/
theorem HasBoundedApproximationPropertyWith.of_complexification {C : ℝ≥0}
    (h : HasBoundedApproximationPropertyWith ℂ (Complexification X) C) :
    HasBoundedApproximationPropertyWith ℝ X C := by
  rw [hasBoundedApproximationPropertyWith_iff] at h ⊢
  intro K hK ε hε
  obtain ⟨T, hT, hnorm, herr⟩ := h (ofRealLI X '' K)
    (hK.image (ofRealLI X).continuous) ε hε
  obtain ⟨S, hS, hbound, herror⟩ := exists_real_approximation T hT
    (fun x hx ↦ by simpa using herr _ (mem_image_of_mem (ofRealLI X) hx))
  exact ⟨S, hS, hbound.trans hnorm, herror⟩

/-- The Taylor-norm complexification preserves and reflects every approximation bound.
This includes bounds below one and the zero space. -/
@[simp]
theorem hasBoundedApproximationPropertyWith_complexification_iff {C : ℝ≥0} :
    HasBoundedApproximationPropertyWith ℂ (Complexification X) C ↔
      HasBoundedApproximationPropertyWith ℝ X C :=
  ⟨HasBoundedApproximationPropertyWith.of_complexification,
    HasBoundedApproximationPropertyWith.complexification⟩

/-- BAP is invariant under Taylor-norm complexification. -/
@[simp]
theorem hasBoundedApproximationProperty_complexification_iff :
    HasBoundedApproximationProperty ℂ (Complexification X) ↔
      HasBoundedApproximationProperty ℝ X := by
  simp only [hasBoundedApproximationProperty_iff,
    hasBoundedApproximationPropertyWith_complexification_iff]

/-- MAP is invariant under Taylor-norm complexification. -/
@[simp]
theorem hasMetricApproximationProperty_complexification_iff :
    HasMetricApproximationProperty ℂ (Complexification X) ↔
      HasMetricApproximationProperty ℝ X := by
  simp only [hasMetricApproximationProperty_iff,
    hasBoundedApproximationPropertyWith_complexification_iff]

end TauCeti
