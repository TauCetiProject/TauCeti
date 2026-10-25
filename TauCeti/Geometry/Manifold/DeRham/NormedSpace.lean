/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Poincare

/-!
# De Rham cohomology of a normed space

A real normed space `E`, viewed as a manifold over its own model `𝓘(ℝ, E)`, is star-convex
about the origin. The Poincaré lemma (`StarConvex.exists_contDiffOn_forall_extDeriv_eq`) therefore
provides a smooth primitive for every closed smooth form of positive degree, so the de Rham
cohomology of `E` vanishes in every positive degree. Together with the degree-zero computation
`TauCeti.finrank_deRhamCohomology_zero`, this computes `H^•_dR(E)` completely.

No finite dimensionality or completeness of `E` is needed: the coefficients are real, and the
primitive is an integral of real-valued alternating maps.

## Main declarations

* `TauCeti.exactForms_succ_eq_closedForms_normedSpace`: every closed smooth form of positive
  degree on `E` is exact.
* `TauCeti.subsingleton_deRhamCohomology_normedSpace`: `H^(k+1)_dR(E) = 0`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17, the Poincaré lemma.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The Poincaré lemma on a normed space.** Every closed smooth real form of positive degree
on `E` is the exterior derivative of a smooth form. -/
theorem exactForms_succ_eq_closedForms_normedSpace (k : ℕ) :
    exactForms 𝓘(ℝ, E) E (k + 1) = closedForms 𝓘(ℝ, E) E (k + 1) := by
  refine le_antisymm (exactForms_le_closedForms _ _) fun φ hφ ↦ ?_
  have hsmooth : ContDiff ℝ ∞ φ.1 := isSmoothForm_modelSpace_iff.mp φ.isSmoothForm
  have hclosed (y : E) (_ : y ∈ Set.univ) : extDeriv φ.1 y = 0 := by
    rw [← mextDeriv_eq_extDeriv, (mem_closedForms _ φ).mp hφ]
    -- The two zeros differ only through the identification `TangentSpace 𝓘(ℝ, E) y = E`.
    rfl
  obtain ⟨α, hα, -, hdα⟩ := (starConvex_univ (0 : E)).exists_contDiffOn_forall_extDeriv_eq
    isOpen_univ le_top hsmooth.contDiffOn hclosed
  have hαs : IsSmoothForm 𝓘(ℝ, E) ∞ (α : RoughForm 𝓘(ℝ, E) E ℝ k) :=
    isSmoothForm_modelSpace_iff.mpr (contDiffOn_univ.mp hα)
  rw [exactForms_succ]
  refine ⟨⟨α, hαs.mem_smoothForms⟩, Subtype.ext (funext fun x ↦ ?_)⟩
  rw [mextDerivₗ_apply, mextDeriv_eq_extDeriv]
  exact hdα x (Set.mem_univ x)

/-- **The de Rham cohomology of a normed space vanishes in positive degrees.** -/
theorem subsingleton_deRhamCohomology_normedSpace (k : ℕ) :
    Subsingleton (deRhamCohomology 𝓘(ℝ, E) E (k + 1)) := by
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  obtain ⟨φ, rfl⟩ := deRhamCohomology.mk_surjective _ _ c
  rw [deRhamCohomology.mk_eq_zero_iff, exactForms_succ_eq_closedForms_normedSpace]
  exact φ.2

end TauCeti
