/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Gluing
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# Gluing symplectic forms along a partial diffeomorphism

Let `Z` be the gluing of two manifolds `X` and `Y` along a partial diffeomorphism `Φ : Y ⇀ X`,
with a manifold structure for which the canonical maps `ι_X : X → Z` and `ι_Y : Y → Z` are local
diffeomorphisms. Two smooth two-forms `α` on `X` and `β` on `Y` with `Φ^* α = β` on the source of
`Φ` glue to a smooth two-form on `Z` (`PartialDiffeomorph.glueForm`). Nondegeneracy is a pointwise
condition, the canonical maps are local diffeomorphisms and together they cover `Z`, so the glued
form is nondegenerate exactly when `α` and `β` are
(`PartialDiffeomorph.isNondegenerate_glueForm_iff`). Since closedness also glues
(`PartialDiffeomorph.isClosed_glueForm_iff`), the glued form is symplectic exactly when `α` and
`β` are (`PartialDiffeomorph.isSymplectic_glueForm_iff`).

For the completion of a Liouville domain `W`, glued from the interior of `W` and the cylinder over
its boundary along the Liouville flow, this makes the exterior derivative of the glued primitive a
symplectic form: by `PartialDiffeomorph.mextDerivₗ_glueForm` it is the gluing of the symplectic
form of `W` and of the symplectic form `d(eᵗ λ|_{∂W})` of the symplectization of the contact
boundary (`TauCeti.SmoothForm.isSymplectic_mextDerivₗ_symplectization_iff`).

## Main results

* `PartialDiffeomorph.isNondegenerate_glueForm_iff`: the glued two-form is nondegenerate exactly
  when both forms are.
* `PartialDiffeomorph.isSymplectic_glueForm_iff`: the glued two-form is symplectic exactly when
  both forms are.

## References

* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  §2(a) (the completion of a Liouville domain).
-/

public section

noncomputable section

open TauCeti OpenPartialHomeomorph
open scoped Manifold ContDiff

namespace PartialDiffeomorph

universe u

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace H X]
  [ChartedSpace H Y] [IsManifold I ∞ X] [IsManifold I ∞ Y] {Φ : PartialDiffeomorph I I Y X ∞}
  [ChartedSpace H Φ.toOpenPartialHomeomorph.glueData.toGlueData.glued]
  [IsManifold I ∞ Φ.toOpenPartialHomeomorph.glueData.toGlueData.glued]
  {hl : IsLocalDiffeomorph I I ∞ Φ.toOpenPartialHomeomorph.glueInl}
  {hr : IsLocalDiffeomorph I I ∞ Φ.toOpenPartialHomeomorph.glueInr}
  {α : SmoothTwoForm I X} {β : SmoothTwoForm I Y}
  {hαβ : ∀ y ∈ Φ.source, mpullback I I Φ α.val y = β.val y}

/-- **The glued two-form is nondegenerate exactly when both forms are.** -/
@[simp]
theorem isNondegenerate_glueForm_iff :
    SmoothTwoForm.IsNondegenerate (Φ.glueForm hl hr α β hαβ) ↔
      α.IsNondegenerate ∧ β.IsNondegenerate := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hα, hβ⟩ ↦ ?_⟩
  · rw [← mpullback_glueInl_glueForm (hr := hr) (hαβ := hαβ)]
    exact h.isNondegenerate_mpullback_of_isLocalDiffeomorph hl
  · rw [← mpullback_glueInr_glueForm (hl := hl) (hαβ := hαβ)]
    exact h.isNondegenerate_mpullback_of_isLocalDiffeomorph hr
  rw [SmoothTwoForm.isNondegenerate_iff_separatingLeft]
  intro p v hv
  rcases exists_glueInl_eq_or_exists_glueInr_eq _ p with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact hl.eq_zero_of_isNondegenerate_mpullback (by rwa [mpullback_glueInl_glueForm]) x v hv
  · exact hr.eq_zero_of_isNondegenerate_mpullback (by rwa [mpullback_glueInr_glueForm]) y v hv

/-- **The glued two-form is symplectic exactly when both forms are.** -/
@[simp]
theorem isSymplectic_glueForm_iff :
    SmoothTwoForm.IsSymplectic (Φ.glueForm hl hr α β hαβ) ↔
      α.IsSymplectic ∧ β.IsSymplectic := by
  refine ⟨fun h ↦ ?_, fun ⟨hα, hβ⟩ ↦ ⟨isClosed_glueForm_iff.2 ⟨hα.isClosed, hβ.isClosed⟩,
    isNondegenerate_glueForm_iff.2 ⟨hα.isNondegenerate, hβ.isNondegenerate⟩⟩⟩
  obtain ⟨hcα, hcβ⟩ := isClosed_glueForm_iff.1 h.isClosed
  obtain ⟨hnα, hnβ⟩ := isNondegenerate_glueForm_iff.1 h.isNondegenerate
  exact ⟨⟨hcα, hnα⟩, ⟨hcβ, hnβ⟩⟩

end PartialDiffeomorph
