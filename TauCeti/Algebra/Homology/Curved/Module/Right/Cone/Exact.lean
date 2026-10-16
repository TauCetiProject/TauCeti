/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Cone.Basic
public import TauCeti.Algebra.Homology.Curved.Module.Right.Exact

/-!
# The graded-split cone sequence

The canonical inclusion and projection of a cone form a conflation of the graded-split exact
structure. Its graded splitting is given by the second projection and first inclusion. These
maps need not commute with the differentials.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 7.6.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.CurvedDGRightModuleCat

universe u

attribute [local implicit_reducible] ForgetEnrichment

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w} {M N : CurvedDGRightModuleCat.{u, u, u} h}
  (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N)

/-- The short complex `N → Cone(f) → M[1]` of closed cone maps. -/
@[expose]
noncomputable def coneShortComplex : ShortComplex
    (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) :=
  ShortComplex.mk (coneInclusion f) (coneProjection f) (coneInclusion_comp_coneProjection f)

attribute [local implicit_reducible] coneShortComplex

/-- The cone sequence splits after forgetting the differential. -/
noncomputable def coneGradedSplitting :
    ((coneShortComplex f).map (forgetDifferential (h := h))).Splitting where
  r := GradedModuleCat.ofHom (LinearMap.snd Aᵐᵒᵖ M N)
    (LinearMap.isHomogeneous_def.mpr fun p x hx ↦ by
      change x ∈ (toGradedModuleCat (cone f)).grading.piece p at hx
      change x.2 ∈ (toGradedModuleCat N).grading.piece (p + 0)
      simp only [toGradedModuleCat_piece, cone_grading, add_zero] at hx ⊢
      exact hx.2)
  s := GradedModuleCat.ofHom (LinearMap.inl Aᵐᵒᵖ M N)
    (LinearMap.isHomogeneous_def.mpr fun p x hx ↦ by
      change x ∈ (toGradedModuleCat (M.shift 1)).grading.piece p at hx
      change (x, (0 : N)) ∈ (toGradedModuleCat (cone f)).grading.piece (p + 0)
      simp only [toGradedModuleCat_piece, cone_grading, shift_grading, add_zero] at hx ⊢
      exact ⟨hx, (N.grading p).zero_mem⟩)
  f_r := by
    apply GradedModuleCat.hom_ext
    ext x
    change (closedHom (coneInclusion f) x).2 = x
    rw [closedHom_coneInclusion]
    rfl
  s_g := by
    apply GradedModuleCat.hom_ext
    ext x
    change closedHom (coneProjection f) (x, 0) = x
    rw [closedHom_coneProjection]
    rfl
  id := by
    apply GradedModuleCat.hom_ext
    let i : N →ₗ[Aᵐᵒᵖ] M × N := closedHom (coneInclusion f)
    let p : M × N →ₗ[Aᵐᵒᵖ] M := closedHom (coneProjection f)
    change i.comp (LinearMap.snd Aᵐᵒᵖ M N) + (LinearMap.inl Aᵐᵒᵖ M N).comp p = LinearMap.id
    dsimp only [i, p]
    rw [closedHom_coneInclusion, closedHom_coneProjection]
    apply LinearMap.ext
    intro x
    change ((0 : M), x.2) + (x.1, (0 : N)) = x
    exact Prod.ext (zero_add _) (add_zero _)

/-- The cone sequence is a graded-split conflation. -/
theorem coneShortComplex_conflation :
    (gradedSplitExact (h := h)).Conflation (coneShortComplex f) := by
  rw [gradedSplitExact_conflation_iff, ExactStructure.split_conflation]
  exact ⟨coneGradedSplitting f⟩

/-- The closed cone inclusion is an inflation of the graded-split exact structure. -/
theorem gradedSplitExact_isInflation_coneInclusion :
    (gradedSplitExact (h := h)).IsInflation (coneInclusion f) :=
  (gradedSplitExact (h := h)).isInflation_f (coneShortComplex_conflation f)

/-- The closed cone projection is a deflation of the graded-split exact structure. -/
theorem gradedSplitExact_isDeflation_coneProjection :
    (gradedSplitExact (h := h)).IsDeflation (coneProjection f) :=
  (gradedSplitExact (h := h)).isDeflation_g (coneShortComplex_conflation f)

end TauCeti.CurvedDGRightModuleCat
