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
noncomputable def coneShortComplex : ShortComplex
    (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) :=
  ShortComplex.mk (coneInclusion f) (coneProjection f) (coneInclusion_comp_coneProjection f)

attribute [local implicit_reducible] coneShortComplex

/-- The cone sequence has the canonical inclusion and projection as its two arrows. -/
theorem coneShortComplex_eq_mk :
    coneShortComplex f = ShortComplex.mk (coneInclusion f) (coneProjection f)
      (coneInclusion_comp_coneProjection f) := by
  rfl

/-- The first object of the cone sequence is its target module. -/
@[simp]
theorem coneShortComplex_X₁ : (coneShortComplex f).X₁ =
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N :=
  (rfl)

/-- The middle object of the cone sequence is the cone. -/
@[simp]
theorem coneShortComplex_X₂ : (coneShortComplex f).X₂ =
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (cone f) :=
  (rfl)

/-- The last object of the cone sequence is the shifted source. -/
@[simp]
theorem coneShortComplex_X₃ : (coneShortComplex f).X₃ =
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M.shift 1) :=
  (rfl)

/-- After identifying its endpoints, the first map is the cone inclusion. -/
@[simp]
theorem coneShortComplex_f :
    eqToHom (coneShortComplex_X₁ f).symm ≫ (coneShortComplex f).f ≫
      eqToHom (coneShortComplex_X₂ f) = coneInclusion f := by
  simp [coneShortComplex]

/-- After identifying its endpoints, the second map is the cone projection. -/
@[simp]
theorem coneShortComplex_g :
    eqToHom (coneShortComplex_X₂ f).symm ≫ (coneShortComplex f).g ≫
      eqToHom (coneShortComplex_X₃ f) = coneProjection f := by
  simp [coneShortComplex]

/-- The cone sequence splits after forgetting the differential. -/
noncomputable def coneGradedSplitting :
    ((coneShortComplex f).map (forgetDifferential (h := h))).Splitting where
  r := GradedModuleCat.ofHom (LinearMap.snd Aᵐᵒᵖ M N)
    (LinearMap.isHomogeneous_def.mpr fun p x hx ↦ by
      -- The mapped short complex stores its cone through the closed-object wrapper.
      -- Identify that object before applying the public grading equation.
      change x ∈ (toGradedModuleCat (cone f)).grading.piece p at hx
      -- Degree-zero homogeneity presents the target degree as `p + 0`.
      change x.2 ∈ (toGradedModuleCat N).grading.piece (p + 0)
      simp only [toGradedModuleCat_piece, cone_grading, add_zero] at hx ⊢
      exact hx.2)
  s := GradedModuleCat.ofHom (LinearMap.inl Aᵐᵒᵖ M N)
    (LinearMap.isHomogeneous_def.mpr fun p x hx ↦ by
      -- The source is the mapped sequence's last closed object, namely the shifted module.
      change x ∈ (toGradedModuleCat (M.shift 1)).grading.piece p at hx
      -- Evaluate the inherited product inclusion and retain the degree-zero target index.
      change (x, (0 : N)) ∈ (toGradedModuleCat (cone f)).grading.piece (p + 0)
      simp only [toGradedModuleCat_piece, cone_grading, shift_grading, add_zero] at hx ⊢
      exact ⟨hx, (N.grading p).zero_mem⟩)
  f_r := by
    apply GradedModuleCat.hom_ext
    ext x
    -- The sequence map and splitting component are wrapped graded morphisms; identify
    -- their underlying composite before using the public closed cone-inclusion equation.
    change (closedHom (coneInclusion f) x).2 = x
    rw [closedHom_coneInclusion]
    -- The public map equation has reduced the inclusion; its second component is definitionally x.
    rfl
  s_g := by
    apply GradedModuleCat.hom_ext
    ext x
    -- Evaluate the first inclusion in the underlying composite of graded morphisms.
    change closedHom (coneProjection f) (x, 0) = x
    rw [closedHom_coneProjection]
    -- The public map equation has reduced the projection on the inherited product carrier.
    rfl
  id := by
    apply GradedModuleCat.hom_ext
    let i : N →ₗ[Aᵐᵒᵖ] M × N := closedHom (coneInclusion f)
    let p : M × N →ₗ[Aᵐᵒᵖ] M := closedHom (coneProjection f)
    -- The splitting identity is stored in the mapped short complex's middle object.
    -- Its original product carrier expresses both compositions as linear-map compositions.
    change i.comp (LinearMap.snd Aᵐᵒᵖ M N) + (LinearMap.inl Aᵐᵒᵖ M N).comp p = LinearMap.id
    dsimp only [i, p]
    rw [closedHom_coneInclusion, closedHom_coneProjection]
    apply LinearMap.ext
    intro x
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.inr_apply,
      LinearMap.snd_apply, LinearMap.inl_apply, LinearMap.fst_apply, LinearMap.id_apply] using
      (show ((0 : M), x.2) + (x.1, (0 : N)) = x from
        Prod.ext (zero_add _) (add_zero _))

/-- The graded retraction is the second product projection on the identified objects. -/
-- Compute before `hom_comp` expands the composite and its dependent object types.
@[simp↓]
theorem coneGradedSplitting_r :
    (eqToHom (congrArg (forgetDifferential (h := h)).obj (coneShortComplex_X₂ f)).symm ≫
        (coneGradedSplitting f).r ≫
          eqToHom (congrArg (forgetDifferential (h := h)).obj (coneShortComplex_X₁ f))).hom =
      LinearMap.snd Aᵐᵒᵖ M N := by
  simp [coneGradedSplitting, coneShortComplex]

/-- The graded section is the first product inclusion on the identified objects. -/
-- As for the retraction, preserve the splitting's projection shape until this computation fires.
@[simp↓]
theorem coneGradedSplitting_s :
    (eqToHom (congrArg (forgetDifferential (h := h)).obj (coneShortComplex_X₃ f)).symm ≫
        (coneGradedSplitting f).s ≫
          eqToHom (congrArg (forgetDifferential (h := h)).obj (coneShortComplex_X₂ f))).hom =
      LinearMap.inl Aᵐᵒᵖ M N := by
  simp [coneGradedSplitting, coneShortComplex]

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
