/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Suspension
public import TauCeti.CategoryTheory.Exact.Stable.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# The homotopy category of curved right modules is triangulated

Let `A` be a right-convention curved DG algebra. The graded-split exact structure on curved right
`A`-modules is Frobenius, and its stable category is identified with the curved homotopy category
by `gradedSplitStableToHomotopy`, compatibly with the shifts by `ℤ` (stable suspension on one
side, the coherent cohomological shift on the other). This file transports Happel's triangulation
of the stable category along this equivalence. The curved homotopy category thereby becomes a
triangulated category whose shift by one is the cohomological shift, although individual curved
modules have no homology.

No centrality of the curvature is assumed. The distinguished triangles are, up to isomorphism, the
images of Happel's standard triangles of graded-split conflations: short sequences of closed maps
of curved modules which split after forgetting the differentials.

## Main definitions

* `TauCeti.CurvedDGRightModuleCat.homotopyPretriangulated`: the pretriangulated structure on the
  curved homotopy category.

## Main results

* `TauCeti.CurvedDGRightModuleCat.homotopyIsTriangulated`: the curved homotopy category is
  triangulated.
* `TauCeti.CurvedDGRightModuleCat.gradedSplitStableToHomotopy_isTriangulated`: the comparison from
  the graded-split stable category is a triangle functor.
* `TauCeti.CurvedDGRightModuleCat.map_stableConflationTriangle_mem_distTriang`: graded-split
  conflations give distinguished triangles.
* `TauCeti.CurvedDGRightModuleCat.homotopy_mem_distTriang_iff`: every distinguished triangle is
  isomorphic to the image of the standard triangle of a graded-split conflation.
* `TauCeti.CurvedDGRightModuleCat.prop_cone`,
  `TauCeti.CurvedDGRightModuleCat.prop_target_of_prop_cone`,
  `TauCeti.CurvedDGRightModuleCat.prop_source_of_prop_cone`: the two-out-of-three property for
  the source, target and cone of a closed map, in isomorphism-closed triangulated subcategories.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 7.6: the
  homotopy category of curved DG modules is triangulated.
* D. Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2, Theorem 2.6: the stable category of a Frobenius category is
  triangulated.
* The Tau Ceti contributors, `TauCeti.Algebra.Homology.Periodic.Triangulated`: the transport
  follows the corresponding statements for periodic homotopy categories.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace TauCeti.CurvedDGRightModuleCat

universe u

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}

/-- The curved homotopy category is pretriangulated: its distinguished triangles are the triangles
isomorphic to images of Happel's distinguished triangles under the equivalence with the
graded-split stable category. -/
noncomputable instance homotopyPretriangulated :
    Pretriangulated (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) :=
  gradedSplitExact_isFrobenius.pretriangulatedOfCommShiftEquivalence
    gradedSplitStableToHomotopy gradedSplitStableToHomotopyCommShift

/-- The comparison from the graded-split stable category of curved right modules to their
homotopy category is a triangle functor. -/
theorem gradedSplitStableToHomotopy_isTriangulated :
    letI := (gradedSplitExact_isFrobenius (h := h)).stableHasShift
    letI := (gradedSplitExact_isFrobenius (h := h)).stableShiftFunctor_additive
    letI := (gradedSplitExact_isFrobenius (h := h)).stablePretriangulated
    letI := gradedSplitStableToHomotopyCommShift (h := h)
    (gradedSplitStableToHomotopy (h := h)).IsTriangulated :=
  gradedSplitExact_isFrobenius.isTriangulated_functor_ofCommShiftEquivalence
    gradedSplitStableToHomotopy gradedSplitStableToHomotopyCommShift

/-- **The homotopy category of curved right modules is triangulated**, with the shift by one given
by the cohomological shift. -/
instance homotopyIsTriangulated :
    IsTriangulated (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) :=
  gradedSplitExact_isFrobenius.isTriangulated_ofCommShiftEquivalence
    gradedSplitStableToHomotopy gradedSplitStableToHomotopyCommShift

/-- **Graded-split conflations give distinguished triangles.** The image of the standard stable
triangle of a graded-split conflation of curved right modules is distinguished in the curved
homotopy category. -/
theorem map_stableConflationTriangle_mem_distTriang
    (S : ShortComplex (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ)
      (CurvedDGRightModuleCat.{u, u, u} h)))
    (hS : (gradedSplitExact (h := h)).Conflation S) :
    letI := (gradedSplitExact_isFrobenius (h := h)).stableHasShift
    letI := gradedSplitStableToHomotopyCommShift (h := h)
    gradedSplitStableToHomotopy.mapTriangle.obj
        (gradedSplitExact_isFrobenius.stableConflationTriangle S hS) ∈
      distTriang (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) :=
  gradedSplitExact_isFrobenius.map_stableConflationTriangle_mem_distTriang
    gradedSplitStableToHomotopy gradedSplitStableToHomotopyCommShift S hS

/-- A triangle in the curved homotopy category is distinguished exactly when it is isomorphic to
the image of the standard stable triangle of a graded-split conflation. -/
theorem homotopy_mem_distTriang_iff
    (T : Triangle (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h))) :
    letI := (gradedSplitExact_isFrobenius (h := h)).stableHasShift
    letI := gradedSplitStableToHomotopyCommShift (h := h)
    T ∈ distTriang (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) ↔
      ∃ (S : ShortComplex (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ)
          (CurvedDGRightModuleCat.{u, u, u} h)))
        (hS : (gradedSplitExact (h := h)).Conflation S),
        Nonempty (T ≅ gradedSplitStableToHomotopy.mapTriangle.obj
          (gradedSplitExact_isFrobenius.stableConflationTriangle S hS)) :=
  gradedSplitExact_isFrobenius.mem_distTriang_ofCommShiftEquivalence_iff
    gradedSplitStableToHomotopy gradedSplitStableToHomotopyCommShift T

/-! ### Two out of three for cones -/

section Cone

variable {M N : CurvedDGRightModuleCat.{u, u, u} h}
  (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N)

/-- The graded-split cone sequence `N ⟶ cone(f) ⟶ M[1]` gives a distinguished triangle of the
curved homotopy category with these three objects. -/
private theorem exists_mem_distTriang_cone :
    ∃ T ∈ distTriang (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)),
      T.obj₁ = DGHomotopyCategory.of R N ∧ T.obj₂ = DGHomotopyCategory.of R (cone f) ∧
        T.obj₃ = (DGHomotopyCategory.of R M)⟦(1 : ℤ)⟧ :=
  ⟨_, map_stableConflationTriangle_mem_distTriang _ (coneShortComplex_conflation f),
    by simp, by simp, by simp⟩

variable (Q : ObjectProperty (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)))
  [Q.IsTriangulated] [Q.IsClosedUnderIsomorphisms]

/-- An isomorphism-closed triangulated subcategory containing the source and target of a closed
map contains its cone. -/
theorem prop_cone (hM : Q (DGHomotopyCategory.of R M)) (hN : Q (DGHomotopyCategory.of R N)) :
    Q (DGHomotopyCategory.of R (cone f)) := by
  obtain ⟨T, hT, h₁, h₂, h₃⟩ := exists_mem_distTriang_cone f
  rw [← h₂]
  refine Q.ext_of_isTriangulatedClosed₂ T hT (h₁ ▸ hN) ?_
  rw [h₃]
  exact Q.le_shift 1 _ hM

/-- An isomorphism-closed triangulated subcategory containing the source and the cone of a
closed map contains its target. -/
theorem prop_target_of_prop_cone (hM : Q (DGHomotopyCategory.of R M))
    (hC : Q (DGHomotopyCategory.of R (cone f))) : Q (DGHomotopyCategory.of R N) := by
  obtain ⟨T, hT, h₁, h₂, h₃⟩ := exists_mem_distTriang_cone f
  rw [← h₁]
  refine Q.ext_of_isTriangulatedClosed₁ T hT (h₂ ▸ hC) ?_
  rw [h₃]
  exact Q.le_shift 1 _ hM

/-- An isomorphism-closed triangulated subcategory containing the target and the cone of a
closed map contains its source. -/
theorem prop_source_of_prop_cone (hN : Q (DGHomotopyCategory.of R N))
    (hC : Q (DGHomotopyCategory.of R (cone f))) : Q (DGHomotopyCategory.of R M) := by
  obtain ⟨T, hT, h₁, h₂, h₃⟩ := exists_mem_distTriang_cone f
  have h := Q.ext_of_isTriangulatedClosed₃ T hT (h₁ ▸ hN) (h₂ ▸ hC)
  rw [h₃] at h
  exact (Q.prop_shift_iff_of_isStableUnderShift _ (1 : ℤ)).1 h

end Cone

end TauCeti.CurvedDGRightModuleCat
