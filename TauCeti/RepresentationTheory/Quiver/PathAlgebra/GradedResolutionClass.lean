/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GradedSimple

/-!
# The class of a graded quiver vertex simple

The first-arrow resolution of a vertex simple gives its class in the graded Grothendieck group
as the class of the vertex projective minus the class of the direct sum of shifted projectives
indexed by outgoing arrows. This is the resolution identity behind the graded Cartan inverse
and the q-Euler form for a path algebra. The path-length shift is retained in the kernel term.

The resolution is the graded form of the projective resolution in Assem--Simson--Skowroński,
*Elements of the Representation Theory of Associative Algebras I*, Chapter III, Section 2.
-/

public section

noncomputable section

namespace TauCeti.PathAlgebra

open CategoryTheory

universe u v w

variable (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] [Finite Q]

/-- The first-arrow resolution expresses a graded vertex simple in `G₀^gr(mod kQ)` as its
projective cover minus the shifted direct sum of vertex projectives at the heads of its outgoing
arrows. -/
theorem laurentK0_gradedVertexSimple_eq_projective_sub_arrowSum (i : Q)
    [Finite ((j : Q) × (i ⟶ j))] :
    LaurentK0.of.{max u v w} (gradedFiniteModulesExactStructure (integerGrade k Q))
        ⟨gradedVertexSimple k Q i, gradedFiniteModules_gradedVertexSimple k Q i⟩ =
      gradedCartanMap (integerGrade k Q) (gradedVertexProjectiveClass k Q i) -
        LaurentK0.of.{max u v w} (gradedFiniteModulesExactStructure (integerGrade k Q))
          ⟨gradedArrowSum k Q i, gradedFiniteModules_gradedArrowSum k Q i⟩ := by
  let _ := integerGradedAlgebra k Q
  let S := gradedVertexSimpleResolution k Q i
  have hS : (GradedExactStructure.abelian _
      (GradedModuleCat.shift (integerGrade k Q))).toExactStructure.Conflation S := by
    rw [GradedExactStructure.abelian_toExactStructure, ExactStructure.abelian_conflation]
    exact shortExact_gradedVertexSimpleResolution k Q i
  have h₁ : gradedFiniteModules (integerGrade k Q) S.X₁ := by
    simpa only [S, gradedVertexSimpleResolution_def] using
      gradedFiniteModules_gradedArrowSum k Q i
  have h₃ : gradedFiniteModules (integerGrade k Q) S.X₃ :=
    by simpa only [S, gradedVertexSimpleResolution_def] using
      gradedFiniteModules_gradedVertexSimple k Q i
  have h := ExactK0.of_conflation_fullSubcategory.{max u v w}
    (isExtensionClosed_gradedFiniteModules_gradedAbelian (𝒜 := integerGrade k Q)) hS h₁ h₃
  rw [← GradedExactStructure.fullSubcategory_toExactStructure
    (E := GradedExactStructure.abelian _ (GradedModuleCat.shift (integerGrade k Q)))
    (P := gradedFiniteModules (integerGrade k Q))
    isExtensionClosed_gradedFiniteModules_gradedAbelian
    gradedFiniteModules_gradedAbelian_shift] at h
  apply_fun LaurentK0.ofExactK0.{max u v w}
      ((GradedExactStructure.abelian _ (GradedModuleCat.shift (integerGrade k Q))).fullSubcategory
        _ isExtensionClosed_gradedFiniteModules_gradedAbelian
          gradedFiniteModules_gradedAbelian_shift) at h
  simp only [map_add, LaurentK0.ofExactK0_exactK0_of] at h
  rw [gradedVertexProjectiveClass_eq, gradedCartanMap_of]
  rw [eq_sub_iff_add_eq]
  simp only [S, gradedVertexSimpleResolution_def] at h
  exact (add_comm _ _).trans h.symm

end TauCeti.PathAlgebra
