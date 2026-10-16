/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Ideal
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Grading
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Multiplication

/-!
# Graded vertex projectives of the componentwise zigzag algebra

For the public algebra `Z = zigzagAlgebra k G`, the ideal `Z e_i` is a finite graded
projective in the signed componentwise grading. Its Laurent Grothendieck class represents
an internal shift by multiplication by `qᵈ`.

These objects use the actual componentwise algebra. At an isolated vertex they retain
the degree-two infinitesimal of the dual-number factor. The relation-quotient objects
`zigzagGradedProjective` belong to a different algebra.

The construction uses `GradedModuleCat.ofIdeal` and the existing graded projective
Grothendieck group and its shift computation.
-/

public section
noncomputable section

namespace TauCeti

universe u w
variable (k : Type w) [CommRing k] {V : Type u} [Finite V] (G : SimpleGraph V)

local notation "e" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inl i)

/-- The principal vertex ideal is homogeneous for the canonical signed grading. -/
theorem isHomogeneous_span_zigzagAlgebraBasis_inl (i : V) :
    let _ := zigzagAlgebraIntegerGradedAlgebra k G
    (Ideal.span {e i} : Ideal (zigzagAlgebra k G)).IsHomogeneous
      (zigzagAlgebraIntegerGrade k G) := by
  let _ := zigzagAlgebraIntegerGradedAlgebra k G
  have he : e i ∈ zigzagAlgebraIntegerGrade k G 0 := by
    have hg : zigzagAlgebraIntegerGrade k G 0 = zigzagAlgebraGrade k G 0 := by
      simpa only [Int.natCast_zero] using zigzagAlgebraIntegerGrade_ofNat k G 0
    rw [hg]
    exact zigzagAlgebraBasis_inl_mem_grade_zero k G i
  exact Ideal.homogeneous_span _ _ fun _ hx ↦ ⟨0, (Set.mem_singleton_iff.1 hx) ▸ he⟩

/-- The graded principal left ideal `Z e_i` of the public componentwise algebra. -/
abbrev zigzagAlgebraGradedProjective (i : V) :
    GradedModuleCat.{max u w} (zigzagAlgebraIntegerGrade k G) :=
  let _ := zigzagAlgebraIntegerGradedAlgebra k G
  GradedModuleCat.ofIdeal _ (Ideal.span {e i}) (isHomogeneous_span_zigzagAlgebraBasis_inl k G i)

/-- The projective's grading is the restriction of the signed algebra grading. -/
theorem mem_zigzagAlgebraGradedProjective_piece_iff (i : V) (d : ℤ)
    {x : zigzagAlgebraGradedProjective k G i} :
    x ∈ (zigzagAlgebraGradedProjective k G i).grading.piece d ↔
      (x : zigzagAlgebra k G) ∈ zigzagAlgebraIntegerGrade k G d :=
  let _ := zigzagAlgebraIntegerGradedAlgebra k G
  GradedModuleCat.mem_ofIdeal_piece_iff (isHomogeneous_span_zigzagAlgebraBasis_inl k G i)

/-- The vertex ideal is a finite projective over the public algebra. -/
theorem gradedFiniteProjectiveModules_zigzagAlgebraGradedProjective (i : V) :
    gradedFiniteProjectiveModules (zigzagAlgebraIntegerGrade k G)
      (zigzagAlgebraGradedProjective k G i) :=
  let _ := zigzagAlgebraIntegerGradedAlgebra k G
  gradedFiniteProjectiveModules_ofIdeal_span_singleton
    (isIdempotentElem_zigzagAlgebraBasis_inl k G i)
    (isHomogeneous_span_zigzagAlgebraBasis_inl k G i)

/-- The class of the vertex projective in the actual Laurent projective Grothendieck group. -/
def zigzagAlgebraGradedProjectiveClass (i : V) :
    LaurentK0.{max u w}
      (gradedFiniteProjectiveModulesExactStructure (zigzagAlgebraIntegerGrade k G)) :=
  LaurentK0.of.{max u w} _ ⟨zigzagAlgebraGradedProjective k G i,
    gradedFiniteProjectiveModules_zigzagAlgebraGradedProjective k G i⟩

/-- The named vertex-projective class is the class of its finite graded projective object. -/
theorem zigzagAlgebraGradedProjectiveClass_def (i : V) :
    zigzagAlgebraGradedProjectiveClass k G i =
      LaurentK0.of.{max u w}
        (gradedFiniteProjectiveModulesExactStructure (zigzagAlgebraIntegerGrade k G))
        ⟨zigzagAlgebraGradedProjective k G i,
          gradedFiniteProjectiveModules_zigzagAlgebraGradedProjective k G i⟩ :=
  zigzagAlgebraGradedProjectiveClass.eq_def k G i

end TauCeti
