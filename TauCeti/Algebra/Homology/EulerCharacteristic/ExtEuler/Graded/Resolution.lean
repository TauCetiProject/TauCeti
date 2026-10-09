/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Additivity
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Resolution

/-!
# Graded Ext-Euler admissibility from finite resolutions

In a linear abelian category with an internal-shift autoequivalence, a finite resolution by
projectives with finitely Laurent-supported graded Hom spaces makes the resolved pair graded
Euler-admissible. Internal finiteness propagates through the long exact Ext sequence, while
projectivity gives a cohomological bound uniform in every internal degree. These are separate
conclusions: internal finiteness alone does not imply eventual Ext-vanishing.

The q-Euler characteristic is the alternating sum of the target-shift graded Hom dimensions of
the resolving terms. This computes the Laurent polynomial without choosing cohomological or
internal support bounds and shows that the result is independent of the resolution.

## Main results

* `TauCeti.ExactStructure.FiniteResolution.isGradedExtInternallyFinite`: internal finiteness
  propagates along any finite resolution, without requiring projectivity.
* `TauCeti.ExactStructure.FiniteResolution.isGradedExtBoundedBy`: a projective resolution of
  length `l` gives vanishing from cohomological degree `l + 1`, in every internal degree.
* `TauCeti.ExactStructure.FiniteResolution.isGradedEulerAdmissible`: the resulting admissibility
  criterion using graded Hom-finiteness of the projectives.
* `TauCeti.ExactStructure.FiniteResolution.gradedExtEuler_eq_foldAlternating`: computation by
  the alternating graded Hom dimensions.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 2.4--2.7, for
  dimension shifting and the long exact Ext sequence.
* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", Section 2.2,
  for the q-Euler form and the target-shift grading convention.

The cohomological bound reuses
`TauCeti.ExactStructure.FiniteResolution.isExtBoundedBy`.
-/

public section

namespace TauCeti

open CategoryTheory

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type t} [Field k] [Linear k C]
  [HasExt.{w} C] {e : C ≌ C}

namespace ExactStructure.FiniteResolution

variable {P : ObjectProperty C} {X Y : C}

/-- Finite internal support of Ext propagates along a finite resolution. No projectivity of
its terms is required. -/
theorem isGradedExtInternallyFinite (r : (ExactStructure.abelian C).FiniteResolution P X)
    (hfinite : ∀ Z, P Z → IsGradedExtInternallyFinite.{w} k e Z Y) :
    IsGradedExtInternallyFinite.{w} k e X Y := by
  induction r with
  | base hX => exact hfinite _ hX
  | step hQ i p zero hp r ih =>
      exact ih.of_shortExact₃' ((ExactStructure.abelian_conflation _).mp hp) (hfinite _ hQ)

/-- A finite projective resolution of length `l` makes Ext vanish from degree `l + 1` in
all internal degrees. The same bound works against every shift of the target. -/
theorem isGradedExtBoundedBy (r : (ExactStructure.abelian C).FiniteResolution P X)
    (hproj : P ≤ (ExactStructure.abelian C).isProjective) :
    IsGradedExtBoundedBy.{w} e X Y (r.length + 1) :=
  ⟨fun _ hn j ↦ (r.isExtBoundedBy (Y := (e ^ j).functor.obj Y) hproj).subsingleton hn⟩

/-- A finite resolution by projectives whose graded Hom spaces into `Y` have finite Laurent
support makes `(X,Y)` graded Euler-admissible. -/
theorem isGradedEulerAdmissible (r : (ExactStructure.abelian C).FiniteResolution P X)
    (hproj : P ≤ (ExactStructure.abelian C).isProjective)
    (hHom : ∀ Z, P Z → HasFiniteLaurentSupport k fun j ↦ Z ⟶ (e ^ j).functor.obj Y) :
    IsGradedEulerAdmissible.{w} k e X Y :=
  ⟨r.isGradedExtInternallyFinite fun Z hZ ↦ by
      have : Projective Z := (ExactStructure.abelian_isProjective_iff Z).mp (hproj Z hZ)
      exact (isGradedEulerAdmissible_of_projective k e Z Y (hHom Z hZ)).internallyFinite,
    (r.isGradedExtBoundedBy (Y := Y) hproj).isGradedExtBounded⟩

/-- The q-Euler characteristic computed from a finite projective resolution is the alternating
sum of the graded Hom dimensions of its terms, with exponent `-j` for target shift `j`. -/
theorem gradedExtEuler_eq_foldAlternating
    (r : (ExactStructure.abelian C).FiniteResolution P X)
    (hproj : P ≤ (ExactStructure.abelian C).isProjective)
    (hHom : ∀ Z, P Z → HasFiniteLaurentSupport k fun j ↦ Z ⟶ (e ^ j).functor.obj Y) :
    gradedExtEuler k e (r.isGradedEulerAdmissible hproj hHom) =
      r.foldAlternating fun Z hZ ↦
        targetShiftGradedDimension k (fun j ↦ Z ⟶ (e ^ j).functor.obj Y) (hHom Z hZ) := by
  induction r with
  | @base X hX =>
      have : Projective X := (ExactStructure.abelian_isProjective_iff X).mp (hproj X hX)
      rw [foldAlternating_base, gradedExtEuler_projective]
  | @step K Q X hQ i p zero hp r ih =>
      have : Projective Q := (ExactStructure.abelian_isProjective_iff Q).mp (hproj Q hQ)
      have hQ' := isGradedEulerAdmissible_of_projective k e Q Y (hHom Q hQ)
      have hadd := gradedExtEuler_shortExact₁ ((ExactStructure.abelian_conflation _).mp hp) Y
        (r.isGradedEulerAdmissible hproj hHom)
        ((step hQ i p zero hp r).isGradedEulerAdmissible hproj hHom)
      have heval : gradedExtEuler k e hQ' =
          targetShiftGradedDimension k (fun j ↦ Q ⟶ (e ^ j).functor.obj Y) (hHom Q hQ) := by
        rw [gradedExtEuler_projective]
      rw [foldAlternating_step, ← ih, ← heval]
      exact eq_sub_of_add_eq' hadd.symm

end ExactStructure.FiniteResolution

end TauCeti
