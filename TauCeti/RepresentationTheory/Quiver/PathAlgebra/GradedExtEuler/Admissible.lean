/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GradedSimple
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Quotient
public import TauCeti.Algebra.Category.GradedModuleCat.HomLaurentSupport

/-!
# Graded Euler admissibility of quiver vertex simples

For a finite quiver with finitely many arrows, the first-arrow
resolution of a vertex simple has finitely generated projective terms. Against a finite
graded module, their shifted Hom spaces have finite Laurent support. The resolution
therefore makes the vertex simple Euler-admissible.

This is the finiteness step needed before computing the graded Ringel form from the
first-arrow resolution. The resolution follows Assem--Simson--Skowroński,
*Elements of the Representation Theory of Associative Algebras I*, Chapter III,
Sections 2--3; the q-Euler convention follows Dancso--Licata, *Koszul algebras and
flow lattices*, Section 2.2.
-/

public section

namespace TauCeti.PathAlgebra

open CategoryTheory

universe u v w t

variable (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] [Finite Q]
  [∀ a b : Q, Finite (a ⟶ b)]
  [HasExt.{t} (GradedModuleCat.{max u v w} (integerGrade k Q))]

/-- The shifted projective sum in the first-arrow resolution is Euler-admissible against
every finite-dimensional graded target. -/
theorem isGradedEulerAdmissible_gradedArrowSum (i : Q)
    (Y : GradedModuleCat.{max u v w} (integerGrade k Q)) [Module.Finite k Y] :
    IsGradedEulerAdmissible.{t} k (GradedModuleCat.shift (integerGrade k Q))
      (gradedArrowSum k Q i) Y := by
  let _ := integerGradedAlgebra k Q
  let hF (a : (j : Q) × (i ⟶ j)) :
      Module.Finite (pathAlgebra k Q) ((gradedVertexProjective k Q a.1).shiftObj 1) :=
    (gradedFiniteProjectiveModules_iff.1
      (gradedFiniteProjectiveModules_shiftObj
        (gradedFiniteProjectiveModules_gradedVertexProjective k Q a.1) 1)).1
  let _ : Module.Finite (pathAlgebra k Q) (gradedArrowSum k Q i) := inferInstance
  exact isGradedEulerAdmissible_of_projective k _ _ Y
    ((GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj _ Y).of_equiv
      fun j ↦ (GradedModuleCat.homShiftPowEquiv (integerGrade k Q) _ Y j).symm)

omit [∀ a b : Q, Finite (a ⟶ b)] in
/-- A graded vertex projective is Euler-admissible against every finite-dimensional
graded target, even when the path algebra itself is infinite-dimensional. -/
theorem isGradedEulerAdmissible_gradedVertexProjective (i : Q)
    (Y : GradedModuleCat.{max u v w} (integerGrade k Q)) [Module.Finite k Y] :
    IsGradedEulerAdmissible.{t} k (GradedModuleCat.shift (integerGrade k Q))
      (gradedVertexProjective k Q i) Y := by
  let _ := integerGradedAlgebra k Q
  let _ : Module.Finite (pathAlgebra k Q) (gradedVertexProjective k Q i) :=
    (gradedFiniteProjectiveModules_iff.1
      (gradedFiniteProjectiveModules_gradedVertexProjective k Q i)).1
  exact isGradedEulerAdmissible_of_projective k _ _ Y
    ((GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj _ Y).of_equiv
      fun j ↦ (GradedModuleCat.homShiftPowEquiv (integerGrade k Q) _ Y j).symm)

/-- A graded vertex simple of a finite quiver is Euler-admissible
against every finite-dimensional graded target. The first-arrow resolution bounds its
cohomological Ext support, while finite generation of the projectives bounds the
internal support. -/
theorem isGradedEulerAdmissible_gradedVertexSimple (i : Q)
    (Y : GradedModuleCat.{max u v w} (integerGrade k Q)) [Module.Finite k Y] :
    IsGradedEulerAdmissible.{t} k (GradedModuleCat.shift (integerGrade k Q))
      (gradedVertexSimple k Q i) Y := by
  have hA : IsGradedEulerAdmissible.{t} k (GradedModuleCat.shift (integerGrade k Q))
      (gradedVertexSimpleResolution k Q i).X₁ Y := by
    simpa only [gradedVertexSimpleResolution_def] using
      isGradedEulerAdmissible_gradedArrowSum k Q i Y
  have hP : IsGradedEulerAdmissible.{t} k (GradedModuleCat.shift (integerGrade k Q))
      (gradedVertexSimpleResolution k Q i).X₂ Y := by
    simpa only [gradedVertexSimpleResolution_def] using
      isGradedEulerAdmissible_gradedVertexProjective k Q i Y
  simpa only [gradedVertexSimpleResolution_def] using
    hA.of_shortExact₃' (shortExact_gradedVertexSimpleResolution k Q i) hP

end TauCeti.PathAlgebra
