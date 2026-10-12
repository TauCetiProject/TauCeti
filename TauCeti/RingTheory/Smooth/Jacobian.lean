/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Smooth.StandardSmooth

/-!
# Smoothness after inverting a Jacobian minor

A finite presentation equipped with a choice of as many variables as relations becomes
standard smooth after inverting the corresponding Jacobian determinant. Its relative
dimension is the number of variables minus the number of relations. This provides smooth
coordinate charts for hypersurfaces.

For a hypersurface, one can apply the criterion wherever a chosen partial derivative is
invertible; with several relations, use the determinant of a square Jacobian minor.

## References

* Stacks Project, Tag 00T7.
-/

public section

namespace Algebra.PreSubmersivePresentation

variable {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Finite ι] [Finite σ]

/-- Inverting the selected Jacobian minor of a finite presentation gives a standard smooth
algebra of the dimension of that presentation. -/
theorem isStandardSmoothOfRelativeDimension_localizationAway
    (P : PreSubmersivePresentation R S ι σ) (T : Type*) [CommRing T]
    [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalization.Away P.jacobian T] :
    IsStandardSmoothOfRelativeDimension P.dimension R T := by
  let Q := PreSubmersivePresentation.localizationAway T P.jacobian
  let QP : SubmersivePresentation R T (Unit ⊕ ι) (Unit ⊕ σ) :=
    { Q.comp P with
      jacobian_isUnit := by
        rw [comp_jacobian_eq_jacobian_smul_jacobian, Algebra.smul_def,
          localizationAway_jacobian]
        exact (IsLocalization.Away.algebraMap_isUnit P.jacobian).mul
          (IsLocalization.Away.algebraMap_isUnit P.jacobian) }
  apply QP.isStandardSmoothOfRelativeDimension
  exact (Q.dimension_comp_eq_dimension_add_dimension P).trans (by
    simp [Presentation.dimension])

end Algebra.PreSubmersivePresentation
