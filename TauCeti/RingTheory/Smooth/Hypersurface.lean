/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Smooth.Jacobian
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.RingHom.Locally

/-!
# Smooth affine hypersurfaces

For an equation in finitely many variables, inverting a partial derivative makes its coordinate
ring standard smooth, of relative dimension the number of variables minus one. If the equation
and its partial derivatives generate the unit ideal, these open sets cover the hypersurface.
This gives the local standard-smooth criterion used on affine charts of projective hypersurfaces.

## References

* Stacks Project, Tag 00T7.
-/

public section

namespace MvPolynomial

section Localization

variable {R ι : Type*} [CommRing R] [Fintype ι]

/-- A hypersurface in `ι` variables is standard smooth of relative dimension `card ι - 1`
after inverting any one of its partial derivatives. -/
theorem isStandardSmoothOfRelativeDimension_localizationAway_pderiv
    (g : MvPolynomial ι R) (j : ι) :
    Algebra.IsStandardSmoothOfRelativeDimension (Fintype.card ι - 1) R
      (Localization.Away (Ideal.Quotient.mk (Ideal.span {g}) (pderiv j g))) := by
  classical
  let v : Fin 1 → MvPolynomial ι R := fun _ ↦ g
  have hv : Set.range v = {g} := Set.range_const
  let P := Algebra.PreSubmersivePresentation.naive (v := v) (fun _ ↦ j)
    (Function.injective_of_subsingleton _)
  have hJ : P.jacobian = Ideal.Quotient.mk (Ideal.span (Set.range v)) (pderiv j g) := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_fin_one]
    simp only [P, Algebra.PreSubmersivePresentation.jacobiMatrix_naive, v]
    -- The naive presentation's algebra map is the quotient map.
    rfl
  have : IsLocalization.Away P.jacobian
      (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range v)) (pderiv j g))) := by
    rw [hJ]
    infer_instance
  have h : Algebra.IsStandardSmoothOfRelativeDimension (Fintype.card ι - 1) R
      (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range v)) (pderiv j g))) := by
    simpa [Algebra.Presentation.dimension] using
      P.isStandardSmoothOfRelativeDimension_localizationAway
        (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range v)) (pderiv j g)))
  rw [hv] at h
  exact h

end Localization

section Locally

universe u v

variable {R : Type (max u v)} {ι : Type v} [CommRing R] [Fintype ι]

/-- If an equation and its partial derivatives generate the unit ideal, its hypersurface
is locally standard smooth of relative dimension the number of variables minus one. -/
theorem locally_isStandardSmoothOfRelativeDimension_quotient
    (g : MvPolynomial ι R)
    (h : Ideal.span (insert g (Set.range fun j ↦ pderiv j g)) = ⊤) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension (Fintype.card ι - 1))
      (algebraMap R (MvPolynomial ι R ⧸ Ideal.span {g})) := by
  have hspan : Ideal.span (Set.range fun j ↦
      Ideal.Quotient.mk (Ideal.span {g}) (pderiv j g)) = ⊤ := by
    have hmap := congrArg (Ideal.map (Ideal.Quotient.mk (Ideal.span {g}))) h
    rw [Ideal.map_span, Set.image_insert_eq, ← Set.range_comp] at hmap
    simpa [Ideal.map_top, Function.comp_def] using hmap
  refine RingHom.locally_of_exists RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ _
    hspan (fun j ↦ Localization.Away
      (Ideal.Quotient.mk (Ideal.span {g}) (pderiv j g))) fun j ↦ ?_
  rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact isStandardSmoothOfRelativeDimension_localizationAway_pderiv g j

end Locally

end MvPolynomial
