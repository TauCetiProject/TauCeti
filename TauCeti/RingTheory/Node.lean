/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Smooth.Jacobian
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Smooth.Locus

/-!
# Smooth coordinate charts of the nodal equation

The algebra `NodeAlgebra R a = R[x,y]/(xy-a)` is the local model for smoothing a node.
Inverting either coordinate gives a standard smooth algebra of relative dimension one.
Consequently a prime at which at least one coordinate is nonzero belongs to the smooth
locus. These assertions hold over any commutative base ring.

For a discrete valuation ring and `a = πⁿ`, this supplies the smooth charts away from
the origin in the local model used to resolve nodal curves.

## References

* Stacks Project, Example 55.14.1, Tag 0CDC.
-/

public section

noncomputable section

namespace TauCeti

open MvPolynomial Algebra

/-- The coordinate algebra of the equation `xy = a` over `R`. -/
abbrev NodeAlgebra (R : Type*) [CommRing R] (a : R) :=
  MvPolynomial (Fin 2) R ⧸ Ideal.span {X 0 * X 1 - C a}

namespace NodeAlgebra

variable {R : Type*} [CommRing R] (a : R)

/-- The two coordinate functions on `xy = a`. -/
def coord (i : Fin 2) : NodeAlgebra R a :=
  Ideal.Quotient.mk _ (X i)

lemma coord_def (i : Fin 2) :
    coord a i = Ideal.Quotient.mk (Ideal.span {X 0 * X 1 - C a}) (X i) :=
  (rfl)

/-- The defining equation of the nodal algebra. -/
@[simp]
lemma coord_zero_mul_coord_one :
    coord a 0 * coord a 1 = algebraMap R (NodeAlgebra R a) a := by
  apply sub_eq_zero.mp
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton (X (0 : Fin 2) * X 1 - C a)))
  have hC : Ideal.Quotient.mk (Ideal.span {X (0 : Fin 2) * X 1 - C a}) (C a) =
      algebraMap R (NodeAlgebra R a) a :=
    Ideal.Quotient.mk_algebraMap R _ a
  simpa only [coord, map_sub, map_mul, hC] using h

private def presentation : Presentation R (NodeAlgebra R a) (Fin 2) Unit where
  __ := Generators.naive
  relation _ := X 0 * X 1 - C a
  span_range_relation_eq_ker := by
    simpa using (Generators.ker_naive (R := R)
      (σ := Fin 2) (I := Ideal.span {X 0 * X 1 - C a}) _ _).symm

/-- The nodal equation is an algebra of finite presentation over its coefficient ring. -/
instance : FinitePresentation R (NodeAlgebra R a) :=
  (presentation a).finitePresentation_of_isFinite

private def prePresentation (i : Fin 2) :
    PreSubmersivePresentation R (NodeAlgebra R a) (Fin 2) Unit where
  __ := presentation a
  map _ := 1 - i
  map_inj := Function.injective_of_subsingleton _

private lemma prePresentation_jacobian (i : Fin 2) :
    (prePresentation a i).jacobian = coord a i := by
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_unique]
  rw [PreSubmersivePresentation.jacobiMatrix_apply]
  fin_cases i <;> simp [prePresentation, presentation, coord] <;> rfl

/-- Each coordinate chart of `xy = a` is standard smooth of relative dimension one. -/
theorem isStandardSmoothOfRelativeDimension_away_coord (i : Fin 2) :
    IsStandardSmoothOfRelativeDimension 1 R (Localization.Away (coord a i)) := by
  have : IsLocalization.Away (prePresentation a i).jacobian
      (Localization.Away (coord a i)) := by
    rw [prePresentation_jacobian]
    infer_instance
  simpa [Presentation.dimension] using
    (prePresentation a i).isStandardSmoothOfRelativeDimension_localizationAway
      (Localization.Away (coord a i))

/-- The complement of either coordinate's zero locus lies in the smooth locus of `xy = a`. -/
theorem basicOpen_coord_subset_smoothLocus (i : Fin 2) :
    (PrimeSpectrum.basicOpen (coord a i) : Set (PrimeSpectrum (NodeAlgebra R a))) ⊆
      Algebra.smoothLocus R (NodeAlgebra R a) := by
  have := (isStandardSmoothOfRelativeDimension_away_coord a i).isStandardSmooth
  exact Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr inferInstance

/-- A point of `xy = a` is smooth whenever at least one coordinate is outside its prime ideal. -/
theorem isSmoothAt_of_coord_notMem (p : Ideal (NodeAlgebra R a)) [p.IsPrime]
    (h : ∃ i, coord a i ∉ p) : Algebra.IsSmoothAt R p := by
  obtain ⟨i, hi⟩ := h
  exact basicOpen_coord_subset_smoothLocus a i
    ((PrimeSpectrum.mem_basicOpen _ ⟨p, inferInstance⟩).mpr hi)

/-- If the smoothing parameter is invertible, the whole nodal algebra is standard smooth
of relative dimension one. This includes `xy = 1` and `xy = a` over a field with `a ≠ 0`. -/
theorem isStandardSmoothOfRelativeDimension_of_isUnit (ha : IsUnit a) :
    IsStandardSmoothOfRelativeDimension 1 R (NodeAlgebra R a) := by
  have hx : IsUnit (coord a 0) := by
    have h := ha.map (algebraMap R (NodeAlgebra R a))
    rw [← coord_zero_mul_coord_one] at h
    exact isUnit_of_mul_isUnit_left h
  let P : SubmersivePresentation R (NodeAlgebra R a) (Fin 2) Unit :=
    { prePresentation a 0 with
      jacobian_isUnit := by rwa [prePresentation_jacobian] }
  exact P.isStandardSmoothOfRelativeDimension (by simp [Presentation.dimension])

end NodeAlgebra

end TauCeti
