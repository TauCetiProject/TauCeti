/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IntersectionNumber.FieldTower
public import TauCeti.AlgebraicGeometry.SpecialFiber.Weight

/-!
# Divisibility of intersection numbers by component weights

Let `X` be a proper scheme over a local ring `R` with residue field `k`, and let `C` be the reduced
closure of a point of the special fibre, with constant field `κ = H⁰(C, 𝒪_C)` and weight
`w = [κ : k]` (`AlgebraicGeometry.Scheme.Hom.specialFiberWeight`). This file proves that `w`
divides the intersection number `(a · C)_k` along any morphism `ι : C ⟶ Y`, as an application of
`TauCeti.AlgebraicGeometry.LineBundleClass.finrank_cohomology_zero_trivial_dvd_intersectionNumber`.

The matrix corollary for the components of a regular model lives in
`TauCeti.AlgebraicGeometry.IntersectionNumber.Weight.Matrix`.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.specialFiberWeight_dvd_intersectionNumber`: the weight of the
  reduced closure of any point in the special fibre divides its intersection number with any line
  bundle.

## References

* [The Stacks Project, Section 55.8](https://stacks.math.columbia.edu/tag/0C6Y) and
  [Section 55.9](https://stacks.math.columbia.edu/tag/0C5Y), for the numerical type of a regular
  model.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 9.1.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.IdealSheafData (vanishingIdeal)

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- **The weight of a component divides any intersection number on it.** For a proper scheme `X`
over a local ring `R` and a point `x` of the special fibre with reduced closure `C`, the weight
`w = dim_k H⁰(C, 𝒪_C)` divides `(a · C)_k` along any morphism `ι : C ⟶ Y`. -/
theorem specialFiberWeight_dvd_intersectionNumber {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) [IsProper toBase] {x : X}
    (hx : toBase x = closedPoint R) {Y : Scheme.{u}}
    (ι : (vanishingIdeal ⟨closure {x}, isClosed_closure⟩).subscheme ⟶ Y)
    (a : LineBundleClass Y) :
    letI := subschemeOverResidueField
      (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton hx)
    (toBase.specialFiberWeight hx : ℤ) ∣
      LineBundleClass.intersectionNumber (ResidueField R) ι a := by
  let := subschemeOverResidueField
    (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton hx)
  rw [specialFiberWeight_def]
  exact LineBundleClass.finrank_cohomology_zero_trivial_dvd_intersectionNumber (ResidueField R) ι
    (toBase.isField_globalSections_subscheme_closure_singleton hx) a

end AlgebraicGeometry.Scheme.Hom

end
