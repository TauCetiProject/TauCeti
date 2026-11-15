/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IntersectionNumber.FieldTower
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Matrix
public import TauCeti.AlgebraicGeometry.SpecialFiber.Weight

/-!
# Weights of the components of the special fibre divide the intersection matrix

Let `X` be a regular model over a local ring `R` with residue field `k`, and let `Cᵢ` be the
components of its special fibre, with constant fields `κᵢ = H⁰(Cᵢ, 𝒪_{Cᵢ})` and weights
`wᵢ = [κᵢ : k]` (`AlgebraicGeometry.Scheme.Hom.specialFiberWeight`). This file proves that `wᵢ`
divides every entry `aᵢⱼ = (Cⱼ · Cᵢ)` in the `i`-th row of the intersection matrix of the special
fibre, the divisibility axiom `TauCeti.NumericalType.weight_dvd` of an abstract numerical type.
It is the constant-field divisibility of intersection numbers,
`TauCeti.AlgebraicGeometry.LineBundleClass.finrank_cohomology_zero_trivial_dvd_intersectionNumber`,
applied to the components.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.specialFiberWeight_dvd_intersectionNumber`: the weight of the
  closure of a point of the special fibre divides its intersection number with every line bundle.
* `AlgebraicGeometry.Scheme.Hom.specialFiberWeight_dvd_specialFiberIntersectionMatrix`: the
  weight of the `i`-th component divides the `i`-th row of the intersection matrix.

## References

* [The Stacks Project, Section 55.3 (Tag 0C6Y)](https://stacks.math.columbia.edu/tag/0C6Y) and
  [Section 55.9 (Tag 0C5Y)](https://stacks.math.columbia.edu/tag/0C5Y), for the numerical type of a
  regular model.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 9.1.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing Order
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.IdealSheafData (vanishingIdeal)

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- **The weight of a component divides its intersection numbers with every line bundle.** For a
scheme `X` proper over a local ring `R`, the closure `C` of a point `x` of the special fibre, and
any morphism `f : C ⟶ Y`, the weight `w_C = [κ_C : k]` divides the intersection number `(a · C)_k`
over the residue field `k` of every line-bundle class `a` on `Y`. -/
theorem specialFiberWeight_dvd_intersectionNumber {R : Type u} [CommRing R] [IsLocalRing R]
    {X Y : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) [IsProper toBase]
    {x : X} (hx : toBase x = closedPoint R)
    (f : (vanishingIdeal ⟨closure {x}, isClosed_closure⟩).subscheme ⟶ Y)
    (a : LineBundleClass Y) :
    letI := subschemeOverResidueField
      (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton hx)
    (toBase.specialFiberWeight hx : ℤ) ∣
      LineBundleClass.intersectionNumber (ResidueField R) f a := by
  let := subschemeOverResidueField (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton hx)
  rw [specialFiberWeight_def]
  exact LineBundleClass.finrank_cohomology_zero_trivial_dvd_intersectionNumber (ResidueField R) f
    (toBase.isField_globalSections_subscheme_closure_singleton hx) a

variable {R : Type u} [CommRing R] [IsLocalRing R] [Ring.DimensionLEOne R] {X : Scheme.{u}}
  [IsIntegral X] [IsNoetherian X] [TauCeti.AlgebraicGeometry.IsRegular X]
  (toBase : X ⟶ Spec (.of R)) [IsProper toBase]

/-- **The weight of a component divides its intersection numbers.** For a regular Noetherian
integral scheme `X`, proper over a local ring `R` of dimension at most one, with all points of
codimension at most two and generic point away from the closed point, the weight `wᵢ` of the
`i`-th component `Cᵢ` of the special fibre divides every entry `aᵢⱼ = (Cⱼ · Cᵢ)` of the `i`-th row
of the intersection matrix. -/
theorem specialFiberWeight_dvd_specialFiberIntersectionMatrix (hX : ∀ x : X, coheight x ≤ 2)
    (hη : toBase (genericPoint X) ≠ closedPoint R) (i j) :
    (toBase.specialFiberWeight ((Set.Finite.mem_toFinset _).mp i.2) : ℤ) ∣
      toBase.specialFiberIntersectionMatrix hX hη i j := by
  rw [specialFiberIntersectionMatrix_apply]
  exact toBase.specialFiberWeight_dvd_intersectionNumber ((Set.Finite.mem_toFinset _).mp i.2) _ _

end AlgebraicGeometry.Scheme.Hom

end
