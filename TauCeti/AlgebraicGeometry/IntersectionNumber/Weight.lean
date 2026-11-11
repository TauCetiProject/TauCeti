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

* `AlgebraicGeometry.Scheme.Hom.specialFiberWeight_dvd_specialFiberIntersectionMatrix`: the
  weight of the `i`-th component divides the `i`-th row of the intersection matrix.

## References

* [The Stacks Project, Section 55.8](https://stacks.math.columbia.edu/tag/0C6Y) and
  [Section 55.9](https://stacks.math.columbia.edu/tag/0C9U), for the numerical type of a regular
  model.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 9.1.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing Order
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.IdealSheafData (vanishingIdeal)

universe u

namespace AlgebraicGeometry.Scheme.Hom

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
  have hi : toBase (i : CodimensionOnePoint X) = closedPoint R := (Set.Finite.mem_toFinset _).mp i.2
  let := subschemeOverResidueField (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton hi)
  rw [specialFiberWeight_def, specialFiberIntersectionMatrix_apply]
  exact LineBundleClass.finrank_cohomology_zero_trivial_dvd_intersectionNumber (ResidueField R) _
    (toBase.isField_globalSections_subscheme_closure_singleton hi) _

end AlgebraicGeometry.Scheme.Hom

end
