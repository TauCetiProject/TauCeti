/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IntersectionNumber.FieldTower
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Matrix
import TauCeti.AlgebraicGeometry.Geometrically.GlobalSections

/-!
# Weights and genera of the components of the special fibre

Let `R` be a local ring with residue field `k`, let `X → Spec R` be proper, and let `C` be the
closure of a point of the special fibre, with its reduced structure, for instance an irreducible
component of the special fibre of a proper regular model of a curve. Then `C` is an integral
scheme proper over `k`, so its global functions form a field
`κ_C = H⁰(C, 𝒪_C)`, the **constant field** of `C`
(`AlgebraicGeometry.Scheme.isField_globalSections_of_isReduced_of_connectedSpace`). The numerical
type of a regular model ([Stacks, Tag 0C6Z](https://stacks.math.columbia.edu/tag/0C6Z) and
[Section 55.9](https://stacks.math.columbia.edu/tag/0C9U)) attaches to the component `C` its
**weight** and its **genus**,

`w_C = [κ_C : k] = dim_k H⁰(C, 𝒪_C)` and `g_C = dim_{κ_C} H¹(C, 𝒪_C)`,

the genus being taken over the constant field rather than over `k`.

This file defines the weight (`AlgebraicGeometry.Scheme.Hom.specialFiberWeight`) and proves the
properties of weights and genera that the numerical type requires:

* the weight is positive when `H⁰(C, 𝒪_C)` is finite-dimensional over `k`;
* the dimension of `H¹(C, 𝒪_C)` over `k` is `w_C g_C`;
* the weight `wᵢ` of the `i`-th component divides every entry `aᵢⱼ = (Cⱼ · Cᵢ)` in the `i`-th row
  of the intersection matrix of the special fibre, the divisibility axiom
  `TauCeti.NumericalType.weight_dvd` of an abstract numerical type.

Each of these reduces to the tower law for cohomology over the constant field,
`AlgebraicGeometry.Scheme.Modules.finrank_cohomology_eq_finrank_cohomology_zero_trivial_mul`.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.specialFiberWeight`: the weight `dim_k H⁰(C, 𝒪_C)` of the closure
  `C` of a point of the special fibre.
* `AlgebraicGeometry.Scheme.Hom.isField_globalSections_subscheme_closure_singleton`: the global
  functions on `C` form a field.
* `AlgebraicGeometry.Scheme.Hom.specialFiberWeight_pos`: the weight is positive.
* `AlgebraicGeometry.Scheme.Hom.specialFiberWeight_mul_finrank_cohomology_one`:
  `w_C · dim_{κ_C} H¹(C, 𝒪_C) = dim_k H¹(C, 𝒪_C)`.
* `AlgebraicGeometry.Scheme.Hom.specialFiberWeight_dvd_specialFiberIntersectionMatrix`: the
  weight of the `i`-th component divides the `i`-th row of the intersection matrix.

## References

* [The Stacks Project, Section 55.8](https://stacks.math.columbia.edu/tag/0C6Y) and
  [Section 55.9](https://stacks.math.columbia.edu/tag/0C9U), for the weights and genera of the
  components of the numerical type of a regular model.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 9.1.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing Order
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.IdealSheafData (vanishingIdeal)

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R))

/-- The **weight** of the closure `C` of a point `x` of the special fibre of a scheme over a local
ring `R`: the dimension `dim_k H⁰(C, 𝒪_C)` over the residue field `k` of `R`, where `C` carries its
reduced structure and its structure over `k` through the special fibre. When `X` is proper over
`R`, the global functions on `C` form a field `κ_C`
(`AlgebraicGeometry.Scheme.Hom.isField_globalSections_subscheme_closure_singleton`), and the weight
is the degree `[κ_C : k]` of this constant field. -/
def specialFiberWeight {x : X} (hx : toBase x = closedPoint R) : ℕ :=
  letI := subschemeOverResidueField
    (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton hx)
  Module.finrank (ResidueField R) (Cohomology (InvertibleSheaf.trivial
    (vanishingIdeal ⟨closure {x}, isClosed_closure⟩).subscheme).obj 0)

/-- The weight of the closure `C` of a point of the special fibre is `dim_k H⁰(C, 𝒪_C)`. -/
theorem specialFiberWeight_def {x : X} (hx : toBase x = closedPoint R) :
    toBase.specialFiberWeight hx =
      letI := subschemeOverResidueField
        (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton hx)
      Module.finrank (ResidueField R) (Cohomology (InvertibleSheaf.trivial
        (vanishingIdeal ⟨closure {x}, isClosed_closure⟩).subscheme).obj 0) := by
  rw [specialFiberWeight]

/-- **The weight of a component of the special fibre is positive.** The closure `C` of a point
of the special fibre of a scheme over a local ring `R` has positive weight `dim_k H⁰(C, 𝒪_C)` as
soon as `H⁰(C, 𝒪_C)` is finite-dimensional over the residue field `k`. -/
theorem specialFiberWeight_pos {x : X} (hx : toBase x = closedPoint R)
    (h₀ :
      letI := subschemeOverResidueField
        (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton hx)
      FiniteDimensional (ResidueField R) (Cohomology (InvertibleSheaf.trivial
        (vanishingIdeal ⟨closure {x}, isClosed_closure⟩).subscheme).obj 0)) :
    0 < toBase.specialFiberWeight hx := by
  let := subschemeOverResidueField (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton hx)
  rw [specialFiberWeight_def]
  -- `H⁰(C, 𝒪_C)` is a one-dimensional vector space over the constant field, hence nonzero.
  have : Nontrivial (Cohomology (InvertibleSheaf.trivial
      (vanishingIdeal ⟨closure {x}, isClosed_closure⟩).subscheme).obj 0) :=
    Module.nontrivial_of_finrank_eq_succ
      Scheme.Modules.finrank_globalSections_cohomology_zero_trivial_eq_one
  exact Module.finrank_pos

variable [IsProper toBase]

/-- **The constant field of a component of the special fibre.** For `X` proper over a local ring
`R`, the global functions on the closure of a point of the special fibre, with its reduced
structure, form a field: this closure is an integral scheme proper over the residue field. -/
theorem isField_globalSections_subscheme_closure_singleton {x : X}
    (hx : toBase x = closedPoint R) :
    IsField Γ((vanishingIdeal ⟨closure {x}, isClosed_closure⟩).subscheme, ⊤) := by
  let := subschemeOverResidueField (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton hx)
  have := isProper_subschemeOverResidueField
    (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton hx)
  exact Scheme.isField_globalSections_of_isReduced_of_connectedSpace _ (ResidueField R)

/-- **The genus of a component of the special fibre over its constant field.** For `X` proper over
a local ring `R` and the closure `C` of a point of the special fibre, with constant field
`κ_C = H⁰(C, 𝒪_C)`, the weight `w_C = [κ_C : k]` and the genus `g_C = dim_{κ_C} H¹(C, 𝒪_C)` satisfy
`w_C g_C = dim_k H¹(C, 𝒪_C)`, where `k` is the residue field of `R`. -/
theorem specialFiberWeight_mul_finrank_cohomology_one {x : X}
    (hx : toBase x = closedPoint R) :
    letI := subschemeOverResidueField
      (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton hx)
    toBase.specialFiberWeight hx *
        Module.finrank Γ((vanishingIdeal ⟨closure {x}, isClosed_closure⟩).subscheme, ⊤)
          (Cohomology (InvertibleSheaf.trivial
            (vanishingIdeal ⟨closure {x}, isClosed_closure⟩).subscheme).obj 1) =
      Module.finrank (ResidueField R) (Cohomology (InvertibleSheaf.trivial
        (vanishingIdeal ⟨closure {x}, isClosed_closure⟩).subscheme).obj 1) := by
  let := subschemeOverResidueField (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton hx)
  rw [specialFiberWeight_def]
  exact (Scheme.Modules.finrank_cohomology_eq_finrank_cohomology_zero_trivial_mul (ResidueField R)
    (toBase.isField_globalSections_subscheme_closure_singleton hx) _ 1).symm

variable [Ring.DimensionLEOne R] [IsIntegral X] [IsNoetherian X]
  [TauCeti.AlgebraicGeometry.IsRegular X]

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
