/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.RationalFunctions
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# Rational functions without poles are regular

On a locally Noetherian integral scheme a regular function has nonnegative order at every point
where it is defined (`TauCeti.AlgebraicGeometry.Scheme.ord_germToFunctionField_nonneg`). This file
proves the converse for a scheme of dimension at most one whose codimension-one local rings on an
open subset `U` are discrete valuation rings: a rational function with no poles on `U` is the germ
of a regular function on `U`.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.exists_algebraMap_stalk_eq_of_ord_nonneg`: at a
  codimension-one point whose local ring is a discrete valuation ring, a rational function of
  nonnegative order lies in that local ring;
* `TauCeti.AlgebraicGeometry.Scheme.exists_algebraMap_stalk_eq_of_coheight_eq_zero`: at a point
  with no proper generization the local ring is already the whole function field;
* `TauCeti.AlgebraicGeometry.Scheme.exists_germToFunctionField_eq_of_ord_nonneg`: a rational
  function with nonnegative order at every codimension-one point of `U` is the germ at the generic
  point of a section of `𝒪_X` over `U`;
* `TauCeti.AlgebraicGeometry.Scheme.exists_unit_germToFunctionField_eq_of_ord_eq_zero`: a nonzero
  rational function with *zero* order at every codimension-one point of `U` is the germ of a unit
  of `Γ(X, U)`.

The third statement is the one-dimensional case of algebraic Hartogs' principle, and it is the
input that identifies the sheaf `𝒪_X(0)` of the zero divisor with the structure sheaf. The last
one applies it to a function and to its inverse; it is the local comparison used to glue the
local equations of a locally principal Weil divisor into a Cartier divisor.

The argument follows Hartshorne, *Algebraic Geometry*, II.6.3A and Proposition II.6.11, in the
dimension-one case where the intersection of the local rings can be taken over the points of `U`
themselves. The local step is Mathlib's `IsDiscreteValuationRing.exists_lift_of_le_one` together
with `Ring.ordFrac_eq_valuation_inv`, and the global step, that a rational function lying in every
local ring of `U` is regular on `U`, is
`TauCeti.AlgebraicGeometry.Scheme.exists_germToFunctionField_eq_of_forall_mem_range`.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite Order TopologicalSpace
open scoped WithZero

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

noncomputable section

namespace Scheme

/-- At a codimension-one point whose local ring is a discrete valuation ring, a rational function
of nonnegative order is a section of that local ring. This is the local half of the statement that
a rational function without poles is regular. -/
theorem exists_algebraMap_stalk_eq_of_ord_nonneg {x : X}
    [IsDiscreteValuationRing (X.presheaf.stalk x)] (hx : coheight x = 1)
    {f : X.functionField} (hf : 0 ≤ X.ord f x) :
    ∃ g : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField g = f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨0, map_zero _⟩
  refine IsDiscreteValuationRing.exists_lift_of_le_one ?_
  have h1 : (1 : ℤᵐ⁰) ≤ X.ordHom x hx f := by
    simpa using (X.le_ord_iff hx hf0 (n := 0)).mp (by simpa using hf)
  simp only [_root_.AlgebraicGeometry.Scheme.ordHom, Ring.ordFrac_eq_valuation_inv] at h1
  exact (one_le_inv_iff₀.mp h1).2

omit [IsLocallyNoetherian X] in
/-- At a point with no proper generization the local ring is the whole function field: it is a
zero-dimensional local domain, hence a field, and it has the function field as its field of
fractions. -/
theorem exists_algebraMap_stalk_eq_of_coheight_eq_zero {x : X} (hx : coheight x = 0)
    (f : X.functionField) :
    ∃ g : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField g = f := by
  have hdim : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hfield : IsField (X.presheaf.stalk x) :=
    Ring.isField_iff_maximal_bot.mpr (Ring.krullDimLE_zero_iff.mp hdim ⊥ Ideal.isPrime_bot)
  exact IsFractionRing.surjective_iff_isField.mpr hfield f

/-- **A rational function without poles is regular.** On a locally Noetherian integral scheme, let
`U` be a nonempty open subset of dimension at most one whose codimension-one local rings are
discrete valuation rings. A rational function whose order is nonnegative at every codimension-one
point of `U` is the image of a section of `𝒪_X` over `U`.

This is the one-dimensional case of algebraic Hartogs' principle. The hypothesis on the dimension
enters only through the points of `U`: at a codimension-one point the discrete valuation gives the
bound, and at a point with no proper generization the local ring is already the function field. -/
theorem exists_germToFunctionField_eq_of_ord_nonneg
    {U : X.Opens} [Nonempty U]
    (hDVR : ∀ y : CodimensionOnePoint X, (y : X) ∈ U →
      IsDiscreteValuationRing (X.presheaf.stalk (y : X)))
    (hU : ∀ y ∈ U, coheight y ≤ 1) {f : X.functionField}
    (hf : ∀ (y : CodimensionOnePoint X), (y : X) ∈ U → 0 ≤ X.ord f y) :
    ∃ a : Γ(X, U), X.germToFunctionField U a = f := by
  refine exists_germToFunctionField_eq_of_forall_mem_range fun y hy ↦ ?_
  rcases eq_or_lt_of_le (hU y hy) with hy' | hy'
  · have : IsDiscreteValuationRing (X.presheaf.stalk y) := hDVR ⟨y, hy'⟩ hy
    exact exists_algebraMap_stalk_eq_of_ord_nonneg hy' (hf ⟨y, hy'⟩ hy)
  · exact exists_algebraMap_stalk_eq_of_coheight_eq_zero (Order.lt_one_iff.mp hy') f

/-- **A rational function without zeros or poles is a regular unit.** On a locally Noetherian
integral scheme, let `U` be a nonempty open subset of dimension at most one whose codimension-one
local rings are discrete valuation rings. A nonzero rational function whose order vanishes at
every codimension-one point of `U` is the germ of a unit of `Γ(X, U)`.

Simultaneous regularity of the function and its inverse makes the resulting section a unit. -/
theorem exists_unit_germToFunctionField_eq_of_ord_eq_zero
    {U : X.Opens} [Nonempty U]
    (hDVR : ∀ y : CodimensionOnePoint X, (y : X) ∈ U →
      IsDiscreteValuationRing (X.presheaf.stalk (y : X)))
    (hU : ∀ y ∈ U, coheight y ≤ 1) {f : X.functionFieldˣ}
    (hf : ∀ (y : CodimensionOnePoint X), (y : X) ∈ U → X.ord (f : X.functionField) y = 0) :
    ∃ a : Γ(X, U)ˣ, X.germToFunctionField U (a : Γ(X, U)) = (f : X.functionField) := by
  obtain ⟨a, ha⟩ := exists_germToFunctionField_eq_of_ord_nonneg hDVR hU
    (f := (f : X.functionField)) fun y hy ↦ (hf y hy).ge
  obtain ⟨b, hb⟩ := exists_germToFunctionField_eq_of_ord_nonneg hDVR hU
    (f := ((f⁻¹ : X.functionFieldˣ) : X.functionField)) fun y hy ↦ by
      rw [Units.val_inv_eq_inv_val, ord_inv, hf y hy, neg_zero]
  have hab : a * b = 1 := by
    refine X.germToFunctionField_injective U ?_
    rw [map_mul, ha, hb, map_one, Units.mul_inv]
  exact ⟨⟨a, b, hab, (mul_comm b a).trans hab⟩, ha⟩

end Scheme

end

end AlgebraicGeometry

end TauCeti
