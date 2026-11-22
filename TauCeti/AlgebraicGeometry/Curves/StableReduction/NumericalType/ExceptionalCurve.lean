/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Minimal
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.RegularModel
public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve

/-!
# Exceptional components of the special fibre are `(-1)`-indices

Let `X` be a regular model over a discrete valuation ring `R` with residue field `k`, in the
setting of `AlgebraicGeometry.Scheme.Hom.specialFiberNumericalType`, and let `Cᵢ` be a component
of its special fibre, with its reduced structure. If `Cᵢ` is an exceptional curve of the first
kind (`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurve`), then `i` is a `(-1)`-index
of the numerical type of `X` (`TauCeti.NumericalType.IsMinusOneIndex`): its genus is `gᵢ = 0` and
its self-intersection is `aᵢᵢ = -wᵢ`.

Indeed, `Cᵢ ≅ ℙ¹_κ` has `H¹(Cᵢ, 𝒪_{Cᵢ}) = 0`, and its self-intersection over `k` is minus the
degree `wᵢ = dim_k H⁰(Cᵢ, 𝒪_{Cᵢ})` of its constant field, since the normal sheaf `𝒪_X(Cᵢ)|_{Cᵢ}`
has degree `-1` over that field
(`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurve.intersectionNumber_self`).

Consequently, when the numerical type of `X` is minimal, no component of the special fibre is an
exceptional curve of the first kind. This is one half of the comparison
([Stacks, Section 55.9](https://stacks.math.columbia.edu/tag/0C9U)) between minimal regular
models and minimal numerical types; the converse, that a `(-1)`-index is an exceptional curve,
requires recognizing a genus-zero curve carrying a line bundle of degree `-1` as a projective line.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isMinusOneIndex_specialFiberNumericalType`: an exceptional
  component of the special fibre is a `(-1)`-index of the numerical type.
* `AlgebraicGeometry.Scheme.Hom.not_isExceptionalCurve_of_isMinimal`: if the numerical type is
  minimal, no component of the special fibre is an exceptional curve of the first kind.

## References

* [The Stacks Project, Section 55.9](https://stacks.math.columbia.edu/tag/0C9U), for the
  numerical type of a regular model, and
  [Tag 0C76](https://stacks.math.columbia.edu/tag/0C76) for `(-1)`-indices.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 9.3.1.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing Order
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.IdealSheafData (vanishingIdeal)

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {R : Type u} [CommRing R] [IsLocalRing R] [Ring.DimensionLEOne R]
  {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) [IsIntegral X] [IsNoetherian X]
  [TauCeti.AlgebraicGeometry.IsRegular X] [IsProper toBase] [Flat toBase]
  [ConnectedSpace (specialFiber R toBase).left]
  (hX : ∀ x : X, coheight x ≤ 2)
  {π : R} (hπ : maximalIdeal R = Ideal.span {π}) (hreg : IsSMulRegular R π)

/-- **Exceptional components are `(-1)`-indices.** If a component `Cᵢ` of the special fibre of a
regular model, with its reduced structure, is an exceptional curve of the first kind, then `i` is
a `(-1)`-index of the numerical type of the model: `gᵢ = 0` and `aᵢᵢ = -wᵢ`. -/
theorem isMinusOneIndex_specialFiberNumericalType
    (i : (toBase.specialFiberNumericalType hX hπ hreg).Component)
    (hi : (vanishingIdeal ⟨closure {(i.val : X)}, isClosed_closure⟩).IsExceptionalCurve) :
    (toBase.specialFiberNumericalType hX hπ hreg).IsMinusOneIndex i := by
  have hc := toBase.base_eq_closedPoint_of_specialFiberNumericalType hX hπ hreg i
  let := subschemeOverResidueField (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton hc)
  refine (NumericalType.isMinusOneIndex_iff _).mpr ⟨?_, ?_⟩
  · -- `wᵢ gᵢ = dim_k H¹(Cᵢ, 𝒪_{Cᵢ}) = 0` with `wᵢ > 0`.
    have h := toBase.specialFiberWeight_mul_finrank_cohomology_one hc
    rw [hi.finrank_cohomology_one_trivial (ResidueField R), mul_eq_zero] at h
    exact h.resolve_left (toBase.specialFiberWeight_pos hc
      (toBase.finiteDimensional_cohomology_zero_subscheme_closure_singleton hc)).ne'
  · rw [specialFiberNumericalType_intersection_apply,
      hi.intersectionNumber_self (ResidueField R), specialFiberNumericalType_weight,
      specialFiberWeight_def]

/-- **A minimal numerical type has no exceptional components.** If the numerical type of a
regular model is minimal, then no component of its special fibre, with its reduced structure, is
an exceptional curve of the first kind. -/
theorem not_isExceptionalCurve_of_isMinimal
    (hmin : (toBase.specialFiberNumericalType hX hπ hreg).IsMinimal)
    (i : (toBase.specialFiberNumericalType hX hπ hreg).Component) :
    ¬ (vanishingIdeal ⟨closure {(i.val : X)}, isClosed_closure⟩).IsExceptionalCurve :=
  fun hi ↦ (NumericalType.isMinimal_iff _).mp hmin i
    (toBase.isMinusOneIndex_specialFiberNumericalType hX hπ hreg i hi)

end AlgebraicGeometry.Scheme.Hom

end
