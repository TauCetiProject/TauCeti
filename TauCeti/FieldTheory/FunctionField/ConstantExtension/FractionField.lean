/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.LinearDisjoint
public import TauCeti.FieldTheory.Separable.Regular
public import TauCeti.RingTheory.TensorProduct.FractionRing
import TauCeti.FieldTheory.FunctionField.SeparablyGenerated

/-!
# Constant extension through the fraction field of a tensor product

Suppose `F ⊗[k] K` is a domain. Its fraction field, with the scalar maps from both
factors, is the linearly disjoint compositum `F · K`. If `F/k` is a one-variable
function field, it is therefore a one-variable function field over `K` too,
transcendental and separating parameters of `F/k` remain transcendental and separating
in `Frac(F ⊗[k] K)` over `K`, and `[Frac(F ⊗[k] K) : K(x)] = [F : k(x)]` for every
parameter `x` with `F / k(x)` finite. The extension `K/k` need not be algebraic.

For a one-variable function field `F/k`, geometric reducedness is equivalent to the
existence of a separating element, so `F ⊗[k] Ω` is a domain for an algebraically
closed field `Ω` over `k` (equivalently, `F ⊗[k] K` is a domain for every field
extension `K/k`) if and only if `F/k` admits a separating element and `k` is
integrally closed in `F`. We retain the actual fraction-field carrier rather than
asserting that the tensor product itself is a field; the results apply to any
specified fraction field with compatible scalar maps.

## Main results

* `TauCeti.IsFunctionField.isGeometricallyReduced_iff_exists_separating`,
  `TauCeti.IsFunctionField.isDomain_tensorProduct_iff_exists_separating_and_isIntegrallyClosedIn`,
  `TauCeti.IsFunctionField.forall_isDomain_tensorProduct_field_iff`: regular-extension
  equivalences for one-variable function fields.
* `TauCeti.transcendental_algebraMap_of_isFractionRing_tensorProduct`,
  `TauCeti.isSeparable_adjoin_image_of_isFractionRing_tensorProduct`,
  `TauCeti.isSeparable_adjoin_simple_of_isFractionRing_tensorProduct`: persistence of
  transcendental and separating generators in `Frac(F ⊗[k] K)`.
* `TauCeti.IsFunctionField.of_isFractionRing_tensorProduct`,
  `TauCeti.finrank_over_adjoin_simple_eq_of_isFractionRing_tensorProduct`: preservation
  of the function-field property and degree over a parameter.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6.
* S. Lang, *Introduction to Algebraic Geometry*, Chapter III, Section 1.
* S. Lang, *Algebra*, the theory of linearly disjoint field extensions.
-/

public section

open scoped TensorProduct IntermediateField

namespace TauCeti

section RegularFunctionField

universe u v

/-- A one-variable function field is geometrically reduced over its base field if and
only if it admits a separating element. -/
theorem IsFunctionField.isGeometricallyReduced_iff_exists_separating
    {k F : Type*} [Field k] [Field F] [Algebra k F] (hF : IsFunctionField k F) :
    Algebra.IsGeometricallyReduced k F ↔
      ∃ x : F, Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F :=
  ⟨fun _ ↦ hF.exists_transcendental_and_isSeparable_adjoin_of_isGeometricallyReduced,
    fun ⟨_, hx, _⟩ ↦ isGeometricallyReduced_of_separating hx⟩

/-- **Regular-extension equivalence for one-variable function fields.** For an
algebraically closed field `Ω` over `k`, `F ⊗[k] Ω` is a domain if and only if `F/k`
admits a separating element and `k` is integrally closed in `F`. -/
theorem IsFunctionField.isDomain_tensorProduct_iff_exists_separating_and_isIntegrallyClosedIn
    {k F : Type*} [Field k] [Field F] [Algebra k F] (hF : IsFunctionField k F)
    (Ω : Type*) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] :
    IsDomain (F ⊗[k] Ω) ↔
      (∃ x : F, Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F) ∧
        IsIntegrallyClosedIn k F := by
  rw [isDomain_tensorProduct_iff_isGeometricallyReduced_and_isIntegrallyClosedIn Ω,
    hF.isGeometricallyReduced_iff_exists_separating]

/-- A one-variable function field `F/k` stays a domain after tensoring with every field
extension `K/k` if and only if `F/k` admits a separating element and `k` is integrally
closed in `F`. -/
theorem IsFunctionField.forall_isDomain_tensorProduct_field_iff
    {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F] (hF : IsFunctionField k F) :
    (∀ (K : Type u) [Field K] [Algebra k K], IsDomain (F ⊗[k] K)) ↔
      (∃ x : F, Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F) ∧
        IsIntegrallyClosedIn k F := by
  rw [TauCeti.forall_isDomain_tensorProduct_field_iff,
    hF.isGeometricallyReduced_iff_exists_separating]

end RegularFunctionField

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

variable {k F K Q : Type*} [Field k] [Field F] [Field K] [Field Q]
  [Algebra k F] [Algebra k K] [Algebra (F ⊗[k] K) Q]
  [Algebra k Q] [Algebra F Q] [Algebra K Q]
  [IsScalarTower F (F ⊗[k] K) Q]
  [IsScalarTower K (F ⊗[k] K) Q] [IsScalarTower k F Q] [IsScalarTower k K Q]
  [IsFractionRing (F ⊗[k] K) Q]

/-- If `F` is separable algebraic over `k(S)`, then any fraction field `Q` of `F ⊗[k] K`
is separable algebraic over `K(S)`. -/
theorem isSeparable_adjoin_image_of_isFractionRing_tensorProduct {S : Set F}
    [Algebra.IsSeparable (IntermediateField.adjoin k S) F] :
    Algebra.IsSeparable (IntermediateField.adjoin K (algebraMap F Q '' S)) Q :=
  isSeparable_adjoin_image_of_constantCompositum_eq_top (k := k) <| by
    rw [constantCompositum_def]
    exact adjoin_range_right_eq_top_of_isFractionRing_tensorProduct (k := k)

/-- A separating parameter `x` of `F/k` remains separating over `K` in any fraction
field `Q` of `F ⊗[k] K`. -/
theorem isSeparable_adjoin_simple_of_isFractionRing_tensorProduct (x : F)
    [Algebra.IsSeparable k⟮x⟯ F] :
    Algebra.IsSeparable K⟮algebraMap F Q x⟯ Q := by
  have h := isSeparable_adjoin_image_of_isFractionRing_tensorProduct
    (k := k) (K := K) (Q := Q) (S := {x})
  rwa [Set.image_singleton] at h

variable [IsScalarTower k (F ⊗[k] K) Q]

/-- An element of `F` transcendental over `k` remains transcendental over `K` in any
fraction field `Q` of `F ⊗[k] K`. -/
theorem transcendental_algebraMap_of_isFractionRing_tensorProduct {x : F}
    (hx : Transcendental k x) : Transcendental K (algebraMap F Q x) :=
  (linearDisjoint_of_isFractionRing_tensorProduct (k := k)).transcendental_algebraMap hx

/-- A fraction field of a domain tensor product is a one-variable function field
over the enlarged constants. -/
theorem IsFunctionField.of_isFractionRing_tensorProduct (hF : IsFunctionField k F) :
    IsFunctionField K Q :=
  hF.of_constantCompositum_eq_top_of_linearDisjoint
    (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
    (by
      rw [constantCompositum_def]
      exact adjoin_range_right_eq_top_of_isFractionRing_tensorProduct (k := k))

/-- Tensor-fraction-field extension of constants preserves the degree over a parameter.
Neither the constants nor the relative extension need be separable. -/
theorem finrank_over_adjoin_simple_eq_of_isFractionRing_tensorProduct (x : F)
    [FiniteDimensional k⟮x⟯ F] :
    Module.finrank K⟮algebraMap F Q x⟯ Q = Module.finrank k⟮x⟯ F :=
  finrank_over_adjoin_simple_eq_of_linearDisjoint
    (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
    (by
      rw [constantCompositum_def]
      exact adjoin_range_right_eq_top_of_isFractionRing_tensorProduct (k := k)) x

/-- If `F/k` is a geometrically reduced one-variable function field with exact constants,
then the fraction field of `F ⊗[k] K` is a one-variable function field over `K`.
The enlarged constant field may be transcendental over the original one. -/
theorem IsFunctionField.fractionRing_tensorProduct (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F] :
    letI := isDomain_tensorProduct_of_isGeometricallyReduced hex K
    IsFunctionField K (FractionRing (F ⊗[k] K)) := by
  have := isDomain_tensorProduct_of_isGeometricallyReduced hex K
  exact hF.of_isFractionRing_tensorProduct

/-- If `F/k` is a one-variable function field with exact constants and a separating
element `x`, then the fraction field of `F ⊗[k] K` is a one-variable function field over
`K` for every field extension `K/k`. -/
theorem IsFunctionField.fractionRing_tensorProduct_of_separating (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {x : F} [Algebra.IsSeparable k⟮x⟯ F] :
    letI := isDomain_tensorProduct_of_separating hex (x := x) K
    IsFunctionField K (FractionRing (F ⊗[k] K)) := by
  have := isDomain_tensorProduct_of_separating hex (x := x) K
  exact hF.of_isFractionRing_tensorProduct

end TauCeti
