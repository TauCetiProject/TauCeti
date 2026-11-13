/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.LinearDisjoint
public import TauCeti.FieldTheory.Separable.Regular
public import TauCeti.RingTheory.TensorProduct.FractionRing
import TauCeti.RingTheory.TensorProduct.Reduced

/-!
# Constant extension through the fraction field of a tensor product

Suppose `F ⊗[k] K` is a domain. Its fraction field, with the scalar maps from both
factors, is the linearly disjoint compositum `F · K`. If `F/k` is a one-variable
function field, it is therefore a one-variable function field over `K` too, a
transcendental (or separating) parameter `x` of `F/k` remains transcendental (or
separating) over `K`, and `[Frac(F ⊗[k] K) : K(x)] = [F : k(x)]`.
The extension `K/k` need not be algebraic.

The domain hypothesis is available from
`TauCeti.isDomain_tensorProduct_of_isGeometricallyReduced` for a geometrically reduced
field with exact constants (automatic when `k` is perfect, and needing neither
hypothesis when `k` is algebraically closed), and regularity — both exactness of `K`
and geometric reducedness over `K` — persists in `FractionRing (F ⊗[k] K)`
(`TauCeti.isIntegrallyClosedIn_fractionRing_tensorProduct` and
`TauCeti.isGeometricallyReduced_fractionRing_tensorProduct`). We retain
the actual fraction-field carrier, rather than asserting that the tensor product itself
is a field. The results also apply to any specified fraction field with compatible
scalar maps.

## Main results

* `TauCeti.constantCompositum_eq_top_of_isFractionRing_tensorProduct`,
  `TauCeti.IsFunctionField.of_isFractionRing_tensorProduct`,
  `Transcendental.algebraMap_of_isFractionRing_tensorProduct`,
  `TauCeti.isSeparable_adjoin_simple_of_isFractionRing_tensorProduct`,
  `TauCeti.finrank_over_adjoin_simple_eq_of_isFractionRing_tensorProduct`,
  `TauCeti.isSeparable_ratFunc_of_isFractionRing_tensorProduct`, and
  `TauCeti.finrank_ratFunc_eq_of_isFractionRing_tensorProduct`: compositum generation,
  function-field structure, transcendental and separating parameters, and degrees over `k(x)` and
  `RatFunc k` persist in any fraction field of `F ⊗[k] K`.
* `TauCeti.IsFunctionField.fractionRing_tensorProduct`,
  `TauCeti.IsFunctionField.fractionRing_tensorProduct_of_perfectField`, and
  `TauCeti.IsFunctionField.fractionRing_tensorProduct_of_isAlgClosed`: `FractionRing (F ⊗[k] K)` is
  a one-variable function field over `K` when `F/k` is regular, over a perfect base field with
  exact constants, or unconditionally over an algebraically closed base field.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6.
* S. Lang, *Algebra*, the theory of linearly disjoint field extensions.
-/

public section

open scoped TensorProduct IntermediateField

namespace TauCeti

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

/-- The two factors generate any fraction field `Q` of `F ⊗[k] K` as the constant compositum
`F · K`. -/
theorem constantCompositum_eq_top_of_isFractionRing_tensorProduct
    {k F K Q : Type*} [CommRing k] [Field F] [CommRing K] [Field Q]
    [Algebra k F] [Algebra k K] [Algebra (F ⊗[k] K) Q] [Algebra F Q] [Algebra K Q]
    [IsScalarTower F (F ⊗[k] K) Q] [IsScalarTower K (F ⊗[k] K) Q]
    [IsFractionRing (F ⊗[k] K) Q] :
    constantCompositum F K Q = ⊤ := by
  rw [constantCompositum_def]
  exact adjoin_range_right_eq_top_of_isFractionRing_tensorProduct (k := k)

section SpecifiedFractionField

variable {k F K Q : Type*} [Field k] [Field F] [Field K] [Field Q]
  [Algebra k F] [Algebra k K] [Algebra (F ⊗[k] K) Q]
  [Algebra k Q] [Algebra F Q] [Algebra K Q]
  [IsScalarTower k (F ⊗[k] K) Q] [IsScalarTower F (F ⊗[k] K) Q]
  [IsScalarTower K (F ⊗[k] K) Q] [IsScalarTower k F Q] [IsScalarTower k K Q]
  [IsFractionRing (F ⊗[k] K) Q]

/-- A fraction field of a domain tensor product is a one-variable function field
over the enlarged constants. -/
theorem IsFunctionField.of_isFractionRing_tensorProduct (hF : IsFunctionField k F) :
    IsFunctionField K Q :=
  hF.of_constantCompositum_eq_top_of_linearDisjoint
    (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k))

/-- An element of `F` transcendental over `k` remains transcendental over `K` in any fraction
field `Q` of `F ⊗[k] K`. -/
theorem _root_.Transcendental.algebraMap_of_isFractionRing_tensorProduct {x : F}
    (hx : Transcendental k x) :
    Transcendental K (algebraMap F Q x) :=
  (linearDisjoint_of_isFractionRing_tensorProduct (k := k)).transcendental_algebraMap hx

omit [IsScalarTower k (F ⊗[k] K) Q] in
include k in
/-- Separability over a simple parameter persists in any fraction field `Q` of `F ⊗[k] K`: if
`F / k(x)` is separable algebraic, then `Q / K(x)` is separable algebraic. -/
theorem isSeparable_adjoin_simple_of_isFractionRing_tensorProduct (x : F)
    [Algebra.IsSeparable k⟮x⟯ F] :
    Algebra.IsSeparable K⟮algebraMap F Q x⟯ Q := by
  have hsep := isSeparable_adjoin_image_of_constantCompositum_eq_top (k := k) (k' := K)
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k) (Q := Q))
    (S := ({x} : Set F))
  rwa [Set.image_singleton] at hsep

/-- Tensor-fraction-field extension of constants preserves the degree over a parameter.
Neither the constants nor the relative extension need be separable. -/
theorem finrank_over_adjoin_simple_eq_of_isFractionRing_tensorProduct (x : F) :
    Module.finrank K⟮algebraMap F Q x⟯ Q = Module.finrank k⟮x⟯ F :=
  finrank_over_adjoin_simple_eq_of_linearDisjoint
    (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k)) x

section RatFunc

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra (RatFunc K) Q] [IsScalarTower K (RatFunc K) Q]

omit [IsScalarTower k (F ⊗[k] K) Q] in
/-- Separability over `RatFunc k` persists in any fraction field `Q` of `F ⊗[k] K` over
`RatFunc K` when the rational variable `X` maps compatibly. -/
theorem isSeparable_ratFunc_of_isFractionRing_tensorProduct
    (hX : algebraMap F Q (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) Q RatFunc.X)
    [Algebra.IsSeparable (RatFunc k) F] :
    Algebra.IsSeparable (RatFunc K) Q :=
  isSeparable_ratFunc_of_constantCompositum_eq_top (k := k)
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k)) hX

/-- **Degree over the rational function field is preserved in any fraction field of `F ⊗[k] K`.**
When `X` acts compatibly on `F` and `Q`, we have `[Q : RatFunc K] = [F : RatFunc k]`, with no
algebraicity or separability hypothesis on `K / k` or `F / RatFunc k`. -/
theorem finrank_ratFunc_eq_of_isFractionRing_tensorProduct
    (hX : algebraMap F Q (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) Q RatFunc.X) :
    Module.finrank (RatFunc K) Q = Module.finrank (RatFunc k) F :=
  finrank_ratFunc_eq_of_linearDisjoint
    (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k)) hX

end RatFunc

end SpecifiedFractionField

section FractionRing

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (K : Type*) [Field K] [Algebra k K]

/-- If `F/k` is a geometrically reduced one-variable function field with exact constants,
then the fraction field of `F ⊗[k] K` is a one-variable function field over `K`.
The enlarged constant field may be transcendental over the original one. -/
theorem IsFunctionField.fractionRing_tensorProduct
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    [Algebra.IsGeometricallyReduced k F] :
    letI := isDomain_tensorProduct_of_isGeometricallyReduced hex K
    IsFunctionField K (FractionRing (F ⊗[k] K)) := by
  have := isDomain_tensorProduct_of_isGeometricallyReduced hex K
  exact hF.of_isFractionRing_tensorProduct

/-- Over a perfect base field `k`, exactness of `k` in a function field `F` suffices for
`FractionRing (F ⊗[k] K)` to be a one-variable function field over `K`. -/
theorem IsFunctionField.fractionRing_tensorProduct_of_perfectField [PerfectField k]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) :
    letI := isDomain_tensorProduct_of_perfectField hex K
    IsFunctionField K (FractionRing (F ⊗[k] K)) :=
  hF.fractionRing_tensorProduct K hex

/-- Over an algebraically closed base field `k`, `FractionRing (F ⊗[k] K)` is unconditionally a
one-variable function field over `K` for every function field `F/k` and field extension `K/k`. -/
theorem IsFunctionField.fractionRing_tensorProduct_of_isAlgClosed [IsAlgClosed k]
    (hF : IsFunctionField k F) :
    IsFunctionField K (FractionRing (F ⊗[k] K)) :=
  hF.of_isFractionRing_tensorProduct

end FractionRing

end TauCeti
