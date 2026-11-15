/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.LinearDisjoint
public import TauCeti.FieldTheory.Separable.Regular
public import TauCeti.RingTheory.TensorProduct.FractionRing
import Mathlib.RingTheory.PolynomialAlgebra
import TauCeti.FieldTheory.RatFunc.Map

/-!
# Constant extension through the fraction field of a tensor product

Suppose `F ⊗[k] K` is a domain. Its fraction field, with the scalar maps from both
factors, is the linearly disjoint compositum `F · K`. If `F/k` is a one-variable
function field, it is therefore a one-variable function field over `K` too, and
`[Frac(F ⊗[k] K) : K(x)] = [F : k(x)]` for every transcendental parameter `x`.
Transcendental and separating parameters of `F/k` remain transcendental and separating
in `Frac(F ⊗[k] K)` over `K`. The extension `K/k` need not be algebraic.

The domain hypothesis is available from
`TauCeti.isDomain_tensorProduct_of_isGeometricallyReduced` for a geometrically reduced
field with exact constants, and automatically from the instance
`TauCeti.isDomain_tensorProduct_of_isAlgClosed` whenever `k` is algebraically closed. We
retain the actual fraction-field carrier, rather than asserting that the tensor product
itself is a field. The results also apply to any specified fraction field with compatible
scalar maps; in particular, `RatFunc K` is a fraction field of `RatFunc k ⊗[k] K`
(`TauCeti.isFractionRing_ratFunc_tensorProduct`,
`TauCeti.isFractionRing_ratFuncTensorProductAlgebra`).

## Main results

* `TauCeti.constantCompositum_eq_top_of_isFractionRing_tensorProduct`: a fraction field `Q` of
  `F ⊗[k] K` equals the constant compositum `F · K`.
* `TauCeti.transcendental_algebraMap_of_isFractionRing_tensorProduct`,
  `TauCeti.isSeparable_adjoin_simple_of_isFractionRing_tensorProduct`: transcendental and
  separating parameters of `F/k` persist in `Q/K`.
* `TauCeti.IsFunctionField.of_isFractionRing_tensorProduct`,
  `TauCeti.IsFunctionField.fractionRing_tensorProduct`: preservation of the one-variable
  function-field property.
* `TauCeti.isFractionRing_ratFunc_tensorProduct`, `TauCeti.ratFuncTensorProductAlgebra`,
  `TauCeti.isFractionRing_ratFuncTensorProductAlgebra`: `RatFunc K` is a fraction field of
  `RatFunc k ⊗[k] K` for any `k`-algebra map `RatFunc k → RatFunc K` sending `X` to `X`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6.
* S. Lang, *Algebra*, the theory of linearly disjoint field extensions.
-/

public section

open scoped TensorProduct IntermediateField

namespace TauCeti

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

section General

variable {k F K Q : Type*} [Field k] [Field F] [Field K] [Field Q]
  [Algebra k F] [Algebra k K] [Algebra (F ⊗[k] K) Q]
  [Algebra k Q] [Algebra F Q] [Algebra K Q]
  [IsScalarTower k (F ⊗[k] K) Q] [IsScalarTower F (F ⊗[k] K) Q]
  [IsScalarTower K (F ⊗[k] K) Q] [IsScalarTower k F Q] [IsScalarTower k K Q]
  [IsFractionRing (F ⊗[k] K) Q]

omit [Algebra k Q] [IsScalarTower k (F ⊗[k] K) Q] [IsScalarTower k F Q] [IsScalarTower k K Q] in
include k in
/-- A specified fraction field of `F ⊗[k] K` is the constant compositum `F · K`. -/
theorem constantCompositum_eq_top_of_isFractionRing_tensorProduct :
    constantCompositum F K Q = ⊤ := by
  rw [constantCompositum_def]
  exact adjoin_range_right_eq_top_of_isFractionRing_tensorProduct (k := k)

/-- An element transcendental over `k` in `F` remains transcendental over `K` in any specified
fraction field of `F ⊗[k] K`. -/
theorem transcendental_algebraMap_of_isFractionRing_tensorProduct {x : F}
    (hx : Transcendental k x) : Transcendental K (algebraMap F Q x) :=
  (linearDisjoint_of_isFractionRing_tensorProduct (k := k)).transcendental_algebraMap hx

omit [IsScalarTower k (F ⊗[k] K) Q] in
/-- Generators of `F` over `k` map to generators of `Q` over `K` in any specified fraction field
`Q` of `F ⊗[k] K`. -/
theorem adjoin_image_eq_top_of_isFractionRing_tensorProduct {S : Set F}
    (hS : IntermediateField.adjoin k S = ⊤) :
    IntermediateField.adjoin K (algebraMap F Q '' S) = ⊤ :=
  adjoin_image_eq_top_of_constantCompositum_eq_top hS
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k))

omit [IsScalarTower k (F ⊗[k] K) Q] in
/-- If `F` is separable over `k(S)`, then a fraction field `Q` of `F ⊗[k] K` is separable over
`K(S)`. -/
theorem isSeparable_adjoin_image_of_isFractionRing_tensorProduct {S : Set F}
    [Algebra.IsSeparable (IntermediateField.adjoin k S) F] :
    Algebra.IsSeparable (IntermediateField.adjoin K (algebraMap F Q '' S)) Q :=
  isSeparable_adjoin_image_of_constantCompositum_eq_top (k := k)
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k))

omit [IsScalarTower k (F ⊗[k] K) Q] in
/-- If `F` is separable over `k(x)`, then a fraction field `Q` of `F ⊗[k] K` is separable over
`K(x)`. In particular, a separating parameter of `F/k` remains separating in `Q/K` for any
(possibly transcendental) field extension `K/k`. -/
theorem isSeparable_adjoin_simple_of_isFractionRing_tensorProduct (x : F)
    [Algebra.IsSeparable k⟮x⟯ F] :
    Algebra.IsSeparable K⟮algebraMap F Q x⟯ Q := by
  have hsep := isSeparable_adjoin_image_of_isFractionRing_tensorProduct (k := k)
    (K := K) (Q := Q) (S := {x})
  rwa [Set.image_singleton] at hsep

/-- A fraction field of a domain tensor product is a one-variable function field
over the enlarged constants. -/
theorem IsFunctionField.of_isFractionRing_tensorProduct (hF : IsFunctionField k F) :
    IsFunctionField K Q :=
  hF.of_constantCompositum_eq_top_of_linearDisjoint
    (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k))

/-- Tensor-fraction-field extension of constants preserves the degree over a parameter.
Neither the constants nor the relative extension need be separable. -/
theorem finrank_over_adjoin_simple_eq_of_isFractionRing_tensorProduct (x : F)
    [FiniteDimensional k⟮x⟯ F] :
    Module.finrank K⟮algebraMap F Q x⟯ Q = Module.finrank k⟮x⟯ F :=
  finrank_over_adjoin_simple_eq_of_linearDisjoint
    (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k)) x

/-- If `F/k` is a geometrically reduced one-variable function field with exact constants,
then the fraction field of `F ⊗[k] K` is a one-variable function field over `K`.
The enlarged constant field may be transcendental over the original one. -/
theorem IsFunctionField.fractionRing_tensorProduct (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F] :
    letI := isDomain_tensorProduct_of_isGeometricallyReduced hex K
    IsFunctionField K (FractionRing (F ⊗[k] K)) := by
  have := isDomain_tensorProduct_of_isGeometricallyReduced hex K
  exact hF.of_isFractionRing_tensorProduct

end General

section RatFunc

open scoped Polynomial

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
  [Algebra (RatFunc k) (RatFunc K)] [IsScalarTower k (RatFunc k) (RatFunc K)]

/-- **`RatFunc K` is a fraction field of `RatFunc k ⊗[k] K`**, for any `k`-algebra map
`RatFunc k → RatFunc K` sending `X` to `X` and any compatible `RatFunc k ⊗[k] K`-algebra
structure on `RatFunc K`. Here `K/k` may be transcendental. -/
theorem isFractionRing_ratFunc_tensorProduct
    [Algebra (RatFunc k ⊗[k] K) (RatFunc K)]
    [IsScalarTower (RatFunc k) (RatFunc k ⊗[k] K) (RatFunc K)]
    [IsScalarTower K (RatFunc k ⊗[k] K) (RatFunc K)]
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) :
    IsFractionRing (RatFunc k ⊗[k] K) (RatFunc K) := by
  -- Identify `k[X] ⊗[k] K` with the polynomial ring `K[X]`, whose fraction field is `RatFunc K`.
  let e : k[X] ⊗[k] K ≃ₐ[k] K[X] :=
    (Algebra.TensorProduct.comm k k[X] K).trans (polyEquivTensor k K).symm
  have : IsDomain (k[X] ⊗[k] K) := e.toMulEquiv.isDomain
  let _ : Algebra (k[X] ⊗[k] K) (RatFunc K) :=
    ((algebraMap K[X] (RatFunc K)).comp e.toRingHom).toAlgebra
  have : IsFractionRing (k[X] ⊗[k] K) (RatFunc K) :=
    _root_.IsFractionRing.of_ringEquiv_left e.toRingEquiv fun _ ↦ rfl
  refine isFractionRing_tensorProduct_of_isFractionRing_base_tensorProduct
    (k := k) (A := k[X]) (F := RatFunc k) (K := K) (Q := RatFunc K) fun p c ↦ ?_
  have h1 : algebraMap (k[X] ⊗[k] K) (RatFunc K) (p ⊗ₜ[k] c) =
      algebraMap K (RatFunc K) c *
        algebraMap (RatFunc k) (RatFunc K) (algebraMap k[X] (RatFunc k) p) := by
    simp [e, RingHom.algebraMap_toAlgebra, polyEquivTensor_symm_apply_tmul_eq_smul,
      Algebra.smul_def, algebraMap_ratFunc_algebraMap_polynomial hX]
  have h2 : algebraMap (RatFunc k ⊗[k] K) (RatFunc K) (algebraMap k[X] (RatFunc k) p ⊗ₜ[k] c) =
      algebraMap (RatFunc k) (RatFunc K) (algebraMap k[X] (RatFunc k) p) *
        algebraMap K (RatFunc K) c := by
    rw [IsScalarTower.algebraMap_apply (RatFunc k) (RatFunc k ⊗[k] K) (RatFunc K),
      IsScalarTower.algebraMap_apply K (RatFunc k ⊗[k] K) (RatFunc K), ← map_mul]
    simp [Algebra.TensorProduct.right_algebraMap_apply]
  rw [h1, h2, mul_comm]

/-- The `RatFunc k ⊗[k] K`-algebra structure on `RatFunc K` given by multiplying the scalar maps
from `RatFunc k` and `K`. -/
@[instance_reducible]
noncomputable def ratFuncTensorProductAlgebra : Algebra (RatFunc k ⊗[k] K) (RatFunc K) :=
  (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k (RatFunc k) (RatFunc K))
    (IsScalarTower.toAlgHom k K (RatFunc K))).toRingHom.toAlgebra

/-- Under `TauCeti.ratFuncTensorProductAlgebra`, `algebraMap` sends a pure tensor `f ⊗ₜ c` to the
product of the two scalar images in `RatFunc K`. -/
theorem algebraMap_ratFuncTensorProductAlgebra_tmul (f : RatFunc k) (c : K) :
    letI := ratFuncTensorProductAlgebra (k := k) (K := K)
    algebraMap (RatFunc k ⊗[k] K) (RatFunc K) (f ⊗ₜ[k] c) =
      algebraMap (RatFunc k) (RatFunc K) f * algebraMap K (RatFunc K) c := by
  let _ := ratFuncTensorProductAlgebra (k := k) (K := K)
  have h : algebraMap (RatFunc k ⊗[k] K) (RatFunc K) =
      (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k (RatFunc k) (RatFunc K))
        (IsScalarTower.toAlgHom k K (RatFunc K))).toRingHom := rfl
  simp [h]

/-- Left scalar tower for `TauCeti.ratFuncTensorProductAlgebra`. -/
theorem isScalarTower_ratFunc_ratFuncTensorProductAlgebra :
    letI := ratFuncTensorProductAlgebra (k := k) (K := K)
    IsScalarTower (RatFunc k) (RatFunc k ⊗[k] K) (RatFunc K) := by
  let _ := ratFuncTensorProductAlgebra (k := k) (K := K)
  exact .of_algebraMap_eq fun _ ↦ by simp [algebraMap_ratFuncTensorProductAlgebra_tmul]

/-- Right scalar tower for `TauCeti.ratFuncTensorProductAlgebra`. -/
theorem isScalarTower_right_ratFuncTensorProductAlgebra :
    letI := ratFuncTensorProductAlgebra (k := k) (K := K)
    IsScalarTower K (RatFunc k ⊗[k] K) (RatFunc K) := by
  let _ := ratFuncTensorProductAlgebra (k := k) (K := K)
  exact .of_algebraMap_eq fun _ ↦ by
    simp [Algebra.TensorProduct.right_algebraMap_apply,
      algebraMap_ratFuncTensorProductAlgebra_tmul]

/-- **`RatFunc K` is a fraction field of `RatFunc k ⊗[k] K`** under
`TauCeti.ratFuncTensorProductAlgebra` whenever `algebraMap (RatFunc k) (RatFunc K)` fixes `X`. -/
theorem isFractionRing_ratFuncTensorProductAlgebra
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) :
    letI := ratFuncTensorProductAlgebra (k := k) (K := K)
    IsFractionRing (RatFunc k ⊗[k] K) (RatFunc K) := by
  let _ := ratFuncTensorProductAlgebra (k := k) (K := K)
  have := isScalarTower_ratFunc_ratFuncTensorProductAlgebra (k := k) (K := K)
  have := isScalarTower_right_ratFuncTensorProductAlgebra (k := k) (K := K)
  exact isFractionRing_ratFunc_tensorProduct hX

end RatFunc

end TauCeti
