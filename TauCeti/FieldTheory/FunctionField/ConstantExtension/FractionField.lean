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
field with exact constants, and from
`TauCeti.isDomain_tensorProduct_of_isGeometricallyReduced_right` whenever `k` is
algebraically closed. We retain the actual fraction-field carrier, rather than asserting
that the tensor product itself is a field. The results also apply to any specified
fraction field with compatible scalar maps; in particular, `RatFunc K` is a fraction
field of `RatFunc k ⊗[k] K` (`TauCeti.isFractionRing_ratFunc_tensorProduct`).

## Main results

* `TauCeti.constantCompositum_eq_top_of_isFractionRing_tensorProduct`: a fraction field `Q` of
  `F ⊗[k] K` equals the constant compositum `F · K`.
* `TauCeti.transcendental_algebraMap_of_isFractionRing_tensorProduct`,
  `TauCeti.isSeparable_adjoin_simple_of_isFractionRing_tensorProduct`: transcendental and
  separating parameters of `F/k` persist in `Q/K`.
* `TauCeti.IsFunctionField.of_isFractionRing_tensorProduct`,
  `TauCeti.IsFunctionField.fractionRing_tensorProduct`,
  `TauCeti.IsFunctionField.fractionRing_tensorProduct_of_isAlgClosed`: preservation of the
  one-variable function-field property.
* `TauCeti.isFractionRing_ratFunc_tensorProduct`, `TauCeti.constantCompositum_ratFunc_eq_top`:
  `RatFunc K` is a fraction field of `RatFunc k ⊗[k] K` and equals `(RatFunc k) · K` for any
  `k`-algebra map `RatFunc k → RatFunc K` sending `X` to `X`.
* `TauCeti.algebraMap_ratFunc_apply_eq`: two routes `RatFunc k → RatFunc K → Q` and
  `RatFunc k → F → Q` sharing the image of `X` agree on all of `RatFunc k`.

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

omit [Algebra (F ⊗[k] K) Q] [Algebra k Q] [Algebra F Q] [Algebra K Q]
  [IsScalarTower k (F ⊗[k] K) Q] [IsScalarTower F (F ⊗[k] K) Q]
  [IsScalarTower K (F ⊗[k] K) Q] [IsScalarTower k F Q] [IsScalarTower k K Q]
  [IsFractionRing (F ⊗[k] K) Q] in
/-- Over an algebraically closed field `k`, the fraction field of `F ⊗[k] K` is a one-variable
function field over `K` for every one-variable function field `F/k` and every field extension
`K/k`. -/
theorem IsFunctionField.fractionRing_tensorProduct_of_isAlgClosed (hF : IsFunctionField k F)
    [IsAlgClosed k] (K : Type*) [Field K] [Algebra k K] :
    IsFunctionField K (FractionRing (F ⊗[k] K)) :=
  hF.of_isFractionRing_tensorProduct

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
    have he : e.toRingHom (p ⊗ₜ[k] c) = (polyEquivTensor k K).symm (c ⊗ₜ[k] p) := by simp [e]
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, he,
      polyEquivTensor_symm_apply_tmul_eq_smul, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply K K[X] (RatFunc K),
      algebraMap_ratFunc_algebraMap_polynomial hX]
  have h2 : algebraMap (RatFunc k ⊗[k] K) (RatFunc K) (algebraMap k[X] (RatFunc k) p ⊗ₜ[k] c) =
      algebraMap (RatFunc k) (RatFunc K) (algebraMap k[X] (RatFunc k) p) *
        algebraMap K (RatFunc K) c := by
    have htmul : (algebraMap k[X] (RatFunc k) p ⊗ₜ[k] c : RatFunc k ⊗[k] K) =
        algebraMap (RatFunc k) (RatFunc k ⊗[k] K) (algebraMap k[X] (RatFunc k) p) *
          algebraMap K (RatFunc k ⊗[k] K) c := by
      simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.right_algebraMap_apply]
    rw [htmul, map_mul,
      ← IsScalarTower.algebraMap_apply (RatFunc k) (RatFunc k ⊗[k] K) (RatFunc K),
      ← IsScalarTower.algebraMap_apply K (RatFunc k ⊗[k] K) (RatFunc K)]
  rw [h1, h2, mul_comm]

/-- `RatFunc K` is generated as a field by the images of `RatFunc k` and `K` whenever the map
`RatFunc k → RatFunc K` sends `X` to `X`. -/
theorem constantCompositum_ratFunc_eq_top
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) :
    constantCompositum (RatFunc k) K (RatFunc K) = ⊤ := by
  let _ : Algebra (RatFunc k ⊗[k] K) (RatFunc K) :=
    (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k (RatFunc k) (RatFunc K))
      (IsScalarTower.toAlgHom k K (RatFunc K))).toRingHom.toAlgebra
  have : IsScalarTower (RatFunc k) (RatFunc k ⊗[k] K) (RatFunc K) :=
    .of_algebraMap_eq fun _ ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower K (RatFunc k ⊗[k] K) (RatFunc K) :=
    .of_algebraMap_eq fun _ ↦ by simp [RingHom.algebraMap_toAlgebra]
  have := isFractionRing_ratFunc_tensorProduct hX
  exact constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k) (K := K)

/-- Two routes `RatFunc k → RatFunc K → Q` and `RatFunc k → F → Q` into a commutative `k`-algebra
`Q` that map `RatFunc.X` compatibly agree on all of `RatFunc k`. -/
theorem algebraMap_ratFunc_apply_eq {F Q : Type*} [Field F] [CommRing Q]
    [Algebra k F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    [Algebra k Q] [Algebra K Q] [Algebra F Q] [Algebra (RatFunc K) Q]
    [IsScalarTower k K Q] [IsScalarTower k F Q] [IsScalarTower K (RatFunc K) Q]
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hX' : algebraMap F Q (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) Q RatFunc.X)
    (w : RatFunc k) :
    algebraMap (RatFunc K) Q (algebraMap (RatFunc k) (RatFunc K) w) =
      algebraMap F Q (algebraMap (RatFunc k) F w) := by
  have hhom : (algebraMap (RatFunc K) Q).comp (algebraMap (RatFunc k) (RatFunc K)) =
      (algebraMap F Q).comp (algebraMap (RatFunc k) F) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors k[X]) <|
      Polynomial.ringHom_ext (fun c ↦ ?_) ?_
    · simp only [RingHom.comp_apply, ← Polynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply k k[X] (RatFunc k),
        ← IsScalarTower.algebraMap_apply k (RatFunc k) (RatFunc K),
        ← IsScalarTower.algebraMap_apply k (RatFunc k) F]
      rw [IsScalarTower.algebraMap_apply k K (RatFunc K),
        ← IsScalarTower.algebraMap_apply K (RatFunc K) Q,
        ← IsScalarTower.algebraMap_apply k K Q, ← IsScalarTower.algebraMap_apply k F Q]
    · simp [RingHom.comp_apply, RatFunc.algebraMap_X, hX, hX']
  exact congr($hhom w)

end RatFunc

end TauCeti
