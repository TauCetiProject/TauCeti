/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.LinearDisjoint
public import TauCeti.FieldTheory.Separable.Regular
public import TauCeti.RingTheory.TensorProduct.FractionRing

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
scalar maps (for instance `RatFunc K` for `RatFunc k ⊗[k] K`, proved in
`TauCeti.FieldTheory.RatFunc.TensorProduct`), and conversely any linearly disjoint
compositum `F · k'` is a fraction field of `F ⊗[k] k'`
(`TauCeti.isFractionRing_tensorProduct_of_linearDisjoint`).

## Main results

* `TauCeti.constantCompositum_eq_top_of_isFractionRing_tensorProduct`: a fraction field `Q` of
  `F ⊗[k] K` equals the constant compositum `F · K`.
* `TauCeti.transcendental_algebraMap_of_isFractionRing_tensorProduct`,
  `TauCeti.isSeparable_adjoin_simple_of_isFractionRing_tensorProduct`: transcendental and
  separating parameters of `F/k` persist in `Q/K`.
* `TauCeti.IsFunctionField.of_isFractionRing_tensorProduct`,
  `TauCeti.IsFunctionField.fractionRing_tensorProduct`: preservation of the one-variable
  function-field property.
* `TauCeti.isFractionRing_tensorProduct_of_linearDisjoint`: a linearly disjoint compositum is
  a fraction field of the tensor product.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6.
* S. Lang, *Algebra*, the theory of linearly disjoint field extensions.
-/

public section

open scoped TensorProduct IntermediateField

namespace TauCeti

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

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

section Compositum

variable {k F k' F' : Type*} [Field k] [Field F] [Field k'] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k F'] [Algebra F F'] [Algebra k' F']
  [IsScalarTower k F F'] [IsScalarTower k k' F']

/-- **A linearly disjoint compositum is the fraction field of the tensor product.** -/
theorem isFractionRing_tensorProduct_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) :
    letI := (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
      (IsScalarTower.toAlgHom k k' F')).toRingHom.toAlgebra
    IsFractionRing (F ⊗[k] k') F' := by
  let g : F ⊗[k] k' →ₐ[F] F' := Algebra.TensorProduct.productLeftAlgHom
    (Algebra.ofId F F') (IsScalarTower.toAlgHom k k' F')
  let _ := (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
    (IsScalarTower.toAlgHom k k' F')).toRingHom.toAlgebra
  have hg_eq : ⇑g = algebraMap (F ⊗[k] k') F' := by
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul a b => simp [g, RingHom.algebraMap_toAlgebra]
    | add u v hu hv => simp only [map_add, hu, hv]
  have hg : Function.Injective g :=
    hg_eq.symm ▸ productMap_injective_iff_linearDisjoint.mpr H
  have : IsDomain (F ⊗[k] k') := hg.isDomain g.toRingHom
  let ψ : FractionRing (F ⊗[k] k') →ₐ[F] F' := IsFractionRing.liftAlgHom hg
  have hrange : ψ '' Set.range (algebraMap k' (FractionRing (F ⊗[k] k'))) =
      Set.range (algebraMap k' F') := by
    rw [← Set.range_comp]
    refine congrArg Set.range (funext fun c ↦ ?_)
    have hc : algebraMap k' (F ⊗[k] k') c = 1 ⊗ₜ c := rfl
    rw [Function.comp_apply,
      IsScalarTower.algebraMap_apply k' (F ⊗[k] k') (FractionRing (F ⊗[k] k')),
      IsFractionRing.coe_liftAlgHom, IsFractionRing.lift_algebraMap, hc]
    simp [g]
  have htop : ψ.fieldRange = ⊤ := by
    rw [AlgHom.fieldRange_eq_map, ← adjoin_range_right_eq_top_of_isFractionRing_tensorProduct
      (k := k) (F := F) (K := k') (Q := FractionRing (F ⊗[k] k')),
      IntermediateField.adjoin_map, hrange, ← constantCompositum_def, h]
  exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors (F ⊗[k] k'))
    (AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective ψ.toRingHom
      ⟨ψ.injective, fun y ↦ (htop ▸ IntermediateField.mem_top : y ∈ ψ.fieldRange)⟩)
      fun z ↦ (IsFractionRing.lift_algebraMap hg z).trans (congrFun hg_eq z))

end Compositum

end TauCeti
