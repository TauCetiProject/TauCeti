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
function field, it is therefore a one-variable function field over `K` too, a
transcendental (or separating) parameter `x` of `F/k` remains transcendental (or
separating) over `K`, and `[Frac(F ⊗[k] K) : K(x)] = [F : k(x)]`.
The extension `K/k` need not be algebraic.

The domain hypothesis is available from
`TauCeti.isDomain_tensorProduct_of_isGeometricallyReduced` for a geometrically reduced
field with exact constants (geometric reducedness is automatic when `k` is perfect), and
automatically from the instance `TauCeti.isDomain_tensorProduct_of_isAlgClosed` whenever `k` is
algebraically closed. Regularity — both exactness of `K` and geometric reducedness over `K` —
persists in any fraction field of `F ⊗[k] K`
(`TauCeti.isIntegrallyClosedIn_right_of_isFractionRing_tensorProduct` and
`TauCeti.isGeometricallyReduced_of_isFractionRing_tensorProduct`). We retain
the actual fraction-field carrier, rather than asserting that the tensor product itself
is a field. The results also apply to any specified fraction field with compatible
scalar maps (for instance `RatFunc K` for `RatFunc k ⊗[k] K`, proved in
`TauCeti.FieldTheory.RatFunc.TensorProduct`); no `k`-algebra structure on the fraction field needs
to be supplied. Conversely any linearly disjoint compositum `F · k'` is a fraction field of
`F ⊗[k] k'` (`TauCeti.isFractionRing_tensorProduct_of_linearDisjoint`).

## Main results

* `TauCeti.constantCompositum_eq_top_of_isFractionRing_tensorProduct`,
  `TauCeti.IsFunctionField.of_isFractionRing_tensorProduct`,
  `TauCeti.transcendental_algebraMap_of_isFractionRing_tensorProduct`,
  `TauCeti.adjoin_image_eq_top_of_isFractionRing_tensorProduct`,
  `TauCeti.isSeparable_adjoin_image_of_isFractionRing_tensorProduct`,
  `TauCeti.isSeparable_adjoin_simple_of_isFractionRing_tensorProduct`,
  `TauCeti.finrank_over_adjoin_simple_eq_of_isFractionRing_tensorProduct`,
  `TauCeti.isSeparable_ratFunc_of_isFractionRing_tensorProduct`, and
  `TauCeti.finrank_ratFunc_eq_of_isFractionRing_tensorProduct`: compositum generation,
  function-field structure, generators, transcendental and separating parameters, and degrees over
  `k(x)` and `RatFunc k` persist in any fraction field of `F ⊗[k] K`.
* `TauCeti.IsFunctionField.fractionRing_tensorProduct` and
  `TauCeti.IsFunctionField.fractionRing_tensorProduct_of_isAlgClosed`: `FractionRing (F ⊗[k] K)` is
  a one-variable function field over `K` when `F/k` is regular (including over a perfect base field
  with exact constants) or unconditionally over an algebraically closed base field.
* `TauCeti.isFractionRing_tensorProduct_of_linearDisjoint`: a linearly disjoint compositum is a
  fraction field of the tensor product.

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

namespace ConstantExtension.Internal

/-- Internal helper shared by `ConstantExtension.FractionField` and
`ConstantExtension.Parameter`: the canonical `k`-algebra structure on an `(F ⊗[k] K)`-algebra `Q`,
induced through `k → F ⊗[k] K → Q`. -/
@[instance_reducible]
noncomputable def baseAlgebra {k F K Q : Type*} [CommSemiring k] [CommSemiring F]
    [CommSemiring K] [CommSemiring Q] [Algebra k F] [Algebra k K] [Algebra (F ⊗[k] K) Q] :
    Algebra k Q :=
  ((algebraMap (F ⊗[k] K) Q).comp (algebraMap k (F ⊗[k] K))).toAlgebra

/-- Internal helper shared by `ConstantExtension.FractionField` and
`ConstantExtension.Parameter`: the induced `k`-algebra structure `baseAlgebra` makes both
`k → F → Q` and `k → K → Q` scalar towers. -/
theorem baseAlgebra_isScalarTowers {k F K Q : Type*} [CommSemiring k] [CommSemiring F]
    [CommSemiring K] [CommSemiring Q] [Algebra k F] [Algebra k K] [Algebra (F ⊗[k] K) Q]
    [Algebra F Q] [Algebra K Q] [IsScalarTower F (F ⊗[k] K) Q] [IsScalarTower K (F ⊗[k] K) Q] :
    letI := baseAlgebra (k := k) (F := F) (K := K) (Q := Q)
    IsScalarTower k F Q ∧ IsScalarTower k K Q :=
  letI := baseAlgebra (k := k) (F := F) (K := K) (Q := Q)
  ⟨.of_algebraMap_eq fun c ↦ by
      rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
        IsScalarTower.algebraMap_apply k F (F ⊗[k] K),
        ← IsScalarTower.algebraMap_apply F (F ⊗[k] K) Q],
    .of_algebraMap_eq fun c ↦ by
      rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
        IsScalarTower.algebraMap_apply k K (F ⊗[k] K),
        ← IsScalarTower.algebraMap_apply K (F ⊗[k] K) Q]⟩

end ConstantExtension.Internal

section SpecifiedFractionField

variable {k F K Q : Type*} [Field k] [Field F] [Field K] [Field Q]
  [Algebra k F] [Algebra k K] [Algebra (F ⊗[k] K) Q]
  [Algebra F Q] [Algebra K Q]
  [IsScalarTower F (F ⊗[k] K) Q] [IsScalarTower K (F ⊗[k] K) Q]
  [IsFractionRing (F ⊗[k] K) Q]

/-- A fraction field of a domain tensor product is a one-variable function field
over the enlarged constants. -/
theorem IsFunctionField.of_isFractionRing_tensorProduct (hF : IsFunctionField k F) :
    IsFunctionField K Q := by
  let _ := ConstantExtension.Internal.baseAlgebra (k := k) (F := F) (K := K) (Q := Q)
  obtain ⟨_, _⟩ := ConstantExtension.Internal.baseAlgebra_isScalarTowers
    (k := k) (F := F) (K := K) (Q := Q)
  exact hF.of_constantCompositum_eq_top_of_linearDisjoint
    (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k))

/-- An element transcendental over `k` in `F` remains transcendental over `K` in any specified
fraction field of `F ⊗[k] K`. -/
theorem transcendental_algebraMap_of_isFractionRing_tensorProduct {x : F}
    (hx : Transcendental k x) : Transcendental K (algebraMap F Q x) := by
  let _ := ConstantExtension.Internal.baseAlgebra (k := k) (F := F) (K := K) (Q := Q)
  obtain ⟨_, _⟩ := ConstantExtension.Internal.baseAlgebra_isScalarTowers
    (k := k) (F := F) (K := K) (Q := Q)
  exact (linearDisjoint_of_isFractionRing_tensorProduct (k := k)).transcendental_algebraMap hx

/-- Generators of `F` over `k` map to generators of `Q` over `K` in any specified fraction field
`Q` of `F ⊗[k] K`. -/
theorem adjoin_image_eq_top_of_isFractionRing_tensorProduct {S : Set F}
    (hS : IntermediateField.adjoin k S = ⊤) :
    IntermediateField.adjoin K (algebraMap F Q '' S) = ⊤ := by
  let _ := ConstantExtension.Internal.baseAlgebra (k := k) (F := F) (K := K) (Q := Q)
  obtain ⟨_, _⟩ := ConstantExtension.Internal.baseAlgebra_isScalarTowers
    (k := k) (F := F) (K := K) (Q := Q)
  exact adjoin_image_eq_top_of_constantCompositum_eq_top hS
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k))

/-- If `F` is separable over `k(S)`, then a fraction field `Q` of `F ⊗[k] K` is separable over
`K(S)`. -/
theorem isSeparable_adjoin_image_of_isFractionRing_tensorProduct {S : Set F}
    [Algebra.IsSeparable (IntermediateField.adjoin k S) F] :
    Algebra.IsSeparable (IntermediateField.adjoin K (algebraMap F Q '' S)) Q := by
  let _ := ConstantExtension.Internal.baseAlgebra (k := k) (F := F) (K := K) (Q := Q)
  obtain ⟨_, _⟩ := ConstantExtension.Internal.baseAlgebra_isScalarTowers
    (k := k) (F := F) (K := K) (Q := Q)
  exact isSeparable_adjoin_image_of_constantCompositum_eq_top (k := k)
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k))

/-- If `F` is separable over `k(x)`, then a fraction field `Q` of `F ⊗[k] K` is separable over
`K(x)`. In particular, a separating parameter of `F/k` remains separating in `Q/K` for any
(possibly transcendental) field extension `K/k`. -/
theorem isSeparable_adjoin_simple_of_isFractionRing_tensorProduct (x : F)
    [Algebra.IsSeparable k⟮x⟯ F] :
    Algebra.IsSeparable K⟮algebraMap F Q x⟯ Q := by
  have hsep := isSeparable_adjoin_image_of_isFractionRing_tensorProduct (k := k)
    (K := K) (Q := Q) (S := {x})
  rwa [Set.image_singleton] at hsep

/-- Tensor-fraction-field extension of constants preserves the degree over a parameter.
Neither the constants nor the relative extension need be separable. -/
theorem finrank_over_adjoin_simple_eq_of_isFractionRing_tensorProduct (x : F) :
    Module.finrank K⟮algebraMap F Q x⟯ Q = Module.finrank k⟮x⟯ F := by
  let _ := ConstantExtension.Internal.baseAlgebra (k := k) (F := F) (K := K) (Q := Q)
  obtain ⟨_, _⟩ := ConstantExtension.Internal.baseAlgebra_isScalarTowers
    (k := k) (F := F) (K := K) (Q := Q)
  exact finrank_over_adjoin_simple_eq_of_linearDisjoint
    (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k)) x

section RatFunc

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra (RatFunc K) Q] [IsScalarTower K (RatFunc K) Q]

/-- Separability over `RatFunc k` persists in any fraction field `Q` of `F ⊗[k] K` over
`RatFunc K` when the rational variable `X` maps compatibly. -/
theorem isSeparable_ratFunc_of_isFractionRing_tensorProduct
    (hX : algebraMap F Q (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) Q RatFunc.X)
    [Algebra.IsSeparable (RatFunc k) F] :
    Algebra.IsSeparable (RatFunc K) Q := by
  let _ := ConstantExtension.Internal.baseAlgebra (k := k) (F := F) (K := K) (Q := Q)
  obtain ⟨_, _⟩ := ConstantExtension.Internal.baseAlgebra_isScalarTowers
    (k := k) (F := F) (K := K) (Q := Q)
  exact isSeparable_ratFunc_of_constantCompositum_eq_top (k := k)
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k)) hX

/-- **Degree over the rational function field is preserved in any fraction field of `F ⊗[k] K`.**
When `X` acts compatibly on `F` and `Q`, we have `[Q : RatFunc K] = [F : RatFunc k]`, with no
algebraicity or separability hypothesis on `K / k` or `F / RatFunc k`. -/
theorem finrank_ratFunc_eq_of_isFractionRing_tensorProduct
    (hX : algebraMap F Q (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) Q RatFunc.X) :
    Module.finrank (RatFunc K) Q = Module.finrank (RatFunc k) F := by
  let _ := ConstantExtension.Internal.baseAlgebra (k := k) (F := F) (K := K) (Q := Q)
  obtain ⟨_, _⟩ := ConstantExtension.Internal.baseAlgebra_isScalarTowers
    (k := k) (F := F) (K := K) (Q := Q)
  exact finrank_ratFunc_eq_of_linearDisjoint
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

/-- Over an algebraically closed base field `k`, `FractionRing (F ⊗[k] K)` is unconditionally a
one-variable function field over `K` for every function field `F/k` and field extension `K/k`. -/
theorem IsFunctionField.fractionRing_tensorProduct_of_isAlgClosed [IsAlgClosed k]
    (hF : IsFunctionField k F) :
    IsFunctionField K (FractionRing (F ⊗[k] K)) :=
  hF.of_isFractionRing_tensorProduct

end FractionRing

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
