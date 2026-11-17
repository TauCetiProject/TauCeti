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
The extension `K/k` need not be algebraic.

The domain hypothesis is available from
`TauCeti.isDomain_tensorProduct_of_separating` for a separably generated field with
exact constants. We retain the actual fraction-field carrier, rather than asserting
that the tensor product itself is a field. The results also apply to any specified
fraction field with compatible scalar maps, and conversely any linearly disjoint
compositum `F · k'` is a fraction field of `F ⊗[k] k'`
(`TauCeti.isFractionRing_tensorProduct_of_linearDisjoint`).

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
