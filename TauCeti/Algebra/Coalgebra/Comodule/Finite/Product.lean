/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Preadditive
public import TauCeti.Algebra.Coalgebra.Comodule.Product

/-!
# Products of finitely generated comodules

The ambient category `ComoduleCat` has the product comodule on the cartesian product of the
underlying modules as its categorical binary product. Finite generation is preserved by binary
products of modules, so finite generation, as an object property of all comodules, is closed
under binary and finite products. Mathlib's `ObjectProperty` instances for full subcategories
then give `FGComoduleCat` binary and finite products, created by the inclusion into all
comodules, and over a commutative ring these products are biproducts. Downstream code uses
Mathlib's generic `M ⨯ N` / `M ⊞ N` API.

## Main declarations

* `TauCeti.ComoduleCat.isFG_isClosedUnderBinaryProducts`,
  `TauCeti.ComoduleCat.isFG_isClosedUnderFiniteProducts`: finite generation of comodules is
  closed under binary and finite products.
* `TauCeti.FGComoduleCat.hasBinaryBiproduct`: the ring/preadditive biproduct instance induced
  by the binary product.
* `TauCeti.FGComoduleCat.hasBinaryBiproducts`, `hasFiniteBiproducts`: aggregate
  ring/preadditive biproduct infrastructure.

## References

The products come from the direct-sum comodule in `TauCeti.Algebra.Coalgebra.Comodule.Product`.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

universe u v w

variable (R : Type u) [CommSemiring R]
variable (C : Type v) [AddCommMonoid C] [Module R C] [Coalgebra R C]

namespace ComoduleCat

/-- Finitely generated comodules are closed under binary products: the categorical product is
isomorphic to the concrete product comodule on the product of the underlying modules. -/
instance isFG_isClosedUnderBinaryProducts :
    (isFG.{u, v, w} R C).IsClosedUnderBinaryProducts := by
  refine ObjectProperty.IsClosedUnderLimitsOfShape.mk' ?_
  rintro _ ⟨F, hF⟩
  let M := F.obj ⟨.left⟩
  let N := F.obj ⟨.right⟩
  have : Module.Finite R M := (isFG_iff R C M).mp (hF _)
  have : Module.Finite R N := (isFG_iff R C N).mp (hF _)
  have hprod : isFG R C (binaryProductLimitCone M N).cone.pt := by
    rw [binaryProductLimitCone_cone_pt]
    exact (isFG_iff R C (prod R C M N)).mpr (Module.Finite.prod : Module.Finite R (M × N))
  exact (isFG R C).prop_of_iso
    ((limit.isoLimitCone (binaryProductLimitCone M N)).symm ≪≫
      (HasLimit.isoOfNatIso (diagramIsoPair F)).symm) hprod

/-- Finitely generated comodules are closed under finite products. -/
instance isFG_isClosedUnderFiniteProducts :
    (isFG.{u, v, w} R C).IsClosedUnderFiniteProducts :=
  .mk'

end ComoduleCat

namespace FGComoduleCat

section Ring

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The preadditive binary product is also a binary biproduct. -/
instance hasBinaryBiproduct (M N : FGComoduleCat.{u, v, w} R C) :
    Limits.HasBinaryBiproduct M N :=
  Limits.HasBinaryBiproduct.of_hasBinaryProduct M N

/-- Finitely generated comodules over a commutative ring have binary biproducts. -/
instance hasBinaryBiproducts : Limits.HasBinaryBiproducts (FGComoduleCat.{u, v, w} R C) :=
  Limits.HasBinaryBiproducts.of_hasBinaryProducts

/-- Finitely generated comodules over a commutative ring have finite biproducts. -/
instance hasFiniteBiproducts : Limits.HasFiniteBiproducts (FGComoduleCat.{u, v, w} R C) :=
  Limits.HasFiniteBiproducts.of_hasFiniteProducts

end Ring

end FGComoduleCat

end TauCeti
