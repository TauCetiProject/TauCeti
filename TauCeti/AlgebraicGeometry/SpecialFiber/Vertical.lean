/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Excision
public import TauCeti.AlgebraicGeometry.SpecialFiber.Components
import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Vertical Cartier homomorphism on special-fibre components

Let `R` be a local ring of dimension at most one and `toBase : X ⟶ Spec R` a Noetherian locally
factorial integral scheme over `R` whose generic point lies outside the special fibre. The special
fibre has finitely many irreducible components `Cᵢ = closure {ηᵢ}` indexed by the codimension-one
points `ηᵢ` over the closed point (`AlgebraicGeometry.Scheme.Hom.finite_setOf_base_eq_closedPoint`).

By converting component tuples to finitely supported Weil divisors via
`Finsupp.linearEquivFunOnFinite` and `Finsupp.lmapDomain`, and composing with
`TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.weilToLineBundleClassHom`, this file defines the
`ℤ`-linear vertical Cartier homomorphism
`AlgebraicGeometry.Scheme.Hom.verticalLineBundleLinear` from `(Component → ℤ)` to
`Additive (LineBundleClass X)` sending `v ↦ ∏ᵢ [𝒪_X(Cᵢ)] ^ vᵢ`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.verticalLineBundleLinear`: the `ℤ`-linear vertical Cartier
  homomorphism `v ↦ ∏ᵢ [𝒪_X(Cᵢ)] ^ vᵢ` on special-fibre component tuples.
* `AlgebraicGeometry.Scheme.Hom.toMul_verticalLineBundleLinear_apply`: multiplicative expansion as
  a product of prime-divisor line-bundle powers.
* `AlgebraicGeometry.Scheme.Hom.verticalLineBundleLinear_single`: evaluation on a basis vector
  `Pi.single i 1`.

## References

* [The Stacks Project, Section 55.9](https://stacks.math.columbia.edu/tag/0C5Y), vertical divisors
  on a regular model.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 9.1.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing Order
open TauCeti TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData (isEffectiveCartier_vanishingIdeal_closure_singleton)

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {R : Type u} [CommRing R] [IsLocalRing R] [Ring.DimensionLEOne R]
  {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) [IsIntegral X] [IsNoetherian X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

/-- **Vertical Cartier homomorphism**, sending a tuple `v` on the special-fibre components to
`∏ᵢ [𝒪_X(Cᵢ)] ^ vᵢ` in `Additive (LineBundleClass X)`. -/
def verticalLineBundleLinear (hη : toBase (genericPoint X) ≠ closedPoint R) :
    ((toBase.finite_setOf_base_eq_closedPoint
        (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset → ℤ) →ₗ[ℤ]
      Additive (LineBundleClass X) :=
  (Scheme.CartierDivisor.weilToLineBundleClassHom X).toIntLinearMap ∘ₗ
    Finsupp.lmapDomain ℤ ℤ Subtype.val ∘ₗ
    (Finsupp.linearEquivFunOnFinite ℤ ℤ _).symm.toLinearMap

/-- Multiplicative expansion of `verticalLineBundleLinear v` as `∏ᵢ [𝒪_X(Cᵢ)] ^ vᵢ`. -/
@[simp]
lemma toMul_verticalLineBundleLinear_apply (hη : toBase (genericPoint X) ≠ closedPoint R)
    (v : (toBase.finite_setOf_base_eq_closedPoint
      (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset → ℤ) :
    (toBase.verticalLineBundleLinear hη v).toMul =
      ∏ i : (toBase.finite_setOf_base_eq_closedPoint
          (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset,
        (LineBundleClass.mk (isEffectiveCartier_vanishingIdeal_closure_singleton
          i.val.property).toInvertibleSheaf)⁻¹ ^ v i := by
  rw [verticalLineBundleLinear, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, AddMonoidHom.coe_toIntLinearMap, Finsupp.lmapDomain_apply,
    LineBundleClass.toMul_weilToLineBundleClassHom,
    Finsupp.prod_mapDomain_index_inj Subtype.val_injective,
    Finsupp.prod_of_support_subset _ (Finset.subset_univ _)]
  · simp [LineBundleClass.primeDivisorClass_def]
  · simp

/-- Evaluating `verticalLineBundleLinear` at `Pi.single i 1` yields `[𝒪_X(Cᵢ)]`. -/
@[simp]
lemma verticalLineBundleLinear_single (hη : toBase (genericPoint X) ≠ closedPoint R)
    [DecidableEq (toBase.finite_setOf_base_eq_closedPoint
      (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset]
    (i : (toBase.finite_setOf_base_eq_closedPoint
      (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset) :
    toBase.verticalLineBundleLinear hη (Pi.single i 1) =
      Additive.ofMul (LineBundleClass.mk
        (isEffectiveCartier_vanishingIdeal_closure_singleton
          i.val.property).toInvertibleSheaf)⁻¹ := by
  rw [verticalLineBundleLinear, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, Finsupp.linearEquivFunOnFinite_symm_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, AddMonoidHom.coe_toIntLinearMap,
    Scheme.CartierDivisor.weilToLineBundleClassHom_single, one_zsmul]

end AlgebraicGeometry.Scheme.Hom

end
