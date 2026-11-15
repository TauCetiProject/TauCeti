/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GradedCochainComplex
public import TauCeti.CategoryTheory.AInfinity.Basic

/-!
# The Hom complexes of an `A∞` category

An `A∞` category `𝒞` on a graded linear quiver `C` over a commutative ring `R` has Hom complexes:
the morphisms `X ⟶ Y` of degree `n` form the degree-`n` term of
`TauCeti.AInfinityCategory.homComplex 𝒞 X Y`, and the differential is `m₁`.  No unit and no
vanishing of the higher operations is needed.

## Main definitions

* `TauCeti.AInfinityCategory.homComplex`: the Hom complex of an `A∞` category, with differential
  `m₁`.
* `TauCeti.AInfinityCategory.homComplexXEquiv`: its degree-`n` term is the module of morphisms of
  degree `n`.

## Main results

* `TauCeti.AInfinityCategory.homComplexXEquiv_d`: the differential of the Hom complex is `m₁`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 7.1.
-/

public section

namespace TauCeti

universe u v w

open GradedLinearQuiver

namespace AInfinityCategory

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]
  (𝒞 : AInfinityCategory R C)

/-- The **Hom complex** from `X` to `Y` of an `A∞` category: its degree-`n` term is the module of
morphisms `X ⟶ Y` of degree `n`, and its differential is `m₁`. -/
noncomputable def homComplex (X Y : C) : CochainComplex (ModuleCat.{v} R) ℤ :=
  gradedCochainComplex (grading (R := R) X Y).piece (𝒞.homDifferential X Y)
    (LinearMap.isHomogeneous_def.mpr fun _ _ hf ↦ 𝒞.homDifferential_mem_piece hf)
    fun _ f ↦ 𝒞.homDifferential_homDifferential X Y f

/-- The degree-`n` term of the Hom complex is the module of morphisms of degree `n`. -/
noncomputable def homComplexXEquiv (X Y : C) (n : ℤ) :
    (𝒞.homComplex X Y).X n ≃ₗ[R] grHom R X Y n :=
  gradedCochainComplexXEquiv n

/-- The differential of the Hom complex is `m₁`. -/
@[simp]
theorem homComplexXEquiv_d (X Y : C) (n : ℤ) (f : (𝒞.homComplex X Y).X n) :
    (𝒞.homComplexXEquiv X Y (n + 1) (((𝒞.homComplex X Y).d n (n + 1)).hom f) :
        homModule (R := R) X Y) =
      𝒞.homDifferential X Y (𝒞.homComplexXEquiv X Y n f) :=
  gradedCochainComplexXEquiv_d n f

end AInfinityCategory

end TauCeti
