/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import TauCeti.CategoryTheory.Limits.Lattice

/-!
# Inverse images of finite intersections of opens

Taking inverse images of opens under a morphism of schemes commutes with finite intersections,
whether written as `Finset.inf` or as finite products in the category of opens. Since inverse
images of affine opens under an affine morphism are affine
(`AlgebraicGeometry.IsAffineOpen.preimage`), a family of opens whose nonempty finite intersections
are affine, such as the covers used to compute cohomology by Čech complexes, pulls back along an
affine morphism to a family with the same property.

## Main results

* `AlgebraicGeometry.Scheme.Hom.preimage_finset_inf`: `f⁻¹` commutes with `Finset.inf`.
* `AlgebraicGeometry.Scheme.Hom.preimage_finite_product`: `f⁻¹` commutes with finite products
  of opens.
* `AlgebraicGeometry.Scheme.Hom.nonempty_pi_preimage_hom`: the comparison morphism from the product
  of the inverse images to the inverse image of the product, the hypothesis of
  `TauCeti.CategoryTheory.cechComplexCompIso` for `f⁻¹`.
* `AlgebraicGeometry.Scheme.Hom.isAffineOpen_finset_inf_preimage`: along an affine morphism, the
  inverse images of a family of opens with affine nonempty finite intersections again have affine
  nonempty finite intersections.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Taking inverse images under a morphism of schemes commutes with finite intersections. -/
@[simp]
lemma preimage_finset_inf {ι : Type*} (s : Finset ι) (U : ι → Y.Opens) :
    f ⁻¹ᵁ s.inf U = s.inf fun i ↦ f ⁻¹ᵁ U i :=
  Finset.apply_inf_eq_inf_comp (f ⁻¹ᵁ ·) (fun _ _ ↦ rfl) rfl

/-- Taking inverse images under a morphism of schemes commutes with finite products of opens,
which are their intersections. -/
lemma preimage_finite_product {J : Type*} [Finite J] (U : J → Y.Opens) :
    f ⁻¹ᵁ ∏ᶜ U = ∏ᶜ fun j ↦ f ⁻¹ᵁ U j := by
  classical
  have := Fintype.ofFinite J
  exact (congrArg (f ⁻¹ᵁ ·) (CompleteLattice.finite_product_eq_finset_image_inf U id)).trans <|
    (f.preimage_finset_inf _ U).trans
      (CompleteLattice.finite_product_eq_finset_image_inf (fun j ↦ f ⁻¹ᵁ U j) id).symm

/-- The finite product of the inverse images of opens maps to the inverse image of their product,
as both are the same open (`preimage_finite_product`). This is the hypothesis of
`TauCeti.CategoryTheory.cechComplexCompIso` for the functor `f⁻¹`. -/
lemma nonempty_pi_preimage_hom {J : Type*} [Finite J] (U : J → Y.Opens) :
    Nonempty ((∏ᶜ fun j ↦ f ⁻¹ᵁ U j) ⟶ f ⁻¹ᵁ ∏ᶜ U) :=
  ⟨homOfLE (f.preimage_finite_product U).ge⟩

/-- Along an affine morphism, the inverse images of a family of opens whose nonempty finite
intersections are affine again have affine nonempty finite intersections. -/
lemma isAffineOpen_finset_inf_preimage [IsAffineHom f] {ι : Type*} {U : ι → Y.Opens}
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (s.inf U)) (s : Finset ι) (hs : s.Nonempty) :
    IsAffineOpen (s.inf fun i ↦ f ⁻¹ᵁ U i) :=
  f.preimage_finset_inf s U ▸ (hU s hs).preimage f

end AlgebraicGeometry.Scheme.Hom
