/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.BaseChange

/-!
# The Grassmannian scheme of an isomorphic module

Let `M` and `M'` be modules over a commutative ring `R` and `k` a natural number. This file
proves that a linear equivalence `e : M ≃ₗ[R] M'` induces an isomorphism of Grassmannian schemes
`G(k, M) ≅ G(k, M')` over `Spec R` (`Module.Grassmannian.schemeIsoOfLinearEquiv`), functorial in
`e`.

On points over an `R`-algebra `A`, the isomorphism sends the point classifying
`N ∈ G(k, A ⊗[R] M; A)` to the point classifying its image under the base change
`A ⊗[R] M ≃ A ⊗[R] M'` of `e` (`LinearEquiv.grassmannianCongr`). This map of points is natural in
`A` (`Module.Grassmannian.map_grassmannianCongr_baseChange`), so it is composition with a morphism
of schemes (`AlgebraicGeometry.Scheme.homOfAffinePoints`), and the identities between the maps of
points give the identities between the morphisms, since a morphism out of the Grassmannian is
determined by its points (`Module.Grassmannian.scheme_hom_ext`). The morphisms are built from
their maps of points by `Module.Grassmannian.homOfPoints`.

This is the comparison needed for the relative Grassmannian of a finite locally free sheaf `E` on
a scheme to be independent of the trivialisations of `E`: two trivialisations over the same affine
open differ by a linear automorphism of `M`.

## Main definitions

* `Module.Grassmannian.schemeIsoOfLinearEquiv k e`: the isomorphism `G(k, M) ≅ G(k, M')` induced
  by `e : M ≃ₗ[R] M'`.

## Main results

* `Module.Grassmannian.toSchemeHom_comp_schemeIsoOfLinearEquiv_hom`: the isomorphism on points.
* `Module.Grassmannian.schemeIsoOfLinearEquiv_hom_toSpec`: the isomorphism lies over `Spec R`.
* `Module.Grassmannian.schemeIsoOfLinearEquiv_refl`, `schemeIsoOfLinearEquiv_trans`,
  `schemeIsoOfLinearEquiv_inv` and `schemeIsoOfLinearEquiv_symm`: functoriality in `e`.
* `Module.Grassmannian.schemeIsoOfLinearEquiv_baseChange_hom_comp_baseChangeHom`: compatibility
  with base change along `Spec R' ⟶ Spec R` (`Module.Grassmannian.baseChangeHom`).

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7.
* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M M' M'' : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M''] {k : ℕ}

/-- The map of points underlying `schemeIsoOfLinearEquiv`: transport along the base change of
`e`, as a morphism `Spec A ⟶ G(k, M')`. -/
private noncomputable def congrPoints (e : M ≃ₗ[R] M') (A : Type u) [CommRing A] [Algebra R A]
    (N : G(k, A ⊗[R] M; A)) : Spec (.of A) ⟶ scheme R M' k :=
  toSchemeHom ((e.baseChange R A M M').grassmannianCongr N)

private lemma congrPoints_map (e : M ≃ₗ[R] M') (A B : Type u) [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)) :
    congrPoints e B (map f N) = Spec.map (CommRingCat.ofHom (f : A →+* B)) ≫ congrPoints e A N := by
  rw [congrPoints, congrPoints, ← map_grassmannianCongr_baseChange, toSchemeHom_map]

variable (k) in
/-- **The Grassmannian scheme of an isomorphic module.** A linear equivalence `e : M ≃ₗ[R] M'`
induces an isomorphism `G(k, M) ≅ G(k, M')` over `Spec R`
(`Module.Grassmannian.schemeIsoOfLinearEquiv_hom_toSpec`), which sends the point classifying `N`
over an `R`-algebra `A` to the point classifying its image under `A ⊗[R] M ≃ A ⊗[R] M'`
(`Module.Grassmannian.toSchemeHom_comp_schemeIsoOfLinearEquiv_hom`). -/
noncomputable def schemeIsoOfLinearEquiv (e : M ≃ₗ[R] M') : scheme R M k ≅ scheme R M' k where
  hom := homOfPoints (congrPoints e) (congrPoints_map e)
  inv := homOfPoints (congrPoints e.symm) (congrPoints_map e.symm)
  hom_inv_id := scheme_hom_ext fun A _ _ N ↦ by
    simp [congrPoints, LinearEquiv.baseChange_symm, ← LinearEquiv.grassmannianCongr_symm]
  inv_hom_id := scheme_hom_ext fun A _ _ N ↦ by
    simp [congrPoints, LinearEquiv.baseChange_symm, ← LinearEquiv.grassmannianCongr_symm]

/-- **`schemeIsoOfLinearEquiv` on points.** The morphism classifying `N` over an `R`-algebra `A`,
composed with `schemeIsoOfLinearEquiv k e`, classifies the image of `N` under the base change
`A ⊗[R] M ≃ A ⊗[R] M'` of `e`. -/
@[reassoc (attr := simp)]
theorem toSchemeHom_comp_schemeIsoOfLinearEquiv_hom (e : M ≃ₗ[R] M') {A : Type u} [CommRing A]
    [Algebra R A] (N : G(k, A ⊗[R] M; A)) :
    toSchemeHom N ≫ (schemeIsoOfLinearEquiv k e).hom =
      toSchemeHom ((e.baseChange R A M M').grassmannianCongr N) :=
  toSchemeHom_comp_homOfPoints _ _ N

/-- The inverse of the isomorphism induced by `e` is the forward map induced by `e.symm`. -/
@[simp]
theorem schemeIsoOfLinearEquiv_inv (e : M ≃ₗ[R] M') :
    (schemeIsoOfLinearEquiv k e).inv = (schemeIsoOfLinearEquiv k e.symm).hom :=
  (rfl)

/-- The inverse of the isomorphism induced by `e` is the isomorphism induced by `e.symm`. -/
@[simp]
theorem schemeIsoOfLinearEquiv_symm (e : M ≃ₗ[R] M') :
    (schemeIsoOfLinearEquiv k e).symm = schemeIsoOfLinearEquiv k e.symm :=
  Iso.ext (schemeIsoOfLinearEquiv_inv e)

/-- `schemeIsoOfLinearEquiv k e` lies over `Spec R`. -/
@[reassoc (attr := simp)]
theorem schemeIsoOfLinearEquiv_hom_toSpec (e : M ≃ₗ[R] M') :
    (schemeIsoOfLinearEquiv k e).hom ≫ toSpec R M' k = toSpec R M k :=
  scheme_hom_ext fun A _ _ N ↦ by simp [toSchemeHom_toSpec]

/-- The identity of `M` induces the identity of `G(k, M)`. -/
@[simp]
theorem schemeIsoOfLinearEquiv_refl :
    schemeIsoOfLinearEquiv k (LinearEquiv.refl R M) = Iso.refl (scheme R M k) :=
  Iso.ext <| scheme_hom_ext fun A _ _ N ↦ by
    -- the base change of the identity of `M` is the identity of `A ⊗[R] M`
    rw [toSchemeHom_comp_schemeIsoOfLinearEquiv_hom, ← LinearEquiv.one_eq_refl,
      LinearEquiv.baseChange_one, LinearEquiv.one_eq_refl, LinearEquiv.grassmannianCongr_refl]
    simp

/-- The isomorphism induced by a composite is the composite of the isomorphisms. -/
theorem schemeIsoOfLinearEquiv_trans (e : M ≃ₗ[R] M') (e' : M' ≃ₗ[R] M'') :
    schemeIsoOfLinearEquiv k (e.trans e') =
      schemeIsoOfLinearEquiv k e ≪≫ schemeIsoOfLinearEquiv k e' :=
  Iso.ext <| scheme_hom_ext fun A _ _ N ↦ by
    simp [LinearEquiv.baseChange_trans, LinearEquiv.grassmannianCongr_trans]

/-- **Compatibility with base change.** For an `R`-algebra `R'`, the isomorphism
`G(k, R' ⊗[R] M) ≅ G(k, R' ⊗[R] M')` induced by the base change of `e` lies over the isomorphism
`G(k, M) ≅ G(k, M')` induced by `e`, along the projections `Module.Grassmannian.baseChangeHom`. -/
@[reassoc]
theorem schemeIsoOfLinearEquiv_baseChange_hom_comp_baseChangeHom (R' : Type u) [CommRing R']
    [Algebra R R'] (e : M ≃ₗ[R] M') :
    (schemeIsoOfLinearEquiv k (e.baseChange R R' M M')).hom ≫ baseChangeHom R R' M' k =
      baseChangeHom R R' M k ≫ (schemeIsoOfLinearEquiv k e).hom :=
  scheme_hom_ext fun A _ _ N ↦ by
    -- make `A` an `R`-algebra through `R'`, so that `baseChangeHom` can be computed on points
    let _ : Algebra R A := ((algebraMap R' A).comp (algebraMap R R')).toAlgebra
    have : IsScalarTower R R' A := .of_algebraMap_eq' rfl
    simp [baseChangeEquiv_grassmannianCongr]

end Module.Grassmannian
