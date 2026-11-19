/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.IsBaseChange

/-!
# Base change of the Grassmannian scheme

Let `M` be a module over a commutative ring `R`, let `R'` be an `R`-algebra and `k` a natural
number. This file proves that the formation of the Grassmannian scheme
`Module.Grassmannian.scheme R M k` commutes with base change along `Spec R' ⟶ Spec R`: the
Grassmannian `G(k, R' ⊗[R] M)` of the base-changed module over `Spec R'` is the fibre product
`Spec R' ×_{Spec R} G(k, M)` (`Module.Grassmannian.isPullback_baseChangeHom`).

Both schemes represent the same functor on affine schemes over `Spec R'`. For an `R'`-algebra
`A`, a morphism `Spec A ⟶ G(k, R' ⊗[R] M)` over `Spec R'` is a point of
`G(k, A ⊗[R'] (R' ⊗[R] M); A)` (`Module.Grassmannian.schemeHomEquiv`), and the isomorphism
`A ⊗[R'] (R' ⊗[R] M) ≃ A ⊗[R] M` identifies these points with the points of `G(k, A ⊗[R] M; A)`
(`Module.Grassmannian.baseChangeEquiv`), that is, with the morphisms `Spec A ⟶ G(k, M)` over
`Spec R`. This is the case `M' = R' ⊗[R] M` of the morphism `Module.Grassmannian.isBaseChangeHom`
attached to a base change of modules, so `Module.Grassmannian.baseChangeHom R R' M k` is that
morphism for the base change `M → R' ⊗[R] M`, `m ↦ 1 ⊗ m`.

For instance, over a basic open `Spec R[1/f] ⊆ Spec R` it identifies the restriction of `G(k, M)`
with `G(k, R[1/f] ⊗[R] M)`.

## Main definitions

* `Module.Grassmannian.baseChangeHom R R' M k`: the projection
  `G(k, R' ⊗[R] M) ⟶ G(k, M)`, sending the point classifying `N` to the point classifying its
  image under `A ⊗[R'] (R' ⊗[R] M) ≃ A ⊗[R] M`.

## Main results

* `Module.Grassmannian.isBaseChangeEquiv_isBaseChange`: for the base change `m ↦ 1 ⊗ m`, the
  bijection `isBaseChangeEquiv` on points is `baseChangeEquiv`.
* `Module.Grassmannian.toSchemeHom_comp_baseChangeHom`: the characterisation of
  `baseChangeHom` on points.
* `Module.Grassmannian.isPullback_baseChangeHom`: **base change**; `G(k, R' ⊗[R] M)` is the fibre
  product of `G(k, M)` and `Spec R'` over `Spec R`.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7.
* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace Module.Grassmannian

variable (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type u) [AddCommGroup M]
  [Module R M] (k : ℕ)

/-- **The projection from the Grassmannian of a base change.** For an `R`-algebra `R'`, the
morphism `G(k, R' ⊗[R] M) ⟶ G(k, M)` which sends the point classifying `N` over an `R'`-algebra
`A` to the point classifying its image under `A ⊗[R'] (R' ⊗[R] M) ≃ A ⊗[R] M`
(`Module.Grassmannian.toSchemeHom_comp_baseChangeHom`): the morphism
`Module.Grassmannian.isBaseChangeHom` of the base change `m ↦ 1 ⊗ m`. Together with the structure
morphism of `G(k, R' ⊗[R] M)`, it exhibits `G(k, R' ⊗[R] M)` as the base change of `G(k, M)` to
`Spec R'` (`Module.Grassmannian.isPullback_baseChangeHom`). -/
noncomputable def baseChangeHom : scheme R' (R' ⊗[R] M) k ⟶ scheme R M k :=
  isBaseChangeHom (TensorProduct.isBaseChange R M R') k

variable {R R' M k}

variable {A : Type u} [CommRing A] [Algebra R' A] [Algebra R A] [IsScalarTower R R' A]

/-- For the base change `m ↦ 1 ⊗ m`, the bijection `isBaseChangeEquiv` on points is
`baseChangeEquiv`. -/
theorem isBaseChangeEquiv_isBaseChange (N : G(k, A ⊗[R'] (R' ⊗[R] M); A)) :
    isBaseChangeEquiv (TensorProduct.isBaseChange R M R') A N = baseChangeEquiv R' N := by
  ext : 1
  rw [toSubmodule_isBaseChangeEquiv, toSubmodule_baseChangeEquiv]
  congr 1
  refine LinearMap.ext fun x ↦ ?_
  induction x using (TensorProduct.isBaseChange R M R').forall_tmul A with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a m => simpa using isBaseChangeLinearEquiv_tmul (TensorProduct.isBaseChange R M R') A a m

/-- **`baseChangeHom` on points.** The morphism classifying `N` over an `R'`-algebra `A`, composed
with `baseChangeHom`, classifies the image of `N` in `G(k, A ⊗[R] M; A)`. -/
@[reassoc (attr := simp)]
theorem toSchemeHom_comp_baseChangeHom (N : G(k, A ⊗[R'] (R' ⊗[R] M); A)) :
    toSchemeHom N ≫ baseChangeHom R R' M k = toSchemeHom (baseChangeEquiv R' N) := by
  rw [baseChangeHom, toSchemeHom_comp_isBaseChangeHom, isBaseChangeEquiv_isBaseChange]

variable (R R' M k) in
/-- `baseChangeHom` lies over `Spec R' ⟶ Spec R`. -/
@[reassoc (attr := simp)]
theorem baseChangeHom_toSpec :
    baseChangeHom R R' M k ≫ toSpec R M k =
      toSpec R' (R' ⊗[R] M) k ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) :=
  isBaseChangeHom_toSpec _ k

variable (R R' M k) in
/-- **Base change of the Grassmannian scheme.** For an `R`-algebra `R'`, the Grassmannian
`G(k, R' ⊗[R] M)` over `Spec R'` is the fibre product of `G(k, M) ⟶ Spec R` and
`Spec R' ⟶ Spec R`, with projections `baseChangeHom` and the structure morphism. -/
theorem isPullback_baseChangeHom :
    IsPullback (baseChangeHom R R' M k) (toSpec R' (R' ⊗[R] M) k) (toSpec R M k)
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
  isPullback_isBaseChangeHom _ k

end Module.Grassmannian
