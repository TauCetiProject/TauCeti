/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.IdealLocus
public import TauCeti.RingTheory.Grassmannian.Isotropic

/-!
# The isotropic Grassmannian

Let `ω` be a bilinear form on a module `M` over a commutative ring `R`. A point of the Grassmannian
scheme `G(k, M) = Module.Grassmannian.scheme R M k` over `Spec A` is an `A`-submodule `N` of
`A ⊗[R] M` whose quotient is finite projective of constant rank `k`
(`Module.Grassmannian.schemeHomEquiv`); it is *isotropic* when the base change `ω_A` of `ω`
vanishes on `N × N`. This file constructs the **isotropic Grassmannian**, the closed subscheme of
`G(k, M)` over which the tautological submodule is isotropic, and proves that it represents the
isotropic points: a morphism `Spec A ⟶ G(k, M)` over `Spec R` factors through it exactly when the
point it classifies is isotropic. For a nondegenerate alternating form on `R^{2m}` and quotient
rank `k = 2m - r`, this is the Grassmannian of rank-`r` isotropic subbundles. Nothing is assumed
about the form or about `2`, so this covers characteristic `2` with an actual alternating form.

The closed subscheme is the instance `Module.Grassmannian.schemeIdealLocus` of the general
construction of closed subschemes of `G(k, M)` cut out by ideals of points: isotropy is cut out by
the ideal `Module.Grassmannian.isotropicLocus` of the values of `ω_A` on `N × N`, whose formation
commutes with base change (`Module.Grassmannian.isotropicLocus_map`). Over an affine open `U` of
`G(k, M)`, the ideal of the isotropic Grassmannian is `isotropicLocus` of the point over
`Γ(G(k, M), U)` classifying the inclusion of `U`.

## Main definitions

* `Module.Grassmannian.schemeIsotropicLocus k ω`: the ideal sheaf on `G(k, M)` of the isotropic
  Grassmannian.
* `Module.Grassmannian.schemeIsotropicLocusHomEquiv k ω A`: the isotropic points of
  `G(k, A ⊗[R] M; A)` are the morphisms from `Spec A` to the isotropic Grassmannian over
  `Spec R`.

## Main results

* `Module.Grassmannian.comap_toSchemeHom_schemeIsotropicLocus`: the inverse image of the isotropic
  Grassmannian along the morphism `Spec A ⟶ G(k, M)` classifying a point `N` is the zero scheme of
  `N.isotropicLocus ω`.
* `Module.Grassmannian.schemeIsotropicLocus_le_ker_toSchemeHom_iff`: **the universal property**;
  the morphism classifying `N` factors through the isotropic Grassmannian exactly when `N` is
  isotropic for `ω_A`.

For `M` finite over `R`, the isotropic Grassmannian is proper over `Spec R` by instance inference,
as a closed subscheme of the proper Grassmannian scheme (`Module.Grassmannian.isProper_toSpec`).

## References

* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7, for
  closed conditions on the Grassmannian.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Scheme.IdealSheafData

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M] {k : ℕ}

variable (k) in
/-- The ideal sheaf of the **isotropic Grassmannian** of a bilinear form `ω` on `M`: the closed
subscheme of the Grassmannian scheme `G(k, M)` over which the tautological submodule is isotropic
for `ω`. A morphism `Spec A ⟶ G(k, M)` over `Spec R`, classifying a point `N` of
`G(k, A ⊗[R] M; A)`, factors through this closed subscheme exactly when `N` is isotropic for the
base change of `ω` to `A`
(`Module.Grassmannian.schemeIsotropicLocus_le_ker_toSchemeHom_iff`). Over an affine open `U`, its
ideal is `Module.Grassmannian.isotropicLocus` of the point over `Γ(G(k, M), U)` classifying the
inclusion of `U`. -/
noncomputable def schemeIsotropicLocus (ω : LinearMap.BilinForm R M) :
    (scheme R M k).IdealSheafData :=
  schemeIdealLocus (R := R) (M := M) (k := k) (fun N ↦ N.isotropicLocus ω)
    fun f N ↦ isotropicLocus_map f N ω

/-- **The inverse image of the isotropic Grassmannian along a point.** For an `R`-algebra `A` and
a point `N` of `G(k, A ⊗[R] M; A)`, the inverse image of the isotropic Grassmannian along the
morphism `Spec A ⟶ G(k, M)` classifying `N` is the zero scheme of `N.isotropicLocus ω`. -/
theorem comap_toSchemeHom_schemeIsotropicLocus (ω : LinearMap.BilinForm R M) {A : Type u}
    [CommRing A] [Algebra R A] (N : G(k, A ⊗[R] M; A)) :
    (schemeIsotropicLocus k ω).comap (toSchemeHom N) =
      ofIdealTop ((N.isotropicLocus ω).map (Scheme.ΓSpecIso (.of A)).inv.hom) :=
  comap_toSchemeHom_schemeIdealLocus (R := R) (M := M) (k := k) (fun N ↦ N.isotropicLocus ω)
    (fun f N ↦ isotropicLocus_map f N ω) N

/-- **The universal property of the isotropic Grassmannian.** For an `R`-algebra `A`, the
morphism `Spec A ⟶ G(k, M)` classifying a point `N` of `G(k, A ⊗[R] M; A)` factors through the
isotropic Grassmannian exactly when `N` is isotropic for the base change `ω_A` of `ω`, that is,
when `N` lies in its own orthogonal for `ω_A`. -/
theorem schemeIsotropicLocus_le_ker_toSchemeHom_iff (ω : LinearMap.BilinForm R M) {A : Type u}
    [CommRing A] [Algebra R A] (N : G(k, A ⊗[R] M; A)) :
    schemeIsotropicLocus k ω ≤ (toSchemeHom N).ker ↔
      N.toSubmodule ≤ (ω.baseChange A).orthogonal N.toSubmodule :=
  (schemeIdealLocus_le_ker_toSchemeHom_iff (R := R) (M := M) (k := k)
    (fun N ↦ N.isotropicLocus ω) (fun f N ↦ isotropicLocus_map f N ω) N).trans
    (isotropicLocus_eq_bot_iff N ω)

variable (k) in
/-- **The isotropic Grassmannian represents the isotropic points of the Grassmannian.** For an
`R`-algebra `A`, the points `N` of `G(k, A ⊗[R] M; A)` which are isotropic for the base change
`ω_A` of `ω` are in bijection with the morphisms from `Spec A` to the isotropic Grassmannian over
`Spec R`. The bijection composes with the inclusion into `G(k, M)` to the morphism classifying `N`
(`Module.Grassmannian.schemeIsotropicLocusHomEquiv_apply_comp_subschemeι` and
`Module.Grassmannian.toSchemeHom_schemeIsotropicLocusHomEquiv_symm_apply`). -/
noncomputable def schemeIsotropicLocusHomEquiv (ω : LinearMap.BilinForm R M) (A : Type u)
    [CommRing A] [Algebra R A] :
    {N : G(k, A ⊗[R] M; A) // N.toSubmodule ≤ (ω.baseChange A).orthogonal N.toSubmodule} ≃
      {h : Spec (.of A) ⟶ (schemeIsotropicLocus k ω).subscheme //
        h ≫ (schemeIsotropicLocus k ω).subschemeι ≫ toSpec R M k =
          Spec.map (CommRingCat.ofHom (algebraMap R A))} :=
  (Equiv.subtypeEquivRight fun N ↦ (isotropicLocus_eq_bot_iff N ω).symm).trans
    (schemeIdealLocusHomEquiv (R := R) (M := M) (k := k) (fun N ↦ N.isotropicLocus ω)
      (fun f N ↦ isotropicLocus_map f N ω) A)

/-- The morphism to the isotropic Grassmannian corresponding to an isotropic point `N`, followed by
the inclusion into the Grassmannian scheme, is the morphism classifying `N`. -/
@[reassoc (attr := simp)]
theorem schemeIsotropicLocusHomEquiv_apply_comp_subschemeι (ω : LinearMap.BilinForm R M)
    {A : Type u} [CommRing A] [Algebra R A]
    (N : {N : G(k, A ⊗[R] M; A) // N.toSubmodule ≤ (ω.baseChange A).orthogonal N.toSubmodule}) :
    (schemeIsotropicLocusHomEquiv k ω A N).1 ≫ (schemeIsotropicLocus k ω).subschemeι =
      toSchemeHom N.1 :=
  schemeIdealLocusHomEquiv_apply_comp_subschemeι (R := R) (M := M) (k := k)
    (fun N ↦ N.isotropicLocus ω) (fun f N ↦ isotropicLocus_map f N ω) _

/-- The isotropic point corresponding to a morphism `h` to the isotropic Grassmannian is the point
classified by `h` followed by the inclusion into the Grassmannian scheme. -/
@[simp]
theorem toSchemeHom_schemeIsotropicLocusHomEquiv_symm_apply (ω : LinearMap.BilinForm R M)
    {A : Type u} [CommRing A] [Algebra R A]
    (h : {h : Spec (.of A) ⟶ (schemeIsotropicLocus k ω).subscheme //
      h ≫ (schemeIsotropicLocus k ω).subschemeι ≫ toSpec R M k =
        Spec.map (CommRingCat.ofHom (algebraMap R A))}) :
    toSchemeHom ((schemeIsotropicLocusHomEquiv k ω A).symm h).1 =
      h.1 ≫ (schemeIsotropicLocus k ω).subschemeι :=
  toSchemeHom_schemeIdealLocusHomEquiv_symm_apply (R := R) (M := M) (k := k)
    (fun N ↦ N.isotropicLocus ω) (fun f N ↦ isotropicLocus_map f N ω) h

end Module.Grassmannian
