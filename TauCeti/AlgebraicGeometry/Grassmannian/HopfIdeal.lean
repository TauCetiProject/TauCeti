/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import TauCeti.AlgebraicGeometry.Grassmannian.IdealLocus
public import TauCeti.RingTheory.Grassmannian.HopfIdeal

import TauCeti.AlgebraicGeometry.Grassmannian.Proper

/-!
# The closed subscheme of Hopf ideals in the Grassmannian scheme

Let `H` be a Hopf algebra over a commutative ring `R`. A point of the Grassmannian scheme
`G(k, H) = Module.Grassmannian.scheme R H k` over `Spec A` is an `A`-submodule `N` of `A ⊗[R] H`
whose quotient is finite projective of constant rank `k`
(`Module.Grassmannian.schemeHomEquiv`). When `N` is a two-sided Hopf ideal, the quotient is a Hopf
algebra over `A`; for commutative `H`, `Spec ((A ⊗[R] H) ⧸ N)` is then a subgroup scheme of
`Spec (A ⊗[R] H)`, finite locally free of rank `k` over `A`. This file cuts out the closed
subscheme of `G(k, H)` over which the universal submodule is a Hopf ideal; for commutative `H` it
parametrises these subgroup schemes.

The closed subscheme is the instance `Module.Grassmannian.schemeIdealLocus` of the general
construction of closed subschemes of `G(k, H)` cut out by ideals of points: being a two-sided Hopf
ideal is cut out by the ideal `Module.Grassmannian.hopfIdealLocus`, whose formation commutes with
base change (`Module.Grassmannian.hopfIdealLocus_map`). Over an affine open `U` of `G(k, H)`, the
ideal of the closed subscheme is `hopfIdealLocus` of the point over `Γ(G(k, H), U)` classifying the
inclusion of `U`.

## Main definitions

* `Module.Grassmannian.schemeHopfIdealLocus R H k`: the ideal sheaf on `G(k, H)` of the closed
  subscheme of Hopf ideals.
* `Module.Grassmannian.schemeHopfIdealLocusHomEquiv R H k A`: the points of `G(k, A ⊗[R] H; A)`
  which are two-sided Hopf ideals are the morphisms from `Spec A` to this closed subscheme over
  `Spec R`.

## Main results

* `Module.Grassmannian.comap_toSchemeHom_schemeHopfIdealLocus`: the inverse image of the closed
  subscheme along the morphism `Spec A ⟶ G(k, H)` classifying a point `N` is the zero scheme of
  `N.hopfIdealLocus`.
* `Module.Grassmannian.schemeHopfIdealLocus_le_ker_toSchemeHom_iff`: **the universal property**;
  the morphism classifying `N` factors through the closed subscheme exactly when `N` is a
  two-sided Hopf ideal of `A ⊗[R] H`.
* `Module.Grassmannian.isProper_subschemeι_schemeHopfIdealLocus_toSpec`: for `H` finite over `R`,
  the closed subscheme is proper over `Spec R`.

## References

* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Scheme.IdealSheafData

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {H : Type u} [Ring H] [HopfAlgebra R H] {k : ℕ}

variable (R H k) in
/-- The ideal sheaf of the **closed subscheme of Hopf ideals** in the Grassmannian scheme
`G(k, H)` of a Hopf algebra `H` over `R`. A morphism `Spec A ⟶ G(k, H)` over `Spec R`, classifying
a point `N` of `G(k, A ⊗[R] H; A)`, factors through this closed subscheme exactly when `N` is a
two-sided Hopf ideal of `A ⊗[R] H`
(`Module.Grassmannian.schemeHopfIdealLocus_le_ker_toSchemeHom_iff`). Over an affine open `U`, its
ideal is `Module.Grassmannian.hopfIdealLocus` of the point over `Γ(G(k, H), U)` classifying the
inclusion of `U`. -/
noncomputable def schemeHopfIdealLocus : (scheme R H k).IdealSheafData :=
  schemeIdealLocus (R := R) (M := H) (k := k) (fun N ↦ N.hopfIdealLocus) hopfIdealLocus_map

/-- **The inverse image of the closed subscheme of Hopf ideals along a point.** For an
`R`-algebra `A` and a point `N` of `G(k, A ⊗[R] H; A)`, the inverse image of the closed subscheme
of Hopf ideals along the morphism `Spec A ⟶ G(k, H)` classifying `N` is the zero scheme of
`N.hopfIdealLocus`. -/
theorem comap_toSchemeHom_schemeHopfIdealLocus {A : Type u} [CommRing A] [Algebra R A]
    (N : G(k, A ⊗[R] H; A)) :
    (schemeHopfIdealLocus R H k).comap (toSchemeHom N) =
      ofIdealTop (N.hopfIdealLocus.map (Scheme.ΓSpecIso (.of A)).inv.hom) :=
  comap_toSchemeHom_schemeIdealLocus (R := R) (M := H) (k := k) (fun N ↦ N.hopfIdealLocus)
    hopfIdealLocus_map N

/-- **The universal property of the closed subscheme of Hopf ideals.** For an `R`-algebra `A`, the
morphism `Spec A ⟶ G(k, H)` classifying a point `N` of `G(k, A ⊗[R] H; A)` factors through the
closed subscheme of Hopf ideals exactly when `N.hopfIdealLocus` vanishes, that is, exactly when `N`
is a two-sided Hopf ideal of `A ⊗[R] H` (`Module.Grassmannian.hopfIdealLocus_eq_bot_iff`). -/
theorem schemeHopfIdealLocus_le_ker_toSchemeHom_iff {A : Type u} [CommRing A] [Algebra R A]
    (N : G(k, A ⊗[R] H; A)) :
    schemeHopfIdealLocus R H k ≤ (toSchemeHom N).ker ↔ N.hopfIdealLocus = ⊥ :=
  schemeIdealLocus_le_ker_toSchemeHom_iff (R := R) (M := H) (k := k) (fun N ↦ N.hopfIdealLocus)
    hopfIdealLocus_map N

variable (R H k) in
/-- **The closed subscheme of Hopf ideals represents the Hopf ideals in the Grassmannian.** For an
`R`-algebra `A`, the points `N` of `G(k, A ⊗[R] H; A)` which are two-sided Hopf ideals, that is,
with `N.hopfIdealLocus = ⊥` (`Module.Grassmannian.hopfIdealLocus_eq_bot_iff`), are in bijection
with the morphisms from `Spec A` to the closed subscheme of Hopf ideals over `Spec R`. The
bijection composes with the inclusion into `G(k, H)` to the morphism classifying `N`
(`Module.Grassmannian.schemeHopfIdealLocusHomEquiv_apply_comp_subschemeι` and
`Module.Grassmannian.toSchemeHom_schemeHopfIdealLocusHomEquiv_symm_apply`). -/
noncomputable def schemeHopfIdealLocusHomEquiv (A : Type u) [CommRing A] [Algebra R A] :
    {N : G(k, A ⊗[R] H; A) // N.hopfIdealLocus = ⊥} ≃
      {h : Spec (.of A) ⟶ (schemeHopfIdealLocus R H k).subscheme //
        h ≫ (schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k =
          Spec.map (CommRingCat.ofHom (algebraMap R A))} :=
  schemeIdealLocusHomEquiv (R := R) (M := H) (k := k) (fun N ↦ N.hopfIdealLocus)
    hopfIdealLocus_map A

/-- The morphism to the closed subscheme of Hopf ideals corresponding to a Hopf ideal `N`, followed
by the inclusion into the Grassmannian scheme, is the morphism classifying `N`. -/
@[reassoc (attr := simp)]
theorem schemeHopfIdealLocusHomEquiv_apply_comp_subschemeι {A : Type u} [CommRing A] [Algebra R A]
    (N : {N : G(k, A ⊗[R] H; A) // N.hopfIdealLocus = ⊥}) :
    (schemeHopfIdealLocusHomEquiv R H k A N).1 ≫ (schemeHopfIdealLocus R H k).subschemeι =
      toSchemeHom N.1 :=
  schemeIdealLocusHomEquiv_apply_comp_subschemeι (R := R) (M := H) (k := k)
    (fun N ↦ N.hopfIdealLocus) hopfIdealLocus_map N

/-- The Hopf ideal corresponding to a morphism `h` to the closed subscheme of Hopf ideals is the
point classified by `h` followed by the inclusion into the Grassmannian scheme. -/
@[simp]
theorem toSchemeHom_schemeHopfIdealLocusHomEquiv_symm_apply {A : Type u} [CommRing A]
    [Algebra R A] (h : {h : Spec (.of A) ⟶ (schemeHopfIdealLocus R H k).subscheme //
      h ≫ (schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k =
        Spec.map (CommRingCat.ofHom (algebraMap R A))}) :
    toSchemeHom ((schemeHopfIdealLocusHomEquiv R H k A).symm h).1 =
      h.1 ≫ (schemeHopfIdealLocus R H k).subschemeι :=
  toSchemeHom_schemeIdealLocusHomEquiv_symm_apply (R := R) (M := H) (k := k)
    (fun N ↦ N.hopfIdealLocus) hopfIdealLocus_map h

/-- For `H` finite over `R`, the closed subscheme of Hopf ideals is proper over `Spec R`, as a
closed subscheme of the proper Grassmannian scheme. -/
instance isProper_subschemeι_schemeHopfIdealLocus_toSpec [Module.Finite R H] :
    IsProper ((schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k) :=
  inferInstance

end Module.Grassmannian
