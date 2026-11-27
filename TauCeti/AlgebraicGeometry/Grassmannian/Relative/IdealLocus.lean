/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.IdealLocus
public import TauCeti.AlgebraicGeometry.Grassmannian.Relative.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.Glue

import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# Closed subschemes of the relative Grassmannian cut out by ideals of points

Let `E` be a quasi-coherent `𝒪_X`-module on a scheme `X`. Over each affine open `U` of `X`, the
relative Grassmannian `G(k, E) = AlgebraicGeometry.Scheme.Modules.grassmannian E k` is the
Grassmannian scheme `G(k, Γ(E, U))` over `Spec Γ(X, U)`, whose points over a `Γ(X, U)`-algebra `A`
are the points of `G(k, A ⊗[Γ(X, U)] Γ(E, U); A)`. A closed condition on these points is an ideal
`I U N` of `A` for each such point `N`, compatible with base change in `A`; it cuts out a closed
subscheme `Module.Grassmannian.schemeIdealLocus` of `G(k, Γ(E, U))`. Examples are being a
two-sided Hopf ideal (`Module.Grassmannian.hopfIdealLocus`), when the sections of `E` are Hopf
algebras, and being stable under an endomorphism (`Module.Grassmannian.stableLocus`).

This file glues such closed conditions over the affine opens of `X`. Suppose that for affine opens
`V ≤ U` the condition over `V` on a point over a `Γ(X, V)`-algebra is the condition over `U` on its
image under `Γ(X, V) ⊗[Γ(X, U)] Γ(E, U) ≃ Γ(E, V)`. Then the closed subschemes over the affine
opens are compatible with the comparison morphisms `grassmannianChartMap`
(`AlgebraicGeometry.Scheme.Modules.comap_grassmannianChartMap_schemeIdealLocus`), so they glue
along the open cover of `G(k, E)` by the `G(k, Γ(E, U))`
(`AlgebraicGeometry.Scheme.IdealSheafData.glue`) to a closed subscheme of the relative
Grassmannian over the arbitrary base `X`
(`AlgebraicGeometry.Scheme.Modules.grassmannianIdealLocus`).
Its part over each affine open `U` is the closed subscheme of `G(k, Γ(E, U))` cut out by the
condition over `U`, as a scheme over `Spec Γ(X, U)`
(`AlgebraicGeometry.Scheme.Modules.isPullback_grassmannianIdealLocus_fromSpec`).

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.grassmannianIdealLocus E I hI hres`: the closed subscheme of
  the relative Grassmannian glued from the closed subschemes of the `G(k, Γ(E, U))` cut out by
  the ideals `I U`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.comap_grassmannianι_grassmannianIdealLocus`: its inverse image
  on `G(k, Γ(E, U))` is the closed subscheme cut out by `I U`;
  `AlgebraicGeometry.Scheme.Modules.eq_grassmannianIdealLocus_iff` characterises it by these
  inverse images.
* `AlgebraicGeometry.Scheme.Modules.isPullback_grassmannianIdealLocus_fromSpec`: its part over an
  affine open `U` is the closed subscheme of `G(k, Γ(E, U))` cut out by `I U`, over `Spec Γ(X, U)`.
* `AlgebraicGeometry.Scheme.Modules.grassmannianIdealLocus_le_ker_iff`: **the universal property
  on points**; the morphism from `Spec A` classifying a point `N` over an affine open `U` factors
  through the closed subscheme exactly when `I U N = ⊥`.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7, for
  closed conditions on the Grassmannian.
* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
-/

public section

universe u

open CategoryTheory Limits TensorProduct AlgebraicGeometry Module.Grassmannian
  Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] {k : ℕ}
  (I : ∀ (U : X.affineOpens) {A : Type u} [CommRing A] [Algebra Γ(X, U.val) A],
    G(k, A ⊗[Γ(X, U.val)] Γ(E, U.val); A) → Ideal A)
  (hI : ∀ (U : X.affineOpens) {A B : Type u} [CommRing A] [Algebra Γ(X, U.val) A] [CommRing B]
    [Algebra Γ(X, U.val) B] (f : A →ₐ[Γ(X, U.val)] B)
    (N : G(k, A ⊗[Γ(X, U.val)] Γ(E, U.val); A)), I U (map f N) = Ideal.map f (I U N))
  (hres : ∀ {U V : X.affineOpens} (h : V.val ≤ U.val),
    letI := restrictionAlgebra h
    letI := restrictionModule E h
    haveI := isScalarTower_restriction E h
    ∀ {A : Type u} [CommRing A] [Algebra Γ(X, V.val) A] [Algebra Γ(X, U.val) A]
      [IsScalarTower Γ(X, U.val) Γ(X, V.val) A] (N : G(k, A ⊗[Γ(X, V.val)] Γ(E, V.val); A)),
      I U ((E.isBaseChange_sectionsRestrictionLinearMap U.property V.property h
        fun _ ↦ rfl).grassmannianEquiv A N) = I V N)

include hres in
/-- **The closed subschemes over the affine opens are compatible.** For affine opens `V ≤ U`, the
inverse image along `grassmannianChartMap : G(k, Γ(E, V)) ⟶ G(k, Γ(E, U))` of the closed
subscheme cut out by `I U` is the closed subscheme cut out by `I V`. -/
theorem comap_grassmannianChartMap_schemeIdealLocus {U V : X.affineOpens} (h : V.val ≤ U.val) :
    (schemeIdealLocus (I U) (hI U)).comap (grassmannianChartMap E k h) =
      schemeIdealLocus (I V) (hI V) := by
  let _ := restrictionAlgebra h
  let _ := restrictionModule E h
  have _ := isScalarTower_restriction E h
  rw [grassmannianChartMap_eq]
  exact IsBaseChange.comap_grassmannianSchemeHom_schemeIdealLocus _ (I U) (hI U) (I V) (hI V)
    (hres h)

/-- The **closed subscheme of the relative Grassmannian cut out by ideals of points**: for closed
conditions `I U` on the points of the Grassmannians `G(k, Γ(E, U))` over the affine opens `U` of
`X`, compatible with restriction to smaller affine opens, the closed subscheme of `G(k, E)` whose
part over each affine open `U` is the closed subscheme of `G(k, Γ(E, U))` cut out by `I U`
(`AlgebraicGeometry.Scheme.Modules.comap_grassmannianι_grassmannianIdealLocus`). -/
noncomputable def grassmannianIdealLocus : (grassmannian E k).IdealSheafData :=
  glue (grassmannianOpenCover E k) (fun U ↦ schemeIdealLocus (I U) (hI U))
    fun h ↦ comap_grassmannianChartMap_schemeIdealLocus E I hI hres (leOfHom h)

/-- The inverse image of `grassmannianIdealLocus` on the part `G(k, Γ(E, U))` of the relative
Grassmannian over an affine open `U` is the closed subscheme cut out by `I U`. -/
@[simp]
theorem comap_grassmannianι_grassmannianIdealLocus (U : X.affineOpens) :
    (grassmannianIdealLocus E I hI hres).comap (grassmannianι E k U) =
      schemeIdealLocus (I U) (hI U) :=
  comap_glue (grassmannianOpenCover E k) _
    (fun h ↦ comap_grassmannianChartMap_schemeIdealLocus E I hI hres (leOfHom h)) U

/-- **Uniqueness of the glued closed subscheme.** An ideal sheaf on the relative Grassmannian is
`grassmannianIdealLocus` exactly when its inverse image on each part `G(k, Γ(E, U))` over an affine
open `U` is the closed subscheme cut out by `I U`. -/
theorem eq_grassmannianIdealLocus_iff {J : (grassmannian E k).IdealSheafData} :
    J = grassmannianIdealLocus E I hI hres ↔
      ∀ U : X.affineOpens, J.comap (grassmannianι E k U) = schemeIdealLocus (I U) (hI U) :=
  eq_glue_iff (grassmannianOpenCover E k) _
    fun h ↦ comap_grassmannianChartMap_schemeIdealLocus E I hI hres (leOfHom h)

/-- **The closed subscheme over an affine open.** For an affine open `U` of `X`, the part of
`grassmannianIdealLocus` over `U` is the closed subscheme of `G(k, Γ(E, U))` cut out by `I U`: the
square formed by `Spec Γ(X, U) ⟶ X` and the structure morphisms of the two closed subschemes is a
pullback square. -/
theorem isPullback_grassmannianIdealLocus_fromSpec (U : X.affineOpens) :
    IsPullback
      (subschemeMap (schemeIdealLocus (I U) (hI U)) (grassmannianIdealLocus E I hI hres)
        (grassmannianι E k U)
        (le_map_iff_comap_le.2 (comap_grassmannianι_grassmannianIdealLocus E I hI hres U).le))
      ((schemeIdealLocus (I U) (hI U)).subschemeι ≫ toSpec Γ(X, U.val) Γ(E, U.val) k)
      ((grassmannianIdealLocus E I hI hres).subschemeι ≫ grassmannianToBase E k)
      U.property.fromSpec := by
  -- the closed subscheme cut out by `I U` is the inverse image of the glued one, and inverse
  -- images of closed subschemes along a base change are base changes
  have key (J : (grassmannianChart E k U).IdealSheafData)
      (hJ : (grassmannianIdealLocus E I hI hres).comap (grassmannianι E k U) = J) (hle) :
      IsPullback (subschemeMap J (grassmannianIdealLocus E I hI hres) (grassmannianι E k U) hle)
        (J.subschemeι ≫ toSpec Γ(X, U.val) Γ(E, U.val) k)
        ((grassmannianIdealLocus E I hI hres).subschemeι ≫ grassmannianToBase E k)
        U.property.fromSpec := by
    subst hJ
    exact isPullback_subschemeMap_comap _ _ (isPullback_grassmannianι_fromSpec E k U).flip
  exact key _ (comap_grassmannianι_grassmannianIdealLocus E I hI hres U) _

/-- **The universal property of `grassmannianIdealLocus` on points.** For an affine open `U` of
`X`, a `Γ(X, U)`-algebra `A` and a point `N` of `G(k, A ⊗[Γ(X, U)] Γ(E, U); A)`, the morphism
`Spec A ⟶ G(k, E)` classifying `N` through the part over `U` factors through the closed
subscheme exactly when `I U N` vanishes. -/
theorem grassmannianIdealLocus_le_ker_iff (U : X.affineOpens) {A : Type u} [CommRing A]
    [Algebra Γ(X, U.val) A] (N : G(k, A ⊗[Γ(X, U.val)] Γ(E, U.val); A)) :
    grassmannianIdealLocus E I hI hres ≤ (toSchemeHom N ≫ grassmannianι E k U).ker ↔
      I U N = ⊥ := by
  rw [← map_ker, le_map_iff_comap_le, comap_grassmannianι_grassmannianIdealLocus,
    schemeIdealLocus_le_ker_toSchemeHom_iff]

end AlgebraicGeometry.Scheme.Modules
