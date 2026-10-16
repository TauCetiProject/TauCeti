/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import TauCeti.Geometry.RingedSpace.LocallyRingedSpace

/-!
# Descent of morphisms along contractions

Let `c : X ⟶ Y` be a morphism of locally ringed spaces, for instance of schemes, which is a
topological quotient map and for which `𝒪_Y → c_* 𝒪_X` is an isomorphism, that is, every
`Γ(Y, U) ⟶ Γ(X, c⁻¹ U)` is an isomorphism. A proper surjective morphism of schemes with
`c_* 𝒪_X = 𝒪_Y`, such as the contraction of rational tails and bridges of a nodal curve, or the
contraction of an exceptional curve on a surface, is of this kind: a closed surjective continuous
map is a quotient map.

This file shows that such a `c` is a categorical quotient for maps which are constant on its
fibres: a morphism `h : X ⟶ Z` to an arbitrary scheme `Z` whose underlying map is constant on the
fibres of `c` factors uniquely through `c`. The construction uses nothing about schemes, so it is
carried out for locally ringed spaces in `TauCeti.Geometry.RingedSpace.LocallyRingedSpace`
(`AlgebraicGeometry.LocallyRingedSpace.Hom.descOfIsQuotientMap`), and the scheme versions here are
deduced from it; in particular no separatedness of `Z` is needed. A morphism `X ⟶ Z` over a base
`S` which is constant on every geometric fibre of `c` is constant on its set-theoretic fibres,
since each geometric fibre surjects onto the corresponding fibre, so it descends to a morphism
`Y ⟶ Z` over `S`.

The construction is compatible with any commutative square, in particular with base change: if
`c' : X' ⟶ Y'` has the same two properties and `u ≫ c = c' ≫ v`, then the descent of `u ≫ h`
along `c'` is `v` followed by the descent of `h` along `c`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.descOfIsQuotientMap`: the morphism `Y ⟶ Z` of schemes induced by
  a morphism `X ⟶ Z` which is constant on the fibres of `c`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.comp_descOfIsQuotientMap`: the descended morphism factors `h`.
* `AlgebraicGeometry.Scheme.Hom.eq_descOfIsQuotientMap`: it is the only such factorization.
* `AlgebraicGeometry.Scheme.Hom.existsUnique_comp_eq_of_isQuotientMap`: the universal property.
* `AlgebraicGeometry.Scheme.Hom.existsUnique_comp_eq_of_universallyClosed`: the universal
  property for a universally closed surjective `c`, for instance a proper surjective one.
* `AlgebraicGeometry.Scheme.Hom.descOfIsQuotientMap_comp_eq`: descent preserves morphisms over a
  base `S`.
* `AlgebraicGeometry.Scheme.Hom.descOfIsQuotientMap_of_commSq`: compatibility with commutative
  squares, and so with base change.

## References

* The Stacks Project, Tag 0E7B (contractions of nodal curves) and Tag 0E8A (the stabilization of
  a family of nodal curves, where morphisms are descended along such contractions).
-/

public section

open CategoryTheory Opposite Topology TopologicalSpace

namespace AlgebraicGeometry

universe u

namespace Scheme.Hom

variable {X Y Z : Scheme.{u}}

section Desc

variable (c : X ⟶ Y) (hq : IsQuotientMap c) (hc : ∀ U, IsIso (c.app U)) (h : X ⟶ Z)
  (hh : Function.FactorsThrough h c)

/-- **Descent along a contraction.** Let `c : X ⟶ Y` be a topological quotient map for which
`𝒪_Y → c_* 𝒪_X` is an isomorphism. A morphism `h : X ⟶ Z` whose underlying map is constant on the
fibres of `c` induces the morphism `Y ⟶ Z` through which it factors
(`AlgebraicGeometry.Scheme.Hom.comp_descOfIsQuotientMap`). This is the descent of `h` as a
morphism of locally ringed spaces
(`AlgebraicGeometry.LocallyRingedSpace.Hom.descOfIsQuotientMap`). -/
noncomputable def descOfIsQuotientMap : Y ⟶ Z :=
  ⟨c.toLRSHom.descOfIsQuotientMap hq (fun U ↦ hc U.unop) h.toLRSHom hh⟩

/-- The morphism descended along `c` factors the original morphism. -/
@[reassoc (attr := simp)]
theorem comp_descOfIsQuotientMap : c ≫ c.descOfIsQuotientMap hq hc h hh = h :=
  Scheme.Hom.ext' (LocallyRingedSpace.Hom.comp_descOfIsQuotientMap ..)

/-- On points, the morphism descended along `c` sends `c x` to `h x`. -/
@[simp]
theorem descOfIsQuotientMap_apply (x : X) : c.descOfIsQuotientMap hq hc h hh (c x) = h x := by
  rw [← Scheme.Hom.comp_apply, comp_descOfIsQuotientMap]

/-- The morphism descended along `c` is the only morphism through which `h` factors. -/
theorem eq_descOfIsQuotientMap {g : Y ⟶ Z} (hg : c ≫ g = h) :
    g = c.descOfIsQuotientMap hq hc h hh :=
  Scheme.Hom.ext' (LocallyRingedSpace.Hom.eq_descOfIsQuotientMap _ _ _ _ _ congr(($hg).toLRSHom))

/-- Descending a morphism already expressed as a composite through `c` recovers that morphism. -/
@[simp]
theorem descOfIsQuotientMap_comp (g : Y ⟶ Z) (hh' : Function.FactorsThrough (c ≫ g) c) :
    c.descOfIsQuotientMap hq hc (c ≫ g) hh' = g :=
  (eq_descOfIsQuotientMap c hq hc (c ≫ g) hh' rfl).symm

include hq hc hh in
/-- **The universal property of a contraction.** If `c : X ⟶ Y` is a topological quotient map for
which `𝒪_Y → c_* 𝒪_X` is an isomorphism, then every morphism of schemes `h : X ⟶ Z` whose
underlying map is constant on the fibres of `c` factors uniquely through `c`. -/
theorem existsUnique_comp_eq_of_isQuotientMap : ∃! g : Y ⟶ Z, c ≫ g = h :=
  ⟨c.descOfIsQuotientMap hq hc h hh, comp_descOfIsQuotientMap c hq hc h hh,
    fun _ ↦ eq_descOfIsQuotientMap c hq hc h hh⟩

include hc hh in
/-- **The universal property of a contraction**, for a universally closed surjective morphism,
such as a proper surjective one, for which `𝒪_Y → c_* 𝒪_X` is an isomorphism. -/
theorem existsUnique_comp_eq_of_universallyClosed [UniversallyClosed c] [Surjective c] :
    ∃! g : Y ⟶ Z, c ≫ g = h :=
  existsUnique_comp_eq_of_isQuotientMap c
    (c.isClosedMap.isQuotientMap c.continuous c.surjective) hc h hh

/-- Descent along `c` preserves morphisms over a base: if `h` lies over `S` through `Z ⟶ S` and
`c` lies over `S` through `Y ⟶ S`, then so does the descended morphism. -/
@[reassoc]
theorem descOfIsQuotientMap_comp_eq {S : Scheme.{u}} {p : Y ⟶ S} {q : Z ⟶ S}
    (e : h ≫ q = c ≫ p) : c.descOfIsQuotientMap hq hc h hh ≫ q = p :=
  Scheme.Hom.ext' <|
    LocallyRingedSpace.Hom.descOfIsQuotientMap_comp_eq _ _ _ _ _ congr(($e).toLRSHom)

include hh in
/-- Given a commutative square `u ≫ c = c' ≫ v`, if `h` is constant on the fibres of `c`, then
`u ≫ h` is constant on the fibres of `c'`. -/
theorem factorsThrough_comp_of_commSq {X' Y' : Scheme.{u}} {c' : X' ⟶ Y'} {u : X' ⟶ X}
    {v : Y' ⟶ Y} (sq : CommSq u c' c v) : Function.FactorsThrough (u ≫ h) c' :=
  LocallyRingedSpace.Hom.factorsThrough_comp_of_commSq c.toLRSHom h.toLRSHom hh
    ⟨congr(($sq.w).toLRSHom)⟩

/-- **Descent commutes with base change.** Given a commutative square `u ≫ c = c' ≫ v` in which
`c'` is also a topological quotient map that is an isomorphism on sections, for instance the base
change of `c` along `v` when these properties hold universally, the descent of `u ≫ h` along `c'`
is `v` followed by the descent of `h` along `c`. -/
theorem descOfIsQuotientMap_of_commSq {X' Y' : Scheme.{u}} {c' : X' ⟶ Y'} {u : X' ⟶ X}
    {v : Y' ⟶ Y} (sq : CommSq u c' c v) (hq' : IsQuotientMap c') (hc' : ∀ U, IsIso (c'.app U)) :
    c'.descOfIsQuotientMap hq' hc' (u ≫ h) (factorsThrough_comp_of_commSq c h hh sq) =
      v ≫ c.descOfIsQuotientMap hq hc h hh :=
  (eq_descOfIsQuotientMap c' hq' hc' (u ≫ h) _ (by
    rw [← Category.assoc, ← sq.w, Category.assoc, comp_descOfIsQuotientMap])).symm

end Desc

end Scheme.Hom

end AlgebraicGeometry
