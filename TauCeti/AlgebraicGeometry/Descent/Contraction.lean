/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import TauCeti.Geometry.RingedSpace.PresheafedSpace.Basic

/-!
# Descent of morphisms along contractions

Let `c : X ⟶ Y` be a morphism of locally ringed spaces, for instance of schemes, which is a
topological quotient map and for which `𝒪_Y → c_* 𝒪_X` is an isomorphism, that is, every
`Γ(Y, U) ⟶ Γ(X, c⁻¹ U)` is an isomorphism. A proper surjective morphism of schemes with
`c_* 𝒪_X = 𝒪_Y`, such as the contraction of rational tails and bridges of a nodal curve, or the
contraction of an exceptional curve on a surface, is of this kind: a closed surjective continuous
map is a quotient map.

This file shows that such a `c` is a categorical quotient for maps which are constant on its
fibres: a morphism `h : X ⟶ Z` to an arbitrary locally ringed space `Z` whose underlying map is
constant on the fibres of `c` factors uniquely through `c`. The construction uses nothing about
schemes, so it is carried out for locally ringed spaces and the scheme versions are deduced from
it; in particular no separatedness of `Z` is needed. For schemes, a morphism `X ⟶ Z` over a base
`S` which is constant on every geometric fibre of `c` is constant on its set-theoretic fibres,
since each geometric fibre surjects onto the corresponding fibre, so it descends to a morphism
`Y ⟶ Z` over `S`.

The underlying continuous map of the descended morphism `g : Y ⟶ Z` is the map induced by the
quotient map `c`. On sections over an open `W ⊆ Z`, it is the composite
`Γ(Z, W) ⟶ Γ(X, h⁻¹ W) ⟶ Γ(X, c⁻¹ g⁻¹ W) ≅ Γ(Y, g⁻¹ W)`, using `c⁻¹ g⁻¹ W ⊆ h⁻¹ W` and the
inverse of `c` on sections. The composite `c ≫ g` is then `h` as a morphism of presheafed spaces.
Every point of `Y` is `c x` for some `x`, and the stalk map of `h` at `x` is the stalk map of `g`
at `c x` followed by that of `c` at `x`, so the stalk maps of `g` are local because those of `h`
are. Uniqueness holds because `c` is surjective and injective on sections, hence an epimorphism
(`AlgebraicGeometry.PresheafedSpace.epi_of_base_surjective_of_c_app_mono`).

The construction is compatible with any commutative square, in particular with base change: if
`c' : X' ⟶ Y'` has the same two properties and `u ≫ c = c' ≫ v`, then the descent of `u ≫ h`
along `c'` is `v` followed by the descent of `h` along `c`.

## Main definitions

* `AlgebraicGeometry.LocallyRingedSpace.Hom.descOfIsQuotientMap`: the morphism `Y ⟶ Z` of locally
  ringed spaces induced by a morphism `X ⟶ Z` which is constant on the fibres of `c`.
* `AlgebraicGeometry.Scheme.Hom.descOfIsQuotientMap`: the same construction for schemes.

## Main results

Each of the following is stated in `AlgebraicGeometry.LocallyRingedSpace.Hom` and, for schemes,
in `AlgebraicGeometry.Scheme.Hom`.

* `comp_descOfIsQuotientMap`: the descended morphism factors `h`.
* `eq_descOfIsQuotientMap`: it is the only such factorization.
* `existsUnique_comp_eq_of_isQuotientMap`: the universal property.
* `descOfIsQuotientMap_comp_eq`: descent preserves morphisms over a base `S`.
* `descOfIsQuotientMap_of_commSq`: compatibility with commutative squares, and so with base
  change.

For schemes, `AlgebraicGeometry.Scheme.Hom.existsUnique_comp_eq_of_universallyClosed` gives the
universal property for a universally closed surjective `c`, for instance a proper surjective one.

## References

* The Stacks Project, Tag 0E7B (contractions of nodal curves) and Tag 0E8A (the stabilization of
  a family of nodal curves, where morphisms are descended along such contractions).
-/

public section

open CategoryTheory Opposite Topology TopologicalSpace

namespace AlgebraicGeometry

universe u

namespace LocallyRingedSpace.Hom

variable {X Y Z : LocallyRingedSpace.{u}}

section Desc

variable (c : X ⟶ Y) (hq : IsQuotientMap c.base) (hc : ∀ U, IsIso (c.c.app U)) (h : X ⟶ Z)
  (hh : Function.FactorsThrough h.base c.base)

/-- The continuous map `Y → Z` induced by `h` along the quotient map `c`. -/
private noncomputable def descBase : Y.toTopCat ⟶ Z.toTopCat :=
  TopCat.ofHom (hq.lift h.base.hom hh)

private theorem comp_descBase : c.base ≫ descBase c hq h hh = h.base := by
  ext x
  exact congr($(hq.lift_comp h.base.hom hh) x)

private theorem preimage_descBase_le (W : Opens Z) :
    (Opens.map c.base).obj ((Opens.map (descBase c hq h hh)).obj W) ≤ (Opens.map h.base).obj W := by
  intro x hx
  simpa [← comp_descBase c hq h hh] using hx

/-- Restricting a section to a smaller open and back again, along any two inclusions, is the
identity; the opens of a space form a thin category. -/
private theorem presheaf_map_map_eq_self {C : Type*} [Category* C] {T : TopCat.{u}}
    {F : TopCat.Presheaf C T} {A : C} {V V' : Opens T} (a : A ⟶ F.obj (op V))
    (i : op V ⟶ op V') (j : op V' ⟶ op V) : (a ≫ F.map i) ≫ F.map j = a := by
  rw [Category.assoc, ← F.map_comp, Subsingleton.elim (i ≫ j) (𝟙 _), F.map_id, Category.comp_id]

/-- The descended morphism as a morphism of presheafed spaces: on sections over `W` it maps
`Γ(Z, W)` to `Γ(X, c⁻¹ g⁻¹ W)` by `h`, and then back to `Γ(Y, g⁻¹ W)` by the inverse of `c`. -/
private noncomputable def descPsh : Y.toPresheafedSpace ⟶ Z.toPresheafedSpace where
  base := descBase c hq h hh
  c :=
    { app W := (h.c.app W ≫ X.presheaf.map (homOfLE (preimage_descBase_le c hq h hh W.unop)).op) ≫
        inv (c.c.app (op ((Opens.map (descBase c hq h hh)).obj W.unop)))
      naturality W W' i := by
        rw [← cancel_mono (c.c.app _)]
        simp [← Functor.map_comp]
        congr 2 }

/-- On sections over `W`, the composite `c ≫ g` is the restriction of `h` from `h⁻¹ W` to
`c⁻¹ g⁻¹ W`, since the inverse of `c` on sections cancels against `c`. -/
private theorem comp_descPsh_c_app (W : Opens Z) :
    (c.toHom ≫ descPsh c hq hc h hh).c.app (op W) =
      h.c.app (op W) ≫ X.presheaf.map (homOfLE (preimage_descBase_le c hq h hh W)).op :=
  ((Category.assoc _ _ _).trans (congrArg _ (@IsIso.inv_hom_id _ _ _ _ _ (hc _)))).trans
    (Category.comp_id _)

private theorem comp_descPsh : c.toHom ≫ descPsh c hq hc h hh = h.toHom := by
  refine PresheafedSpace.ext_of_app (comp_descBase c hq h hh) fun W ↦ ?_
  rw [comp_descPsh_c_app]
  exact presheaf_map_map_eq_self _ _ _

private theorem isLocalHom_stalkMap_descPsh (y : Y) :
    IsLocalHom ((descPsh c hq hc h hh).stalkMap y).hom := by
  obtain ⟨x, rfl⟩ := hq.surjective y
  have : IsLocalHom ((c.toHom ≫ descPsh c hq hc h hh).stalkMap x).hom := by
    rw [PresheafedSpace.stalkMap.congr_hom _ _ (comp_descPsh c hq hc h hh) x,
      CommRingCat.hom_comp]
    have := isLocalHom_of_isIso (eqToHom (comp_descPsh c hq hc h hh ▸ rfl :
      Z.presheaf.stalk ((c.toHom ≫ descPsh c hq hc h hh).base x) =
        Z.presheaf.stalk (h.base x)))
    exact CommRingCat.isLocalHom_comp _ _
  rw [PresheafedSpace.stalkMap.comp] at this
  have : IsLocalHom ((c.toHom.stalkMap x).hom.comp
      ((descPsh c hq hc h hh).stalkMap (c.base x)).hom) := this
  exact isLocalHom_of_comp _ (c.toHom.stalkMap x).hom

/-- **Descent along a contraction.** Let `c : X ⟶ Y` be a topological quotient map for which
`𝒪_Y → c_* 𝒪_X` is an isomorphism. A morphism `h : X ⟶ Z` of locally ringed spaces whose
underlying map is constant on the fibres of `c` induces the morphism `Y ⟶ Z` through which it
factors (`AlgebraicGeometry.LocallyRingedSpace.Hom.comp_descOfIsQuotientMap`). -/
noncomputable def descOfIsQuotientMap : Y ⟶ Z :=
  ⟨descPsh c hq hc h hh, isLocalHom_stalkMap_descPsh c hq hc h hh⟩

/-- The morphism descended along `c` factors the original morphism. -/
@[reassoc (attr := simp)]
theorem comp_descOfIsQuotientMap : c ≫ c.descOfIsQuotientMap hq hc h hh = h :=
  LocallyRingedSpace.Hom.ext' (comp_descPsh c hq hc h hh)

include hq hc in
/-- A quotient map of locally ringed spaces which is an isomorphism on sections is an
epimorphism. -/
private theorem epi_of_isQuotientMap : Epi c := by
  apply Functor.epi_of_epi_map LocallyRingedSpace.forgetToSheafedSpace
  apply Functor.epi_of_epi_map SheafedSpace.forgetToPresheafedSpace
  exact PresheafedSpace.epi_of_base_surjective_of_c_app_mono _ hq.surjective fun U ↦
    (hc U).mono_of_iso

/-- The morphism descended along `c` is the only morphism through which `h` factors. -/
theorem eq_descOfIsQuotientMap {g : Y ⟶ Z} (hg : c ≫ g = h) :
    g = c.descOfIsQuotientMap hq hc h hh := by
  have := epi_of_isQuotientMap c hq hc
  rw [← cancel_epi c, hg, comp_descOfIsQuotientMap]

/-- Descending a morphism already expressed as a composite through `c` recovers that morphism. -/
@[simp]
theorem descOfIsQuotientMap_comp (g : Y ⟶ Z) (hh' : Function.FactorsThrough (c ≫ g).base c.base) :
    c.descOfIsQuotientMap hq hc (c ≫ g) hh' = g :=
  (eq_descOfIsQuotientMap c hq hc (c ≫ g) hh' rfl).symm

include hq hc hh in
/-- **The universal property of a contraction.** If `c : X ⟶ Y` is a topological quotient map for
which `𝒪_Y → c_* 𝒪_X` is an isomorphism, then every morphism of locally ringed spaces
`h : X ⟶ Z` whose underlying map is constant on the fibres of `c` factors uniquely through `c`. -/
theorem existsUnique_comp_eq_of_isQuotientMap : ∃! g : Y ⟶ Z, c ≫ g = h :=
  ⟨c.descOfIsQuotientMap hq hc h hh, comp_descOfIsQuotientMap c hq hc h hh,
    fun _ ↦ eq_descOfIsQuotientMap c hq hc h hh⟩

/-- Descent along `c` preserves morphisms over a base: if `h` lies over `S` through `Z ⟶ S` and
`c` lies over `S` through `Y ⟶ S`, then so does the descended morphism. -/
@[reassoc]
theorem descOfIsQuotientMap_comp_eq {S : LocallyRingedSpace.{u}} {p : Y ⟶ S} {q : Z ⟶ S}
    (e : h ≫ q = c ≫ p) : c.descOfIsQuotientMap hq hc h hh ≫ q = p := by
  have := epi_of_isQuotientMap c hq hc
  rw [← cancel_epi c, comp_descOfIsQuotientMap_assoc, e]

/-- **Descent commutes with base change.** Given a commutative square `u ≫ c = c' ≫ v` in which
`c'` is also a topological quotient map that is an isomorphism on sections, the descent of
`u ≫ h` along `c'` is `v` followed by the descent of `h` along `c`. -/
theorem descOfIsQuotientMap_of_commSq {X' Y' : LocallyRingedSpace.{u}} {c' : X' ⟶ Y'}
    {u : X' ⟶ X} {v : Y' ⟶ Y} (sq : CommSq u c' c v) (hq' : IsQuotientMap c'.base)
    (hc' : ∀ U, IsIso (c'.c.app U)) (hh' : Function.FactorsThrough (u ≫ h).base c'.base) :
    c'.descOfIsQuotientMap hq' hc' (u ≫ h) hh' = v ≫ c.descOfIsQuotientMap hq hc h hh :=
  (eq_descOfIsQuotientMap c' hq' hc' (u ≫ h) hh' (by
    rw [← Category.assoc, ← sq.w, Category.assoc, comp_descOfIsQuotientMap])).symm

end Desc

end LocallyRingedSpace.Hom

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

/-- **Descent commutes with base change.** Given a commutative square `u ≫ c = c' ≫ v` in which
`c'` is also a topological quotient map that is an isomorphism on sections, for instance the base
change of `c` along `v` when these properties hold universally, the descent of `u ≫ h` along `c'`
is `v` followed by the descent of `h` along `c`. -/
theorem descOfIsQuotientMap_of_commSq {X' Y' : Scheme.{u}} {c' : X' ⟶ Y'} {u : X' ⟶ X}
    {v : Y' ⟶ Y} (sq : CommSq u c' c v) (hq' : IsQuotientMap c') (hc' : ∀ U, IsIso (c'.app U))
    (hh' : Function.FactorsThrough (u ≫ h) c') :
    c'.descOfIsQuotientMap hq' hc' (u ≫ h) hh' = v ≫ c.descOfIsQuotientMap hq hc h hh :=
  (eq_descOfIsQuotientMap c' hq' hc' (u ≫ h) hh' (by
    rw [← Category.assoc, ← sq.w, Category.assoc, comp_descOfIsQuotientMap])).symm

end Desc

end Scheme.Hom

end AlgebraicGeometry
