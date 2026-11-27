/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import TauCeti.CategoryTheory.Abelian.FunctorCohomology.Basic
public import TauCeti.CategoryTheory.Subfunctor.Basic

/-!
# Zariski descent and partitions for functors on categories of rings

Let `C` be a category whose objects carry commutative rings through a functor
`ι : C ⥤ CommRingCat`, as the test rings of a cohomology theory of functors do. This file states
the two conditions on a coefficient functor `F : C ⥤ AddCommGrpCat` that relate the cohomology of
functors on `C` to the Zariski topology of the rings `ι A`.

* `CategoryTheory.Subfunctor.IsZariskiLocallyTop ι U`: a subfunctor `U` of `Y : C ⥤ Type w` is
  *Zariski-locally everything*: for every point `y ∈ Y(A)` and every maximal ideal `m` of `ι A`
  there is `a ∉ m` such that `y` lands in `U` along every map `f : A ⟶ B` for which `ι f` makes `a`
  a unit.
* `CategoryTheory.HasZariskiDescent ι F`: every Zariski-locally everything subfunctor is dense
  for `F` (`CategoryTheory.Subfunctor.IsDenseFor`).
* `CategoryTheory.HasPartitions ι F`: an object can be cut along each idempotent `e ≠ 1` of its
  ring, by a universal map killing `e` whose ring map is the quotient by `e`; and whenever two maps
  out of `A` identify `ι A` with a product of rings, they identify `F A` with the product of the
  corresponding groups.

The whole functor is Zariski-locally everything, and such subfunctors are stable under enlarging,
under finite intersections, and under restriction along a functor `φ : C' ⥤ C`
(`CategoryTheory.Subfunctor.whiskerLeft`). Over local rings
they contain every point, so every coefficient functor has Zariski descent when all the rings
`ι A` are local (`CategoryTheory.hasZariskiDescent_of_isLocalRing`). A coefficient functor with
partitions vanishes on objects whose ring is zero (`CategoryTheory.HasPartitions.subsingleton`).

## References

* [ShortProof]: `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/Cohomology/Etale/Basic.lean` (declarations `New.Variety.IsZariskiLocallyTop`,
  `New.Variety.HasZariskiDescent`, `New.Variety.HasPartitions`,
  `New.Variety.IsQuotientByElem`, `New.Variety.IsZariskiLocallyTop.whisker`); Apache 2.0,
  Copyright 2026 Anthropic, PBC. The definitions are adapted from these declarations.
-/

public section

open CategoryTheory Abelian

universe t w v u v' u' w'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (ι : C ⥤ CommRingCat.{w'})

/-- A subfunctor `U` of `Y : C ⥤ Type w` is *Zariski-locally everything* for the rings `ι A`: for
every `y ∈ Y(A)` and every maximal ideal `m` of `ι A` there is `a ∉ m` such that `Y(f)(y) ∈ U(B)`
for every `f : A ⟶ B` for which `ι f` sends `a` to a unit. -/
def Subfunctor.IsZariskiLocallyTop {Y : C ⥤ Type w} (U : Subfunctor Y) : Prop :=
  ∀ (A : C) (y : Y.obj A) (m : Ideal (ι.obj A)), m.IsMaximal →
    ∃ a ∉ m, ∀ (B : C) (f : A ⟶ B), IsUnit (ι.map f a) → Y.map f y ∈ U.obj B

/-- A coefficient functor `F` has *Zariski descent* for the rings `ι A` if every subfunctor that is
Zariski-locally everything is dense for `F`. -/
def HasZariskiDescent [HasExt.{t} (C ⥤ AddCommGrpCat.{w})] (F : C ⥤ AddCommGrpCat.{w}) : Prop :=
  ∀ ⦃Y : C ⥤ Type w⦄ (U : Subfunctor Y), U.IsZariskiLocallyTop ι → U.IsDenseFor.{t} F

/-- A coefficient functor `F` has *partitions* for the rings `ι A` if
(i) every idempotent `e ≠ 1` of `ι A` is killed by a map `π : A ⟶ B` through which every map
killing `e` factors uniquely, and `ι π` is onto with kernel inside the ideal `(e)`; and
(ii) whenever two maps `π₁ : A ⟶ B₁` and `π₂ : A ⟶ B₂` identify `ι A` with `ι B₁ × ι B₂`, they
identify `F A` with `F B₁ × F B₂`. -/
structure HasPartitions (F : C ⥤ AddCommGrpCat.{w}) : Prop where
  /-- Every idempotent `e ≠ 1` of `ι A` has a universal map killing it, whose ring map is the
  quotient by `e`. -/
  exists_quotient {A : C} {e : ι.obj A} (he : IsIdempotentElem e) (h1 : e ≠ 1) :
    ∃ (B : C) (π : A ⟶ B), ι.map π e = 0 ∧ Function.Surjective (ι.map π) ∧
      RingHom.ker (ι.map π).hom ≤ Ideal.span {e} ∧
      ∀ ⦃B' : C⦄ (f : A ⟶ B'), ι.map f e = 0 → ∃! g : B ⟶ B', π ≫ g = f
  /-- Two maps that split the ring of `A` as a product split the group `F A` as a product. -/
  bijective_prod {A B₁ B₂ : C} (π₁ : A ⟶ B₁) (π₂ : A ⟶ B₂) :
    Function.Bijective (fun x : ι.obj A ↦ (ι.map π₁ x, ι.map π₂ x)) →
      Function.Bijective (fun x : F.obj A ↦ (F.map π₁ x, F.map π₂ x))

namespace Subfunctor

variable {ι} {Y : C ⥤ Type w}

/-- The whole functor is Zariski-locally everything. -/
lemma isZariskiLocallyTop_top : (⊤ : Subfunctor Y).IsZariskiLocallyTop ι :=
  fun _ _ m _ ↦ ⟨1, fun h ↦ (Ideal.IsMaximal.ne_top ‹_›) ((Ideal.eq_top_iff_one m).2 h),
    fun _ _ _ ↦ Set.mem_univ _⟩

/-- A subfunctor containing a Zariski-locally everything subfunctor is Zariski-locally
everything. -/
lemma IsZariskiLocallyTop.mono {U V : Subfunctor Y} (hU : U.IsZariskiLocallyTop ι) (h : U ≤ V) :
    V.IsZariskiLocallyTop ι := fun A y m hm ↦ by
  obtain ⟨a, ha, hU⟩ := hU A y m hm
  exact ⟨a, ha, fun B f hf ↦ h B (hU B f hf)⟩

/-- The intersection of two Zariski-locally everything subfunctors is Zariski-locally everything:
the product of two elements outside a maximal ideal lies outside it, and it becomes a unit only if
both factors do. -/
lemma IsZariskiLocallyTop.inf {U V : Subfunctor Y} (hU : U.IsZariskiLocallyTop ι)
    (hV : V.IsZariskiLocallyTop ι) : (U ⊓ V).IsZariskiLocallyTop ι := fun A y m hm ↦ by
  obtain ⟨a, ha, hU⟩ := hU A y m hm
  obtain ⟨b, hb, hV⟩ := hV A y m hm
  refine ⟨a * b, fun h ↦ (hm.isPrime.mem_or_mem h).elim ha hb, fun B f hf ↦ ?_⟩
  rw [map_mul] at hf
  exact ⟨hU B f (isUnit_of_mul_isUnit_left hf), hV B f (isUnit_of_mul_isUnit_right hf)⟩

/-- Restricting along `φ : C' ⥤ C` preserves being Zariski-locally everything, for the rings
`ι (φ A')`. -/
lemma IsZariskiLocallyTop.whiskerLeft {C' : Type u'} [Category.{v'} C'] (φ : C' ⥤ C)
    {U : Subfunctor Y} (hU : U.IsZariskiLocallyTop ι) :
    (U.whiskerLeft φ).IsZariskiLocallyTop (φ ⋙ ι) := fun A y m hm ↦ by
  obtain ⟨a, ha, hU⟩ := hU (φ.obj A) y m hm
  exact ⟨a, ha, fun B f hf ↦ (U.mem_whiskerLeft_obj_iff φ _).2 (hU (φ.obj B) (φ.map f) hf)⟩

/-- Over a local ring a Zariski-locally everything subfunctor contains every point: an element
outside the maximal ideal is already a unit. -/
lemma IsZariskiLocallyTop.mem_of_isLocalRing {U : Subfunctor Y} (hU : U.IsZariskiLocallyTop ι)
    {A : C} [IsLocalRing (ι.obj A)] (y : Y.obj A) : y ∈ U.obj A := by
  obtain ⟨a, ha, h⟩ := hU A y _ (IsLocalRing.maximalIdeal.isMaximal _)
  have ha : IsUnit a := of_not_not fun h' ↦ ha ((IsLocalRing.mem_maximalIdeal a).2 h')
  simpa using h A (𝟙 A) (by simpa using ha)

end Subfunctor

/-- If every ring `ι A` is local, every coefficient functor has Zariski descent: a
Zariski-locally everything subfunctor is then the whole functor. -/
lemma hasZariskiDescent_of_isLocalRing [HasExt.{t} (C ⥤ AddCommGrpCat.{w})]
    [∀ A, IsLocalRing (ι.obj A)] (F : C ⥤ AddCommGrpCat.{w}) : HasZariskiDescent.{t} ι F :=
  fun Y U hU ↦ by
    obtain rfl : U = ⊤ := le_antisymm le_top fun _ y _ ↦ hU.mem_of_isLocalRing y
    exact Subfunctor.isDenseFor_top Y

variable {ι} in
/-- A coefficient functor with partitions vanishes on every object whose ring is zero: the two
copies of the identity split the zero ring as a product, so they split `F A` as `F A × F A`. -/
lemma HasPartitions.subsingleton {F : C ⥤ AddCommGrpCat.{w}} (hF : HasPartitions ι F) {A : C}
    [Subsingleton (ι.obj A)] : Subsingleton (F.obj A) := by
  have h := (hF.bijective_prod (𝟙 A) (𝟙 A)
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩).2
  have hzero (a : F.obj A) : a = 0 := by
    obtain ⟨x, hx⟩ := h (0, a)
    exact (Prod.ext_iff.1 hx).2.symm.trans (Prod.ext_iff.1 hx).1
  exact ⟨fun a b ↦ (hzero a).trans (hzero b).symm⟩

end CategoryTheory
