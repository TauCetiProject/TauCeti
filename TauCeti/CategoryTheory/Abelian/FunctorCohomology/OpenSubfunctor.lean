/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import TauCeti.CategoryTheory.Abelian.FunctorCohomology.ZariskiDescent

import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Ideal

/-!
# Separated functors and open subfunctors

Let `C` be a category whose objects carry commutative rings through a functor
`ι : C ⥤ CommRingCat`, for instance the commutative rings themselves (`ι = 𝟭`) or the commutative
algebras over a ring `k` (`ι` the forgetful functor). This file defines two conditions on functors
`X : C ⥤ Type w` that read the Zariski topology of the rings `ι A` through the points of `X`.

* `CategoryTheory.Functor.IsSeparated X ι`: `X` is *separated*, or has a *closed diagonal*: for
  any two points `x, y ∈ X(A)` there is an ideal `J` of `ι A` such that a map `f : A ⟶ B` makes
  the images of `x` and `y` in `X(B)` agree exactly when `ι f` kills `J`.
* `CategoryTheory.Subfunctor.IsOpen ι V`: a subfunctor `V` of `X` is *open*: every point
  `x ∈ X(A)` has an ideal `I` of `ι A` such that the image of `x` in `X(B)` along `f : A ⟶ B` lies
  in `V` exactly when `ι f` sends `I` to the unit ideal of `ι B`.

For the functor of points of a scheme these are the separatedness of the scheme and the openness
of a subscheme, tested on affine schemes; the equality locus of two points, resp. the preimage of
the open subscheme, is the closed subscheme cut out by `J`, resp. the complement of the closed
subscheme cut out by `I`.

## Main results

* `CategoryTheory.Functor.IsSeparated.of_mono`: a functor with a monomorphism to a separated
  functor is separated; in particular subfunctors of separated functors are separated.
* `CategoryTheory.Functor.CorepresentableBy.isSeparated`: a corepresentable functor is separated
  when `ι` is faithful.
* `CategoryTheory.Subfunctor.isOpen_top`, `CategoryTheory.Subfunctor.IsOpen.inf`,
  `CategoryTheory.Subfunctor.IsOpen.preimage`: the whole functor is open, and open subfunctors
  are stable under finite intersections and preimages. Both notions are stable under restriction
  along a functor `φ : C' ⥤ C`.
* `CategoryTheory.Functor.CorepresentableBy.basicOpen`: for a functor corepresented by `R` and
  `r ∈ ι R`, the open subfunctor of points along which `r` becomes a unit, with
  `basicOpen_one` and `basicOpen_mul`.
* `CategoryTheory.Subfunctor.isZariskiLocallyTop_iSup_of_isOpen`: open subfunctors that together
  contain every point after passing to a residue object of each maximal ideal have a union that is
  Zariski-locally everything; `isZariskiLocallyTop_iSup_of_isOpen_of_isField` is the case of
  functors on `k`-algebras, where it suffices that they contain all points with values in fields.
* `CategoryTheory.Subfunctor.IsOpen.image_ι`: for functors on `k`-algebras, openness is
  transitive: an open subfunctor of an open subfunctor of `X` is open in `X`. The ideal cutting
  it out at a point is assembled from ideals over localizations and checked at residue fields.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., Mathematical Surveys and
  Monographs 107, American Mathematical Society, 2003, Part I, Chapter 1 (open and closed
  subfunctors of `k`-functors).
* M. Demazure, P. Gabriel, *Groupes algébriques I*, Masson, 1970, Chapitre I, §1 (sous-foncteurs
  ouverts et fermés).
* `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/General/Geometry/EtaleCharts.lean` (declarations `New.Variety.IsSeparatedFunctor`,
  `New.Variety.IsOpenSubfunctor`); Apache 2.0, Copyright 2026 Anthropic, PBC. The definitions are
  adapted from these declarations and stated for an arbitrary category with a ring-valued functor.
-/

public section

open CategoryTheory Opposite

universe w v u v' u' w' u''

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A functor `X : C ⥤ Type w` is *separated* for the rings `ι A`, or has a *closed diagonal*, if
for all points `x, y ∈ X(A)` there is an ideal `J` of `ι A` such that a map `f : A ⟶ B` makes
`X(f)(x) = X(f)(y)` exactly when `ι f` kills `J`. -/
def Functor.IsSeparated (X : C ⥤ Type w) (ι : C ⥤ CommRingCat.{w'}) : Prop :=
  ∀ ⦃A : C⦄ (x y : X.obj A), ∃ J : Ideal (ι.obj A), ∀ ⦃B : C⦄ (f : A ⟶ B),
    X.map f x = X.map f y ↔ J ≤ RingHom.ker (ι.map f).hom

/-- A subfunctor `V` of `X : C ⥤ Type w` is *open* for the rings `ι A` if every point `x ∈ X(A)`
has an ideal `I` of `ι A` such that, for every map `f : A ⟶ B`, `X(f)(x)` lies in `V(B)` exactly
when `ι f` sends `I` to the unit ideal of `ι B`. -/
def Subfunctor.IsOpen (ι : C ⥤ CommRingCat.{w'}) {X : C ⥤ Type w} (V : Subfunctor X) : Prop :=
  ∀ ⦃A : C⦄ (x : X.obj A), ∃ I : Ideal (ι.obj A), ∀ ⦃B : C⦄ (f : A ⟶ B),
    X.map f x ∈ V.obj B ↔ I.map (ι.map f).hom = ⊤

variable {ι : C ⥤ CommRingCat.{w'}} {X X' : C ⥤ Type w}

/-- Unfolds `CategoryTheory.Functor.IsSeparated`. -/
lemma Functor.isSeparated_iff : X.IsSeparated ι ↔ ∀ ⦃A : C⦄ (x y : X.obj A),
    ∃ J : Ideal (ι.obj A), ∀ ⦃B : C⦄ (f : A ⟶ B),
      X.map f x = X.map f y ↔ J ≤ RingHom.ker (ι.map f).hom :=
  Iff.rfl

/-- Unfolds `CategoryTheory.Subfunctor.IsOpen`. -/
lemma Subfunctor.isOpen_iff {V : Subfunctor X} : V.IsOpen ι ↔ ∀ ⦃A : C⦄ (x : X.obj A),
    ∃ I : Ideal (ι.obj A), ∀ ⦃B : C⦄ (f : A ⟶ B), X.map f x ∈ V.obj B ↔ I.map (ι.map f).hom = ⊤ :=
  Iff.rfl

/-! ### Separated functors -/

namespace Functor.IsSeparated

/-- A functor with a monomorphism to a separated functor is separated. In particular every
subfunctor of a separated functor is separated (`hX.of_mono V.ι`). -/
lemma of_mono (hX : X.IsSeparated ι) (g : X' ⟶ X) [Mono g] : X'.IsSeparated ι := by
  intro A x y
  obtain ⟨J, hJ⟩ := hX (g.app A x) (g.app A y)
  refine ⟨J, fun B f ↦ ?_⟩
  rw [← hJ f, ← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
  exact ((mono_iff_injective (g.app B)).1 inferInstance).eq_iff.symm

/-- Restricting a separated functor along `φ : C' ⥤ C` gives a separated functor, for the rings
`ι (φ A')`. -/
lemma whiskerLeft (hX : X.IsSeparated ι) {C' : Type u'} [Category.{v'} C'] (φ : C' ⥤ C) :
    (φ ⋙ X).IsSeparated (φ ⋙ ι) := fun A x y ↦ by
  obtain ⟨J, hJ⟩ := hX x y
  exact ⟨J, fun B f ↦ hJ (φ.map f)⟩

end Functor.IsSeparated

/-- A functor corepresented by an object `R` is separated when `ι` is faithful: two points
`x, y ∈ X(A)` are maps `φ, ψ : R ⟶ A`, and they agree after `f : A ⟶ B` exactly when `ι f` kills
the ideal generated by the differences `ι φ r - ι ψ r`. -/
lemma Functor.CorepresentableBy.isSeparated [ι.Faithful] {R : C} (e : X.CorepresentableBy R) :
    X.IsSeparated ι := by
  intro A x y
  refine ⟨Ideal.span (Set.range fun r ↦ ι.map (e.homEquiv.symm x) r -
    ι.map (e.homEquiv.symm y) r), fun B f ↦ ?_⟩
  rw [← e.homEquiv.symm.injective.eq_iff, ← e.homEquiv_symm_comp, ← e.homEquiv_symm_comp,
    ← ι.map_injective.eq_iff, Ideal.span_le, Set.range_subset_iff, CommRingCat.hom_ext_iff,
    RingHom.ext_iff]
  simp [sub_eq_zero]

/-! ### Open subfunctors -/

namespace Subfunctor

/-- The whole functor is an open subfunctor of itself. -/
lemma isOpen_top : (⊤ : Subfunctor X).IsOpen ι :=
  fun _ _ ↦ ⟨⊤, fun _ f ↦ by simp [Ideal.map_top]⟩

/-- The intersection of two open subfunctors is open: the ideal of a point is the product of the
two ideals, which is sent to the unit ideal exactly when both are. -/
lemma IsOpen.inf {U V : Subfunctor X} (hU : U.IsOpen ι) (hV : V.IsOpen ι) :
    (U ⊓ V).IsOpen ι := fun A x ↦ by
  obtain ⟨I, hI⟩ := hU x
  obtain ⟨J, hJ⟩ := hV x
  refine ⟨I * J, fun B f ↦ ?_⟩
  rw [Ideal.map_mul, min_obj, Set.mem_inter_iff, hI f, hJ f]
  refine ⟨fun ⟨h₁, h₂⟩ ↦ by rw [h₁, h₂, Ideal.top_mul], fun h ↦ ⟨?_, ?_⟩⟩
  · exact top_le_iff.1 (h ▸ Ideal.mul_le_left)
  · exact top_le_iff.1 (h ▸ Ideal.mul_le_right)

/-- The preimage of an open subfunctor along a map of functors is open. -/
lemma IsOpen.preimage {V : Subfunctor X} (hV : V.IsOpen ι) (g : X' ⟶ X) :
    (V.preimage g).IsOpen ι := fun A x ↦ by
  obtain ⟨I, hI⟩ := hV (g.app A x)
  refine ⟨I, fun B f ↦ ?_⟩
  rw [preimage_obj, Set.mem_preimage, NatTrans.naturality_apply, hI f]

/-- Restricting an open subfunctor along `φ : C' ⥤ C` gives an open subfunctor, for the rings
`ι (φ A')`. -/
lemma IsOpen.whiskerLeft {V : Subfunctor X} (hV : V.IsOpen ι) {C' : Type u'} [Category.{v'} C']
    (φ : C' ⥤ C) : (V.whiskerLeft φ).IsOpen (φ ⋙ ι) := fun A x ↦ by
  obtain ⟨I, hI⟩ := hV x
  exact ⟨I, fun B f ↦ (V.mem_whiskerLeft_obj_iff φ _).trans (hI (φ.map f))⟩

/-- Open subfunctors `V j` have a Zariski-locally everything union as soon as at each maximal
ideal `m` of `ι A`, every point `x ∈ X(A)` lies in some `V j` after a map `π : A ⟶ B` that keeps
`m` proper, such as the map to the residue field at `m`. The ideal of `x` for `V j` then contains
an element outside `m`, and `x` lies in `V j` wherever that element becomes a unit. -/
lemma isZariskiLocallyTop_iSup_of_isOpen {J : Sort*} {V : J → Subfunctor X}
    (hV : ∀ j, (V j).IsOpen ι)
    (h : ∀ ⦃A : C⦄ (x : X.obj A) (m : Ideal (ι.obj A)), m.IsMaximal →
      ∃ (B : C) (π : A ⟶ B) (j : J), m.map (ι.map π).hom ≠ ⊤ ∧ X.map π x ∈ (V j).obj B) :
    (⨆ j, V j).IsZariskiLocallyTop ι := by
  rw [isZariskiLocallyTop_iff]
  intro A x m hm
  obtain ⟨B, π, j, hπ, hx⟩ := h x m hm
  obtain ⟨I, hI⟩ := hV j x
  obtain ⟨a, haI, ham⟩ : ∃ a ∈ I, a ∉ m := by
    by_contra! H
    exact hπ (top_le_iff.1 ((hI π).1 hx ▸ Ideal.map_mono H))
  refine ⟨a, ham, fun B' f hf ↦ ?_⟩
  rw [iSup_obj, Set.mem_iUnion]
  exact ⟨j, (hI f).2 (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ haI) hf)⟩

end Subfunctor

/-! ### Basic open subfunctors of corepresentable functors -/

namespace Functor.CorepresentableBy

variable {R : C} (e : X.CorepresentableBy R)

variable (ι) in
/-- For a functor `X` corepresented by `R` and an element `r ∈ ι R`, the *basic open* subfunctor
`D(r)` of `X`: the points `x ∈ X(A)`, that is the maps `R ⟶ A`, along which `r` becomes a unit. -/
def basicOpen (r : ι.obj R) : Subfunctor X where
  obj A := {x | IsUnit (ι.map (e.homEquiv.symm x) r)}
  map {A B} f x hx := by
    simpa [Set.mem_preimage, ← e.homEquiv_symm_comp] using hx.map (ι.map f).hom

/-- A point lies in `D(r)` exactly when the corresponding map sends `r` to a unit. -/
@[simp]
lemma mem_basicOpen_obj_iff {r : ι.obj R} {A : C} {x : X.obj A} :
    x ∈ (e.basicOpen ι r).obj A ↔ IsUnit (ι.map (e.homEquiv.symm x) r) :=
  Iff.rfl

variable (ι) in
/-- A basic open subfunctor is open: at a point `x`, its ideal is generated by the image of `r`
along the map corresponding to `x`. -/
lemma isOpen_basicOpen (r : ι.obj R) : (e.basicOpen ι r).IsOpen ι := fun A x ↦ by
  refine ⟨Ideal.span {ι.map (e.homEquiv.symm x) r}, fun B f ↦ ?_⟩
  rw [mem_basicOpen_obj_iff, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top,
    ← e.homEquiv_symm_comp, Functor.map_comp, CommRingCat.comp_apply]

/-- The basic open subfunctor of `1` is the whole functor. -/
@[simp]
lemma basicOpen_one : e.basicOpen ι 1 = ⊤ := by
  ext A x
  simp

/-- The basic open subfunctor of a product is the intersection of the basic open subfunctors of
the factors. -/
@[simp]
lemma basicOpen_mul (r s : ι.obj R) :
    e.basicOpen ι (r * s) = e.basicOpen ι r ⊓ e.basicOpen ι s := by
  ext A x
  simp [IsUnit.mul_iff]

end Functor.CorepresentableBy

/-! ### Functors on commutative algebras -/

namespace Subfunctor

variable {k : Type u''} [CommRing k] {X : CommAlgCat.{u} k ⥤ Type w}

/-- For functors on commutative `k`-algebras, openness is read with ideals of the algebras
themselves. -/
lemma isOpen_forget₂_iff {V : Subfunctor X} :
    V.IsOpen (forget₂ (CommAlgCat.{u} k) CommRingCat.{u}) ↔
      ∀ ⦃A : CommAlgCat.{u} k⦄ (x : X.obj A), ∃ I : Ideal A, ∀ ⦃B : CommAlgCat.{u} k⦄ (f : A ⟶ B),
        X.map f x ∈ V.obj B ↔ I.map f.hom = ⊤ :=
  Iff.rfl

/-- Open subfunctors of a functor on commutative `k`-algebras that together contain every point
with values in a field have a Zariski-locally everything union: the residue fields `A ⧸ m` of an
algebra `A` provide the maps required by `isZariskiLocallyTop_iSup_of_isOpen`. -/
lemma isZariskiLocallyTop_iSup_of_isOpen_of_isField {J : Sort*} {V : J → Subfunctor X}
    (hV : ∀ j, (V j).IsOpen (forget₂ (CommAlgCat.{u} k) CommRingCat.{u}))
    (h : ∀ (K : CommAlgCat.{u} k), IsField K → ∀ x : X.obj K, ∃ j, x ∈ (V j).obj K) :
    (⨆ j, V j).IsZariskiLocallyTop (forget₂ (CommAlgCat.{u} k) CommRingCat.{u}) := by
  refine isZariskiLocallyTop_iSup_of_isOpen hV fun A x m hm ↦ ?_
  -- `m` is an ideal of `A` itself, read through the forgetful functor
  let m' : Ideal A := m
  have hK : IsField (A ⧸ m') := (Ideal.Quotient.maximal_ideal_iff_isField_quotient m').1 hm
  let π : A ⟶ CommAlgCat.of k (A ⧸ m') := CommAlgCat.ofHom (Ideal.Quotient.mkₐ k m')
  obtain ⟨j, hj⟩ := h _ hK (X.map π x)
  refine ⟨_, π, j, ?_, hj⟩
  have : Nontrivial (A ⧸ m') := hK.nontrivial
  have h₀ : m'.map (Ideal.Quotient.mk m') ≠ ⊤ := by
    rw [Ideal.map_quotient_self]
    exact bot_ne_top
  exact h₀

/-- A map of `k`-algebras that sends `a` to a unit factors through the localization `A[1/a]`. -/
private lemma exists_away_comp_eq {A B : CommAlgCat.{u} k} (f : A ⟶ B) {a : A}
    (ha : IsUnit (f a)) : ∃ g : CommAlgCat.of k (Localization.Away a) ⟶ B,
      CommAlgCat.ofHom (IsScalarTower.toAlgHom k A (Localization.Away a)) ≫ g = f :=
  ⟨CommAlgCat.ofHom (IsLocalization.Away.liftAlgHom (f := f.hom) a ha), by
    ext b
    exact IsLocalization.Away.lift_eq a ha b⟩

/-- Extending an ideal along a composite of maps of `k`-algebras extends it in two steps. -/
private lemma map_comp_hom {A B B' : CommAlgCat.{u} k} (T : Ideal A) (f : A ⟶ B) (g : B ⟶ B') :
    T.map (f ≫ g).hom = (T.map f.hom).map g.hom := by
  rw [CommAlgCat.hom_comp, ← Ideal.map_coe (g.hom.comp f.hom), AlgHom.comp_toRingHom,
    ← Ideal.map_map, Ideal.map_coe, Ideal.map_coe]

/-- The quotient map `B ⟶ B ⧸ 𝔫` sends every ideal contained in `𝔫` to zero. -/
private lemma map_quotient_eq_bot {B : CommAlgCat.{u} k} {T 𝔫 : Ideal B} (h : T ≤ 𝔫) :
    T.map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ k 𝔫)).hom = ⊥ := by
  rw [Ideal.map_eq_bot_iff_le_ker]
  intro c hc
  simpa [Ideal.Quotient.eq_zero_iff_mem] using h hc

variable {V : Subfunctor X} {W : Subfunctor V.toFunctor} {A : CommAlgCat.{u} k} {x : X.obj A}

/-- If `x ∈ X(A)` lies in `V` over `A[1/a]`, where `W` is cut out by an ideal `J` at the image of
`x`, then along any `f : A ⟶ B` sending `a` to a unit, `W` is cut out at `x` by the contraction of
`J` to `A`. -/
private lemma mem_iff_map_under_eq_top {a : A}
    (hπ : X.map (CommAlgCat.ofHom (IsScalarTower.toAlgHom k A (Localization.Away a))) x ∈
      V.obj (CommAlgCat.of k (Localization.Away a)))
    {J : Ideal (Localization.Away a)}
    (hJ : ∀ ⦃B : CommAlgCat.{u} k⦄ (g : CommAlgCat.of k (Localization.Away a) ⟶ B),
      V.toFunctor.map g ⟨_, hπ⟩ ∈ W.obj B ↔ J.map g.hom = ⊤)
    {B : CommAlgCat.{u} k} (f : A ⟶ B) (ha : IsUnit (f a)) (hx : X.map f x ∈ V.obj B) :
    (⟨X.map f x, hx⟩ : V.toFunctor.obj B) ∈ W.obj B ↔ (J.under A).map f.hom = ⊤ := by
  obtain ⟨g, hg⟩ := exists_away_comp_eq f ha
  have hgf : (g.hom : Localization.Away a →+* B).comp (algebraMap A (Localization.Away a)) =
      f.hom := by
    ext b
    simpa using congr(($hg) b)
  have hpt : (⟨X.map f x, hx⟩ : V.toFunctor.obj B) = V.toFunctor.map g ⟨_, hπ⟩ :=
    Subtype.ext ((congrArg (fun φ ↦ X.map φ x) hg).symm.trans (Functor.map_comp_apply X _ g x))
  have hJ' : J.map g.hom = (J.under A).map f.hom := by
    conv_lhs => rw [← IsLocalization.map_under (Submonoid.powers a) (Localization.Away a) J]
    rw [← Ideal.map_coe g.hom, Ideal.map_map, hgf, Ideal.map_coe]
  rw [hpt, hJ g, hJ']

/-- The image of `x` in `X(B')` along `f ≫ q` lies in `V` when its image along `f` does. -/
private lemma map_comp_mem {B B' : CommAlgCat.{u} k} (f : A ⟶ B) (q : B ⟶ B')
    (hx : X.map f x ∈ V.obj B) : X.map (f ≫ q) x ∈ V.obj B' := by
  rw [Functor.map_comp_apply]
  exact V.map q hx

/-- The image of `x` along `f ≫ q`, as a point of `V`, is the image along `q` of its image along
`f`. -/
private lemma toFunctor_map_mk {B B' : CommAlgCat.{u} k} (f : A ⟶ B) (q : B ⟶ B')
    (hx : X.map f x ∈ V.obj B) :
    V.toFunctor.map q ⟨X.map f x, hx⟩ = ⟨X.map (f ≫ q) x, map_comp_mem f q hx⟩ :=
  Subtype.ext <| by exact (Functor.map_comp_apply X f q x).symm

/-- The image along `q` of a point of `V` lying in `W` lies in `W`. -/
private lemma mk_map_comp_mem {B B' : CommAlgCat.{u} k} (f : A ⟶ B) (q : B ⟶ B')
    (hx : X.map f x ∈ V.obj B) (hw : (⟨X.map f x, hx⟩ : V.toFunctor.obj B) ∈ W.obj B) :
    (⟨X.map (f ≫ q) x, map_comp_mem f q hx⟩ : V.toFunctor.obj B') ∈ W.obj B' := by
  have := W.map q hw
  rwa [Set.mem_preimage, toFunctor_map_mk] at this

/-- In the setting of `IsOpen.image_ι`, if the image of `x` in `X(B)` lies in `W`, then the
ideal `⨆ a, (a) · (J a ∩ A)` is sent to the unit ideal of `B`: otherwise it lies in a maximal
ideal `𝔫`, some `a ∈ I` becomes a unit in the field `B ⧸ 𝔫`, and then so does `J a ∩ A`. -/
private lemma map_iSup_eq_top_of_mem {I : Ideal A}
    (hI : ∀ ⦃B : CommAlgCat.{u} k⦄ (f : A ⟶ B), X.map f x ∈ V.obj B ↔ I.map f.hom = ⊤)
    {J : ∀ a : I, Ideal (Localization.Away (a : A))}
    (key : ∀ (a : I) ⦃B : CommAlgCat.{u} k⦄ (f : A ⟶ B), IsUnit (f a) →
      ∀ hx : X.map f x ∈ V.obj B, (⟨X.map f x, hx⟩ : V.toFunctor.obj B) ∈ W.obj B ↔
        ((J a).under A).map f.hom = ⊤)
    {B : CommAlgCat.{u} k} (f : A ⟶ B)
    (hx : X.map f x ∈ V.obj B) (hw : (⟨X.map f x, hx⟩ : V.toFunctor.obj B) ∈ W.obj B) :
    (⨆ a : I, Ideal.span {(a : A)} * (J a).under A).map f.hom = ⊤ := by
  by_contra hne
  obtain ⟨𝔫, h𝔫, hle⟩ := Ideal.exists_le_maximal _ hne
  let := Ideal.Quotient.field 𝔫
  let q : B ⟶ CommAlgCat.of k (B ⧸ 𝔫) := CommAlgCat.ofHom (Ideal.Quotient.mkₐ k 𝔫)
  obtain ⟨a, ha⟩ : ∃ a : I, IsUnit ((f ≫ q) a) := by
    by_contra! H
    have h₀ : I.map (f ≫ q).hom = ⊥ := by
      rw [Ideal.map_eq_bot_iff_le_ker]
      intro b hb
      rw [RingHom.mem_ker]
      by_contra h
      exact H ⟨b, hb⟩ ((isUnit_iff_ne_zero (G₀ := B ⧸ 𝔫)).2 h)
    exact bot_ne_top (h₀.symm.trans ((hI _).1 (map_comp_mem f q hx)))
  have hT : (Ideal.span {(a : A)} * (J a).under A).map (f ≫ q).hom = ⊤ := by
    rw [Ideal.map_mul, (key a _ ha (map_comp_mem f q hx)).1 (mk_map_comp_mem f q hx hw),
      Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top.2 ha, Ideal.top_mul]
  have hle' : (Ideal.span {(a : A)} * (J a).under A).map (f ≫ q).hom ≤ ⊥ := by
    rw [map_comp_hom, ← map_quotient_eq_bot (k := k) (le_refl 𝔫)]
    exact Ideal.map_mono ((Ideal.map_mono
      (le_iSup (fun b : I ↦ Ideal.span {(b : A)} * (J b).under A) a)).trans hle)
  exact top_ne_bot (le_bot_iff.1 (hT ▸ hle'))

/-- In the setting of `IsOpen.image_ι`, if `f : A ⟶ B` sends the ideal `⨆ a, (a) · (J a ∩ A)`
to the unit ideal, then the image of `x` in `X(B)` lies in `W`: otherwise the ideal cutting out
`W` at that point lies in a maximal ideal `𝔫`, while in the field `B ⧸ 𝔫` some `a` and
`J a ∩ A` become units. -/
private lemma mem_of_map_iSup_eq_top {I : Ideal A}
    {J : ∀ a : I, Ideal (Localization.Away (a : A))}
    (key : ∀ (a : I) ⦃B : CommAlgCat.{u} k⦄ (f : A ⟶ B), IsUnit (f a) →
      ∀ hx : X.map f x ∈ V.obj B, (⟨X.map f x, hx⟩ : V.toFunctor.obj B) ∈ W.obj B ↔
        ((J a).under A).map f.hom = ⊤)
    (hW : ∀ ⦃B : CommAlgCat.{u} k⦄ (w : V.toFunctor.obj B), ∃ Iw : Ideal B,
      ∀ ⦃B' : CommAlgCat.{u} k⦄ (q : B ⟶ B'), V.toFunctor.map q w ∈ W.obj B' ↔ Iw.map q.hom = ⊤)
    {B : CommAlgCat.{u} k} (f : A ⟶ B) (hx : X.map f x ∈ V.obj B)
    (hf : (⨆ a : I, Ideal.span {(a : A)} * (J a).under A).map f.hom = ⊤) :
    (⟨X.map f x, hx⟩ : V.toFunctor.obj B) ∈ W.obj B := by
  obtain ⟨Iw, hIw⟩ := hW (⟨X.map f x, hx⟩ : V.toFunctor.obj B)
  suffices Iw = ⊤ by simpa [this] using (hIw (𝟙 B)).2
  by_contra hne
  obtain ⟨𝔫, h𝔫, hle⟩ := Ideal.exists_le_maximal _ hne
  let := Ideal.Quotient.field 𝔫
  let q : B ⟶ CommAlgCat.of k (B ⧸ 𝔫) := CommAlgCat.ofHom (Ideal.Quotient.mkₐ k 𝔫)
  have htop : (⨆ a : I, Ideal.span {(a : A)} * (J a).under A).map (f ≫ q).hom = ⊤ := by
    rw [map_comp_hom, hf, Ideal.map_top]
  obtain ⟨a, ha⟩ : ∃ a : I, (Ideal.span {(a : A)} * (J a).under A).map (f ≫ q).hom = ⊤ := by
    by_contra! H
    rw [Ideal.map_iSup] at htop
    exact bot_ne_top ((iSup_eq_bot.2 fun a ↦ (Ideal.eq_bot_or_top _).resolve_right (H a)).symm.trans
      htop)
  rw [Ideal.map_mul] at ha
  have hunit : IsUnit ((f ≫ q) a) := by
    have h₁ := top_le_iff.1 (ha ▸ Ideal.mul_le_left)
    rwa [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top] at h₁
  have h₁ := (hIw q).1 (by
    rw [toFunctor_map_mk]
    exact (key a (f ≫ q) hunit _).2 (top_le_iff.1 (ha ▸ Ideal.mul_le_right)))
  rw [map_quotient_eq_bot hle] at h₁
  exact bot_ne_top h₁

/-- **Openness is transitive.** If `V` is an open subfunctor of a functor `X` on commutative
`k`-algebras and `W` is an open subfunctor of `V`, then `W` is an open subfunctor of `X`. At a
point `x ∈ X(A)` cut out from `V` by an ideal `I`, the point lies in `V` over each localization
`A[1/a]` with `a ∈ I`, where `W` is cut out by some ideal `J a`; then `W` is cut out at `x` by
`⨆ a, (a) · (J a ∩ A)`, as one checks at the residue fields of the maximal ideals. -/
theorem IsOpen.image_ι (hV : V.IsOpen (forget₂ (CommAlgCat.{u} k) CommRingCat.{u}))
    (hW : W.IsOpen (forget₂ (CommAlgCat.{u} k) CommRingCat.{u})) :
    (W.image V.ι).IsOpen (forget₂ (CommAlgCat.{u} k) CommRingCat.{u}) := by
  rw [isOpen_forget₂_iff] at hV hW ⊢
  intro A x
  obtain ⟨I, hI⟩ := hV x
  have hπ (a : I) : X.map (CommAlgCat.ofHom
      (IsScalarTower.toAlgHom k A (Localization.Away (a : A)))) x ∈ V.obj _ :=
    (hI _).2 (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ a.property)
      (IsLocalization.Away.algebraMap_isUnit (a : A)))
  choose J hJ using fun a : I ↦ hW (⟨_, hπ a⟩ : V.toFunctor.obj _)
  have key : ∀ (a : I) ⦃B : CommAlgCat.{u} k⦄ (f : A ⟶ B), IsUnit (f a) →
      ∀ hx : X.map f x ∈ V.obj B, (⟨X.map f x, hx⟩ : V.toFunctor.obj B) ∈ W.obj B ↔
        ((J a).under A).map f.hom = ⊤ :=
    fun a _ f ha hx ↦ mem_iff_map_under_eq_top (hπ a) (hJ a) f ha hx
  refine ⟨⨆ a : I, Ideal.span {(a : A)} * (J a).under A, fun B f ↦ ?_⟩
  have hTI : (⨆ a : I, Ideal.span {(a : A)} * (J a).under A) ≤ I :=
    iSup_le fun a ↦ Ideal.mul_le_left.trans ((Ideal.span_singleton_le_iff_mem _).2 a.property)
  rw [mem_image_ι_obj_iff]
  refine ⟨fun ⟨hx, hw⟩ ↦ map_iSup_eq_top_of_mem hI key f hx hw, fun hf ↦ ?_⟩
  have hx : X.map f x ∈ V.obj B := (hI f).2 (top_le_iff.1 (hf ▸ Ideal.map_mono hTI))
  exact ⟨hx, mem_of_map_iSup_eq_top key hW f hx hf⟩

end Subfunctor

end CategoryTheory
