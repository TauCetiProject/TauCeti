/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import TauCeti.CategoryTheory.Sites.Continuous
public import TauCeti.CategoryTheory.Sites.Point.ConstantSheaf
public import TauCeti.CategoryTheory.Sites.Point.Over

/-!
# Locally constant sheaves

Let `(C, J)` be a site, let `A` be a category in which sheafification exists, and let `P` be a
property of objects of `A`. A sheaf `F : Sheaf J A` is *locally constant with values in `P`* if
every object `X : C` is covered by morphisms `Y ⟶ X` over which `F` becomes isomorphic to a
constant sheaf with value `M` satisfying `P`. Over `Y` this means that the restriction `F.over Y`
to the site `(Over Y, J.over Y)` is isomorphic to the restriction of the constant sheaf
`(constantSheaf J A).obj M`. Phrasing it through restrictions of constant sheaves on `(C, J)`
avoids sheafification on the sites `Over Y`.

For instance, with `A = ModuleCat Λ` and `P` the finitely generated modules, the locally constant
sheaves on the small étale site of a scheme are the finite lisse sheaves when `Λ` is finite.

At a point `Φ` of the site, the fibre of a locally constant sheaf with values in `P` is isomorphic
to an object satisfying `P` (`CategoryTheory.Sheaf.IsLocallyConstantIn.exists_sheafFiber_iso`):
the fibre can be computed after restricting to an object `Y` of the covering, where the sheaf is
constant, and the fibre of a constant sheaf with value `M` is `M`.

## Main declarations

* `CategoryTheory.Sheaf.locallyConstantSieve`: the sieve on `X` of the morphisms `Y ⟶ X` over
  which `F` is constant with value satisfying `P`.
* `CategoryTheory.Sheaf.IsLocallyConstantIn`: `F` is locally constant with values in `P`.
* `CategoryTheory.Sheaf.isLocallyConstantIn_constantSheaf`: a constant sheaf is locally constant.
* `CategoryTheory.Sheaf.isLocallyConstantIn_iff_of_isTerminal`: on a site with a terminal object
  `T`, local constancy only needs to be checked over `T`.
* `CategoryTheory.Sheaf.mem_locallyConstantSieve_iff_of_mem`,
  `CategoryTheory.Sheaf.isLocallyConstantIn_iff_of_sieve_mem_of_isTerminal`: local constancy is
  local for `J`-coverings.
* `CategoryTheory.Sheaf.isLocallyConstantIn_zero`,
  `CategoryTheory.Sheaf.IsLocallyConstantIn.biprod`: closure of locally constant sheaves with
  preadditive coefficients under zero objects and binary biproducts.
* `CategoryTheory.Sheaf.IsLocallyConstantIn.exists_sheafFiber_iso`: the fibres of a locally
  constant sheaf are isomorphic to objects satisfying `P`.

## References

* M. Artin, *SGA 4*, Exposé IX, §2, for locally constant sheaves on a site.
-/

public section

universe w v u u' v'

open CategoryTheory Limits ZeroObject

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {A : Type u'}
  [Category.{v'} A] [HasWeakSheafify J A] (P : ObjectProperty A)

/-- For a sheaf `F` and a property `P` of objects of `A`, the sieve on `X` of the morphisms
`Y ⟶ X` such that the restriction `F.over Y` is isomorphic to the restriction to `Over Y` of the
constant sheaf with value some `M` satisfying `P`. -/
def locallyConstantSieve (F : Sheaf J A) (X : C) : Sieve X where
  arrows Y _ := ∃ M, P M ∧ Nonempty (F.over Y ≅ ((constantSheaf J A).obj M).over Y)
  downward_closed := by
    rintro Y Z - ⟨M, hM, ⟨e⟩⟩ g
    exact ⟨M, hM, ⟨(F.pushforwardOverMapIso g).symm ≪≫
      ((Over.map g).sheafPushforwardContinuous A _ _).mapIso e ≪≫
        ((constantSheaf J A).obj M).pushforwardOverMapIso g⟩⟩

@[simp]
lemma locallyConstantSieve_apply (F : Sheaf J A) {X Y : C} (f : Y ⟶ X) :
    F.locallyConstantSieve P X f ↔
      ∃ M, P M ∧ Nonempty (F.over Y ≅ ((constantSheaf J A).obj M).over Y) :=
  Iff.rfl

/-- Whether `F` is constant over `Y ⟶ X` does not depend on `X`, so the sieves of local constancy
are stable under pullback. -/
@[simp]
lemma pullback_locallyConstantSieve (F : Sheaf J A) {X Z : C} (g : Z ⟶ X) :
    (F.locallyConstantSieve P X).pullback g = F.locallyConstantSieve P Z :=
  Sieve.ext fun _ _ ↦ Iff.rfl

variable {P} in
lemma locallyConstantSieve_mono {Q : ObjectProperty A} (h : P ≤ Q) (F : Sheaf J A) (X : C) :
    F.locallyConstantSieve P X ≤ F.locallyConstantSieve Q X :=
  fun _ _ ⟨M, hM, e⟩ ↦ ⟨M, h M hM, e⟩

/-- Isomorphic sheaves have the same sieves of local constancy. -/
lemma locallyConstantSieve_congr {F G : Sheaf J A} (e : F ≅ G) (X : C) :
    F.locallyConstantSieve P X = G.locallyConstantSieve P X := by
  ext Y f
  exact ⟨fun ⟨M, hM, ⟨e'⟩⟩ ↦ ⟨M, hM, ⟨(J.overPullback A Y).mapIso e.symm ≪≫ e'⟩⟩,
    fun ⟨M, hM, ⟨e'⟩⟩ ↦ ⟨M, hM, ⟨(J.overPullback A Y).mapIso e ≪≫ e'⟩⟩⟩

variable (J) in
/-- A sheaf `F` is *locally constant with values in `P`* if every object `X` is covered by
morphisms `Y ⟶ X` such that `F.over Y` is isomorphic to the restriction to `Over Y` of the
constant sheaf with value some `M` satisfying `P`. -/
def IsLocallyConstantIn (F : Sheaf J A) : Prop :=
  ∀ X : C, F.locallyConstantSieve P X ∈ J X

lemma isLocallyConstantIn_iff (F : Sheaf J A) :
    F.IsLocallyConstantIn J P ↔ ∀ X : C, F.locallyConstantSieve P X ∈ J X :=
  Iff.rfl

/-- On a site with a terminal object `T`, a sheaf is locally constant as soon as it is so over
`T`, since the sieves of local constancy are stable under pullback. -/
lemma isLocallyConstantIn_iff_of_isTerminal (F : Sheaf J A) {T : C} (hT : IsTerminal T) :
    F.IsLocallyConstantIn J P ↔ F.locallyConstantSieve P T ∈ J T :=
  ⟨fun hF ↦ hF T, fun h X ↦
    F.pullback_locallyConstantSieve P (hT.from X) ▸ J.pullback_stable (hT.from X) h⟩

/-- By transitivity of `J`, `F.locallyConstantSieve P X` covers `X` as soon as it covers the source
of every arrow in a `J`-covering sieve of `X`. -/
lemma mem_locallyConstantSieve_of_mem {F : Sheaf J A} {X : C} {R : Sieve X} (hR : R ∈ J X)
    (h : ∀ ⦃Y : C⦄ ⦃g : Y ⟶ X⦄, R g → F.locallyConstantSieve P Y ∈ J Y) :
    F.locallyConstantSieve P X ∈ J X :=
  J.transitive hR (F.locallyConstantSieve P X) fun _ g hg ↦
    (F.pullback_locallyConstantSieve P g).symm ▸ h hg

/-- Given a covering sieve `R ∈ J X`, `F` is locally constant with values in `P` over `X` if and
only if it is so over the source of every arrow in `R`. -/
lemma mem_locallyConstantSieve_iff_of_mem (F : Sheaf J A) {X : C} {R : Sieve X} (hR : R ∈ J X) :
    F.locallyConstantSieve P X ∈ J X ↔
      ∀ ⦃Y : C⦄ ⦃g : Y ⟶ X⦄, R g → F.locallyConstantSieve P Y ∈ J Y :=
  ⟨fun hX _ g _ ↦ F.pullback_locallyConstantSieve P g ▸ J.pullback_stable g hX,
    mem_locallyConstantSieve_of_mem P hR⟩

/-- On a site with a terminal object `T`, local constancy can be tested on any covering sieve
`R ∈ J T`. -/
lemma isLocallyConstantIn_iff_of_sieve_mem_of_isTerminal (F : Sheaf J A) {T : C}
    (hT : IsTerminal T) {R : Sieve T} (hR : R ∈ J T) :
    F.IsLocallyConstantIn J P ↔ ∀ ⦃Y : C⦄ ⦃g : Y ⟶ T⦄, R g → F.locallyConstantSieve P Y ∈ J Y :=
  (F.isLocallyConstantIn_iff_of_isTerminal P hT).trans (F.mem_locallyConstantSieve_iff_of_mem P hR)

variable {P}

lemma IsLocallyConstantIn.mono {Q : ObjectProperty A} (h : P ≤ Q) {F : Sheaf J A}
    (hF : F.IsLocallyConstantIn J P) : F.IsLocallyConstantIn J Q :=
  fun X ↦ J.superset_covering (locallyConstantSieve_mono h F X) (hF X)

lemma IsLocallyConstantIn.of_iso {F G : Sheaf J A} (e : F ≅ G) (hF : F.IsLocallyConstantIn J P) :
    G.IsLocallyConstantIn J P :=
  fun X ↦ locallyConstantSieve_congr P e X ▸ hF X

lemma isLocallyConstantIn_iff_of_iso {F G : Sheaf J A} (e : F ≅ G) :
    F.IsLocallyConstantIn J P ↔ G.IsLocallyConstantIn J P :=
  ⟨.of_iso e, .of_iso e.symm⟩

/-- The constant sheaf with value `M` satisfying `P` is locally constant with values in `P`. -/
lemma isLocallyConstantIn_constantSheaf {M : A} (hM : P M) :
    ((constantSheaf J A).obj M).IsLocallyConstantIn J P := fun X ↦ by
  convert J.top_mem X
  exact top_unique fun Y _ _ ↦ ⟨M, hM, ⟨Iso.refl _⟩⟩

/-- When `A` is preadditive and `P` contains `0`, the zero sheaf is locally constant with values in
`P`. -/
lemma isLocallyConstantIn_zero [Preadditive A] [HasZeroObject A] [HasZeroObject (Sheaf J A)]
    (h₀ : P 0) : (0 : Sheaf J A).IsLocallyConstantIn J P := by
  have : (presheafToSheaf J A).Additive := (sheafificationAdjunction J A).left_adjoint_additive
  have : (Functor.const Cᵒᵖ : A ⥤ Cᵒᵖ ⥤ A).Additive := ⟨rfl⟩
  have : (constantSheaf J A).Additive :=
    inferInstanceAs (Functor.const Cᵒᵖ ⋙ presheafToSheaf J A).Additive
  exact (isLocallyConstantIn_constantSheaf h₀).of_iso (constantSheaf J A).mapZeroObject

/-- When `A` is preadditive with binary biproducts and `P` is closed under binary biproducts,
`IsLocallyConstantIn J P` is closed under binary biproducts, by intersecting trivializing sieves. -/
lemma IsLocallyConstantIn.biprod [Preadditive A] [HasBinaryBiproducts A]
    [HasBinaryBiproducts (Sheaf J A)]
    (hP : ∀ ⦃M₁ M₂ : A⦄, P M₁ → P M₂ → P (M₁ ⊞ M₂))
    {F₁ F₂ : Sheaf J A} (hF₁ : F₁.IsLocallyConstantIn J P) (hF₂ : F₂.IsLocallyConstantIn J P) :
    (F₁ ⊞ F₂).IsLocallyConstantIn J P := by
  have : (presheafToSheaf J A).Additive := (sheafificationAdjunction J A).left_adjoint_additive
  have : (Functor.const Cᵒᵖ : A ⥤ Cᵒᵖ ⥤ A).Additive := ⟨rfl⟩
  have : (constantSheaf J A).Additive :=
    inferInstanceAs (Functor.const Cᵒᵖ ⋙ presheafToSheaf J A).Additive
  have := preservesBinaryBiproducts_of_preservesBiproducts (constantSheaf J A)
  intro X
  refine J.superset_covering ?_ (J.intersection_covering (hF₁ X) (hF₂ X))
  rintro Y _ ⟨⟨M₁, hM₁, ⟨e₁⟩⟩, ⟨M₂, hM₂, ⟨e₂⟩⟩⟩
  have : HasBinaryBiproducts (Sheaf (J.over Y) A) := HasBinaryBiproducts.of_hasBinaryProducts
  have := preservesBinaryBiproducts_of_preservesBiproducts (J.overPullback A Y)
  exact ⟨M₁ ⊞ M₂, hP hM₁ hM₂,
    ⟨(J.overPullback A Y).mapBiprod F₁ F₂ ≪≫ biprod.mapIso e₁ e₂ ≪≫
      ((J.overPullback A Y).mapBiprod _ _).symm ≪≫
      (J.overPullback A Y).mapIso ((constantSheaf J A).mapBiprod M₁ M₂).symm⟩⟩

/-- **The fibres of a locally constant sheaf.** At every point `Φ` of the site, the fibre of a
sheaf which is locally constant with values in `P` is isomorphic to an object satisfying `P`. -/
lemma IsLocallyConstantIn.exists_sheafFiber_iso [LocallySmall.{w} C]
    [HasColimitsOfSize.{w, w} A] [HasProducts.{w} A] {F : Sheaf J A}
    (hF : F.IsLocallyConstantIn J P) (Φ : GrothendieckTopology.Point.{w} J) :
    ∃ M, P M ∧ Nonempty (Φ.sheafFiber.obj F ≅ M) := by
  obtain ⟨u⟩ : Nonempty Φ.fiber.Elements := IsCofiltered.nonempty
  obtain ⟨Y, -, ⟨M, hM, ⟨e⟩⟩, y, -⟩ := Φ.jointly_surjective _ (hF u.obj) u.val
  exact ⟨M, hM, ⟨(Φ.sheafFiberOverIso y F).symm ≪≫ (Φ.over y).sheafFiber.mapIso e ≪≫
    Φ.sheafFiberOverIso y _ ≪≫ Φ.sheafFiberConstantSheafIso M⟩⟩

end CategoryTheory.Sheaf
