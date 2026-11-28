/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Subfunctor.Image
public import TauCeti.Algebra.Homology.Ext.Coproduct
public import TauCeti.Algebra.Homology.Ext.EquivFor
public import TauCeti.CategoryTheory.Yoneda

/-!
# Cohomology of functors as Ext groups

Let `C` be a category. For a functor `Y : C ⥤ Type w`, write `ℤ[Y] = Y ⋙ AddCommGrpCat.free` for
the functor `c ↦ ℤ[Y(c)]`. For functors `N, F : C ⥤ AddCommGrpCat` the groups `Extⁿ(N, F)` are
Mathlib's Ext groups of the abelian category `C ⥤ AddCommGrpCat`, and `Extⁿ(ℤ[Y], F)` is the
*cohomology of `Y` with coefficients in `F`*. Pull-back along `α : N' ⟶ N` is
`(Ext.mk₀ α).precomp F _`, push-forward along `β : F ⟶ F'` is `(Ext.mk₀ β).postcomp N _`, and a
subfunctor `U` of `V` gives the relative groups `Extⁿ(ℤ[V] / ℤ[U], F)`, with `ℤ[V] / ℤ[U]` the
cokernel of the monomorphism `ℤ[U] ⟶ ℤ[V]` (`CategoryTheory.Subfunctor.shortExact_free`). When `C`
is essentially small these Ext groups exist by
`CategoryTheory.Functor.isGrothendieckAbelian`.

This file fixes the vocabulary built on these groups and proves the basic facts about them. The
general notion of a morphism inducing bijections on `Extⁿ(-, F)`
(`CategoryTheory.IsExtEquivFor`) is in `TauCeti.Algebra.Homology.Ext.EquivFor`.

* `CategoryTheory.Subfunctor.IsDenseFor F U`: a subfunctor `U` of `Y` is *dense for `F`* if its
  preimage under every map `y : R ⟶ Y` from a corepresentable functor gives an equivalence
  `ℤ[y⁻¹ U] ⟶ ℤ[R]` for `F`; and `CategoryTheory.IsCoverFor F p`: a map `p : E ⟶ Y` is a *cover
  for `F`* if the inclusion of its image gives an equivalence for `F`.
* `CategoryTheory.free_hom_ext`: maps out of `ℤ[Y]` are determined by their values on the
  generators.
* `CategoryTheory.Functor.CorepresentableBy.freeHomAddEquiv`: the additive Yoneda lemma: if `Y`
  is corepresented by `A`, morphisms `ℤ[Y] ⟶ F` are the elements of `F(A)`. Hence `ℤ[Y]` is
  projective, so its cohomology vanishes in positive degrees (`Ext.eq_zero_of_projective`), and
  in degree `0` it is `Ext⁰(ℤ[Y], F) ≃ F(A)`
  (`CategoryTheory.Functor.CorepresentableBy.extZeroAddEquiv`). An endomorphism `g` of `A`
  induces the endomorphism `CategoryTheory.Functor.CorepresentableBy.precompEndo` of `Y`,
  precomposition with `g`, which these bijections turn into `F(g)`.
* `CategoryTheory.extFreeCoproductAddEquiv`: the cohomology of a disjoint union of functors is
  the product of the cohomology groups of its pieces, by restriction to the summands.

## References

* [ShortProof]: `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/Cohomology/Etale/Basic.lean` (declarations `New.Variety.IsCohomDense`,
  `New.Variety.homReprEquiv`, `New.Variety.relFreeAb`) and
  `src/Lib/Cohomology/Etale/BijectiveComparisons.lean` (`New.Variety.IsCover`), and
  `src/Lib/General/Algebra/LongExactSequences.lean` (`New.Variety.H.sigma_bijective`); Apache 2.0,
  Copyright 2026 Anthropic, PBC. The statements here are adapted from these declarations and
  restated with Mathlib's Ext groups, subfunctors and corepresentable functors.
-/

public section

open CategoryTheory Limits Abelian

universe t w v u

namespace CategoryTheory

/-! ### Free abelian functors and relative chains -/

section Free

variable {C : Type u} [Category.{v} C]

/-- For a subfunctor `U` of `Y`, the sequence `ℤ[U] ⟶ ℤ[Y] ⟶ ℤ[Y] / ℤ[U]` is short exact. Its
long exact Ext sequence is the long exact sequence of the pair `(Y, U)`. -/
lemma Subfunctor.shortExact_free {Y : C ⥤ Type w} (U : Subfunctor Y) :
    (ShortComplex.mk (Functor.whiskerRight U.ι AddCommGrpCat.free)
      (cokernel.π (Functor.whiskerRight U.ι AddCommGrpCat.free))
      (cokernel.condition _)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance

/-- Two maps out of a free abelian functor `ℤ[Y]` agree if they agree on the generators. -/
lemma free_hom_ext {Y : C ⥤ Type w} {F : C ⥤ AddCommGrpCat.{w}}
    {f g : Y ⋙ AddCommGrpCat.free ⟶ F}
    (h : ∀ (c : C) (y : Y.obj c),
      f.app c (FreeAddCommGroup.of y) = g.app c (FreeAddCommGroup.of y)) :
    f = g :=
  NatTrans.ext (funext fun c ↦ AddCommGrpCat.hom_ext (FreeAddCommGroup.lift_ext _ _ (h c)))

/-- `ℤ[a]` sends the generator of `y` to the generator of `a y`. Not a `simp` lemma: `simp`
rewrites the types in its left-hand side through `Functor.comp_obj`. -/
lemma whiskerRight_free_app_of {Y Y' : C ⥤ Type w} (a : Y ⟶ Y') (c : C) (y : Y.obj c) :
    (Functor.whiskerRight a AddCommGrpCat.free).app c
        (FreeAddCommGroup.of y : (Y ⋙ AddCommGrpCat.free).obj c) =
      (FreeAddCommGroup.of (a.app c y) : (Y' ⋙ AddCommGrpCat.free).obj c) :=
  FreeAddCommGroup.map_of_apply _

/-- `ℤ[φ.whiskerLeft a]` is `φ.whiskerLeft ℤ[a]`: both have the components `ℤ[a_{φ d}]`. Mathlib's
`CategoryTheory.Functor.whiskerRight_left` states this for any functor in place of `ℤ[-]`, up to
the associators `(φ ⋙ Y) ⋙ ℤ[-] ≅ φ ⋙ (Y ⋙ ℤ[-])`, which are identities. -/
lemma whiskerRight_whiskerLeft_free {D : Type*} [Category* D] (φ : D ⥤ C) {Y Y' : C ⥤ Type w}
    (a : Y ⟶ Y') :
    Functor.whiskerRight (φ.whiskerLeft a) AddCommGrpCat.free =
      φ.whiskerLeft (Functor.whiskerRight a AddCommGrpCat.free) :=
  rfl

/-! ### The additive Yoneda lemma -/

/-- **Additive Yoneda lemma.** If `Y : C ⥤ Type w` is corepresented by `A`, morphisms from the
free abelian functor `ℤ[Y]` to `F` are the elements of `F(A)`: a morphism is sent to the image of
the universal element. -/
def Functor.CorepresentableBy.freeHomAddEquiv {Y : C ⥤ Type w} {A : C}
    (e : Y.CorepresentableBy A) (F : C ⥤ AddCommGrpCat.{w}) :
    (Y ⋙ AddCommGrpCat.free ⟶ F) ≃+ F.obj A where
  toEquiv := ((Adjunction.whiskerRight C AddCommGrpCat.adj).homEquiv Y F).trans
    (e.natTransEquiv (F ⋙ forget AddCommGrpCat))
  map_add' f g := by
    simp only [Equiv.toFun_as_coe, Equiv.trans_apply]
    rw [natTransEquiv_apply, natTransEquiv_apply, natTransEquiv_apply]
    -- The adjunction transposes `f + g` componentwise, and addition of morphisms in
    -- `AddCommGrpCat` is pointwise.
    rfl

/-- The additive Yoneda bijection sends a morphism to its value at the generator given by the
universal element. -/
@[simp]
lemma Functor.CorepresentableBy.freeHomAddEquiv_apply {Y : C ⥤ Type w} {A : C}
    (e : Y.CorepresentableBy A) (F : C ⥤ AddCommGrpCat.{w}) (f : Y ⋙ AddCommGrpCat.free ⟶ F) :
    e.freeHomAddEquiv F f = f.app A (FreeAddCommGroup.of (e.homEquiv (𝟙 A))) :=
  e.natTransEquiv_apply _ _

/-- The morphism `ℤ[Y] ⟶ F` corresponding to `g ∈ F(A)` sends the generator of `y ∈ Y(c)`, the
image of a morphism `A ⟶ c`, to the image of `g` under that morphism. Not a `simp` lemma: its
left-hand side is not in simp normal form, since `simp` rewrites the type of `FreeAddCommGroup.of y`
through `Functor.comp_obj`. -/
lemma Functor.CorepresentableBy.freeHomAddEquiv_symm_apply_app_of {Y : C ⥤ Type w} {A : C}
    (e : Y.CorepresentableBy A) (F : C ⥤ AddCommGrpCat.{w}) (g : F.obj A) {c : C} (y : Y.obj c) :
    ((e.freeHomAddEquiv F).symm g).app c (FreeAddCommGroup.of y) = F.map (e.homEquiv.symm y) g := by
  -- `y` is the image of the universal element under `k : A ⟶ c`, so naturality of the morphism
  -- reduces the claim to its value at the universal element, which is `g`.
  set f := (e.freeHomAddEquiv F).symm g
  have hf : f.app A (FreeAddCommGroup.of (e.homEquiv (𝟙 A))) = g :=
    (e.freeHomAddEquiv_apply F f).symm.trans ((e.freeHomAddEquiv F).apply_symm_apply g)
  obtain ⟨k, rfl⟩ := e.homEquiv.surjective y
  have hk : e.homEquiv k = Y.map k (e.homEquiv (𝟙 A)) := by
    rw [← e.homEquiv_comp, Category.id_comp]
  rw [Equiv.symm_apply_apply, ← hf, hk]
  exact NatTrans.naturality_apply f k (FreeAddCommGroup.of (e.homEquiv (𝟙 A)))

/-- The additive Yoneda bijection is natural in the coefficients. -/
lemma Functor.CorepresentableBy.freeHomAddEquiv_comp {Y : C ⥤ Type w} {A : C}
    (e : Y.CorepresentableBy A) {F G : C ⥤ AddCommGrpCat.{w}} (f : Y ⋙ AddCommGrpCat.free ⟶ F)
    (g : F ⟶ G) : e.freeHomAddEquiv G (f ≫ g) = g.app A (e.freeHomAddEquiv F f) := by
  rw [freeHomAddEquiv_apply, freeHomAddEquiv_apply, NatTrans.comp_app]
  -- Applying `f.app A ≫ g.app A` is applying `f.app A` and then `g.app A`.
  -- `ConcreteCategory.comp_apply` does not match here, because the generator has type
  -- `(Y ⋙ free).obj A` only up to unfolding.
  rfl

/-- The endomorphism of a functor `Y` corepresented by `A` induced by `g : A ⟶ A`: the element
of `Y(c)` given by a morphism `k : A ⟶ c` goes to the one given by `g ≫ k`. -/
def Functor.CorepresentableBy.precompEndo {Y : C ⥤ Type w} {A : C} (e : Y.CorepresentableBy A)
    (g : A ⟶ A) : Y ⟶ Y where
  app _ := ↾fun y ↦ e.homEquiv (g ≫ e.homEquiv.symm y)
  naturality c c' f := by
    ext y
    exact (congrArg e.homEquiv ((congrArg (g ≫ ·) (e.homEquiv_symm_comp y f).symm).trans
      (Category.assoc _ _ _).symm)).trans (e.homEquiv_comp f _)

/-- `e.precompEndo g` precomposes with `g` the morphism that an element represents. -/
lemma Functor.CorepresentableBy.precompEndo_app_apply {Y : C ⥤ Type w} {A : C}
    (e : Y.CorepresentableBy A) (g : A ⟶ A) (c : C) (y : Y.obj c) :
    (e.precompEndo g).app c y = e.homEquiv (g ≫ e.homEquiv.symm y) :=
  (rfl)

/-- Under the additive Yoneda lemma, precomposition with `ℤ[e.precompEndo g]` is `F(g)`. -/
lemma Functor.CorepresentableBy.freeHomAddEquiv_whiskerRight_precompEndo_comp {Y : C ⥤ Type w}
    {A : C} (e : Y.CorepresentableBy A) (g : A ⟶ A) (F : C ⥤ AddCommGrpCat.{w})
    (f : Y ⋙ AddCommGrpCat.free ⟶ F) :
    e.freeHomAddEquiv F (Functor.whiskerRight (e.precompEndo g) AddCommGrpCat.free ≫ f) =
      F.map g (e.freeHomAddEquiv F f) := by
  rw [freeHomAddEquiv_apply, freeHomAddEquiv_apply]
  -- Both sides evaluate `f` at the generator of `g`, seen as an element of `Y(A)`.
  have h : (e.precompEndo g).app A (e.homEquiv (𝟙 A)) = Y.map g (e.homEquiv (𝟙 A)) := by
    rw [precompEndo_app_apply, ← e.homEquiv_comp, Equiv.symm_apply_apply, Category.comp_id,
      Category.id_comp]
  exact (congrArg (f.app A) ((FreeAddCommGroup.map_of_apply _).trans
    ((congrArg FreeAddCommGroup.of h).trans (FreeAddCommGroup.map_of_apply _).symm))).trans
    (NatTrans.naturality_apply f g _)

/-- The free abelian functor on a corepresentable functor is projective. -/
instance projective_free {Y : C ⥤ Type w} [Y.IsCorepresentable] :
    Projective (Y ⋙ AddCommGrpCat.free) where
  factors {E X} f g _ := by
    let e := Y.corepresentableBy
    obtain ⟨x, hx⟩ := (AddCommGrpCat.epi_iff_surjective (g.app _)).1 inferInstance
      (e.freeHomAddEquiv X f)
    refine ⟨(e.freeHomAddEquiv E).symm x, (e.freeHomAddEquiv X).injective ?_⟩
    rw [e.freeHomAddEquiv_comp, AddEquiv.apply_symm_apply, hx]

section ExtZero

variable [HasExt.{t} (C ⥤ AddCommGrpCat.{w})]

/-- **The additive Yoneda lemma in degree `0`.** If `Y` is corepresented by `A`, then
`Ext⁰(ℤ[Y], F) ≃ F(A)`: a class of degree `0` is a morphism `ℤ[Y] ⟶ F`
(`CategoryTheory.Abelian.Ext.addEquiv₀`), which is an element of `F(A)`
(`CategoryTheory.Functor.CorepresentableBy.freeHomAddEquiv`). -/
noncomputable def Functor.CorepresentableBy.extZeroAddEquiv {Y : C ⥤ Type w} {A : C}
    (e : Y.CorepresentableBy A) (F : C ⥤ AddCommGrpCat.{w}) :
    Ext.{t} (Y ⋙ AddCommGrpCat.free) F 0 ≃+ F.obj A :=
  Ext.addEquiv₀.trans (e.freeHomAddEquiv F)

/-- `e.extZeroAddEquiv F` reads a class of degree `0` as a morphism `ℤ[Y] ⟶ F` and applies the
additive Yoneda lemma. -/
lemma Functor.CorepresentableBy.extZeroAddEquiv_apply {Y : C ⥤ Type w} {A : C}
    (e : Y.CorepresentableBy A) (F : C ⥤ AddCommGrpCat.{w})
    (x : Ext.{t} (Y ⋙ AddCommGrpCat.free) F 0) :
    e.extZeroAddEquiv F x = e.freeHomAddEquiv F (Ext.addEquiv₀ x) :=
  (rfl)

/-- The class of degree `0` corresponding to an element `a` of `F(A)` is that of the morphism
`ℤ[Y] ⟶ F` corresponding to `a`. -/
@[simp]
lemma Functor.CorepresentableBy.extZeroAddEquiv_symm_apply {Y : C ⥤ Type w} {A : C}
    (e : Y.CorepresentableBy A) (F : C ⥤ AddCommGrpCat.{w}) (a : F.obj A) :
    (e.extZeroAddEquiv F).symm a = Ext.mk₀ ((e.freeHomAddEquiv F).symm a) :=
  (rfl)

/-- Under the additive Yoneda lemma in degree `0`, pull-back along `ℤ[e.precompEndo g]` is
`F(g)`. -/
lemma Functor.CorepresentableBy.extZeroAddEquiv_mk₀_whiskerRight_precompEndo_comp
    {Y : C ⥤ Type w} {A : C} (e : Y.CorepresentableBy A) (g : A ⟶ A) (F : C ⥤ AddCommGrpCat.{w})
    (x : Ext.{t} (Y ⋙ AddCommGrpCat.free) F 0) :
    e.extZeroAddEquiv F ((Ext.mk₀ (Functor.whiskerRight (e.precompEndo g)
      AddCommGrpCat.free)).comp x (zero_add 0)) = F.map g (e.extZeroAddEquiv F x) := by
  rw [extZeroAddEquiv_apply, extZeroAddEquiv_apply, TauCeti.ext_addEquiv₀_mk₀_comp,
    freeHomAddEquiv_whiskerRight_precompEndo_comp]

end ExtZero

/-! ### Disjoint unions -/

variable [HasExt.{t} (C ⥤ AddCommGrpCat.{w})] [EnoughInjectives (C ⥤ AddCommGrpCat.{w})]

/-- The cohomology of a disjoint union of functors is the product of the cohomology groups of the
pieces: for a coproduct `∐ Xᵢ` of functors `C ⥤ Type w`, restriction to the summands is an
isomorphism `Extⁿ(ℤ[∐ Xᵢ], F) ≃+ ∀ i, Extⁿ(ℤ[Xᵢ], F)`. -/
noncomputable def extFreeCoproductAddEquiv {J : Type*} {X : J → C ⥤ Type w} {c : Cofan X}
    (hc : IsColimit c) (F : C ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    Ext.{t} (c.pt ⋙ AddCommGrpCat.free) F n ≃+ ∀ i, Ext.{t} (X i ⋙ AddCommGrpCat.free) F n :=
  have := (Adjunction.whiskerRight C AddCommGrpCat.adj).leftAdjoint_preservesColimits
  Ext.coproductAddEquiv
    (isColimitCofanMkObjOfIsColimit ((Functor.whiskeringRight C _ _).obj AddCommGrpCat.free)
      X c.inj hc) F n

/-- The restriction of a class on a disjoint union to a summand. -/
@[simp]
lemma extFreeCoproductAddEquiv_apply {J : Type*} {X : J → C ⥤ Type w} {c : Cofan X}
    (hc : IsColimit c) (F : C ⥤ AddCommGrpCat.{w}) (n : ℕ)
    (x : Ext.{t} (c.pt ⋙ AddCommGrpCat.free) F n) (i : J) :
    extFreeCoproductAddEquiv hc F n x i =
      (Ext.mk₀ (Functor.whiskerRight (c.inj i) AddCommGrpCat.free)).comp x (zero_add n) := by
  rw [extFreeCoproductAddEquiv, Ext.coproductAddEquiv_apply, cofan_mk_inj,
    Functor.whiskeringRight_obj_map]

/-- Restriction to a summand of the class on a disjoint union assembled from a family of classes
recovers the indicated member of the family. -/
@[simp]
lemma mk₀_comp_extFreeCoproductAddEquiv_symm {J : Type*} {X : J → C ⥤ Type w} {c : Cofan X}
    (hc : IsColimit c) (F : C ⥤ AddCommGrpCat.{w}) (n : ℕ)
    (x : ∀ i, Ext.{t} (X i ⋙ AddCommGrpCat.free) F n) (i : J) :
    (Ext.mk₀ (Functor.whiskerRight (c.inj i) AddCommGrpCat.free)).comp
      ((extFreeCoproductAddEquiv hc F n).symm x) (zero_add n) = x i := by
  rw [← extFreeCoproductAddEquiv_apply, AddEquiv.apply_symm_apply]

end Free

/-! ### Density and covers -/

section Density

variable {C : Type u} [Category.{v} C] [HasExt.{t} (C ⥤ AddCommGrpCat.{w})]
  (F : C ⥤ AddCommGrpCat.{w})

/-- A subfunctor `U` of `Y : C ⥤ Type w` is *dense for* `F` if for every map `y : R ⟶ Y` from a
corepresentable functor (a point of `Y` with values in an object of `C`), the inclusion of the
preimage `y⁻¹ U` into `R` induces an equivalence `ℤ[y⁻¹ U] ⟶ ℤ[R]` for `F`. -/
def Subfunctor.IsDenseFor {Y : C ⥤ Type w} (U : Subfunctor Y) : Prop :=
  ∀ ⦃R : C ⥤ Type w⦄ [R.IsCorepresentable] (y : R ⟶ Y),
    IsExtEquivFor.{t} F (Functor.whiskerRight (U.preimage y).ι AddCommGrpCat.free)

/-- A map `p : E ⟶ Y` of functors `C ⥤ Type w` is a *cover for* `F` if the inclusion of its image
into `Y` induces an equivalence `ℤ[im p] ⟶ ℤ[Y]` for `F`. -/
def IsCoverFor {E Y : C ⥤ Type w} (p : E ⟶ Y) : Prop :=
  IsExtEquivFor.{t} F (Functor.whiskerRight (Subfunctor.range p).ι AddCommGrpCat.free)

variable {F}

/-- The whole functor is dense in itself. -/
lemma Subfunctor.isDenseFor_top (Y : C ⥤ Type w) : (⊤ : Subfunctor Y).IsDenseFor.{t} F :=
  fun R _ y ↦ by
    rw [(Subfunctor.preimage_eq_top_iff _ _).2 le_top]
    exact isExtEquivFor_of_isIso _

/-- A subfunctor `U` of `Y` is dense for `F` exactly when, for every map `y : R ⟶ Y` from a
corepresentable functor, the relative cohomology `Extⁿ(ℤ[R] / ℤ[y⁻¹ U], F)` vanishes in every
degree. -/
lemma Subfunctor.isDenseFor_iff_forall_subsingleton_ext {Y : C ⥤ Type w} (U : Subfunctor Y) :
    U.IsDenseFor.{t} F ↔ ∀ ⦃R : C ⥤ Type w⦄ [R.IsCorepresentable] (y : R ⟶ Y) (n : ℕ),
      Subsingleton (Ext.{t} (cokernel (Functor.whiskerRight (U.preimage y).ι
        AddCommGrpCat.free)) F n) :=
  ⟨fun h _ _ y ↦ (isExtEquivFor_iff_of_shortExact (U.preimage y).shortExact_free).1 (h y),
    fun h _ _ y ↦ (isExtEquivFor_iff_of_shortExact (U.preimage y).shortExact_free).2 (h y)⟩

/-- A pointwise surjective map is a cover for every coefficient functor. -/
lemma isCoverFor_of_epi {E Y : C ⥤ Type w} (p : E ⟶ Y) [Epi p] : IsCoverFor.{t} F p := by
  have : IsIso (Subfunctor.range p).ι := by
    rw [← Subfunctor.eq_top_iff_isIso]
    exact Subfunctor.range_eq_top p
  exact isExtEquivFor_of_isIso _

end Density

end CategoryTheory
