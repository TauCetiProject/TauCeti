/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.Subfunctor.Image
public import TauCeti.Algebra.Homology.Ext.Coproduct
public import TauCeti.Algebra.Homology.ShortComplex.FunctorCategory

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

This file fixes the vocabulary built on these groups and proves the basic facts about them.

* `CategoryTheory.IsExtEquivFor F α`: a morphism `α : X' ⟶ X` of an abelian category is an
  *equivalence for `F`* if precomposition with `α` is bijective on `Extⁿ(-, F)` for every `n`.
  Such morphisms compose and satisfy two out of three, and the first map of a short exact
  sequence is an equivalence for `F` exactly when `Ext*(-, F)` vanishes on the third term
  (`CategoryTheory.isExtEquivFor_iff_of_shortExact`).
* `CategoryTheory.ObjectProperty.IsClosedClass`: a property of objects that holds for zero
  objects and, in a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with `X₁` in it, holds for `X₂`
  exactly when it holds for `X₃`. The objects on which `Ext*(-, F)` vanishes form one
  (`CategoryTheory.isClosedClass_forall_subsingleton_ext`).
* `CategoryTheory.Subfunctor.IsDenseFor F U`: a subfunctor `U` of `Y` is *dense for `F`* if its
  preimage under every map `y : R ⟶ Y` from a corepresentable functor gives an equivalence
  `ℤ[y⁻¹ U] ⟶ ℤ[R]` for `F`; and `CategoryTheory.IsCoverFor F p`: a map `p : E ⟶ Y` is a *cover
  for `F`* if the inclusion of its image gives an equivalence for `F`.
* `CategoryTheory.Functor.CorepresentableBy.freeHomAddEquiv`: the additive Yoneda lemma: if `Y`
  is corepresented by `A`, morphisms `ℤ[Y] ⟶ F` are the elements of `F(A)`. Hence `ℤ[Y]` is
  projective, so its cohomology vanishes in positive degrees (`Ext.eq_zero_of_projective`).
* `CategoryTheory.extFreeCoproductAddEquiv`: the cohomology of a disjoint union of functors is
  the product of the cohomology groups of its pieces, by restriction to the summands.
* `CategoryTheory.ShortComplex.exact_iff_forall_function_exact`: a sequence of functors to abelian
  groups is exact if it is exact at every object.

## References

* [ShortProof]: `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/Cohomology/Etale/Basic.lean` (declarations `New.Variety.IsCohomEquiv`,
  `New.Variety.IsCohomDense`, `New.Variety.homReprEquiv`, `New.Variety.exact_of_app`) and
  `src/Lib/Cohomology/Etale/BijectiveComparisons.lean` (`New.Variety.IsCover`,
  `New.Variety.IsClosedClass`), and `src/Lib/General/Algebra/LongExactSequences.lean`
  (`New.Variety.H.sigma_bijective`, `New.Variety.isCohomEquiv_iff_subsingleton`); Apache 2.0,
  Copyright 2026 Anthropic, PBC. The statements here are adapted from these declarations and
  restated with Mathlib's Ext groups, subfunctors and corepresentable functors.
-/

public section

open CategoryTheory Limits Abelian

universe t w v u

namespace CategoryTheory

/-! ### Equivalences for a coefficient object -/

section IsExtEquivFor

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [HasExt.{t} 𝒜] (F : 𝒜)

/-- A morphism `α : X' ⟶ X` is an *equivalence for* `F` if precomposition with `α` is a bijection
`Extⁿ(X, F) ⟶ Extⁿ(X', F)` for every `n`. -/
def IsExtEquivFor {X X' : 𝒜} (α : X' ⟶ X) : Prop :=
  ∀ n : ℕ, Function.Bijective ((Ext.mk₀ α).precomp F (zero_add n))

variable {F} {X X' X'' : 𝒜}

/-- An isomorphism is an equivalence for every coefficient object. -/
lemma isExtEquivFor_of_isIso (α : X' ⟶ X) [IsIso α] : IsExtEquivFor F α := fun n ↦ by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨(Ext.mk₀ (inv α)).precomp F (zero_add n), fun x ↦ ?_, fun x ↦ ?_⟩ <;>
  simp only [Ext.precomp, Ext.bilinearComp_apply_apply,
    Ext.mk₀_comp_mk₀_assoc, IsIso.inv_hom_id, IsIso.hom_inv_id, Ext.mk₀_id_comp]

/-- Precomposition with a composite is the composite of the precompositions. -/
private lemma precomp_mk₀_comp (α' : X'' ⟶ X') (α : X' ⟶ X) (n : ℕ) :
    ⇑((Ext.mk₀ (α' ≫ α)).precomp F (zero_add n)) =
      (Ext.mk₀ α').precomp F (zero_add n) ∘ (Ext.mk₀ α).precomp F (zero_add n) := by
  ext x
  simp [Ext.mk₀_comp_mk₀_assoc]

/-- Equivalences for `F` compose. -/
lemma IsExtEquivFor.comp {α' : X'' ⟶ X'} {α : X' ⟶ X} (h' : IsExtEquivFor F α')
    (h : IsExtEquivFor F α) : IsExtEquivFor F (α' ≫ α) := fun n ↦ by
  rw [precomp_mk₀_comp]
  exact (h' n).comp (h n)

/-- If `α'` is an equivalence for `F`, then `α' ≫ α` is one exactly when `α` is. -/
lemma IsExtEquivFor.comp_iff_right {α' : X'' ⟶ X'} (h' : IsExtEquivFor F α') (α : X' ⟶ X) :
    IsExtEquivFor F (α' ≫ α) ↔ IsExtEquivFor F α :=
  forall_congr' fun n ↦ by rw [precomp_mk₀_comp]; exact (h' n).of_comp_iff' _

/-- If `α` is an equivalence for `F`, then `α' ≫ α` is one exactly when `α'` is. -/
lemma IsExtEquivFor.comp_iff_left (α' : X'' ⟶ X') {α : X' ⟶ X} (h : IsExtEquivFor F α) :
    IsExtEquivFor F (α' ≫ α) ↔ IsExtEquivFor F α' :=
  forall_congr' fun n ↦ by rw [precomp_mk₀_comp]; exact Function.Bijective.of_comp_iff _ (h n)

variable {S : ShortComplex 𝒜}

/-- If `Ext*(S.X₃, F)` vanishes, the first map of the short exact sequence `S` is an equivalence
for `F`, by the long exact sequence in the first variable. -/
private lemma isExtEquivFor_of_shortExact (hS : S.ShortExact)
    (h : ∀ n, Subsingleton (Ext.{t} S.X₃ F n)) : IsExtEquivFor F S.f := fun n ↦ by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := Ext.contravariant_sequence_exact₂ hS F x hx
    rw [Subsingleton.elim z 0, Ext.comp_zero]
  · exact Ext.contravariant_sequence_exact₁ hS F x (add_comm 1 n) (Subsingleton.elim _ _)

/-- If the first map of the short exact sequence `S` is an equivalence for `F`, then
`Ext*(S.X₃, F)` vanishes: the connecting maps vanish because the maps before them are onto, and
then `Extⁿ(S.X₃, F)` injects into the kernel of an injective map. -/
private lemma subsingleton_ext_of_isExtEquivFor (hS : S.ShortExact) (h : IsExtEquivFor F S.f)
    (n : ℕ) : Subsingleton (Ext.{t} S.X₃ F n) := by
  have hinj : Function.Injective ((Ext.mk₀ S.g).precomp F (zero_add n)) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
    cases n with
    | zero =>
      obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
      have hf : S.g ≫ f = S.g ≫ 0 := by simpa using (Ext.mk₀_bijective _ _).1 (by simpa using hx)
      have := hS.epi_g
      simp [(cancel_epi S.g).1 hf]
    | succ n =>
      obtain ⟨y, rfl⟩ := Ext.contravariant_sequence_exact₃ hS F x hx (add_comm 1 n)
      obtain ⟨z, rfl⟩ := (h n).2 y
      simp
  refine ⟨fun x x' ↦ hinj ?_⟩
  refine (h n).1 ?_
  simp [Ext.mk₀_comp_mk₀_assoc, S.zero]

/-- The first map of a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is an equivalence for `F`
exactly when `Extⁿ(X₃, F)` vanishes for every `n`. -/
lemma isExtEquivFor_iff_of_shortExact (hS : S.ShortExact) :
    IsExtEquivFor F S.f ↔ ∀ n, Subsingleton (Ext.{t} S.X₃ F n) :=
  ⟨subsingleton_ext_of_isExtEquivFor hS, isExtEquivFor_of_shortExact hS⟩

end IsExtEquivFor

/-! ### Closed classes -/

section ClosedClass

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜]

/-- A property `P` of objects of an abelian category is a *closed class* if it holds for every
zero object and, for every short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with `P X₁`, `P X₂`
holds exactly when `P X₃` does. Such a class is closed under extensions
(`CategoryTheory.ObjectProperty.IsClosedClass.isClosedUnderExtensions`). -/
class ObjectProperty.IsClosedClass (P : ObjectProperty 𝒜) : Prop where
  /-- A closed class contains every zero object. -/
  prop_of_isZero {X : 𝒜} : IsZero X → P X
  /-- In a short exact sequence whose first term is in the class, the middle term is in it
  exactly when the last one is. -/
  prop_X₂_iff_prop_X₃ {S : ShortComplex 𝒜} (hS : S.ShortExact) (h₁ : P S.X₁) : P S.X₂ ↔ P S.X₃

/-- A closed class is closed under extensions. -/
instance ObjectProperty.IsClosedClass.isClosedUnderExtensions (P : ObjectProperty 𝒜)
    [P.IsClosedClass] : P.IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := (IsClosedClass.prop_X₂_iff_prop_X₃ hS h₁).2 h₃

variable [HasExt.{t} 𝒜] (F : 𝒜)

/-- The objects `X` with `Extⁿ(X, F) = 0` for every `n` form a closed class. -/
instance isClosedClass_forall_subsingleton_ext :
    ObjectProperty.IsClosedClass fun X : 𝒜 ↦ ∀ n, Subsingleton (Ext.{t} X F n) where
  prop_of_isZero hX n := TauCeti.subsingleton_ext_of_isZero_left hX F n
  prop_X₂_iff_prop_X₃ {S} hS h₁ := by
    -- The long exact sequence makes `Extⁿ(S.X₃, F) ⟶ Extⁿ(S.X₂, F)` bijective.
    have hb (n : ℕ) : Function.Bijective ((Ext.mk₀ S.g).precomp F (zero_add n)) := by
      refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun x ↦ ?_⟩
      · cases n with
        | zero =>
          obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
          have hf : S.g ≫ f = S.g ≫ 0 := by
            simpa using (Ext.mk₀_bijective _ _).1 (by simpa using hx)
          have := hS.epi_g
          simp [(cancel_epi S.g).1 hf]
        | succ n =>
          obtain ⟨y, rfl⟩ := Ext.contravariant_sequence_exact₃ hS F x hx (add_comm 1 n)
          rw [Subsingleton.elim y 0, Ext.comp_zero]
      · exact Ext.contravariant_sequence_exact₂ hS F x (Subsingleton.elim _ _)
    exact forall_congr' fun n ↦ ⟨fun _ ↦ (hb n).1.subsingleton,
      fun _ ↦ (Equiv.ofBijective _ (hb n)).symm.subsingleton⟩

end ClosedClass

/-! ### Objectwise exactness -/

namespace ShortComplex

variable {C : Type u} [Category.{v} C]

/-- A short complex of functors to abelian groups is exact exactly when it is exact at every
object. -/
lemma exact_iff_forall_function_exact (S : ShortComplex (C ⥤ AddCommGrpCat.{w})) :
    S.Exact ↔ ∀ c : C, Function.Exact (S.f.app c) (S.g.app c) := by
  rw [exact_iff_evaluation]
  exact forall_congr' fun c ↦ ab_exact_iff_function_exact (S.map ((evaluation _ _).obj c))

/-- A short complex of functors to abelian groups is short exact if, at every object, its first
map is injective, its last map is surjective, and it is exact in the middle. -/
lemma shortExact_of_forall_function_exact {S : ShortComplex (C ⥤ AddCommGrpCat.{w})}
    (h₁ : ∀ c : C, Function.Injective (S.f.app c))
    (h₂ : ∀ c : C, Function.Exact (S.f.app c) (S.g.app c))
    (h₃ : ∀ c : C, Function.Surjective (S.g.app c)) : S.ShortExact := by
  have (c : C) : Mono (S.f.app c) := (AddCommGrpCat.mono_iff_injective _).2 (h₁ c)
  have (c : C) : Epi (S.g.app c) := (AddCommGrpCat.epi_iff_surjective _).2 (h₃ c)
  have : Mono S.f := NatTrans.mono_of_mono_app _
  have : Epi S.g := NatTrans.epi_of_epi_app _
  exact ShortExact.mk' ((exact_iff_forall_function_exact S).2 h₂) inferInstance inferInstance

end ShortComplex

/-! ### Free abelian functors and relative chains -/

section Free

variable {C : Type u} [Category.{v} C]

/-- The free abelian group functor `ℤ[-]` sends monomorphisms of functors to monomorphisms. -/
instance mono_whiskerRight_free {Y Y' : C ⥤ Type w} (u : Y' ⟶ Y) [Mono u] :
    Mono (Functor.whiskerRight u AddCommGrpCat.free) := by
  have (c : C) : Mono (u.app c) := inferInstance
  exact NatTrans.mono_of_mono_app _

/-- For a subfunctor `U` of `Y`, the sequence `ℤ[U] ⟶ ℤ[Y] ⟶ ℤ[Y] / ℤ[U]` is short exact. Its
long exact Ext sequence is the long exact sequence of the pair `(Y, U)`. -/
lemma Subfunctor.shortExact_free {Y : C ⥤ Type w} (U : Subfunctor Y) :
    (ShortComplex.mk (Functor.whiskerRight U.ι AddCommGrpCat.free)
      (cokernel.π (Functor.whiskerRight U.ι AddCommGrpCat.free))
      (cokernel.condition _)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance

/-! ### The additive Yoneda lemma -/

/-- **Yoneda lemma** for a functor `Y : C ⥤ Type w` corepresented by `A`: natural transformations
from `Y` to a functor `G` are the elements of `G(A)`, by evaluation at the universal element. -/
def Functor.CorepresentableBy.natTransEquiv {Y : C ⥤ Type w} {A : C} (e : Y.CorepresentableBy A)
    (G : C ⥤ Type w) : (Y ⟶ G) ≃ G.obj A where
  toFun φ := φ.app A (e.homEquiv (𝟙 A))
  invFun g :=
    { app _ := ↾fun y ↦ G.map (e.homEquiv.symm y) g
      naturality _ _ f := by
        ext y
        simp [← e.homEquiv_symm_comp] }
  left_inv φ := by
    ext c y
    obtain ⟨f, rfl⟩ := e.homEquiv.surjective y
    simp [← NatTrans.naturality_apply, ← e.homEquiv_comp]
  right_inv g := by simp

/-- The Yoneda bijection evaluates a natural transformation at the universal element. -/
lemma Functor.CorepresentableBy.natTransEquiv_apply {Y : C ⥤ Type w} {A : C}
    (e : Y.CorepresentableBy A) (G : C ⥤ Type w) (φ : Y ⟶ G) :
    e.natTransEquiv G φ = φ.app A (e.homEquiv (𝟙 A)) :=
  (rfl)

/-- **Additive Yoneda lemma.** If `Y : C ⥤ Type w` is corepresented by `A`, morphisms from the
free abelian functor `ℤ[Y]` to `F` are the elements of `F(A)`: a morphism is sent to the image of
the universal element. -/
def Functor.CorepresentableBy.freeHomAddEquiv {Y : C ⥤ Type w} {A : C}
    (e : Y.CorepresentableBy A) (F : C ⥤ AddCommGrpCat.{w}) :
    (Y ⋙ AddCommGrpCat.free ⟶ F) ≃+ F.obj A where
  toEquiv := ((Adjunction.whiskerRight C AddCommGrpCat.adj).homEquiv Y F).trans
    (e.natTransEquiv (F ⋙ forget AddCommGrpCat))
  map_add' _ _ := rfl

/-- The additive Yoneda bijection sends a morphism to its value at the generator given by the
universal element. -/
lemma Functor.CorepresentableBy.freeHomAddEquiv_apply {Y : C ⥤ Type w} {A : C}
    (e : Y.CorepresentableBy A) (F : C ⥤ AddCommGrpCat.{w}) (f : Y ⋙ AddCommGrpCat.free ⟶ F) :
    e.freeHomAddEquiv F f = f.app A (FreeAddCommGroup.of (e.homEquiv (𝟙 A))) :=
  (rfl)

/-- The additive Yoneda bijection is natural in the coefficients. -/
lemma Functor.CorepresentableBy.freeHomAddEquiv_comp {Y : C ⥤ Type w} {A : C}
    (e : Y.CorepresentableBy A) {F G : C ⥤ AddCommGrpCat.{w}} (f : Y ⋙ AddCommGrpCat.free ⟶ F)
    (g : F ⟶ G) : e.freeHomAddEquiv G (f ≫ g) = g.app A (e.freeHomAddEquiv F f) :=
  (rfl)

/-- The free abelian functor on a corepresentable functor is projective. -/
instance projective_free {Y : C ⥤ Type w} [Y.IsCorepresentable] :
    Projective (Y ⋙ AddCommGrpCat.free) where
  factors {E X} f g _ := by
    let e := Y.corepresentableBy
    obtain ⟨x, hx⟩ := (AddCommGrpCat.epi_iff_surjective (g.app _)).1 inferInstance
      (e.freeHomAddEquiv X f)
    refine ⟨(e.freeHomAddEquiv E).symm x, (e.freeHomAddEquiv X).injective ?_⟩
    rw [e.freeHomAddEquiv_comp, AddEquiv.apply_symm_apply, hx]

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
  rw [extFreeCoproductAddEquiv, Ext.coproductAddEquiv_apply]
  rfl

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
