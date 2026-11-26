/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import TauCeti.Algebra.Homology.Ext.LerayHirsch
public import TauCeti.CategoryTheory.Abelian.Devissage
import TauCeti.CategoryTheory.Abelian.FunctorCohomology.Basic

/-!
# Dévissage from representable functors and the Leray–Hirsch theorem for functors

Let `C` be an essentially small category. For a family `c : J → C` of objects write
`ℤ[⊔ⱼ h_{cⱼ}]` for the free abelian functor on the disjoint union of the corepresentable functors
`h_{cⱼ} = Hom(cⱼ, -)`, here `(∐ fun j ↦ shrinkCoyoneda.obj (op (c j))) ⋙ AddCommGrpCat.free`.
Every functor `N : C ⥤ AddCommGrpCat` is a quotient of such a functor
(`CategoryTheory.Functor.exists_epi_free_sigma_shrinkCoyoneda`), with one summand for each element
of each value of `N`, mapped to `N` by the additive Yoneda lemma. So statements about Ext groups of
all functors reduce to the functors `ℤ[⊔ⱼ h_{cⱼ}]`, whose Ext groups are products of those of the
`ℤ[h_{cⱼ}]` (`CategoryTheory.extFreeCoproductAddEquiv`), which vanish in positive degrees.

## Main results

* `TauCeti.bijective_of_forall_bijective_free_sigma_shrinkCoyoneda`: **dévissage**. A family of
  maps `f N n : A N n → B N n`, indexed by the functors `N : C ⥤ AddCommGrpCat` and the degrees `n`,
  which satisfies the two four-lemma steps of `TauCeti.bijective_of_forall_exists_epi` along short
  exact sequences of functors and is bijective in all degrees at every `ℤ[⊔ⱼ h_{cⱼ}]` is bijective
  in all degrees at every functor. Morphisms of contravariant cohomological δ-functors, such as
  maps between Ext groups that are natural and compatible with connecting maps, satisfy the steps.
* `CategoryTheory.Functor.isLerayHirschBasis_whiskeringLeft_of_free_shrinkCoyoneda`: **the
  Leray–Hirsch theorem**. For a functor `φ : C ⥤ A` and finitely many classes
  `θᵢ ∈ Ext^{dᵢ}(φ ⋙ G, F)`, if the Leray–Hirsch map `(wᵢ) ↦ ∑ᵢ φ*(wᵢ) · θᵢ` is bijective at
  `ℤ[h_a]` for every object `a` of `A`, it is bijective at every functor `S : A ⥤ AddCommGrpCat`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 4D.1 (the
  Leray–Hirsch theorem).
* `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/Cohomology/LerayHirsch.lean` (declarations
  `New.Variety.Devissage.allBijective_of_allBijective_sigma_reprBy`,
  `New.Variety.isLerayHirschBasis_of_reprBy`); Apache 2.0, Copyright 2026 Anthropic, PBC. The
  statements are adapted from these declarations.
-/
public section

open CategoryTheory hiding Injective
open Limits Opposite Function Abelian

universe t t' w v u v' u'

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]

/-- Every functor `N : C ⥤ AddCommGrpCat` on an essentially small category is a quotient of the
free abelian functor `ℤ[⊔ⱼ h_{cⱼ}]` on a disjoint union of corepresentable functors. The family
`c` has one member for each element of each value of `N`, up to isomorphism of the objects of `C`,
and the summand of an element `x ∈ N(c)` is sent to `N` by the morphism `ℤ[h_c] ⟶ N` corresponding
to `x`. -/
theorem exists_epi_free_sigma_shrinkCoyoneda [EssentiallySmall.{w} C] (N : C ⥤ AddCommGrpCat.{w}) :
    ∃ (J : Type w) (c : J → C)
      (p : (∐ fun j ↦ shrinkCoyoneda.{w}.obj (op (c j))) ⋙ AddCommGrpCat.free ⟶ N), Epi p := by
  let e := equivSmallModel.{w} C
  let c : (Σ c : SmallModel.{w} C, N.obj (e.inverse.obj c)) → C := fun j ↦ e.inverse.obj j.fst
  let R := fun j ↦ shrinkCoyoneda.{w}.obj (op (c j))
  have := (Adjunction.whiskerRight C AddCommGrpCat.adj.{w}).leftAdjoint_preservesColimits.{w, w}
  -- `ℤ[⊔ⱼ h_{cⱼ}]` is the coproduct of the `ℤ[h_{cⱼ}]`, as `ℤ[-]` is a left adjoint.
  let hc := isColimitCofanMkObjOfIsColimit ((whiskeringRight C _ _).obj AddCommGrpCat.free)
    R _ (coproductIsCoproduct R)
  let x := fun j ↦ ((shrinkCoyonedaCorepresentableBy (op (c j))).freeHomAddEquiv N).symm j.snd
  let p := Cofan.IsColimit.desc hc x
  suffices ∀ d, Epi (p.app d) from ⟨_, c, p, NatTrans.epi_of_epi_app p⟩
  intro d
  rw [AddCommGrpCat.epi_iff_surjective]
  intro z
  -- `z ∈ N(d)` is the image of its transport `N(d ⟶ c')` to the object `c'` of the small model
  -- isomorphic to `d`, which is the image of the generator of the summand of that transport.
  let j : Σ c : SmallModel.{w} C, N.obj (e.inverse.obj c) :=
    ⟨e.functor.obj d, N.map (e.unitIso.hom.app d) z⟩
  let y : (R j).obj d := (shrinkCoyonedaCorepresentableBy (op (c j))).homEquiv (e.unitIso.inv.app d)
  have hp := congrArg (fun φ ↦ φ.app d) (Cofan.IsColimit.fac hc x j)
  replace hp := ConcreteCategory.congr_hom hp (FreeAddCommGroup.of y)
  have hx :=
    (shrinkCoyonedaCorepresentableBy (op (c j))).freeHomAddEquiv_symm_apply_app_of N j.snd y
  rw [NatTrans.comp_app] at hp
  simp only [y, Equiv.symm_apply_apply] at hx
  refine ⟨(AddCommGrpCat.free.map ((Sigma.ι R j).app d)) (FreeAddCommGroup.of y), hp.trans
    (hx.trans ?_)⟩
  simp [j, ← ConcreteCategory.comp_apply, ← Functor.map_comp]

end CategoryTheory.Functor

namespace TauCeti

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {A B : (C ⥤ AddCommGrpCat.{w}) → ℕ → Type*} {f : ∀ N n, A N n → B N n}

/-- **Dévissage from representable functors.** Let `C` be essentially small and let
`f N n : A N n → B N n` be maps, for functors `N : C ⥤ AddCommGrpCat` and degrees `n`, such that
for every short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of functors and every `n`, if `f` is
bijective below `n` at `X₁` and `X₂`, then injectivity of `f X₂ n` gives injectivity of `f X₃ n`,
and injectivity of `f X₁ n` with bijectivity of `f X₂ n` gives surjectivity of `f X₃ n`. If `f` is
bijective in all degrees at the free abelian functor `ℤ[⊔ⱼ h_{cⱼ}]` on every disjoint union of
corepresentable functors, then it is bijective in all degrees at every functor. -/
theorem bijective_of_forall_bijective_free_sigma_shrinkCoyoneda
    (hinj : ∀ ⦃S : ShortComplex (C ⥤ AddCommGrpCat.{w})⦄, S.ShortExact → ∀ n,
      (∀ m < n, Bijective (f S.X₁ m)) → (∀ m < n, Bijective (f S.X₂ m)) →
      Injective (f S.X₂ n) → Injective (f S.X₃ n))
    (hsurj : ∀ ⦃S : ShortComplex (C ⥤ AddCommGrpCat.{w})⦄, S.ShortExact → ∀ n,
      (∀ m < n, Bijective (f S.X₁ m)) → Injective (f S.X₁ n) →
      (∀ m ≤ n, Bijective (f S.X₂ m)) → Surjective (f S.X₃ n))
    (h : ∀ (J : Type w) (c : J → C) (n : ℕ),
      Bijective (f ((∐ fun j ↦ shrinkCoyoneda.{w}.obj (op (c j))) ⋙ AddCommGrpCat.free) n))
    (N : C ⥤ AddCommGrpCat.{w}) (n : ℕ) : Bijective (f N n) :=
  bijective_of_forall_exists_epi hinj hsurj (fun N ↦ by
    obtain ⟨J, c, p, hp⟩ := N.exists_epi_free_sigma_shrinkCoyoneda
    exact ⟨_, p, hp, h J c⟩) N n

end TauCeti

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A] [EssentiallySmall.{w} A]
  [HasExt.{t} (A ⥤ AddCommGrpCat.{w})] [HasExt.{t'} (C ⥤ AddCommGrpCat.{w})]
  [EnoughInjectives (A ⥤ AddCommGrpCat.{w})] [EnoughInjectives (C ⥤ AddCommGrpCat.{w})]
  {G : A ⥤ AddCommGrpCat.{w}} {F : C ⥤ AddCommGrpCat.{w}} {I : Type*} [DecidableEq I] [Finite I]
  {d : I → ℕ}

/-- **The Leray–Hirsch theorem for functors.** Let `φ : C ⥤ A` be a functor with `A` essentially
small, and `θᵢ ∈ Ext^{dᵢ}(φ ⋙ G, F)` finitely many classes. If the `θᵢ` form a Leray–Hirsch basis
for restriction along `φ` at the free abelian functor `ℤ[h_a]` of every object `a` of `A`, that is,
if `(wᵢ) ↦ ∑ᵢ φ*(wᵢ) · θᵢ` is a bijection `⨁ᵢ H*(ℤ[h_a], G) ≃ H*(φ ⋙ ℤ[h_a], F)`, then they form a
Leray–Hirsch basis at every functor `S : A ⥤ AddCommGrpCat`. -/
theorem isLerayHirschBasis_whiskeringLeft_of_free_shrinkCoyoneda (φ : C ⥤ A)
    (θ : ∀ i, Ext.{t'} (φ ⋙ G) F (d i))
    (h : ∀ a : A, ((whiskeringLeft C A AddCommGrpCat.{w}).obj φ).IsLerayHirschBasis θ
      (shrinkCoyoneda.{w}.obj (op a) ⋙ AddCommGrpCat.free))
    (S : A ⥤ AddCommGrpCat.{w}) :
    ((whiskeringLeft C A AddCommGrpCat.{w}).obj φ).IsLerayHirschBasis θ S := by
  refine isLerayHirschBasis_of_forall_exists_epi ((whiskeringLeft C A _).obj φ) θ (fun X ↦ ?_) S
  obtain ⟨J, c, p, hp⟩ := X.exists_epi_free_sigma_shrinkCoyoneda
  refine ⟨_, p, hp, ?_⟩
  -- `ℤ[⊔ⱼ h_{cⱼ}]` is the coproduct of the `ℤ[h_{cⱼ}]`, as `ℤ[-]` is a left adjoint.
  have := (Adjunction.whiskerRight A AddCommGrpCat.adj.{w}).leftAdjoint_preservesColimits.{w, w}
  exact isLerayHirschBasis_of_isColimit ((whiskeringLeft C A _).obj φ) θ
    (isColimitCofanMkObjOfIsColimit ((whiskeringRight A _ _).obj AddCommGrpCat.free) _ _
      (coproductIsCoproduct _)) fun j ↦ h (c j)

end CategoryTheory.Functor
