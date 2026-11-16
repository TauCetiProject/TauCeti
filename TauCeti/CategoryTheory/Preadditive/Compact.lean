/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Shift.Basic
public import TauCeti.Algebra.Category.Grp.Coproducts

import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Objects compact for coproducts in a preadditive category

An object `G` of a preadditive category `T` (with morphisms in `Type v`) is *compact for
coproducts* (`TauCeti.IsCompactForCoproducts G`) if its additive corepresented functor
`preadditiveCoyoneda.obj (op G) : T ⥤ AddCommGrpCat.{v}` preserves all coproducts indexed by types
in `Type v`.

For any family `f : J → T` with a coproduct, there is a canonical additive comparison homomorphism
`TauCeti.coprodComparisonAddHom G f : (⨁ j, (G ⟶ f j)) →+ (G ⟶ ∐ f)` sending a morphism
`g : G ⟶ f j` in the `j`-th summand to `g ≫ Sigma.ι f j`. Since coproducts in `AddCommGrpCat`
are computed by external direct sums (`AddCommGrpCat.coproductCoconeIsColimit`), the functor
`Hom(G, -)` preserves the coproduct of `f` if and only if `coprodComparisonAddHom G f` is bijective
(`TauCeti.preservesColimit_discrete_preadditiveCoyoneda_iff`). Consequently, compactness is
characterized by bijectivity of this comparison map on all small coproducts
(`TauCeti.isCompactForCoproducts_iff`), yielding the additive equivalence
`TauCeti.IsCompactForCoproducts.homCoprodEquiv : (⨁ j, (G ⟶ f j)) ≃+ (G ⟶ ∐ f)` retaining
the canonical inclusions `Sigma.ι`.

Compactness is invariant under isomorphism, holds for zero objects, and is closed under retracts,
finite coproducts (in particular binary biproducts and finite biproducts), additive equivalences,
and shifts. Conversely, a countable coproduct of copies of any nonzero object is never compact
(`TauCeti.not_isCompactForCoproducts_sigma_nat`), while `ULift ℤ` is compact in `AddCommGrpCat`
(`TauCeti.isCompactForCoproducts_uliftInt`).

## Main definitions

* `TauCeti.IsCompactForCoproducts`: compactness with respect to `Type v`-indexed coproducts.
* `TauCeti.coprodComparisonAddHom`: the canonical map `(⨁ j, (G ⟶ f j)) →+ (G ⟶ ∐ f)`.
* `TauCeti.IsCompactForCoproducts.homCoprodEquiv`: the direct-sum equivalence
  `(⨁ j, (G ⟶ f j)) ≃+ (G ⟶ ∐ f)` for a compact object `G`.

## Main results

* `TauCeti.isCompactForCoproducts_iff`: characterization via bijectivity of
  `coprodComparisonAddHom`.
* `TauCeti.IsCompactForCoproducts.of_iso`, `TauCeti.isCompactForCoproducts_of_isZero`,
  `TauCeti.IsCompactForCoproducts.of_retract`,
  `TauCeti.IsCompactForCoproducts.coproduct_of_finite`,
  `TauCeti.IsCompactForCoproducts.biprod`, `TauCeti.IsCompactForCoproducts.shift`: closure
  properties.
* `TauCeti.not_isCompactForCoproducts_sigma_nat`: a countable coproduct of copies of a nonzero
  object is not compact.
* `TauCeti.isCompactForCoproducts_uliftInt`: `AddCommGrpCat.of (ULift ℤ)` is compact in
  `AddCommGrpCat`.

## References

* A. Neeman, *Triangulated categories*, Annals of Mathematics Studies 148, Princeton University
  Press (2001), Definition 4.2.7.
* S. Schwede, *Symmetric spectra*, Chapter II, Definition 5.4.
-/

public section

open CategoryTheory Limits ZeroObject Opposite
open scoped DirectSum

universe w v u u'

namespace TauCeti

section Basic

variable {T : Type u} [Category.{v} T] [Preadditive T]

/-- An object `G` of a preadditive category `T` is *compact for coproducts* if its additive
corepresented functor `Hom(G, -)` preserves all coproducts indexed by types in the morphism
universe. -/
def IsCompactForCoproducts (G : T) : Prop :=
  ∀ J : Type v, PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (op G))

theorem isCompactForCoproducts_iff_preservesColimitsOfShape (G : T) :
    IsCompactForCoproducts G ↔
      ∀ J : Type v, PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (op G)) :=
  Iff.rfl

/-- A compact object's corepresented functor preserves coproducts indexed by any `v`-small type,
such as `ℕ` or any finite type. -/
theorem IsCompactForCoproducts.preservesColimitsOfShape {G : T}
    (hG : IsCompactForCoproducts G) (J : Type w) [Small.{v} J] :
    PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (op G)) :=
  have := hG (Shrink.{v} J)
  preservesColimitsOfShape_of_equiv (Discrete.equivalence (equivShrink.{v} J)).symm _

/-- Compactness is invariant under isomorphism. -/
theorem IsCompactForCoproducts.of_iso {G G' : T} (e : G ≅ G') (hG : IsCompactForCoproducts G) :
    IsCompactForCoproducts G' := fun J ↦
  have := hG J
  preservesColimitsOfShape_of_natIso (preadditiveCoyoneda.mapIso e.symm.op)

theorem isCompactForCoproducts_iff_of_iso {G G' : T} (e : G ≅ G') :
    IsCompactForCoproducts G ↔ IsCompactForCoproducts G' :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

/-- The canonical comparison homomorphism `⨁ j, (G ⟶ f j) →+ (G ⟶ ∐ f)` sending a morphism
`g : G ⟶ f j` in the `j`-th summand to `g ≫ Sigma.ι f j`. -/
noncomputable def coprodComparisonAddHom (G : T) {J : Type w} [DecidableEq J] (f : J → T)
    [HasCoproduct f] : (⨁ j, (G ⟶ f j)) →+ (G ⟶ ∐ f) :=
  DirectSum.toAddMonoid fun j ↦ Preadditive.rightComp G (Sigma.ι f j)

@[simp]
theorem coprodComparisonAddHom_of (G : T) {J : Type w} [DecidableEq J] (f : J → T)
    [HasCoproduct f] (j : J) (g : G ⟶ f j) :
    coprodComparisonAddHom G f (DirectSum.of (fun j ↦ G ⟶ f j) j g) = g ≫ Sigma.ι f j := by
  simp [coprodComparisonAddHom, Preadditive.rightComp]

theorem coprodComparisonAddHom_apply (G : T) {J : Type w} [DecidableEq J] (f : J → T)
    [HasCoproduct f] [∀ j (x : G ⟶ f j), Decidable (x ≠ 0)] (a : ⨁ j, (G ⟶ f j)) :
    coprodComparisonAddHom G f a = ∑ j ∈ a.support, a j ≫ Sigma.ι f j := by
  conv_lhs => rw [← DirectSum.sum_support_of a]
  simp [map_sum]

/-- Naturality of `coprodComparisonAddHom` in the source object `G`. -/
theorem coprodComparisonAddHom_naturality_left {G' G : T} (α : G' ⟶ G) {J : Type w}
    [DecidableEq J] (f : J → T) [HasCoproduct f] (a : ⨁ j, (G ⟶ f j)) :
    coprodComparisonAddHom G' f
        (DirectSum.map (fun j ↦ Preadditive.leftComp (f j) α) a) =
      α ≫ coprodComparisonAddHom G f a := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of j g => simp [Preadditive.leftComp]
  | add a b ha hb => simp [map_add, ha, hb, Preadditive.comp_add]

/-- Naturality of `coprodComparisonAddHom` in the coproduct family `f`. -/
theorem coprodComparisonAddHom_naturality_right (G : T) {J : Type w} [DecidableEq J]
    {f f' : J → T} [HasCoproduct f] [HasCoproduct f'] (φ : ∀ j, f j ⟶ f' j)
    (a : ⨁ j, (G ⟶ f j)) :
    coprodComparisonAddHom G f'
        (DirectSum.map (fun j ↦ Preadditive.rightComp G (φ j)) a) =
      coprodComparisonAddHom G f a ≫ Limits.Sigma.map φ := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of j g => simp [Preadditive.rightComp]
  | add a b ha hb => simp [map_add, ha, hb, Preadditive.add_comp]

/-- Reindexing a coproduct along an equivalence of index types intertwines the direct-sum
comparison maps. -/
theorem coprodComparisonAddHom_equivCongrLeft (G : T) {J : Type w} {K : Type*} [DecidableEq J]
    [DecidableEq K] (e : J ≃ K) (f : J → T) [HasCoproduct f] [HasCoproduct (f ∘ e.symm)]
    (a : ⨁ j, (G ⟶ f j)) :
    coprodComparisonAddHom G (f ∘ e.symm)
        (DirectSum.equivCongrLeft (β := fun j ↦ G ⟶ f j) e a) =
      coprodComparisonAddHom G f a ≫ (Limits.Sigma.reindex e.symm f).inv := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of j g =>
    obtain ⟨k, rfl⟩ := e.symm.surjective j
    rw [DirectSum.equivCongrLeft_of, coprodComparisonAddHom_of]
    have hof : DirectSum.of (fun k' ↦ G ⟶ f (e.symm k')) k g =
        DirectSum.of (fun k' ↦ G ⟶ (f ∘ e.symm) k') k g := rfl
    rw [hof, coprodComparisonAddHom_of]
    simp
  | add a b ha hb => simp [map_add, ha, hb, Preadditive.add_comp]

/-- The corepresented functor `Hom(G, -)` preserves a `Type v`-indexed coproduct `∐ f` if and only
if the direct-sum comparison homomorphism `coprodComparisonAddHom G f` is bijective. -/
theorem preservesColimit_discrete_preadditiveCoyoneda_iff_sameUniv (G : T) {J : Type v}
    [DecidableEq J] (f : J → T) [HasCoproduct f] :
    PreservesColimit (Discrete.functor f) (preadditiveCoyoneda.obj (op G)) ↔
      Function.Bijective (coprodComparisonAddHom G f) := by
  let F := preadditiveCoyoneda.obj (op G)
  let c := AddCommGrpCat.coproductCocone (fun j ↦ F.obj (f j))
  let hc : IsColimit c := AddCommGrpCat.coproductCoconeIsColimit (fun j ↦ F.obj (f j))
  let d : Cofan (fun j ↦ F.obj (f j)) := Cofan.mk (F.obj (∐ f)) fun j ↦ F.map (Sigma.ι f j)
  let idFwd (j : J) : ↑(F.obj (f j)) →+ (G ⟶ f j) :=
    { toFun := id, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  let idBwd (j : J) : (G ⟶ f j) →+ ↑(F.obj (f j)) :=
    { toFun := id, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  let eDS : (⨁ j, ↑(F.obj (f j))) ≃+ (⨁ j, (G ⟶ f j)) :=
    { toFun := DirectSum.map idFwd
      invFun := DirectSum.map idBwd
      left_inv := fun a ↦ DFunLike.congr_fun
        (DirectSum.addHom_ext fun j x ↦ by simp [idFwd, idBwd]; rfl :
          (DirectSum.map idBwd).comp (DirectSum.map idFwd) = AddMonoidHom.id _) a
      right_inv := fun a ↦ DFunLike.congr_fun
        (DirectSum.addHom_ext fun j x ↦ by simp [idFwd, idBwd]; rfl :
          (DirectSum.map idFwd).comp (DirectSum.map idBwd) = AddMonoidHom.id _) a
      map_add' := map_add (DirectSum.map idFwd) }
  have hdesc :
      ((AddCommGrpCat.coproductCoconeIsColimit fun j ↦ F.obj (f j)).desc d).hom =
        (coprodComparisonAddHom G f).comp eDS.toAddMonoidHom := by
    rw [AddCommGrpCat.coproductCoconeIsColimit_desc]
    refine DirectSum.addHom_ext fun j g ↦ ?_
    have hL : (DirectSum.toAddMonoid fun i ↦ (d.inj i).hom)
        (DirectSum.of (fun i ↦ ↑(F.obj (f i))) j g) = (d.inj j).hom g :=
      DirectSum.toAddMonoid_of (fun i ↦ (d.inj i).hom) j g
    have hR : coprodComparisonAddHom G f
        (DirectSum.map idFwd (DirectSum.of (fun i ↦ ↑(F.obj (f i))) j g)) =
        idFwd j g ≫ Sigma.ι f j := by
      rw [DirectSum.map_of, coprodComparisonAddHom_of]
    exact hL.trans hR.symm
  have hbij_iff :
      Function.Bijective (hc.desc d) ↔ Function.Bijective (coprodComparisonAddHom G f) := by
    have hfun : ⇑(hc.desc d) = ⇑(coprodComparisonAddHom G f) ∘ ⇑eDS :=
      funext fun a ↦ DFunLike.congr_fun hdesc a
    rw [hfun]
    exact Function.Bijective.of_comp_iff _ eDS.bijective
  constructor
  · intro _
    have hd : IsColimit d := isColimitOfHasCoproductOfPreservesColimit F f
    have heq : hc.desc d = (hc.coconePointUniqueUpToIso hd).hom :=
      hc.uniq d _ fun j ↦ hc.comp_coconePointUniqueUpToIso_hom hd j
    have hiso : IsIso (hc.desc d) := heq ▸ inferInstance
    exact hbij_iff.1 ((ConcreteCategory.isIso_iff_bijective _).1 hiso)
  · intro hbij
    have hiso : IsIso (hc.desc d) := (ConcreteCategory.isIso_iff_bijective _).2 (hbij_iff.2 hbij)
    have hd : IsColimit d :=
      IsColimit.ofIsoColimit hc (Cocone.ext (asIso (hc.desc d)) fun ⟨j⟩ ↦ hc.fac d ⟨j⟩)
    exact preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct f)
      ((isColimitMapCoconeCofanMkEquiv F f (Sigma.ι f)).symm hd)

/-- For any `v`-small index type `J`, the corepresented functor `Hom(G, -)` preserves `∐ f` if and
only if the direct-sum comparison homomorphism `coprodComparisonAddHom G f` is bijective. -/
theorem preservesColimit_discrete_preadditiveCoyoneda_iff (G : T) {J : Type w} [DecidableEq J]
    [Small.{v} J] (f : J → T) [HasCoproduct f] :
    PreservesColimit (Discrete.functor f) (preadditiveCoyoneda.obj (op G)) ↔
      Function.Bijective (coprodComparisonAddHom G f) := by
  classical
  let F := preadditiveCoyoneda.obj (op G)
  let e : J ≃ Shrink.{v} J := equivShrink.{v} J
  let eqv : Discrete (Shrink.{v} J) ≌ Discrete J := Discrete.equivalence e.symm
  let iso : eqv.functor ⋙ Discrete.functor f ≅ Discrete.functor (f ∘ e.symm) :=
    Discrete.natIso fun ⟨k⟩ ↦ Iso.refl (f (e.symm k))
  let c := colimit.cocone (Discrete.functor f)
  let hc : IsColimit c := colimit.isColimit (Discrete.functor f)
  let c' : Cocone (Discrete.functor (f ∘ e.symm)) :=
    (Cocone.precompose iso.inv).obj (c.whisker eqv.functor)
  have hc' : IsColimit c' :=
    (IsColimit.precomposeInvEquiv iso _).symm (hc.whiskerEquivalence eqv)
  have : HasCoproduct (f ∘ e.symm) := ⟨⟨⟨c', hc'⟩⟩⟩
  have hmapIso :
      F.mapCocone c' ≅
        (Cocone.precompose (Functor.whiskerRight iso.inv F)).obj
          ((F.mapCocone c).whisker eqv.functor) :=
    Cocone.ext (Iso.refl _) fun ⟨k⟩ ↦ by simp [c', iso]
  have hpres : PreservesColimit (Discrete.functor f) F ↔
      PreservesColimit (Discrete.functor (f ∘ e.symm)) F := by
    refine ⟨fun _ ↦ preservesColimit_of_preserves_colimit_cocone hc' <|
        IsColimit.ofIsoColimit
          ((IsColimit.precomposeInvEquiv (Functor.isoWhiskerRight iso F) _).symm
            ((isColimitOfPreserves F hc).whiskerEquivalence eqv)) hmapIso.symm,
      fun _ ↦ preservesColimit_of_preserves_colimit_cocone hc <|
        IsColimit.ofWhiskerEquivalence eqv <|
          (IsColimit.precomposeInvEquiv (Functor.isoWhiskerRight iso F) _)
            (IsColimit.ofIsoColimit (isColimitOfPreserves F hc') hmapIso)⟩
  rw [hpres, preservesColimit_discrete_preadditiveCoyoneda_iff_sameUniv G (f ∘ e.symm)]
  let equivDS : (⨁ j, (G ⟶ f j)) ≃+ (⨁ k, (G ⟶ (f ∘ e.symm) k)) :=
    DirectSum.equivCongrLeft (β := fun j ↦ G ⟶ f j) e
  have hcomp :
      ⇑(coprodComparisonAddHom G (f ∘ e.symm)) ∘ ⇑equivDS =
        (fun g : G ⟶ ∐ f ↦ g ≫ (Limits.Sigma.reindex e.symm f).inv) ∘
          ⇑(coprodComparisonAddHom G f) :=
    funext (coprodComparisonAddHom_equivCongrLeft G e f)
  have hpost :
      Function.Bijective (fun g : G ⟶ ∐ f ↦ g ≫ (Limits.Sigma.reindex e.symm f).inv) := by
    have hEq : (fun g : G ⟶ ∐ f ↦ g ≫ (Limits.Sigma.reindex e.symm f).inv) =
        ⇑((Iso.refl G).homCongr (Limits.Sigma.reindex e.symm f).symm) :=
      funext fun g ↦ by simp
    rw [hEq]
    exact Equiv.bijective _
  rw [← Function.Bijective.of_comp_iff _ equivDS.bijective, hcomp, hpost.of_comp_iff']

/-- An object `G` is compact for coproducts if and only if the direct-sum comparison map
`(⨁ j, (G ⟶ f j)) →+ (G ⟶ ∐ f)` is bijective for every `Type v`-indexed coproduct. -/
theorem isCompactForCoproducts_iff (G : T) :
    IsCompactForCoproducts G ↔
      ∀ (J : Type v) [DecidableEq J] (f : J → T) [HasCoproduct f],
        Function.Bijective (coprodComparisonAddHom G f) := by
  constructor
  · intro hG J _ f _
    have := hG J
    exact (preservesColimit_discrete_preadditiveCoyoneda_iff_sameUniv G f).1 inferInstance
  · intro h J
    classical
    have (f : J → T) :
        PreservesColimit (Discrete.functor f) (preadditiveCoyoneda.obj (op G)) := by
      refine ⟨fun {c} hc ↦ ?_⟩
      have : HasCoproduct f := ⟨⟨⟨c, hc⟩⟩⟩
      have : PreservesColimit (Discrete.functor f) (preadditiveCoyoneda.obj (op G)) :=
        (preservesColimit_discrete_preadditiveCoyoneda_iff_sameUniv G f).2 (h J f)
      exact ⟨isColimitOfPreserves (preadditiveCoyoneda.obj (op G)) hc⟩
    exact preservesColimitsOfShape_of_discrete (preadditiveCoyoneda.obj (op G))

/-- For a compact object `G` and any `v`-small family `f` with a coproduct, the direct-sum
comparison map `coprodComparisonAddHom G f` is bijective. -/
theorem IsCompactForCoproducts.bijective_coprodComparisonAddHom {G : T}
    (hG : IsCompactForCoproducts G) {J : Type w} [DecidableEq J] [Small.{v} J]
    (f : J → T) [HasCoproduct f] :
    Function.Bijective (coprodComparisonAddHom G f) :=
  have := hG.preservesColimitsOfShape J
  (preservesColimit_discrete_preadditiveCoyoneda_iff G f).1 inferInstance

/-- Compactness identifies morphisms from `G` into a `v`-small coproduct `∐ f` with the external
direct sum of the component homomorphism groups `G ⟶ f j`, sending the `j`-th summand inclusion
to postcomposition with `Sigma.ι f j`. -/
noncomputable def IsCompactForCoproducts.homCoprodEquiv {G : T}
    (hG : IsCompactForCoproducts G) {J : Type w} [DecidableEq J] [Small.{v} J]
    (f : J → T) [HasCoproduct f] :
    (⨁ j, (G ⟶ f j)) ≃+ (G ⟶ ∐ f) :=
  AddEquiv.ofBijective (coprodComparisonAddHom G f) (hG.bijective_coprodComparisonAddHom f)

@[simp]
theorem IsCompactForCoproducts.homCoprodEquiv_apply {G : T}
    (hG : IsCompactForCoproducts G) {J : Type w} [DecidableEq J] [Small.{v} J]
    (f : J → T) [HasCoproduct f] (a : ⨁ j, (G ⟶ f j)) :
    hG.homCoprodEquiv f a = coprodComparisonAddHom G f a :=
  (rfl)

theorem IsCompactForCoproducts.homCoprodEquiv_of {G : T}
    (hG : IsCompactForCoproducts G) {J : Type w} [DecidableEq J] [Small.{v} J]
    (f : J → T) [HasCoproduct f] (j : J) (g : G ⟶ f j) :
    hG.homCoprodEquiv f (DirectSum.of (fun j ↦ G ⟶ f j) j g) = g ≫ Sigma.ι f j :=
  coprodComparisonAddHom_of G f j g

@[simp]
theorem IsCompactForCoproducts.homCoprodEquiv_symm_comp_ι {G : T}
    (hG : IsCompactForCoproducts G) {J : Type w} [DecidableEq J] [Small.{v} J]
    (f : J → T) [HasCoproduct f] (j : J) (g : G ⟶ f j) :
    (hG.homCoprodEquiv f).symm (g ≫ Sigma.ι f j) = DirectSum.of (fun j ↦ G ⟶ f j) j g := by
  apply (hG.homCoprodEquiv f).injective
  simp

/-- Every morphism from a compact object `G` into a `v`-small coproduct `∐ f` is a finite sum of
morphisms factoring through the summand inclusions `Sigma.ι f j`. -/
theorem IsCompactForCoproducts.exists_finset_sum_comp_ι {G : T}
    (hG : IsCompactForCoproducts G) {J : Type w} [Small.{v} J]
    (f : J → T) [HasCoproduct f] (g : G ⟶ ∐ f) :
    ∃ (s : Finset J) (h : ∀ j, G ⟶ f j), g = ∑ j ∈ s, h j ≫ Sigma.ι f j := by
  classical
  obtain ⟨a, rfl⟩ := (hG.bijective_coprodComparisonAddHom f).2 g
  exact ⟨a.support, fun j ↦ a j, coprodComparisonAddHom_apply G f a⟩

end Basic

section Closure

variable {T : Type u} [Category.{v} T] [Preadditive T]

/-- Every zero object is compact for coproducts. -/
theorem isCompactForCoproducts_of_isZero {G : T} (hG : IsZero G) :
    IsCompactForCoproducts G := by
  rw [isCompactForCoproducts_iff]
  intro J _ f _
  have (j : J) : Subsingleton (G ⟶ f j) := ⟨fun x y ↦ hG.eq_of_src x y⟩
  have : Subsingleton (G ⟶ ∐ f) := ⟨fun x y ↦ hG.eq_of_src x y⟩
  exact ⟨fun a b _ ↦ Subsingleton.elim a b, fun g ↦ ⟨0, Subsingleton.elim _ g⟩⟩

/-- The chosen zero object is compact for coproducts. -/
theorem isCompactForCoproducts_zero [HasZeroObject T] :
    IsCompactForCoproducts (0 : T) :=
  isCompactForCoproducts_of_isZero (Limits.isZero_zero T)

/-- Retracts of compact objects are compact. -/
theorem IsCompactForCoproducts.of_retract {G H : T} (r : Retract G H)
    (hH : IsCompactForCoproducts H) : IsCompactForCoproducts G := by
  rw [isCompactForCoproducts_iff] at hH ⊢
  intro J _ f _
  have hcomp_id :
      (DirectSum.map (fun j ↦ Preadditive.leftComp (f j) r.i)).comp
        (DirectSum.map (fun j ↦ Preadditive.leftComp (f j) r.r)) =
          AddMonoidHom.id _ := by
    refine DirectSum.addHom_ext fun j g ↦ ?_
    simp [Preadditive.leftComp, ← Category.assoc, r.retract]
  constructor
  · intro a b hab
    have h' : coprodComparisonAddHom H f
          (DirectSum.map (fun j ↦ Preadditive.leftComp (f j) r.r) a) =
        coprodComparisonAddHom H f
          (DirectSum.map (fun j ↦ Preadditive.leftComp (f j) r.r) b) := by
      rw [coprodComparisonAddHom_naturality_left, coprodComparisonAddHom_naturality_left, hab]
    have h'' := (hH J f).1 h'
    have := congrArg (DirectSum.map (fun j ↦ Preadditive.leftComp (f j) r.i)) h''
    simpa only [← AddMonoidHom.comp_apply, hcomp_id, AddMonoidHom.id_apply] using this
  · intro g
    obtain ⟨b, hb⟩ := (hH J f).2 (r.r ≫ g)
    refine ⟨DirectSum.map (fun j ↦ Preadditive.leftComp (f j) r.i) b, ?_⟩
    rw [coprodComparisonAddHom_naturality_left, hb, ← Category.assoc, r.retract, Category.id_comp]

/-- Finite coproducts of compact objects are compact. -/
theorem IsCompactForCoproducts.coproduct_of_finite {K : Type w} [Finite K] (X : K → T)
    [HasCoproduct X] (hX : ∀ k, IsCompactForCoproducts (X k)) :
    IsCompactForCoproducts (∐ X) := by
  rw [isCompactForCoproducts_iff]
  intro J _ f _
  classical
  have : Fintype K := Fintype.ofFinite K
  constructor
  · intro a b hab
    refine DFinsupp.ext fun j ↦ Sigma.hom_ext _ _ fun k ↦ ?_
    have hk := (hX k).bijective_coprodComparisonAddHom f
    have heq :
        DirectSum.map (fun j ↦ Preadditive.leftComp (f j) (Sigma.ι X k)) a =
          DirectSum.map (fun j ↦ Preadditive.leftComp (f j) (Sigma.ι X k)) b :=
      hk.1 <| by
        rw [coprodComparisonAddHom_naturality_left, coprodComparisonAddHom_naturality_left, hab]
    simpa [Preadditive.leftComp] using congrArg (fun z : ⨁ j, (X k ⟶ f j) ↦ z j) heq
  · intro g
    choose b hb using fun k ↦ ((hX k).bijective_coprodComparisonAddHom f).2 (Sigma.ι X k ≫ g)
    let S : Finset J := Finset.univ.biUnion fun k ↦ (b k).support
    let a : ⨁ j, (∐ X ⟶ f j) :=
      ∑ j ∈ S, DirectSum.of (fun j ↦ ∐ X ⟶ f j) j (Sigma.desc fun k ↦ b k j)
    refine ⟨a, Sigma.hom_ext _ _ fun k ↦ ?_⟩
    rw [← coprodComparisonAddHom_naturality_left]
    have hmap :
        DirectSum.map (fun j ↦ Preadditive.leftComp (f j) (Sigma.ι X k)) a = b k := by
      have hterm (j : J) :
          DirectSum.map (fun j ↦ Preadditive.leftComp (f j) (Sigma.ι X k))
              (DirectSum.of (fun j ↦ ∐ X ⟶ f j) j (Sigma.desc fun k ↦ b k j)) =
            DirectSum.of (fun j ↦ X k ⟶ f j) j (b k j) := by
        rw [DirectSum.map_of]
        simp [Preadditive.leftComp]
      simp only [a, map_sum, hterm]
      conv_rhs => rw [← DirectSum.sum_support_of (b k)]
      symm
      refine Finset.sum_subset (f := fun j ↦ DirectSum.of (fun j ↦ X k ⟶ f j) j (b k j))
        (Finset.subset_biUnion_of_mem (fun k ↦ (b k).support) (Finset.mem_univ k))
        fun j _ hj ↦ ?_
      have hbj : b k j = 0 := DFinsupp.notMem_support_iff.1 hj
      rw [hbj, map_zero]
    rw [hmap, hb k]

/-- Binary biproducts of compact objects are compact. -/
theorem IsCompactForCoproducts.biprod {X Y : T} [HasBinaryBiproduct X Y]
    (hX : IsCompactForCoproducts X) (hY : IsCompactForCoproducts Y) :
    IsCompactForCoproducts (X ⊞ Y) := by
  let inj : ∀ b : Bool, (match b with | true => X | false => Y) ⟶ X ⊞ Y
    | true => biprod.inl
    | false => biprod.inr
  have hc : IsColimit (Cofan.mk (X ⊞ Y) inj) :=
    Cofan.IsColimit.mk _ (fun s ↦ biprod.desc (s.inj true) (s.inj false))
      (fun s b ↦ by cases b <;> simp [inj])
      (fun s m h ↦ biprod.hom_ext' _ _ (by simpa [inj] using h true)
        (by simpa [inj] using h false))
  have : HasCoproduct (fun b : Bool ↦ match b with | true => X | false => Y) :=
    ⟨⟨⟨_, hc⟩⟩⟩
  have he : (∐ fun b : Bool ↦ match b with | true => X | false => Y) ≅ X ⊞ Y :=
    (colimit.isColimit _).coconePointUniqueUpToIso hc
  refine (IsCompactForCoproducts.coproduct_of_finite
      (fun b : Bool ↦ match b with | true => X | false => Y) fun b ↦ ?_).of_iso he
  cases b
  · exact hY
  · exact hX

/-- Finite biproducts of compact objects are compact. -/
theorem IsCompactForCoproducts.biproduct {K : Type w} [Finite K] (X : K → T) [HasBiproduct X]
    (hX : ∀ k, IsCompactForCoproducts (X k)) :
    IsCompactForCoproducts (Limits.biproduct X) := by
  have : HasCoproduct X := ⟨⟨⟨_, biproduct.isColimit X⟩⟩⟩
  exact (IsCompactForCoproducts.coproduct_of_finite X hX).of_iso
    ((colimit.isColimit _).coconePointUniqueUpToIso (biproduct.isColimit X))

/-- Additive equivalences preserve compactness for coproducts. -/
theorem IsCompactForCoproducts.map_of_equivalence {T' : Type u'} [Category.{v} T']
    [Preadditive T'] (e : T ≌ T') [e.functor.Additive] {G : T} (hG : IsCompactForCoproducts G) :
    IsCompactForCoproducts (e.functor.obj G) := by
  intro J
  have := hG J
  have : PreservesColimitsOfShape (Discrete J) (e.inverse ⋙ preadditiveCoyoneda.obj (op G)) :=
    comp_preservesColimitsOfShape e.inverse (preadditiveCoyoneda.obj (op G))
  let homAddEquiv (X : T') : (G ⟶ e.inverse.obj X) ≃+ (e.functor.obj G ⟶ X) :=
    { toEquiv := (e.toAdjunction.homEquiv G X).symm
      map_add' := fun f g ↦ by
        simp [Adjunction.homEquiv_symm_apply, e.functor.map_add, Preadditive.add_comp] }
  let α : e.inverse ⋙ preadditiveCoyoneda.obj (op G) ≅
      preadditiveCoyoneda.obj (op (e.functor.obj G)) :=
    NatIso.ofComponents (fun X ↦ (homAddEquiv X).toAddCommGrpIso) fun {X Y} φ ↦ by
      ext (f : G ⟶ e.inverse.obj X)
      exact e.toAdjunction.homEquiv_naturality_right_symm f φ
  exact preservesColimitsOfShape_of_natIso α

/-- Compactness for coproducts is invariant under additive equivalences. -/
theorem isCompactForCoproducts_map_of_equivalence_iff {T' : Type u'} [Category.{v} T']
    [Preadditive T'] (e : T ≌ T') [e.functor.Additive] (G : T) :
    IsCompactForCoproducts (e.functor.obj G) ↔ IsCompactForCoproducts G :=
  ⟨fun h ↦
      have : e.symm.functor.Additive := inferInstanceAs e.inverse.Additive
      (h.map_of_equivalence e.symm).of_iso (e.unitIso.symm.app G),
    fun h ↦ h.map_of_equivalence e⟩

/-- Shifts of compact objects are compact, for any group-indexed shift whose shift functor is
additive. -/
theorem IsCompactForCoproducts.shift {A : Type*} [AddGroup A] [HasShift T A] {G : T}
    (hG : IsCompactForCoproducts G) (a : A) [(shiftFunctor T a).Additive] :
    IsCompactForCoproducts (G⟦a⟧) :=
  have : (shiftEquiv T a).functor.Additive := inferInstanceAs (shiftFunctor T a).Additive
  hG.map_of_equivalence (shiftEquiv T a)

theorem isCompactForCoproducts_shift_iff {A : Type*} [AddGroup A] [HasShift T A] (G : T) (a : A)
    [(shiftFunctor T a).Additive] :
    IsCompactForCoproducts (G⟦a⟧) ↔ IsCompactForCoproducts G :=
  have : (shiftEquiv T a).functor.Additive := inferInstanceAs (shiftFunctor T a).Additive
  isCompactForCoproducts_map_of_equivalence_iff (shiftEquiv T a) G

end Closure

section Examples

/-- In any preadditive category with countable coproducts, a countable coproduct of copies of a
nonzero object is never compact: its identity morphism does not factor through any finite
subcoproduct. -/
theorem not_isCompactForCoproducts_sigma_nat {T : Type u} [Category.{v} T] [Preadditive T]
    {X : T} (hX : ¬ IsZero X) [HasCoproductsOfShape ℕ T] :
    ¬ IsCompactForCoproducts (∐ fun _ : ℕ ↦ X) := by
  classical
  intro hC
  let f : ℕ → T := fun _ ↦ X
  obtain ⟨s, h, hid⟩ := hC.exists_finset_sum_comp_ι f (𝟙 (∐ f))
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m ∉ s := Infinite.exists_notMem_finset s
  let p : (∐ f) ⟶ X := Sigma.desc fun n ↦ if n = m then 𝟙 X else 0
  have hp (n : ℕ) : Sigma.ι f n ≫ p = if n = m then 𝟙 X else 0 := Sigma.ι_comp_desc _ n
  have hzero : (𝟙 X : X ⟶ X) = 0 := by
    calc
      𝟙 X = Sigma.ι f m ≫ 𝟙 (∐ f) ≫ p := by simp [hp]
      _ = Sigma.ι f m ≫ (∑ n ∈ s, h n ≫ Sigma.ι f n) ≫ p := by rw [hid]
      _ = ∑ n ∈ s, Sigma.ι f m ≫ h n ≫ (Sigma.ι f n ≫ p) := by
        simp [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
      _ = ∑ _ ∈ s, (0 : X ⟶ X) := by
        refine Finset.sum_congr rfl fun n hn ↦ ?_
        have hnm : n ≠ m := fun h' ↦ hm (h' ▸ hn)
        simp [hp, hnm]
      _ = 0 := Finset.sum_const_zero
  exact hX ((IsZero.iff_id_eq_zero X).2 hzero)

/-- The free abelian group of rank one (`ULift ℤ`) is compact for coproducts in
`AddCommGrpCat`. -/
theorem isCompactForCoproducts_uliftInt :
    IsCompactForCoproducts (AddCommGrpCat.of (ULift.{v} ℤ)) := by
  let α : 𝟭 AddCommGrpCat.{v} ≅
      preadditiveCoyoneda.obj (op (AddCommGrpCat.of (ULift.{v} ℤ))) :=
    NatIso.ofComponents (fun A ↦ (AddCommGrpCat.uliftZMultiplesAddEquiv A).symm.toAddCommGrpIso)
      fun {A B} φ ↦ by
        ext x
        apply (AddCommGrpCat.uliftZMultiplesAddEquiv B).injective
        have hL : B.uliftZMultiplesAddEquiv (B.uliftZMultiplesAddEquiv.symm (φ x)) = φ x :=
          B.uliftZMultiplesAddEquiv.apply_symm_apply (φ x)
        have hR : B.uliftZMultiplesAddEquiv (A.uliftZMultiplesAddEquiv.symm x ≫ φ) = φ x :=
          congrArg φ (A.uliftZMultiplesAddEquiv.apply_symm_apply x)
        exact hL.trans hR.symm
  exact fun J ↦ preservesColimitsOfShape_of_natIso α

end Examples

end TauCeti
