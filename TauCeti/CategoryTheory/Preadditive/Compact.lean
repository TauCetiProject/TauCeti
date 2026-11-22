/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Shift.Basic
public import TauCeti.Algebra.Category.Grp.Coproducts

import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits

/-!
# Objects compact for coproducts in a preadditive category

An object `G` of a preadditive category `T` (with morphisms in `Type v`) is *compact for
coproducts* (`TauCeti.IsCompactForCoproducts G`) if `preadditiveCoyoneda.obj (op G)` preserves
`Type v`-indexed coproducts, equivalently (`TauCeti.isCompactForCoproducts_iff`) if
`TauCeti.coprodComparisonAddHom G f : (⨁ j, (G ⟶ f j)) →+ (G ⟶ ∐ f)` is bijective, yielding
`TauCeti.IsCompactForCoproducts.homCoprodEquiv`. The `ObjectProperty` of compact objects is
`TauCeti.compactForCoproducts T`.

## Main definitions

* `TauCeti.IsCompactForCoproducts`, `TauCeti.compactForCoproducts`,
  `TauCeti.coprodComparisonAddHom`, `TauCeti.IsCompactForCoproducts.homCoprodEquiv`

## Main results

* `TauCeti.isCompactForCoproducts_iff`: characterization via `coprodComparisonAddHom`.
* `TauCeti.IsCompactForCoproducts.of_iso`, `TauCeti.isCompactForCoproducts_of_isZero`,
  `TauCeti.IsCompactForCoproducts.of_retract`,
  `TauCeti.IsCompactForCoproducts.coproduct_of_finite`,
  `TauCeti.IsCompactForCoproducts.biprod`, `TauCeti.IsCompactForCoproducts.shift`.
* `TauCeti.not_isCompactForCoproducts_sigma`, `TauCeti.isCompactForCoproducts_uliftInt`.

## References

* A. Neeman, *Triangulated categories*, Princeton Univ. Press (2001), Def. 4.2.7.
* S. Schwede, *Symmetric spectra*, Chapter II, Def. 5.4.
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
      ∀ J : Type v,
        PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (op G)) := Iff.rfl

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
    coprodComparisonAddHom G' f (DirectSum.map (fun j ↦ Preadditive.leftComp (f j) α) a) =
      α ≫ coprodComparisonAddHom G f a := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of j g => simp [Preadditive.leftComp]
  | add a b ha hb => simp [map_add, ha, hb, Preadditive.comp_add]

/-- Naturality of `coprodComparisonAddHom` in the coproduct family `f`. -/
theorem coprodComparisonAddHom_naturality_right (G : T) {J : Type w} [DecidableEq J]
    {f f' : J → T} [HasCoproduct f] [HasCoproduct f'] (φ : ∀ j, f j ⟶ f' j)
    (a : ⨁ j, (G ⟶ f j)) :
    coprodComparisonAddHom G f' (DirectSum.map (fun j ↦ Preadditive.rightComp G (φ j)) a) =
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
    exact (coprodComparisonAddHom_of G (f ∘ e.symm) k g).trans (by simp)
  | add a b ha hb => simp [map_add, ha, hb, Preadditive.add_comp]

/-- The corepresented functor `Hom(G, -)` preserves a `Type v`-indexed coproduct `∐ f` if and only
if the direct-sum comparison homomorphism `coprodComparisonAddHom G f` is bijective. -/
private theorem preservesColimit_discrete_preadditiveCoyoneda_iff_sameUniv (G : T) {J : Type v}
    [DecidableEq J] (f : J → T) [HasCoproduct f] :
    PreservesColimit (Discrete.functor f) (preadditiveCoyoneda.obj (op G)) ↔
      Function.Bijective (coprodComparisonAddHom G f) := by
  let F := preadditiveCoyoneda.obj (op G)
  have : HasCoproduct (fun j ↦ F.obj (f j)) :=
    ⟨⟨⟨_, AddCommGrpCat.coproductCoconeIsColimit _⟩⟩⟩
  let φ : AddCommGrpCat.of (⨁ j, ↑(F.obj (f j))) ⟶ F.obj (∐ f) :=
    (AddCommGrpCat.coprodIsoDirectSum (fun j ↦ F.obj (f j))).inv ≫ sigmaComparison F f
  let eDS : (⨁ j, ↑(F.obj (f j))) ≃+ (⨁ j, (G ⟶ f j)) :=
    DFinsupp.mapRange.addEquiv fun _ ↦ AddEquiv.refl _
  have hφ : φ.hom = (coprodComparisonAddHom G f).comp eDS.toAddMonoidHom := by
    refine DirectSum.addHom_ext fun j g ↦ ?_
    have hcomp := congrArg (fun ψ : F.obj (f j) ⟶ F.obj (∐ f) ↦ ψ g)
      (AddCommGrpCat.of_coprodIsoDirectSum_inv_assoc (fun i ↦ F.obj (f i)) j
        (sigmaComparison F f))
    rw [ι_comp_sigmaComparison] at hcomp
    refine hcomp.trans ?_
    exact (coprodComparisonAddHom_of G f j g).symm.trans <| congrArg (coprodComparisonAddHom G f)
      (DFinsupp.mapRange_single (f := fun _ ↦ id) (hf := fun _ ↦ rfl) (i := j)).symm
  have hbij : Function.Bijective φ ↔ Function.Bijective (coprodComparisonAddHom G f) := by
    have hfun : ⇑φ = ⇑(coprodComparisonAddHom G f) ∘ ⇑eDS :=
      funext (DFunLike.congr_fun hφ)
    rw [hfun]
    exact Function.Bijective.of_comp_iff _ eDS.bijective
  have hiso : IsIso φ ↔ IsIso (sigmaComparison F f) :=
    ⟨fun _ ↦ by
      rw [← Iso.hom_inv_id_assoc (AddCommGrpCat.coprodIsoDirectSum (fun j ↦ F.obj (f j)))
        (sigmaComparison F f)]
      infer_instance,
     fun _ ↦ inferInstance⟩
  rw [← hbij, ← ConcreteCategory.isIso_iff_bijective, hiso]
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ PreservesCoproduct.of_iso_comparison F f⟩

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
  have : HasCoproduct (f ∘ e.symm) :=
    ⟨⟨⟨_, (IsColimit.precomposeInvEquiv iso _).symm
      ((colimit.isColimit (Discrete.functor f)).whiskerEquivalence eqv)⟩⟩⟩
  have hpres :
      PreservesColimit (Discrete.functor f) F ↔
        PreservesColimit (Discrete.functor (f ∘ e.symm)) F := by
    rw [← Functor.Final.preservesColimit_comp_iff (G := Discrete.functor f) eqv.functor]
    exact ⟨fun _ ↦ preservesColimit_of_iso_diagram _ iso,
      fun _ ↦ preservesColimit_of_iso_diagram _ iso.symm⟩
  rw [hpres, preservesColimit_discrete_preadditiveCoyoneda_iff_sameUniv G (f ∘ e.symm)]
  let equivDS := DirectSum.equivCongrLeft (β := fun j ↦ G ⟶ f j) e
  have hpostEq : (fun g : G ⟶ ∐ f ↦ g ≫ (Limits.Sigma.reindex e.symm f).inv) =
      ⇑((Iso.refl G).homCongr (Limits.Sigma.reindex e.symm f).symm) := funext fun _ ↦ by simp
  have hpost : Function.Bijective (fun g : G ⟶ ∐ f ↦ g ≫ (Limits.Sigma.reindex e.symm f).inv) :=
    hpostEq ▸ Equiv.bijective _
  have hcomp : ⇑(coprodComparisonAddHom G (f ∘ e.symm)) ∘ ⇑equivDS =
      (fun g : G ⟶ ∐ f ↦ g ≫ (Limits.Sigma.reindex e.symm f).inv) ∘
        ⇑(coprodComparisonAddHom G f) := funext (coprodComparisonAddHom_equivCongrLeft G e f)
  rw [← Function.Bijective.of_comp_iff _ equivDS.bijective, hcomp, hpost.of_comp_iff']

/-- An object `G` is compact for coproducts if and only if the direct-sum comparison map
`(⨁ j, (G ⟶ f j)) →+ (G ⟶ ∐ f)` is bijective for every `Type v`-indexed coproduct. -/
theorem isCompactForCoproducts_iff (G : T) :
    IsCompactForCoproducts G ↔
      ∀ (J : Type v) [DecidableEq J] (f : J → T) [HasCoproduct f],
        Function.Bijective (coprodComparisonAddHom G f) := by
  refine ⟨fun hG J _ f _ ↦ have := hG J
      (preservesColimit_discrete_preadditiveCoyoneda_iff_sameUniv G f).1 inferInstance,
    fun h J ↦ ?_⟩
  classical
  have (f : J → T) : PreservesColimit (Discrete.functor f) (preadditiveCoyoneda.obj (op G)) :=
    ⟨fun {c} hc ↦
      have : HasCoproduct f := ⟨⟨⟨c, hc⟩⟩⟩
      have := (preservesColimit_discrete_preadditiveCoyoneda_iff_sameUniv G f).2 (h J f)
      ⟨isColimitOfPreserves (preadditiveCoyoneda.obj (op G)) hc⟩⟩
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
    hG.homCoprodEquiv f a = coprodComparisonAddHom G f a := (rfl)

theorem IsCompactForCoproducts.homCoprodEquiv_of {G : T}
    (hG : IsCompactForCoproducts G) {J : Type w} [DecidableEq J] [Small.{v} J]
    (f : J → T) [HasCoproduct f] (j : J) (g : G ⟶ f j) :
    hG.homCoprodEquiv f (DirectSum.of (fun j ↦ G ⟶ f j) j g) = g ≫ Sigma.ι f j :=
  coprodComparisonAddHom_of G f j g

@[simp]
theorem IsCompactForCoproducts.homCoprodEquiv_symm_comp_ι {G : T}
    (hG : IsCompactForCoproducts G) {J : Type w} [DecidableEq J] [Small.{v} J]
    (f : J → T) [HasCoproduct f] (j : J) (g : G ⟶ f j) :
    (hG.homCoprodEquiv f).symm (g ≫ Sigma.ι f j) = DirectSum.of (fun j ↦ G ⟶ f j) j g :=
  (hG.homCoprodEquiv f).injective (by simp)

/-- Every morphism from `G` into a `v`-small coproduct `∐ f` preserved by `Hom(G, -)` is a
finite sum of morphisms factoring through the summand inclusions `Sigma.ι f j`. -/
theorem exists_finset_sum_comp_ι_of_preservesColimit {G : T} {J : Type w} [Small.{v} J]
    (f : J → T) [HasCoproduct f]
    [PreservesColimit (Discrete.functor f) (preadditiveCoyoneda.obj (op G))]
    (g : G ⟶ ∐ f) :
    ∃ (s : Finset J) (h : ∀ j, G ⟶ f j), g = ∑ j ∈ s, h j ≫ Sigma.ι f j := by
  classical
  obtain ⟨a, rfl⟩ := ((preservesColimit_discrete_preadditiveCoyoneda_iff G f).1 inferInstance).2 g
  exact ⟨a.support, fun j ↦ a j, coprodComparisonAddHom_apply G f a⟩

/-- Every morphism from a compact object `G` into a `v`-small coproduct `∐ f` is a finite sum of
morphisms factoring through the summand inclusions `Sigma.ι f j`. -/
theorem IsCompactForCoproducts.exists_finset_sum_comp_ι {G : T}
    (hG : IsCompactForCoproducts G) {J : Type w} [Small.{v} J]
    (f : J → T) [HasCoproduct f] (g : G ⟶ ∐ f) :
    ∃ (s : Finset J) (h : ∀ j, G ⟶ f j), g = ∑ j ∈ s, h j ≫ Sigma.ι f j :=
  have := hG.preservesColimitsOfShape J
  exists_finset_sum_comp_ι_of_preservesColimit f g

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
    (hH : IsCompactForCoproducts H) : IsCompactForCoproducts G := fun J ↦
  (ObjectProperty.preservesColimitsOfShape (Discrete J)).prop_of_retract
    (r.op.map preadditiveCoyoneda) (hH J)

/-- The `ObjectProperty` of objects compact for coproducts in a preadditive category. -/
def compactForCoproducts (T : Type u) [Category.{v} T] [Preadditive T] : ObjectProperty T :=
  IsCompactForCoproducts

@[simp]
theorem compactForCoproducts_iff (G : T) :
    compactForCoproducts T G ↔ IsCompactForCoproducts G :=
  Iff.rfl

instance : (compactForCoproducts T).IsClosedUnderIsomorphisms where
  of_iso e h := h.of_iso e

instance : (compactForCoproducts T).IsStableUnderRetracts where
  of_retract h hY := hY.of_retract h

/-- Finite coproducts of compact objects are compact. -/
theorem IsCompactForCoproducts.coproduct_of_finite {K : Type w} [Finite K] (X : K → T)
    [HasCoproduct X] (hX : ∀ k, IsCompactForCoproducts (X k)) :
    IsCompactForCoproducts (∐ X) := by
  rw [isCompactForCoproducts_iff]
  intro J _ f _
  classical
  have : Fintype K := Fintype.ofFinite K
  refine ⟨fun a b hab ↦ DFinsupp.ext fun j ↦ Sigma.hom_ext _ _ fun k ↦ ?_, fun g ↦ ?_⟩
  · have heq := ((hX k).bijective_coprodComparisonAddHom f).1
      (a₁ := DirectSum.map (fun j ↦ Preadditive.leftComp (f j) (Sigma.ι X k)) a)
      (a₂ := DirectSum.map (fun j ↦ Preadditive.leftComp (f j) (Sigma.ι X k)) b) <| by
        rw [coprodComparisonAddHom_naturality_left, coprodComparisonAddHom_naturality_left, hab]
    simpa [Preadditive.leftComp] using congrArg (fun z : ⨁ j, (X k ⟶ f j) ↦ z j) heq
  · choose b hb using fun k ↦ ((hX k).bijective_coprodComparisonAddHom f).2 (Sigma.ι X k ≫ g)
    let S : Finset J := Finset.univ.biUnion fun k ↦ (b k).support
    let a : ⨁ j, (∐ X ⟶ f j) :=
      ∑ j ∈ S, DirectSum.of (fun j ↦ ∐ X ⟶ f j) j (Sigma.desc fun k ↦ b k j)
    refine ⟨a, Sigma.hom_ext _ _ fun k ↦ ?_⟩
    rw [← coprodComparisonAddHom_naturality_left]
    have hmap : DirectSum.map (fun j ↦ Preadditive.leftComp (f j) (Sigma.ι X k)) a = b k := by
      simp only [a, map_sum, DirectSum.map_of, Preadditive.leftComp, AddMonoidHom.mk'_apply,
        Sigma.ι_comp_desc]
      conv_rhs => rw [← DirectSum.sum_support_of (b k)]
      exact (Finset.sum_subset (f := fun j ↦ DirectSum.of (fun j ↦ X k ⟶ f j) j (b k j))
        (Finset.subset_biUnion_of_mem (fun k ↦ (b k).support) (Finset.mem_univ k))
        fun j _ hj ↦ by rw [DFinsupp.notMem_support_iff.1 hj, map_zero]).symm
    rw [hmap, hb k]

/-- Binary biproducts of compact objects are compact. -/
theorem IsCompactForCoproducts.biprod {X Y : T} [HasBinaryBiproduct X Y]
    (hX : IsCompactForCoproducts X) (hY : IsCompactForCoproducts Y) :
    IsCompactForCoproducts (X ⊞ Y) := by
  have hc : IsColimit (BinaryBiproduct.bicone X Y).toBicone.toCocone :=
    (BinaryBiproduct.bicone X Y).toBiconeIsColimit.symm (BinaryBiproduct.isColimit X Y)
  have : HasCoproduct (pairFunction X Y) := ⟨⟨⟨_, hc⟩⟩⟩
  exact (IsCompactForCoproducts.coproduct_of_finite (pairFunction X Y) fun p ↦ by
    cases p <;> assumption).of_iso ((colimit.isColimit _).coconePointUniqueUpToIso hc)

/-- Finite biproducts of compact objects are compact. -/
theorem IsCompactForCoproducts.biproduct {K : Type w} [Finite K] (X : K → T) [HasBiproduct X]
    (hX : ∀ k, IsCompactForCoproducts (X k)) : IsCompactForCoproducts (Limits.biproduct X) :=
  have : HasCoproduct X := ⟨⟨⟨_, biproduct.isColimit X⟩⟩⟩
  (IsCompactForCoproducts.coproduct_of_finite X hX).of_iso (biproduct.isoCoproduct X).symm

/-- An additive equivalence `e : T ≌ T'` carries preservation of `I`-shaped colimits by
`Hom(G, -)` to preservation of `I`-shaped colimits by `Hom(e.functor.obj G, -)`. -/
theorem preservesColimitsOfShape_preadditiveCoyoneda_of_equivalence
    {T' : Type u'} [Category.{v} T'] [Preadditive T'] (e : T ≌ T') [e.functor.Additive]
    (I : Type*) [Category* I] (G : T)
    [PreservesColimitsOfShape I (preadditiveCoyoneda.obj (op G))] :
    PreservesColimitsOfShape I (preadditiveCoyoneda.obj (op (e.functor.obj G))) := by
  have := comp_preservesColimitsOfShape (J := I) e.inverse (preadditiveCoyoneda.obj (op G))
  let α : e.inverse ⋙ preadditiveCoyoneda.obj (op G) ≅
      preadditiveCoyoneda.obj (op (e.functor.obj G)) :=
    NatIso.ofComponents (fun X ↦ (e.toAdjunction.homAddEquiv G X).symm.toAddCommGrpIso)
      fun {X Y} φ ↦ AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun f ↦ by
        dsimp
        exact e.toAdjunction.homEquiv_naturality_right_symm f φ
  exact preservesColimitsOfShape_of_natIso α

/-- If `Hom(G, -)` preserves `I`-shaped colimits, then so does `Hom(G⟦a⟧, -)`. -/
theorem preservesColimitsOfShape_preadditiveCoyoneda_shift {A : Type*} [AddGroup A]
    [HasShift T A] (I : Type*) [Category* I] (G : T) (a : A) [(shiftFunctor T a).Additive]
    [PreservesColimitsOfShape I (preadditiveCoyoneda.obj (op G))] :
    PreservesColimitsOfShape I (preadditiveCoyoneda.obj (op (G⟦a⟧))) :=
  have : (shiftEquiv T a).functor.Additive := inferInstanceAs (shiftFunctor T a).Additive
  preservesColimitsOfShape_preadditiveCoyoneda_of_equivalence (shiftEquiv T a) I G

/-- Additive equivalences preserve compactness for coproducts. -/
theorem IsCompactForCoproducts.map_of_equivalence {T' : Type u'} [Category.{v} T']
    [Preadditive T'] (e : T ≌ T') [e.functor.Additive] {G : T} (hG : IsCompactForCoproducts G) :
    IsCompactForCoproducts (e.functor.obj G) := fun J ↦
  have := hG J
  preservesColimitsOfShape_preadditiveCoyoneda_of_equivalence e (Discrete J) G

/-- Compactness for coproducts is invariant under additive equivalences. -/
theorem isCompactForCoproducts_map_of_equivalence_iff {T' : Type u'} [Category.{v} T']
    [Preadditive T'] (e : T ≌ T') [e.functor.Additive] (G : T) :
    IsCompactForCoproducts (e.functor.obj G) ↔ IsCompactForCoproducts G :=
  ⟨fun h ↦ have : e.symm.functor.Additive := inferInstanceAs e.inverse.Additive
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

/-- In a preadditive category, a `v`-small coproduct with infinitely many nonzero summands is
never compact: its identity morphism does not factor through any finite subcoproduct. -/
theorem not_isCompactForCoproducts_sigma {T : Type u} [Category.{v} T] [Preadditive T]
    {J : Type w} [Small.{v} J] (f : J → T) [HasCoproduct f]
    (hf : Set.Infinite {j | ¬ IsZero (f j)}) :
    ¬ IsCompactForCoproducts (∐ f) := by
  classical
  intro hC
  obtain ⟨s, h, hid⟩ := hC.exists_finset_sum_comp_ι f (𝟙 (∐ f))
  obtain ⟨m, hmS, hm0⟩ : ∃ m ∈ {j | ¬ IsZero (f j)}, m ∉ s := hf.exists_notMem_finset s
  let p : (∐ f) ⟶ f m := Sigma.desc fun j ↦ if hjm : j = m then eqToHom (congrArg f hjm) else 0
  have hp (j : J) : Sigma.ι f j ≫ p = if hjm : j = m then eqToHom (congrArg f hjm) else 0 :=
    Sigma.ι_comp_desc _ j
  refine hmS ((IsZero.iff_id_eq_zero (f m)).2 ?_)
  calc
    𝟙 (f m) = Sigma.ι f m ≫ (∑ j ∈ s, h j ≫ Sigma.ι f j) ≫ p := by
      rw [← hid]; simp [hp]
    _ = ∑ j ∈ s, Sigma.ι f m ≫ h j ≫ (Sigma.ι f j ≫ p) := by
      simp [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
    _ = 0 := Finset.sum_eq_zero fun j hj ↦ by
      have hjm : j ≠ m := fun h' ↦ hm0 (h' ▸ hj); simp [hp, hjm]

/-- The free abelian group of rank one (`ULift ℤ`) is compact for coproducts in
`AddCommGrpCat`. -/
theorem isCompactForCoproducts_uliftInt :
    IsCompactForCoproducts (AddCommGrpCat.of (ULift.{v} ℤ)) := fun _ ↦
  let α : 𝟭 AddCommGrpCat.{v} ≅ preadditiveCoyoneda.obj (op (AddCommGrpCat.of (ULift.{v} ℤ))) :=
    NatIso.ofComponents (fun A ↦ (AddCommGrpCat.uliftZMultiplesAddEquiv A).symm.toAddCommGrpIso)
      fun {A B} φ ↦ AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun x ↦
        (AddCommGrpCat.uliftZMultiplesAddEquiv B).injective <|
          (B.uliftZMultiplesAddEquiv.apply_symm_apply (φ x)).trans
            (congrArg φ (A.uliftZMultiplesAddEquiv.apply_symm_apply x)).symm
  preservesColimitsOfShape_of_natIso α

end Examples

end TauCeti
