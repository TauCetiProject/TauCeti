/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Topology.Category.TopCat.Basic
public import TauCeti.Topology.Grassmannian.Infinite.Classification
import TauCeti.Topology.VectorBundle.FiniteRank.HomotopyInvariance

/-!
# The infinite Grassmannian represents rank-`k` bundles

Let `HoPara` be the homotopy category of paracompact Hausdorff spaces
(`TauCeti.ParacompactHomotopyCat`): the `CategoryTheory.Quotient` of the full subcategory of
`TopCat` on these spaces (`TauCeti.isParacompactT2`) by homotopy of continuous maps. For
`RCLike 𝕜`, sending `X` to the set of isomorphism classes of rank-`k` vector-bundle cores over `X`,
with pullback of classes, is a functor `TauCeti.rankClassFunctor 𝕜 k : HoParaᵒᵖ ⥤ Type u`:
homotopic maps pull back isomorphic cores over a paracompact base.

The infinite Grassmannian `Gr_k(𝕜^∞)`, lifted to the universe of the bases, is paracompact and
Hausdorff, hence an object of `HoPara` (`TauCeti.infiniteGrassmannianObj`), and it represents
this functor (`TauCeti.rankClassFunctorRepresentableBy`): the homotopy class of a map
`f : X → Gr_k(𝕜^∞)` corresponds to the class of `f*γ_k`, the pullback of the universal
tautological bundle (`TauCeti.universalRankClass`), which is the fixed-rank classification
`TauCeti.infiniteGrassmannian.classificationEquiv`. The naturality of the bijection is the
composite-pullback identity `(f ∘ g)*γ_k = g*(f*γ_k)`.

The homotopy category is needed: over `[0, 1]` every rank-`k` bundle is trivial, while
`C([0, 1], Gr_k(𝕜^∞))` has more than one element for `k ≥ 1`.

## Main definitions

* `TauCeti.isParacompactT2`, `TauCeti.ParacompactHomotopyCat`: paracompact Hausdorff spaces and
  their homotopy category.
* `TauCeti.ParacompactHomotopyCat.homMk`: the homotopy class of a continuous map.
* `TauCeti.FiniteRankBundleCore.RankClass`: isomorphism classes of rank-`k` cores.
* `TauCeti.rankClassFunctor`: rank-`k` bundles as a functor on `HoParaᵒᵖ`.
* `TauCeti.infiniteGrassmannianObj`, `TauCeti.universalRankClass`: the Grassmannian and the class
  of its universal bundle.
* `TauCeti.rankClassFunctorRepresentableBy`: the Grassmannian represents rank-`k` bundles.

## Main results

* `TauCeti.ParacompactHomotopyCat.homMk_surjective`,
  `TauCeti.ParacompactHomotopyCat.homMk_eq_homMk_iff`: morphisms are homotopy classes.
* `TauCeti.rankClassFunctor_map_homMk`: the functor acts by pullback of classes.

## References

* J. Milnor and J. Stasheff, *Characteristic Classes*, §5; A. Hatcher, *Vector Bundles and
  K-Theory*, Theorem 1.16.
-/

public section

noncomputable section

open CategoryTheory Opposite

universe u

namespace TauCeti

/-- The paracompact Hausdorff spaces. -/
@[expose] def isParacompactT2 : ObjectProperty TopCat.{u} :=
  fun X ↦ ParacompactSpace X ∧ T2Space X

instance (X : isParacompactT2.{u}.FullSubcategory) : ParacompactSpace X.obj := X.property.1
instance (X : isParacompactT2.{u}.FullSubcategory) : T2Space X.obj := X.property.2

/-- Homotopy of continuous maps between paracompact Hausdorff spaces. -/
@[expose] def paracompactHomotopicRel : HomRel isParacompactT2.{u}.FullSubcategory :=
  fun _ _ f g ↦ ContinuousMap.Homotopic f.hom.hom g.hom.hom

instance : Congruence paracompactHomotopicRel.{u} where
  equivalence := ⟨fun f ↦ .refl f.hom.hom, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩
  comp_left f _ _ h := h.comp (.refl f.hom.hom)
  comp_right g h := (ContinuousMap.Homotopic.refl g.hom.hom).comp h

/-- **The homotopy category of paracompact Hausdorff spaces**, `HoPara`: paracompact Hausdorff
spaces and homotopy classes of continuous maps. -/
abbrev ParacompactHomotopyCat : Type (u + 1) :=
  CategoryTheory.Quotient paracompactHomotopicRel.{u}

namespace ParacompactHomotopyCat

/-- A paracompact Hausdorff space as an object of the homotopy category. -/
abbrev of (X : TopCat.{u}) [ParacompactSpace X] [T2Space X] : ParacompactHomotopyCat.{u} :=
  ⟨⟨X, ‹_›, ‹_›⟩⟩

/-- The homotopy class of a continuous map. -/
abbrev homMk {X Y : ParacompactHomotopyCat.{u}} (f : C(X.as.obj, Y.as.obj)) : X ⟶ Y :=
  (CategoryTheory.Quotient.functor _).map (ObjectProperty.homMk (TopCat.ofHom f))

theorem homMk_surjective {X Y : ParacompactHomotopyCat.{u}} :
    Function.Surjective (homMk : C(X.as.obj, Y.as.obj) → (X ⟶ Y)) := fun g ↦ by
  obtain ⟨f, rfl⟩ := (CategoryTheory.Quotient.functor paracompactHomotopicRel).map_surjective g
  exact ⟨f.hom.hom, rfl⟩

theorem homMk_eq_homMk_iff {X Y : ParacompactHomotopyCat.{u}} {f g : C(X.as.obj, Y.as.obj)} :
    homMk f = homMk g ↔ f.Homotopic g :=
  CategoryTheory.Quotient.functor_map_eq_iff _ _ _

end ParacompactHomotopyCat

variable (𝕜 : Type) [RCLike 𝕜] (k : ℕ)

/-- Isomorphism classes of rank-`k` vector-bundle cores over `X`. -/
abbrev FiniteRankBundleCore.RankClass (X : Type u) [TopologicalSpace X] : Type u :=
  Quotient ((isIsomorphicSetoid (FiniteRankBundleCore 𝕜 X)).comap
    (Subtype.val : {A : FiniteRankBundleCore 𝕜 X // A.rank = k} → _))

open FiniteRankBundleCore

/-- Pullback of isomorphism classes of rank-`k` cores, as a contravariant functor on paracompact
Hausdorff spaces into types, before passing to homotopy classes (`rankClassFunctor`). -/
@[expose] def rankClassFunctorAux : isParacompactT2.{u}.FullSubcategory ⥤ (Type u)ᵒᵖ where
  obj X := op (RankClass 𝕜 k X.obj)
  map f := (TypeCat.ofHom (pullbackRankClass f.hom.hom k)).op
  map_id X := by
    apply Quiver.Hom.unop_inj
    ext c
    exact pullbackRankClass_id k c
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    ext c
    exact (pullbackRankClass_comp f.hom.hom g.hom.hom k c).symm

/-- **Rank-`k` vector bundles on the homotopy category.** `X ↦ Vect_k(X)`, the isomorphism
classes of rank-`k` vector-bundle cores over `X`, with pullback of classes; homotopic maps pull
back isomorphic cores (`FiniteRankBundleCore.nonempty_pullback_iso_pullback_of_homotopic`). -/
@[expose] def rankClassFunctor : ParacompactHomotopyCat.{u}ᵒᵖ ⥤ Type u :=
  (CategoryTheory.Quotient.lift _ (rankClassFunctorAux 𝕜 k) fun _ _ f g h ↦ by
    apply Quiver.Hom.unop_inj
    ext c
    induction c using Quotient.inductionOn with
    | h A =>
      change pullbackRankClass f.hom.hom k ⟦A⟧ = pullbackRankClass g.hom.hom k ⟦A⟧
      rw [pullbackRankClass_mk, pullbackRankClass_mk]
      exact Quotient.sound (A.val.nonempty_pullback_iso_pullback_of_homotopic (𝕜 := 𝕜) h)).leftOp

theorem rankClassFunctor_map_homMk {X Y : ParacompactHomotopyCat.{u}} (f : C(X.as.obj, Y.as.obj))
    (c : RankClass 𝕜 k Y.as.obj) :
    (rankClassFunctor 𝕜 k).map (ParacompactHomotopyCat.homMk f).op c = pullbackRankClass f k c :=
  rfl

instance : ParacompactSpace (ULift.{u} (infiniteGrassmannian 𝕜 k)) :=
  Homeomorph.ulift.isClosedEmbedding.paracompactSpace

/-- The infinite Grassmannian `Gr_k(𝕜^∞)`, lifted to the universe `u`, as an object of the
homotopy category of paracompact Hausdorff spaces. -/
abbrev infiniteGrassmannianObj : ParacompactHomotopyCat.{u} :=
  ParacompactHomotopyCat.of (TopCat.of (ULift.{u} (infiniteGrassmannian 𝕜 k)))

/-- The projection `ULift Gr_k(𝕜^∞) → Gr_k(𝕜^∞)`. -/
@[expose] def ulowerGrassmannian :
    C(ULift.{u} (infiniteGrassmannian 𝕜 k), infiniteGrassmannian 𝕜 k) :=
  ⟨ULift.down, continuous_uliftDown⟩

/-- The class of the universal tautological bundle `γ_k` on the lifted Grassmannian. -/
abbrev universalRankClass : (rankClassFunctor 𝕜 k).obj (op (infiniteGrassmannianObj.{u} 𝕜 k)) :=
  Quotient.mk _ ⟨(infiniteGrassmannian.tautologicalCore 𝕜 k).pullback (ulowerGrassmannian 𝕜 k),
    rfl⟩

private theorem rankClassFunctor_map_homMk_universalRankClass {X : ParacompactHomotopyCat.{u}}
    (f : C(X.as.obj, ULift.{u} (infiniteGrassmannian 𝕜 k))) :
    (rankClassFunctor 𝕜 k).map (ParacompactHomotopyCat.homMk
        (Y := infiniteGrassmannianObj.{u} 𝕜 k) f).op (universalRankClass 𝕜 k) =
      infiniteGrassmannian.classificationEquiv 𝕜 X.as.obj k
        (Quotient.mk _ ((ulowerGrassmannian 𝕜 k).comp f)) :=
  (rankClassFunctor_map_homMk 𝕜 k f (universalRankClass 𝕜 k)).trans <|
    (pullbackRankClass_mk f k _).trans <|
      (congrArg (Quotient.mk _) (Subtype.ext (pullback_comp _ f (ulowerGrassmannian 𝕜 k)))).trans
        (infiniteGrassmannian.classificationEquiv_mk (𝕜 := 𝕜) (X := X.as.obj) k _).symm

/-- **The infinite Grassmannian represents rank-`k` vector bundles** on the homotopy category of
paracompact Hausdorff spaces: the homotopy class of `f : X → Gr_k(𝕜^∞)` corresponds to the class
of the pullback `f*γ_k` of the universal bundle, and the naturality is the composite-pullback
identity `(f ∘ g)*γ_k = g*(f*γ_k)`. The bijection is
`TauCeti.infiniteGrassmannian.classificationEquiv`. -/
def rankClassFunctorRepresentableBy :
    (rankClassFunctor 𝕜 k).RepresentableBy (infiniteGrassmannianObj.{u} 𝕜 k) where
  homEquiv {X} := Equiv.ofBijective
    (fun g ↦ (rankClassFunctor 𝕜 k).map g.op (universalRankClass 𝕜 k)) <| by
    refine ⟨fun g₁ g₂ h ↦ ?_, fun c ↦ ?_⟩
    · obtain ⟨f₁, rfl⟩ := ParacompactHomotopyCat.homMk_surjective g₁
      obtain ⟨f₂, rfl⟩ := ParacompactHomotopyCat.homMk_surjective g₂
      have h₁ := (rankClassFunctor_map_homMk_universalRankClass 𝕜 k f₁).symm.trans
        (h.trans (rankClassFunctor_map_homMk_universalRankClass 𝕜 k f₂))
      have h' := Quotient.exact
        ((infiniteGrassmannian.classificationEquiv 𝕜 X.as.obj k).injective h₁)
      exact ParacompactHomotopyCat.homMk_eq_homMk_iff.2
        ((ContinuousMap.Homotopic.refl ⟨ULift.up, continuous_uliftUp⟩).comp h')
    · obtain ⟨q, rfl⟩ := (infiniteGrassmannian.classificationEquiv 𝕜 X.as.obj k).surjective c
      induction q using Quotient.inductionOn with
      | h f =>
        exact ⟨ParacompactHomotopyCat.homMk ((⟨ULift.up, continuous_uliftUp⟩ :
          C(infiniteGrassmannian 𝕜 k, ULift.{u} (infiniteGrassmannian 𝕜 k))).comp f),
          rankClassFunctor_map_homMk_universalRankClass 𝕜 k _⟩
  homEquiv_comp f g := by
    change (rankClassFunctor 𝕜 k).map (f ≫ g).op (universalRankClass 𝕜 k) =
      (rankClassFunctor 𝕜 k).map f.op ((rankClassFunctor 𝕜 k).map g.op (universalRankClass 𝕜 k))
    rw [op_comp, Functor.map_comp]
    rfl

end TauCeti
