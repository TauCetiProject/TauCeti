/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Topology.ContinuousMap.Basic
public import TauCeti.Topology.Compactness.Paracompact
public import TauCeti.Topology.Grassmannian.Infinite.Classification
public import TauCeti.Topology.Homotopy.Homotopic.Rel
public import TauCeti.Topology.VectorBundle.FiniteRank.RankClassFunctor

/-!
# The infinite Grassmannian represents rank-`k` bundles

Let `HoPara` be the homotopy category of paracompact Hausdorff spaces
(`TauCeti.ParacompactHomotopyCat`), and for `RCLike 𝕜` let
`TauCeti.rankClassFunctor 𝕜 k : HoParaᵒᵖ ⥤ Type u` send `X` to the isomorphism classes of rank-`k`
vector-bundle cores over `X`. The infinite Grassmannian `Gr_k(𝕜^∞)`, lifted to the universe of the
bases, is paracompact and Hausdorff, hence an object of `HoPara`
(`TauCeti.infiniteGrassmannianObj`), and it represents this functor
(`TauCeti.rankClassFunctorRepresentableBy`): the homotopy class of a map `f : X → Gr_k(𝕜^∞)`
corresponds to the class of `f*γ_k`, the pullback of the universal tautological bundle
(`TauCeti.universalRankClass`). The bijection is the fixed-rank classification
`TauCeti.infiniteGrassmannian.classificationEquiv`
(`TauCeti.rankClassFunctorRepresentableBy_homEquiv_homMk`), and its naturality is the
composite-pullback identity `(f ∘ g)*γ_k = g*(f*γ_k)`.

The homotopy category is needed: over `[0, 1]` every rank-`k` bundle is trivial, while
`C([0, 1], Gr_k(𝕜^∞))` has more than one element for `k ≥ 1`.

## Main definitions

* `TauCeti.infiniteGrassmannianObj`: the Grassmannian as an object of `HoPara`.
* `TauCeti.infiniteGrassmannianULiftProj`: the projection from the lifted Grassmannian.
* `TauCeti.universalRankClass`: the class of its universal bundle.
* `TauCeti.rankClassFunctorRepresentableBy`: the Grassmannian represents rank-`k` bundles.

## Main results

* `TauCeti.rankClassFunctorRepresentableBy_homEquiv_homMk`: the bijection sends the class of `f`
  to `classificationEquiv` of the class of `f` followed by the projection from the lift.

## References

* J. Milnor and J. Stasheff, *Characteristic Classes*, §5; A. Hatcher, *Vector Bundles and
  K-Theory*, Theorem 1.16.
-/

public section

noncomputable section

open CategoryTheory Opposite

universe u

namespace TauCeti

open FiniteRankBundleCore

variable (𝕜 : Type) [RCLike 𝕜] (k : ℕ)

/-- The infinite Grassmannian `Gr_k(𝕜^∞)`, lifted to the universe `u`, as an object of the
homotopy category of paracompact Hausdorff spaces. -/
abbrev infiniteGrassmannianObj : ParacompactHomotopyCat.{u} :=
  ParacompactHomotopyCat.of (TopCat.of (ULift.{u} (infiniteGrassmannian 𝕜 k)))

/-- The projection `ULift Gr_k(𝕜^∞) → Gr_k(𝕜^∞)`, the homeomorphism `Homeomorph.ulift`. -/
abbrev infiniteGrassmannianULiftProj :
    C(ULift.{u} (infiniteGrassmannian 𝕜 k), infiniteGrassmannian 𝕜 k) :=
  Homeomorph.ulift.{u} (X := infiniteGrassmannian 𝕜 k)

/-- The class of the universal tautological bundle `γ_k`, pulled back to the lifted Grassmannian
along the projection `ULift.down`. -/
abbrev universalRankClass : (rankClassFunctor 𝕜 k).obj (op (infiniteGrassmannianObj.{u} 𝕜 k)) :=
  infiniteGrassmannian.classificationEquiv 𝕜 (ULift.{u} (infiniteGrassmannian 𝕜 k)) k
    (Quotient.mk _ (infiniteGrassmannianULiftProj.{u} 𝕜 k))

/-- Pulling the universal class back along `f` gives the class classified by `f` followed by the
projection from the lift. -/
theorem rankClassFunctor_map_homMk_universalRankClass {X : ParacompactHomotopyCat.{u}}
    (f : C(X.as.obj, ULift.{u} (infiniteGrassmannian 𝕜 k))) :
    (rankClassFunctor 𝕜 k).map (ParacompactHomotopyCat.homMk
        (Y := infiniteGrassmannianObj.{u} 𝕜 k) f).op (universalRankClass 𝕜 k) =
      infiniteGrassmannian.classificationEquiv 𝕜 X.as.obj k
        (Quotient.mk _ ((infiniteGrassmannianULiftProj.{u} 𝕜 k).comp f)) := by
  rw [rankClassFunctor_map_homMk]
  exact (infiniteGrassmannian.classificationEquiv_comp f k _).symm

/-- Homotopy classes `X ⟶ Gr_k(𝕜^∞)` in `HoPara` are rank-`k` classes over `X`: the composite of
`ParacompactHomotopyCat.homEquivQuotient`, post-composition with the projection from the lift
(`Homeomorph.homotopicQuotientCongr`) and `TauCeti.infiniteGrassmannian.classificationEquiv`. -/
private def rankClassHomEquiv (X : ParacompactHomotopyCat.{u}) :
    (X ⟶ infiniteGrassmannianObj.{u} 𝕜 k) ≃ RankClass 𝕜 X.as.obj k :=
  (ParacompactHomotopyCat.homEquivQuotient _ _).symm.trans <|
    (Homeomorph.ulift.homotopicQuotientCongr X.as.obj).trans
      (infiniteGrassmannian.classificationEquiv 𝕜 X.as.obj k)

private theorem rankClassHomEquiv_homMk {X : ParacompactHomotopyCat.{u}}
    (f : C(X.as.obj, ULift.{u} (infiniteGrassmannian 𝕜 k))) :
    rankClassHomEquiv 𝕜 k X
        (ParacompactHomotopyCat.homMk (Y := infiniteGrassmannianObj.{u} 𝕜 k) f) =
      infiniteGrassmannian.classificationEquiv 𝕜 X.as.obj k
        (Quotient.mk _ ((infiniteGrassmannianULiftProj.{u} 𝕜 k).comp f)) := by
  rw [rankClassHomEquiv, Equiv.trans_apply, Equiv.trans_apply,
    ParacompactHomotopyCat.homEquivQuotient_symm_homMk (Y := infiniteGrassmannianObj.{u} 𝕜 k) f,
    Homeomorph.homotopicQuotientCongr_mk]

/-- **The infinite Grassmannian represents rank-`k` vector bundles** on the homotopy category of
paracompact Hausdorff spaces: the homotopy class of `f : X → Gr_k(𝕜^∞)` corresponds to the class
of the pullback `f*γ_k` of the universal bundle. The bijection is
`TauCeti.infiniteGrassmannian.classificationEquiv`, read through the projection from the lift. -/
def rankClassFunctorRepresentableBy :
    (rankClassFunctor 𝕜 k).RepresentableBy (infiniteGrassmannianObj.{u} 𝕜 k) where
  homEquiv {X} := rankClassHomEquiv 𝕜 k X
  homEquiv_comp {X X'} f g := by
    obtain ⟨a, rfl⟩ := ParacompactHomotopyCat.homMk_surjective f
    obtain ⟨b, rfl⟩ := ParacompactHomotopyCat.homMk_surjective g
    -- `(rankClassFunctor 𝕜 k).map (homMk a).op` is `pullbackRankClass a k`
    -- (`rankClassFunctor_map_homMk`), stated here on `RankClass` rather than on the functor's
    -- objects so that the rewrites below see well-typed terms.
    change rankClassHomEquiv 𝕜 k X
        (ParacompactHomotopyCat.homMk a ≫ ParacompactHomotopyCat.homMk b) =
      pullbackRankClass a k (rankClassHomEquiv 𝕜 k X' (ParacompactHomotopyCat.homMk b))
    rw [← ParacompactHomotopyCat.homMk_comp, rankClassHomEquiv_homMk, rankClassHomEquiv_homMk,
      ← ContinuousMap.comp_assoc, infiniteGrassmannian.classificationEquiv_comp]

/-- The bijection of `rankClassFunctorRepresentableBy` sends the class of `f` to the class that
`classificationEquiv` assigns to `f` followed by the projection from the lift. -/
@[simp]
theorem rankClassFunctorRepresentableBy_homEquiv_homMk {X : ParacompactHomotopyCat.{u}}
    (f : C(X.as.obj, ULift.{u} (infiniteGrassmannian 𝕜 k))) :
    (rankClassFunctorRepresentableBy 𝕜 k).homEquiv
        (ParacompactHomotopyCat.homMk (Y := infiniteGrassmannianObj.{u} 𝕜 k) f) =
      infiniteGrassmannian.classificationEquiv 𝕜 X.as.obj k
        (Quotient.mk _ ((infiniteGrassmannianULiftProj.{u} 𝕜 k).comp f)) :=
  rankClassHomEquiv_homMk 𝕜 k f

end TauCeti
