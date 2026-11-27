/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Yoneda
public import TauCeti.Topology.Compactness.Paracompact
public import TauCeti.Topology.Grassmannian.Infinite.Classification
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

/-- The class of the universal tautological bundle `γ_k`, pulled back to the lifted Grassmannian
along the projection `ULift.down`. -/
abbrev universalRankClass : (rankClassFunctor 𝕜 k).obj (op (infiniteGrassmannianObj.{u} 𝕜 k)) :=
  infiniteGrassmannian.classificationEquiv 𝕜 (ULift.{u} (infiniteGrassmannian 𝕜 k)) k
    (Quotient.mk _ (ContinuousMap.mk ULift.down continuous_uliftDown))

/-- Pulling the universal class back along `f` gives the class classified by `f` followed by the
projection from the lift. -/
theorem rankClassFunctor_map_homMk_universalRankClass {X : ParacompactHomotopyCat.{u}}
    (f : C(X.as.obj, ULift.{u} (infiniteGrassmannian 𝕜 k))) :
    (rankClassFunctor 𝕜 k).map (ParacompactHomotopyCat.homMk
        (Y := infiniteGrassmannianObj.{u} 𝕜 k) f).op (universalRankClass 𝕜 k) =
      infiniteGrassmannian.classificationEquiv 𝕜 X.as.obj k
        (Quotient.mk _ ((ContinuousMap.mk ULift.down continuous_uliftDown).comp f)) :=
  (infiniteGrassmannian.classificationEquiv_comp f k _).symm

/-- Lifting after projecting from the lift is the identity. -/
private theorem uliftUp_comp_uliftDown_comp {X : Type*} [TopologicalSpace X]
    (f : C(X, ULift.{u} (infiniteGrassmannian 𝕜 k))) :
    (ContinuousMap.mk ULift.up continuous_uliftUp).comp
      ((ContinuousMap.mk ULift.down continuous_uliftDown).comp f) = f :=
  ContinuousMap.ext fun _ ↦ rfl

/-- **The infinite Grassmannian represents rank-`k` vector bundles** on the homotopy category of
paracompact Hausdorff spaces: the homotopy class of `f : X → Gr_k(𝕜^∞)` corresponds to the class
of the pullback `f*γ_k` of the universal bundle. The bijection is
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
      have h' := (ContinuousMap.Homotopic.refl (ContinuousMap.mk ULift.up continuous_uliftUp)).comp
        (Quotient.exact ((infiniteGrassmannian.classificationEquiv 𝕜 X.as.obj k).injective h₁))
      rw [uliftUp_comp_uliftDown_comp, uliftUp_comp_uliftDown_comp] at h'
      exact ParacompactHomotopyCat.homMk_eq_homMk_iff.2 h'
    · obtain ⟨q, rfl⟩ := (infiniteGrassmannian.classificationEquiv 𝕜 X.as.obj k).surjective c
      induction q using Quotient.inductionOn with
      | h f =>
        exact ⟨ParacompactHomotopyCat.homMk ((ContinuousMap.mk ULift.up continuous_uliftUp).comp f),
          rankClassFunctor_map_homMk_universalRankClass 𝕜 k _⟩
  homEquiv_comp f g := by
    simp only [Equiv.ofBijective, Equiv.coe_fn_mk, op_comp, Functor.map_comp,
      ConcreteCategory.comp_apply]

/-- The bijection of `rankClassFunctorRepresentableBy` sends the class of `f` to the class that
`classificationEquiv` assigns to `f` followed by the projection from the lift. -/
@[simp]
theorem rankClassFunctorRepresentableBy_homEquiv_homMk {X : ParacompactHomotopyCat.{u}}
    (f : C(X.as.obj, ULift.{u} (infiniteGrassmannian 𝕜 k))) :
    (rankClassFunctorRepresentableBy 𝕜 k).homEquiv
        (ParacompactHomotopyCat.homMk (Y := infiniteGrassmannianObj.{u} 𝕜 k) f) =
      infiniteGrassmannian.classificationEquiv 𝕜 X.as.obj k
        (Quotient.mk _ ((ContinuousMap.mk ULift.down continuous_uliftDown).comp f)) := by
  simp only [rankClassFunctorRepresentableBy, Equiv.ofBijective, Equiv.coe_fn_mk]
  exact rankClassFunctor_map_homMk_universalRankClass 𝕜 k f

end TauCeti
