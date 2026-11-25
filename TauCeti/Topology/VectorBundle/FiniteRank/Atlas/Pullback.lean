/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Preadditive
public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Trivial
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback

/-!
# Pullback of variable-rank bundle atlases

A continuous map `f : C(X, Y)` pulls a variable-rank atlas `A : FiniteRankAtlas 𝕜 Y` back to
`A.pullback f : FiniteRankAtlas 𝕜 X`. Its rank is `A.rank.comap f`, its fibre at `x` is the fibre of
`A` at `f x`, and on each clopen rank stratum its point-indexed core is the pullback
`TauCeti.FiniteRankBundleCore.pullback` of the corresponding stratum core of `A`, so that the chart
at `x` is the inverse image of the chart at `f x` (`chartBaseSet_pullback`). As for cores, the
charts are indexed by the new base points, so the pulled-back atlas lives in the universe of `X`.
No bounded-rank, finite-cover, compactness or separation hypothesis is needed.

The total space of the pullback carries the reconstructed bundle topology of `A.pullback f`. It is
the topology of a pullback: a map into it is continuous exactly when its base projection and its
image under the canonical lift `pullbackLift` to the total space of `A` are continuous
(`continuous_totalSpace_pullback_iff`, `continuous_mk_pullback_iff`).

Bundle maps pull back fibrewise (`pullbackMap`), giving the additive functor
`pullbackFunctor f : FiniteRankAtlas 𝕜 Y ⥤ FiniteRankAtlas 𝕜 X`. Being additive it preserves the
zero atlas and Whitney sums, which are the biproducts of the atlas category. Pullback along a
composite is literally the iterated pullback (`pullback_comp`, `pullbackFunctor_comp`), pullback
along the identity is naturally isomorphic to the identity (`pullbackIdIso`,
`pullbackFunctorIdIso`), and trivial atlases pull back to trivial atlases (`pullback_trivial`).
These are the bundle-level inputs for the contravariant functoriality of the Grothendieck group of
finite-rank bundles.
-/

public section

open Bundle CategoryTheory

namespace TauCeti.FiniteRankAtlas

universe u v w z

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} {Y : Type w} {Z : Type z}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Pull back a variable-rank atlas along a continuous map. The rank is composed with the map, and
on the rank-`n` stratum the point-indexed core is the pullback of the rank-`n` stratum core of `A`
along the restriction of `f`, so that the chart at `x` is the inverse image of the chart at
`f x`. -/
-- Expose the rank so that `(A.pullback f).Fiber x` reduces to `A.Fiber (f x)`.
@[expose]
def pullback (A : FiniteRankAtlas 𝕜 Y) (f : C(X, Y)) : FiniteRankAtlas 𝕜 X where
  rank := A.rank.comap f
  charts n := ((A.stratumCore n).pullback (f.restrictPreimage {y | A.rank y = n})).core
  indexAt_eq _ _ := rfl

variable (A : FiniteRankAtlas 𝕜 Y) (f : C(X, Y))

/-- The rank of a pulled-back atlas is the composite of the rank with the map. -/
@[simp] theorem rank_pullback : (A.pullback f).rank = A.rank.comap f := (rfl)

/-- The rank-`n` stratum core of a pulled-back atlas is the pullback of the rank-`n` stratum core
along the restriction of the map to the rank-`n` strata. -/
theorem stratumCore_pullback (n : ℕ) :
    (A.pullback f).stratumCore n =
      (A.stratumCore n).pullback (f.restrictPreimage {y | A.rank y = n}) := (rfl)

/-- The preferred chart of a pulled-back atlas at `x` is the inverse image of the preferred chart of
the original atlas at `f x`. -/
@[simp] theorem chartBaseSet_pullback (x : X) :
    (A.pullback f).chartBaseSet x = f ⁻¹' A.chartBaseSet (f x) := by
  ext z
  simp only [Set.mem_preimage, mem_chartBaseSet_iff]
  -- The rank-stratum chart of the pulled-back core at `x` is by definition the preimage of the
  -- rank-stratum chart at `f x`.
  rfl

/-- The canonical map from the total space of the pullback to the total space of `A`. It covers `f`
on the base and is the identity on fibres. -/
def pullbackLift (p : TotalSpace Unit (A.pullback f).Fiber) : TotalSpace Unit A.Fiber :=
  ⟨f p.proj, p.snd⟩

@[simp] theorem pullbackLift_mk (x : X) (v : (A.pullback f).Fiber x) :
    A.pullbackLift f ⟨x, v⟩ = ⟨f x, v⟩ := (rfl)

@[simp] theorem proj_pullbackLift (p : TotalSpace Unit (A.pullback f).Fiber) :
    (A.pullbackLift f p).proj = f p.proj := (rfl)

section Continuity

variable {W : Type*} [TopologicalSpace W]

/-- A map `w ↦ ⟨b w, s w⟩` into the total space of a pulled-back atlas over a continuous base map
`b` is continuous exactly when the corresponding map `w ↦ ⟨f (b w), s w⟩` into the total space of
the original atlas is continuous. -/
theorem continuous_mk_pullback_iff {b : W → X} (hb : Continuous b)
    (s : ∀ w, (A.pullback f).Fiber (b w)) :
    Continuous (fun w => (⟨b w, s w⟩ : TotalSpace Unit (A.pullback f).Fiber)) ↔
      Continuous (fun w => (⟨f (b w), s w⟩ : TotalSpace Unit A.Fiber)) := by
  refine ((A.pullback f).continuous_mk_iff_rankStrata hb s).trans
    (Iff.trans (forall_congr' fun n => ?_)
      (A.continuous_mk_iff_rankStrata (b := fun w => f (b w)) (f.continuous.comp hb) s).symm)
  -- On each stratum this is the pullback criterion for the stratum core, whose base projection is
  -- continuous because `b` is.
  refine ((A.stratumCore n).continuous_core_pullback_iff _).trans
    ((and_iff_right ((hb.comp continuous_subtypeVal).subtype_mk _)).trans ?_)
  exact Iff.of_eq <| congrArg Continuous <|
    funext fun _ => FiniteRankBundleCore.pullbackLift_mk _ _ _ _

/-- The canonical lift from the total space of the pullback to the total space of `A` is
continuous. -/
@[fun_prop] theorem continuous_pullbackLift : Continuous (A.pullbackLift f) :=
  (A.continuous_mk_pullback_iff f (A.pullback f).continuous_proj
    (fun p : TotalSpace Unit (A.pullback f).Fiber => p.snd)).1 continuous_id

/-- The total space of a pulled-back atlas carries the pullback topology: a map into it is
continuous exactly when its base projection and its composite with `pullbackLift` are
continuous. -/
theorem continuous_totalSpace_pullback_iff {q : W → TotalSpace Unit (A.pullback f).Fiber} :
    Continuous q ↔
      Continuous (fun w => (q w).proj) ∧ Continuous (fun w => A.pullbackLift f (q w)) := by
  refine ⟨fun hq => ⟨(A.pullback f).continuous_proj.comp hq,
    (A.continuous_pullbackLift f).comp hq⟩, fun ⟨hp, hl⟩ => ?_⟩
  exact (A.continuous_mk_pullback_iff f hp (fun w => (q w).snd)).2 hl

end Continuity

variable {A} in
/-- Pull back a bundle map of atlases fibrewise along a continuous map. -/
def pullbackMap {D : FiniteRankAtlas 𝕜 Y} (g : A ⟶ D) : A.pullback f ⟶ D.pullback f where
  fiberMap x := g.fiberMap (f x)
  continuous_totalSpaceMap :=
    (D.continuous_totalSpace_pullback_iff f).2 ⟨(A.pullback f).continuous_proj,
      g.continuous_totalSpaceMap.comp (A.continuous_pullbackLift f)⟩

section PullbackMap

variable {A} {D C : FiniteRankAtlas 𝕜 Y}

/-- The pulled-back bundle map acts on the fibre at `x` as the original map on the fibre at
`f x`. -/
@[simp] theorem fiberMap_pullbackMap (g : A ⟶ D) (x : X) :
    (pullbackMap f g).fiberMap x = g.fiberMap (f x) := (rfl)

/-- The canonical lifts intertwine a pulled-back bundle map with the original one. -/
@[simp] theorem pullbackLift_totalSpaceMap (g : A ⟶ D)
    (p : TotalSpace Unit (A.pullback f).Fiber) :
    D.pullbackLift f ((pullbackMap f g).totalSpaceMap p) =
      g.totalSpaceMap (A.pullbackLift f p) := by
  rcases p with ⟨x, v⟩
  simp only [Hom.totalSpaceMap_mk, pullbackLift_mk]
  exact (g.totalSpaceMap_mk (f x) v).symm

@[simp] theorem pullbackMap_id : pullbackMap f (𝟙 A) = 𝟙 (A.pullback f) := (rfl)

@[simp] theorem pullbackMap_comp (g : A ⟶ D) (h : D ⟶ C) :
    pullbackMap f (g ≫ h) = pullbackMap f g ≫ pullbackMap f h := (rfl)

@[simp] theorem pullbackMap_add (g h : A ⟶ D) :
    pullbackMap f (g + h) = pullbackMap f g + pullbackMap f h := (rfl)

end PullbackMap

variable (𝕜) in
/-- Pullback of variable-rank atlases and their bundle maps along a continuous map. -/
-- Expose the object and morphism assignments for the generated projection lemmas.
@[expose, simps]
def pullbackFunctor : FiniteRankAtlas 𝕜 Y ⥤ FiniteRankAtlas 𝕜 X where
  obj A := A.pullback f
  map g := pullbackMap f g

/-- Pullback is additive; in particular it preserves the zero atlas and Whitney sums. -/
instance : (pullbackFunctor 𝕜 f).Additive where
  map_add := pullbackMap_add f _ _

/-- Evaluating a pulled-back atlas at `x` is evaluating the original atlas at `f x`. -/
theorem pullbackFunctor_comp_fiberFunctor (x : X) :
    pullbackFunctor 𝕜 f ⋙ fiberFunctor x = fiberFunctor (f x) := (rfl)

/-- Pulling back a trivial atlas gives the trivial atlas of the pulled-back rank. -/
@[simp] theorem pullback_trivial (r : LocallyConstant Y ℕ) :
    (trivial 𝕜 Y r).pullback f = trivial 𝕜 X (r.comap f) := (rfl)

/-- Pullback along a composite is the iterated pullback, with literally the same coordinate
data. -/
@[simp] theorem pullback_comp (g : C(Y, Z)) (B : FiniteRankAtlas 𝕜 Z) :
    (B.pullback g).pullback f = B.pullback (g.comp f) := (rfl)

/-- The canonical lift of a composite pullback factors through the two individual lifts. -/
theorem pullbackLift_comp (g : C(Y, Z)) (B : FiniteRankAtlas 𝕜 Z)
    (p : TotalSpace Unit (B.pullback (g.comp f)).Fiber) :
    B.pullbackLift (g.comp f) p = B.pullbackLift g ((B.pullback g).pullbackLift f p) := (rfl)

/-- Pullback along a composite is the composite of the pullback functors. -/
theorem pullbackFunctor_comp (g : C(Y, Z)) :
    pullbackFunctor 𝕜 g ⋙ pullbackFunctor 𝕜 f = pullbackFunctor 𝕜 (g.comp f) := (rfl)

/-- Pullback along the identity is isomorphic to the original atlas, by the identity on every
fibre. -/
def pullbackIdIso : A.pullback (ContinuousMap.id Y) ≅ A :=
  isoMk (fun _ => LinearEquiv.refl 𝕜 _) (A.continuous_pullbackLift _)
    ((A.continuous_totalSpace_pullback_iff _).2 ⟨A.continuous_proj, continuous_id⟩)

@[simp] theorem fiberMap_pullbackIdIso_hom (y : Y) :
    (pullbackIdIso A).hom.fiberMap y = LinearMap.id := by
  unfold pullbackIdIso
  exact fiberMap_isoMk_hom _ _ _ y

@[simp] theorem fiberMap_pullbackIdIso_inv (y : Y) :
    (pullbackIdIso A).inv.fiberMap y = LinearMap.id := by
  unfold pullbackIdIso
  exact fiberMap_isoMk_inv _ _ _ y

variable (𝕜 Y) in
/-- Pullback along the identity is naturally isomorphic to the identity functor. -/
def pullbackFunctorIdIso : pullbackFunctor 𝕜 (ContinuousMap.id Y) ≅ 𝟭 (FiniteRankAtlas 𝕜 Y) :=
  NatIso.ofComponents pullbackIdIso fun g => hom_ext fun y => by
    rw [fiberMap_comp, fiberMap_comp, fiberMap_pullbackIdIso_hom, fiberMap_pullbackIdIso_hom]
    simp only [pullbackFunctor_map, fiberMap_pullbackMap, ContinuousMap.id_apply, Functor.id_map]
    exact (LinearMap.id_comp _).trans (LinearMap.comp_id _).symm

@[simp] theorem pullbackFunctorIdIso_hom_app :
    (pullbackFunctorIdIso 𝕜 Y).hom.app A = (pullbackIdIso A).hom := (rfl)

@[simp] theorem pullbackFunctorIdIso_inv_app :
    (pullbackFunctorIdIso 𝕜 Y).inv.app A = (pullbackIdIso A).inv := (rfl)

end TauCeti.FiniteRankAtlas
