/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Stratum
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback

/-!
# Pullback of variable-rank bundle atlases

Pulling back a `TauCeti.FiniteRankAtlas` along `f : C(X, Y)` pulls back its locally constant rank
via `LocallyConstant.comap` and each stratum core via `TauCeti.FiniteRankBundleCore.pullback`,
keeping charts indexed by the new base points. Together with `pullbackLift` and `pullbackMap`, this
defines the additive contravariant functor `pullbackFunctor`, satisfying strict identity and
composition laws (`pullbackFunctor_id`, `pullbackFunctor_comp`).
-/

public section

open Bundle CategoryTheory

namespace TauCeti.FiniteRankAtlas

universe u v w z

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} {Y : Type w} {Z : Type z}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Pull back a variable-rank atlas along a continuous map of bases. -/
-- Expose the rank projection so pulled-back coordinate fibres reduce to `A.Fiber (f x)`.
@[expose, implicit_reducible]
def pullback (A : FiniteRankAtlas 𝕜 Y) (f : C(X, Y)) : FiniteRankAtlas 𝕜 X where
  rank := A.rank.comap f
  charts n := ((A.stratumCore n).pullback ⟨fun x : {x : X // A.rank.comap f x = n} => ⟨f x.1, x.2⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩).core
  indexAt_eq _ _ := rfl

@[simp] theorem rank_pullback (A : FiniteRankAtlas 𝕜 Y) (f : C(X, Y)) :
    (A.pullback f).rank = A.rank.comap f := (rfl)

@[simp] theorem pullback_trivialOfRank (r : LocallyConstant Y ℕ) (f : C(X, Y)) :
    (trivialOfRank 𝕜 r).pullback f = trivialOfRank 𝕜 (r.comap f) := (rfl)

@[simp] theorem pullback_trivial (f : C(X, Y)) (n : ℕ) :
    (trivial 𝕜 Y n).pullback f = trivial 𝕜 X n := (rfl)

/-- Pullback along the identity map recovers the original variable-rank atlas. -/
@[simp] theorem pullback_id (A : FiniteRankAtlas 𝕜 Y) : A.pullback (ContinuousMap.id Y) = A := by
  induction A using induction_on; rfl

/-- Iterated pullback of variable-rank atlases agrees strictly with composite pullback. -/
@[simp] theorem pullback_comp (A : FiniteRankAtlas 𝕜 Z) (f : C(X, Y)) (g : C(Y, Z)) :
    (A.pullback g).pullback f = A.pullback (g.comp f) := (rfl)

/-- Canonical continuous total-space map from a pulled-back atlas covering `f`. -/
def pullbackLift (A : FiniteRankAtlas 𝕜 Y) (f : C(X, Y)) :
    C(TotalSpace Unit (A.pullback f).Fiber, TotalSpace Unit A.Fiber) where
  toFun p := ⟨f p.proj, p.2⟩
  continuous_toFun := (A.continuous_mk_iff_rankStrata
    (f.continuous.comp (A.pullback f).continuous_proj) (fun p => p.2)).2 fun m => by
      have hm := ((A.pullback f).continuous_mk_iff_rankStrata
        (A.pullback f).continuous_proj (fun p => p.2)).1 continuous_id m
      exact (((A.stratumCore m).continuous_pullbackLift
        ⟨fun x : {x : X // A.rank.comap f x = m} => ⟨f x.1, x.2⟩,
          (f.continuous.comp continuous_subtype_val).subtype_mk _⟩).comp hm).congr
        fun ⟨⟨_, _⟩, hx⟩ => by cases hx; exact (A.stratumCore _).pullbackLift_mk _ _ _

@[simp] theorem pullbackLift_mk (A : FiniteRankAtlas 𝕜 Y) (f : C(X, Y))
    (x : X) (v : (A.pullback f).Fiber x) : pullbackLift A f ⟨x, v⟩ = ⟨f x, v⟩ := (rfl)

/-- Pull back a morphism of variable-rank atlases along a continuous base map. -/
def pullbackMap {A D : FiniteRankAtlas 𝕜 Y} (φ : A ⟶ D) (f : C(X, Y)) :
    A.pullback f ⟶ D.pullback f where
  fiberMap x := φ.fiberMap (f x)
  continuous_totalSpaceMap := ((D.pullback f).continuous_mk_iff_rankStrata
    (A.pullback f).continuous_proj _).2 fun n => by
      let inc : C({x : X // D.rank.comap f x = n}, {y : Y // D.rank y = n}) :=
        ⟨fun x => ⟨f x.1, x.2⟩, (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
      rw [(D.stratumCore n).continuous_core_pullback_iff inc]
      have hφ := (D.continuous_mk_iff_rankStrata A.continuous_proj
        (fun q : TotalSpace Unit A.Fiber => φ.fiberMap q.proj q.2)).1 φ.continuous_totalSpaceMap n
      exact ⟨((A.pullback f).continuous_proj.comp continuous_subtype_val).subtype_mk _,
        (hφ.comp (((pullbackLift A f).continuous.comp continuous_subtype_val).subtype_mk
          fun p => p.2)).congr fun ⟨⟨x, _⟩, hx⟩ => by
            dsimp only [Function.comp_apply, pullbackLift_mk]
            exact ((D.stratumCore n).pullbackLift_mk inc ⟨x, hx⟩ _).symm⟩

@[simp] theorem fiberMap_pullbackMap {A D : FiniteRankAtlas 𝕜 Y} (φ : A ⟶ D)
    (f : C(X, Y)) (x : X) : (pullbackMap φ f).fiberMap x = φ.fiberMap (f x) := (rfl)

@[simp] theorem pullbackMap_id (A : FiniteRankAtlas 𝕜 Y) (f : C(X, Y)) :
    pullbackMap (𝟙 A) f = 𝟙 (A.pullback f) := hom_ext fun _ => rfl

@[simp] theorem pullbackMap_comp {A D E : FiniteRankAtlas 𝕜 Y} (φ : A ⟶ D) (ψ : D ⟶ E)
    (f : C(X, Y)) : pullbackMap (φ ≫ ψ) f = pullbackMap φ f ≫ pullbackMap ψ f :=
  hom_ext fun _ => rfl

/-- Contravariant pullback functor on variable-rank bundle atlases. -/
-- Expose the object assignment so morphism types act on `A.pullback f`.
@[expose, reducible]
def pullbackFunctor (f : C(X, Y)) : FiniteRankAtlas 𝕜 Y ⥤ FiniteRankAtlas 𝕜 X where
  obj A := A.pullback f
  map φ := pullbackMap φ f

@[simp] theorem pullbackFunctor_obj (f : C(X, Y)) (A : FiniteRankAtlas 𝕜 Y) :
    (pullbackFunctor f).obj A = A.pullback f := (rfl)

@[simp] theorem pullbackFunctor_map (f : C(X, Y)) {A D : FiniteRankAtlas 𝕜 Y} (φ : A ⟶ D) :
    (pullbackFunctor f).map φ = pullbackMap φ f := (rfl)

instance (f : C(X, Y)) : (pullbackFunctor (𝕜 := 𝕜) f).Additive where
  map_add := by intros; exact hom_ext fun _ => rfl

/-- Pullback along the identity continuous map is strictly the identity functor. -/
@[simp] theorem pullbackFunctor_id :
    pullbackFunctor (𝕜 := 𝕜) (ContinuousMap.id Y) = 𝟭 (FiniteRankAtlas 𝕜 Y) :=
  Functor.hext pullback_id fun A D _ => by
    induction A using induction_on; induction D using induction_on
    exact heq_of_eq (hom_ext fun _ => rfl)

/-- Pullback of variable-rank atlases is strictly contravariant under composition. -/
@[simp] theorem pullbackFunctor_comp (f : C(X, Y)) (g : C(Y, Z)) :
    pullbackFunctor (𝕜 := 𝕜) g ⋙ pullbackFunctor f = pullbackFunctor (g.comp f) :=
  Functor.hext (fun A => pullback_comp A f g) fun _ _ _ => heq_of_eq (hom_ext fun _ => rfl)

end TauCeti.FiniteRankAtlas
