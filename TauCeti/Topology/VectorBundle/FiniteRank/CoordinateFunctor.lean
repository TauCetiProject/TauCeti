/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Continuous functors on coordinate spaces and the induced bundle operations

A `TauCeti.CoordinateFunctor 𝕜 𝕜'` sends each standard coordinate space `Fin n → 𝕜` to a
coordinate space `Fin (rank n) → 𝕜'`, and each continuous linear map between coordinate spaces to
a continuous linear map between their images. It preserves identities and composition, and its
action on maps is continuous. This is the classical notion of a continuous functor on
finite-dimensional vector spaces (Milnor–Stasheff, §3), written in coordinates.

Such a functor acts chartwise on finite-rank bundle cores. `CoordinateFunctor.mapCore` keeps the
charts of a core and applies the functor to its transition maps; functoriality is exactly what
makes the result satisfy the cocycle condition, and continuity of the action on maps makes the new
transitions continuous. Bundle maps are transformed in the same way (`CoordinateFunctor.mapHom`),
with fibre maps the images of the original fibre maps (`CoordinateFunctor.fiberMap_mapHom`).
Together these form a functor `CoordinateFunctor.functor` between the categories of finite-rank
bundle cores, which is additive when the action on maps is (`CoordinateFunctor.functor_additive`).
An additive bundle operation preserves Whitney sums, by Mathlib's preservation of biproducts by
additive functors. Trivial cores are sent to trivial cores (`CoordinateFunctor.mapCoreTrivialIso`).
Since the construction acts only on transition maps, it commutes strictly with pullback along
continuous maps of bases (`CoordinateFunctor.mapCore_pullback`,
`CoordinateFunctor.functor_comp_pullbackFunctor`).

Realification and complexification of bundles arise in this way.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, §3.
* M. F. Atiyah, *K-Theory*, §1.2.
-/

public section

open CategoryTheory VectorBundleCore

namespace TauCeti

universe u v w

/-- A continuous functor on standard coordinate spaces, from `𝕜`-coordinates to `𝕜'`-coordinates.
The coordinate space of dimension `n` is sent to that of dimension `rank n`, and the action on
continuous linear maps preserves identities and composition and is continuous. -/
structure CoordinateFunctor (𝕜 : Type v) [NontriviallyNormedField 𝕜]
    (𝕜' : Type w) [NontriviallyNormedField 𝕜'] where
  /-- The dimension of the image of the coordinate space of dimension `n`. -/
  rank : ℕ → ℕ
  /-- The action on continuous linear maps between coordinate spaces. -/
  map {m n : ℕ} : ((Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) →
    ((Fin (rank m) → 𝕜') →L[𝕜'] (Fin (rank n) → 𝕜'))
  /-- The action on maps is continuous. -/
  continuous_map (m n : ℕ) : Continuous (map (m := m) (n := n))
  /-- Identities are preserved. -/
  map_id (n : ℕ) :
    map (ContinuousLinearMap.id 𝕜 (Fin n → 𝕜)) = ContinuousLinearMap.id 𝕜' (Fin (rank n) → 𝕜')
  /-- Composition is preserved. -/
  map_comp {l m n : ℕ} (g : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜))
    (f : (Fin l → 𝕜) →L[𝕜] (Fin m → 𝕜)) : map (g.comp f) = (map g).comp (map f)

namespace CoordinateFunctor

attribute [simp] map_id map_comp

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {𝕜' : Type w} [NontriviallyNormedField 𝕜']
  (Φ : CoordinateFunctor 𝕜 𝕜') {B : Type u} [TopologicalSpace B]

/-- Apply a continuous coordinate functor to the transition maps of a finite-rank core, keeping
its charts. -/
-- Expose the rank projection so the dependent fibre model reduces to `Fin (Φ.rank _) → 𝕜'`.
@[expose]
def mapCore (A : FiniteRankBundleCore 𝕜 B) : FiniteRankBundleCore 𝕜' B where
  rank := Φ.rank A.rank
  core :=
    { baseSet := A.core.baseSet
      isOpen_baseSet := A.core.isOpen_baseSet
      indexAt := A.core.indexAt
      mem_baseSet_at := A.core.mem_baseSet_at
      coordChange i j x := Φ.map (A.core.coordChange i j x)
      coordChange_self i x hx v := by
        rw [show A.core.coordChange i i x = ContinuousLinearMap.id 𝕜 _ from
          ContinuousLinearMap.ext (A.core.coordChange_self i x hx), Φ.map_id,
          ContinuousLinearMap.id_apply]
      continuousOn_coordChange i j :=
        (Φ.continuous_map _ _).comp_continuousOn (A.core.continuousOn_coordChange i j)
      coordChange_comp i j k x hx v := by
        rw [← ContinuousLinearMap.comp_apply, ← Φ.map_comp,
          A.core.coordChange_linear_comp i j k x hx] }
  indexAt_eq := A.indexAt_eq

@[simp] theorem rank_mapCore (A : FiniteRankBundleCore 𝕜 B) :
    (Φ.mapCore A).rank = Φ.rank A.rank := (rfl)

/-- The transformed core has the charts of the original core. -/
@[simp] theorem localTriv_baseSet_mapCore (A : FiniteRankBundleCore 𝕜 B) (i : B) :
    ((Φ.mapCore A).core.localTriv i).baseSet = A.core.baseSet i := (rfl)

/-- The transitions of the transformed core are the images of the original transitions. -/
@[simp] theorem coordChange_mapCore (A : FiniteRankBundleCore 𝕜 B) (i j x : B) :
    (Φ.mapCore A).core.coordChange i j x = Φ.map (A.core.coordChange i j x) := (rfl)

variable {A D C : FiniteRankBundleCore 𝕜 B}

/-- Apply a continuous coordinate functor to the chart operators of a bundle map. -/
def mapHom (f : A ⟶ D) : Φ.mapCore A ⟶ Φ.mapCore D where
  operator i j := ⟨fun x => Φ.map (f.operator i j x),
    (Φ.continuous_map _ _).comp (f.operator i j).continuous⟩
  compatible i i' j j' x hi hi' hj hj' v := by
    -- The chart domains of the transformed cores are those of `A` and `D`.
    have hij : x ∈ A.core.baseSet i ∩ D.core.baseSet j := ⟨hi, hj⟩
    have hij' : x ∈ A.core.baseSet i' ∩ D.core.baseSet j' := ⟨hi', hj'⟩
    have key : (Φ.map (D.core.coordChange j j' x)).comp (Φ.map (f.operator i j ⟨x, hij⟩)) =
        (Φ.map (f.operator i' j' ⟨x, hij'⟩)).comp (Φ.map (A.core.coordChange i i' x)) := by
      have hf : (D.core.coordChange j j' x).comp (f.operator i j ⟨x, hij⟩) =
          (f.operator i' j' ⟨x, hij'⟩).comp (A.core.coordChange i i' x) :=
        ContinuousLinearMap.ext (f.compatible i i' j j' x hij.1 hij'.1 hij.2 hij'.2)
      rw [← Φ.map_comp, ← Φ.map_comp, hf]
    -- Both sides of the goal are the two composites applied to `v`.
    exact congrArg (fun S => S v) key

/-- On every fibre, the transformed bundle map is the image of the original fibre map. -/
@[simp] theorem fiberMap_mapHom (f : A ⟶ D) (x : B) :
    (Φ.mapHom f).fiberMap x = Φ.map (f.fiberMap x) := by
  rw [CoordinateHom.fiberMap_def, CoordinateHom.fiberMap_def]
  -- `mapCore` keeps the charts of `A` and `D`, so both sides evaluate the chart operators in the
  -- same preferred charts, and `mapHom` applies `Φ.map` to those operators.
  rfl

variable (B) in
/-- The bundle operation induced by a continuous coordinate functor, as a functor between the
categories of finite-rank cores. -/
-- Expose the object map so that the coordinate model of `(Φ.functor B).obj A` reduces.
@[expose]
def functor : FiniteRankBundleCore 𝕜 B ⥤ FiniteRankBundleCore 𝕜' B where
  obj := Φ.mapCore
  map := Φ.mapHom
  map_id A := FiniteRankBundleCore.hom_ext fun x => by
    rw [fiberMap_mapHom, FiniteRankBundleCore.fiberMap_id, FiniteRankBundleCore.fiberMap_id,
      map_id]
    -- The two identities are stated on the same coordinate space `Fin (Φ.rank A.rank) → 𝕜'`.
    rfl
  map_comp f g := FiniteRankBundleCore.hom_ext fun x => by
    rw [fiberMap_mapHom, FiniteRankBundleCore.fiberMap_comp, FiniteRankBundleCore.fiberMap_comp,
      fiberMap_mapHom, fiberMap_mapHom, map_comp]
    -- The two composites are stated on the same coordinate spaces `Fin (Φ.rank _) → 𝕜'`.
    rfl

@[simp] theorem functor_obj (A : FiniteRankBundleCore 𝕜 B) :
    (Φ.functor B).obj A = Φ.mapCore A := (rfl)

@[simp] theorem functor_map (f : A ⟶ D) : (Φ.functor B).map f = Φ.mapHom f := (rfl)

/-- The bundle operation of a coordinate functor whose action on maps is additive is an additive
functor; in particular it preserves Whitney sums. -/
theorem functor_additive (h : ∀ {m n : ℕ} (f g : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)),
    Φ.map (f + g) = Φ.map f + Φ.map g) : (Φ.functor B).Additive where
  map_add {_ _ f g} := FiniteRankBundleCore.hom_ext fun x => by
    -- Restate the goal on the transformed cores, where `fiberMap_mapHom` applies.
    change (Φ.mapHom (f + g)).fiberMap x = (Φ.mapHom f + Φ.mapHom g).fiberMap x
    rw [fiberMap_mapHom, FiniteRankBundleCore.fiberMap_add, h, FiniteRankBundleCore.fiberMap_add,
      fiberMap_mapHom, fiberMap_mapHom]
    -- The two sums are stated on the same coordinate spaces `Fin (Φ.rank _) → 𝕜'`.
    rfl

variable (B) in
/-- A continuous coordinate functor sends the trivial core of rank `n` to the trivial core of
rank `Φ.rank n`, by the identity on every fibre. -/
def mapCoreTrivialIso (n : ℕ) :
    Φ.mapCore (FiniteRankBundleCore.trivial 𝕜 B n) ≅
      FiniteRankBundleCore.trivial 𝕜' B (Φ.rank n) :=
  FiniteRankBundleCore.constIso (fun _ => rfl) (ContinuousLinearEquiv.refl 𝕜' _)
    -- Both transitions are identities; that of the transformed core is `Φ.map id`.
    fun _ _ _ _ _ => ContinuousLinearMap.ext fun v => congrArg (fun S => S v) (Φ.map_id n)

@[simp] theorem fiberMap_mapCoreTrivialIso_hom (n : ℕ) (x : B) :
    (Φ.mapCoreTrivialIso B n).hom.fiberMap x = ContinuousLinearMap.id 𝕜' (Fin (Φ.rank n) → 𝕜') := by
  rw [mapCoreTrivialIso]
  exact FiniteRankBundleCore.fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_mapCoreTrivialIso_inv (n : ℕ) (x : B) :
    (Φ.mapCoreTrivialIso B n).inv.fiberMap x = ContinuousLinearMap.id 𝕜' (Fin (Φ.rank n) → 𝕜') := by
  rw [mapCoreTrivialIso]
  exact FiniteRankBundleCore.fiberMap_constIso_inv _ _ _ x

section Pullback

variable {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous coordinate functor commutes strictly with pullback: both sides have the
pulled-back charts and the transformed pulled-back transitions. -/
@[simp] theorem mapCore_pullback (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    Φ.mapCore (A.pullback f) = (Φ.mapCore A).pullback f := (rfl)

/-- The transformed pullback of a bundle map is the pullback of the transformed bundle map. -/
@[simp] theorem mapHom_pullbackMap {A D : FiniteRankBundleCore 𝕜 Y} (a : A ⟶ D) (f : C(X, Y)) :
    Φ.mapHom (FiniteRankBundleCore.pullbackMap a f) =
      FiniteRankBundleCore.pullbackMap (Φ.mapHom a) f :=
  FiniteRankBundleCore.hom_ext fun x =>
    -- Both fibre maps are `Φ.map (a.fiberMap (f x))`, on the same coordinate spaces.
    ((Φ.fiberMap_mapHom _ x).trans
      (congrArg Φ.map (FiniteRankBundleCore.fiberMap_pullbackMap a f x))).trans
      ((Φ.fiberMap_mapHom a (f x)).symm.trans
        (FiniteRankBundleCore.fiberMap_pullbackMap (Φ.mapHom a) f x).symm)

/-- The bundle operation of a continuous coordinate functor commutes strictly with pullback, as
functors. -/
theorem functor_comp_pullbackFunctor (f : C(X, Y)) :
    Φ.functor Y ⋙ FiniteRankBundleCore.pullbackFunctor f =
      FiniteRankBundleCore.pullbackFunctor f ⋙ Φ.functor X :=
  Functor.hext (fun _ => rfl) fun _ _ a => heq_of_eq (Φ.mapHom_pullbackMap a f).symm

end Pullback

end CoordinateFunctor
end TauCeti
