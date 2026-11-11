/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Biproduct
public import Mathlib.Topology.VectorBundle.Constructions

/-!
# Pullback of point-indexed finite-rank bundle cores

Pullback retains the finite coordinate model and indexes charts by the new base points.
Its chart at `x` is the inverse image of the old chart at `f x`. In particular the
construction does not retain the old base as a chart index type. This matters when
presenting bundles in the universe of their base.

`FiniteRankBundleCore.pullbackFunctor` pulls back both bundles and continuous linear
bundle maps, and preserves addition. Identity and composition of base maps give
strict equalities of functors, not just equality of bundle classes. Pullback is also strictly
compatible with trivial cores and Whitney sums (`pullback_trivial`, `pullback_whitneySum`).
The reconstructed bundle is identified with Mathlib's actual pullback by `pullbackHomeomorph`,
which carries each core chart to Mathlib's pulled-back trivialization
(`pullbackHomeomorph_localTriv`).

The construction uses Mathlib's vector-bundle cores and native pullback topology,
and `VectorBundleCore.CoordinateHom` for descent of continuous linear bundle maps.
-/

public section

open Bundle CategoryTheory VectorBundleCore

namespace TauCeti.FiniteRankBundleCore

universe u v w z

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} {Y : Type w} {Z : Type z}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Pull back a finite-rank core, indexing its charts by the new base points. -/
-- Reduce the rank also during implicit-argument matching of coordinate-map simp lemmas.
@[expose, implicit_reducible]
def pullback (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) : FiniteRankBundleCore 𝕜 X where
  rank := A.rank
  core :=
    { baseSet := fun x => f ⁻¹' A.core.baseSet (f x)
      isOpen_baseSet := fun x => (A.core.isOpen_baseSet (f x)).preimage f.continuous
      indexAt := id
      mem_baseSet_at := fun x => by
        simpa only [Set.mem_preimage, id_eq, A.indexAt_eq] using A.core.mem_baseSet_at (f x)
      coordChange := fun i j x => A.core.coordChange (f i) (f j) (f x)
      coordChange_self := fun i x hx v => A.core.coordChange_self (f i) (f x) hx v
      continuousOn_coordChange := fun i j =>
        (A.core.continuousOn_coordChange (f i) (f j)).comp f.continuous.continuousOn
          (fun _ hx => hx)
      coordChange_comp := fun i j k x hx v =>
        A.core.coordChange_comp (f i) (f j) (f k) (f x) hx v }
  indexAt_eq := fun _ => rfl

@[simp] theorem rank_pullback (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    (A.pullback f).rank = A.rank := (rfl)

@[simp] theorem localTriv_baseSet_pullback (A : FiniteRankBundleCore 𝕜 Y)
    (f : C(X, Y)) (i : X) :
    ((A.pullback f).core.localTriv i).baseSet =
      f ⁻¹' (A.core.localTriv (f i)).baseSet := (rfl)

@[simp] theorem coordChange_pullback (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    (i j x : X) :
    (A.pullback f).core.coordChange i j x = A.core.coordChange (f i) (f j) (f x) := (rfl)

/-- Pulling back a trivial core gives the trivial core of the same rank. -/
@[simp] theorem pullback_trivial (f : C(X, Y)) (n : ℕ) :
    (trivial 𝕜 Y n).pullback f = trivial 𝕜 X n := (rfl)

/-- Pulling back commutes strictly with Whitney sums. -/
@[simp] theorem pullback_whitneySum (A D : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    (whitneySum A D).pullback f = whitneySum (A.pullback f) (D.pullback f) := (rfl)

/-- Pull back compatible chart operators. Their continuity is inherited by composition
with the map between the actual chart intersections. -/
def pullbackMap {A D : FiniteRankBundleCore 𝕜 Y} (a : A ⟶ D) (f : C(X, Y)) :
    A.pullback f ⟶ D.pullback f where
  operator i j := (a.operator (f i) (f j)).comp
    ⟨fun x => ⟨f x, x.2⟩, (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  compatible i i' j j' x hi hi' hj hj' v :=
    a.compatible (f i) (f i') (f j) (f j') (f x) hi hi' hj hj' v

@[simp] theorem operator_pullbackMap {A D : FiniteRankBundleCore 𝕜 Y} (a : A ⟶ D)
    (f : C(X, Y)) (i j : X) :
    (pullbackMap a f).operator i j = (a.operator (f i) (f j)).comp
      ⟨fun x : ↥((A.pullback f).core.baseSet i ∩ (D.pullback f).core.baseSet j) => ⟨f x, x.2⟩,
        (f.continuous.comp continuous_subtype_val).subtype_mk _⟩ := (rfl)

/-- In preferred coordinates pullback simply evaluates the original map at `f x`. -/
@[simp] theorem fiberMap_pullbackMap {A D : FiniteRankBundleCore 𝕜 Y} (a : A ⟶ D)
    (f : C(X, Y)) (x : X) :
    (pullbackMap a f).fiberMap x = a.fiberMap (f x) := by
  symm
  exact congrFun (CoordinateHom.fiberMap_unique (pullbackMap a f)
    (fun x => a.fiberMap (f x)) (fun i j x v => by
      -- Normalize the dependent finite-coordinate models before comparing chart operators.
      dsimp only [pullback, pullbackMap, ContinuousMap.comp_apply, ContinuousMap.coe_mk, id_eq]
      convert a.coordChange_fiberMap (f i) (f j) x.2.1 x.2.2 v using 1 <;>
        simp only [A.indexAt_eq, D.indexAt_eq])) x

/-- Pullback preserves identity bundle maps. -/
@[simp] theorem pullbackMap_id (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    pullbackMap (𝟙 A) f = 𝟙 (A.pullback f) := by
  apply hom_ext
  intro x
  simp only [fiberMap_pullbackMap, fiberMap_id]
  -- The coordinate models coincide definitionally, as recorded by `rank_pullback`.
  rfl

/-- Pullback preserves composition of bundle maps. -/
@[simp] theorem pullbackMap_comp {A D E : FiniteRankBundleCore 𝕜 Y}
    (a : A ⟶ D) (b : D ⟶ E) (f : C(X, Y)) :
    pullbackMap (a ≫ b) f = pullbackMap a f ≫ pullbackMap b f := by
  apply hom_ext
  intro x
  simp only [fiberMap_comp, fiberMap_pullbackMap]

/-- Pullback preserves sums of bundle maps. -/
@[simp] theorem pullbackMap_add {A D : FiniteRankBundleCore 𝕜 Y} (a b : A ⟶ D)
    (f : C(X, Y)) : pullbackMap (a + b) f = pullbackMap a f + pullbackMap b f := by
  apply hom_ext
  intro x
  simp only [fiberMap_add, fiberMap_pullbackMap]

/-- Pullback preserves the zero bundle map. -/
@[simp] theorem pullbackMap_zero (A D : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    pullbackMap (0 : A ⟶ D) f = 0 := by
  apply hom_ext
  intro x
  simp only [fiberMap_pullbackMap, CoordinateHom.fiberMap_zero]

/-- Pullback preserves negatives of bundle maps. -/
@[simp] theorem pullbackMap_neg {A D : FiniteRankBundleCore 𝕜 Y} (a : A ⟶ D)
    (f : C(X, Y)) : pullbackMap (-a) f = -pullbackMap a f := by
  apply hom_ext
  intro x
  simp only [fiberMap_neg, fiberMap_pullbackMap]

/-- Pullback on bundles and their continuous fibrewise linear maps. -/
-- Its object projection must reduce when simp matches the dependent fibre-map types.
@[expose, reducible]
def pullbackFunctor (f : C(X, Y)) : FiniteRankBundleCore 𝕜 Y ⥤ FiniteRankBundleCore 𝕜 X where
  obj A := A.pullback f
  map a := pullbackMap a f
  map_id A := pullbackMap_id A f
  map_comp a b := pullbackMap_comp a b f

@[simp] theorem pullbackFunctor_obj (f : C(X, Y)) (A : FiniteRankBundleCore 𝕜 Y) :
    (pullbackFunctor f).obj A = A.pullback f := (rfl)

@[simp] theorem pullbackFunctor_map {A D : FiniteRankBundleCore 𝕜 Y} (a : A ⟶ D)
    (f : C(X, Y)) :
    (pullbackFunctor f).map a = pullbackMap a f := (rfl)

/-- Pullback is additive, with no compactness or separation assumption on either base. -/
instance (f : C(X, Y)) : (pullbackFunctor (𝕜 := 𝕜) f).Additive where
  map_add := fun {_ _ a b} => pullbackMap_add a b f

/-- Pullback by the identity retains the original point-indexed core. -/
@[simp] theorem pullback_id (A : FiniteRankBundleCore 𝕜 Y) :
    A.pullback (ContinuousMap.id Y) = A := by
  induction A using induction_on
  rfl

/-- Iterated pullback and pullback by a composite have literally the same coordinate data. -/
@[simp] theorem pullback_comp (A : FiniteRankBundleCore 𝕜 Z) (f : C(X, Y)) (g : C(Y, Z)) :
    (A.pullback g).pullback f = A.pullback (g.comp f) := (rfl)

/-- Pullback by the identity is the identity functor, including on morphisms. -/
@[simp] theorem pullbackFunctor_id :
    pullbackFunctor (𝕜 := 𝕜) (ContinuousMap.id Y) = 𝟭 (FiniteRankBundleCore 𝕜 Y) := by
  apply Functor.hext pullback_id
  intro A D a
  induction A using induction_on
  induction D using induction_on
  apply heq_of_eq
  apply hom_ext
  intro x
  exact fiberMap_pullbackMap a (ContinuousMap.id Y) x

/-- Pullback is contravariantly compatible with composition of base maps. -/
@[simp] theorem pullbackFunctor_comp (f : C(X, Y)) (g : C(Y, Z)) :
    pullbackFunctor (𝕜 := 𝕜) g ⋙ pullbackFunctor f = pullbackFunctor (g.comp f) := by
  apply Functor.hext (fun A => pullback_comp A f g)
  intro A D a
  apply heq_of_eq
  apply hom_ext
  intro x
  exact (fiberMap_pullbackMap (pullbackMap a g) f x).trans
    ((fiberMap_pullbackMap a g (f x)).trans (fiberMap_pullbackMap a (g.comp f) x).symm)

private def pullbackTotalEquiv (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    (A.pullback f).core.TotalSpace ≃ TotalSpace (Fin A.rank → 𝕜) ((⇑f) *ᵖ A.core.Fiber) where
  toFun p := ⟨p.proj, p.2⟩
  invFun p := ⟨p.proj, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem pullback_chart (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    (i : X) (p : (A.pullback f).core.TotalSpace) :
    ((A.core.localTriv (f i)) ⟨f p.proj, p.2⟩).2 =
      (((A.pullback f).core.localTriv i) p).2 := by
  simp only [localTriv_apply, indexAt_eq, coordChange_pullback]

private theorem continuous_pullbackLift (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    Continuous (fun p : (A.pullback f).core.TotalSpace =>
      (⟨f p.proj, p.2⟩ : A.core.TotalSpace)) := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(f.continuous.comp (A.pullback f).core.continuous_proj).continuousAt, ?_⟩
  have hp := (A.pullback f).core.mem_source_at p.proj p.2
  have hc := (((A.pullback f).core.localTrivAt p.proj).continuousOn.continuousAt
    (((A.pullback f).core.localTrivAt p.proj).open_source.mem_nhds hp)).snd
  apply hc.congr_of_eventuallyEq
  filter_upwards [] with q
  simp only [VectorBundleCore.trivializationAt, localTrivAt, indexAt_eq]
  exact pullback_chart A f p.proj q

/-- The reconstructed pullback core is the native Mathlib pullback bundle. The map
covers the identity and is the identity linear equivalence in preferred fibre coordinates. -/
def pullbackHomeomorph (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    (A.pullback f).core.TotalSpace ≃ₜ TotalSpace (Fin A.rank → 𝕜) ((⇑f) *ᵖ A.core.Fiber) where
  toEquiv := pullbackTotalEquiv A f
  continuous_toFun := by
    rw [(inducing_pullbackTotalSpaceEmbedding (Fin A.rank → 𝕜) A.core.Fiber f).continuous_iff]
    exact (A.pullback f).core.continuous_proj.prodMk (continuous_pullbackLift A f)
  continuous_invFun := by
    refine continuous_iff_continuousAt.2 fun p => ?_
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨(Pullback.continuous_proj (Fin A.rank → 𝕜) A.core.Fiber f).continuousAt, ?_⟩
    let e := A.core.localTriv (f p.proj)
    have hp : (⟨f p.proj, p.2⟩ : A.core.TotalSpace) ∈ e.source := by
      apply (A.core.mem_localTriv_source (f p.proj) _).2
      simpa only [A.indexAt_eq] using A.core.mem_baseSet_at (f p.proj)
    have hc := (e.continuousOn.continuousAt (e.open_source.mem_nhds hp)).comp
      (f := Pullback.lift (F := Fin A.rank → 𝕜) (E := A.core.Fiber) (⇑f)) (x := p)
      (Pullback.continuous_lift (Fin A.rank → 𝕜) A.core.Fiber f).continuousAt
    apply hc.snd.congr_of_eventuallyEq
    filter_upwards [] with q
    simp only [VectorBundleCore.trivializationAt, localTrivAt, indexAt_eq, pullbackTotalEquiv]
    exact (pullback_chart A f p.proj (⟨q.proj, q.2⟩ : _)).symm

@[simp] theorem pullbackHomeomorph_apply (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    (p : (A.pullback f).core.TotalSpace) :
    A.pullbackHomeomorph f p = ⟨p.proj, p.2⟩ := (rfl)

@[simp] theorem pullbackHomeomorph_symm_apply (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    (p : TotalSpace (Fin A.rank → 𝕜) ((⇑f) *ᵖ A.core.Fiber)) :
    (A.pullbackHomeomorph f).symm p = ⟨p.proj, p.2⟩ := (rfl)

/-- The comparison carries the chart at `i` to Mathlib's pullback of the chart at `f i`. -/
theorem pullbackHomeomorph_localTriv (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) (i : X)
    (p : (A.pullback f).core.TotalSpace) :
    (A.core.localTriv (f i)).pullback f (A.pullbackHomeomorph f p) =
      (A.pullback f).core.localTriv i p := by
  simp only [Trivialization.pullback_apply, pullbackHomeomorph_apply,
    localTriv_apply, A.indexAt_eq, coordChange_pullback]
  -- Both sides are `(p.proj, A.core.coordChange (f p.proj) (f i) (f p.proj) p.2)`.
  rfl

/-- Pulling back a bundle morphism commutes with the native map to the original total space. -/
theorem pullbackHomeomorph_naturality {A D : FiniteRankBundleCore 𝕜 Y} (a : A ⟶ D)
    (f : C(X, Y)) (p : (A.pullback f).core.TotalSpace) :
    Pullback.lift f (D.pullbackHomeomorph f ((pullbackMap a f).totalSpaceMap p)) =
      a.totalSpaceMap (Pullback.lift f (A.pullbackHomeomorph f p)) := by
  rcases p with ⟨x, v⟩
  simp only [CoordinateHom.totalSpaceMap_mk, pullbackHomeomorph_apply, fiberMap_pullbackMap]
  exact (Pullback.lift_mk (E := D.core.Fiber) (F := Fin D.rank → 𝕜) f x _).trans
    ((a.totalSpaceMap_mk (f x) v).symm.trans
      (congrArg a.totalSpaceMap
        (Pullback.lift_mk (E := A.core.Fiber) (F := Fin A.rank → 𝕜) f x v).symm))

end TauCeti.FiniteRankBundleCore
