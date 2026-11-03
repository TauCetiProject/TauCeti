/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Biproduct
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Topology.FiberBundle.Constructions

/-!
# Pullbacks of finite-rank bundle cores

For a continuous map `f : C(B', B)`, `FiniteRankBundleCore.pullback f A` is the point-indexed
core over `B'` whose chart at `x'` is the preimage of the chart of `A` at `f x'`, with the
transition matrices of `A` evaluated at the images of the base points. The rank is unchanged.
The spaces are arbitrary topological spaces and `f` is any continuous map.

`pullbackHomeomorph` identifies its reconstructed total space with the total space of Mathlib's
pullback bundle `f *ᵖ A.core.Fiber`. The comparison covers the identity of `B'` and is the
identity on every fibre, and it carries each core chart to Mathlib's pulled-back trivialization
(`pullbackHomeomorph_localTriv`).

Coordinate morphisms pull back by restricting their chart operators along `f`; on fibres this
is `fiberMap_pullbackMap`. This gives the additive functor `pullbackFunctor f`, together with
the natural isomorphisms `pullbackFunctorId` and `pullbackFunctorComp` for the identity and for
composites. Pullback is strictly compatible with trivial cores and Whitney sums
(`pullback_trivial`, `pullback_whitneySum`); since the functor is additive it also preserves
finite biproducts, by Mathlib's `preservesFiniteBiproductsOfAdditive`. Restriction to a subspace,
such as a clopen rank stratum, is pullback along its inclusion.

The construction uses Mathlib's `VectorBundleCore`, its pullback bundles
`Bundle.Pullback` and pulled-back trivializations `Bundle.Trivialization.pullback`.
-/

public section

open Bundle CategoryTheory VectorBundleCore

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B B' B'' : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace B'']

/-- The pullback of a finite-rank core along a continuous map. The chart at `x'` is the
preimage of the chart at `f x'`, and the transitions are those of the original core at the
image points. -/
-- Expose the rank projection so the dependent model reduces to the original model.
@[expose]
def pullback (f : C(B', B)) (A : FiniteRankBundleCore 𝕜 B) : FiniteRankBundleCore 𝕜 B' where
  rank := A.rank
  core :=
    { baseSet := fun i => f ⁻¹' A.core.baseSet (f i)
      isOpen_baseSet := fun i => (A.core.isOpen_baseSet (f i)).preimage f.continuous
      indexAt := id
      mem_baseSet_at := fun x => by
        simpa only [Set.mem_preimage, id_eq, A.indexAt_eq] using A.core.mem_baseSet_at (f x)
      coordChange := fun i j x => A.core.coordChange (f i) (f j) (f x)
      coordChange_self := fun i x hx v => A.core.coordChange_self (f i) (f x) hx v
      continuousOn_coordChange := fun i j =>
        (A.core.continuousOn_coordChange (f i) (f j)).comp f.continuous.continuousOn
          fun _ hx => hx
      coordChange_comp := fun i j k x hx v => A.core.coordChange_comp _ _ _ _ hx v }
  indexAt_eq := fun _ => rfl

variable (f : C(B', B)) (A D : FiniteRankBundleCore 𝕜 B)

@[simp] theorem rank_pullback : (A.pullback f).rank = A.rank := (rfl)

@[simp] theorem localTriv_baseSet_pullback (i : B') :
    ((A.pullback f).core.localTriv i).baseSet = f ⁻¹' (A.core.localTriv (f i)).baseSet := (rfl)

@[simp] theorem coordChange_pullback (i j x : B') :
    (A.pullback f).core.coordChange i j x = A.core.coordChange (f i) (f j) (f x) := (rfl)

/-- Pulling back a trivial core gives the trivial core of the same rank. -/
@[simp] theorem pullback_trivial (n : ℕ) : (trivial 𝕜 B n).pullback f = trivial 𝕜 B' n := (rfl)

/-- Pulling back commutes strictly with Whitney sums. -/
@[simp] theorem pullback_whitneySum :
    (whitneySum A D).pullback f = whitneySum (A.pullback f) (D.pullback f) := (rfl)

/-- Pulling back along a composite is pulling back successively. -/
theorem pullback_comp (g : C(B, B'')) (A : FiniteRankBundleCore 𝕜 B'') :
    A.pullback (g.comp f) = (A.pullback g).pullback f := (rfl)

/-! ### Comparison with Mathlib's pullback bundle -/

/-- The reconstructed total space of a pulled-back core is the total space of Mathlib's
pullback bundle. The comparison covers the identity and is the identity on each fibre. -/
def pullbackHomeomorph :
    (A.pullback f).core.TotalSpace ≃ₜ TotalSpace (Fin A.rank → 𝕜) ((f : B' → B) *ᵖ A.core.Fiber)
    where
  toFun p := ⟨p.proj, p.2⟩
  invFun p := ⟨p.proj, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    refine (inducing_pullbackTotalSpaceEmbedding _ _ _).continuous_iff.2 ?_
    refine (A.pullback f).core.continuous_proj.prodMk ?_
    refine continuous_iff_continuousAt.2 fun p ↦ ?_
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨(f.continuous.comp (A.pullback f).core.continuous_proj).continuousAt, ?_⟩
    -- Near `p`, the chart of `A` at `f p.proj` reads the coordinates of the pulled-back chart.
    let e := (A.pullback f).core.localTriv p.proj
    have hp : p ∈ e.source := (A.pullback f).core.mem_source_at p.proj p.2
    refine (e.continuousOn.continuousAt (e.open_source.mem_nhds hp)).snd.congr_of_eventuallyEq ?_
    filter_upwards [e.open_source.mem_nhds hp] with q _
    simp only [e, VectorBundleCore.trivializationAt, VectorBundleCore.localTrivAt,
      localTriv_apply, A.indexAt_eq, (A.pullback f).indexAt_eq, coordChange_pullback]
    -- Both coordinates are `A.core.coordChange (f q.proj) (f p.proj) (f q.proj) q.2`.
    rfl
  continuous_invFun := by
    refine continuous_iff_continuousAt.2 fun p ↦ ?_
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨(Pullback.continuous_proj _ _ _).continuousAt, ?_⟩
    -- Read the pulled-back chart through Mathlib's pulled-back trivialization.
    let e := (A.core.localTriv (f p.proj)).pullback f
    have hp : p ∈ e.source := by
      have h := A.core.mem_baseSet_at (f p.proj)
      rw [A.indexAt_eq] at h
      exact (A.core.mem_localTriv_source _ _).2 h
    refine (e.continuousOn.continuousAt (e.open_source.mem_nhds hp)).snd.congr_of_eventuallyEq ?_
    filter_upwards [e.open_source.mem_nhds hp] with q _
    simp only [e, Trivialization.pullback_apply, Pullback.lift, localTriv_apply,
      A.indexAt_eq]
    -- Both coordinates are `A.core.coordChange (f q.proj) (f p.proj) (f q.proj) q.2`.
    rfl

@[simp] theorem pullbackHomeomorph_apply (p : (A.pullback f).core.TotalSpace) :
    pullbackHomeomorph f A p = ⟨p.proj, p.2⟩ := (rfl)

@[simp] theorem pullbackHomeomorph_symm_apply
    (p : TotalSpace (Fin A.rank → 𝕜) ((f : B' → B) *ᵖ A.core.Fiber)) :
    (pullbackHomeomorph f A).symm p = ⟨p.proj, p.2⟩ := (rfl)

/-- The comparison carries the chart at `i` to Mathlib's pullback of the chart at `f i`. -/
theorem pullbackHomeomorph_localTriv (i : B') (p : (A.pullback f).core.TotalSpace) :
    (A.core.localTriv (f i)).pullback f (pullbackHomeomorph f A p) =
      (A.pullback f).core.localTriv i p := by
  simp only [Trivialization.pullback_apply, pullbackHomeomorph_apply,
    localTriv_apply, A.indexAt_eq, coordChange_pullback]
  -- Both sides are `(p.proj, A.core.coordChange (f p.proj) (f i) (f p.proj) p.2)`.
  rfl

/-! ### Pullback of coordinate morphisms -/

variable {A D}

/-- The pullback of a coordinate morphism: its chart operators restricted along `f`. -/
def pullbackMap (a : A ⟶ D) : A.pullback f ⟶ D.pullback f where
  operator i j := (a.operator (f i) (f j)).comp ⟨fun x => ⟨f x.1, x.2⟩, by fun_prop⟩
  compatible i i' j j' x hi hi' hj hj' v := a.compatible _ _ _ _ (f x) hi hi' hj hj' v

/-- On the fibre at `x`, the pulled-back morphism is the original morphism at `f x`. -/
@[simp] theorem fiberMap_pullbackMap (a : A ⟶ D) (x : B') :
    (pullbackMap f a).fiberMap x = a.fiberMap (f x) := by
  -- In the charts at `f x`, the coordinate expression of a fibre map is the map itself.
  have h := A.core.inChartCoordinates_indexAt D.core (f x) (a.fiberMap (f x))
  rw [A.indexAt_eq, D.indexAt_eq] at h
  rw [CoordinateHom.fiberMap_def]
  exact (a.operator_eq (f x) (f x) _).trans h

variable (𝕜) in
/-- Pullback along `f` as an additive functor of finite-rank cores. -/
-- Expose the object map so that pulled-back objects are definitionally `pullback f A`.
@[expose, simps obj]
def pullbackFunctor : FiniteRankBundleCore 𝕜 B ⥤ FiniteRankBundleCore 𝕜 B' where
  obj A := A.pullback f
  map a := pullbackMap f a
  -- The two sides agree up to the defeq rank expressions `(A.pullback f).rank = A.rank`.
  map_id A := hom_ext fun x => by rw [fiberMap_pullbackMap, fiberMap_id, fiberMap_id]; rfl
  map_comp a b := hom_ext fun x => by
    rw [fiberMap_pullbackMap, fiberMap_comp, fiberMap_comp, fiberMap_pullbackMap,
      fiberMap_pullbackMap]; rfl

@[simp] theorem pullbackFunctor_map (a : A ⟶ D) :
    (pullbackFunctor 𝕜 f).map a = pullbackMap f a := (rfl)

/-- Pulling back morphisms is additive. -/
theorem pullbackMap_add (a b : A ⟶ D) : pullbackMap f (a + b) = pullbackMap f a + pullbackMap f b :=
  hom_ext fun x => by
    rw [fiberMap_add, fiberMap_pullbackMap, fiberMap_pullbackMap, fiberMap_pullbackMap,
      fiberMap_add]
    -- The two sides agree up to the defeq rank expression `(A.pullback f).rank = A.rank`.
    rfl

instance : (pullbackFunctor 𝕜 f).Additive where
  map_add {_ _ a b} := pullbackMap_add f a b

/-- A core is isomorphic to its pullback along the identity, by maps that are the identity
on every fibre. -/
def pullbackIdIso (A : FiniteRankBundleCore 𝕜 B) : A.pullback (ContinuousMap.id B) ≅ A where
  -- Both cores have the same charts and transitions, so the identity's operators serve.
  hom := ⟨(CoordinateHom.id A.core).operator, (CoordinateHom.id A.core).compatible⟩
  inv := ⟨(CoordinateHom.id A.core).operator, (CoordinateHom.id A.core).compatible⟩
  hom_inv_id := hom_ext fun x => by
    rw [fiberMap_comp, fiberMap_id, CoordinateHom.fiberMap_def, CoordinateHom.fiberMap_def]
    simp only [CoordinateHom.operator_id]
    -- The two operators are the transitions between the chart at `x` and the preferred chart.
    refine ContinuousLinearMap.ext fun v => ?_
    exact (A.core.coordChange_comp x (A.core.indexAt x) x x
      ⟨⟨(A.pullback (.id B)).core.mem_baseSet_at x, A.core.mem_baseSet_at x⟩,
        (A.pullback (.id B)).core.mem_baseSet_at x⟩ v).trans
      (A.core.coordChange_self x x ((A.pullback (.id B)).core.mem_baseSet_at x) v)
  inv_hom_id := hom_ext fun x => by
    rw [fiberMap_comp, fiberMap_id, CoordinateHom.fiberMap_def, CoordinateHom.fiberMap_def]
    simp only [CoordinateHom.operator_id]
    -- The two operators are the transitions between the preferred chart and the chart at `x`.
    refine ContinuousLinearMap.ext fun v => ?_
    exact (A.core.coordChange_comp (A.core.indexAt x) x (A.core.indexAt x) x
      ⟨⟨A.core.mem_baseSet_at x, (A.pullback (.id B)).core.mem_baseSet_at x⟩,
        A.core.mem_baseSet_at x⟩ v).trans
      (A.core.coordChange_self _ x (A.core.mem_baseSet_at x) v)

@[simp] theorem fiberMap_pullbackIdIso_hom (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (pullbackIdIso A).hom.fiberMap x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) := by
  rw [CoordinateHom.fiberMap_def]
  simp only [pullbackIdIso, CoordinateHom.operator_id]
  -- The operator is the transition from the chart at `x` to the preferred chart at `x`.
  exact (congrArg (A.core.coordChange x · x) (A.indexAt_eq x)).trans (coordChange_self A x)

@[simp] theorem fiberMap_pullbackIdIso_inv (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (pullbackIdIso A).inv.fiberMap x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) := by
  rw [CoordinateHom.fiberMap_def]
  simp only [pullbackIdIso, CoordinateHom.operator_id]
  -- The operator is the transition from the preferred chart at `x` to the chart at `x`.
  exact (congrArg (A.core.coordChange · x x) (A.indexAt_eq x)).trans (coordChange_self A x)

/-- The comparison with the pullback along the identity is natural. -/
theorem pullbackMap_comp_pullbackIdIso_hom (a : A ⟶ D) :
    pullbackMap (.id B) a ≫ (pullbackIdIso D).hom = (pullbackIdIso A).hom ≫ a :=
  hom_ext fun x => by
    rw [fiberMap_comp, fiberMap_comp, fiberMap_pullbackIdIso_hom, fiberMap_pullbackIdIso_hom,
      fiberMap_pullbackMap]
    -- The two sides agree up to the defeq rank expression `(A.pullback f).rank = A.rank`.
    rfl

/-- Pulling back a morphism along a composite is pulling it back successively. -/
theorem pullbackMap_comp (g : C(B, B'')) {A D : FiniteRankBundleCore 𝕜 B''} (a : A ⟶ D) :
    pullbackMap (g.comp f) a = pullbackMap f (pullbackMap g a) :=
  hom_ext fun x => (fiberMap_pullbackMap (g.comp f) a x).trans
    ((fiberMap_pullbackMap g a (f x)).symm.trans (fiberMap_pullbackMap f (pullbackMap g a) x).symm)

variable (𝕜 B) in
/-- Pullback along the identity is naturally isomorphic to the identity functor, by maps that
are the identity on every fibre. -/
def pullbackFunctorId : pullbackFunctor 𝕜 (ContinuousMap.id B) ≅ 𝟭 _ :=
  NatIso.ofComponents pullbackIdIso pullbackMap_comp_pullbackIdIso_hom

@[simp] theorem pullbackFunctorId_hom_app (A : FiniteRankBundleCore 𝕜 B) :
    (pullbackFunctorId 𝕜 B).hom.app A = (pullbackIdIso A).hom := by
  unfold pullbackFunctorId
  rfl

@[simp] theorem pullbackFunctorId_inv_app (A : FiniteRankBundleCore 𝕜 B) :
    (pullbackFunctorId 𝕜 B).inv.app A = (pullbackIdIso A).inv := by
  unfold pullbackFunctorId
  rfl

variable (𝕜) in
/-- Pullback along a composite is naturally isomorphic to the composite of the pullbacks.
The components are identities, since the two pulled-back cores coincide. -/
def pullbackFunctorComp (g : C(B, B'')) :
    pullbackFunctor 𝕜 (g.comp f) ≅ pullbackFunctor 𝕜 g ⋙ pullbackFunctor 𝕜 f :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun a =>
    (Category.comp_id _).trans ((pullbackMap_comp f g a).trans (Category.id_comp _).symm)

@[simp] theorem pullbackFunctorComp_hom_app (g : C(B, B'')) (A : FiniteRankBundleCore 𝕜 B'') :
    (pullbackFunctorComp 𝕜 f g).hom.app A = 𝟙 (A.pullback (g.comp f)) := by
  unfold pullbackFunctorComp
  rfl

@[simp] theorem pullbackFunctorComp_inv_app (g : C(B, B'')) (A : FiniteRankBundleCore 𝕜 B'') :
    (pullbackFunctorComp 𝕜 f g).inv.app A = 𝟙 (A.pullback (g.comp f)) := by
  unfold pullbackFunctorComp
  rfl

end TauCeti.FiniteRankBundleCore
