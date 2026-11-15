/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Biproduct
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.Topology.VectorBundle.Constructions

/-!
# Pullback of point-indexed finite-rank bundle cores

Pullback retains the finite coordinate model and indexes charts by the new base points.
Its chart at `x` is the inverse image of the old chart at `f x`. In particular the
construction does not retain the old base as a chart index type. This matters when
presenting bundles in the universe of their base.

`FiniteRankBundleCore.pullbackFunctor` pulls back both bundles and continuous linear
bundle maps, and preserves addition. Identity and composition of base maps give
strict equalities of functors, not just equality of bundle classes, and `pullbackRankClass`
gives the induced contravariant action on isomorphism classes of fixed rank. Pullback is also
strictly compatible with trivial cores, constant maps, and Whitney sums (`pullback_trivial`,
`pullback_const`, `pullback_whitneySum`) together with the Whitney projections, inclusions,
pairings, copairings, and direct sums of maps, and `pullbackOfBundleIso` identifies
`(ofBundle 𝕜 n E).pullback f` with `ofBundle 𝕜 n ((⇑f) *ᵖ E)`.
The reconstructed bundle is identified with Mathlib's actual pullback by `pullbackHomeomorph`,
which carries each core chart to Mathlib's pulled-back trivialization
(`pullbackHomeomorph_localTriv`, `pullback_trivializationAt_eq`), and lifts to the original core
total space via `pullbackLift`.

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

/-- Pulling back any core along a constant map gives the trivial core of the same rank. -/
@[simp] theorem pullback_const (A : FiniteRankBundleCore 𝕜 Y) (y : Y) :
    A.pullback (ContinuousMap.const X y) = trivial 𝕜 X A.rank := by
  have hbase : (fun _ : X ↦ (ContinuousMap.const X y) ⁻¹' A.core.baseSet y) =
      fun _ ↦ Set.univ :=
    funext fun _ ↦ Set.eq_univ_of_forall fun _ ↦ by
      simpa only [Set.mem_preimage, ContinuousMap.const_apply, A.indexAt_eq] using
        A.core.mem_baseSet_at y
  have hcoord : (fun (_ _ _ : X) ↦ A.core.coordChange y y y) =
      fun _ _ _ ↦ ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) :=
    funext fun _ ↦ funext fun _ ↦ funext fun _ ↦ A.coordChange_self y
  dsimp only [pullback, trivial, ContinuousMap.const_apply]
  congr

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

/-- Pulling back a cocycle morphism with bijective fibre maps preserves fibrewise bijectivity. -/
theorem bijective_fiberMap_pullbackMap {A D : FiniteRankBundleCore 𝕜 Y} (a : A ⟶ D)
    (hbij : ∀ y, Function.Bijective (a.fiberMap y)) (f : C(X, Y)) (x : X) :
    Function.Bijective ((pullbackMap a f).fiberMap x) := by
  simpa only [fiberMap_pullbackMap] using hbij (f x)

/-- Expressing a fibre operator in pulled-back charts `i` and `j` at `x` evaluates the expression
in the original charts `f i` and `f j` at `f x`. -/
@[simp] theorem inChartCoordinates_pullback (A D : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    (i j x : X) (ϕ : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)) :
    (A.pullback f).core.inChartCoordinates (D.pullback f).core i j x ϕ =
      A.core.inChartCoordinates D.core (f i) (f j) (f x) ϕ := by
  rw [inChartCoordinates_core, inChartCoordinates_core, coordChange_pullback, coordChange_pullback]

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

/-- The canonical lift from the reconstructed pullback total space to the original core total space,
covering `f` on the base and acting as the identity on preferred fibre coordinates. -/
def pullbackLift (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    (p : (A.pullback f).core.TotalSpace) : A.core.TotalSpace :=
  ⟨f p.proj, p.2⟩

/-- The base projection of `pullbackLift` applies `f` to the base projection. -/
@[simp] theorem pullbackLift_proj (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    (p : (A.pullback f).core.TotalSpace) :
    (A.pullbackLift f p).proj = f p.proj := (rfl)

/-- On preferred fibre coordinates, `pullbackLift` acts as the identity. -/
@[simp] theorem pullbackLift_snd (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    (p : (A.pullback f).core.TotalSpace) :
    (A.pullbackLift f p).2 = p.2 := (rfl)

/-- On a fibre coordinate pair `⟨x, v⟩`, `pullbackLift` shifts the base point to `f x`. -/
@[simp] theorem pullbackLift_mk (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    (x : X) (v : (A.pullback f).core.Fiber x) :
    A.pullbackLift f ⟨x, v⟩ = ⟨f x, v⟩ := (rfl)

/-- `A.pullbackLift f p` equals `⟨y, v⟩` whenever `f p.proj = y` and `p.2 = v` in preferred fibre
coordinates. -/
theorem pullbackLift_eq_mk (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    (p : (A.pullback f).core.TotalSpace) {y : Y} {v : Fin A.rank → 𝕜}
    (hy : f p.proj = y) (hv : p.2 = v) :
    A.pullbackLift f p = ⟨y, v⟩ :=
  TotalSpace.ext ((A.pullbackLift_proj f p).trans hy)
    (heq_of_eq ((A.pullbackLift_snd f p).trans hv))

/-- Along the identity map, `pullbackLift` acts as the identity on base points and preferred fibre
coordinates. -/
@[simp] theorem pullbackLift_id (A : FiniteRankBundleCore 𝕜 Y)
    (p : (A.pullback (ContinuousMap.id Y)).core.TotalSpace) :
    A.pullbackLift (ContinuousMap.id Y) p = ⟨p.proj, p.2⟩ :=
  A.pullbackLift_eq_mk (ContinuousMap.id Y) p rfl rfl

/-- The canonical lift of a composite pullback factors through the two individual lifts. -/
theorem pullbackLift_comp (A : FiniteRankBundleCore 𝕜 Z) (f : C(X, Y)) (g : C(Y, Z))
    (p : (A.pullback (g.comp f)).core.TotalSpace) :
    A.pullbackLift (g.comp f) p = A.pullbackLift g ((A.pullback g).pullbackLift f p) := (rfl)

/-- The canonical lift `pullbackLift` is continuous on the reconstructed pullback total space. -/
theorem continuous_pullbackLift (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    Continuous (A.pullbackLift f) := by
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

/-- Mathlib's `Pullback.lift f` composed with `pullbackHomeomorph` is `pullbackLift`. -/
theorem lift_pullbackHomeomorph (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    (p : (A.pullback f).core.TotalSpace) :
    Pullback.lift f (A.pullbackHomeomorph f p) = A.pullbackLift f p := by
  rcases p with ⟨x, v⟩
  exact Pullback.lift_mk (E := A.core.Fiber) (F := Fin A.rank → 𝕜) f x v

/-- A map into the reconstructed pullback total space is continuous if and only if its base
projection and its lift to `A.core.TotalSpace` are continuous. -/
theorem continuous_core_pullback_iff (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    {q : Z → (A.pullback f).core.TotalSpace} :
    Continuous q ↔
      Continuous (fun z ↦ (q z).proj) ∧ Continuous (fun z ↦ A.pullbackLift f (q z)) := by
  rw [← (A.pullbackHomeomorph f).comp_continuous_iff,
    (inducing_pullbackTotalSpaceEmbedding (Fin A.rank → 𝕜) A.core.Fiber f).continuous_iff]
  simp only [Function.comp_def, pullbackTotalSpaceEmbedding, pullbackHomeomorph_apply,
    continuous_prodMk]
  -- `pullbackTotalSpaceEmbedding` builds `⟨f (q z).proj, (q z).2⟩`, which is
  -- `A.pullbackLift f (q z)` by definition of `pullbackLift`.
  rfl

/-- The canonical lift intertwines the total-space map of a pulled-back morphism with the original
total-space map. -/
theorem pullbackLift_totalSpaceMap {A D : FiniteRankBundleCore 𝕜 Y} (a : A ⟶ D)
    (f : C(X, Y)) (p : (A.pullback f).core.TotalSpace) :
    D.pullbackLift f ((pullbackMap a f).totalSpaceMap p) =
      a.totalSpaceMap (A.pullbackLift f p) := by
  rcases p with ⟨x, v⟩
  exact (congrArg (D.pullbackLift f) ((pullbackMap a f).totalSpaceMap_mk x v)).trans
    ((congrArg (fun m ↦ (⟨f x, m v⟩ : D.core.TotalSpace)) (fiberMap_pullbackMap a f x)).trans
      (a.totalSpaceMap_mk (f x) v).symm)

/-- Mathlib's preferred trivialization of `((⇑f) *ᵖ A.core.Fiber)` at `x` is the pullback along `f`
of the core chart `A.core.localTriv (f x)`. -/
theorem pullback_trivializationAt_eq (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) (x : X) :
    trivializationAt (Fin A.rank → 𝕜) ((⇑f) *ᵖ A.core.Fiber) x =
      (A.core.localTriv (f x)).pullback f := by
  refine (FiberBundle.pullback_trivializationAt' (F := Fin A.rank → 𝕜) (E := A.core.Fiber)
    f x).trans ?_
  rw [A.trivializationAt_core]

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
  rw [lift_pullbackHomeomorph, lift_pullbackHomeomorph]
  exact pullbackLift_totalSpaceMap a f p

section WhitneySum

/-- Pulling back the first projection of a Whitney sum gives the first projection of the pulled-back
Whitney sum. -/
@[simp] theorem pullbackMap_whitneyFst (A D : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    pullbackMap (whitneyFst A D) f = whitneyFst (A.pullback f) (D.pullback f) := by
  apply hom_ext
  intro x
  rw [fiberMap_pullbackMap, fiberMap_whitneyFst]
  -- `(whitneySum A D).pullback f` is definitionally `whitneySum (A.pullback f) (D.pullback f)`
  -- (`pullback_whitneySum`), identifying the implicit source core of `fiberMap` on the right.
  exact Eq.symm (fiberMap_whitneyFst _ _ x)

/-- Pulling back the second projection of a Whitney sum gives the second projection of the
pulled-back Whitney sum. -/
@[simp] theorem pullbackMap_whitneySnd (A D : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    pullbackMap (whitneySnd A D) f = whitneySnd (A.pullback f) (D.pullback f) := by
  apply hom_ext
  intro x
  rw [fiberMap_pullbackMap, fiberMap_whitneySnd]
  -- `(whitneySum A D).pullback f` is definitionally `whitneySum (A.pullback f) (D.pullback f)`
  -- (`pullback_whitneySum`), identifying the implicit source core of `fiberMap` on the right.
  exact Eq.symm (fiberMap_whitneySnd _ _ x)

/-- Pulling back the first inclusion into a Whitney sum gives the first inclusion into the
pulled-back Whitney sum. -/
@[simp] theorem pullbackMap_whitneyInl (A D : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    pullbackMap (whitneyInl A D) f = whitneyInl (A.pullback f) (D.pullback f) := by
  apply hom_ext
  intro x
  rw [fiberMap_pullbackMap, fiberMap_whitneyInl]
  -- `(whitneySum A D).pullback f` is definitionally `whitneySum (A.pullback f) (D.pullback f)`
  -- (`pullback_whitneySum`), identifying the implicit target core of `fiberMap` on the right.
  exact Eq.symm (fiberMap_whitneyInl _ _ x)

/-- Pulling back the second inclusion into a Whitney sum gives the second inclusion into the
pulled-back Whitney sum. -/
@[simp] theorem pullbackMap_whitneyInr (A D : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    pullbackMap (whitneyInr A D) f = whitneyInr (A.pullback f) (D.pullback f) := by
  apply hom_ext
  intro x
  rw [fiberMap_pullbackMap, fiberMap_whitneyInr]
  -- `(whitneySum A D).pullback f` is definitionally `whitneySum (A.pullback f) (D.pullback f)`
  -- (`pullback_whitneySum`), identifying the implicit target core of `fiberMap` on the right.
  exact Eq.symm (fiberMap_whitneyInr _ _ x)

/-- Pulling back commutes with pairing into a Whitney sum. -/
@[simp] theorem pullbackMap_whitneyLift {A D E : FiniteRankBundleCore 𝕜 Y}
    (a : E ⟶ A) (b : E ⟶ D) (f : C(X, Y)) :
    pullbackMap (whitneyLift a b) f = whitneyLift (pullbackMap a f) (pullbackMap b f) := by
  simp only [whitneyLift_def, pullbackMap_add, pullbackMap_comp, pullbackMap_whitneyInl,
    pullbackMap_whitneyInr]
  -- `(whitneySum A D).pullback f` and `whitneySum (A.pullback f) (D.pullback f)` coincide
  -- definitionally, as recorded by `pullback_whitneySum`.
  rfl

/-- Pulling back commutes with copairing out of a Whitney sum. -/
@[simp] theorem pullbackMap_whitneyDesc {A D E : FiniteRankBundleCore 𝕜 Y}
    (a : A ⟶ E) (b : D ⟶ E) (f : C(X, Y)) :
    pullbackMap (whitneyDesc a b) f = whitneyDesc (pullbackMap a f) (pullbackMap b f) := by
  simp only [whitneyDesc_def, pullbackMap_add, pullbackMap_comp, pullbackMap_whitneyFst,
    pullbackMap_whitneySnd]
  -- `(whitneySum A D).pullback f` and `whitneySum (A.pullback f) (D.pullback f)` coincide
  -- definitionally, as recorded by `pullback_whitneySum`.
  rfl

/-- Pulling back commutes with direct sums of bundle morphisms. -/
@[simp] theorem pullbackMap_whitneyMap {A A' D D' : FiniteRankBundleCore 𝕜 Y}
    (a : A ⟶ A') (b : D ⟶ D') (f : C(X, Y)) :
    pullbackMap (whitneyMap a b) f = whitneyMap (pullbackMap a f) (pullbackMap b f) := by
  simp only [whitneyMap_def, pullbackMap_whitneyLift, pullbackMap_comp, pullbackMap_whitneyFst,
    pullbackMap_whitneySnd]
  -- `(whitneySum A D).pullback f` and `whitneySum (A.pullback f) (D.pullback f)` coincide
  -- definitionally, as recorded by `pullback_whitneySum`.
  rfl

/-- On every fibre, `whitneySumFiberEquiv` on a pulled-back Whitney sum agrees with
`whitneySumFiberEquiv` at the image base point. -/
@[simp] theorem whitneySumFiberEquiv_pullback_apply (A D : FiniteRankBundleCore 𝕜 Y)
    (f : C(X, Y)) (x : X) (v : (whitneySum (A.pullback f) (D.pullback f)).core.Fiber x) :
    whitneySumFiberEquiv (A.pullback f) (D.pullback f) x v = whitneySumFiberEquiv A D (f x) v := by
  rw [whitneySumFiberEquiv_apply]
  -- Both fibres are `Fin (A.rank + D.rank) → 𝕜` (`rank_pullback`), matching
  -- `whitneySumFiberEquiv_apply` on the right.
  exact Eq.symm (whitneySumFiberEquiv_apply _ _ (f x) v)

end WhitneySum

/-- Over a complete scalar field, `(ofBundle 𝕜 n E).pullback f` is canonically isomorphic to
`ofBundle 𝕜 n ((⇑f) *ᵖ E)`. -/
noncomputable def pullbackOfBundleIso [CompleteSpace 𝕜] {n : ℕ} (E : Y → Type*)
    [∀ y, AddCommMonoid (E y)] [∀ y, Module 𝕜 (E y)] [∀ y, TopologicalSpace (E y)]
    [TopologicalSpace (TotalSpace (Fin n → 𝕜) E)] [FiberBundle (Fin n → 𝕜) E]
    [VectorBundle 𝕜 (Fin n → 𝕜) E] (f : C(X, Y)) :
    (ofBundle 𝕜 n E).pullback f ≅ ofBundle 𝕜 n ((⇑f) *ᵖ E) :=
  let eE := pointIndexedCoreFiberEquiv 𝕜 (Fin n → 𝕜) E
  have hg : Continuous fun p : ((ofBundle 𝕜 n E).pullback f).core.TotalSpace ↦
      (⟨p.proj, eE (f p.proj) p.2⟩ : TotalSpace (Fin n → 𝕜) ((⇑f) *ᵖ E)) := by
    rw [(inducing_pullbackTotalSpaceEmbedding (Fin n → 𝕜) E f).continuous_iff]
    exact ((ofBundle 𝕜 n E).pullback f).core.continuous_proj.prodMk
      (((pointIndexedCoreHomeomorph 𝕜 (Fin n → 𝕜) E).continuous.comp
        (continuous_pullbackLift (ofBundle 𝕜 n E) f)).congr fun ⟨x, v⟩ ↦
          pointIndexedCoreHomeomorph_apply 𝕜 (Fin n → 𝕜) E ⟨f x, v⟩)
  isoOfContinuousEquiv (fun x ↦ (eE (f x)).trans
      (pointIndexedCoreFiberEquiv 𝕜 (Fin n → 𝕜) ((⇑f) *ᵖ E) x).symm)
    (((pointIndexedCoreHomeomorph 𝕜 (Fin n → 𝕜) ((⇑f) *ᵖ E)).symm.continuous.comp hg).congr
      fun ⟨x, v⟩ ↦ pointIndexedCoreHomeomorph_symm_apply 𝕜 (Fin n → 𝕜) ((⇑f) *ᵖ E) ⟨x, eE (f x) v⟩)

@[simp] theorem fiberMap_pullbackOfBundleIso_hom [CompleteSpace 𝕜] {n : ℕ} (E : Y → Type*)
    [∀ y, AddCommMonoid (E y)] [∀ y, Module 𝕜 (E y)] [∀ y, TopologicalSpace (E y)]
    [TopologicalSpace (TotalSpace (Fin n → 𝕜) E)] [FiberBundle (Fin n → 𝕜) E]
    [VectorBundle 𝕜 (Fin n → 𝕜) E] (f : C(X, Y)) (x : X) :
    (pullbackOfBundleIso E f).hom.fiberMap x = ContinuousLinearEquiv.toContinuousLinearMap
      ((pointIndexedCoreFiberEquiv 𝕜 (Fin n → 𝕜) E (f x)).trans
        (pointIndexedCoreFiberEquiv 𝕜 (Fin n → 𝕜) ((⇑f) *ᵖ E) x).symm) :=
  fiberMap_isoOfContinuousEquiv_hom _ _ x

@[simp] theorem fiberMap_pullbackOfBundleIso_inv [CompleteSpace 𝕜] {n : ℕ} (E : Y → Type*)
    [∀ y, AddCommMonoid (E y)] [∀ y, Module 𝕜 (E y)] [∀ y, TopologicalSpace (E y)]
    [TopologicalSpace (TotalSpace (Fin n → 𝕜) E)] [FiberBundle (Fin n → 𝕜) E]
    [VectorBundle 𝕜 (Fin n → 𝕜) E] (f : C(X, Y)) (x : X) :
    (pullbackOfBundleIso E f).inv.fiberMap x = ContinuousLinearEquiv.toContinuousLinearMap
      ((pointIndexedCoreFiberEquiv 𝕜 (Fin n → 𝕜) E (f x)).trans
        (pointIndexedCoreFiberEquiv 𝕜 (Fin n → 𝕜) ((⇑f) *ᵖ E) x).symm).symm :=
  fiberMap_isoOfContinuousEquiv_inv _ _ x

/-- Pullback of isomorphism classes of rank-`n` vector-bundle cores along `f : C(X, Y)`. -/
def pullbackRankClass (f : C(X, Y)) (n : ℕ) :
    Quotient ((CategoryTheory.isIsomorphicSetoid (FiniteRankBundleCore 𝕜 Y)).comap
        (Subtype.val : {A : FiniteRankBundleCore 𝕜 Y // A.rank = n} → _)) →
      Quotient ((CategoryTheory.isIsomorphicSetoid (FiniteRankBundleCore 𝕜 X)).comap
        (Subtype.val : {A : FiniteRankBundleCore 𝕜 X // A.rank = n} → _)) :=
  Quotient.map (fun A ↦ ⟨A.1.pullback f, A.2⟩) fun _ _ ⟨α⟩ ↦ ⟨(pullbackFunctor f).mapIso α⟩

@[simp] theorem pullbackRankClass_mk (f : C(X, Y)) (n : ℕ)
    (A : {A : FiniteRankBundleCore 𝕜 Y // A.rank = n}) :
    pullbackRankClass f n (Quotient.mk _ A) = Quotient.mk _ ⟨A.1.pullback f, A.2⟩ := (rfl)

@[simp] theorem pullbackRankClass_id (n : ℕ)
    (c : Quotient ((CategoryTheory.isIsomorphicSetoid (FiniteRankBundleCore 𝕜 Y)).comap
      (Subtype.val : {A : FiniteRankBundleCore 𝕜 Y // A.rank = n} → _))) :
    pullbackRankClass (ContinuousMap.id Y) n c = c :=
  Quotient.inductionOn c fun A ↦ congrArg (Quotient.mk _) (Subtype.ext (pullback_id A.1))

@[simp] theorem pullbackRankClass_comp (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ)
    (c : Quotient ((CategoryTheory.isIsomorphicSetoid (FiniteRankBundleCore 𝕜 Z)).comap
      (Subtype.val : {A : FiniteRankBundleCore 𝕜 Z // A.rank = n} → _))) :
    pullbackRankClass f n (pullbackRankClass g n c) = pullbackRankClass (g.comp f) n c :=
  Quotient.inductionOn c fun A ↦ congrArg (Quotient.mk _) (Subtype.ext (pullback_comp A.1 f g))

end TauCeti.FiniteRankBundleCore
