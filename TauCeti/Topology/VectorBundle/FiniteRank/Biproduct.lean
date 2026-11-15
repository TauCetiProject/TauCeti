/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Basic
public import TauCeti.Topology.Algebra.Module.Equiv.Fin
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Topology.VectorBundle.Constructions

/-!
# Whitney sums of finite-rank bundle cores

The Whitney sum of two point-indexed cores uses the intersections of their charts
and block-diagonal transition maps, transported by `TauCeti.splitCoords` to the
standard model `Fin (A.rank + D.rank) → 𝕜`. Its projections and inclusions are
continuous coordinate morphisms, hence continuous fibrewise linear maps of the
reconstructed Mathlib bundles.

`whitneyBiconeIsBilimit` proves the product and coproduct universal properties of
this geometric sum, with concrete pairing (`whitneyLift`), copairing (`whitneyDesc`),
functorial action on pairs of morphisms and isomorphisms (`whitneyMap`,
`whitneyMapIso`), and symmetry, associativity, and rank-zero unit isomorphisms
(`whitneyCommIso`, `whitneyAssocIso`, `whitneyZeroLeftIso`, `whitneyZeroRightIso`).
Thus `FiniteRankBundleCore` has binary biproducts, including zero-rank bundles and
bundles over the empty base.

`whitneySumTotalSpaceHomeomorph` identifies the reconstructed total space of
`whitneySum A D` with the total space of Mathlib's native direct-sum bundle
`A.core.Fiber ×ᵇ D.core.Fiber`, over the identity of the base and by
`whitneySumFiberEquiv` (`TauCeti.splitCoords`) on each fibre, intertwining the
projections, inclusions, and direct sums of bundle maps. The base is arbitrary, and
the scalar field need not be complete.

The construction uses Mathlib's coordinate cores, its direct-sum vector bundle
`Bundle.Prod`, and its preadditive criterion
`CategoryTheory.Limits.isBinaryBilimitOfTotal`.
-/

public section

open Bundle CategoryTheory CategoryTheory.Limits VectorBundleCore Set

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]

/-- The Whitney sum, with concatenated finite coordinates and intersected charts. -/
-- Expose the rank projection so the dependent model reduces to the concatenated coordinates.
@[expose]
def whitneySum (A D : FiniteRankBundleCore 𝕜 B) : FiniteRankBundleCore 𝕜 B where
  rank := A.rank + D.rank
  core :=
    { baseSet := fun i => A.core.baseSet i ∩ D.core.baseSet i
      isOpen_baseSet := fun i => (A.core.isOpen_baseSet i).inter (D.core.isOpen_baseSet i)
      indexAt := id
      mem_baseSet_at := fun x => by
        simpa only [mem_inter_iff, id_eq, A.indexAt_eq, D.indexAt_eq] using
          And.intro (A.core.mem_baseSet_at x) (D.core.mem_baseSet_at x)
      coordChange := fun i j x =>
        (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm.toContinuousLinearMap.comp
          (((A.core.coordChange i j x).prodMap (D.core.coordChange i j x)).comp
            (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap)
      coordChange_self := fun i x hx v => by
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
          ContinuousLinearMap.coe_prodMap', Prod.map_apply', A.core.coordChange_self i x hx.1,
          D.core.coordChange_self i x hx.2, Prod.mk.eta,
          ContinuousLinearEquiv.symm_apply_apply]
      continuousOn_coordChange := fun i j => by
        have hA : ContinuousOn (A.core.coordChange i j)
            ((A.core.baseSet i ∩ D.core.baseSet i) ∩ (A.core.baseSet j ∩ D.core.baseSet j)) :=
          (A.core.continuousOn_coordChange i j).mono
          (fun _ h => ⟨h.1.1, h.2.1⟩)
        have hD : ContinuousOn (D.core.coordChange i j)
            ((A.core.baseSet i ∩ D.core.baseSet i) ∩ (A.core.baseSet j ∩ D.core.baseSet j)) :=
          (D.core.continuousOn_coordChange i j).mono
          (fun _ h => ⟨h.1.2, h.2.2⟩)
        exact continuousOn_iff_continuous_domRestrict.2
          (((hA.domRestrict.prod_mapL 𝕜 hD.domRestrict).clm_comp_const
            (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap).const_clm_comp
              (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm.toContinuousLinearMap)
      coordChange_comp := fun i j k x hx v => by
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.coe_prodMap', Prod.map_apply']
        rw [A.core.coordChange_comp i j k x ⟨⟨hx.1.1.1, hx.1.2.1⟩, hx.2.1⟩,
          D.core.coordChange_comp i j k x ⟨⟨hx.1.1.2, hx.1.2.2⟩, hx.2.2⟩] }
  indexAt_eq := fun _ => rfl

@[simp] theorem rank_whitneySum (A D : FiniteRankBundleCore 𝕜 B) :
    (whitneySum A D).rank = A.rank + D.rank := (rfl)

@[simp] theorem localTriv_baseSet_whitneySum (A D : FiniteRankBundleCore 𝕜 B) (i : B) :
    ((whitneySum A D).core.localTriv i).baseSet = A.core.baseSet i ∩ D.core.baseSet i := (rfl)

/-- In block coordinates the Whitney-sum transition is the pair of original transitions. -/
theorem splitCoords_coordChange_whitneySum (A D : FiniteRankBundleCore 𝕜 B)
    (i j x : B) (v : Fin (A.rank + D.rank) → 𝕜) :
    splitCoords (𝕜 := 𝕜) A.rank D.rank ((whitneySum A D).core.coordChange i j x v) =
      (A.core.coordChange i j x (splitCoords (𝕜 := 𝕜) A.rank D.rank v).1,
        D.core.coordChange i j x (splitCoords (𝕜 := 𝕜) A.rank D.rank v).2) :=
  (splitCoords (𝕜 := 𝕜) A.rank D.rank).apply_symm_apply _

/-- Applying the Whitney-sum transition to a block-split vector applies the two summand transitions
to the blocks. -/
theorem coordChange_whitneySum_splitCoords_symm (A D : FiniteRankBundleCore 𝕜 B)
    (i j x : B) (u : Fin A.rank → 𝕜) (w : Fin D.rank → 𝕜) :
    (whitneySum A D).core.coordChange i j x
      ((splitCoords (𝕜 := 𝕜) A.rank D.rank).symm (u, w)) =
      (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm
        (A.core.coordChange i j x u, D.core.coordChange i j x w) := by
  apply (splitCoords (𝕜 := 𝕜) A.rank D.rank).injective
  rw [splitCoords_coordChange_whitneySum]
  simp only [ContinuousLinearEquiv.apply_symm_apply]

/-- Projection of the Whitney sum onto its first bundle. -/
def whitneyFst (A D : FiniteRankBundleCore 𝕜 B) : whitneySum A D ⟶ A where
  operator i j :=
    ⟨fun x => (A.core.coordChange i j x.1).comp
      ((ContinuousLinearMap.fst 𝕜 _ _).comp
        (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap),
      (((A.core.continuousOn_coordChange i j).mono
        (fun x (h : x ∈ (A.core.baseSet i ∩ D.core.baseSet i) ∩ A.core.baseSet j) =>
          ⟨h.1.1, h.2⟩)).domRestrict.clm_comp_const _)⟩
  compatible i i' j j' x hi hi' hj hj' v := by
    -- Normalize the source model so rewriting does not need to unfold the rank projection.
    change Fin (A.rank + D.rank) → 𝕜 at v
    change A.core.coordChange j j' x
      (A.core.coordChange i j x (splitCoords (𝕜 := 𝕜) A.rank D.rank v).1) =
        A.core.coordChange i' j' x
          (splitCoords (𝕜 := 𝕜) A.rank D.rank
            ((whitneySum A D).core.coordChange i i' x v)).1
    rw [splitCoords_coordChange_whitneySum,
      A.core.coordChange_comp i j j' x ⟨⟨hi.1, hj⟩, hj'⟩,
      A.core.coordChange_comp i i' j' x ⟨⟨hi.1, hi'.1⟩, hj'⟩]

/-- Projection of the Whitney sum onto its second bundle. -/
def whitneySnd (A D : FiniteRankBundleCore 𝕜 B) : whitneySum A D ⟶ D where
  operator i j :=
    ⟨fun x => (D.core.coordChange i j x.1).comp
      ((ContinuousLinearMap.snd 𝕜 _ _).comp
        (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap),
      (((D.core.continuousOn_coordChange i j).mono
        (fun x (h : x ∈ (A.core.baseSet i ∩ D.core.baseSet i) ∩ D.core.baseSet j) =>
          ⟨h.1.2, h.2⟩)).domRestrict.clm_comp_const _)⟩
  compatible i i' j j' x hi hi' hj hj' v := by
    -- Normalize the source model so rewriting does not need to unfold the rank projection.
    change Fin (A.rank + D.rank) → 𝕜 at v
    change D.core.coordChange j j' x
      (D.core.coordChange i j x (splitCoords (𝕜 := 𝕜) A.rank D.rank v).2) =
        D.core.coordChange i' j' x
          (splitCoords (𝕜 := 𝕜) A.rank D.rank
            ((whitneySum A D).core.coordChange i i' x v)).2
    rw [splitCoords_coordChange_whitneySum,
      D.core.coordChange_comp i j j' x ⟨⟨hi.2, hj⟩, hj'⟩,
      D.core.coordChange_comp i i' j' x ⟨⟨hi.2, hi'.2⟩, hj'⟩]

/-- Inclusion of the first bundle into the Whitney sum. -/
def whitneyInl (A D : FiniteRankBundleCore 𝕜 B) : A ⟶ whitneySum A D where
  operator i j :=
    ⟨fun x => (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.inl 𝕜 _ _).comp (A.core.coordChange i j x.1)),
      ((((A.core.continuousOn_coordChange i j).mono
        (fun x (h : x ∈ A.core.baseSet i ∩ (A.core.baseSet j ∩ D.core.baseSet j)) =>
          ⟨h.1, h.2.1⟩)).domRestrict.const_clm_comp _).const_clm_comp _)⟩
  compatible i i' j j' x hi hi' hj hj' v := by
    -- Normalize the dependent model types before applying the block-coordinate equation.
    change (whitneySum A D).core.coordChange j j' x
      ((splitCoords (𝕜 := 𝕜) A.rank D.rank).symm (A.core.coordChange i j x v, 0)) =
        (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm
          (A.core.coordChange i' j' x (A.core.coordChange i i' x v), 0)
    apply (splitCoords (𝕜 := 𝕜) A.rank D.rank).injective
    simp only [splitCoords_coordChange_whitneySum,
      ContinuousLinearEquiv.apply_symm_apply, map_zero]
    rw [A.core.coordChange_comp i j j' x ⟨⟨hi, hj.1⟩, hj'.1⟩,
      A.core.coordChange_comp i i' j' x ⟨⟨hi, hi'⟩, hj'.1⟩]

/-- Inclusion of the second bundle into the Whitney sum. -/
def whitneyInr (A D : FiniteRankBundleCore 𝕜 B) : D ⟶ whitneySum A D where
  operator i j :=
    ⟨fun x => (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.inr 𝕜 _ _).comp (D.core.coordChange i j x.1)),
      ((((D.core.continuousOn_coordChange i j).mono
        (fun x (h : x ∈ D.core.baseSet i ∩ (A.core.baseSet j ∩ D.core.baseSet j)) =>
          ⟨h.1, h.2.2⟩)).domRestrict.const_clm_comp _).const_clm_comp _)⟩
  compatible i i' j j' x hi hi' hj hj' v := by
    -- Normalize the dependent model types before applying the block-coordinate equation.
    change (whitneySum A D).core.coordChange j j' x
      ((splitCoords (𝕜 := 𝕜) A.rank D.rank).symm (0, D.core.coordChange i j x v)) =
        (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm
          (0, D.core.coordChange i' j' x (D.core.coordChange i i' x v))
    apply (splitCoords (𝕜 := 𝕜) A.rank D.rank).injective
    simp only [splitCoords_coordChange_whitneySum,
      ContinuousLinearEquiv.apply_symm_apply, map_zero]
    rw [D.core.coordChange_comp i j j' x ⟨⟨hi, hj.2⟩, hj'.2⟩,
      D.core.coordChange_comp i i' j' x ⟨⟨hi, hi'⟩, hj'.2⟩]

-- The characteristic equation identifies each preferred-chart operator with a map between
-- standard models; the remaining calculation uses the shared self-transition equation.
/-- The first projection is the first coordinate block in every fibre. -/
@[simp] theorem fiberMap_whitneyFst (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (whitneyFst A D).fiberMap x =
      (ContinuousLinearMap.fst 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜)).comp
        (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap := by
  calc
    _ = (A.core.coordChange ((whitneySum A D).core.indexAt x)
        (A.core.indexAt x) x).comp
        ((ContinuousLinearMap.fst 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜)).comp
          (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap) :=
      CoordinateHom.fiberMap_def _ x
    _ = _ := by
      rw [(whitneySum A D).indexAt_eq, A.indexAt_eq, coordChange_self,
        ContinuousLinearMap.id_comp]

/-- The second projection is the second coordinate block in every fibre. -/
@[simp] theorem fiberMap_whitneySnd (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (whitneySnd A D).fiberMap x =
      (ContinuousLinearMap.snd 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜)).comp
        (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap := by
  calc
    _ = (D.core.coordChange ((whitneySum A D).core.indexAt x)
        (D.core.indexAt x) x).comp
        ((ContinuousLinearMap.snd 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜)).comp
          (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap) :=
      CoordinateHom.fiberMap_def _ x
    _ = _ := by
      rw [(whitneySum A D).indexAt_eq, D.indexAt_eq, coordChange_self,
        ContinuousLinearMap.id_comp]

/-- The first inclusion appends a zero block in every fibre. -/
@[simp] theorem fiberMap_whitneyInl (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (whitneyInl A D).fiberMap x =
      (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜)) := by
  calc
    _ = (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.inl 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜)).comp
          (A.core.coordChange (A.core.indexAt x)
            ((whitneySum A D).core.indexAt x) x)) := CoordinateHom.fiberMap_def _ x
    _ = _ := by
      rw [(whitneySum A D).indexAt_eq, A.indexAt_eq, coordChange_self,
        ContinuousLinearMap.comp_id]

/-- The second inclusion prepends a zero block in every fibre. -/
@[simp] theorem fiberMap_whitneyInr (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (whitneyInr A D).fiberMap x =
      (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inr 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜)) := by
  calc
    _ = (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.inr 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜)).comp
          (D.core.coordChange (D.core.indexAt x)
            ((whitneySum A D).core.indexAt x) x)) := CoordinateHom.fiberMap_def _ x
    _ = _ := by
      rw [(whitneySum A D).indexAt_eq, D.indexAt_eq, coordChange_self,
        ContinuousLinearMap.comp_id]

@[reassoc (attr := simp)] theorem whitneyInl_fst (A D : FiniteRankBundleCore 𝕜 B) :
    whitneyInl A D ≫ whitneyFst A D = 𝟙 A := by
  apply hom_ext
  intro x
  -- Work in the standard model so simplification does not unfold dependent fibre instances.
  let e := splitCoords (𝕜 := 𝕜) (M := 𝕜) A.rank D.rank
  have h : ((ContinuousLinearMap.fst 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜)).comp
        e.toContinuousLinearMap).comp
      (e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl 𝕜 _ _)) =
        ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) := by
    ext v i
    simp
  simp only [fiberMap_comp, fiberMap_whitneyFst, fiberMap_whitneyInl, fiberMap_id]
  exact h

@[reassoc (attr := simp)] theorem whitneyInl_snd (A D : FiniteRankBundleCore 𝕜 B) :
    whitneyInl A D ≫ whitneySnd A D = 0 := by
  apply hom_ext
  intro x
  -- Work in the standard model so simplification does not unfold dependent fibre instances.
  let e := splitCoords (𝕜 := 𝕜) (M := 𝕜) A.rank D.rank
  have h : ((ContinuousLinearMap.snd 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜)).comp
        e.toContinuousLinearMap).comp
      (e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl 𝕜 _ _)) =
        (0 : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)) := by
    ext v i
    simp
  simp only [fiberMap_comp, fiberMap_whitneySnd, fiberMap_whitneyInl, CoordinateHom.fiberMap_zero]
  exact h

@[reassoc (attr := simp)] theorem whitneyInr_fst (A D : FiniteRankBundleCore 𝕜 B) :
    whitneyInr A D ≫ whitneyFst A D = 0 := by
  apply hom_ext
  intro x
  -- Work in the standard model so simplification does not unfold dependent fibre instances.
  let e := splitCoords (𝕜 := 𝕜) (M := 𝕜) A.rank D.rank
  have h : ((ContinuousLinearMap.fst 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜)).comp
        e.toContinuousLinearMap).comp
      (e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr 𝕜 _ _)) =
        (0 : (Fin D.rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜)) := by
    ext v i
    simp
  simp only [fiberMap_comp, fiberMap_whitneyFst, fiberMap_whitneyInr, CoordinateHom.fiberMap_zero]
  exact h

@[reassoc (attr := simp)] theorem whitneyInr_snd (A D : FiniteRankBundleCore 𝕜 B) :
    whitneyInr A D ≫ whitneySnd A D = 𝟙 D := by
  apply hom_ext
  intro x
  -- Work in the standard model so simplification does not unfold dependent fibre instances.
  let e := splitCoords (𝕜 := 𝕜) (M := 𝕜) A.rank D.rank
  have h : ((ContinuousLinearMap.snd 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜)).comp
        e.toContinuousLinearMap).comp
      (e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr 𝕜 _ _)) =
        ContinuousLinearMap.id 𝕜 (Fin D.rank → 𝕜) := by
    ext v i
    simp
  simp only [fiberMap_comp, fiberMap_whitneySnd, fiberMap_whitneyInr, fiberMap_id]
  exact h

/-- The Whitney sum with its four canonical bundle maps. -/
-- Expose the point projection so the types of the four legs reduce to the Whitney sum.
@[expose]
def whitneyBicone (A D : FiniteRankBundleCore 𝕜 B) : BinaryBicone A D where
  pt := whitneySum A D
  fst := whitneyFst A D
  snd := whitneySnd A D
  inl := whitneyInl A D
  inr := whitneyInr A D
  inl_fst := whitneyInl_fst A D
  inl_snd := whitneyInl_snd A D
  inr_fst := whitneyInr_fst A D
  inr_snd := whitneyInr_snd A D

@[simp] theorem whitneyBicone_pt (A D : FiniteRankBundleCore 𝕜 B) :
    (whitneyBicone A D).pt = whitneySum A D := (rfl)

@[simp] theorem whitneyBicone_fst (A D : FiniteRankBundleCore 𝕜 B) :
    (whitneyBicone A D).fst = whitneyFst A D := (rfl)

@[simp] theorem whitneyBicone_snd (A D : FiniteRankBundleCore 𝕜 B) :
    (whitneyBicone A D).snd = whitneySnd A D := (rfl)

@[simp] theorem whitneyBicone_inl (A D : FiniteRankBundleCore 𝕜 B) :
    (whitneyBicone A D).inl = whitneyInl A D := (rfl)

@[simp] theorem whitneyBicone_inr (A D : FiniteRankBundleCore 𝕜 B) :
    (whitneyBicone A D).inr = whitneyInr A D := (rfl)

/-- The two coordinate-block projections and inclusions resolve the identity. -/
@[simp] theorem whitney_total (A D : FiniteRankBundleCore 𝕜 B) :
    whitneyFst A D ≫ whitneyInl A D + whitneySnd A D ≫ whitneyInr A D =
      𝟙 (whitneySum A D) := by
  apply hom_ext
  intro x
  -- Work in the standard model so simplification does not unfold dependent fibre instances.
  let e := splitCoords (𝕜 := 𝕜) (M := 𝕜) A.rank D.rank
  have h : (e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl 𝕜 _ _)).comp
        ((ContinuousLinearMap.fst 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜)).comp
          e.toContinuousLinearMap) +
      (e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr 𝕜 _ _)).comp
        ((ContinuousLinearMap.snd 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜)).comp
          e.toContinuousLinearMap) =
      ContinuousLinearMap.id 𝕜 (Fin (A.rank + D.rank) → 𝕜) := by
    apply ContinuousLinearMap.ext
    intro v
    simp [← map_add]
  simp only [fiberMap_add, fiberMap_comp, fiberMap_id, fiberMap_whitneyFst,
    fiberMap_whitneySnd, fiberMap_whitneyInl, fiberMap_whitneyInr]
  exact h

/-- The geometric Whitney sum is simultaneously a product and a coproduct. -/
def whitneyBiconeIsBilimit (A D : FiniteRankBundleCore 𝕜 B) :
    (whitneyBicone A D).IsBilimit :=
  isBinaryBilimitOfTotal _ (whitney_total A D)

/-- Whitney sums provide binary biproducts of finite-rank bundle cores. -/
instance : HasBinaryBiproducts (FiniteRankBundleCore 𝕜 B) where
  has_binary_biproduct A D := ⟨⟨whitneyBicone A D, whitneyBiconeIsBilimit A D⟩⟩

section UniversalProperty

variable {A A' A'' D D' D'' C E : FiniteRankBundleCore 𝕜 B}

/-- Pair two bundle morphisms with common source into the concrete Whitney sum. -/
def whitneyLift (f : E ⟶ A) (g : E ⟶ D) : E ⟶ whitneySum A D :=
  f ≫ whitneyInl A D + g ≫ whitneyInr A D

theorem whitneyLift_def (f : E ⟶ A) (g : E ⟶ D) :
    whitneyLift f g = f ≫ whitneyInl A D + g ≫ whitneyInr A D := (rfl)

@[reassoc (attr := simp)]
theorem whitneyLift_fst (f : E ⟶ A) (g : E ⟶ D) :
    whitneyLift f g ≫ whitneyFst A D = f := by
  simp [whitneyLift, Preadditive.add_comp]

@[reassoc (attr := simp)]
theorem whitneyLift_snd (f : E ⟶ A) (g : E ⟶ D) :
    whitneyLift f g ≫ whitneySnd A D = g := by
  simp [whitneyLift, Preadditive.add_comp]

/-- Every morphism into a Whitney sum is the pairing of its two projections. -/
theorem eq_whitneyLift (h : E ⟶ whitneySum A D) :
    h = whitneyLift (h ≫ whitneyFst A D) (h ≫ whitneySnd A D) := by
  calc
    h = h ≫ 𝟙 (whitneySum A D) := (Category.comp_id h).symm
    _ = h ≫ (whitneyFst A D ≫ whitneyInl A D + whitneySnd A D ≫ whitneyInr A D) := by
      rw [whitney_total]
    _ = whitneyLift (h ≫ whitneyFst A D) (h ≫ whitneySnd A D) := by
      simp only [whitneyLift, Preadditive.comp_add, Category.assoc]

/-- Morphisms into a Whitney sum are determined by their two projections. -/
theorem whitneySum_hom_ext {h₁ h₂ : E ⟶ whitneySum A D}
    (hfst : h₁ ≫ whitneyFst A D = h₂ ≫ whitneyFst A D)
    (hsnd : h₁ ≫ whitneySnd A D = h₂ ≫ whitneySnd A D) : h₁ = h₂ := by
  rw [eq_whitneyLift h₁, eq_whitneyLift h₂, hfst, hsnd]

@[reassoc]
theorem comp_whitneyLift (h : C ⟶ E) (f : E ⟶ A) (g : E ⟶ D) :
    h ≫ whitneyLift f g = whitneyLift (h ≫ f) (h ≫ g) := by
  simp only [whitneyLift, Preadditive.comp_add, Category.assoc]

@[simp]
theorem whitneyLift_fst_snd (A D : FiniteRankBundleCore 𝕜 B) :
    whitneyLift (whitneyFst A D) (whitneySnd A D) = 𝟙 (whitneySum A D) :=
  whitney_total A D

@[simp]
theorem fiberMap_whitneyLift (f : E ⟶ A) (g : E ⟶ D) (x : B) :
    (whitneyLift f g).fiberMap x =
      (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm.toContinuousLinearMap.comp
        ((f.fiberMap x).prod (g.fiberMap x)) := by
  -- Work in the standard model so simplification does not unfold dependent fibre instances.
  let e := splitCoords (𝕜 := 𝕜) (M := 𝕜) A.rank D.rank
  have h : (e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl 𝕜 _ _)).comp (f.fiberMap x) +
      (e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr 𝕜 _ _)).comp (g.fiberMap x) =
      e.symm.toContinuousLinearMap.comp ((f.fiberMap x).prod (g.fiberMap x)) := by
    apply ContinuousLinearMap.ext
    intro v
    simp [← map_add]
  simp only [whitneyLift, fiberMap_add, fiberMap_comp, fiberMap_whitneyInl, fiberMap_whitneyInr]
  exact h

theorem splitCoords_fiberMap_whitneyLift (f : E ⟶ A) (g : E ⟶ D) (x : B) (v : Fin E.rank → 𝕜) :
    splitCoords (𝕜 := 𝕜) A.rank D.rank ((whitneyLift f g).fiberMap x v) =
      (f.fiberMap x v, g.fiberMap x v) := by
  rw [DFunLike.congr_fun (fiberMap_whitneyLift f g x) v]
  exact (splitCoords (𝕜 := 𝕜) A.rank D.rank).apply_symm_apply (f.fiberMap x v, g.fiberMap x v)

/-- Copair two bundle morphisms with common target out of the concrete Whitney sum. -/
def whitneyDesc (f : A ⟶ E) (g : D ⟶ E) : whitneySum A D ⟶ E :=
  whitneyFst A D ≫ f + whitneySnd A D ≫ g

theorem whitneyDesc_def (f : A ⟶ E) (g : D ⟶ E) :
    whitneyDesc f g = whitneyFst A D ≫ f + whitneySnd A D ≫ g := (rfl)

@[reassoc (attr := simp)]
theorem whitneyInl_desc (f : A ⟶ E) (g : D ⟶ E) :
    whitneyInl A D ≫ whitneyDesc f g = f := by
  simp [whitneyDesc, Preadditive.comp_add]

@[reassoc (attr := simp)]
theorem whitneyInr_desc (f : A ⟶ E) (g : D ⟶ E) :
    whitneyInr A D ≫ whitneyDesc f g = g := by
  simp [whitneyDesc, Preadditive.comp_add]

@[reassoc (attr := simp)]
theorem whitneyLift_desc (f : E ⟶ A) (g : E ⟶ D) (h : A ⟶ C) (k : D ⟶ C) :
    whitneyLift f g ≫ whitneyDesc h k = f ≫ h + g ≫ k := by
  simp [whitneyLift, whitneyDesc, Preadditive.add_comp, Preadditive.comp_add]

/-- Every morphism out of a Whitney sum is the copairing of its two restrictions. -/
theorem eq_whitneyDesc (h : whitneySum A D ⟶ E) :
    h = whitneyDesc (whitneyInl A D ≫ h) (whitneyInr A D ≫ h) := by
  calc
    h = 𝟙 (whitneySum A D) ≫ h := (Category.id_comp h).symm
    _ = (whitneyFst A D ≫ whitneyInl A D + whitneySnd A D ≫ whitneyInr A D) ≫ h := by
      rw [whitney_total]
    _ = whitneyDesc (whitneyInl A D ≫ h) (whitneyInr A D ≫ h) := by
      simp only [whitneyDesc, Preadditive.add_comp, Category.assoc]

/-- Morphisms out of a Whitney sum are determined by their restrictions to the two summands. -/
theorem whitneySum_hom_ext' {h₁ h₂ : whitneySum A D ⟶ E}
    (hinl : whitneyInl A D ≫ h₁ = whitneyInl A D ≫ h₂)
    (hinr : whitneyInr A D ≫ h₁ = whitneyInr A D ≫ h₂) : h₁ = h₂ := by
  rw [eq_whitneyDesc h₁, eq_whitneyDesc h₂, hinl, hinr]

@[reassoc]
theorem whitneyDesc_comp (f : A ⟶ E) (g : D ⟶ E) (h : E ⟶ C) :
    whitneyDesc f g ≫ h = whitneyDesc (f ≫ h) (g ≫ h) := by
  simp only [whitneyDesc, Preadditive.add_comp, Category.assoc]

@[simp]
theorem whitneyDesc_inl_inr (A D : FiniteRankBundleCore 𝕜 B) :
    whitneyDesc (whitneyInl A D) (whitneyInr A D) = 𝟙 (whitneySum A D) :=
  whitney_total A D

@[simp]
theorem fiberMap_whitneyDesc (f : A ⟶ E) (g : D ⟶ E) (x : B) :
    (whitneyDesc f g).fiberMap x =
      ((f.fiberMap x).coprod (g.fiberMap x)).comp
        (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap := by
  -- Work in the standard model so simplification does not unfold dependent fibre instances.
  let e := splitCoords (𝕜 := 𝕜) (M := 𝕜) A.rank D.rank
  have h : (f.fiberMap x).comp ((ContinuousLinearMap.fst 𝕜 _ _).comp e.toContinuousLinearMap) +
      (g.fiberMap x).comp ((ContinuousLinearMap.snd 𝕜 _ _).comp e.toContinuousLinearMap) =
      ((f.fiberMap x).coprod (g.fiberMap x)).comp e.toContinuousLinearMap := by
    ext v
    rfl
  simp only [whitneyDesc, fiberMap_add, fiberMap_comp, fiberMap_whitneyFst, fiberMap_whitneySnd]
  exact h

theorem fiberMap_whitneyDesc_apply (f : A ⟶ E) (g : D ⟶ E) (x : B)
    (v : Fin (A.rank + D.rank) → 𝕜) :
    (whitneyDesc f g).fiberMap x v =
      f.fiberMap x (splitCoords (𝕜 := 𝕜) A.rank D.rank v).1 +
        g.fiberMap x (splitCoords (𝕜 := 𝕜) A.rank D.rank v).2 :=
  (DFunLike.congr_fun (fiberMap_whitneyDesc f g x) v).trans <|
    ContinuousLinearMap.coprod_apply (f.fiberMap x) (g.fiberMap x)
      (splitCoords (𝕜 := 𝕜) A.rank D.rank v)

/-- Direct sum of two bundle morphisms on Whitney sums. -/
def whitneyMap (f : A ⟶ A') (g : D ⟶ D') : whitneySum A D ⟶ whitneySum A' D' :=
  whitneyLift (whitneyFst A D ≫ f) (whitneySnd A D ≫ g)

theorem whitneyMap_def (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g = whitneyLift (whitneyFst A D ≫ f) (whitneySnd A D ≫ g) := (rfl)

@[reassoc (attr := simp)]
theorem whitneyMap_fst (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g ≫ whitneyFst A' D' = whitneyFst A D ≫ f :=
  whitneyLift_fst _ _

@[reassoc (attr := simp)]
theorem whitneyMap_snd (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g ≫ whitneySnd A' D' = whitneySnd A D ≫ g :=
  whitneyLift_snd _ _

@[reassoc (attr := simp)]
theorem whitneyInl_map (f : A ⟶ A') (g : D ⟶ D') :
    whitneyInl A D ≫ whitneyMap f g = f ≫ whitneyInl A' D' :=
  whitneySum_hom_ext (by simp) (by simp)

@[reassoc (attr := simp)]
theorem whitneyInr_map (f : A ⟶ A') (g : D ⟶ D') :
    whitneyInr A D ≫ whitneyMap f g = g ≫ whitneyInr A' D' :=
  whitneySum_hom_ext (by simp) (by simp)

@[simp]
theorem whitneyMap_id (A D : FiniteRankBundleCore 𝕜 B) :
    whitneyMap (𝟙 A) (𝟙 D) = 𝟙 (whitneySum A D) := by
  simp [whitneyMap_def]

@[simp]
theorem whitneyMap_zero (A A' D D' : FiniteRankBundleCore 𝕜 B) :
    whitneyMap (0 : A ⟶ A') (0 : D ⟶ D') = 0 :=
  whitneySum_hom_ext (by simp) (by simp)

@[simp]
theorem whitneyMap_comp (f₁ : A ⟶ A') (f₂ : A' ⟶ A'') (g₁ : D ⟶ D') (g₂ : D' ⟶ D'') :
    whitneyMap (f₁ ≫ f₂) (g₁ ≫ g₂) = whitneyMap f₁ g₁ ≫ whitneyMap f₂ g₂ :=
  whitneySum_hom_ext (by simp) (by simp)

@[simp]
theorem fiberMap_whitneyMap (f : A ⟶ A') (g : D ⟶ D') (x : B) :
    (whitneyMap f g).fiberMap x =
      (splitCoords (𝕜 := 𝕜) A'.rank D'.rank).symm.toContinuousLinearMap.comp
        (((f.fiberMap x).prodMap (g.fiberMap x)).comp
          (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap) := by
  -- Work in the standard model so simplification does not unfold dependent fibre instances.
  let e := splitCoords (𝕜 := 𝕜) (M := 𝕜) A.rank D.rank
  let e' := splitCoords (𝕜 := 𝕜) (M := 𝕜) A'.rank D'.rank
  have h : e'.symm.toContinuousLinearMap.comp
      (((f.fiberMap x).comp ((ContinuousLinearMap.fst 𝕜 _ _).comp e.toContinuousLinearMap)).prod
        ((g.fiberMap x).comp ((ContinuousLinearMap.snd 𝕜 _ _).comp e.toContinuousLinearMap))) =
      e'.symm.toContinuousLinearMap.comp
        (((f.fiberMap x).prodMap (g.fiberMap x)).comp e.toContinuousLinearMap) := by
    ext v i
    rfl
  simp only [whitneyMap, fiberMap_whitneyLift, fiberMap_comp, fiberMap_whitneyFst,
    fiberMap_whitneySnd]
  exact h

theorem splitCoords_fiberMap_whitneyMap (f : A ⟶ A') (g : D ⟶ D') (x : B)
    (v : Fin (A.rank + D.rank) → 𝕜) :
    splitCoords (𝕜 := 𝕜) A'.rank D'.rank ((whitneyMap f g).fiberMap x v) =
      (f.fiberMap x (splitCoords (𝕜 := 𝕜) A.rank D.rank v).1,
        g.fiberMap x (splitCoords (𝕜 := 𝕜) A.rank D.rank v).2) :=
  (congrArg (splitCoords (𝕜 := 𝕜) A'.rank D'.rank)
    (DFunLike.congr_fun (fiberMap_whitneyMap f g x) v)).trans <|
    (splitCoords (𝕜 := 𝕜) A'.rank D'.rank).apply_symm_apply _

/-- Direct sum of two bundle core isomorphisms. -/
def whitneyMapIso (e₁ : A ≅ A') (e₂ : D ≅ D') : whitneySum A D ≅ whitneySum A' D' where
  hom := whitneyMap e₁.hom e₂.hom
  inv := whitneyMap e₁.inv e₂.inv
  hom_inv_id := by rw [← whitneyMap_comp, e₁.hom_inv_id, e₂.hom_inv_id, whitneyMap_id]
  inv_hom_id := by rw [← whitneyMap_comp, e₁.inv_hom_id, e₂.inv_hom_id, whitneyMap_id]

@[simp]
theorem whitneyMapIso_hom (e₁ : A ≅ A') (e₂ : D ≅ D') :
    (whitneyMapIso e₁ e₂).hom = whitneyMap e₁.hom e₂.hom := (rfl)

@[simp]
theorem whitneyMapIso_inv (e₁ : A ≅ A') (e₂ : D ≅ D') :
    (whitneyMapIso e₁ e₂).inv = whitneyMap e₁.inv e₂.inv := (rfl)

end UniversalProperty

section Coherence

/-- Symmetry isomorphism exchanging the two summands of a Whitney sum. -/
def whitneyCommIso (A D : FiniteRankBundleCore 𝕜 B) : whitneySum A D ≅ whitneySum D A where
  hom := whitneyLift (whitneySnd A D) (whitneyFst A D)
  inv := whitneyLift (whitneySnd D A) (whitneyFst D A)
  hom_inv_id := whitneySum_hom_ext (by simp) (by simp)
  inv_hom_id := whitneySum_hom_ext (by simp) (by simp)

@[simp]
theorem whitneyCommIso_hom (A D : FiniteRankBundleCore 𝕜 B) :
    (whitneyCommIso A D).hom = whitneyLift (whitneySnd A D) (whitneyFst A D) := (rfl)

@[simp]
theorem whitneyCommIso_inv (A D : FiniteRankBundleCore 𝕜 B) :
    (whitneyCommIso A D).inv = whitneyLift (whitneySnd D A) (whitneyFst D A) := (rfl)

@[reassoc]
theorem whitneyMap_commIso_hom {A A' D D' : FiniteRankBundleCore 𝕜 B}
    (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g ≫ (whitneyCommIso A' D').hom =
      (whitneyCommIso A D).hom ≫ whitneyMap g f :=
  whitneySum_hom_ext (by simp) (by simp)

/-- Associativity isomorphism regrouping a threefold Whitney sum. -/
def whitneyAssocIso (A D C : FiniteRankBundleCore 𝕜 B) :
    whitneySum (whitneySum A D) C ≅ whitneySum A (whitneySum D C) where
  hom := whitneyLift (whitneyFst _ _ ≫ whitneyFst A D)
    (whitneyLift (whitneyFst _ _ ≫ whitneySnd A D) (whitneySnd _ _))
  inv := whitneyLift (whitneyLift (whitneyFst _ _) (whitneySnd _ _ ≫ whitneyFst D C))
    (whitneySnd _ _ ≫ whitneySnd D C)
  hom_inv_id := whitneySum_hom_ext (whitneySum_hom_ext (by simp) (by simp)) (by simp)
  inv_hom_id := whitneySum_hom_ext (by simp) (whitneySum_hom_ext (by simp) (by simp))

@[simp]
theorem whitneyAssocIso_hom (A D C : FiniteRankBundleCore 𝕜 B) :
    (whitneyAssocIso A D C).hom =
      whitneyLift (whitneyFst _ _ ≫ whitneyFst A D)
        (whitneyLift (whitneyFst _ _ ≫ whitneySnd A D) (whitneySnd _ _)) := (rfl)

@[simp]
theorem whitneyAssocIso_inv (A D C : FiniteRankBundleCore 𝕜 B) :
    (whitneyAssocIso A D C).inv =
      whitneyLift (whitneyLift (whitneyFst _ _) (whitneySnd _ _ ≫ whitneyFst D C))
        (whitneySnd _ _ ≫ whitneySnd D C) := (rfl)

@[reassoc]
theorem whitneyMap_assocIso_hom {A A' D D' C C' : FiniteRankBundleCore 𝕜 B}
    (f : A ⟶ A') (g : D ⟶ D') (h : C ⟶ C') :
    whitneyMap (whitneyMap f g) h ≫ (whitneyAssocIso A' D' C').hom =
      (whitneyAssocIso A D C).hom ≫ whitneyMap f (whitneyMap g h) :=
  whitneySum_hom_ext (by simp) (whitneySum_hom_ext (by simp) (by simp))

/-- Left unit isomorphism for Whitney sum with the trivial rank-zero core. -/
def whitneyZeroLeftIso (A : FiniteRankBundleCore 𝕜 B) :
    whitneySum (trivial 𝕜 B 0) A ≅ A where
  hom := whitneySnd (trivial 𝕜 B 0) A
  inv := whitneyInr (trivial 𝕜 B 0) A
  hom_inv_id := whitneySum_hom_ext' (isZero_trivial_zero.eq_of_src _ _) (by simp)
  inv_hom_id := whitneyInr_snd (trivial 𝕜 B 0) A

@[simp]
theorem whitneyZeroLeftIso_hom (A : FiniteRankBundleCore 𝕜 B) :
    (whitneyZeroLeftIso A).hom = whitneySnd (trivial 𝕜 B 0) A := (rfl)

@[simp]
theorem whitneyZeroLeftIso_inv (A : FiniteRankBundleCore 𝕜 B) :
    (whitneyZeroLeftIso A).inv = whitneyInr (trivial 𝕜 B 0) A := (rfl)

@[reassoc]
theorem whitneyMap_zeroLeftIso_hom {A A' : FiniteRankBundleCore 𝕜 B}
    (g : trivial 𝕜 B 0 ⟶ trivial 𝕜 B 0) (f : A ⟶ A') :
    whitneyMap g f ≫ (whitneyZeroLeftIso A').hom = (whitneyZeroLeftIso A).hom ≫ f := by
  simp only [whitneyZeroLeftIso_hom, whitneyMap_snd]

/-- Right unit isomorphism for Whitney sum with the trivial rank-zero core. -/
def whitneyZeroRightIso (A : FiniteRankBundleCore 𝕜 B) :
    whitneySum A (trivial 𝕜 B 0) ≅ A where
  hom := whitneyFst A (trivial 𝕜 B 0)
  inv := whitneyInl A (trivial 𝕜 B 0)
  hom_inv_id := whitneySum_hom_ext' (by simp) (isZero_trivial_zero.eq_of_src _ _)
  inv_hom_id := whitneyInl_fst A (trivial 𝕜 B 0)

@[simp]
theorem whitneyZeroRightIso_hom (A : FiniteRankBundleCore 𝕜 B) :
    (whitneyZeroRightIso A).hom = whitneyFst A (trivial 𝕜 B 0) := (rfl)

@[simp]
theorem whitneyZeroRightIso_inv (A : FiniteRankBundleCore 𝕜 B) :
    (whitneyZeroRightIso A).inv = whitneyInl A (trivial 𝕜 B 0) := (rfl)

@[reassoc]
theorem whitneyMap_zeroRightIso_hom {A A' : FiniteRankBundleCore 𝕜 B}
    (f : A ⟶ A') (g : trivial 𝕜 B 0 ⟶ trivial 𝕜 B 0) :
    whitneyMap f g ≫ (whitneyZeroRightIso A').hom = (whitneyZeroRightIso A).hom ≫ f := by
  simp only [whitneyZeroRightIso_hom, whitneyMap_fst]

end Coherence

section MathlibProd

/-- The coordinate vector in the Whitney-sum core over `x`, split into its pair of vectors in the
fibres of `A` and `D`. -/
def whitneySumFiberEquiv (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (whitneySum A D).core.Fiber x ≃L[𝕜] (A.core.Fiber ×ᵇ D.core.Fiber) x :=
  splitCoords (𝕜 := 𝕜) A.rank D.rank

theorem whitneySumFiberEquiv_apply (A D : FiniteRankBundleCore 𝕜 B) (x : B)
    (v : (whitneySum A D).core.Fiber x) :
    whitneySumFiberEquiv A D x v = splitCoords (𝕜 := 𝕜) A.rank D.rank v := (rfl)

theorem whitneySumFiberEquiv_symm_apply (A D : FiniteRankBundleCore 𝕜 B) (x : B)
    (w : (A.core.Fiber ×ᵇ D.core.Fiber) x) :
    (whitneySumFiberEquiv A D x).symm w = (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm w := (rfl)

theorem fst_whitneySumFiberEquiv (A D : FiniteRankBundleCore 𝕜 B) (x : B)
    (v : (whitneySum A D).core.Fiber x) :
    (whitneySumFiberEquiv A D x v).1 = (whitneyFst A D).fiberMap x v :=
  (congrArg Prod.fst (whitneySumFiberEquiv_apply A D x v)).trans
    (DFunLike.congr_fun (fiberMap_whitneyFst A D x) v).symm

theorem snd_whitneySumFiberEquiv (A D : FiniteRankBundleCore 𝕜 B) (x : B)
    (v : (whitneySum A D).core.Fiber x) :
    (whitneySumFiberEquiv A D x v).2 = (whitneySnd A D).fiberMap x v :=
  (congrArg Prod.snd (whitneySumFiberEquiv_apply A D x v)).trans
    (DFunLike.congr_fun (fiberMap_whitneySnd A D x) v).symm

theorem whitneySumFiberEquiv_whitneyInl (A D : FiniteRankBundleCore 𝕜 B) (x : B)
    (u : Fin A.rank → 𝕜) :
    whitneySumFiberEquiv A D x ((whitneyInl A D).fiberMap x u) = (u, 0) := by
  refine (whitneySumFiberEquiv_apply A D x _).trans ?_
  rw [DFunLike.congr_fun (fiberMap_whitneyInl A D x) u]
  exact (splitCoords (𝕜 := 𝕜) A.rank D.rank).apply_symm_apply (u, 0)

theorem whitneySumFiberEquiv_whitneyInr (A D : FiniteRankBundleCore 𝕜 B) (x : B)
    (w : Fin D.rank → 𝕜) :
    whitneySumFiberEquiv A D x ((whitneyInr A D).fiberMap x w) = (0, w) := by
  refine (whitneySumFiberEquiv_apply A D x _).trans ?_
  rw [DFunLike.congr_fun (fiberMap_whitneyInr A D x) w]
  exact (splitCoords (𝕜 := 𝕜) A.rank D.rank).apply_symm_apply (0, w)

/-- Under `whitneySumFiberEquiv`, the direct sum of two bundle maps acts componentwise on the
direct-sum fibres. -/
theorem whitneySumFiberEquiv_fiberMap_whitneyMap {A A' D D' : FiniteRankBundleCore 𝕜 B}
    (f : A ⟶ A') (g : D ⟶ D') (x : B) (v : (whitneySum A D).core.Fiber x) :
    whitneySumFiberEquiv A' D' x ((whitneyMap f g).fiberMap x v) =
      (f.fiberMap x (whitneySumFiberEquiv A D x v).1,
        g.fiberMap x (whitneySumFiberEquiv A D x v).2) := by
  refine (whitneySumFiberEquiv_apply A' D' x _).trans ?_
  rw [whitneySumFiberEquiv_apply A D x v]
  exact splitCoords_fiberMap_whitneyMap f g x v

/-- In matching local trivializations at `i`, `whitneySumFiberEquiv` intertwines the Whitney-sum
core chart with Mathlib's product trivialization `(A.core.localTriv i).prod (D.core.localTriv i)`.
This holds for every `p`, with no base-set hypothesis. -/
theorem localTriv_prod_whitneySumFiberEquiv (A D : FiniteRankBundleCore 𝕜 B) (i : B)
    (p : (whitneySum A D).core.TotalSpace) :
    (((A.core.localTriv i).prod (D.core.localTriv i))
      ⟨p.proj, whitneySumFiberEquiv A D p.proj p.2⟩).2 =
      splitCoords (𝕜 := 𝕜) A.rank D.rank (((whitneySum A D).core.localTriv i p).2) := by
  simp only [Trivialization.prod_apply, Trivialization.Prod.toFun', localTriv_apply,
    A.indexAt_eq, D.indexAt_eq, (whitneySum A D).indexAt_eq, whitneySumFiberEquiv_apply]
  exact (splitCoords_coordChange_whitneySum A D p.proj i p.proj p.2).symm

/-- In matching local trivializations at `i`, `(whitneySumFiberEquiv A D q.proj).symm` intertwines
Mathlib's product trivialization `(A.core.localTriv i).prod (D.core.localTriv i)` with the
Whitney-sum core chart. This holds for every `q`, with no base-set hypothesis. -/
theorem localTriv_whitneySumFiberEquiv_symm (A D : FiniteRankBundleCore 𝕜 B) (i : B)
    (q : TotalSpace ((Fin A.rank → 𝕜) × (Fin D.rank → 𝕜)) (A.core.Fiber ×ᵇ D.core.Fiber)) :
    ((whitneySum A D).core.localTriv i
      ⟨q.proj, (whitneySumFiberEquiv A D q.proj).symm q.2⟩).2 =
      (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm
        ((((A.core.localTriv i).prod (D.core.localTriv i)) q).2) := by
  rcases q with ⟨y, w⟩
  apply (splitCoords (𝕜 := 𝕜) A.rank D.rank).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, ← localTriv_prod_whitneySumFiberEquiv A D i]
  simp only [ContinuousLinearEquiv.apply_symm_apply]

/-- The reconstructed total space of the Whitney sum is homeomorphic to Mathlib's native
direct-sum bundle `A.core.Fiber ×ᵇ D.core.Fiber`, over the identity of the base and by
`whitneySumFiberEquiv` on each fibre. -/
def whitneySumTotalSpaceHomeomorph (A D : FiniteRankBundleCore 𝕜 B) :
    (whitneySum A D).core.TotalSpace ≃ₜ
      TotalSpace ((Fin A.rank → 𝕜) × (Fin D.rank → 𝕜)) (A.core.Fiber ×ᵇ D.core.Fiber) where
  toFun p := ⟨p.proj, whitneySumFiberEquiv A D p.proj p.2⟩
  invFun p := ⟨p.proj, (whitneySumFiberEquiv A D p.proj).symm p.2⟩
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := by
    rw [(FiberBundle.Prod.isInducing_diag (Fin A.rank → 𝕜) A.core.Fiber
      (Fin D.rank → 𝕜) D.core.Fiber).continuous_iff]
    refine (((whitneyFst A D).continuous_totalSpaceMap).prodMk
      ((whitneySnd A D).continuous_totalSpaceMap)).congr ?_
    rintro ⟨x, v⟩
    simp only [Function.comp_apply, CoordinateHom.totalSpaceMap_mk, fst_whitneySumFiberEquiv,
      snd_whitneySumFiberEquiv]
  continuous_invFun := by
    refine continuous_iff_continuousAt.2 fun p => ?_
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨(FiberBundle.continuous_proj ((Fin A.rank → 𝕜) × (Fin D.rank → 𝕜))
      (A.core.Fiber ×ᵇ D.core.Fiber)).continuousAt, ?_⟩
    let e := (A.core.localTriv p.proj).prod (D.core.localTriv p.proj)
    have hp : p ∈ e.source := e.mem_source.2 ⟨A.mem_baseSet_self p.proj, D.mem_baseSet_self p.proj⟩
    have hc := ((splitCoords (𝕜 := 𝕜) A.rank D.rank).symm.continuous.continuousAt.comp
      ((e.continuousOn.continuousAt (e.open_source.mem_nhds hp)).snd))
    refine hc.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
    dsimp only [Function.comp_apply]
    rw [(whitneySum A D).trivializationAt_core]
    exact localTriv_whitneySumFiberEquiv_symm A D p.proj q

@[simp]
theorem whitneySumTotalSpaceHomeomorph_apply (A D : FiniteRankBundleCore 𝕜 B)
    (p : (whitneySum A D).core.TotalSpace) :
    whitneySumTotalSpaceHomeomorph A D p = ⟨p.proj, whitneySumFiberEquiv A D p.proj p.2⟩ := (rfl)

@[simp]
theorem whitneySumTotalSpaceHomeomorph_symm_apply (A D : FiniteRankBundleCore 𝕜 B)
    (p : TotalSpace ((Fin A.rank → 𝕜) × (Fin D.rank → 𝕜)) (A.core.Fiber ×ᵇ D.core.Fiber)) :
    (whitneySumTotalSpaceHomeomorph A D).symm p =
      ⟨p.proj, (whitneySumFiberEquiv A D p.proj).symm p.2⟩ := (rfl)

/-- `whitneySumTotalSpaceHomeomorph` intertwines `whitneyMap f g` on the Whitney sum with the
componentwise action of `f` and `g` on Mathlib's direct-sum bundle. -/
theorem whitneySumTotalSpaceHomeomorph_naturality {A A' D D' : FiniteRankBundleCore 𝕜 B}
    (f : A ⟶ A') (g : D ⟶ D') (p : (whitneySum A D).core.TotalSpace) :
    whitneySumTotalSpaceHomeomorph A' D' ((whitneyMap f g).totalSpaceMap p) =
      ⟨p.proj, (f.fiberMap p.proj (whitneySumTotalSpaceHomeomorph A D p).2.1,
        g.fiberMap p.proj (whitneySumTotalSpaceHomeomorph A D p).2.2)⟩ := by
  rw [whitneySumTotalSpaceHomeomorph_apply A D p]
  rcases p with ⟨x, v⟩
  rw [CoordinateHom.totalSpaceMap_mk, whitneySumTotalSpaceHomeomorph_apply]
  exact congrArg (TotalSpace.mk' ((Fin A'.rank → 𝕜) × (Fin D'.rank → 𝕜)) x)
    (whitneySumFiberEquiv_fiberMap_whitneyMap f g x v)

end MathlibProd

end TauCeti.FiniteRankBundleCore
