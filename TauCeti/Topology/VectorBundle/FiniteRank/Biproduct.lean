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

/-!
# Whitney sums of finite-rank bundle cores

The Whitney sum of two point-indexed cores uses the intersections of their charts
and block-diagonal transition maps, transported by `TauCeti.splitCoords` to the
standard model `Fin (A.rank + D.rank) → 𝕜`. Its projections and inclusions are
continuous coordinate morphisms, hence continuous fibrewise linear maps of the
reconstructed Mathlib bundles.

`whitneyBiconeIsBilimit` proves the product and coproduct universal properties of
this geometric sum. Thus `FiniteRankBundleCore` has binary biproducts, including
zero-rank bundles and bundles over the empty base. The base is arbitrary, and
the scalar field need not be complete.

The construction uses Mathlib's coordinate cores and its preadditive criterion
`CategoryTheory.Limits.isBinaryBilimitOfTotal`.
-/

public section

open CategoryTheory CategoryTheory.Limits VectorBundleCore Set

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

end TauCeti.FiniteRankBundleCore
