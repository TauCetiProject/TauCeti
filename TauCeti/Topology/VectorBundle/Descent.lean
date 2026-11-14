/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Hom
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Topology.ContinuousMap.Algebra
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Pi

/-!
# Descent of vector-bundle maps from coordinates

`VectorBundleCore.CoordinateHom` consists of continuous operator-valued functions on
source/target chart intersections, intertwining the two transition functions. Values
are stored only on these intersections: there is no unconstrained off-chart data.
For finite coordinate models these are continuous finite-matrix functions, independently
of any original fibre universe.

`CoordinateHom.totalSpaceMap` glues these operators to a continuous map of the actual
Mathlib total spaces, linear on each fibre. `CoordinateHom.localTriv_fiberMap` recovers
all the prescribed coordinates, and `CoordinateHom.fiberMap_injective` proves uniqueness.
Thus coordinate descent loses no morphism data. The identity is represented by the
transition functions themselves, not by constant identity matrices in different charts.

Conversely, `CoordinateHom.ofContinuous` extracts the chart operators of any continuous
section of Mathlib's Hom bundle between two cores; continuity in a pair of charts on their
whole common domain, with chart expressions `VectorBundleCore.inChartCoordinates`, is
`VectorBundleCore.continuousOn_inChartCoordinates`.
`CoordinateHom.fiberMapEquiv` identifies coordinate morphisms with these continuous
sections. For a finite-dimensional source model over a complete scalar field these are exactly
the continuous fibrewise linear maps of total spaces, by `TauCeti.continuous_hom_bundle_iff`;
when the source model is a finite coordinate space `α → 𝕜`,
`CoordinateHom.ofContinuousTotalSpacePi` extracts the chart operators directly from a continuous
total-space map without assuming `CompleteSpace 𝕜`, and `CoordinateHom.invOfBijectivePi`
inverts fibrewise bijective coordinate morphisms between finite coordinate models.
`CoordinateHom.comp` composes coordinate morphisms; in charts it multiplies the chart
operators through any intermediate chart (`CoordinateHom.operator_comp`), and it is
associative and unital for `CoordinateHom.id`.
Coordinate morphisms form an abelian group under pointwise addition of chart operators,
and composition is additive in both arguments.

The construction uses Mathlib's `VectorBundleCore`, its local trivializations and the
trivializations `Bundle.Trivialization.continuousLinearMap` of the Hom bundle.
-/

public section

open Bundle Set Topology

namespace VectorBundleCore

variable {𝕜 B F G H ι κ ν : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- Continuous chart operators intertwining source and target transition functions.
Only values on actual chart intersections are part of the data. -/
structure CoordinateHom (Z : VectorBundleCore 𝕜 B F ι) (W : VectorBundleCore 𝕜 B G κ) where
  /-- The operator from source chart `i` to target chart `j`. -/
  operator : ∀ i j, C(↥(Z.baseSet i ∩ W.baseSet j), F →L[𝕜] G)
  /-- Changing either chart preserves the represented fibre map. -/
  compatible : ∀ i i' j j' (x : B) (hi : x ∈ Z.baseSet i) (hi' : x ∈ Z.baseSet i')
    (hj : x ∈ W.baseSet j) (hj' : x ∈ W.baseSet j') (v : F),
    W.coordChange j j' x (operator i j ⟨x, hi, hj⟩ v) =
      operator i' j' ⟨x, hi', hj'⟩ (Z.coordChange i i' x v)

namespace CoordinateHom

variable {Z : VectorBundleCore 𝕜 B F ι} {W : VectorBundleCore 𝕜 B G κ}

@[ext] theorem ext {a b : CoordinateHom Z W}
    (h : ∀ i j x, a.operator i j x = b.operator i j x) : a = b := by
  cases a
  cases b
  congr
  funext i j
  exact ContinuousMap.ext (h i j)

/-- The operator form of `CoordinateHom.compatible`: changing the target chart after a chart
operator agrees with changing the source chart before the other chart operator. -/
theorem coordChange_comp_operator (a : CoordinateHom Z W) (i i' : ι) (j j' : κ) (x : B)
    (hi : x ∈ Z.baseSet i) (hi' : x ∈ Z.baseSet i') (hj : x ∈ W.baseSet j)
    (hj' : x ∈ W.baseSet j') :
    (W.coordChange j j' x).comp (a.operator i j ⟨x, hi, hj⟩) =
      (a.operator i' j' ⟨x, hi', hj'⟩).comp (Z.coordChange i i' x) :=
  ContinuousLinearMap.ext (a.compatible i i' j j' x hi hi' hj hj')

/-- The descended linear operator in the preferred coordinates at a base point. -/
def fiberMap (a : CoordinateHom Z W) (x : B) : F →L[𝕜] G :=
  a.operator (Z.indexAt x) (W.indexAt x) ⟨x, Z.mem_baseSet_at x, W.mem_baseSet_at x⟩

/-- The descended operator is the chart operator in the two preferred charts. -/
theorem fiberMap_def (a : CoordinateHom Z W) (x : B) :
    a.fiberMap x =
      a.operator (Z.indexAt x) (W.indexAt x) ⟨x, Z.mem_baseSet_at x, W.mem_baseSet_at x⟩ :=
  (rfl)

/-- The descended operator has the prescribed expression in every pair of charts. -/
theorem coordChange_fiberMap (a : CoordinateHom Z W) (i : ι) (j : κ) {x : B}
    (hi : x ∈ Z.baseSet i) (hj : x ∈ W.baseSet j) (v : F) :
    W.coordChange (W.indexAt x) j x (a.fiberMap x v) =
      a.operator i j ⟨x, hi, hj⟩ (Z.coordChange (Z.indexAt x) i x v) :=
  a.compatible _ i _ j x (Z.mem_baseSet_at x) hi (W.mem_baseSet_at x) hj v

/-- Recovery of a chart operator from the descended fibre map. -/
theorem operator_eq (a : CoordinateHom Z W) (i : ι) (j : κ)
    (x : ↥(Z.baseSet i ∩ W.baseSet j)) :
    a.operator i j x = Z.inChartCoordinates W i j x.1 (a.fiberMap x.1) := by
  ext v
  rw [inChartCoordinates_apply, a.coordChange_fiberMap i j x.2.1 x.2.2,
    Z.coordChange_comp i (Z.indexAt x.1) i x.1
      ⟨⟨x.2.1, Z.mem_baseSet_at x.1⟩, x.2.1⟩,
    Z.coordChange_self i x.1 x.2.1]

/-- Preferred-coordinate descent is faithful; there is no off-chart data to forget. -/
theorem fiberMap_injective : Function.Injective (fiberMap (Z := Z) (W := W)) := by
  intro a b hab
  ext i j x
  rw [a.operator_eq, b.operator_eq, hab]

/-- The fibrewise linear map of total spaces determined by compatible chart operators. -/
def totalSpaceMap (a : CoordinateHom Z W) (p : Z.TotalSpace) : W.TotalSpace :=
  ⟨p.proj, a.fiberMap p.proj p.2⟩

@[simp] theorem totalSpaceMap_proj (a : CoordinateHom Z W) (p : Z.TotalSpace) :
    (a.totalSpaceMap p).proj = p.proj := (rfl)

@[simp] theorem totalSpaceMap_mk (a : CoordinateHom Z W) (x : B) (v : Z.Fiber x) :
    a.totalSpaceMap ⟨x, v⟩ = ⟨x, a.fiberMap x v⟩ := (rfl)

theorem totalSpaceMap_def (a : CoordinateHom Z W) :
    a.totalSpaceMap = fun p ↦ TotalSpace.mk' G p.proj (a.fiberMap p.proj p.2) := (rfl)

/-- In local trivializations the descended map is precisely the given chart operator. -/
theorem localTriv_fiberMap (a : CoordinateHom Z W) (i : ι) (j : κ) (p : Z.TotalSpace)
    (hi : p.proj ∈ Z.baseSet i) (hj : p.proj ∈ W.baseSet j) :
    ((W.localTriv j) (a.totalSpaceMap p)).2 =
      a.operator i j ⟨p.proj, hi, hj⟩ ((Z.localTriv i) p).2 := by
  simp only [localTriv_apply, totalSpaceMap]
  exact a.coordChange_fiberMap i j hi hj p.2

/-- Two coordinate morphisms inducing the same map of total spaces are equal. -/
theorem totalSpaceMap_injective : Function.Injective (totalSpaceMap (Z := Z) (W := W)) := by
  intro a b hab
  apply fiberMap_injective
  funext x
  ext v
  exact congrArg TotalSpace.snd (congrFun hab (⟨x, v⟩ : Z.TotalSpace))

/-- Compatible continuous coordinate operators glue to a continuous total-space map. -/
theorem continuous_totalSpaceMap (a : CoordinateHom Z W) : Continuous a.totalSpaceMap := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  -- Fix both charts near the point; the preferred chart indices need not vary continuously.
  let i := Z.indexAt p.proj
  let j := W.indexAt p.proj
  let s : Set Z.TotalSpace := {q | q.proj ∈ Z.baseSet i ∩ W.baseSet j}
  have hp : p ∈ s := ⟨Z.mem_baseSet_at _, W.mem_baseSet_at _⟩
  have hs : IsOpen s :=
    ((Z.isOpen_baseSet i).inter (W.isOpen_baseSet j)).preimage Z.continuous_proj
  have hbase : Continuous (fun q : s ↦ (⟨q.1.proj, q.2⟩ : ↥(Z.baseSet i ∩ W.baseSet j))) :=
    (Z.continuous_proj.comp continuous_subtype_val).subtype_mk _
  have hcoord : Continuous (fun q : s ↦ ((Z.localTriv i) q.1).2) :=
    ((Z.localTriv i).continuousOn.comp_continuous continuous_subtype_val
      (fun q ↦ q.2.1)).snd
  have hlocal := ((a.operator i j).continuous.comp hbase).clm_apply hcoord
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨Z.continuous_proj.continuousAt, ?_⟩
  apply ContinuousWithinAt.continuousAt (s := s) _ (hs.mem_nhds hp)
  apply (continuousWithinAt_iff_continuousAt_domRestrict _ hp).2
  apply hlocal.continuousAt.congr
  exact Filter.Eventually.of_forall fun q ↦
    (a.localTriv_fiberMap i j q.1 q.2.1 q.2.2).symm

/-- A fibre family realizing all the chart operators is necessarily the descended family.
No regularity hypothesis is needed for uniqueness. -/
theorem fiberMap_unique (a : CoordinateHom Z W) (f : B → F →L[𝕜] G)
    (hf : ∀ i j (x : ↥(Z.baseSet i ∩ W.baseSet j)) (v : F),
      W.coordChange (W.indexAt x.1) j x.1 (f x.1 v) =
        a.operator i j x (Z.coordChange (Z.indexAt x.1) i x.1 v)) :
    f = a.fiberMap := by
  funext x
  ext v
  simpa only [fiberMap, Z.coordChange_self _ _ (Z.mem_baseSet_at x),
    W.coordChange_self _ _ (W.mem_baseSet_at x)] using
    hf (Z.indexAt x) (W.indexAt x) ⟨x, Z.mem_baseSet_at x, W.mem_baseSet_at x⟩ v

/-- The identity bundle map is represented in two charts by their transition operator. -/
def id (Z : VectorBundleCore 𝕜 B F ι) : CoordinateHom Z Z where
  operator i j := ⟨_, (Z.continuousOn_coordChange i j).domRestrict⟩
  compatible i i' j j' x hi hi' hj hj' v :=
    (Z.coordChange_comp i j j' x ⟨⟨hi, hj⟩, hj'⟩ v).trans
      (Z.coordChange_comp i i' j' x ⟨⟨hi, hi'⟩, hj'⟩ v).symm

@[simp] theorem operator_id (Z : VectorBundleCore 𝕜 B F ι) (i j : ι) :
    (id Z).operator i j =
      ⟨(Z.baseSet i ∩ Z.baseSet j).domRestrict (Z.coordChange i j),
        (Z.continuousOn_coordChange i j).domRestrict⟩ := (rfl)

@[simp] theorem fiberMap_id (Z : VectorBundleCore 𝕜 B F ι) (x : B) :
    (id Z).fiberMap x = ContinuousLinearMap.id 𝕜 F := by
  ext v
  exact Z.coordChange_self _ _ (Z.mem_baseSet_at x) v

@[simp] theorem totalSpaceMap_id (Z : VectorBundleCore 𝕜 B F ι) :
    (id Z).totalSpaceMap = _root_.id := by
  funext p
  simp only [totalSpaceMap, fiberMap_id]
  rfl

/-- The descended fibre maps of a coordinate morphism form a continuous section of the Hom
bundle. -/
theorem continuous_fiberMap (a : CoordinateHom Z W) :
    Continuous fun x ↦ TotalSpace.mk' (F →L[𝕜] G)
      (E := fun y ↦ Z.Fiber y →L[𝕜] W.Fiber y) x (a.fiberMap x) :=
  continuous_hom_bundle_iff_forall_continuousOn.2 fun i j ↦
    continuousOn_iff_continuous_domRestrict.2 <|
      (a.operator i j).continuous.congr fun x ↦ a.operator_eq i j x

/-- The coordinate morphism of a continuous section of the Hom bundle. Its chart operators
are the coordinate expressions of the section. -/
def ofContinuous (f : B → F →L[𝕜] G)
    (hf : Continuous fun x ↦ TotalSpace.mk' (F →L[𝕜] G)
      (E := fun y ↦ Z.Fiber y →L[𝕜] W.Fiber y) x (f x)) :
    CoordinateHom Z W where
  operator i j :=
    ⟨_, continuousOn_iff_continuous_domRestrict.1
      (continuousOn_inChartCoordinates hf.continuousOn)⟩
  compatible i i' j j' x hi hi' hj hj' v := by
    simp only [ContinuousMap.coe_mk, Set.domRestrict_apply, inChartCoordinates_apply]
    rw [W.coordChange_comp _ j j' x ⟨⟨W.mem_baseSet_at x, hj⟩, hj'⟩,
      Z.coordChange_comp i i' _ x ⟨⟨hi, hi'⟩, Z.mem_baseSet_at x⟩]

section ofContinuous

variable (f : B → F →L[𝕜] G)
  (hf : Continuous fun x ↦ TotalSpace.mk' (F →L[𝕜] G)
    (E := fun y ↦ Z.Fiber y →L[𝕜] W.Fiber y) x (f x))

theorem operator_ofContinuous (i : ι) (j : κ) (x : ↥(Z.baseSet i ∩ W.baseSet j)) :
    (ofContinuous f hf).operator i j x = Z.inChartCoordinates W i j x.1 (f x.1) := (rfl)

/-- Descent recovers the continuous section a coordinate morphism was extracted from. -/
@[simp] theorem fiberMap_ofContinuous : (ofContinuous f hf).fiberMap = f :=
  funext fun x ↦ inChartCoordinates_indexAt Z W x (f x)

end ofContinuous

/-- Every coordinate morphism is extracted from its descended fibre maps. -/
@[simp] theorem ofContinuous_fiberMap (a : CoordinateHom Z W) :
    ofContinuous a.fiberMap a.continuous_fiberMap = a :=
  fiberMap_injective (fiberMap_ofContinuous _ _)

variable (Z W) in
/-- Coordinate morphisms correspond exactly to continuous sections of the Hom bundle, by
preferred-chart descent. -/
def fiberMapEquiv : CoordinateHom Z W ≃ {f : B → F →L[𝕜] G // Continuous fun x ↦
    TotalSpace.mk' (F →L[𝕜] G) (E := fun y ↦ Z.Fiber y →L[𝕜] W.Fiber y) x (f x)} where
  toFun a := ⟨a.fiberMap, a.continuous_fiberMap⟩
  invFun f := ofContinuous f.1 f.2
  left_inv := ofContinuous_fiberMap
  right_inv f := Subtype.ext (fiberMap_ofContinuous f.1 f.2)

@[simp] theorem coe_fiberMapEquiv_apply (a : CoordinateHom Z W) :
    (fiberMapEquiv Z W a : B → F →L[𝕜] G) = a.fiberMap := (rfl)

@[simp] theorem fiberMapEquiv_symm_apply (f : {f : B → F →L[𝕜] G // Continuous fun x ↦
    TotalSpace.mk' (F →L[𝕜] G) (E := fun y ↦ Z.Fiber y →L[𝕜] W.Fiber y) x (f x)}) :
    (fiberMapEquiv Z W).symm f = ofContinuous f.1 f.2 := (rfl)

variable {V : VectorBundleCore 𝕜 B H ν}

/-- Composition of coordinate morphisms, descending to the composite of the fibre maps. -/
def comp (b : CoordinateHom W V) (a : CoordinateHom Z W) : CoordinateHom Z V :=
  ofContinuous (fun x ↦ (b.fiberMap x).comp (a.fiberMap x))
    (b.continuous_fiberMap.clm_bundle_comp (E₁ := Z.Fiber) (E₂ := W.Fiber) (E₃ := V.Fiber)
      (b := fun x ↦ x) a.continuous_fiberMap)

@[simp] theorem fiberMap_comp (b : CoordinateHom W V) (a : CoordinateHom Z W) (x : B) :
    (b.comp a).fiberMap x = (b.fiberMap x).comp (a.fiberMap x) :=
  congrFun (fiberMap_ofContinuous _ _) x

/-- In charts, composition of coordinate morphisms is composition of the chart operators,
through any intermediate chart. -/
theorem operator_comp (b : CoordinateHom W V) (a : CoordinateHom Z W) (i : ι) (j : κ) (k : ν)
    {x : B} (hi : x ∈ Z.baseSet i) (hj : x ∈ W.baseSet j) (hk : x ∈ V.baseSet k) :
    (b.comp a).operator i k ⟨x, hi, hk⟩ =
      (b.operator j k ⟨x, hj, hk⟩).comp (a.operator i j ⟨x, hi, hj⟩) := by
  rw [operator_eq, operator_eq, operator_eq, fiberMap_comp, inChartCoordinates_comp Z W V i k hj]

@[simp] theorem totalSpaceMap_comp (b : CoordinateHom W V) (a : CoordinateHom Z W) :
    (b.comp a).totalSpaceMap = b.totalSpaceMap ∘ a.totalSpaceMap := by
  funext p
  simp only [totalSpaceMap, fiberMap_comp, Function.comp_apply]
  -- `ContinuousLinearMap.comp_apply` does not fire on a vector of the core fibre `Z.Fiber`,
  -- which is the model fibre `F` only up to unfolding.
  rfl

@[simp] theorem id_comp (a : CoordinateHom Z W) : (id W).comp a = a :=
  fiberMap_injective <| funext fun x ↦ by
    rw [fiberMap_comp, fiberMap_id, ContinuousLinearMap.id_comp]

@[simp] theorem comp_id (a : CoordinateHom Z W) : a.comp (id Z) = a :=
  fiberMap_injective <| funext fun x ↦ by
    rw [fiberMap_comp, fiberMap_id, ContinuousLinearMap.comp_id]

theorem comp_assoc {μ : Type*} {K : Type*} [NormedAddCommGroup K] [NormedSpace 𝕜 K]
    {U : VectorBundleCore 𝕜 B K μ} (c : CoordinateHom V U) (b : CoordinateHom W V)
    (a : CoordinateHom Z W) : (c.comp b).comp a = c.comp (b.comp a) :=
  fiberMap_injective <| funext fun x ↦ by
    simp only [fiberMap_comp, ContinuousLinearMap.comp_assoc]

/-! The additive structure is inherited from the chart operators. Compatibility is a linear
condition, so compatible families form an additive subgroup of all chart operators. -/

/-- Coordinate morphisms form an abelian group under pointwise addition of chart operators. -/
instance : AddCommGroup (CoordinateHom Z W) :=
  let S : AddSubgroup (∀ i j, C(↥(Z.baseSet i ∩ W.baseSet j), F →L[𝕜] G)) :=
    { carrier := {A | ∀ i i' j j' (x : B) (hi : x ∈ Z.baseSet i) (hi' : x ∈ Z.baseSet i')
        (hj : x ∈ W.baseSet j) (hj' : x ∈ W.baseSet j') (v : F),
        W.coordChange j j' x (A i j ⟨x, hi, hj⟩ v) =
          A i' j' ⟨x, hi', hj'⟩ (Z.coordChange i i' x v)}
      zero_mem' := by
        intro i i' j j' x hi hi' hj hj' v
        simp only [Pi.zero_apply, ContinuousMap.zero_apply, zero_apply, map_zero]
      add_mem' := by
        intro a b ha hb i i' j j' x hi hi' hj hj' v
        simp only [Pi.add_apply, ContinuousMap.add_apply, add_apply, map_add]
        rw [ha i i' j j' x hi hi' hj hj', hb i i' j j' x hi hi' hj hj']
      neg_mem' := by
        intro a ha i i' j j' x hi hi' hj hj' v
        simp only [Pi.neg_apply, ContinuousMap.neg_apply, neg_apply, map_neg]
        rw [ha i i' j j' x hi hi' hj hj'] }
  let e : CoordinateHom Z W ≃ S :=
    { toFun a := ⟨a.operator, a.compatible⟩
      invFun a := ⟨a.1, a.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  e.addCommGroup

@[simp] theorem operator_zero (i : ι) (j : κ) :
    (0 : CoordinateHom Z W).operator i j = 0 := (rfl)

@[simp] theorem operator_add (a b : CoordinateHom Z W) (i : ι) (j : κ) :
    (a + b).operator i j = a.operator i j + b.operator i j := (rfl)

@[simp] theorem operator_neg (a : CoordinateHom Z W) (i : ι) (j : κ) :
    (-a).operator i j = -a.operator i j := (rfl)

@[simp] theorem fiberMap_zero (x : B) :
    (0 : CoordinateHom Z W).fiberMap x = 0 := (rfl)

@[simp] theorem fiberMap_add (a b : CoordinateHom Z W) (x : B) :
    (a + b).fiberMap x = a.fiberMap x + b.fiberMap x := (rfl)

@[simp] theorem fiberMap_neg (a : CoordinateHom Z W) (x : B) :
    (-a).fiberMap x = -a.fiberMap x := (rfl)

/-- Composition of coordinate morphisms is additive in its first argument. -/
theorem add_comp (b c : CoordinateHom W V) (a : CoordinateHom Z W) :
    (b + c).comp a = b.comp a + c.comp a := by
  apply fiberMap_injective
  funext x
  simp only [fiberMap_comp, fiberMap_add, ContinuousLinearMap.add_comp]

/-- Composition of coordinate morphisms is additive in its second argument. -/
theorem comp_add (b : CoordinateHom W V) (a c : CoordinateHom Z W) :
    b.comp (a + c) = b.comp a + b.comp c := by
  apply fiberMap_injective
  funext x
  simp only [fiberMap_comp, fiberMap_add, ContinuousLinearMap.comp_add]

section PiSource

variable {α β : Type*} [Fintype α] [Fintype β]

/-- When the source model is a finite coordinate space `α → 𝕜`, any fibrewise continuous linear
map inducing a continuous map of total spaces defines a coordinate morphism, without assuming
`CompleteSpace 𝕜`. -/
def ofContinuousTotalSpacePi (Z : VectorBundleCore 𝕜 B (α → 𝕜) ι)
    (W : VectorBundleCore 𝕜 B G κ) (f : B → (α → 𝕜) →L[𝕜] G)
    (hf : Continuous fun p : Z.TotalSpace ↦ (⟨p.proj, f p.proj p.2⟩ : W.TotalSpace)) :
    CoordinateHom Z W where
  operator i j :=
    ⟨fun x ↦ Z.inChartCoordinates W i j x.1 (f x.1), by
      classical
      refine TauCeti.continuous_pi_clm_iff_apply.2 fun k ↦ ?_
      have hsymm : Continuous fun x : ↥(Z.baseSet i ∩ W.baseSet j) ↦
          (Z.localTriv i).toOpenPartialHomeomorph.symm (x.1, (Pi.single k 1 : α → 𝕜)) :=
        (Z.localTriv i).toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
          (continuous_subtype_val.prodMk
            (continuous_const : Continuous fun _ ↦ (Pi.single k 1 : α → 𝕜)))
          fun x ↦ (Z.mem_localTriv_target i (x.1, (Pi.single k 1 : α → 𝕜))).2
            (by rw [← Z.baseSet_at]; exact x.2.1)
      refine (((W.localTriv j).continuousOn.comp_continuous (hf.comp hsymm) fun x ↦ ?_).snd).congr
        fun x ↦ ?_
      · rw [W.mem_localTriv_source]
        simpa only [Function.comp_apply, Z.localTriv_symm_fst] using x.2.2
      · simp only [inChartCoordinates_apply, Function.comp_apply,
          Z.localTriv_symm_fst, W.localTriv_apply]⟩
  compatible i i' j j' x hi hi' hj hj' v := by
    simp only [ContinuousMap.coe_mk, inChartCoordinates_apply]
    rw [W.coordChange_comp _ j j' x ⟨⟨W.mem_baseSet_at x, hj⟩, hj'⟩,
      Z.coordChange_comp i i' _ x ⟨⟨hi, hi'⟩, Z.mem_baseSet_at x⟩]

@[simp] theorem fiberMap_ofContinuousTotalSpacePi (Z : VectorBundleCore 𝕜 B (α → 𝕜) ι)
    (W : VectorBundleCore 𝕜 B G κ) (f : B → (α → 𝕜) →L[𝕜] G)
    (hf : Continuous fun p : Z.TotalSpace ↦ (⟨p.proj, f p.proj p.2⟩ : W.TotalSpace)) (x : B) :
    (ofContinuousTotalSpacePi Z W f hf).fiberMap x = f x :=
  inChartCoordinates_indexAt Z W x (f x)

end PiSource

end CoordinateHom

/-- Every transition operator of a `VectorBundleCore` on the overlap of two charts is bijective,
with inverse given by the reverse transition operator. -/
theorem coordChange_bijective (Z : VectorBundleCore 𝕜 B F ι) {i j : ι} {x : B}
    (hi : x ∈ Z.baseSet i) (hj : x ∈ Z.baseSet j) :
    Function.Bijective (Z.coordChange i j x) :=
  ⟨fun u v huv ↦ by
    have hcomp := Z.coordChange_comp i j i x ⟨⟨hi, hj⟩, hi⟩
    simpa only [Z.coordChange_self i x hi] using
      (hcomp u).symm.trans ((congrArg (Z.coordChange j i x) huv).trans (hcomp v)),
   fun w ↦ ⟨Z.coordChange j i x w, by
    simpa only [Z.coordChange_self j x hj] using
      Z.coordChange_comp j i j x ⟨⟨hj, hi⟩, hj⟩ w⟩⟩

namespace CoordinateHom

/-- On an overlap of source chart `i` and target chart `j`, the chart operator of `a` at `x` is
bijective if and only if the represented fibre map `a.fiberMap x` is bijective. -/
theorem operator_bijective_iff {Z : VectorBundleCore 𝕜 B F ι} {W : VectorBundleCore 𝕜 B G κ}
    (a : CoordinateHom Z W) {i : ι} {j : κ} {x : B}
    (hi : x ∈ Z.baseSet i) (hj : x ∈ W.baseSet j) :
    Function.Bijective (a.operator i j ⟨x, hi, hj⟩) ↔ Function.Bijective (a.fiberMap x) := by
  rw [a.operator_eq, inChartCoordinates_def, ContinuousLinearMap.coe_comp,
    ContinuousLinearMap.coe_comp,
    (W.coordChange_bijective (W.mem_baseSet_at x) hj).of_comp_iff',
    (Z.coordChange_bijective hi (Z.mem_baseSet_at x)).of_comp_iff]

/-- Invert a fibrewise bijective coordinate morphism between vector bundle cores modelled on finite
coordinate spaces `α → 𝕜` and `β → 𝕜`, without assuming `CompleteSpace 𝕜`. -/
noncomputable def invOfBijectivePi {α β : Type*} [Fintype α] [Fintype β]
    (Z : VectorBundleCore 𝕜 B (α → 𝕜) ι) (W : VectorBundleCore 𝕜 B (β → 𝕜) κ)
    (a : CoordinateHom Z W) (ha : ∀ x, Function.Bijective (a.fiberMap x)) :
    CoordinateHom W Z where
  operator i j :=
    ⟨fun z ↦ (a.operator j i ⟨z.1, z.2.2, z.2.1⟩).inverse,
      ((a.operator j i).continuous.comp
        (continuous_subtype_val.subtype_mk fun z ↦ ⟨z.2.2, z.2.1⟩)).pi_clm_inverse
        fun z ↦ (a.operator_bijective_iff z.2.2 z.2.1).2 (ha z.1)⟩
  compatible i i' j j' x hi hi' hj hj' v := by
    simp only [ContinuousMap.coe_mk]
    have hbij_ij := (a.operator_bijective_iff hj hi).2 (ha x)
    have hbij_i'j' := (a.operator_bijective_iff hj' hi').2 (ha x)
    have hinv_ij := (a.operator j i ⟨x, hj, hi⟩).isInvertible_of_bijective_pi hbij_ij
    have hinv_i'j' := (a.operator j' i' ⟨x, hj', hi'⟩).isInvertible_of_bijective_pi hbij_i'j'
    apply hinv_i'j'.injective
    rw [hinv_i'j'.self_apply_inverse]
    have hcompat := a.compatible j j' i i' x hj hj' hi hi'
      ((a.operator j i ⟨x, hj, hi⟩).inverse v)
    rw [hinv_ij.self_apply_inverse] at hcompat
    exact hcompat.symm

@[simp]
theorem fiberMap_invOfBijectivePi {α β : Type*} [Fintype α] [Fintype β]
    (Z : VectorBundleCore 𝕜 B (α → 𝕜) ι) (W : VectorBundleCore 𝕜 B (β → 𝕜) κ)
    (a : CoordinateHom Z W) (ha : ∀ x, Function.Bijective (a.fiberMap x)) (x : B) :
    (invOfBijectivePi Z W a ha).fiberMap x = (a.fiberMap x).inverse := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have hinv := (a.fiberMap x).isInvertible_of_bijective_pi (ha x)
  apply hinv.injective
  rw [hinv.self_apply_inverse, (invOfBijectivePi Z W a ha).fiberMap_def, a.fiberMap_def]
  exact ((a.operator (Z.indexAt x) (W.indexAt x) _).isInvertible_of_bijective_pi
    ((a.operator_bijective_iff (Z.mem_baseSet_at x) (W.mem_baseSet_at x)).2
      (ha x))).self_apply_inverse v

end CoordinateHom
end VectorBundleCore
