/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Basic

/-!
# Finite bundle atlases of derived bundles

A `TauCeti.FiniteBundleAtlas E M F V` is a finite cover of `M` by relatively compact open sets
`dom i` inside the preferred manifold chart and the preferred trivialization of `V` at a point
`center i`. The same chart domains serve as a finite bundle atlas of any other fibre bundle `V'`
over `M` as soon as their closures also lie in the base sets of the preferred trivializations of
`V'` (`TauCeti.FiniteBundleAtlas.ofBaseSet`). This file uses this to build atlases of bundles
constructed from `V` and `V'`, so that function spaces of sections of these bundles are built on
the same charts as those of `V` and `V'`:

* the fibrewise product `V ×ᵇ V'` (`TauCeti.FiniteBundleAtlas.prod`), whose sections are read in
  each chart as the pair of the readings of their components
  (`TauCeti.FiniteBundleAtlas.coord_prod`);
* the bundle of continuous linear maps `x ↦ V₁ x →L[ℝ] V₂ x` of two real vector bundles
  (`TauCeti.FiniteBundleAtlas.hom`), whose sections are read in each chart through
  `ContinuousLinearMap.inCoordinates` (`TauCeti.FiniteBundleAtlas.coord_hom`), so that applying a
  section of the hom bundle to a section of `V₁` is applying the chart readings pointwise
  (`TauCeti.FiniteBundleAtlas.coord_hom_apply`);
* the bundle `x ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ] V x` of `V`-valued one-forms
  (`TauCeti.FiniteBundleAtlas.tangentHom`), which needs no hypothesis because the preferred
  trivialization of the tangent bundle has the chart source as its base set.

Every compact Hausdorff manifold modelled on a locally compact space has a finite bundle atlas
whose chart domains have closures inside any prescribed open neighbourhoods of their centres
(`TauCeti.FiniteBundleAtlas.exists_closure_dom_subset`), in particular a joint atlas for two fibre
bundles (`TauCeti.FiniteBundleAtlas.exists_closure_dom_subset_baseSet`).

## Main definitions

* `TauCeti.FiniteBundleAtlas.ofBaseSet`: the charts of an atlas of `V` as an atlas of `V'`.
* `TauCeti.FiniteBundleAtlas.prod`: the atlas of `V ×ᵇ V'` on the charts of an atlas of `V`.
* `TauCeti.FiniteBundleAtlas.hom`: the atlas of the hom bundle of `V₁` and `V₂` on the charts of an
  atlas of `V₁`.
* `TauCeti.FiniteBundleAtlas.tangent`: the charts of an atlas of `V` as an atlas of the tangent
  bundle.
* `TauCeti.FiniteBundleAtlas.tangentHom`: the atlas of the bundle of `V`-valued one-forms on the
  charts of an atlas of `V`.

## Main results

* `TauCeti.FiniteBundleAtlas.exists_closure_dom_subset`,
  `TauCeti.FiniteBundleAtlas.exists_closure_dom_subset_baseSet`: existence of atlases subordinate
  to given neighbourhoods, and of joint atlases.
* `TauCeti.FiniteBundleAtlas.coord_prod`, `TauCeti.FiniteBundleAtlas.coord_hom`,
  `TauCeti.FiniteBundleAtlas.coord_hom_apply`: the chart readings of sections of the derived
  bundles.
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold

universe u

namespace TauCeti

namespace FiniteBundleAtlas

section Fiber

variable {E : Type u} [TopologicalSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [TopologicalSpace F] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  {F' : Type*} [TopologicalSpace F'] {V' : M → Type*} [TopologicalSpace (TotalSpace F' V')]
  [∀ x, TopologicalSpace (V' x)] [FiberBundle F' V']

/-- **Atlases subordinate to given neighbourhoods.** On a compact Hausdorff manifold modelled on a
locally compact space, for every family of open neighbourhoods `U x ∋ x` there is a finite bundle
atlas whose chart domains have closures inside the neighbourhood of their centre. -/
theorem exists_closure_dom_subset [LocallyCompactSpace E] [CompactSpace M] [T2Space M]
    (U : M → Set M) (hU : ∀ x, IsOpen (U x)) (hxU : ∀ x, x ∈ U x) :
    ∃ A : FiniteBundleAtlas E M F V, ∀ i, closure (A.dom i) ⊆ U (A.center i) := by
  have := ChartedSpace.locallyCompactSpace E M
  let W : M → Set M := fun x ↦ U x ∩ ((chartAt E x).source ∩ (trivializationAt F V x).baseSet)
  have hW (x : M) : IsOpen (W x) :=
    (hU x).inter ((chartAt E x).open_source.inter (trivializationAt F V x).open_baseSet)
  have hxW (x : M) : x ∈ W x :=
    ⟨hxU x, mem_chart_source E x, mem_baseSet_trivializationAt F V x⟩
  -- Shrink each `W x` to the interior of a compact neighbourhood of `x` inside it.
  choose K hK hxK hKW using fun x ↦ exists_compact_subset (hW x) (hxW x)
  have hcl (x : M) : closure (interior (K x)) ⊆ W x :=
    (closure_mono interior_subset).trans ((hK x).isClosed.closure_subset.trans (hKW x))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ interior (K x))
    (fun x ↦ isOpen_interior) fun x _ ↦ mem_iUnion.2 ⟨x, hxK x⟩
  let c : Fin t.card → M := fun i ↦ (t.equivFin.symm i).1
  refine ⟨⟨t.card, c, fun i ↦ interior (K (c i)), fun i ↦ isOpen_interior,
    fun i ↦ (hK _).closure_of_subset interior_subset,
    fun i ↦ (hcl _).trans (inter_subset_right.trans inter_subset_left),
    fun i ↦ (hcl _).trans (inter_subset_right.trans inter_subset_right),
    eq_univ_of_forall fun x ↦ ?_⟩, fun i ↦ (hcl _).trans inter_subset_left⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (ht (mem_univ x))
  exact mem_iUnion.2 ⟨t.equivFin ⟨y, hy⟩, by simpa [c] using hxy⟩

variable (F' V') in
/-- **Joint atlases.** A compact Hausdorff manifold modelled on a locally compact space has a
finite bundle atlas of `V` whose chart domains have closures inside the base sets of the preferred
trivializations of a second fibre bundle `V'`, so that the same charts form an atlas of `V'`
(`TauCeti.FiniteBundleAtlas.ofBaseSet`). -/
theorem exists_closure_dom_subset_baseSet [LocallyCompactSpace E] [CompactSpace M] [T2Space M] :
    ∃ A : FiniteBundleAtlas E M F V,
      ∀ i, closure (A.dom i) ⊆ (trivializationAt F' V' (A.center i)).baseSet :=
  exists_closure_dom_subset _ (fun x ↦ (trivializationAt F' V' x).open_baseSet)
    fun x ↦ mem_baseSet_trivializationAt F' V' x

variable (A : FiniteBundleAtlas E M F V)

/-- The charts of a finite bundle atlas of `V` as a finite bundle atlas of a second fibre bundle
`V'`, when the closures of the chart domains lie in the base sets of the preferred trivializations
of `V'`: the number of charts, the centres and the chart domains are unchanged. -/
@[expose, simps n center dom]
def ofBaseSet (h : ∀ i, closure (A.dom i) ⊆ (trivializationAt F' V' (A.center i)).baseSet) :
    FiniteBundleAtlas E M F' V' where
  n := A.n
  center := A.center
  dom := A.dom
  isOpen_dom := A.isOpen_dom
  isCompact_closure_dom := A.isCompact_closure_dom
  closure_dom_subset_source := A.closure_dom_subset_source
  closure_dom_subset_baseSet := h
  iUnion_dom := A.iUnion_dom

section OfBaseSet

variable {A} {h : ∀ i, closure (A.dom i) ⊆ (trivializationAt F' V' (A.center i)).baseSet}

@[simp]
theorem image_ofBaseSet (i : Fin A.n) : (A.ofBaseSet h).image i = A.image i :=
  SetLike.ext fun _ ↦ (mem_image (A := A.ofBaseSet h) (i := i)).trans (mem_image (A := A)).symm

@[simp]
theorem overlap_ofBaseSet (i i' : Fin A.n) : (A.ofBaseSet h).overlap i i' = A.overlap i i' :=
  Set.ext fun _ ↦ (mem_overlap (A := A.ofBaseSet h) (i := i) (i' := i')).trans
    (mem_overlap (A := A)).symm

end OfBaseSet

variable [∀ x, Zero (V x)] [∀ x, Zero (V' x)]

/-- The finite bundle atlas of the fibrewise product `V ×ᵇ V'` on the charts of a finite bundle
atlas of `V`, when the closures of the chart domains also lie in the base sets of the preferred
trivializations of `V'`. The preferred trivialization of `V ×ᵇ V'` is the product of those of `V`
and `V'`, with the intersection of their base sets as its base set. -/
@[expose, simps n center dom]
def prod (h : ∀ i, closure (A.dom i) ⊆ (trivializationAt F' V' (A.center i)).baseSet) :
    FiniteBundleAtlas E M (F × F') (V ×ᵇ V') where
  n := A.n
  center := A.center
  dom := A.dom
  isOpen_dom := A.isOpen_dom
  isCompact_closure_dom := A.isCompact_closure_dom
  closure_dom_subset_source := A.closure_dom_subset_source
  closure_dom_subset_baseSet i := subset_inter (A.closure_dom_subset_baseSet i) (h i)
  iUnion_dom := A.iUnion_dom

/-- A section of `V ×ᵇ V'` read in a chart of `A.prod h` is the pair of its components read in the
corresponding charts of `A` and `A.ofBaseSet h`. -/
theorem coord_prod (h : ∀ i, closure (A.dom i) ⊆ (trivializationAt F' V' (A.center i)).baseSet)
    (i : Fin A.n) (s : ∀ x, (V ×ᵇ V') x) (y : E) :
    (A.prod h).coord i s y =
      (A.coord i (fun x ↦ (s x).1) y, (A.ofBaseSet h).coord i (fun x ↦ (s x).2) y) := by
  rw [coord_def (A.prod h) i, coord_def A i, coord_def (A.ofBaseSet h) i]
  rfl

end Fiber

section Hom

variable {E : Type u} [TopologicalSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] {V₁ : M → Type*}
  [TopologicalSpace (TotalSpace F₁ V₁)] [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] {V₂ : M → Type*}
  [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]

variable (A : FiniteBundleAtlas E M F₁ V₁)

/-- The finite bundle atlas of the bundle `x ↦ V₁ x →L[ℝ] V₂ x` of continuous linear maps on the
charts of a finite bundle atlas of `V₁`, when the closures of the chart domains also lie in the
base sets of the preferred trivializations of `V₂`. The preferred trivialization of the hom bundle
is built from those of `V₁` and `V₂`, with the intersection of their base sets as its base set
(`hom_trivializationAt_baseSet`). -/
@[expose, simps n center dom]
def hom (h : ∀ i, closure (A.dom i) ⊆ (trivializationAt F₂ V₂ (A.center i)).baseSet) :
    FiniteBundleAtlas E M (F₁ →L[ℝ] F₂) (fun x ↦ V₁ x →L[ℝ] V₂ x) where
  n := A.n
  center := A.center
  dom := A.dom
  isOpen_dom := A.isOpen_dom
  isCompact_closure_dom := A.isCompact_closure_dom
  closure_dom_subset_source := A.closure_dom_subset_source
  closure_dom_subset_baseSet i := by
    rw [hom_trivializationAt_baseSet]
    exact subset_inter (A.closure_dom_subset_baseSet i) (h i)
  iUnion_dom := A.iUnion_dom

variable (h : ∀ i, closure (A.dom i) ⊆ (trivializationAt F₂ V₂ (A.center i)).baseSet)

/-- A section of the hom bundle read in a chart of `A.hom h` is its value at the corresponding
point of `M` expressed in the preferred trivializations of `V₁` and `V₂` at the centre of the
chart (`hom_trivializationAt_apply`). -/
theorem coord_hom (i : Fin A.n) (φ : ∀ x, V₁ x →L[ℝ] V₂ x) (y : E) :
    (A.hom h).coord i φ y =
      ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ (A.center i) ((A.chart i).symm y)
        (A.center i) ((A.chart i).symm y) (φ ((A.chart i).symm y)) := by
  rw [coord_def (A.hom h) i, hom_trivializationAt_apply]
  rfl

/-- **Hom sections act chartwise.** On the image of a chart, applying the chart reading of a
section `φ` of the hom bundle to the chart reading of a section `s` of `V₁` gives the chart reading
of the section `x ↦ φ x (s x)` of `V₂`. -/
theorem coord_hom_apply (i : Fin A.n) (φ : ∀ x, V₁ x →L[ℝ] V₂ x) (s : ∀ x, V₁ x) {y : E}
    (hy : y ∈ A.image i) :
    (A.hom h).coord i φ y (A.coord i s y) = (A.ofBaseSet h).coord i (fun x ↦ φ x (s x)) y := by
  have hdom := A.symm_mem_dom hy
  have h₁ := A.dom_subset_baseSet i hdom
  have h₂ : (A.chart i).symm y ∈ (trivializationAt F₂ V₂ (A.center i)).baseSet :=
    h i (subset_closure hdom)
  rw [coord_hom, ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, Trivialization.symmL_apply _ h₁, coord_def,
    Trivialization.symm_apply_apply_mk _ h₁,
    Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ h₂, coord_def (A.ofBaseSet h) i]
  rfl

end Hom

section Tangent

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
  {F : Type*} [TopologicalSpace F] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]

variable (A : FiniteBundleAtlas E M F V)

/-- The charts of a finite bundle atlas of `V` as a finite bundle atlas of the tangent bundle of
`M`. No hypothesis is needed: the preferred trivialization of the tangent bundle at a point has
the source of the preferred chart as its base set (`TangentBundle.trivializationAt_baseSet`). -/
abbrev tangent : FiniteBundleAtlas E M E (TangentSpace 𝓘(ℝ, E)) :=
  A.ofBaseSet A.closure_dom_subset_source

end Tangent

section TangentHom

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]

variable (A : FiniteBundleAtlas E M F V)

/-- The finite bundle atlas of the bundle `x ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ] V x` of `V`-valued
one-forms on the charts of a finite bundle atlas of `V`. -/
abbrev tangentHom :
    FiniteBundleAtlas E M (E →L[ℝ] F) (fun x ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ] V x) :=
  A.tangent.hom A.closure_dom_subset_baseSet

/-- On the image of a chart, applying the chart reading of a `V`-valued one-form `ω` to the chart
reading of a vector field `v` gives the chart reading of the section `x ↦ ω x (v x)` of `V`. -/
theorem coord_tangentHom_apply (i : Fin A.n) (ω : ∀ x, TangentSpace 𝓘(ℝ, E) x →L[ℝ] V x)
    (v : ∀ x, TangentSpace 𝓘(ℝ, E) x) {y : E} (hy : y ∈ A.image i) :
    A.tangentHom.coord i ω y (A.tangent.coord i v y) = A.coord i (fun x ↦ ω x (v x)) y :=
  A.tangent.coord_hom_apply A.closure_dom_subset_baseSet i ω v
    (A.tangent.mem_image.2 (A.mem_image.1 hy))

end TangentHom

end FiniteBundleAtlas

end TauCeti
