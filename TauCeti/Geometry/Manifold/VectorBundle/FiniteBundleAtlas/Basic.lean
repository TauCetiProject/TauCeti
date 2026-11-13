/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Topology.VectorBundle.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization

/-!
# Finite atlases of bundle charts

Let `M` be a manifold modelled on `E` and `V → M` a fibre bundle with model fibre `F`. A
`TauCeti.FiniteBundleAtlas E M F V` is a finite cover of `M` by open sets `dom i`, each with compact
closure inside the source of the preferred manifold chart and the base set of the preferred bundle
trivialization at a point `center i`. Every compact Hausdorff manifold modelled on a locally
compact space has one (`TauCeti.FiniteBundleAtlas.nonempty`), even one whose chart domains have
closures inside any prescribed open neighbourhoods of their centres
(`TauCeti.FiniteBundleAtlas.exists_closure_dom_subset`). Such atlases are the finite chart data
from which function spaces of sections, such as Sobolev spaces, are built chartwise.

The same chart domains serve as a finite bundle atlas of any other fibre bundle `V'` over `M` as
soon as their closures also lie in the base sets of the preferred trivializations of `V'`
(`TauCeti.FiniteBundleAtlas.ofBaseSet`); such joint atlases exist on every compact Hausdorff
manifold modelled on a locally compact space
(`TauCeti.FiniteBundleAtlas.exists_closure_dom_subset_baseSet`).

In chart `i` a section `s` is read as the `F`-valued function `A.coord i s` on the open set
`A.image i = chart i '' dom i` of the model space. On the overlap `A.overlap i i'` of two charts,
read in chart `i'`, the coordinates in chart `i'` are the coordinate change of the bundle applied
to the coordinates in chart `i` composed with the chart transition `A.transition i i'`
(`TauCeti.FiniteBundleAtlas.coord_eq_coordChange`). For a `C¹` manifold without boundary modelled
on a real normed space, chart transitions are differentiable on the overlaps
(`TauCeti.FiniteBundleAtlas.differentiableOn_transition`). Charts of manifolds modelled on the
closed upper half-plane are read in `ℂ` in
`TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.HalfPlane`.

## Main definitions

* `TauCeti.FiniteBundleAtlas E M F V`: a finite cover of `M` by relatively compact open sets inside
  preferred manifold and bundle charts.
* `TauCeti.FiniteBundleAtlas.image`, `TauCeti.FiniteBundleAtlas.overlap`: chart images of the chart
  domains and of their pairwise intersections.
* `TauCeti.FiniteBundleAtlas.transition`: the chart transition between two charts.
* `TauCeti.FiniteBundleAtlas.coord`: a section read in a chart.
* `TauCeti.FiniteBundleAtlas.ofBaseSet`: the charts of an atlas of `V` as an atlas of `V'`.

## Main results

* `TauCeti.FiniteBundleAtlas.nonempty`: compact Hausdorff manifolds have finite bundle atlases.
* `TauCeti.FiniteBundleAtlas.exists_closure_dom_subset`,
  `TauCeti.FiniteBundleAtlas.exists_closure_dom_subset_baseSet`: existence of atlases subordinate
  to given neighbourhoods, and of joint atlases.
* `TauCeti.FiniteBundleAtlas.coord_eq_coordChange`: coordinates in two charts differ by the
  coordinate change of the bundle.
* `TauCeti.FiniteBundleAtlas.exists_continuous_coord_eqOn`: functions continuous on the chart
  images and related by these coordinate changes are the chart expressions of a continuous section.
* `TauCeti.FiniteBundleAtlas.differentiableOn_transition`: chart transitions are differentiable.
* `TauCeti.FiniteBundleAtlas.contDiffOn_coord`: the chart coordinates of a `Cᵏ` section of a `Cᵏ`
  vector bundle are `Cᵏ`, on an open set containing the compact image of the closure of the chart
  domain (`TauCeti.FiniteBundleAtlas.chart_image_closure_dom_subset`). More generally, the
  expression of such a section in any chart of the maximal atlas and any trivialization of the
  trivialization atlas is `Cᵏ` (`TauCeti.contDiffOn_trivialization_comp_chart_symm_of_contMDiff`).
-/

public section

noncomputable section

open Bundle Set TopologicalSpace
open scoped Manifold Topology

universe u

namespace TauCeti

section Atlas

variable (E : Type u) [TopologicalSpace E] (M : Type*) [TopologicalSpace M] [ChartedSpace E M]
  (F : Type*) [TopologicalSpace F] (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]

/-- A finite atlas of bundle charts: finitely many open sets `dom i` covering `M`, each with compact
closure contained in the source of the preferred manifold chart `chartAt E (center i)` and in the
base set of the preferred trivialization `trivializationAt F V (center i)`. Relative compactness
makes continuous functions on these chart sources and base sets, such as the coordinate changes of
the bundle, bounded on the chart domains. -/
structure FiniteBundleAtlas where
  /-- The number of charts. -/
  n : ℕ
  /-- The point whose preferred charts are used for the `i`th chart. -/
  center : Fin n → M
  /-- The domain of the `i`th chart. -/
  dom : Fin n → Set M
  isOpen_dom : ∀ i, IsOpen (dom i)
  isCompact_closure_dom : ∀ i, IsCompact (closure (dom i))
  closure_dom_subset_source : ∀ i, closure (dom i) ⊆ (chartAt E (center i)).source
  closure_dom_subset_baseSet : ∀ i, closure (dom i) ⊆ (trivializationAt F V (center i)).baseSet
  iUnion_dom : ⋃ i, dom i = univ

variable {E M F V}
  {F' : Type*} [TopologicalSpace F'] {V' : M → Type*} [TopologicalSpace (TotalSpace F' V')]
  [∀ x, TopologicalSpace (V' x)] [FiberBundle F' V']

namespace FiniteBundleAtlas

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

/-- A compact Hausdorff manifold modelled on a locally compact space has a finite bundle atlas. -/
theorem nonempty [LocallyCompactSpace E] [CompactSpace M] [T2Space M] :
    Nonempty (FiniteBundleAtlas E M F V) :=
  (exists_closure_dom_subset (fun _ ↦ univ) (fun _ ↦ isOpen_univ) fun _ ↦ mem_univ _).elim
    fun A _ ↦ ⟨A⟩

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

/-- The manifold chart of the `i`th bundle chart. -/
abbrev chart (i : Fin A.n) : OpenPartialHomeomorph M E :=
  chartAt E (A.center i)

/-- The bundle trivialization of the `i`th bundle chart. -/
abbrev triv (i : Fin A.n) : Trivialization F (π F V) :=
  trivializationAt F V (A.center i)

theorem dom_subset_chart_source (i : Fin A.n) : A.dom i ⊆ (A.chart i).source :=
  subset_closure.trans (A.closure_dom_subset_source i)

theorem dom_subset_baseSet (i : Fin A.n) : A.dom i ⊆ (A.triv i).baseSet :=
  subset_closure.trans (A.closure_dom_subset_baseSet i)

theorem exists_mem_dom (x : M) : ∃ i, x ∈ A.dom i :=
  mem_iUnion.1 (A.iUnion_dom ▸ mem_univ x)

/-- The open set `chart i '' dom i` of the model space on which sections are read in chart `i`. -/
def image (i : Fin A.n) : Opens E :=
  ⟨A.chart i '' A.dom i, (A.chart i).isOpen_image_of_subset_source (A.isOpen_dom i)
    (A.dom_subset_chart_source i)⟩

theorem mem_image {i : Fin A.n} {y : E} : y ∈ A.image i ↔ y ∈ A.chart i '' A.dom i :=
  Iff.rfl

/-- The overlap of the domains of charts `i` and `i'`, in the coordinates of chart `i'`. -/
def overlap (i i' : Fin A.n) : Set E :=
  A.chart i' '' (A.dom i ∩ A.dom i')

theorem mem_overlap {i i' : Fin A.n} {y : E} :
    y ∈ A.overlap i i' ↔ y ∈ A.chart i' '' (A.dom i ∩ A.dom i') :=
  Iff.rfl

theorem chart_mem_overlap {i i' : Fin A.n} {x : M} (hx : x ∈ A.dom i) (hx' : x ∈ A.dom i') :
    A.chart i' x ∈ A.overlap i i' :=
  ⟨x, ⟨hx, hx'⟩, rfl⟩

theorem isOpen_overlap (i i' : Fin A.n) : IsOpen (A.overlap i i') :=
  (A.chart i').isOpen_image_of_subset_source ((A.isOpen_dom i).inter (A.isOpen_dom i'))
    (inter_subset_right.trans (A.dom_subset_chart_source i'))

theorem overlap_subset_image (i i' : Fin A.n) : A.overlap i i' ⊆ A.image i' :=
  image_mono inter_subset_right

/-- The chart transition from chart `i'` to chart `i`. -/
def transition (i i' : Fin A.n) (y : E) : E :=
  A.chart i ((A.chart i').symm y)

theorem transition_chart {i i' : Fin A.n} {x : M} (hx : x ∈ A.dom i') :
    A.transition i i' (A.chart i' x) = A.chart i x := by
  rw [transition, (A.chart i').left_inv (A.dom_subset_chart_source i' hx)]

theorem transition_mem_overlap {i i' : Fin A.n} {y : E} (hy : y ∈ A.overlap i i') :
    A.transition i i' y ∈ A.overlap i' i := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [transition_chart A hx.2]
  exact ⟨x, ⟨hx.2, hx.1⟩, rfl⟩

theorem transition_transition {i i' : Fin A.n} {y : E} (hy : y ∈ A.overlap i i') :
    A.transition i' i (A.transition i i' y) = y := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [transition_chart A hx.2, transition_chart A hx.1]

/-- A section read in chart `i`: its coordinates in the trivialization of chart `i`, as a function
on the model space of `M`. -/
def coord (i : Fin A.n) (s : ∀ x, V x) (y : E) : F :=
  (A.triv i ⟨(A.chart i).symm y, s ((A.chart i).symm y)⟩).2

theorem coord_def (i : Fin A.n) (s : ∀ x, V x) (y : E) :
    A.coord i s y = (A.triv i ⟨(A.chart i).symm y, s ((A.chart i).symm y)⟩).2 :=
  (rfl)

theorem coord_chart {i : Fin A.n} (s : ∀ x, V x) {x : M} (hx : x ∈ A.dom i) :
    A.coord i s (A.chart i x) = (A.triv i ⟨x, s x⟩).2 := by
  rw [coord, (A.chart i).left_inv (A.dom_subset_chart_source i hx)]

theorem symm_mem_dom {i : Fin A.n} {y : E} (hy : y ∈ A.image i) : (A.chart i).symm y ∈ A.dom i := by
  obtain ⟨x, hx, rfl⟩ := hy
  rwa [(A.chart i).left_inv (A.dom_subset_chart_source i hx)]

/-- The inverse of chart `i` is continuous on the chart image `A.image i`. -/
theorem continuousOn_chart_symm (i : Fin A.n) : ContinuousOn (A.chart i).symm (A.image i) :=
  (A.chart i).continuousOn_symm.mono fun y hy ↦ by
    obtain ⟨x, hx, rfl⟩ := A.mem_image.1 hy
    exact (A.chart i).map_source (A.dom_subset_chart_source i hx)

/-- The chart expression in chart `i` of a continuous section is continuous on `A.image i`. -/
theorem continuousOn_coord {s : ∀ x, V x} (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x))
    (i : Fin A.n) : ContinuousOn (A.coord i s) (A.image i) := by
  refine (continuous_snd.comp_continuousOn ((A.triv i).continuousOn.comp
    (hs.comp_continuousOn (A.continuousOn_chart_symm i)) fun y hy ↦ ?_)).congr fun y _ ↦
      A.coord_def i s y
  exact (A.triv i).mem_source.2 (A.dom_subset_baseSet i (A.symm_mem_dom hy))

/-- The image under chart `i` of the closure of its domain is a compact set. -/
theorem isCompact_chart_image_closure_dom (i : Fin A.n) :
    IsCompact (A.chart i '' closure (A.dom i)) :=
  (A.isCompact_closure_dom i).image_of_continuousOn
    ((A.chart i).continuousOn.mono (A.closure_dom_subset_source i))

/-- The image of chart `i` lies in the image of the closure of the chart domain. -/
theorem image_subset_chart_image_closure_dom (i : Fin A.n) :
    (A.image i : Set E) ⊆ A.chart i '' closure (A.dom i) := fun _ hy ↦
  image_mono subset_closure (A.mem_image.1 hy)

/-- The image under chart `i` of the closure of its domain consists of points of the chart target
whose preimage lies in the base set of the bundle chart. -/
theorem chart_image_closure_dom_subset (i : Fin A.n) :
    A.chart i '' closure (A.dom i) ⊆
      (A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.triv i).baseSet := by
  rintro _ ⟨x, hx, rfl⟩
  have hs := A.closure_dom_subset_source i hx
  refine ⟨(A.chart i).map_source hs, ?_⟩
  rw [mem_preimage, (A.chart i).left_inv hs]
  exact A.closure_dom_subset_baseSet i hx

/-- The closure of the image of chart `i` lies in the image of the closure of the chart domain. -/
theorem closure_image_subset_chart_image_closure_dom [T2Space E] (i : Fin A.n) :
    closure (A.image i : Set E) ⊆ A.chart i '' closure (A.dom i) :=
  closure_minimal (A.image_subset_chart_image_closure_dom i)
    (A.isCompact_chart_image_closure_dom i).isClosed

/-- The image of chart `i` has compact closure. -/
theorem isCompact_closure_image [T2Space E] (i : Fin A.n) :
    IsCompact (closure (A.image i : Set E)) :=
  (A.isCompact_chart_image_closure_dom i).closure_of_subset
    (A.image_subset_chart_image_closure_dom i)

/-- The closure of the image of chart `i` lies in the chart target. -/
theorem closure_image_subset_target [T2Space E] (i : Fin A.n) :
    closure (A.image i : Set E) ⊆ (A.chart i).target :=
  (A.closure_image_subset_chart_image_closure_dom i).trans
    ((A.chart_image_closure_dom_subset i).trans inter_subset_left)

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

end FiniteBundleAtlas

end Atlas

section Coordinates

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] {F : Type*} [TopologicalSpace F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V]

namespace FiniteBundleAtlas

variable (A : FiniteBundleAtlas E M F V)

/-- Chart transitions are differentiable on the overlap of the chart domains. -/
theorem differentiableOn_transition [IsManifold 𝓘(ℝ, E) 1 M] (i i' : Fin A.n) :
    DifferentiableOn ℝ (A.transition i i') (A.overlap i i') := by
  refine ((contDiffOn_ext_coord_change (I := 𝓘(ℝ, E)) (A.center i) (A.center i')).differentiableOn
    one_ne_zero).congr_mono (fun y _ ↦ by simp [transition]) ?_
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ (A.chart i').source := A.dom_subset_chart_source i' hx.2
  simp only [PartialEquiv.trans_source, PartialEquiv.symm_source, mem_inter_iff, mem_preimage,
    extChartAt_target, extChartAt_source, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq, range_id, inter_univ,
    preimage_id_eq]
  exact ⟨(A.chart i').map_source hx', by
    rw [(A.chart i').left_inv hx']; exact A.dom_subset_chart_source i hx.1⟩

/-- A `Cⁿ` function on `M`, read in chart `i`, is `Cⁿ` on the chart target. -/
theorem contDiffOn_comp_chart_symm {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {n : WithTop ℕ∞} [IsManifold 𝓘(ℝ, E) n M] {φ : M → G} (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, G) n φ)
    (i : Fin A.n) :
    ContDiffOn ℝ n (fun y ↦ φ ((A.chart i).symm y)) (A.chart i).target := by
  rw [← contMDiffOn_iff_contDiffOn]
  exact hφ.contMDiffOn.comp (t := univ) contMDiffOn_chart_symm fun _ _ ↦ mem_univ _

end FiniteBundleAtlas

end Coordinates

section Linear

variable {E : Type u} [TopologicalSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

namespace FiniteBundleAtlas

variable (A : FiniteBundleAtlas E M F V)

theorem coord_add (i : Fin A.n) (s t : ∀ x, V x) {y : E} (hy : y ∈ A.image i) :
    A.coord i (s + t) y = A.coord i s y + A.coord i t y := by
  have h := A.dom_subset_baseSet i (A.symm_mem_dom hy)
  simp only [coord, Pi.add_apply, ← (A.triv i).continuousLinearMapAt_apply_of_mem (R := ℝ) h,
    map_add]

/-- The chart coordinates of `x ↦ φ x • s x` are those of `s` multiplied by `φ` read in the
chart, because the bundle chart is fibrewise linear. -/
theorem coord_fun_smul (i : Fin A.n) (φ : M → ℝ) (s : ∀ x, V x) {y : E} (hy : y ∈ A.image i) :
    A.coord i (fun x ↦ φ x • s x) y = φ ((A.chart i).symm y) • A.coord i s y := by
  have h := A.dom_subset_baseSet i (A.symm_mem_dom hy)
  simp only [coord, ← (A.triv i).continuousLinearMapAt_apply_of_mem (R := ℝ) h, map_smul]

theorem coord_smul (i : Fin A.n) (c : ℝ) (s : ∀ x, V x) {y : E} (hy : y ∈ A.image i) :
    A.coord i (c • s) y = c • A.coord i s y :=
  A.coord_fun_smul i (fun _ ↦ c) s hy

theorem coord_zero (i : Fin A.n) {y : E} (hy : y ∈ A.image i) : A.coord i (0 : ∀ x, V x) y = 0 := by
  simpa using A.coord_smul i 0 0 hy

/-- On the overlap of two charts, the coordinates of a section in chart `i'` are the coordinate
change applied to its coordinates in chart `i` at the transition point. -/
theorem coord_eq_coordChange {i i' : Fin A.n} (s : ∀ x, V x) {y : E} (hy : y ∈ A.overlap i i') :
    A.coord i' s y = (A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y)
      (A.coord i s (A.transition i i' y)) := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [transition_chart A hx.2, coord_chart A s hx.1, coord_chart A s hx.2,
    (A.chart i').left_inv (A.dom_subset_chart_source i' hx.2),
    Trivialization.coordChangeL_apply _ _
      ⟨A.dom_subset_baseSet i hx.1, A.dom_subset_baseSet i' hx.2⟩,
    (A.triv i).symm_apply_apply_mk (A.dom_subset_baseSet i hx.1)]

/-- **Gluing chart expressions.** Functions `g i`, continuous on the chart images `A.image i` and
related on every overlap by the coordinate changes of the bundle, are the chart expressions of a
continuous section. -/
theorem exists_continuous_coord_eqOn {g : Fin A.n → E → F}
    (hg : ∀ i, ContinuousOn (g i) (A.image i))
    (hcompat : ∀ i i', EqOn (g i')
      (fun y ↦ (A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y)
        (g i (A.transition i i' y))) (A.overlap i i')) :
    ∃ t : ∀ x, V x, Continuous (fun x ↦ TotalSpace.mk' F x (t x)) ∧
      ∀ i, EqOn (A.coord i t) (g i) (A.image i) := by
  -- The section read off from the function of a chosen chart at each point.
  let idx : M → Fin A.n := fun x ↦ (A.exists_mem_dom x).choose
  have hidx (x : M) : x ∈ A.dom (idx x) := (A.exists_mem_dom x).choose_spec
  let t : ∀ x, V x := fun x ↦ (A.triv (idx x)).symm x (g (idx x) (A.chart (idx x) x))
  have hcoord (i : Fin A.n) : EqOn (A.coord i t) (g i) (A.image i) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := A.mem_image.1 hy
    have hov : A.chart i x ∈ A.overlap (idx x) i := A.chart_mem_overlap (hidx x) hx
    rw [hcompat (idx x) i hov, A.coord_chart t hx]
    beta_reduce
    rw [A.transition_chart hx,
      (A.chart i).left_inv (A.dom_subset_chart_source i hx),
      Trivialization.coordChangeL_apply _ _
        ⟨A.dom_subset_baseSet _ (hidx x), A.dom_subset_baseSet i hx⟩]
  refine ⟨t, continuous_iff_continuousAt.2 fun x₀ ↦ ?_, hcoord⟩
  obtain ⟨i, hx₀⟩ := A.exists_mem_dom x₀
  -- On `A.dom i` the section is the inverse of the trivialization of chart `i` applied to the
  -- function of chart `i`.
  have heq : EqOn (fun x ↦ TotalSpace.mk' F x (t x))
      ((fun z : M × F ↦ TotalSpace.mk' F z.1 ((A.triv i).symm z.1 z.2)) ∘
        fun x ↦ (x, g i (A.chart i x))) (A.dom i) := by
    intro x hx
    simp only [Function.comp_apply]
    rw [← hcoord i (A.mem_image.2 ⟨x, hx, rfl⟩), A.coord_chart t hx,
      (A.triv i).symm_apply_apply_mk (A.dom_subset_baseSet i hx)]
  have hcont : ContinuousOn
      ((fun z : M × F ↦ TotalSpace.mk' F z.1 ((A.triv i).symm z.1 z.2)) ∘
        fun x ↦ (x, g i (A.chart i x))) (A.dom i) :=
    (A.triv i).continuousOn_symm.comp (continuousOn_id.prodMk ((hg i).comp
      ((A.chart i).continuousOn.mono (A.dom_subset_chart_source i))
        fun x hx ↦ A.mem_image.2 ⟨x, hx, rfl⟩))
      fun x hx ↦ ⟨A.dom_subset_baseSet i hx, mem_univ _⟩
  exact (hcont.congr heq).continuousAt ((A.isOpen_dom i).mem_nhds hx₀)

end FiniteBundleAtlas

end Linear

section Smooth

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {k : ℕ} [IsManifold 𝓘(ℝ, E) k M] [ContMDiffVectorBundle k F V 𝓘(ℝ, E)]

namespace FiniteBundleAtlas

variable (A : FiniteBundleAtlas E M F V)

/-- **The chart coordinates of a `Cᵏ` section are `Cᵏ`** on the open set of points of the chart
target whose preimage lies in the base set of the bundle chart. This is
`TauCeti.contDiffOn_trivialization_comp_chart_symm_of_contMDiff` for the charts and trivializations
of `A`. -/
theorem contDiffOn_coord {s : ∀ x, V x}
    (hs : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) k fun x ↦ TotalSpace.mk' F x (s x))
    (i : Fin A.n) :
    ContDiffOn ℝ k (A.coord i s)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.triv i).baseSet) :=
  (contDiffOn_trivialization_comp_chart_symm_of_contMDiff hs
    (IsManifold.chart_mem_maximalAtlas _) (A.triv i)).congr fun y _ ↦ A.coord_def i s y

end FiniteBundleAtlas

end Smooth

end TauCeti
