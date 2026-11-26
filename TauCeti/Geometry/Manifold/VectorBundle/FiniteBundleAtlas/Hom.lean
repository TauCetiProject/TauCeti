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
import TauCeti.Topology.VectorBundle.Coordinates

/-!
# Finite bundle atlases of derived bundles

The charts of a `TauCeti.FiniteBundleAtlas H M F V` serve as a finite bundle atlas of a second
fibre bundle `V'` whose preferred trivializations contain the closures of the chart domains
(`TauCeti.FiniteBundleAtlas.ofBaseSet`). This file uses this to build atlases of bundles
constructed from `V` and `V'`, so that function spaces of sections of these bundles are built on
the same charts as those of `V` and `V'`:

* the fibrewise product `V ×ᵇ V'` (`TauCeti.FiniteBundleAtlas.prod`), whose sections are read in
  each chart as the pair of the readings of their components
  (`TauCeti.FiniteBundleAtlas.coord_prod`);
* the bundle of continuous linear maps `x ↦ V₁ x →L[𝕜] V₂ x` of two vector bundles over a
  nontrivially normed field `𝕜` (`TauCeti.FiniteBundleAtlas.hom`), whose sections are read in
  each chart through `ContinuousLinearMap.inCoordinates` (`TauCeti.FiniteBundleAtlas.coord_hom`),
  so that applying a section of the hom bundle to a section of `V₁` is applying the chart readings
  pointwise (`TauCeti.FiniteBundleAtlas.coord_hom_apply`);
* the bundle `x ↦ TangentSpace I x →L[𝕜] V x` of `V`-valued one-forms for a model with corners
  `I : ModelWithCorners 𝕜 E H` (`TauCeti.FiniteBundleAtlas.tangentHom`), which needs no hypothesis
  because the preferred trivialization of the tangent bundle has the chart source as its base set.

Joint atlases of two bundles exist on every compact Hausdorff manifold modelled on a locally
compact space (`TauCeti.FiniteBundleAtlas.exists_closure_dom_subset_baseSet`).

## Main definitions

* `TauCeti.FiniteBundleAtlas.prod`: the atlas of `V ×ᵇ V'` on the charts of an atlas of `V`.
* `TauCeti.FiniteBundleAtlas.hom`: the atlas of the hom bundle of `V₁` and `V₂` on the charts of an
  atlas of `V₁`.
* `TauCeti.FiniteBundleAtlas.tangent`: the charts of an atlas of `V` as an atlas of the tangent
  bundle `TangentSpace I`.
* `TauCeti.FiniteBundleAtlas.tangentHom`: the atlas of the bundle of `V`-valued one-forms on the
  charts of an atlas of `V`.

## Main results

* `TauCeti.FiniteBundleAtlas.coord_prod`, `TauCeti.FiniteBundleAtlas.coord_hom`,
  `TauCeti.FiniteBundleAtlas.coord_hom_apply`, `TauCeti.FiniteBundleAtlas.coord_tangentHom`,
  `TauCeti.FiniteBundleAtlas.coord_tangentHom_apply`: the chart readings of sections of the derived
  bundles.
* `TauCeti.FiniteBundleAtlas.coord_hom_eq_coordChange`,
  `TauCeti.FiniteBundleAtlas.coord_tangentHom_eq_coordChange`: on an overlap, the readings of a
  section of the hom bundle in two charts differ by the coordinate changes of both bundles; in the
  boundaryless case `I = 𝓘(𝕜, E)`, for a `V`-valued one-form these are the derivative of the chart
  transition (`TauCeti.FiniteBundleAtlas.fderiv_transition`) and the coordinate change of `V`.
* `TauCeti.FiniteBundleAtlas.image_tangentHom`, `TauCeti.FiniteBundleAtlas.overlap_tangentHom`,
  `TauCeti.FiniteBundleAtlas.transition_tangentHom`: the atlas of `V`-valued one-forms has the
  chart images, overlaps and transitions of `A`.
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

variable (A : FiniteBundleAtlas E M F V)

variable [∀ x, Zero (V x)] [∀ x, Zero (V' x)]

/-- The finite bundle atlas of the fibrewise product `V ×ᵇ V'` on the charts of a finite bundle
atlas of `V`, when the closures of the chart domains also lie in the base sets of the preferred
trivializations of `V'`. The preferred trivialization of `V ×ᵇ V'` is the product of those of `V`
and `V'`, with the intersection of their base sets as its base set. -/
@[expose, simps! n center dom]
def prod (h : ∀ i, closure (A.dom i) ⊆ (trivializationAt F' V' (A.center i)).baseSet) :
    FiniteBundleAtlas E M (F × F') (V ×ᵇ V') :=
  A.ofBaseSet fun i ↦ subset_inter (A.closure_dom_subset_baseSet i) (h i)

section Prod

variable {A} {h : ∀ i, closure (A.dom i) ⊆ (trivializationAt F' V' (A.center i)).baseSet}

@[simp]
theorem chart_prod (i : Fin A.n) : (A.prod h).chart i = A.chart i :=
  rfl

@[simp]
theorem image_prod (i : Fin A.n) : (A.prod h).image i = A.image i :=
  image_ofBaseSet i

@[simp]
theorem overlap_prod (i i' : Fin A.n) : (A.prod h).overlap i i' = A.overlap i i' :=
  overlap_ofBaseSet i i'

@[simp]
theorem transition_prod (i i' : Fin A.n) : (A.prod h).transition i i' = A.transition i i' :=
  transition_ofBaseSet i i'

end Prod

/-- A section of `V ×ᵇ V'` read in a chart of `A.prod h` is the pair of its components read in the
corresponding charts of `A` and `A.ofBaseSet h`. -/
theorem coord_prod (h : ∀ i, closure (A.dom i) ⊆ (trivializationAt F' V' (A.center i)).baseSet)
    (i : Fin A.n) (s : ∀ x, (V ×ᵇ V') x) (y : E) :
    (A.prod h).coord i s y =
      (A.coord i (fun x ↦ (s x).fst) y, (A.ofBaseSet h).coord i (fun x ↦ (s x).snd) y) := by
  rw [coord_def (A.prod h) i, coord_def A i, coord_def (A.ofBaseSet h) i]
  rfl

end Fiber

section Hom

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type u} [TopologicalSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {V₁ : M → Type*}
  [TopologicalSpace (TotalSpace F₁ V₁)] [∀ x, AddCommGroup (V₁ x)] [∀ x, Module 𝕜 (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {V₂ : M → Type*}
  [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul 𝕜 (V₂ x)]

variable (A : FiniteBundleAtlas E M F₁ V₁)

/-- The finite bundle atlas of the bundle `x ↦ V₁ x →L[𝕜] V₂ x` of continuous linear maps on the
charts of a finite bundle atlas of `V₁`, when the closures of the chart domains also lie in the
base sets of the preferred trivializations of `V₂`. The preferred trivialization of the hom bundle
is built from those of `V₁` and `V₂`, with the intersection of their base sets as its base set
(`hom_trivializationAt_baseSet`). -/
@[expose, simps! n center dom]
def hom (h : ∀ i, closure (A.dom i) ⊆ (trivializationAt F₂ V₂ (A.center i)).baseSet) :
    FiniteBundleAtlas E M (F₁ →L[𝕜] F₂) (fun x ↦ V₁ x →L[𝕜] V₂ x) :=
  A.ofBaseSet fun i ↦ by
    rw [hom_trivializationAt_baseSet]
    exact subset_inter (A.closure_dom_subset_baseSet i) (h i)

section HomImage

variable {A} {h : ∀ i, closure (A.dom i) ⊆ (trivializationAt F₂ V₂ (A.center i)).baseSet}

@[simp]
theorem chart_hom (i : Fin A.n) : (A.hom (𝕜 := 𝕜) h).chart i = A.chart i :=
  rfl

@[simp]
theorem image_hom (i : Fin A.n) : (A.hom (𝕜 := 𝕜) h).image i = A.image i :=
  image_ofBaseSet i

@[simp]
theorem overlap_hom (i i' : Fin A.n) : (A.hom (𝕜 := 𝕜) h).overlap i i' = A.overlap i i' :=
  overlap_ofBaseSet i i'

@[simp]
theorem transition_hom (i i' : Fin A.n) :
    (A.hom (𝕜 := 𝕜) h).transition i i' = A.transition i i' :=
  transition_ofBaseSet i i'

end HomImage

variable (h : ∀ i, closure (A.dom i) ⊆ (trivializationAt F₂ V₂ (A.center i)).baseSet)

/-- A section of the hom bundle read in a chart of `A.hom h` is its value at the corresponding
point of `M` expressed in the preferred trivializations of `V₁` and `V₂` at the centre of the
chart (`hom_trivializationAt_apply`). -/
theorem coord_hom (i : Fin A.n) (φ : ∀ x, V₁ x →L[𝕜] V₂ x) (y : E) :
    (A.hom h).coord i φ y =
      ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ (A.center i) ((A.chart i).symm y)
        (A.center i) ((A.chart i).symm y) (φ ((A.chart i).symm y)) := by
  rw [coord_def (A.hom h) i, hom_trivializationAt_apply]
  rfl

/-- **Hom sections act chartwise over the base sets.** At every point `y` whose preimage under
chart `i` lies in the base sets of the trivializations of `V₁` and `V₂` at the centre of the chart,
applying the chart reading of a section `φ` of the hom bundle to the chart reading of a section `s`
of `V₁` gives the chart reading of the section `x ↦ φ x (s x)` of `V₂`. -/
theorem coord_hom_apply_of_mem_baseSet (i : Fin A.n) (φ : ∀ x, V₁ x →L[𝕜] V₂ x)
    (s : ∀ x, V₁ x) {y : E} (h₁ : (A.chart i).symm y ∈ (A.triv i).baseSet)
    (h₂ : (A.chart i).symm y ∈ (trivializationAt F₂ V₂ (A.center i)).baseSet) :
    (A.hom h).coord i φ y (A.coord i s y) = (A.ofBaseSet h).coord i (fun x ↦ φ x (s x)) y := by
  rw [coord_hom, ContinuousLinearMap.inCoordinates_eq h₁ h₂, coord_def, coord_def (A.ofBaseSet h) i]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Trivialization.continuousLinearEquivAt_symm_apply, Trivialization.symm_apply_apply_mk _ h₁,
    Trivialization.continuousLinearEquivAt_apply]
  rfl

/-- **Hom sections act chartwise.** On the image of a chart, applying the chart reading of a
section `φ` of the hom bundle to the chart reading of a section `s` of `V₁` gives the chart reading
of the section `x ↦ φ x (s x)` of `V₂`. -/
theorem coord_hom_apply (i : Fin A.n) (φ : ∀ x, V₁ x →L[𝕜] V₂ x) (s : ∀ x, V₁ x) {y : E}
    (hy : y ∈ A.image i) :
    (A.hom h).coord i φ y (A.coord i s y) = (A.ofBaseSet h).coord i (fun x ↦ φ x (s x)) y := by
  have hdom := A.symm_mem_dom hy
  exact A.coord_hom_apply_of_mem_baseSet h i φ s (A.dom_subset_baseSet i hdom)
    (h i (subset_closure hdom))

/-- **Change of chart for hom sections.** On the overlap of charts `i` and `i'`, the reading in
chart `i'` of a section of the hom bundle is its reading in chart `i` at the transition point,
precomposed with the coordinate change of `V₁` and followed by the coordinate change of `V₂`. -/
theorem coord_hom_eq_coordChange {i i' : Fin A.n} (φ : ∀ x, V₁ x →L[𝕜] V₂ x) {y : E}
    (hy : y ∈ A.overlap i i') :
    (A.hom h).coord i' φ y =
      ((trivializationAt F₂ V₂ (A.center i)).coordChangeL 𝕜 (trivializationAt F₂ V₂ (A.center i'))
          ((A.chart i').symm y) : F₂ →L[𝕜] F₂).comp
        (((A.hom h).coord i φ (A.transition i i' y)).comp
          ((A.triv i').coordChangeL 𝕜 (A.triv i) ((A.chart i').symm y) : F₁ →L[𝕜] F₁)) := by
  obtain ⟨x, ⟨hx, hx'⟩, rfl⟩ := A.mem_overlap.1 hy
  rw [transition_chart A hx', coord_hom, coord_hom,
    (A.chart i').left_inv (A.dom_subset_chart_source i' hx'),
    (A.chart i).left_inv (A.dom_subset_chart_source i hx)]
  exact ContinuousLinearMap.inCoordinates_eq_coordChangeL_comp _ (A.dom_subset_baseSet i' hx')
    (A.dom_subset_baseSet i hx) (h i' (subset_closure hx')) (h i (subset_closure hx))

end Hom

section Tangent

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type u} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [TopologicalSpace F] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]

variable (A : FiniteBundleAtlas H M F V) (I : ModelWithCorners 𝕜 E H) [IsManifold I 1 M]

/-- The charts of a finite bundle atlas of `V` as a finite bundle atlas of the tangent bundle of
`M` for the model `I`. No hypothesis is needed: the preferred trivialization of the tangent bundle
at a point has the source of the preferred chart as its base set
(`TangentBundle.trivializationAt_baseSet`). -/
abbrev tangent : FiniteBundleAtlas H M E (TangentSpace I) :=
  A.ofBaseSet A.closure_dom_subset_source

end Tangent

section TangentCoordChange

variable {E : Type u} [NormedAddCommGroup E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [TopologicalSpace F] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  (A : FiniteBundleAtlas E M F V)
  (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [IsManifold 𝓘(𝕜, E) 1 M]

/-- On a boundaryless manifold modelled on `𝓘(𝕜, E)`, on the overlap of charts `i` and `i'`, the
derivative of the chart transition is the coordinate change of the tangent bundle between the
trivializations of the two charts. -/
theorem fderiv_transition {i i' : Fin A.n} {y : E} (hy : y ∈ A.overlap i i') :
    fderiv 𝕜 (A.transition i i') y =
      ((trivializationAt E (TangentSpace 𝓘(𝕜, E)) (A.center i')).coordChangeL 𝕜
        (trivializationAt E (TangentSpace 𝓘(𝕜, E)) (A.center i)) ((A.chart i').symm y) :
          E →L[𝕜] E) := by
  obtain ⟨x, ⟨hx, hx'⟩, rfl⟩ := A.mem_overlap.1 hy
  have hs : x ∈ (A.chart i).source := A.dom_subset_chart_source i hx
  have hs' : x ∈ (A.chart i').source := A.dom_subset_chart_source i' hx'
  -- Near the point, the chart transition is the transition of the preferred extended charts, so
  -- its derivative is the coordinate change of the tangent bundle.
  have heq : A.transition i i' =ᶠ[nhds (A.chart i' x)]
      extChartAt 𝓘(𝕜, E) (A.center i) ∘ (extChartAt 𝓘(𝕜, E) (A.center i')).symm := by
    filter_upwards [(A.image i').isOpen.mem_nhds (A.mem_image.2 ⟨x, hx', rfl⟩)] with y hy
    obtain ⟨x', hx'', rfl⟩ := A.mem_image.1 hy
    rw [transition_chart A hx'']
    simp [(A.chart i').left_inv (A.dom_subset_chart_source i' hx'')]
  have hT : x ∈ (trivializationAt E (TangentSpace 𝓘(𝕜, E)) (A.center i')).baseSet ∩
      (trivializationAt E (TangentSpace 𝓘(𝕜, E)) (A.center i)).baseSet := by
    simpa using ⟨hs', hs⟩
  have hcoord : ((trivializationAt E (TangentSpace 𝓘(𝕜, E)) (A.center i')).coordChangeL 𝕜
      (trivializationAt E (TangentSpace 𝓘(𝕜, E)) (A.center i)) x : E →L[𝕜] E) =
        tangentCoordChange 𝓘(𝕜, E) (A.center i') (A.center i) x :=
    (tangentBundleCore 𝓘(𝕜, E) M).trivializationAt_coordChangeL hT
  rw [(A.chart i').left_inv hs', hcoord, heq.fderiv_eq, tangentCoordChange_def]
  simp only [modelWithCornersSelf_coe, range_id, fderivWithin_univ, extChartAt_coe,
    Function.id_comp]

end TangentCoordChange

section TangentHom

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type u} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]

variable (A : FiniteBundleAtlas H M F V) (I : ModelWithCorners 𝕜 E H) [IsManifold I 1 M]

/-- The finite bundle atlas of the bundle `x ↦ TangentSpace I x →L[𝕜] V x` of `V`-valued
one-forms on the charts of a finite bundle atlas of `V`. -/
abbrev tangentHom :
    FiniteBundleAtlas H M (E →L[𝕜] F) (fun x ↦ TangentSpace I x →L[𝕜] V x) :=
  (A.tangent I).hom A.closure_dom_subset_baseSet

/-- The chart images of the atlas of `V`-valued one-forms are those of `A`. -/
@[simp]
theorem image_tangentHom (i : Fin A.n) : (A.tangentHom I).image i = A.image i :=
  (image_hom (A := A.tangent I) i).trans (image_ofBaseSet i)

/-- The chart overlaps of the atlas of `V`-valued one-forms are those of `A`. -/
@[simp]
theorem overlap_tangentHom (i i' : Fin A.n) :
    (A.tangentHom I).overlap i i' = A.overlap i i' :=
  (overlap_hom (A := A.tangent I) i i').trans (overlap_ofBaseSet i i')

/-- The chart transitions of the atlas of `V`-valued one-forms are those of `A`. -/
@[simp]
theorem transition_tangentHom (i i' : Fin A.n) :
    (A.tangentHom I).transition i i' = A.transition i i' :=
  (transition_hom (A := A.tangent I) i i').trans (transition_ofBaseSet i i')

/-- A `V`-valued one-form read in a chart of `A.tangentHom I` is its value at the corresponding
point of `M` expressed in the preferred trivializations of the tangent bundle and of `V` at the
centre of the chart. -/
theorem coord_tangentHom (i : Fin A.n) (ω : ∀ x, TangentSpace I x →L[𝕜] V x) (y : H) :
    (A.tangentHom I).coord i ω y =
      ContinuousLinearMap.inCoordinates E (TangentSpace I) F V (A.center i)
        ((A.chart i).symm y) (A.center i) ((A.chart i).symm y) (ω ((A.chart i).symm y)) :=
  (A.tangent I).coord_hom A.closure_dom_subset_baseSet i ω y

/-- On the image of a chart, applying the chart reading of a `V`-valued one-form `ω` to the chart
reading of a vector field `v` gives the chart reading of the section `x ↦ ω x (v x)` of `V`. -/
theorem coord_tangentHom_apply (i : Fin A.n) (ω : ∀ x, TangentSpace I x →L[𝕜] V x)
    (v : ∀ x, TangentSpace I x) {y : H} (hy : y ∈ A.image i) :
    (A.tangentHom I).coord i ω y ((A.tangent I).coord i v y) =
      A.coord i (fun x ↦ ω x (v x)) y :=
  (A.tangent I).coord_hom_apply A.closure_dom_subset_baseSet i ω v
    ((A.tangent I).mem_image.2 (A.mem_image.1 hy))

end TangentHom

section TangentHomCoordChange

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(𝕜, E) 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  (A : FiniteBundleAtlas E M F V)

/-- **Change of chart for one-forms.** On a boundaryless manifold modelled on `𝓘(𝕜, E)`, on the
overlap of charts `i` and `i'`, the reading in chart `i'` of a `V`-valued one-form is its reading
in chart `i` at the transition point, precomposed with the derivative of the chart transition and
followed by the coordinate change of `V`. -/
theorem coord_tangentHom_eq_coordChange {i i' : Fin A.n}
    (ω : ∀ x, TangentSpace 𝓘(𝕜, E) x →L[𝕜] V x) {y : E} (hy : y ∈ A.overlap i i') :
    (A.tangentHom 𝓘(𝕜, E)).coord i' ω y =
      ((A.triv i).coordChangeL 𝕜 (A.triv i') ((A.chart i').symm y) : F →L[𝕜] F).comp
        (((A.tangentHom 𝓘(𝕜, E)).coord i ω (A.transition i i' y)).comp
          (fderiv 𝕜 (A.transition i i') y)) := by
  rw [A.fderiv_transition 𝕜 hy, ← transition_ofBaseSet (F' := E) (V' := TangentSpace 𝓘(𝕜, E))
    (h := A.closure_dom_subset_source)]
  exact (A.tangent 𝓘(𝕜, E)).coord_hom_eq_coordChange A.closure_dom_subset_baseSet ω
    ((A.tangent 𝓘(𝕜, E)).mem_overlap.2 (A.mem_overlap.1 hy))

end TangentHomCoordChange

end FiniteBundleAtlas

end TauCeti
