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

The charts of a `TauCeti.FiniteBundleAtlas E M F V` serve as a finite bundle atlas of a second
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
* the bundle `x ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ] V x` of `V`-valued one-forms
  (`TauCeti.FiniteBundleAtlas.tangentHom`), which needs no hypothesis because the preferred
  trivialization of the tangent bundle has the chart source as its base set.

Joint atlases of two bundles exist on every compact Hausdorff manifold modelled on a locally
compact space (`TauCeti.FiniteBundleAtlas.exists_closure_dom_subset_baseSet`).

## Main definitions

* `TauCeti.FiniteBundleAtlas.prod`: the atlas of `V ×ᵇ V'` on the charts of an atlas of `V`.
* `TauCeti.FiniteBundleAtlas.hom`: the atlas of the hom bundle of `V₁` and `V₂` on the charts of an
  atlas of `V₁`.
* `TauCeti.FiniteBundleAtlas.tangent`: the charts of an atlas of `V` as an atlas of the tangent
  bundle.
* `TauCeti.FiniteBundleAtlas.tangentHom`: the atlas of the bundle of `V`-valued one-forms on the
  charts of an atlas of `V`.

## Main results

* `TauCeti.FiniteBundleAtlas.coord_prod`, `TauCeti.FiniteBundleAtlas.coord_hom`,
  `TauCeti.FiniteBundleAtlas.coord_hom_apply`, `TauCeti.FiniteBundleAtlas.coord_tangentHom`: the
  chart readings of sections of the derived bundles.
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

end Prod

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

/-- **Hom sections act chartwise.** On the image of a chart, applying the chart reading of a
section `φ` of the hom bundle to the chart reading of a section `s` of `V₁` gives the chart reading
of the section `x ↦ φ x (s x)` of `V₂`. -/
theorem coord_hom_apply (i : Fin A.n) (φ : ∀ x, V₁ x →L[𝕜] V₂ x) (s : ∀ x, V₁ x) {y : E}
    (hy : y ∈ A.image i) :
    (A.hom h).coord i φ y (A.coord i s y) = (A.ofBaseSet h).coord i (fun x ↦ φ x (s x)) y := by
  have hdom := A.symm_mem_dom hy
  have h₁ := A.dom_subset_baseSet i hdom
  have h₂ : (A.chart i).symm y ∈ (trivializationAt F₂ V₂ (A.center i)).baseSet :=
    h i (subset_closure hdom)
  rw [coord_hom, ContinuousLinearMap.inCoordinates_eq h₁ h₂, coord_def, coord_def (A.ofBaseSet h) i]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Trivialization.continuousLinearEquivAt_symm_apply, Trivialization.symm_apply_apply_mk _ h₁,
    Trivialization.continuousLinearEquivAt_apply]
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

/-- A `V`-valued one-form read in a chart of `A.tangentHom` is its value at the corresponding point
of `M` expressed in the preferred trivializations of the tangent bundle and of `V` at the centre
of the chart. -/
theorem coord_tangentHom (i : Fin A.n) (ω : ∀ x, TangentSpace 𝓘(ℝ, E) x →L[ℝ] V x) (y : E) :
    A.tangentHom.coord i ω y =
      ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E)) F V (A.center i)
        ((A.chart i).symm y) (A.center i) ((A.chart i).symm y) (ω ((A.chart i).symm y)) :=
  A.tangent.coord_hom A.closure_dom_subset_baseSet i ω y

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
