/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import TauCeti.Topology.VectorBundle.ContinuousMultilinearMap
public import TauCeti.Geometry.Manifold.ContMDiff.ContinuousMultilinearMap
public import TauCeti.Geometry.Manifold.MFDeriv.ContinuousMultilinearMap

/-!
# The smooth vector bundle of continuous multilinear maps

Let `E₁` and `E₂` be `C^n` vector bundles over a manifold `B`, and `ι` a finite index type. The
topological vector bundle with fibres `ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ x) (E₂ x)`
(`TauCeti.Topology.VectorBundle.ContinuousMultilinearMap`) is a `C^n` vector bundle
(`ContMDiffVectorBundle.continuousMultilinearMap`): its coordinate changes precompose each
variable with a coordinate change of `E₁` and postcompose with one of `E₂`, and precomposition
depends multilinearly, hence smoothly, on the maps it precomposes with. This holds over every
nontrivially normed field and at every order `n`, including the analytic order `ω`, with no
assumption on the dimension.

For the tangent bundle `E₁ = TM` the sections of this bundle are the `E₂`-valued covariant
tensor fields of rank `card ι`, such as the iterated covariant derivatives `∇ʲσ` of a section `σ`
of `E₂`, with `ι = Fin j`.

Applying a `C^n` section of this bundle to `C^n` sections of `E₁` gives a `C^n` section of `E₂`
(`ContMDiffAt.continuousMultilinearMap_bundle_apply`), and similarly for differentiability
(`MDifferentiableAt.continuousMultilinearMap_bundle_apply`). Versions over two different base
maps, with the regularity of the family of multilinear maps read in coordinates, are
`ContMDiffAt.continuousMultilinearMap_apply_of_inCoordinates` and
`MDifferentiableAt.continuousMultilinearMap_apply_of_inCoordinates`.

## Implementation notes

The statements and proofs follow Sébastien Gouëzel's smooth bundle of continuous alternating
maps in Mathlib (`Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap`). For
alternating maps Mathlib only implements the characteristic zero case: in positive
characteristic the result still holds in finite dimension, but can fail for `n = ω` in general.
Precomposition of multilinear maps needs no such assumption, since it is a continuous multilinear
map (`ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear`) composed with the
diagonal, hence smooth at every order (`ContMDiffWithinAt.compContinuousLinearMapL`).
-/

public section

noncomputable section

open Bundle Set Pretrivialization FiberBundle
open ContinuousMultilinearMap (inCoordinates)

open scoped Manifold Bundle Topology

section Bundle

variable {𝕜 B F₁ F₂ M ι : Type*} {n : WithTop ℕ∞} [Fintype ι]
  {E₁ : B → Type*} {E₂ : B → Type*} [NontriviallyNormedField 𝕜]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)] [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {e₁ e₁' : Trivialization F₁ (π F₁ E₁)} {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}

namespace TauCeti

/-- The coordinate changes of the bundle of continuous multilinear maps are `C^n` on the
intersection of the base sets when those of `E₁` and `E₂` are. -/
theorem contMDiffOn_continuousMultilinearMapCoordChange
    [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    ContMDiffOn IB
      𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂ →L[𝕜]
        ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂) n
      (continuousMultilinearMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  have h₁ := contMDiffOn_coordChangeL (IB := IB) e₁' e₁ (n := n)
  have h₂ := contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := n)
  exact (ContMDiffOn.compContinuousLinearMapL fun _ ↦ h₁.mono (by mfld_set_tac)).clm_comp
    (h₂.mono (by mfld_set_tac)).compContinuousMultilinearMapL

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

/-- The chart of the total space of the bundle of continuous multilinear maps at `y₀` sends `y`
to the chart of the base at `y₀.proj` applied to `y.proj`, paired with the fibre component of
`y` read in the trivializations at `y₀.proj`. -/
@[simp]
theorem chartAt_continuousMultilinearMap
    (y₀ y : TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
      (fun b : B ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ b) (E₂ b))) :
    chartAt (ModelProd HB (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)) y₀ y =
      (chartAt HB y₀.proj y.proj, inCoordinates F₁ F₂ y₀.proj y.proj y₀.proj y.proj y.snd) := by
  rw [FiberBundle.chartedSpace_chartAt, OpenPartialHomeomorph.trans_apply,
    OpenPartialHomeomorph.prod_apply, Trivialization.coe_coe, OpenPartialHomeomorph.refl_apply,
    Function.id_def, trivializationAt_continuousMultilinearMap_apply]

/-- A map into the bundle of continuous multilinear maps is `C^n` within a set at a point
exactly when its projection is and its fibre component, read in the trivializations at the
image of the point, is. -/
theorem contMDiffWithinAt_continuousMultilinearMap_bundle
    (f : M → TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
      (fun b : B ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ b) (E₂ b))) {s : Set M} {x₀ : M} :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)) n
        f s x₀ ↔
      ContMDiffWithinAt IM IB n (fun x ↦ (f x).proj) s x₀ ∧
        ContMDiffWithinAt IM 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂) n
          (fun x ↦ inCoordinates F₁ F₂ (f x₀).proj (f x).proj (f x₀).proj (f x).proj (f x).snd)
          s x₀ :=
  contMDiffWithinAt_totalSpace_iff

/-- A map into the bundle of continuous multilinear maps is `C^n` at a point exactly when its
projection is and its fibre component, read in the trivializations at the image of the point,
is. -/
theorem contMDiffAt_continuousMultilinearMap_bundle
    (f : M → TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
      (fun b : B ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ b) (E₂ b))) {x₀ : M} :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)) n f x₀ ↔
      ContMDiffAt IM IB n (fun x ↦ (f x).proj) x₀ ∧
        ContMDiffAt IM 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂) n
          (fun x ↦ inCoordinates F₁ F₂ (f x₀).proj (f x).proj (f x₀).proj (f x).proj (f x).snd)
          x₀ :=
  contMDiffAt_totalSpace_iff

/-- A map into the bundle of continuous multilinear maps is differentiable within a set at a
point exactly when its projection is and its fibre component, read in the trivializations at the
image of the point, is. -/
theorem mdifferentiableWithinAt_continuousMultilinearMap_bundle
    (f : M → TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
      (fun b : B ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ b) (E₂ b))) {s : Set M} {x₀ : M} :
    MDifferentiableWithinAt IM (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂))
        f s x₀ ↔
      MDifferentiableWithinAt IM IB (fun x ↦ (f x).proj) s x₀ ∧
        MDifferentiableWithinAt IM 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
          (fun x ↦ inCoordinates F₁ F₂ (f x₀).proj (f x).proj (f x₀).proj (f x).proj (f x).snd)
          s x₀ :=
  mdifferentiableWithinAt_totalSpace IB ..

/-- A map into the bundle of continuous multilinear maps is differentiable at a point exactly
when its projection is and its fibre component, read in the trivializations at the image of the
point, is. -/
theorem mdifferentiableAt_continuousMultilinearMap_bundle
    (f : M → TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
      (fun b : B ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ b) (E₂ b))) {x₀ : M} :
    MDifferentiableAt IM (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂))
        f x₀ ↔
      MDifferentiableAt IM IB (fun x ↦ (f x).proj) x₀ ∧
        MDifferentiableAt IM 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
          (fun x ↦ inCoordinates F₁ F₂ (f x₀).proj (f x).proj (f x₀).proj (f x).proj (f x).snd)
          x₀ :=
  mdifferentiableAt_totalSpace ..

end TauCeti

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]

/-- The vector prebundle of continuous multilinear maps between two `C^n` vector bundles has
`C^n` coordinate changes. -/
instance Bundle.ContinuousMultilinearMap.vectorPrebundle.isContMDiff :
    (Bundle.ContinuousMultilinearMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).IsContMDiff IB n where
  exists_contMDiffCoordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨continuousMultilinearMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂',
      TauCeti.contMDiffOn_continuousMultilinearMapCoordChange,
      continuousMultilinearMapCoordChange_apply⟩

/-- The continuous multilinear maps between two `C^n` vector bundles form a `C^n` vector
bundle. -/
instance ContMDiffVectorBundle.continuousMultilinearMap :
    ContMDiffVectorBundle n (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
      (fun b : B ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ b) (E₂ b)) IB :=
  (Bundle.ContinuousMultilinearMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).contMDiffVectorBundle IB

end Bundle

/-! ### Applying families of multilinear maps read in coordinates -/

section InCoordinates

variable {𝕜 F₁ F₂ B₁ B₂ M ι : Type*} [Fintype ι]
  {E₁ : B₁ → Type*} {E₂ : B₂ → Type*} [NontriviallyNormedField 𝕜]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)] [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {EB₁ : Type*} [NormedAddCommGroup EB₁] [NormedSpace 𝕜 EB₁] {HB₁ : Type*} [TopologicalSpace HB₁]
  {IB₁ : ModelWithCorners 𝕜 EB₁ HB₁} [TopologicalSpace B₁] [ChartedSpace HB₁ B₁]
  {EB₂ : Type*} [NormedAddCommGroup EB₂] [NormedSpace 𝕜 EB₂] {HB₂ : Type*} [TopologicalSpace HB₂]
  {IB₂ : ModelWithCorners 𝕜 EB₂ HB₂} [TopologicalSpace B₂] [ChartedSpace HB₂ B₂]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {n : WithTop ℕ∞} [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {b₁ : M → B₁} {b₂ : M → B₂} {m₀ : M}
  {ϕ : Π m : M, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ (b₁ m)) (E₂ (b₂ m))}
  {v : ι → Π m : M, E₁ (b₁ m)} {s : Set M}

omit [Fintype ι] [TopologicalSpace M] in
/-- Near `m₀`, applying `ϕ m` to `(v i m)ᵢ` and reading the result in the trivialization of `E₂`
at `b₂ m₀` is the same as applying `ϕ m` read in coordinates to the `v i m` read in the
trivialization of `E₁` at `b₁ m₀`, as long as `b₁ m` and `b₂ m` stay in the base sets of those
trivializations (when `ι` is empty only the second condition is needed). -/
private theorem eventuallyEq_continuousMultilinearMap_apply_inCoordinates {l : Filter M}
    (hb₁ : Nonempty ι → ∀ᶠ m in l, b₁ m ∈ (trivializationAt F₁ E₁ (b₁ m₀)).baseSet)
    (hb₂ : ∀ᶠ m in l, b₂ m ∈ (trivializationAt F₂ E₂ (b₂ m₀)).baseSet) :
    (fun m ↦ inCoordinates F₁ F₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)
        fun i ↦ (trivializationAt F₁ E₁ (b₁ m₀) ⟨b₁ m, v i m⟩).2) =ᶠ[l]
      fun m ↦ (trivializationAt F₂ E₂ (b₂ m₀) ⟨b₂ m, ϕ m fun i ↦ v i m⟩).2 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · filter_upwards [hb₂] with m h'm
    rw [ContinuousMultilinearMap.inCoordinates_eq_of_mem_baseSet₂ _ _ h'm]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, ContinuousLinearEquiv.coe_coe,
      Trivialization.continuousLinearEquivAt_apply, Function.comp_apply]
    congr
    ext i
    exact hι.elim i
  · filter_upwards [hb₁ hι, hb₂] with m hm h'm
    rw [ContinuousMultilinearMap.inCoordinates_eq _ _ hm h'm]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearEquiv.coe_coe, Trivialization.continuousLinearEquivAt_symm_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe,
      Trivialization.continuousLinearEquivAt_apply, Function.comp_apply]
    congr
    ext i
    simp [*]

/-- Consider `C^n` maps `vᵢ : M → E₁` to a vector bundle, over a base map `b₁ : M → B₁`, and
another base map `b₂ : M → B₂`. Given continuous multilinear maps
`ϕ m : E₁ (b₁ m) × ⋯ × E₁ (b₁ m) → E₂ (b₂ m)` depending smoothly on `m` when read in coordinates,
the map `m ↦ ϕ m (v₁ m, …)` is `C^n` within a set at a point.

The regularity of `ϕ` is stated in coordinates, since it is only local information and the
pullback bundles along `b₁` and `b₂` need not be manifolds. For a version with a single base
map, see `ContMDiffWithinAt.continuousMultilinearMap_bundle_apply`. -/
theorem ContMDiffWithinAt.continuousMultilinearMap_apply_of_inCoordinates
    (hϕ : ContMDiffWithinAt IM 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂) n
      (fun m ↦ inCoordinates F₁ F₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) s m₀)
    (hv : ∀ i, ContMDiffWithinAt IM (IB₁.prod 𝓘(𝕜, F₁)) n
      (fun m ↦ (v i m : TotalSpace F₁ E₁)) s m₀)
    (hb₂ : ContMDiffWithinAt IM IB₂ n b₂ s m₀) :
    ContMDiffWithinAt IM (IB₂.prod 𝓘(𝕜, F₂)) n
      (fun m ↦ (ϕ m (fun i ↦ v i m) : TotalSpace F₂ E₂)) s m₀ := by
  rw [← contMDiffWithinAt_insert_self] at hϕ hb₂ ⊢
  replace hv : ∀ i, ContMDiffWithinAt IM (IB₁.prod 𝓘(𝕜, F₁)) n
      (fun m ↦ (v i m : TotalSpace F₁ E₁)) (insert m₀ s) m₀ := fun i ↦
    contMDiffWithinAt_insert_self.2 (hv i)
  simp_rw [contMDiffWithinAt_totalSpace_iff] at hv ⊢
  refine ⟨hb₂, (hϕ.continuousMultilinearMap_apply fun i ↦ (hv i).2).congr_of_eventuallyEq_of_mem
    (eventuallyEq_continuousMultilinearMap_apply_inCoordinates ?_ ?_).symm (mem_insert m₀ s)⟩
  · rintro ⟨i₀⟩
    exact (hv i₀).1.continuousWithinAt <| (trivializationAt F₁ E₁ (b₁ m₀)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' (b₁ m₀))
  · exact hb₂.continuousWithinAt <| (trivializationAt F₂ E₂ (b₂ m₀)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' (b₂ m₀))

/-- Consider `C^n` maps `vᵢ : M → E₁` to a vector bundle, over a base map `b₁ : M → B₁`, and
another base map `b₂ : M → B₂`. Given continuous multilinear maps
`ϕ m : E₁ (b₁ m) × ⋯ × E₁ (b₁ m) → E₂ (b₂ m)` depending smoothly on `m` when read in coordinates,
the map `m ↦ ϕ m (v₁ m, …)` is `C^n` at a point. For a version with a single base map, see
`ContMDiffAt.continuousMultilinearMap_bundle_apply`. -/
theorem ContMDiffAt.continuousMultilinearMap_apply_of_inCoordinates
    (hϕ : ContMDiffAt IM 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂) n
      (fun m ↦ inCoordinates F₁ F₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀)
    (hv : ∀ i, ContMDiffAt IM (IB₁.prod 𝓘(𝕜, F₁)) n (fun m ↦ (v i m : TotalSpace F₁ E₁)) m₀)
    (hb₂ : ContMDiffAt IM IB₂ n b₂ m₀) :
    ContMDiffAt IM (IB₂.prod 𝓘(𝕜, F₂)) n
      (fun m ↦ (ϕ m (fun i ↦ v i m) : TotalSpace F₂ E₂)) m₀ :=
  ContMDiffWithinAt.continuousMultilinearMap_apply_of_inCoordinates hϕ hv hb₂

/-- Consider differentiable maps `vᵢ : M → E₁` to a vector bundle, over a base map
`b₁ : M → B₁`, and another base map `b₂ : M → B₂`. Given continuous multilinear maps
`ϕ m : E₁ (b₁ m) × ⋯ × E₁ (b₁ m) → E₂ (b₂ m)` depending differentiably on `m` when read in
coordinates, the map `m ↦ ϕ m (v₁ m, …)` is differentiable within a set at a point. For a
version with a single base map, see `MDifferentiableWithinAt.continuousMultilinearMap_bundle_apply`.
-/
theorem MDifferentiableWithinAt.continuousMultilinearMap_apply_of_inCoordinates
    (hϕ : MDifferentiableWithinAt IM 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
      (fun m ↦ inCoordinates F₁ F₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) s m₀)
    (hv : ∀ i, MDifferentiableWithinAt IM (IB₁.prod 𝓘(𝕜, F₁))
      (fun m ↦ (v i m : TotalSpace F₁ E₁)) s m₀)
    (hb₂ : MDifferentiableWithinAt IM IB₂ b₂ s m₀) :
    MDifferentiableWithinAt IM (IB₂.prod 𝓘(𝕜, F₂))
      (fun m ↦ (ϕ m (fun i ↦ v i m) : TotalSpace F₂ E₂)) s m₀ := by
  simp_rw [mdifferentiableWithinAt_totalSpace] at hv ⊢
  refine ⟨hb₂, (hϕ.continuousMultilinearMap_apply fun i ↦ (hv i).2).congr_of_eventuallyEq_insert
    (eventuallyEq_continuousMultilinearMap_apply_inCoordinates ?_ ?_).symm⟩
  · rintro ⟨i₀⟩
    exact (hv i₀).1.insert.continuousWithinAt <|
      (trivializationAt F₁ E₁ (b₁ m₀)).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' (b₁ m₀))
  · exact hb₂.insert.continuousWithinAt <| (trivializationAt F₂ E₂ (b₂ m₀)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' (b₂ m₀))

/-- Consider differentiable maps `vᵢ : M → E₁` to a vector bundle, over a base map
`b₁ : M → B₁`, and another base map `b₂ : M → B₂`. Given continuous multilinear maps
`ϕ m : E₁ (b₁ m) × ⋯ × E₁ (b₁ m) → E₂ (b₂ m)` depending differentiably on `m` when read in
coordinates, the map `m ↦ ϕ m (v₁ m, …)` is differentiable at a point. For a version with a
single base map, see `MDifferentiableAt.continuousMultilinearMap_bundle_apply`. -/
theorem MDifferentiableAt.continuousMultilinearMap_apply_of_inCoordinates
    (hϕ : MDifferentiableAt IM 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
      (fun m ↦ inCoordinates F₁ F₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀)
    (hv : ∀ i, MDifferentiableAt IM (IB₁.prod 𝓘(𝕜, F₁)) (fun m ↦ (v i m : TotalSpace F₁ E₁)) m₀)
    (hb₂ : MDifferentiableAt IM IB₂ b₂ m₀) :
    MDifferentiableAt IM (IB₂.prod 𝓘(𝕜, F₂))
      (fun m ↦ (ϕ m (fun i ↦ v i m) : TotalSpace F₂ E₂)) m₀ := by
  simp_rw [← mdifferentiableWithinAt_univ] at hϕ hv hb₂ ⊢
  exact MDifferentiableWithinAt.continuousMultilinearMap_apply_of_inCoordinates hϕ hv hb₂

end InCoordinates

/-! ### Applying sections of the bundle of continuous multilinear maps -/

section BundleApply

variable {𝕜 B F₁ F₂ M ι : Type*} [Fintype ι] [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  {b : M → B} {v : ι → Π x, E₁ (b x)} {s : Set M} {x : M}
  {ϕ : Π x, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ (b x)) (E₂ (b x))}

/-- Applying a `C^n` family of continuous multilinear maps `ϕ m` on the fibres of `E₁` over
`b m` with values in the fibres of `E₂`, to `C^n` families `vᵢ` of vectors of `E₁`, gives a
`C^n` family of vectors of `E₂`, within a set at a point. -/
theorem ContMDiffWithinAt.continuousMultilinearMap_bundle_apply
    (hϕ : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)) n
      (fun m ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
        (E := fun y : B ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ y) (E₂ y)) (b m) (ϕ m))
      s x)
    (hv : ∀ i, ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₁)) n
      (fun m ↦ TotalSpace.mk' F₁ (b m) (v i m)) s x) :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₂)) n
      (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (fun i ↦ v i m))) s x := by
  rw [TauCeti.contMDiffWithinAt_continuousMultilinearMap_bundle] at hϕ
  exact hϕ.2.continuousMultilinearMap_apply_of_inCoordinates hv hϕ.1

/-- Applying a `C^n` family of continuous multilinear maps `ϕ m` on the fibres of `E₁` over
`b m` with values in the fibres of `E₂`, to `C^n` families `vᵢ` of vectors of `E₁`, gives a
`C^n` family of vectors of `E₂`, at a point. -/
theorem ContMDiffAt.continuousMultilinearMap_bundle_apply
    (hϕ : ContMDiffAt IM (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)) n
      (fun m ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
        (E := fun y : B ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ y) (E₂ y)) (b m) (ϕ m)) x)
    (hv : ∀ i, ContMDiffAt IM (IB.prod 𝓘(𝕜, F₁)) n (fun m ↦ TotalSpace.mk' F₁ (b m) (v i m)) x) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, F₂)) n
      (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (fun i ↦ v i m))) x :=
  ContMDiffWithinAt.continuousMultilinearMap_bundle_apply hϕ hv

/-- Applying a `C^n` family of continuous multilinear maps `ϕ m` on the fibres of `E₁` over
`b m` with values in the fibres of `E₂`, to `C^n` families `vᵢ` of vectors of `E₁`, gives a
`C^n` family of vectors of `E₂`, on a set. -/
theorem ContMDiffOn.continuousMultilinearMap_bundle_apply
    (hϕ : ContMDiffOn IM (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)) n
      (fun m ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
        (E := fun y : B ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ y) (E₂ y)) (b m) (ϕ m)) s)
    (hv : ∀ i, ContMDiffOn IM (IB.prod 𝓘(𝕜, F₁)) n (fun m ↦ TotalSpace.mk' F₁ (b m) (v i m)) s) :
    ContMDiffOn IM (IB.prod 𝓘(𝕜, F₂)) n
      (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (fun i ↦ v i m))) s :=
  fun x hx ↦ (hϕ x hx).continuousMultilinearMap_bundle_apply fun i ↦ hv i x hx

/-- Applying a `C^n` family of continuous multilinear maps `ϕ m` on the fibres of `E₁` over
`b m` with values in the fibres of `E₂`, to `C^n` families `vᵢ` of vectors of `E₁`, gives a
`C^n` family of vectors of `E₂`. -/
theorem ContMDiff.continuousMultilinearMap_bundle_apply
    (hϕ : ContMDiff IM (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)) n
      (fun m ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
        (E := fun y : B ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ y) (E₂ y)) (b m) (ϕ m)))
    (hv : ∀ i, ContMDiff IM (IB.prod 𝓘(𝕜, F₁)) n (fun m ↦ TotalSpace.mk' F₁ (b m) (v i m))) :
    ContMDiff IM (IB.prod 𝓘(𝕜, F₂)) n
      (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (fun i ↦ v i m))) :=
  fun x ↦ (hϕ x).continuousMultilinearMap_bundle_apply fun i ↦ hv i x

/-- Applying a differentiable family of continuous multilinear maps `ϕ m` on the fibres of `E₁`
over `b m` with values in the fibres of `E₂`, to differentiable families `vᵢ` of vectors of `E₁`,
gives a differentiable family of vectors of `E₂`, within a set at a point. -/
theorem MDifferentiableWithinAt.continuousMultilinearMap_bundle_apply
    (hϕ : MDifferentiableWithinAt IM
      (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂))
      (fun m ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
        (E := fun y : B ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ y) (E₂ y)) (b m) (ϕ m))
      s x)
    (hv : ∀ i, MDifferentiableWithinAt IM (IB.prod 𝓘(𝕜, F₁))
      (fun m ↦ TotalSpace.mk' F₁ (b m) (v i m)) s x) :
    MDifferentiableWithinAt IM (IB.prod 𝓘(𝕜, F₂))
      (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (fun i ↦ v i m))) s x := by
  rw [TauCeti.mdifferentiableWithinAt_continuousMultilinearMap_bundle] at hϕ
  exact hϕ.2.continuousMultilinearMap_apply_of_inCoordinates hv hϕ.1

/-- Applying a differentiable family of continuous multilinear maps `ϕ m` on the fibres of `E₁`
over `b m` with values in the fibres of `E₂`, to differentiable families `vᵢ` of vectors of `E₁`,
gives a differentiable family of vectors of `E₂`, at a point. -/
theorem MDifferentiableAt.continuousMultilinearMap_bundle_apply
    (hϕ : MDifferentiableAt IM (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂))
      (fun m ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
        (E := fun y : B ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ y) (E₂ y)) (b m) (ϕ m)) x)
    (hv : ∀ i, MDifferentiableAt IM (IB.prod 𝓘(𝕜, F₁))
      (fun m ↦ TotalSpace.mk' F₁ (b m) (v i m)) x) :
    MDifferentiableAt IM (IB.prod 𝓘(𝕜, F₂))
      (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (fun i ↦ v i m))) x :=
  MDifferentiableWithinAt.continuousMultilinearMap_bundle_apply hϕ hv

/-- Applying a differentiable family of continuous multilinear maps `ϕ m` on the fibres of `E₁`
over `b m` with values in the fibres of `E₂`, to differentiable families `vᵢ` of vectors of `E₁`,
gives a differentiable family of vectors of `E₂`, on a set. -/
theorem MDifferentiableOn.continuousMultilinearMap_bundle_apply
    (hϕ : MDifferentiableOn IM (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂))
      (fun m ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
        (E := fun y : B ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ y) (E₂ y)) (b m) (ϕ m)) s)
    (hv : ∀ i, MDifferentiableOn IM (IB.prod 𝓘(𝕜, F₁))
      (fun m ↦ TotalSpace.mk' F₁ (b m) (v i m)) s) :
    MDifferentiableOn IM (IB.prod 𝓘(𝕜, F₂))
      (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (fun i ↦ v i m))) s :=
  fun x hx ↦ (hϕ x hx).continuousMultilinearMap_bundle_apply fun i ↦ hv i x hx

/-- Applying a differentiable family of continuous multilinear maps `ϕ m` on the fibres of `E₁`
over `b m` with values in the fibres of `E₂`, to differentiable families `vᵢ` of vectors of `E₁`,
gives a differentiable family of vectors of `E₂`. -/
theorem MDifferentiable.continuousMultilinearMap_bundle_apply
    (hϕ : MDifferentiable IM (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂))
      (fun m ↦ TotalSpace.mk' (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
        (E := fun y : B ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ y) (E₂ y)) (b m) (ϕ m)))
    (hv : ∀ i, MDifferentiable IM (IB.prod 𝓘(𝕜, F₁)) (fun m ↦ TotalSpace.mk' F₁ (b m) (v i m))) :
    MDifferentiable IM (IB.prod 𝓘(𝕜, F₂))
      (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (fun i ↦ v i m))) :=
  fun x ↦ (hϕ x).continuousMultilinearMap_bundle_apply fun i ↦ hv i x

end BundleApply
