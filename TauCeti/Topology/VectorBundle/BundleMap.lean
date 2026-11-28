/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.VectorBundle.Constructions
public import TauCeti.Topology.FiberBundle.Trivial

/-!
# Bundle maps continuous in charts

Let `E → M` and `E' → N` be vector bundles and `ψ : N → M` a map of the bases. A family of
continuous linear maps `A y : E (ψ y) →L[𝕜] E' y` is a *bundle map covering `ψ`*. It is
*continuous in charts* (`TauCeti.IsContinuousBundleMap`) when, for every vector `v` of the model
fibre and every pair of atlas charts, the coordinates of `A y` applied to the chart section through
`v` depend continuously on `y`. The map `ψ` itself is not required to be continuous.

## Main definitions

* `TauCeti.IsContinuousBundleMap`: a bundle map covering `ψ` is continuous in charts.

## Main results

* `TauCeti.isContinuousBundleMap_id`: the identity bundle map is continuous in charts.
* `TauCeti.IsContinuousBundleMap.comp`: the composite of bundle maps continuous in charts, the
  second covering a continuous map, is continuous in charts when the middle bundle has finite rank.
* `TauCeti.isContinuousBundleMap_trivial_iff`: for trivial bundles, continuity in charts is
  continuity of `y ↦ A y v` for every vector `v`.
-/

public section

open Bundle Set

namespace TauCeti

variable {𝕜 M N P F F' F'' : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [NormedAddCommGroup F''] [NormedSpace 𝕜 F'']
  {E : M → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace 𝕜 (E x)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  {E' : N → Type*} [TopologicalSpace (TotalSpace F' E')] [∀ y, NormedAddCommGroup (E' y)]
  [∀ y, NormedSpace 𝕜 (E' y)] [FiberBundle F' E'] [VectorBundle 𝕜 F' E']
  {E'' : P → Type*} [TopologicalSpace (TotalSpace F'' E'')] [∀ z, NormedAddCommGroup (E'' z)]
  [∀ z, NormedSpace 𝕜 (E'' z)] [FiberBundle F'' E''] [VectorBundle 𝕜 F'' E'']
  {ψ : N → M}

variable (𝕜 F F') in
/-- A family of continuous linear maps `A y : E (ψ y) →L[𝕜] E' y`, a bundle map covering
`ψ : N → M`, is *continuous in charts* when, for every atlas chart `e` of `E`, every atlas chart
`e'` of `E'` and every vector `v` of the model fibre of `E`, the coordinates in `e'` of `A y`
applied to the vector of `E (ψ y)` with coordinates `v` in `e` depend continuously on `y` wherever
both charts are defined. -/
def IsContinuousBundleMap (ψ : N → M) (A : ∀ y, E (ψ y) →L[𝕜] E' y) : Prop :=
  ∀ (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
    (e' : Trivialization F' (π F' E')) [MemTrivializationAtlas e'] (v : F),
    ContinuousOn (fun y ↦ e'.continuousLinearMapAt 𝕜 y (A y (e.symmL 𝕜 (ψ y) v)))
      (ψ ⁻¹' e.baseSet ∩ e'.baseSet)

theorem isContinuousBundleMap_iff {A : ∀ y, E (ψ y) →L[𝕜] E' y} :
    IsContinuousBundleMap 𝕜 F F' ψ A ↔
      ∀ (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
        (e' : Trivialization F' (π F' E')) [MemTrivializationAtlas e'] (v : F),
        ContinuousOn (fun y ↦ e'.continuousLinearMapAt 𝕜 y (A y (e.symmL 𝕜 (ψ y) v)))
          (ψ ⁻¹' e.baseSet ∩ e'.baseSet) :=
  Iff.rfl

variable (𝕜 F E) in
/-- The identity bundle map is continuous in charts: its chart expressions are the coordinate
changes of the bundle. -/
theorem isContinuousBundleMap_id :
    IsContinuousBundleMap 𝕜 F F id (fun x ↦ ContinuousLinearMap.id 𝕜 (E x)) := by
  intro e _ e' _ v
  refine ((continuousOn_coordChange 𝕜 e e').clm_apply (continuousOn_const (c := v))).congr
    fun x hx ↦ ?_
  simp only [ContinuousLinearMap.id_apply, id, e.symmL_apply hx.1,
    e'.continuousLinearMapAt_apply_of_mem (R := 𝕜) hx.2, ContinuousLinearEquiv.coe_coe,
    e.coordChangeL_apply e' hx]

/-- The composite `z ↦ A₂ z ∘ A (ψ₂ z)` of a bundle map `A` covering `ψ` and a bundle map `A₂`
covering a continuous map `ψ₂`, both continuous in charts, is continuous in charts when the middle
bundle has finite rank. -/
theorem IsContinuousBundleMap.comp [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F'] {ψ₂ : P → N}
    (hψ₂ : Continuous ψ₂) {A : ∀ y, E (ψ y) →L[𝕜] E' y} {A₂ : ∀ z, E' (ψ₂ z) →L[𝕜] E'' z}
    (hA : IsContinuousBundleMap 𝕜 F F' ψ A) (hA₂ : IsContinuousBundleMap 𝕜 F' F'' ψ₂ A₂) :
    IsContinuousBundleMap 𝕜 F F'' (ψ ∘ ψ₂) fun z ↦ (A₂ z).comp (A (ψ₂ z)) := by
  -- Near a point, insert the chart of the middle bundle at its image under `ψ₂`: the chart
  -- expressions of `A₂` are then a family of linear maps on a finite-dimensional space, continuous
  -- in the point, applied to the continuous chart coordinates of `A`.
  intro e _ e'' _ v
  refine continuousOn_of_locally_continuousOn fun z₀ _ ↦ ?_
  set e' := trivializationAt F' E' (ψ₂ z₀)
  refine ⟨ψ₂ ⁻¹' e'.baseSet, e'.open_baseSet.preimage hψ₂,
    mem_baseSet_trivializationAt F' E' (ψ₂ z₀), ?_⟩
  -- The chart expressions of `A₂` from `e'` to `e''`, as continuous linear maps.
  have h₂ : ContinuousOn
      (fun z ↦ (e''.continuousLinearMapAt 𝕜 z).comp ((A₂ z).comp (e'.symmL 𝕜 (ψ₂ z))))
      (ψ₂ ⁻¹' e'.baseSet ∩ e''.baseSet) :=
    continuousOn_clm_apply.2 (hA₂ e' e'')
  have h₁ := (hA e e' v).comp hψ₂.continuousOn (mapsTo_preimage _ _)
  have hU : (ψ ∘ ψ₂) ⁻¹' e.baseSet ∩ e''.baseSet ∩ ψ₂ ⁻¹' e'.baseSet ⊆
      ψ₂ ⁻¹' e'.baseSet ∩ e''.baseSet ∩ ψ₂ ⁻¹' (ψ ⁻¹' e.baseSet ∩ e'.baseSet) :=
    fun z hz ↦ ⟨⟨hz.2, hz.1.2⟩, hz.1.1, hz.2⟩
  refine (((h₂.mono inter_subset_left).clm_apply (h₁.mono inter_subset_right)).mono hU).congr
    fun z hz ↦ ?_
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
    e'.symmL_continuousLinearMapAt hz.2]

variable (𝕜 F F' ψ) in
/-- For trivial bundles, a bundle map is continuous in charts exactly when it is strongly
continuous: `y ↦ A y v` is continuous for every vector `v`. -/
theorem isContinuousBundleMap_trivial_iff {A : ∀ y, Trivial M F (ψ y) →L[𝕜] Trivial N F' y} :
    IsContinuousBundleMap 𝕜 F F' ψ A ↔ ∀ v : F, Continuous fun y ↦ A y v := by
  -- In the trivial charts, the chart expression of `A` is `y ↦ A y v` on all of `N`.
  have key (v : F) :
      ContinuousOn (fun y ↦ (Trivial.trivialization N F').continuousLinearMapAt 𝕜 y
          (A y ((Trivial.trivialization M F).symmL 𝕜 (ψ y) v)))
        (ψ ⁻¹' (Trivial.trivialization M F).baseSet ∩ (Trivial.trivialization N F').baseSet) ↔
        Continuous fun y ↦ A y v := by
    simp only [Trivial.trivialization_baseSet, preimage_univ, inter_self, continuousOn_univ,
      Trivial.continuousLinearMapAt_trivialization, Trivial.symmL_trivialization,
      ContinuousLinearMap.id_apply]
  refine ⟨fun h v ↦ (key v).1 (h _ _ v), fun h e _ e' _ v ↦ ?_⟩
  obtain rfl := Trivial.eq_trivialization M F e
  obtain rfl := Trivial.eq_trivialization N F' e'
  exact (key v).2 (h v)

variable (𝕜 F ψ) in
/-- The identity fibre maps of a trivial bundle, covering any map of the bases, are continuous in
charts. -/
theorem isContinuousBundleMap_trivial_id :
    IsContinuousBundleMap 𝕜 F F ψ (E := Trivial M F) (E' := Trivial N F)
      fun _ ↦ (LinearIsometry.id : F →ₗᵢ[𝕜] F).toContinuousLinearMap :=
  (isContinuousBundleMap_trivial_iff 𝕜 F F ψ).2 fun _ ↦ continuous_const

end TauCeti
