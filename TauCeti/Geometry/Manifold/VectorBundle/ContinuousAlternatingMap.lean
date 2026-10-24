/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import TauCeti.Analysis.Calculus.ContDiff.ContinuousAlternatingMap

/-!
# Smooth bundles of continuous alternating maps

Continuous alternating maps between two smooth vector bundles form a smooth vector
bundle. This equips the bundles underlying differential forms with smooth coordinate
changes, without changing Mathlib's topology, trivializations, or atlas.

Mathlib's `Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap` provides the
same construction over characteristic-zero fields, together with the fibre-coordinate
regularity criteria such as `contMDiffAt_continuousAlternatingMap_bundle`. The results here
remove the characteristic-zero assumption.

The coordinate-change proof follows Floris van Doorn's smooth Hom-bundle construction
in `Mathlib.Geometry.Manifold.VectorBundle.Hom`, using the topological alternating-map
bundle of Yury Kudryashov, Heather Macbeth, and Floris van Doorn. Its domain pullback is
smooth, while its codomain postcomposition is continuous linear. The construction
works over every nontrivially normed field at finite orders and `∞`. At the analytic
order `ω`, the construction assumes a nonzero arity factorial, automatically including
characteristic-zero fields. Models with corners are arbitrary, with no dimension or
completeness assumptions.
-/

public section

noncomputable section

open Bundle Set Pretrivialization
open scoped Manifold Bundle ContDiff

namespace TauCeti

variable {𝕜 ι B F₁ F₂ : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
  {n : WithTop ℕ∞}
  {E₁ : B → Type*} {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

section CoordinateChange

variable [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]
  {e₁ e₁' : Trivialization F₁ (π F₁ E₁)} {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}
  [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
  [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂']

/-- Coordinate changes of the alternating-map bundle have the same regularity as the
coordinate changes of its domain and codomain bundles, provided the arity factorial is
nonzero in `𝕜` at the analytic order `ω`. Finite orders and `∞` have no characteristic
restriction. -/
theorem contMDiffOn_continuousAlternatingMapCoordChange
    (hn : n = ω → ((Fintype.card ι).factorial : 𝕜) ≠ 0 := by
      intro h
      first | exact NeZero.ne _ | cases h) :
    ContMDiffOn IB 𝓘(𝕜, (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] F₁ [⋀^ι]→L[𝕜] F₂) n
      (continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  -- Cache the canonical normed structures for the nested operator-valued composition.
  let : NormedAddCommGroup ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] F₁ [⋀^ι]→L[𝕜] F₂) :=
    inferInstance
  let : NormedSpace 𝕜 ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] F₁ [⋀^ι]→L[𝕜] F₂) :=
    inferInstance
  simp +unfoldPartialApp only [continuousAlternatingMapCoordChange,
    ContinuousLinearEquiv.coe_continuousAlternatingMapCongr, ContinuousLinearEquiv.symm_symm]
  have h₁ := contMDiffOn_coordChangeL (IB := IB) e₁' e₁ (n := n)
  have h₂ := contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := n)
  refine ContMDiffOn.clm_comp ?_ ?_
  · refine (ContinuousLinearMap.compContinuousAlternatingMapCLM
      (ι := ι) 𝕜 F₁ F₂ F₂).contMDiff.comp_contMDiffOn (h₂.mono ?_)
    mfld_set_tac
  · refine (ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM
      (𝕜 := 𝕜) (E := F₁) (F := F₁)
      (G := F₂) (ι := ι) n hn).contMDiff.comp_contMDiffOn (h₁.mono ?_)
    mfld_set_tac

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

/-- Mathlib's alternating-map vector prebundle has smooth coordinate changes.
The analytic order `ω` requires a nonzero arity factorial in `𝕜`. -/
theorem isContMDiff_continuousAlternatingMap_vectorPrebundle
    (hn : n = ω → ((Fintype.card ι).factorial : 𝕜) ≠ 0 := by
      intro h
      first | exact NeZero.ne _ | cases h) :
    (Bundle.ContinuousAlternatingMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).IsContMDiff IB n where
  exists_contMDiffCoordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂',
      contMDiffOn_continuousAlternatingMapCoordChange hn,
      continuousAlternatingMapCoordChange_apply⟩

/-- When the arity factorial is nonzero in `𝕜`, the alternating-map prebundle has `C^n`
coordinate changes at every order `n`, including `ω`. -/
instance instIsContMDiffContinuousAlternatingMapVectorPrebundleOfFactorialNeZero
    [NeZero ((Fintype.card ι).factorial : 𝕜)] :
    (Bundle.ContinuousAlternatingMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).IsContMDiff IB n :=
  isContMDiff_continuousAlternatingMap_vectorPrebundle

/-- Smooth coordinate changes of Mathlib's alternating-map prebundle induce a `C^n`
vector bundle with its existing topology and atlas. -/
instance instContMDiffVectorBundleContinuousAlternatingMap
    [(Bundle.ContinuousAlternatingMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).IsContMDiff IB n] :
    ContMDiffVectorBundle n (F₁ [⋀^ι]→L[𝕜] F₂) (fun b ↦ E₁ b [⋀^ι]→L[𝕜] E₂ b) IB :=
  (Bundle.ContinuousAlternatingMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).contMDiffVectorBundle IB

end CoordinateChange

/-- Coordinate changes of the alternating-map bundle are differentiable when the domain and
codomain bundles have `C^1` coordinate changes. -/
theorem mdifferentiableOn_continuousAlternatingMapCoordChange
    [ContMDiffVectorBundle 1 F₁ E₁ IB] [ContMDiffVectorBundle 1 F₂ E₂ IB]
    {e₁ e₁' : Trivialization F₁ (π F₁ E₁)} {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    MDifferentiableOn IB 𝓘(𝕜, (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] F₁ [⋀^ι]→L[𝕜] F₂)
      (continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) :=
  (contMDiffOn_continuousAlternatingMapCoordChange (n := 1)).mdifferentiableOn one_ne_zero

section FiniteOrder

variable [ENat.LEInfty n] [ContMDiffVectorBundle n F₁ E₁ IB]
  [ContMDiffVectorBundle n F₂ E₂ IB]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

/-- At finite orders and `∞`, alternating-map coordinate changes are smooth in every
characteristic. -/
instance instIsContMDiffContinuousAlternatingMapVectorPrebundle :
    (Bundle.ContinuousAlternatingMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).IsContMDiff IB n :=
  isContMDiff_continuousAlternatingMap_vectorPrebundle (by
    intro h
    have hle : n ≤ ∞ := ENat.LEInfty.out
    rw [h] at hle
    exact (not_le_of_gt (WithTop.coe_lt_top (⊤ : ℕ∞))) hle |>.elim)

end FiniteOrder

end TauCeti
