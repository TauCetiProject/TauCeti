/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Analysis.Calculus.ContDiff.ContinuousAlternatingMap
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.ContinuousLinearMap
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Geometry.Manifold.ContMDiff.ContinuousAlternatingMap
import TauCeti.Topology.VectorBundle.Hom

/-!
# Smooth bundles of continuous alternating maps

Continuous alternating maps between two smooth vector bundles form a smooth vector
bundle. This equips the bundles underlying differential forms with smooth coordinate
changes, without changing Mathlib's topology, trivializations, or atlas.

Mathlib's `Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap` provides the
same construction over characteristic-zero fields, together with the fibre-coordinate
regularity criteria such as `contMDiffAt_continuousAlternatingMap_bundle`. The results here
remove the characteristic-zero assumption.

A family of alternating maps of two vectors whose values are given by a `C^n` section of the
bundle of bilinear maps is itself a `C^n` section of the alternating-map bundle
(`TauCeti.contMDiffAt_continuousAlternatingMap_bundle_of_bilinear`). This lets a two-form be
built from a smooth bilinear tensor field without repeating a coordinate computation.

Given a `C^n` fibrewise bilinear pairing of target bundles, the fibrewise paired wedge of two `C^n`
alternating-bundle sections on an arbitrary source vector bundle is again `C^n`
(`ContMDiffWithinAt.pairedWedge_bundle`, `ContMDiffOn.pairedWedge_bundle`,
`ContMDiffAt.pairedWedge_bundle`), computed in coordinates by `TauCeti.inCoordinates_pairedWedge`.

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
open scoped Manifold Bundle ContDiff Topology

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

section Bilinear

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

/-- A family of alternating maps of two vectors whose values are given by a `C^n` section of
the bundle of bilinear maps is a `C^n` section of the alternating-map bundle. -/
theorem contMDiffAt_continuousAlternatingMap_bundle_of_bilinear
    {α : ∀ x, E₁ x [⋀^Fin 2]→L[𝕜] E₂ x} {β : ∀ x, E₁ x →L[𝕜] E₁ x →L[𝕜] E₂ x} {x₀ : B}
    (hβ : ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₁ →L[𝕜] F₂)
        (E := fun x ↦ E₁ x →L[𝕜] E₁ x →L[𝕜] E₂ x) x (β x)) x₀)
    (hα : ∀ x v, α x v = β x (v 0) (v 1)) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁ [⋀^Fin 2]→L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ [⋀^Fin 2]→L[𝕜] F₂)
        (E := fun x ↦ E₁ x [⋀^Fin 2]→L[𝕜] E₂ x) x (α x)) x₀ := by
  rw [contMDiffAt_continuousAlternatingMap_bundle]
  refine ⟨contMDiffAt_id, contMDiffAt_continuousAlternatingMap_apply.2 fun v ↦ ?_⟩
  let e := FiberBundle.trivializationAt F₁ E₁ x₀
  have he : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F₁ E₁ x₀
  have hs (i : Fin 2) : ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁)) n
      (fun y ↦ TotalSpace.mk' F₁ y (e.symm y (v i))) x₀ := by
    rw [contMDiffAt_section_iff]
    refine (contMDiffAt_const (c := v i)).congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds he] with y hy
    exact congr(Prod.snd $(e.apply_mk_symm hy (v i)))
  have hc := (contMDiffAt_totalSpace_iff.1 ((hβ.clm_bundle_apply (hs 0)).clm_bundle_apply (hs 1))).2
  refine hc.congr_of_eventuallyEq ?_
  let e' := FiberBundle.trivializationAt F₂ E₂ x₀
  have he' : x₀ ∈ e'.baseSet := FiberBundle.mem_baseSet_trivializationAt F₂ E₂ x₀
  filter_upwards [e.open_baseSet.mem_nhds he, e'.open_baseSet.mem_nhds he'] with y hy hy'
  simp only [ContinuousAlternatingMap.inCoordinates,
    ContinuousLinearMap.compContinuousAlternatingMap_coe,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, hα, Function.comp_apply]
  rw [Trivialization.symmL_apply _ hy, Trivialization.symmL_apply _ hy]
  exact e'.continuousLinearMapAt_apply_of_mem 𝕜 hy' _

end Bilinear

section PairedWedge

variable {E H M F₀ F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup F₀] [NormedSpace ℝ F₀]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  {V₀ V₁ V₂ V₃ : M → Type*}
  [∀ x, AddCommGroup (V₀ x)] [∀ x, Module ℝ (V₀ x)] [∀ x, TopologicalSpace (V₀ x)]
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
  [∀ x, AddCommGroup (V₃ x)] [∀ x, Module ℝ (V₃ x)] [∀ x, TopologicalSpace (V₃ x)]
  [TopologicalSpace (TotalSpace F₀ V₀)] [FiberBundle F₀ V₀] [VectorBundle ℝ F₀ V₀]
  [TopologicalSpace (TotalSpace F₁ V₁)] [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [TopologicalSpace (TotalSpace F₂ V₂)] [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [TopologicalSpace (TotalSpace F₃ V₃)] [FiberBundle F₃ V₃] [VectorBundle ℝ F₃ V₃]
  [∀ x, IsTopologicalAddGroup (V₃ x)] [∀ x, ContinuousSMul ℝ (V₃ x)]
  {k l : ℕ} {n : WithTop ℕ∞} {s : Set M} {x : M}

/-- In valid coefficient trivializations, coordinates of a fibrewise paired wedge on an arbitrary
source bundle are the paired wedge of the coordinates, with the pairing itself also expressed in
coordinates. -/
theorem inCoordinates_pairedWedge
    (μ : (y : M) → V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y)
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (φ : ∀ y : M, V₀ y [⋀^Fin k]→L[ℝ] V₁ y)
    (ψ : ∀ y : M, V₀ y [⋀^Fin l]→L[ℝ] V₂ y) (x₀ y : M)
    (h₁ : y ∈ (trivializationAt F₁ V₁ x₀).baseSet)
    (h₂ : y ∈ (trivializationAt F₂ V₂ x₀).baseSet)
    (h₃ : y ∈ (trivializationAt F₃ V₃ x₀).baseSet) :
    ContinuousAlternatingMap.inCoordinates F₀ F₃ x₀ y x₀ y
        (ContinuousAlternatingMap.pairedWedge (μ y) (hμ y) (φ y) (ψ y)) =
      ContinuousAlternatingMap.pairedWedgeCLM
        (ContinuousLinearMap.inCoordinates F₁ V₁ (F₂ →L[ℝ] F₃)
          (fun z ↦ V₂ z →L[ℝ] V₃ z) x₀ y x₀ y (μ y))
        (ContinuousAlternatingMap.inCoordinates F₀ F₁ x₀ y x₀ y (φ y))
        (ContinuousAlternatingMap.inCoordinates F₀ F₂ x₀ y x₀ y (ψ y)) := by
  ext v
  simp only [ContinuousAlternatingMap.pairedWedgeCLM_apply,
    ContinuousAlternatingMap.inCoordinates, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe, Function.comp_apply,
    ContinuousAlternatingMap.pairedWedge_apply, map_smul, map_sum]
  congr 2
  funext σ
  rw [ContinuousLinearMap.map_smul_of_tower, inCoordinates_apply_eq₂ h₁ h₂ h₃]
  simp only [Trivialization.continuousLinearMapAt_apply,
    Trivialization.symm_linearMapAt _ h₁, Trivialization.symm_linearMapAt _ h₂,
    Function.comp_def]

section Regularity

variable [∀ x, IsTopologicalAddGroup (V₁ x)] [∀ x, ContinuousSMul ℝ (V₁ x)]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]

/-- A `C^n` bundle pairing takes two `C^n` alternating-bundle sections on an arbitrary source
bundle to a `C^n` section within an arbitrary set. -/
theorem _root_.ContMDiffWithinAt.pairedWedge_bundle
    {μ : (y : M) → V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y}
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiffWithinAt I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) y (μ y)) s x)
    {φ : ∀ y : M, V₀ y [⋀^Fin k]→L[ℝ] V₁ y}
    {ψ : ∀ y : M, V₀ y [⋀^Fin l]→L[ℝ] V₂ y}
    (hφ : ContMDiffWithinAt I (I.prod 𝓘(ℝ, F₀ [⋀^Fin k]→L[ℝ] F₁)) n
      (fun y ↦ TotalSpace.mk' (F₀ [⋀^Fin k]→L[ℝ] F₁) y (φ y)) s x)
    (hψ : ContMDiffWithinAt I (I.prod 𝓘(ℝ, F₀ [⋀^Fin l]→L[ℝ] F₂)) n
      (fun y ↦ TotalSpace.mk' (F₀ [⋀^Fin l]→L[ℝ] F₂) y (ψ y)) s x) :
    ContMDiffWithinAt I (I.prod 𝓘(ℝ, F₀ [⋀^Fin (k + l)]→L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₀ [⋀^Fin (k + l)]→L[ℝ] F₃) y
        (ContinuousAlternatingMap.pairedWedge (μ y) (hμ y) (φ y) (ψ y))) s x := by
  rw [contMDiffWithinAt_hom_bundle] at hpair
  rw [contMDiffWithinAt_continuousAlternatingMap_bundle] at hφ hψ ⊢
  refine ⟨hφ.1, ?_⟩
  have h := (((ContinuousAlternatingMap.pairedWedgeCLM
    (E := F₀) (k := k) (l := l)).contDiff.comp_contMDiffWithinAt hpair.2).clm_apply
      hφ.2).clm_apply hψ.2
  have heq : (fun y ↦ ContinuousAlternatingMap.inCoordinates F₀ F₃ x y x y
      (ContinuousAlternatingMap.pairedWedge (μ y) (hμ y) (φ y) (ψ y))) =ᶠ[𝓝 x]
      (fun y ↦ ContinuousAlternatingMap.pairedWedgeCLM
        (ContinuousLinearMap.inCoordinates F₁ V₁ (F₂ →L[ℝ] F₃)
          (fun z ↦ V₂ z →L[ℝ] V₃ z) x y x y (μ y))
        (ContinuousAlternatingMap.inCoordinates F₀ F₁ x y x y (φ y))
        (ContinuousAlternatingMap.inCoordinates F₀ F₂ x y x y (ψ y))) := by
    filter_upwards [(trivializationAt F₁ V₁ x).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt F₁ V₁ x),
      (trivializationAt F₂ V₂ x).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt F₂ V₂ x),
      (trivializationAt F₃ V₃ x).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt F₃ V₃ x)] with y h₁ h₂ h₃
    exact inCoordinates_pairedWedge μ hμ φ ψ x y h₁ h₂ h₃
  exact h.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds

/-- A `C^n` bundle pairing takes `C^n` alternating-bundle sections on an arbitrary source bundle
to a `C^n` section on a set. -/
theorem _root_.ContMDiffOn.pairedWedge_bundle
    {μ : (y : M) → V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y}
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiffOn I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) y (μ y)) s)
    {φ : ∀ y : M, V₀ y [⋀^Fin k]→L[ℝ] V₁ y}
    {ψ : ∀ y : M, V₀ y [⋀^Fin l]→L[ℝ] V₂ y}
    (hφ : ContMDiffOn I (I.prod 𝓘(ℝ, F₀ [⋀^Fin k]→L[ℝ] F₁)) n
      (fun y ↦ TotalSpace.mk' (F₀ [⋀^Fin k]→L[ℝ] F₁) y (φ y)) s)
    (hψ : ContMDiffOn I (I.prod 𝓘(ℝ, F₀ [⋀^Fin l]→L[ℝ] F₂)) n
      (fun y ↦ TotalSpace.mk' (F₀ [⋀^Fin l]→L[ℝ] F₂) y (ψ y)) s) :
    ContMDiffOn I (I.prod 𝓘(ℝ, F₀ [⋀^Fin (k + l)]→L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₀ [⋀^Fin (k + l)]→L[ℝ] F₃) y
        (ContinuousAlternatingMap.pairedWedge (μ y) (hμ y) (φ y) (ψ y))) s :=
  fun y hy ↦ ContMDiffWithinAt.pairedWedge_bundle hμ (hpair y hy) (hφ y hy) (hψ y hy)

/-- Pointwise regularity of a fibrewise paired wedge on an arbitrary source bundle follows from
regularity of both sections and the pairing. -/
theorem _root_.ContMDiffAt.pairedWedge_bundle
    {μ : (y : M) → V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y}
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiffAt I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) y (μ y)) x)
    {φ : ∀ y : M, V₀ y [⋀^Fin k]→L[ℝ] V₁ y}
    {ψ : ∀ y : M, V₀ y [⋀^Fin l]→L[ℝ] V₂ y}
    (hφ : ContMDiffAt I (I.prod 𝓘(ℝ, F₀ [⋀^Fin k]→L[ℝ] F₁)) n
      (fun y ↦ TotalSpace.mk' (F₀ [⋀^Fin k]→L[ℝ] F₁) y (φ y)) x)
    (hψ : ContMDiffAt I (I.prod 𝓘(ℝ, F₀ [⋀^Fin l]→L[ℝ] F₂)) n
      (fun y ↦ TotalSpace.mk' (F₀ [⋀^Fin l]→L[ℝ] F₂) y (ψ y)) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, F₀ [⋀^Fin (k + l)]→L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₀ [⋀^Fin (k + l)]→L[ℝ] F₃) y
        (ContinuousAlternatingMap.pairedWedge (μ y) (hμ y) (φ y) (ψ y))) x :=
  ContMDiffWithinAt.pairedWedge_bundle hμ hpair hφ hψ

end Regularity

end PairedWedge

end TauCeti
