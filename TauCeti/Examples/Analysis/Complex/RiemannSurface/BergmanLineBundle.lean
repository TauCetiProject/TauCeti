/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Cohomology.BergmanCochains
public import TauCeti.Geometry.Manifold.Instances.OnePoint.LineBundle
import TauCeti.Geometry.Manifold.VectorBundle.MaximalAtlas
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Native line-bundle Bergman realizations

These examples use arbitrary rank-one model spaces and the actual frames of `𝒪(1)` on the
Riemann sphere. Its transition from the affine to the inverted frame is nonconstant. A
holomorphic function with a pole at the boundary of the unit disc is realized only after
proper shrinking; no square-integrability on the whole unit disc is asserted.
-/

public noncomputable section

open Bundle CategoryTheory Metric Opposite Set TopologicalSpace TauCeti
open scoped ContDiff Manifold

namespace TauCeti.Examples.BergmanLineBundle

/-- Rank one supplies scalar coordinates without prescribing a basis or norm normalization. -/
example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (hF : Module.finrank ℂ F = 1) : Nonempty (F ≃L[ℂ] ℂ) := by
  let : Module.Finite ℂ F := Module.finite_of_finrank_eq_succ hF
  exact FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
    (hF.trans (Module.finrank_self ℂ).symm)

/-- For an arbitrary rank-one model, the native dimension theorem supplies coordinates and
therefore an injective realization; scalar model coordinates are not an additional existence
assumption on callers. -/
example {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] (hF : Module.finrank ℂ F = 1)
    {V : X → Type} [TopologicalSpace (TotalSpace F V)]
    [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)] [∀ x, TopologicalSpace (V x)]
    [FiberBundle F V] [VectorBundle ℂ F V] [ContMDiffVectorBundle ω F V 𝓘(ℂ)]
    (τ : Trivialization F (π F V)) [τ.IsLinear ℂ]
    (hτa : τ.toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear X F 𝓘(ℂ) ω).maximalAtlas (TotalSpace F V))
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (U : Opens X) (hU : (U : Set X) ⊆ e.source) (hτ : (U : Set X) ⊆ τ.baseSet) :
    ∃ q : F ≃L[ℂ] ℂ, Function.Injective (τ.bergmanSection q hτa he hU hτ) := by
  let : Module.Finite ℂ F := Module.finite_of_finrank_eq_succ hF
  obtain ⟨q⟩ := FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
    (hF.trans (Module.finrank_self ℂ).symm)
  exact ⟨q, τ.bergmanSection_injective q hτa he hU hτ⟩

/-- The affine-to-inverted `𝒪(1)` factor is the nonconstant function `z⁻¹`. -/
example (z : ℂ) (hz : z ≠ 0) :
    ((OnePoint.twistCore (𝕜 := ℂ) 1).localTriv
      ((0 : ℂ) : OnePoint ℂ)).scalarCoordChange
        ((OnePoint.twistCore 1).localTriv (OnePoint.infty : OnePoint ℂ))
        (ContinuousLinearEquiv.refl ℂ ℂ)
        (ContinuousLinearEquiv.refl ℂ ℂ) (z : OnePoint ℂ) = z⁻¹ := by
  rw [OnePoint.twistCore_localTriv_scalarCoordChange]
  · simp
  · simp
  · simpa using hz

/-- The actual scalar frame changes of `𝒪(1)` are holomorphic on the chart overlaps. -/
example (i j : OnePoint ℂ) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω
      (((OnePoint.twistCore (𝕜 := ℂ) 1).localTriv i).scalarCoordChange
        ((OnePoint.twistCore 1).localTriv j)
        (ContinuousLinearEquiv.refl ℂ ℂ) (ContinuousLinearEquiv.refl ℂ ℂ))
      (((OnePoint.twistCore 1).localTriv i).baseSet ∩
        ((OnePoint.twistCore 1).localTriv j).baseSet) := by
  let : MemTrivializationAtlas ((OnePoint.twistCore (𝕜 := ℂ) 1).localTriv i) := ⟨⟨i, rfl⟩⟩
  let : MemTrivializationAtlas ((OnePoint.twistCore (𝕜 := ℂ) 1).localTriv j) := ⟨⟨j, rfl⟩⟩
  exact Trivialization.contMDiffOn_scalarCoordChange _ _ _ _
    (Trivialization.mem_maximalAtlas_of_memTrivializationAtlas 𝓘(ℂ) ω _)
    (Trivialization.mem_maximalAtlas_of_memTrivializationAtlas 𝓘(ℂ) ω _)

/-- Constant coordinate rescaling changes the scalar transition even when the frame is fixed. -/
example {X : Type*} [TopologicalSpace X] {V : X → Type*}
    [TopologicalSpace (TotalSpace ℂ V)] [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    (τ : Trivialization ℂ (π ℂ V)) [τ.IsLinear ℂ] {x : X} (hx : x ∈ τ.baseSet) :
    τ.scalarCoordChange τ (ContinuousLinearEquiv.refl ℂ ℂ)
        (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 2 (by norm_num))) x = 2 := by
  rw [Trivialization.scalarCoordChange_def, τ.coordChangeL_same_apply ℂ hx]
  simp

/-- The native holomorphic unit disc. -/
def poleDomain : Opens ℂ := ⟨ball 0 1, isOpen_ball⟩

/-- A proper concentric shrink, whose compact closure avoids the pole at `1`. -/
def poleShrink : Opens ℂ := ⟨ball 0 (1 / 2 : ℝ), isOpen_ball⟩

/-- The boundary-pole function as an actual native holomorphic section. -/
def boundaryPole : (holomorphicStructureSheafModules 𝓘(ℂ) ℂ).obj.obj (op poleDomain) :=
  holomorphicStructureSheafModules.ofContMDiff (fun x : poleDomain ↦ (1 - (x : ℂ))⁻¹)
    ((contMDiff_const.sub contMDiff_subtypeVal).inv₀ (by
      intro x hx
      have he : (x : ℂ) = 1 := (sub_eq_zero.1 hx).symm
      have h := x.property
      simp [poleDomain, he] at h))

/-- Compact containment is established for the actual proper shrink. -/
theorem poleShrink_compact : IsCompact (closure (poleShrink : Set ℂ)) := by
  simpa only [poleShrink, Opens.coe_mk, closure_ball (0 : ℂ) (by norm_num : (1 / 2 : ℝ) ≠ 0)] using
    isCompact_closedBall (0 : ℂ) (1 / 2 : ℝ)

/-- Its closure lies strictly inside the larger holomorphic domain. -/
theorem poleShrink_subset : closure (poleShrink : Set ℂ) ⊆ poleDomain := by
  simp only [poleShrink, Opens.coe_mk, closure_ball (0 : ℂ)
    (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  intro z hz
  exact closedBall_subset_ball (by norm_num : (1 / 2 : ℝ) < 1) hz

/-- The boundary-pole function has a canonical square-integrable realization on the proper
shrink, obtained through compact boundedness and the native `ofBounded` inclusion. -/
def boundaryPoleBergman : bergmanSpace ℂ ((chartAt ℂ (0 : ℂ)).imageOpens poleShrink) :=
  (chartAt ℂ (0 : ℂ)).holomorphicSectionToBergman
    (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ (0 : ℂ)))
    (fun _ _ ↦ by simp) poleShrink_compact poleShrink_subset boundaryPole

/-- The constructed Bergman representative recovers the pole function throughout the smaller
disc. -/
theorem boundaryPoleBergman_apply (x : poleShrink) :
    BergmanSpace.representative boundaryPoleBergman (chartAt ℂ (0 : ℂ) x) =
      (1 - (x : ℂ))⁻¹ := by
  rw [boundaryPoleBergman]
  simpa only [boundaryPole, holomorphicStructureSheafModules.ofContMDiff_apply] using
    (chartAt ℂ (0 : ℂ)).holomorphicSectionToBergman_apply
      (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ (0 : ℂ))) (fun _ _ ↦ by simp)
      poleShrink_compact poleShrink_subset boundaryPole x

/-- The actual holomorphic `𝒪(1)` bundle admits realization in every native chart frame. -/
def oOneRealization (i : OnePoint ℂ) (U : Opens (OnePoint ℂ))
    (hU : (U : Set (OnePoint ℂ)) ⊆ (chartAt ℂ i).source) :
    bergmanSpace ℂ ((chartAt ℂ i).imageOpens U) →ₗ[ℂ]
      (holomorphicSectionSheaf 𝓘(ℂ) ℂ (OnePoint.twistCore (𝕜 := ℂ) 1).Fiber).obj.obj (op U) := by
  -- The core atlas contains this local trivialization. Supply its atlas witness for the
  -- holomorphic maximal-atlas criterion.
  letI : MemTrivializationAtlas ((OnePoint.twistCore (𝕜 := ℂ) 1).localTriv i) := ⟨⟨i, rfl⟩⟩
  exact ((OnePoint.twistCore (𝕜 := ℂ) 1).localTriv i).bergmanSection
    (ContinuousLinearEquiv.refl ℂ ℂ)
    (Trivialization.mem_maximalAtlas_of_memTrivializationAtlas 𝓘(ℂ) ω _)
    (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ i)) hU
    (by simpa only [OnePoint.twistCore_localTriv_baseSet] using hU)

/-- This concrete realization preserves every scalar Bergman class. -/
theorem oOneRealization_injective (i : OnePoint ℂ) (U : Opens (OnePoint ℂ))
    (hU : (U : Set (OnePoint ℂ)) ⊆ (chartAt ℂ i).source) :
    Function.Injective (oOneRealization i U hU) := by
  rw [oOneRealization]
  exact Trivialization.bergmanSection_injective _ _ _ _ _ _

/-- There are no artificial constraints or choices on an empty overlap. -/
example {X : Type} [TopologicalSpace X] (e : OpenPartialHomeomorph X ℂ)
    (u : bergmanSpace ℂ (e.imageOpens ⊥)) : u = 0 := by
  apply BergmanSpace.ext
  intro z hz
  exact False.elim (OpenPartialHomeomorph.mem_imageOpens.1 hz).2

/-- Empty covers retain the native empty product of cochains. -/
example (e : Empty → OpenPartialHomeomorph ℂ ℂ) (W : Empty → Opens ℂ)
    (η : (i : Empty) → bergmanSpace ℂ ((e i).imageOpens (W i))) : η = 0 := by
  funext i
  exact i.elim

end TauCeti.Examples.BergmanLineBundle
