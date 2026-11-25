/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.DoubleDual.Line

/-!
# Smooth double duality with values in a line bundle

Fibrewise evaluation gives a diffeomorphism from a finite-rank vector bundle `V` to
`Hom(Hom(V, L), L)` for a line bundle `L`. Its smoothness follows from the constant
formula in the induced Hom frames. Taking `L` to be the density line gives the fibre
identification used for testing distributional sections of a density-valued dual.
-/

public noncomputable section

open Bundle FiberBundle
open scoped Topology ContDiff Manifold

namespace TauCeti

variable {𝕜 B F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (V L : B → Type*)
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [∀ x, AddCommGroup (L x)] [∀ x, Module 𝕜 (L x)] [∀ x, TopologicalSpace (L x)]
  [TopologicalSpace (TotalSpace 𝕜 L)] [FiberBundle 𝕜 L] [VectorBundle 𝕜 𝕜 L]

attribute [local instance] Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
  Bundle.ContinuousLinearMap.fiberBundle Bundle.ContinuousLinearMap.vectorBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [ChartedSpace H B] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}

/-- Evaluation into the line-valued double dual is smooth on total spaces. -/
theorem contMDiff_bundleLineDoubleDualEquiv :
    letI := VectorBundle.isTopologicalAddGroup 𝕜 𝕜 L
    letI := VectorBundle.continuousSMul 𝕜 𝕜 L
    ContMDiff (I.prod 𝓘(𝕜, F))
      (I.prod 𝓘(𝕜, (F →L[𝕜] 𝕜) →L[𝕜] 𝕜)) n
      (fun p : TotalSpace F V ↦
        TotalSpace.mk' ((F →L[𝕜] 𝕜) →L[𝕜] 𝕜)
          (E := fun x ↦ (V x →L[𝕜] L x) →L[𝕜] L x) p.proj
          (bundleLineDoubleDualEquiv (F := F) V L p.proj p.snd)) := by
  let := VectorBundle.isTopologicalAddGroup 𝕜 𝕜 L
  let := VectorBundle.continuousSMul 𝕜 𝕜 L
  refine contMDiff_bundleMap_of_constant_coordinates (IB := I) (E₁ := V)
    (E₂ := fun x ↦ (V x →L[𝕜] L x) →L[𝕜] L x)
    (fun x v ↦ bundleLineDoubleDualEquiv (F := F) V L x v)
    (NormedSpace.inclusionInDoubleDual 𝕜 F) ?_
  intro a x hx v
  -- The preferred Hom frame is built from the preferred frames of its domain and codomain.
  exact (trivializationAt F V a).bundleLineDoubleDualEquiv_inFrame (trivializationAt 𝕜 L a)
    ⟨hx.1, hx.2.2⟩ v

/-- A finite-rank bundle and its line-valued double dual have diffeomorphic total spaces
via fibrewise evaluation. -/
def bundleLineDoubleDualDiffeomorph :
    letI := VectorBundle.isTopologicalAddGroup 𝕜 𝕜 L
    letI := VectorBundle.continuousSMul 𝕜 𝕜 L
    TotalSpace F V ≃ₘ^n⟮I.prod 𝓘(𝕜, F), I.prod 𝓘(𝕜, (F →L[𝕜] 𝕜) →L[𝕜] 𝕜)⟯
      TotalSpace ((F →L[𝕜] 𝕜) →L[𝕜] 𝕜) (fun x ↦ (V x →L[𝕜] L x) →L[𝕜] L x) :=
  letI := VectorBundle.isTopologicalAddGroup 𝕜 𝕜 L
  letI := VectorBundle.continuousSMul 𝕜 𝕜 L
  bundleDiffeomorph (bundleLineDoubleDualEquiv (F := F) V L)
    (contMDiff_bundleLineDoubleDualEquiv V L)

/-- The total-space identification acts by fibrewise evaluation. -/
@[simp]
theorem bundleLineDoubleDualDiffeomorph_apply (p : TotalSpace F V) :
    letI := VectorBundle.isTopologicalAddGroup 𝕜 𝕜 L
    letI := VectorBundle.continuousSMul 𝕜 𝕜 L
    bundleLineDoubleDualDiffeomorph V L (I := I) (n := n) p =
      ⟨p.proj, bundleLineDoubleDualEquiv (F := F) V L p.proj p.snd⟩ := by
  let := VectorBundle.isTopologicalAddGroup 𝕜 𝕜 L
  let := VectorBundle.continuousSMul 𝕜 𝕜 L
  exact bundleDiffeomorph_apply _ _ p

/-- The inverse total-space identification acts by the inverse fibre equivalence. -/
@[simp]
theorem bundleLineDoubleDualDiffeomorph_symm_apply :
    letI := VectorBundle.isTopologicalAddGroup 𝕜 𝕜 L
    letI := VectorBundle.continuousSMul 𝕜 𝕜 L
    ∀ p : TotalSpace ((F →L[𝕜] 𝕜) →L[𝕜] 𝕜) (fun x ↦ (V x →L[𝕜] L x) →L[𝕜] L x),
      (bundleLineDoubleDualDiffeomorph (F := F) V L (I := I) (n := n)).symm p =
        ⟨p.proj, (bundleLineDoubleDualEquiv (F := F) V L p.proj).symm p.snd⟩ := by
  intro p
  let := VectorBundle.isTopologicalAddGroup 𝕜 𝕜 L
  let := VectorBundle.continuousSMul 𝕜 𝕜 L
  exact bundleDiffeomorph_symm_apply _ _ p

end TauCeti
