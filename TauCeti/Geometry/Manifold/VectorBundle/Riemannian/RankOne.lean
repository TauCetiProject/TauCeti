/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Analysis.InnerProductSpace.LinearMap
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# Rank-one endomorphisms of a Riemannian bundle

The rank-one endomorphism `v ↦ ⟪τ, v⟫ • σ` depends smoothly on two sections
`σ` and `τ` of a finite-rank Riemannian bundle. This provides smooth matrix units
from orthonormal local frames, with the native Hom-bundle topology.

The construction is Mathlib's `InnerProductSpace.rankOne`; smoothness uses the
bundle inner product and the total-space criterion for smooth homomorphisms.
-/

public section

open Bundle InnerProductSpace
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [fiberNorm : ∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} [IsContMDiffRiemannianBundle I n F V]
  {σ τ : Π x : M, V x} {x : M}

/-- Rank-one endomorphisms formed from two `C^n` sections are `C^n` at the same point. -/
theorem ContMDiffAt.rankOne_bundle (hσ : CMDiffAt n (T% σ) x)
    (hτ : CMDiffAt n (T% τ) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F) y (rankOne ℝ (σ y) (τ y))) x := by
  apply (TauCeti.contMDiffAt_hom_bundle_iff _ x).2
  intro v
  have hp : ContMDiffAt (I.prod 𝓘(ℝ, F)) I n
      (TotalSpace.proj : TotalSpace F V → M) ⟨x, v⟩ := contMDiffAt_proj V
  have hσp := hσ.comp (⟨x, v⟩ : TotalSpace F V) hp
  have hτp := hτ.comp (⟨x, v⟩ : TotalSpace F V) hp
  exact (hτp.inner_bundle (contMDiffAt_id (I := I.prod 𝓘(ℝ, F)))).smul_totalSpace hσp

end
