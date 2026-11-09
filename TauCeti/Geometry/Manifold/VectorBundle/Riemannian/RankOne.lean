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
# Rank-one maps out of a Riemannian bundle

The rank-one map `v ↦ ⟪τ, v⟫ • σ` depends smoothly on a section `τ` of a finite-rank
Riemannian bundle `V` and a section `σ` of an arbitrary normed vector bundle `W`, as a section
of the Hom bundle from `V` to `W`. Taking `W = V`, this provides smooth matrix units from
orthonormal local frames, with the native Hom-bundle topology.

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
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [targetNorm : ∀ x, NormedAddCommGroup (W x)] [∀ x, NormedSpace ℝ (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W]
  {σ : Π x : M, W x} {τ : Π x : M, V x} {x : M}

/-- Rank-one maps `v ↦ ⟪τ, v⟫ • σ` formed from `C^n` sections `σ` of `W` and `τ` of the
Riemannian bundle `V` are `C^n` sections of the Hom bundle from `V` to `W` at the same point. -/
theorem ContMDiffAt.rankOne_bundle (hσ : CMDiffAt n (T% σ) x)
    (hτ : CMDiffAt n (T% τ) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, F →L[ℝ] F')) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F') (E := fun y ↦ V y →L[ℝ] W y) y
        (rankOne ℝ (σ y) (τ y))) x := by
  apply (TauCeti.contMDiffAt_hom_bundle_iff _ x).2
  intro v
  have hp : ContMDiffAt (I.prod 𝓘(ℝ, F)) I n
      (TotalSpace.proj : TotalSpace F V → M) ⟨x, v⟩ := contMDiffAt_proj V
  have hσp := hσ.comp (⟨x, v⟩ : TotalSpace F V) hp
  have hτp := hτ.comp (⟨x, v⟩ : TotalSpace F V) hp
  exact (hτp.inner_bundle (contMDiffAt_id (I := I.prod 𝓘(ℝ, F)))).smul_totalSpace hσp

end
