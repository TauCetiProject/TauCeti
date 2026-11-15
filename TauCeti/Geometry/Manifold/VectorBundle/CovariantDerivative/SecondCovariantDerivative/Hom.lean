/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.SecondCovariantDerivative
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The second covariant derivative as an induced Hom derivative

For a smooth section `σ`, the second covariant derivative `∇²σ` equals the covariant derivative
of `∇σ`, regarded as a section of `Hom(TM, V)` with the connection induced by `∇ᵀ` and `∇`. This
identification connects the tensor `∇²σ` with the product rule for a bundle map acting on a
field along a curve. The bundle `V` need not have finite rank or a norm.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 4.
-/

public noncomputable section

open Bundle CovariantDerivative FiberBundle
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  (cov : _root_.CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
  (covT : _root_.CovariantDerivative I E (TangentSpace I : M → Type _))
  {σ : Π y : M, V y}

/-- The second covariant derivative of a smooth section is the covariant derivative of its first
covariant derivative, regarded as a section of `Hom(TM, V)` with the induced connection. -/
theorem secondCovariantDerivative_eq_hom_apply (hσ : CMDiff ∞ (T% σ))
    (x : M) (u v : TangentSpace I x) :
    cov.secondCovariantDerivative covT σ x u v = covT.hom cov (cov σ) x u v := by
  have hD : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] V x) x (cov σ x)) :=
    contMDiffOn_univ.mp (ContMDiffCovariantDerivative.contMDiff.contMDiff
      (by simpa using hσ.contMDiffOn))
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E ∞ v
  rw [secondCovariantDerivative_apply cov covT hσ x hY,
    hom_apply covT cov (hD.mdifferentiable (by simp) x) (hY.mdifferentiable (by simp) x)]

end CovariantDerivative
