/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne

/-!
# The canonical connection on a trivial bundle

Ordinary differentiation gives a connection on the trivial bundle `M × F`. Combining it
with a tangent connection through `CovariantDerivative.hom` gives the induced connection
on fixed-coefficient covector fields. This allows comparison of covariant differentiation
with the ordinary exterior derivative, without choosing a frame for the tangent bundle.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 4
  (connections on trivial bundles and induced connections).
-/

public noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The canonical connection on the trivial bundle: its covariant derivative is the ordinary
manifold derivative, with values read in the fixed coefficient space. -/
def trivial : CovariantDerivative I F (Bundle.Trivial M F) where
  toFun := mvfderiv I
  isCovariantDerivativeOnUniv := {
    add := by
      intro σ τ x hσ hτ _
      simp only [mdifferentiableAt_section, Trivial.fiberBundle_trivializationAt',
        Trivial.trivialization_apply] at hσ hτ
      exact mvfderiv_add hσ hτ
    leibniz := by
      intro σ f x hσ hf _
      simp only [mdifferentiableAt_section, Trivial.fiberBundle_trivializationAt',
        Trivial.trivialization_apply] at hσ
      exact mvfderiv_smul hf hσ }

/-- The canonical trivial-bundle connection evaluates as ordinary differentiation. -/
@[simp]
theorem trivial_apply (σ : M → F) (x : M) :
    trivial (I := I) F σ x = mvfderiv I σ x := (rfl)

end CovariantDerivative

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω}

/-- The canonical connection on a real trivial bundle is `C^n` at every regularity order. -/
instance : ContMDiffCovariantDerivative (trivial (I := I) (M := M) F) n where
  contMDiff.contMDiff {σ} hσ := by
    rw [contMDiffOn_univ] at hσ ⊢
    have hf : ContMDiff I 𝓘(ℝ, F) (n + 1) σ := fun x ↦ by
      simpa only [contMDiffAt_section_iff, Trivial.fiberBundle_trivializationAt',
        Trivial.trivialization_apply] using hσ x
    exact hf.contMDiff_totalSpaceMk_mvfderiv

end CovariantDerivative
