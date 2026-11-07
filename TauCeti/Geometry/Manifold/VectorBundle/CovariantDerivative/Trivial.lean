/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The canonical connection on a trivial bundle

Ordinary differentiation of vector-valued functions is a connection on the trivial bundle.
For scalar-valued sections this is the connection used to induce covector connections from
connections on vector bundles, via `CovariantDerivative.hom`.

The construction uses Mathlib's `mvfderiv` and its additivity and Leibniz rules.
-/

public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The canonical connection on a trivial vector bundle is ordinary differentiation of
its sections, viewed as vector-valued functions. -/
def trivial : CovariantDerivative I F (Trivial M F) where
  toFun := mvfderiv I
  isCovariantDerivativeOnUniv := {
    add := by
      intro σ τ x hσ hτ _
      exact mvfderiv_add (by simpa only [mdifferentiableAt_section,
        Trivial.eq_trivialization M F (trivializationAt F (Trivial M F) x),
        Trivial.trivialization_apply] using hσ)
        (by simpa only [mdifferentiableAt_section,
        Trivial.eq_trivialization M F (trivializationAt F (Trivial M F) x),
        Trivial.trivialization_apply] using hτ)
    leibniz := by
      intro σ g x hσ hg _
      exact mvfderiv_smul hg (by simpa only [mdifferentiableAt_section,
        Trivial.eq_trivialization M F (trivializationAt F (Trivial M F) x),
        Trivial.trivialization_apply] using hσ) }

/-- The trivial connection differentiates a section as a vector-valued function. -/
@[simp]
theorem trivial_apply (σ : M → F) (x : M) :
    trivial I F σ x = mvfderiv I σ x := (rfl)

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Ordinary differentiation defines a smooth connection on the trivial bundle. -/
instance : ContMDiffCovariantDerivative (trivial (M := M) I F) ∞ where
  contMDiff.contMDiff {σ} hσ := by
    rw [contMDiffOn_univ] at hσ ⊢
    have hσ' : ContMDiff I 𝓘(ℝ, F) (∞ + 1) σ := by
      intro x
      simpa only [contMDiffAt_section,
        Trivial.eq_trivialization M F (trivializationAt F (Trivial M F) x),
        Trivial.trivialization_apply] using hσ x
    apply (TauCeti.Manifold.contMDiff_hom_iff _).2
    intro X hX
    have hd := (hσ'.contMDiff_mvfderiv_apply (m := ∞) (by simp)).comp hX
    intro x
    simpa only [contMDiffAt_section,
      Trivial.eq_trivialization M F (trivializationAt F (Trivial M F) x),
      Trivial.trivialization_apply, trivial_apply, Function.comp_def] using hd x

end Smooth

end CovariantDerivative
