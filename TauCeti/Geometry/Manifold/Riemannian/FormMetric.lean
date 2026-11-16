/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.AlternatingForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Regularity of the pointwise metric on differential forms

The Gram pairing of real differential forms has the regularity of the forms and the
Riemannian metric. This is a scalar function on the manifold, without an orientation
hypothesis. In particular, smooth forms have smooth pointwise squared lengths, as needed
for their geometric integral pairing.

The pairing is `TauCeti.alternatingFormInner` on the existing alternating tangent fibres;
no new form carrier or norm on those fibres is introduced.
-/

public section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n : ℕ∞ω} [IsManifold I (n + 1) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)] {k : ℕ}

/-- The Gram pairing of `C^n` real forms on a manifold with a `C^n` Riemannian metric
is `C^n`, without requiring orientability. -/
theorem IsSmoothForm.contMDiff_alternatingFormInner {α β : RoughForm I M ℝ k}
    (hα : IsSmoothForm I n α) (hβ : IsSmoothForm I n β) :
    ContMDiff I 𝓘(ℝ) n
      (fun x ↦ alternatingFormInner (TangentSpace I x) k (α x) (β x)) := by
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact hα.contMDiff.alternatingFormInner_bundle hβ.contMDiff

end TauCeti
