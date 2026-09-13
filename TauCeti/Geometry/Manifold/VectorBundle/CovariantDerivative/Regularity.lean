/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Regularity of covariant derivatives along vector fields

This file records the regularity of evaluating a smooth covariant derivative on a smooth vector
field.  It turns the hom-bundle-valued regularity supplied by
`CovariantDerivative.ContMDiffCovariantDerivative` into regularity of the resulting section.

## Main results

* `TauCeti.Manifold.contMDiff_covariantDerivative_apply`: applying a `C^n` covariant derivative
  to a `C^(n + 1)` section along a `C^n` vector field produces a `C^n` section.
-/

public section

open Bundle FiberBundle
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace 𝕜 (V x)]
  [FiberBundle F V] [IsManifold I 1 M] [VectorBundle 𝕜 F V]
  {n : ℕ∞ω}

/-- Applying a `C^n` covariant derivative to a `C^(n + 1)` section along a `C^n` vector field
produces a `C^n` section. -/
theorem contMDiff_covariantDerivative_apply
    (cov : _root_.CovariantDerivative I F V)
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov n]
    {X : Π x : M, TangentSpace I x} {σ : Π x : M, V x}
    (hX : CMDiff n (T% X)) (hσ : CMDiff (n + 1) (T% σ)) :
    CMDiff n (T% (fun x ↦ cov σ x (X x))) := by
  rw [← contMDiffOn_univ]
  exact ContMDiffOn.clm_bundle_apply
    (_root_.CovariantDerivative.ContMDiffCovariantDerivative.contMDiff.contMDiff
      hσ.contMDiffOn) hX.contMDiffOn

end TauCeti.Manifold
