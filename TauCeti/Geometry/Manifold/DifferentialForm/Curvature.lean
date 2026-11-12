/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Endomorphism-valued differential forms

This module supplies the degree-two bundle-valued form carrier used for curvature. Its value
bundle is the continuous-linear endomorphism bundle of a vector bundle, so no global
trivialization is chosen.
-/

public section

open Bundle

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- Smooth endomorphism-valued two-forms on a vector bundle.

The coefficient bundle is the continuous-linear endomorphism bundle of `V`; the form degree is
two.
-/
abbrev CurvatureForm (I : ModelWithCorners ℝ E H) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] (V : M → Type*)
    [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
    [IsManifold I 1 M] : Type _ :=
  SmoothBundleForm I (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x) 2

end TauCeti

end
