/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Topological support of rough differential forms

This file establishes how the topological support of a rough differential form behaves under
scalar multiplication and pullback.  A rough form is a dependent function whose fibre at `x` is
`TangentSpace I x [⋀^Fin k]→L[ℝ] F`, so Mathlib's `tsupport` is used with the model-space codomain
`E [⋀^Fin k]→L[ℝ] F` supplied explicitly.
-/

public section

noncomputable section

open Set
open scoped Manifold Topology

namespace TauCeti

variable {E H X E' H' Y F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace Y] [ChartedSpace H' Y]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] {k : ℕ}

namespace RoughForm

section SMul

variable [ContinuousConstSMul ℝ F]

-- Mathlib's `tsupport_smul_subset_right` at the codomain `E [⋀^Fin k]→L[ℝ] F` times out at `whnf`
-- matching the fibrewise scalar action on `TangentSpace I x [⋀^Fin k]→L[ℝ] F`, so this is proved
-- directly.
/-- Scalar multiplication does not enlarge the support of a rough form. -/
theorem tsupport_smul_subset (c : ℝ) (φ : RoughForm I X F k) :
    _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) (c • φ) ⊆
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ := by
  refine closure_minimal ?_ (_root_.isClosed_tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ)
  intro x hx
  by_contra hxsupport
  have hφ : φ x = 0 := by
    by_contra h
    exact hxsupport (subset_tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ h)
  apply hx
  ext v
  simp [hφ]
  rfl

end SMul

/-- The topological support of a pullback is contained in the preimage of the original support. -/
theorem tsupport_mpullback_subset_preimage {f : X → Y} (hf : Continuous f)
    (φ : RoughForm I' Y F k) :
    _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) (mpullback I I' f φ) ⊆
      f ⁻¹' _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] F) φ := by
  refine closure_minimal ?_
    ((_root_.isClosed_tsupport (α := E' [⋀^Fin k]→L[ℝ] F) φ).preimage hf)
  intro x hx
  apply subset_tsupport (α := E' [⋀^Fin k]→L[ℝ] F) φ
  intro hφ
  apply hx
  ext v
  simp [mpullback_apply, hφ]
  rfl

/-- Pullback by a proper map preserves compact topological support. -/
theorem isCompact_tsupport_mpullback {f : X → Y} (hf : IsProperMap f)
    {φ : RoughForm I' Y F k}
    (hφ : IsCompact (_root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] F) φ)) :
    IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) (mpullback I I' f φ)) :=
  (hf.isCompact_preimage hφ).of_isClosed_subset
    (_root_.isClosed_tsupport (α := E [⋀^Fin k]→L[ℝ] F) _)
    (tsupport_mpullback_subset_preimage hf.continuous φ)

end RoughForm

end TauCeti
