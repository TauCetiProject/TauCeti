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

This file defines the topological support of a rough differential form and establishes its basic
behavior under the pointwise operations and pullback.  A rough form is a dependent function whose
fibre at `x` is `TangentSpace I x [⋀^Fin k]→L[ℝ] F`, so Mathlib's `tsupport` only elaborates on it
once the model-space codomain `E [⋀^Fin k]→L[ℝ] F` is supplied explicitly.  `RoughForm.tsupport`
is Mathlib's `tsupport` at that codomain, and the basic lemmas below are Mathlib's.
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

/-- The topological support of a rough form: Mathlib's `tsupport`, read with the model-space
codomain `E [⋀^Fin k]→L[ℝ] F` of every fibre. -/
def tsupport (φ : RoughForm I X F k) : Set X := _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ

/-- Every point where a rough form is nonzero belongs to its topological support. -/
theorem support_subset_tsupport (φ : RoughForm I X F k) : {x | φ x ≠ 0} ⊆ φ.tsupport :=
  subset_tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ

/-- The topological support of a rough form is closed. -/
theorem isClosed_tsupport (φ : RoughForm I X F k) : IsClosed φ.tsupport :=
  _root_.isClosed_tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ

/-- The support of a sum is contained in the union of the supports. -/
theorem tsupport_add_subset [ContinuousAdd F] (φ ψ : RoughForm I X F k) :
    (φ + ψ).tsupport ⊆ φ.tsupport ∪ ψ.tsupport :=
  tsupport_add (α := E [⋀^Fin k]→L[ℝ] F) φ ψ

/-- The support of a difference is contained in the union of the supports. -/
theorem tsupport_sub_subset [IsTopologicalAddGroup F] (φ ψ : RoughForm I X F k) :
    (φ - ψ).tsupport ⊆ φ.tsupport ∪ ψ.tsupport :=
  tsupport_sub (α := E [⋀^Fin k]→L[ℝ] F) φ ψ

section SMul

variable [ContinuousConstSMul ℝ F]

-- Mathlib's `tsupport_smul_subset_right` at the codomain `E [⋀^Fin k]→L[ℝ] F` times out at `whnf`
-- matching the fibrewise scalar action on `TangentSpace I x [⋀^Fin k]→L[ℝ] F`, so this is proved
-- directly.
/-- Scalar multiplication does not enlarge the support of a rough form. -/
theorem tsupport_smul_subset (c : ℝ) (φ : RoughForm I X F k) :
    (c • φ).tsupport ⊆ φ.tsupport := by
  refine closure_minimal ?_ φ.isClosed_tsupport
  intro x hx
  by_contra hxsupport
  have hφ : φ x = 0 := by
    by_contra h
    exact hxsupport (φ.support_subset_tsupport h)
  apply hx
  ext v
  simp [hφ]
  rfl

end SMul

/-- The topological support of a pullback is contained in the preimage of the original support. -/
theorem tsupport_mpullback_subset_preimage {f : X → Y} (hf : Continuous f)
    (φ : RoughForm I' Y F k) : (mpullback I I' f φ).tsupport ⊆ f ⁻¹' φ.tsupport := by
  refine closure_minimal ?_ (φ.isClosed_tsupport.preimage hf)
  intro x hx
  apply φ.support_subset_tsupport
  intro hφ
  apply hx
  ext v
  simp [mpullback_apply, hφ]
  rfl

/-- Pullback by a proper map preserves compact topological support. -/
theorem isCompact_tsupport_mpullback {f : X → Y} (hf : IsProperMap f)
    {φ : RoughForm I' Y F k} (hφ : IsCompact φ.tsupport) :
    IsCompact (mpullback I I' f φ).tsupport :=
  (hf.isCompact_preimage hφ).of_isClosed_subset
    (isClosed_tsupport _) (φ.tsupport_mpullback_subset_preimage hf.continuous)

end RoughForm

end TauCeti
