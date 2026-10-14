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
behavior under the pointwise operations and pullback.  Unlike an ordinary function, a rough form
has a codomain that varies with its base point, so `Function.tsupport` does not apply directly.
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

/-- The topological support of a rough form is the closure of the points where its fibre value is
nonzero.  This is the dependent-fibre analogue of `Function.tsupport`. -/
def tsupport (φ : RoughForm I X F k) : Set X := closure {x | φ x ≠ 0}

/-- Every point where a rough form is nonzero belongs to its topological support. -/
theorem support_subset_tsupport (φ : RoughForm I X F k) : {x | φ x ≠ 0} ⊆ φ.tsupport :=
  subset_closure

/-- The topological support of a rough form is closed. -/
theorem isClosed_tsupport (φ : RoughForm I X F k) : IsClosed φ.tsupport :=
  isClosed_closure

section Add

variable [ContinuousAdd F]

/-- The support of a sum is contained in the union of the supports. -/
theorem tsupport_add_subset (φ ψ : RoughForm I X F k) :
    (φ + ψ).tsupport ⊆ φ.tsupport ∪ ψ.tsupport := by
  refine closure_minimal ?_ (φ.isClosed_tsupport.union ψ.isClosed_tsupport)
  intro x hx
  by_contra hxunion
  rw [mem_union, not_or] at hxunion
  have hφ : φ x = 0 := by
    by_contra h
    exact hxunion.1 (φ.support_subset_tsupport h)
  have hψ : ψ x = 0 := by
    by_contra h
    exact hxunion.2 (ψ.support_subset_tsupport h)
  exact hx (by simp only [Pi.add_apply, hφ, hψ, add_zero])

end Add

section Sub

variable [IsTopologicalAddGroup F]

/-- The support of a difference is contained in the union of the supports. -/
theorem tsupport_sub_subset (φ ψ : RoughForm I X F k) :
    (φ - ψ).tsupport ⊆ φ.tsupport ∪ ψ.tsupport := by
  refine closure_minimal ?_ (φ.isClosed_tsupport.union ψ.isClosed_tsupport)
  intro x hx
  by_contra hxunion
  rw [mem_union, not_or] at hxunion
  have hφ : φ x = 0 := by
    by_contra h
    exact hxunion.1 (φ.support_subset_tsupport h)
  have hψ : ψ x = 0 := by
    by_contra h
    exact hxunion.2 (ψ.support_subset_tsupport h)
  exact hx (by simp only [Pi.sub_apply, hφ, hψ, sub_zero])

end Sub

section SMul

variable [ContinuousConstSMul ℝ F]

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

/-- Pullback by a proper map preserves compact topological support. -/
theorem isCompact_tsupport_mpullback {f : X → Y} (hf : IsProperMap f)
    {φ : RoughForm I' Y F k} (hφ : IsCompact φ.tsupport) :
    IsCompact (mpullback I I' f φ).tsupport :=
  (hf.isCompact_preimage hφ).of_isClosed_subset
    (isClosed_tsupport _) (φ.tsupport_mpullback_subset_preimage hf.continuous)

end RoughForm

end TauCeti
