/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.DifferentialForm.Support
public import TauCeti.Geometry.Manifold.Measure

/-!
# Boundary restriction and null sets on manifolds

This file supplies the measure-theoretic and differential-form interfaces needed at the boundary of
an oriented manifold with boundary. The imported manifold measure API defines null sets chartwise
and proves boundary nullness
for finite-dimensional models with corners. Rough forms on a manifold with boundary restrict to the
boundary manifold by pulling back along the subtype inclusion.
-/

public section

open Set
open MeasureTheory
open scoped Manifold

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) 1 M]
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] {j : ℕ}

/-- Restrict a rough form on a half-space manifold to its boundary manifold by pulling it back
along the subtype inclusion. -/
noncomputable def boundaryRestriction (φ : RoughForm (𝓡∂ (n + 1)) M F j) :
    RoughForm 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((𝓡∂ (n + 1)).boundary M) F j :=
  mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) Subtype.val φ

/-- Evaluation of boundary restriction is evaluation of the original form on the tangent map of the
boundary inclusion. -/
@[simp]
theorem boundaryRestriction_apply (φ : RoughForm (𝓡∂ (n + 1)) M F j)
    (x : (𝓡∂ (n + 1)).boundary M) (v : Fin j → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    boundaryRestriction φ x v = φ x (fun i ↦ mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (𝓡∂ (n + 1)) Subtype.val x (v i)) := by
  simp [boundaryRestriction]

/-- Boundary restriction is the ordinary manifold pullback along boundary inclusion. -/
theorem boundaryRestriction_eq_mpullback (φ : RoughForm (𝓡∂ (n + 1)) M F j) :
    boundaryRestriction φ =
      mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) Subtype.val φ := (rfl)

/-- Boundary restriction preserves the zero form. -/
@[simp]
theorem boundaryRestriction_zero :
    boundaryRestriction (0 : RoughForm (𝓡∂ (n + 1)) M F j) = 0 :=
  mpullback_zero _

/-- Boundary restriction preserves addition. -/
@[simp]
theorem boundaryRestriction_add [ContinuousAdd F]
    (φ ψ : RoughForm (𝓡∂ (n + 1)) M F j) :
    boundaryRestriction (φ + ψ) = boundaryRestriction φ + boundaryRestriction ψ :=
  mpullback_add _ φ ψ

/-- Boundary restriction commutes with finite sums. -/
theorem boundaryRestriction_sum [ContinuousAdd F] {ι : Type*}
    (φ : ι → RoughForm (𝓡∂ (n + 1)) M F j) (s : Finset ι) :
    boundaryRestriction (∑ i ∈ s, φ i) = ∑ i ∈ s, boundaryRestriction (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi,
      boundaryRestriction_add, ih]

section Support

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Restriction to the boundary cannot add support outside the ambient support. -/
theorem tsupport_boundaryRestriction_subset (φ : RoughForm (𝓡∂ (n + 1)) M F j) :
    _root_.tsupport (α := (EuclideanSpace ℝ (Fin n)) [⋀^Fin j]→L[ℝ] F)
        (boundaryRestriction φ) ⊆
      Subtype.val ⁻¹' _root_.tsupport
        (α := (EuclideanSpace ℝ (Fin (n + 1))) [⋀^Fin j]→L[ℝ] F) φ :=
  RoughForm.tsupport_mpullback_subset_preimage continuous_subtype_val φ

/-- Restriction of a compactly supported form to the closed boundary remains compactly supported. -/
theorem isCompact_tsupport_boundaryRestriction {φ : RoughForm (𝓡∂ (n + 1)) M F j}
    (hc : IsCompact (_root_.tsupport (α := (EuclideanSpace ℝ (Fin (n + 1))) [⋀^Fin _]→L[ℝ] F) φ))
    : IsCompact (_root_.tsupport (α := (EuclideanSpace ℝ (Fin n)) [⋀^Fin j]→L[ℝ] F)
        (boundaryRestriction φ)) :=
  RoughForm.isCompact_tsupport_mpullback
    (((𝓡∂ (n + 1)).isClosed_boundary one_ne_zero).isClosedEmbedding_subtypeVal.isProperMap) hc

/-- Support in an ambient chart restricts to support in its induced boundary chart. -/
theorem tsupport_boundaryRestriction_subset_source {φ : RoughForm (𝓡∂ (n + 1)) M F j}
    (α : (𝓡∂ (n + 1)).boundary M)
    (hs : (_root_.tsupport (α := (EuclideanSpace ℝ (Fin (n + 1))) [⋀^Fin _]→L[ℝ] F) φ)
      ⊆ (extChartAt (𝓡∂ (n + 1)) (α : M)).source) :
    (_root_.tsupport (α := (EuclideanSpace ℝ (Fin n)) [⋀^Fin _]→L[ℝ] F) (boundaryRestriction φ)) ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α).source := by
  intro x hx
  have hm := hs (tsupport_boundaryRestriction_subset φ hx)
  simpa only [extChartAt_source, boundaryChartedSpace_chartAt_source, mem_preimage] using hm

/-- A form supported away from the boundary has zero boundary restriction. -/
theorem boundaryRestriction_eq_zero_of_disjoint {φ : RoughForm (𝓡∂ (n + 1)) M F j}
    (hd : Disjoint (_root_.tsupport (α := (EuclideanSpace ℝ (Fin (n + 1))) [⋀^Fin _]→L[ℝ] F) φ)
      ((𝓡∂ (n + 1)).boundary M)) : boundaryRestriction φ = 0 := by
  funext x
  ext v
  rw [boundaryRestriction_apply,
    _root_.image_eq_zero_of_notMem_tsupport
      (α := (EuclideanSpace ℝ (Fin (n + 1))) [⋀^Fin j]→L[ℝ] F)
      (fun hm ↦ Set.disjoint_left.mp hd hm x.property)]
  rfl

end Support

end TauCeti
