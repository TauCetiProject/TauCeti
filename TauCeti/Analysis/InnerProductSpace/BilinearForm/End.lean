/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Analysis.InnerProductSpace.Trace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Metric index raising of bilinear forms to endomorphisms

On a finite-dimensional real inner product space `E`, `TauCeti.bilinFormToEnd` identifies each
bilinear form `B : BilinForm ℝ E` with the endomorphism `B♯ : Module.End ℝ E` satisfying
`⟪B♯ u, v⟫ = B u v`, inverse to metric lowering `A ↦ (innerₗ E).comp A`. It carries `innerₗ E` to
`LinearMap.id`, converts `B.IsSymm` to `(B♯).IsSymmetric`, identifies `LinearMap.trace` with
`TauCeti.bilinFormTrace`, and is equivariant under linear isometric equivalences.

## Main definitions

* `TauCeti.bilinFormToEnd`: the Riesz index-raising map `BilinForm ℝ E →ₗ[ℝ] Module.End ℝ E`.

## Main results

* `TauCeti.inner_bilinFormToEnd_left`, `TauCeti.innerₗ_comp_bilinFormToEnd`,
  `TauCeti.bilinFormToEnd_innerₗ_comp`, `TauCeti.bilinFormToEnd_innerₗ`: pairing and inverse laws.
* `TauCeti.isSymmetric_bilinFormToEnd_iff`, `TauCeti.trace_bilinFormToEnd`, and
  `TauCeti.linearIsometryEquiv_comp_bilinFormToEnd_compl₁₂`: symmetry, trace, and equivariance.
-/

public section

open LinearMap (BilinForm)
open scoped RealInnerProductSpace

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Metric index raising `BilinForm ℝ E →ₗ[ℝ] Module.End ℝ E`, sending `B` to `B♯` with
`⟪B♯ u, v⟫ = B u v`. -/
def bilinFormToEnd : BilinForm ℝ E →ₗ[ℝ] Module.End ℝ E :=
  ((LinearEquiv.refl ℝ E).arrowCongr
    (LinearMap.toContinuousLinearMap ≪≫ₗ
      (InnerProductSpace.toDual ℝ E).symm.toLinearEquiv)).toLinearMap

/-- Pairing `bilinFormToEnd B u` with `v` recovers `B u v`. -/
@[simp] theorem inner_bilinFormToEnd_left (B : BilinForm ℝ E) (u v : E) :
    ⟪bilinFormToEnd B u, v⟫ = B u v := by
  simp [bilinFormToEnd, InnerProductSpace.toDual_symm_apply]

/-- Lowering `bilinFormToEnd B` with `innerₗ E` recovers `B`. -/
@[simp] theorem innerₗ_comp_bilinFormToEnd (B : BilinForm ℝ E) :
    (innerₗ E).comp (bilinFormToEnd B) = B := LinearMap.ext₂ (inner_bilinFormToEnd_left B)

/-- Raising the metric-lowered form `(innerₗ E).comp A` recovers `A`. -/
@[simp] theorem bilinFormToEnd_innerₗ_comp (A : Module.End ℝ E) :
    bilinFormToEnd ((innerₗ E).comp A) = A :=
  LinearMap.ext fun _ ↦ ext_inner_right ℝ fun _ ↦ by simp

/-- Raising the inner product `innerₗ E` gives the identity endomorphism. -/
@[simp] theorem bilinFormToEnd_innerₗ : bilinFormToEnd (innerₗ E) = LinearMap.id := by
  simpa only [LinearMap.comp_id] using bilinFormToEnd_innerₗ_comp (LinearMap.id : Module.End ℝ E)

/-- The raised endomorphism `bilinFormToEnd B` is symmetric iff `B` is symmetric. -/
theorem isSymmetric_bilinFormToEnd_iff {B : BilinForm ℝ E} :
    (bilinFormToEnd B).IsSymmetric ↔ B.IsSymm :=
  ⟨fun h ↦ ⟨fun u v ↦ by
    rw [← inner_bilinFormToEnd_left, ← inner_bilinFormToEnd_left, real_inner_comm u]; exact h u v⟩,
   fun h u v ↦ by
    rw [inner_bilinFormToEnd_left, real_inner_comm _ u, inner_bilinFormToEnd_left]; exact h.eq u v⟩

/-- The operator trace of `bilinFormToEnd B` equals the metric trace `bilinFormTrace B`. -/
@[simp] theorem trace_bilinFormToEnd (B : BilinForm ℝ E) :
    LinearMap.trace ℝ E (bilinFormToEnd B) = bilinFormTrace B := by
  let b := stdOrthonormalBasis ℝ E
  rw [LinearMap.trace_eq_sum_inner _ b, bilinFormTrace_eq_sum B b]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_comm, inner_bilinFormToEnd_left]

/-- Metric index raising is equivariant under linear isometric equivalences. -/
theorem linearIsometryEquiv_comp_bilinFormToEnd_compl₁₂ {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (e : F ≃ₗᵢ[ℝ] E) (B : BilinForm ℝ E) :
    e.toLinearIsometry.toLinearMap ∘ₗ bilinFormToEnd
        (B.compl₁₂ e.toLinearIsometry.toLinearMap e.toLinearIsometry.toLinearMap) =
      bilinFormToEnd B ∘ₗ e.toLinearIsometry.toLinearMap :=
  LinearMap.ext fun u ↦ ext_inner_right ℝ fun v ↦ by
    simp only [LinearMap.comp_apply, LinearIsometry.coe_toLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, inner_bilinFormToEnd_left]
    rw [← e.apply_symm_apply v, e.inner_map_map, inner_bilinFormToEnd_left, LinearMap.compl₁₂_apply]
    simp

end TauCeti
