/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Analysis.InnerProductSpace.Trace.Basic
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Metric index raising of bilinear forms to endomorphisms

On a finite-dimensional real inner product space `E`, `TauCeti.bilinFormToEnd` is the linear
equivalence `BilinForm ℝ E ≃ₗ[ℝ] Module.End ℝ E` identifying each bilinear form `B` with the
endomorphism `B♯` satisfying `⟪B♯ u, v⟫ = B u v`, inverse to metric lowering
`A ↦ (innerₗ E).comp A`. It carries `innerₗ E` to `LinearMap.id`, converts `B.IsSymm` to
`(B♯).IsSymmetric`, identifies `LinearMap.trace` with `TauCeti.bilinFormTrace` and the trace of
a composite `h♯ ∘ k♯` with the full contraction of `h` and `k`, pulls back `B.compl₁₂ f g` via
`LinearMap.adjoint g`, and is equivariant under linear isometric equivalences.

## Main definitions

* `TauCeti.bilinFormToEnd`: the Riesz index-raising equivalence
  `BilinForm ℝ E ≃ₗ[ℝ] Module.End ℝ E`.

## Main results

* `LinearMap.BilinForm.inner_bilinFormToEnd_left`, `LinearMap.bilinFormToEnd_symm_apply`,
  `LinearMap.BilinForm.innerₗ_comp_bilinFormToEnd`, `LinearMap.bilinFormToEnd_innerₗ_comp`, and
  `TauCeti.bilinFormToEnd_innerₗ`: pairing and inverse laws.
* `TauCeti.isSymmetric_bilinFormToEnd_iff`, `LinearMap.BilinForm.trace_bilinFormToEnd`,
  `LinearMap.BilinForm.trace_bilinFormToEnd_comp_bilinFormToEnd`,
  `LinearMap.BilinForm.bilinFormToEnd_compl₁₂`,
  `LinearIsometryEquiv.comp_bilinFormToEnd_compl₁₂`, and
  `LinearIsometryEquiv.comp_bilinFormToEnd_of_eq`: symmetry, trace, pullback, and equivariance.
-/

public section

open LinearMap (BilinForm)
open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace TauCeti

/-- Metric index raising `BilinForm ℝ E ≃ₗ[ℝ] Module.End ℝ E`, sending `B` to `B♯` with
`⟪B♯ u, v⟫ = B u v`. -/
def bilinFormToEnd : BilinForm ℝ E ≃ₗ[ℝ] Module.End ℝ E :=
  (LinearEquiv.refl ℝ E).arrowCongr
    (LinearMap.toContinuousLinearMap ≪≫ₗ
      (InnerProductSpace.toDual ℝ E).symm.toLinearEquiv)

end TauCeti

namespace LinearMap

open TauCeti

/-- The inverse of `bilinFormToEnd` is metric lowering `A ↦ (innerₗ E).comp A`. -/
@[simp] theorem bilinFormToEnd_symm_apply (A : Module.End ℝ E) :
    bilinFormToEnd.symm A = (innerₗ E).comp A :=
  LinearMap.ext₂ fun u v ↦ by simp [bilinFormToEnd]

/-- Raising the metric-lowered form `(innerₗ E).comp A` recovers `A`. -/
@[simp] theorem bilinFormToEnd_innerₗ_comp (A : Module.End ℝ E) :
    bilinFormToEnd ((innerₗ E).comp A) = A := by
  rw [← A.bilinFormToEnd_symm_apply, LinearEquiv.apply_symm_apply]

end LinearMap

namespace LinearMap.BilinForm

open TauCeti

/-- Pairing `bilinFormToEnd B u` with `v` recovers `B u v`. -/
@[simp] theorem inner_bilinFormToEnd_left (B : BilinForm ℝ E) (u v : E) :
    ⟪bilinFormToEnd B u, v⟫ = B u v := by
  simp [bilinFormToEnd, InnerProductSpace.toDual_symm_apply]

/-- Lowering `bilinFormToEnd B` with `innerₗ E` recovers `B`. -/
@[simp] theorem innerₗ_comp_bilinFormToEnd (B : BilinForm ℝ E) :
    (innerₗ E).comp (bilinFormToEnd B) = B := by
  rw [← (bilinFormToEnd B).bilinFormToEnd_symm_apply, LinearEquiv.symm_apply_apply]

/-- The operator trace of `bilinFormToEnd B` equals the metric trace `bilinFormTrace B`. -/
@[simp] theorem trace_bilinFormToEnd (B : BilinForm ℝ E) :
    LinearMap.trace ℝ E (bilinFormToEnd B) = bilinFormTrace B := by
  let b := stdOrthonormalBasis ℝ E
  rw [LinearMap.trace_eq_sum_inner _ b, bilinFormTrace_eq_sum B b]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_comm, B.inner_bilinFormToEnd_left]

/-- For a symmetric bilinear form `h`, the operator trace of `h♯ ∘ k♯` is the full contraction
`∑ᵢⱼ h(eᵢ, eⱼ) k(eᵢ, eⱼ)` in every orthonormal basis `(eᵢ)`. -/
theorem trace_bilinFormToEnd_comp_bilinFormToEnd {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {h : BilinForm ℝ E} (hh : h.IsSymm) (k : BilinForm ℝ E) :
    LinearMap.trace ℝ E (bilinFormToEnd h ∘ₗ bilinFormToEnd k) =
      ∑ i, ∑ j, h (b i) (b j) * k (b i) (b j) := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [LinearMap.comp_apply, real_inner_comm, inner_bilinFormToEnd_left, hh.eq,
    ← b.sum_repr' (bilinFormToEnd k (b i)), map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_smul, smul_eq_mul, real_inner_comm, inner_bilinFormToEnd_left, mul_comm]

/-- Metric index raising pulls back `B.compl₁₂ f g` via `LinearMap.adjoint g`. -/
theorem bilinFormToEnd_compl₁₂ {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (B : BilinForm ℝ E) (f g : F →ₗ[ℝ] E) :
    bilinFormToEnd (B.compl₁₂ f g) = LinearMap.adjoint g ∘ₗ bilinFormToEnd B ∘ₗ f :=
  LinearMap.ext fun _ ↦ ext_inner_right ℝ fun _ ↦ by
    simp [LinearMap.adjoint_inner_left]

end LinearMap.BilinForm

namespace TauCeti

/-- Raising the inner product `innerₗ E` gives the identity endomorphism. -/
@[simp] theorem bilinFormToEnd_innerₗ : bilinFormToEnd (innerₗ E) = LinearMap.id := by
  simpa only [LinearMap.comp_id] using
    (LinearMap.id : Module.End ℝ E).bilinFormToEnd_innerₗ_comp

/-- The raised endomorphism `bilinFormToEnd B` is symmetric iff `B` is symmetric. -/
@[simp] theorem isSymmetric_bilinFormToEnd_iff {B : BilinForm ℝ E} :
    (bilinFormToEnd B).IsSymmetric ↔ B.IsSymm :=
  ⟨fun h ↦ ⟨fun u v ↦ by
    rw [← B.inner_bilinFormToEnd_left, h, real_inner_comm, B.inner_bilinFormToEnd_left]⟩,
   fun h u v ↦ by
    rw [B.inner_bilinFormToEnd_left, real_inner_comm, B.inner_bilinFormToEnd_left, h.eq]⟩

end TauCeti

namespace LinearIsometryEquiv

open TauCeti

/-- Metric index raising is equivariant under linear isometric equivalences. -/
theorem comp_bilinFormToEnd_compl₁₂ {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (e : F ≃ₗᵢ[ℝ] E) (B : BilinForm ℝ E) :
    e.toLinearIsometry.toLinearMap ∘ₗ bilinFormToEnd
        (B.compl₁₂ e.toLinearIsometry.toLinearMap e.toLinearIsometry.toLinearMap) =
      bilinFormToEnd B ∘ₗ e.toLinearIsometry.toLinearMap := by
  have he : e.toLinearIsometry.toLinearMap = e.toLinearMap := LinearMap.ext fun _ ↦ by simp
  rw [B.bilinFormToEnd_compl₁₂, he, e.adjoint_toLinearMap_eq_symm, ← LinearMap.comp_assoc,
    ← LinearMap.comp_assoc]
  ext; simp

/-- Pointwise equivariance of `bilinFormToEnd` under a linear isometric equivalence `e` relating
`B₁` and `B₂` by `B₁ u v = B₂ (e u) (e v)`. -/
theorem comp_bilinFormToEnd_of_eq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (e : F ≃ₗᵢ[ℝ] E) {B₁ : BilinForm ℝ F}
    {B₂ : BilinForm ℝ E} (h : ∀ u v, B₁ u v = B₂ (e u) (e v)) :
    e.toLinearIsometry.toLinearMap ∘ₗ bilinFormToEnd B₁ =
      bilinFormToEnd B₂ ∘ₗ e.toLinearIsometry.toLinearMap := by
  obtain rfl : B₁ = B₂.compl₁₂ e.toLinearIsometry.toLinearMap e.toLinearIsometry.toLinearMap :=
    LinearMap.ext₂ fun u v ↦ by simpa using h u v
  exact e.comp_bilinFormToEnd_compl₁₂ B₂

end LinearIsometryEquiv
