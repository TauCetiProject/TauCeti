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
import TauCeti.Analysis.InnerProductSpace.Dual

/-!
# Metric index raising of bilinear forms to endomorphisms

On a finite-dimensional real inner product space `E`, `TauCeti.bilinFormToEnd` is the linear
equivalence `BilinForm ℝ E ≃ₗ[ℝ] Module.End ℝ E` identifying each bilinear form `B` with the
endomorphism `B♯` satisfying `⟪B♯ u, v⟫ = B u v`, inverse to metric lowering
`A ↦ (innerₗ E).comp A`. It carries `innerₗ E` to `LinearMap.id`, converts `B.IsSymm` to
`(B♯).IsSymmetric`, identifies `LinearMap.trace` with `LinearMap.BilinMap.metricTrace`, pulls back
`B.compl₁₂ f g` via `LinearMap.adjoint g`, and is equivariant under linear isometric equivalences.
For a continuous metric `g` equal to the inner product, `B♯` is `g⁻¹ ∘ B`, the composition of `B`
with the inverse of `g` regarded as a map to the dual.

## Main definitions

* `TauCeti.bilinFormToEnd`: the Riesz index-raising equivalence
  `BilinForm ℝ E ≃ₗ[ℝ] Module.End ℝ E`.

## Main results

* `LinearMap.BilinForm.inner_bilinFormToEnd_left`, `LinearMap.bilinFormToEnd_symm_apply`,
  `LinearMap.BilinForm.innerₗ_comp_bilinFormToEnd`, `LinearMap.bilinFormToEnd_innerₗ_comp`, and
  `TauCeti.bilinFormToEnd_innerₗ`: pairing and inverse laws.
* `TauCeti.isSymmetric_bilinFormToEnd_iff`, `LinearMap.BilinForm.trace_bilinFormToEnd`,
  `LinearMap.BilinForm.bilinFormToEnd_compl₁₂`,
  `LinearIsometryEquiv.comp_bilinFormToEnd_compl₁₂`, and
  `LinearIsometryEquiv.comp_bilinFormToEnd_of_eq`: symmetry, trace, pullback, and equivariance.
* `ContinuousLinearMap.toLinearMap_inverse_comp_eq_bilinFormToEnd`: raising an index with the
  inverse of a continuous bilinear form `g` equal to the inner product is `bilinFormToEnd`.
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

/-- The operator trace of `bilinFormToEnd B` equals the metric trace
`LinearMap.BilinMap.metricTrace B`. -/
@[simp] theorem trace_bilinFormToEnd (B : BilinForm ℝ E) :
    LinearMap.trace ℝ E (bilinFormToEnd B) = LinearMap.BilinMap.metricTrace B := by
  let b := stdOrthonormalBasis ℝ E
  rw [LinearMap.trace_eq_sum_inner _ b, LinearMap.BilinMap.metricTrace_eq_sum B b]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_comm, B.inner_bilinFormToEnd_left]

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

namespace ContinuousLinearMap

open TauCeti

/-- If `g` is the inner product, raising the first index of `B` with `g` is metric index raising
`TauCeti.bilinFormToEnd` of `B`. -/
theorem toLinearMap_inverse_comp_eq_bilinFormToEnd (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ∀ v w, g v w = ⟪v, w⟫) (B : E →L[ℝ] E →L[ℝ] ℝ) :
    ((g.inverse ∘L B : E →L[ℝ] E) : E →ₗ[ℝ] E) = bilinFormToEnd B.toBilinForm := by
  have hinv : g.IsInvertible :=
    InnerProductSpace.isInvertible_of_apply_apply_eq_mul_inner (c := 1) one_ne_zero
      (by simpa only [one_mul] using hg)
  rw [← LinearMap.bilinFormToEnd_innerₗ_comp ((g.inverse ∘L B : E →L[ℝ] E) : E →ₗ[ℝ] E)]
  refine congrArg bilinFormToEnd (LinearMap.ext₂ fun v w ↦ ?_)
  rw [LinearMap.comp_apply, coe_coe, comp_apply, innerₗ_apply_apply, ← hg, toBilinForm_apply]
  exact congrArg (fun φ ↦ φ w) (hinv.self_apply_inverse (B v))

end ContinuousLinearMap

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
