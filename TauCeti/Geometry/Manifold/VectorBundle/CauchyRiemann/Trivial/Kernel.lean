/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Trivial.Basic
import Mathlib.Geometry.Manifold.Complex

/-!
# The kernel of `∂bar` on functions over a compact connected complex manifold

Let `M` be a compact connected complex manifold modelled on `𝓘(ℂ, E)` and `F` a complex normed
space. A real-differentiable function `σ : M → F` with `∂bar σ = 0`
(`TauCeti.SmoothAlmostComplexStructure.dbarFunction` for the almost complex structure of `M`) is
holomorphic (`TauCeti.SmoothAlmostComplexStructure.dbarFunction_ofComplexManifold_eq_zero_iff`),
hence constant by the maximum modulus principle (`MDifferentiable.exists_eq_const_of_compactSpace`).
So the kernel of `∂bar` on real-differentiable functions
(`TauCeti.SmoothAlmostComplexStructure.dbarFunctionKernel`) is the space of constant functions,
a copy of `F` (`TauCeti.SmoothAlmostComplexStructure.dbarFunctionKernel_eq_range_const`, through
`LinearMap.const`); for
`M` nonempty its real dimension is that of `F`
(`TauCeti.SmoothAlmostComplexStructure.finrank_dbarFunctionKernel`). For `F = ℂ`, on a compact
connected Riemann surface, the kernel of `∂bar` on functions has real dimension `2`
(`TauCeti.SmoothAlmostComplexStructure.finrank_dbarFunctionKernel_complex`). This is the kernel
half of the index computation `ind_ℝ ∂bar = 2 - 2·genus` for the trivial bundle in the proof of
the Riemann–Roch formula for real Cauchy–Riemann operators (McDuff–Salamon, Theorem C.1.10).

## Main definitions

* `TauCeti.SmoothAlmostComplexStructure.dbarFunctionKernel`: the real subspace of
  real-differentiable functions `M → F` with `∂bar σ = 0`.
* `TauCeti.SmoothAlmostComplexStructure.constDbarFunctionKernelEquiv`: for `M` nonempty, the
  identification of `F` with the kernel by constant functions.

## Main results

* `TauCeti.SmoothAlmostComplexStructure.exists_eq_const_of_dbarFunction_eq_zero`: on a compact
  connected complex manifold, a real-differentiable function with `∂bar σ = 0` is constant.
* `TauCeti.SmoothAlmostComplexStructure.dbarFunctionKernel_eq_range_const`: the kernel is the space
  of constant functions.
* `TauCeti.SmoothAlmostComplexStructure.finrank_dbarFunctionKernel` and
  `TauCeti.SmoothAlmostComplexStructure.finrank_dbarFunctionKernel_complex`: its real dimension is
  that of `F`, and `2` for complex-valued functions.

## Implementation notes

The kernel is taken on real-differentiable functions, where `∂bar` is additive. For the Sobolev
realization of `∂bar` the same statement needs elliptic regularity of the kernel.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition, AMS
  Colloquium Publications 52 (2012), proof of Theorem C.1.10.
-/

public section

noncomputable section

open Function Set Module
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

namespace SmoothAlmostComplexStructure

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

variable (E M F) in
/-- The kernel of `∂bar` on functions: the real subspace of real-differentiable functions
`σ : M → F` with `∂bar σ = 0` everywhere, for the almost complex structure of the complex
manifold `M`. -/
def dbarFunctionKernel : Submodule ℝ (M → F) where
  carrier :=
    {σ | MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, F) σ ∧ ∀ x, (ofComplexManifold E M).dbarFunction σ x = 0}
  add_mem' {σ τ} hσ hτ := ⟨hσ.1.add hτ.1, fun x ↦ by
    rw [dbarFunction_add _ (hσ.1 x) (hτ.1 x), hσ.2 x, hτ.2 x, add_zero]⟩
  zero_mem' := ⟨mdifferentiable_const, fun x ↦ dbarFunction_zero _ x⟩
  smul_mem' c σ hσ := ⟨hσ.1.const_smul c, fun x ↦ by
    rw [dbarFunction_const_smul, hσ.2 x, smul_zero]⟩

@[simp]
theorem mem_dbarFunctionKernel {σ : M → F} :
    σ ∈ dbarFunctionKernel E M F ↔
      MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, F) σ ∧ ∀ x, (ofComplexManifold E M).dbarFunction σ x = 0 :=
  Iff.rfl

/-- Every constant function lies in the kernel of `∂bar`. -/
theorem const_mem_dbarFunctionKernel (v : F) : Function.const M v ∈ dbarFunctionKernel E M F :=
  ⟨mdifferentiable_const, fun x ↦ dbarFunction_const _ v x⟩

variable [CompactSpace M] [PreconnectedSpace M]

/-- **Real-differentiable functions in the kernel of `∂bar` are constant.** On a compact connected
complex manifold, a real-differentiable function `σ : M → F` with `∂bar σ = 0` everywhere is
holomorphic, hence constant. -/
theorem exists_eq_const_of_dbarFunction_eq_zero {σ : M → F}
    (hσ : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, F) σ)
    (h0 : ∀ x, (ofComplexManifold E M).dbarFunction σ x = 0) :
    ∃ v : F, σ = Function.const M v :=
  MDifferentiable.exists_eq_const_of_compactSpace (I := 𝓘(ℂ, E)) fun x ↦
    (dbarFunction_ofComplexManifold_eq_zero_iff (hσ x)).1 (h0 x)

variable (E M F) in
/-- **The kernel of `∂bar` on functions is the constants.** On a compact connected complex
manifold, the real-differentiable functions `σ : M → F` with `∂bar σ = 0` are exactly the
constant functions: the kernel is the range of `LinearMap.const`. -/
theorem dbarFunctionKernel_eq_range_const :
    dbarFunctionKernel E M F = LinearMap.range (LinearMap.const (R := ℝ) (ι := M) (M₂ := F)) := by
  ext σ
  refine ⟨fun hσ ↦ ?_, ?_⟩
  · obtain ⟨v, rfl⟩ := exists_eq_const_of_dbarFunction_eq_zero hσ.1 hσ.2
    exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩
    exact const_mem_dbarFunctionKernel v

variable (E M F) in
/-- On a nonempty compact connected complex manifold, the constant functions identify `F` with the
kernel of `∂bar` on functions. -/
def constDbarFunctionKernelEquiv [Nonempty M] : F ≃ₗ[ℝ] dbarFunctionKernel E M F :=
  (LinearEquiv.ofInjective (LinearMap.const (R := ℝ) (ι := M) (M₂ := F))
    Function.const_injective).trans
    (LinearEquiv.ofEq _ _ (dbarFunctionKernel_eq_range_const E M F).symm)

/-- `constDbarFunctionKernelEquiv` sends `v` to the constant function `v`. -/
@[simp]
theorem coe_constDbarFunctionKernelEquiv_apply [Nonempty M] (v : F) :
    (constDbarFunctionKernelEquiv E M F v : M → F) = Function.const M v :=
  (rfl)

/-- The inverse of `constDbarFunctionKernelEquiv` sends a function in the kernel, which is
constant, to its value at any point. -/
theorem constDbarFunctionKernelEquiv_symm_apply [Nonempty M] (σ : dbarFunctionKernel E M F)
    (x : M) : (constDbarFunctionKernelEquiv E M F).symm σ = (σ : M → F) x := by
  conv_rhs => rw [← (constDbarFunctionKernelEquiv E M F).apply_symm_apply σ,
    coe_constDbarFunctionKernelEquiv_apply]
  -- The constant function `Function.const M v` takes the value `v` at `x`.
  rfl

variable (E M F) in
/-- **The real dimension of the kernel of `∂bar`.** On a nonempty compact connected complex
manifold, the kernel of `∂bar` on real-differentiable functions into a complex normed space `F`
has the real dimension of `F`. -/
theorem finrank_dbarFunctionKernel [Nonempty M] :
    finrank ℝ (dbarFunctionKernel E M F) = finrank ℝ F :=
  (constDbarFunctionKernelEquiv E M F).finrank_eq.symm

variable (E M) in
/-- On a nonempty compact connected complex manifold, the kernel of `∂bar` on real-differentiable
complex-valued functions, the constants, has real dimension `2`. -/
theorem finrank_dbarFunctionKernel_complex [Nonempty M] :
    finrank ℝ (dbarFunctionKernel E M ℂ) = 2 := by
  rw [finrank_dbarFunctionKernel E M ℂ, Complex.finrank_real_complex]

end SmoothAlmostComplexStructure

end TauCeti
