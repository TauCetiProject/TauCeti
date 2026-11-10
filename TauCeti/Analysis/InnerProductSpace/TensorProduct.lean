/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import TauCeti.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Tensor products of inner product spaces

Mathlib's `ContinuousLinearMap.norm_rTensor_le` and `ContinuousLinearMap.norm_lTensor_le` bound the
norm of `f ⊗ id` and `id ⊗ f` by the norm of `f`. Together with additivity in `f` this says that
`f ↦ f.rTensor H` and `f ↦ f.lTensor H` are contractions, hence continuous in `f`, which is the
form in which the bound is used to make an operator-valued map into a tensor product continuous.

Mathlib's inner product on `E ⊗[𝕜] F` also says that the tensor product of two positive definite
Hermitian forms is positive definite. `TauCeti.apply_self_pos_of_apply_tmul_tmul` states this for
sesquilinear forms on vector spaces carrying no inner product space structure of their own, such as
the Hodge forms of polarized Hodge structures: a sesquilinear form on `W₁ ⊗[𝕜] W₂` whose value on
pure tensors is the product of the values of two positive definite Hermitian forms is positive
definite.

`InnerProductSpace.tensorDualMetric` puts the ordinary product metric on `F ⊗ E*`, with
`E*` carrying the Riesz-transported algebraic dual metric. Evaluation carries this form to
the unnormalized Hilbert–Schmidt pairing `tr(A† B)`. This fixes the metric normalization
when endomorphisms are identified with tensors, without adding an instance on the dual.

## Main statements

* `TauCeti.lipschitzWith_one_rTensor` and `TauCeti.lipschitzWith_one_lTensor`: tensoring with the
  identity, on either side, is `1`-Lipschitz in the operator.
* `TauCeti.apply_self_pos_of_apply_tmul_tmul`: the tensor product of two positive definite
  Hermitian forms is positive definite.
* `TensorProduct.instCompleteSpaceOfFiniteDimensional`: the tensor product of two
  finite-dimensional inner product spaces is complete, which discharges completeness hypotheses
  on tensor products in adjoint statements for finite-dimensional factors.
* `ContinuousLinearMap.rTensor_lTensor_apply_comm`: `f ⊗ 1` and `1 ⊗ g` commute.
* `InnerProductSpace.tensorDualMetric_tmul`: on pure tensors, the metric on `F ⊗ E*` is the
  product of the inner product of `F` and the dual metric of `E`.
* `InnerProductSpace.tensorDualMetric_eq_trace`: evaluation carries this metric to the
  unnormalized Hilbert–Schmidt pairing `tr(A† B)`.
* `InnerProductSpace.isPosSemidef_tensorDualMetric` and
  `InnerProductSpace.tensorDualMetric_self_pos`: this metric is Hermitian and positive definite.
-/

public section

open scoped TensorProduct ComplexOrder

namespace TauCeti

variable {𝕜 E F H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Tensoring a continuous linear map with the identity on the right is a contraction, hence
continuous in the map. This is the elementary continuity statement that Mathlib's
`ContinuousLinearMap.norm_rTensor_le` and additivity give together. -/
theorem lipschitzWith_one_rTensor :
    LipschitzWith 1 fun f : E →L[𝕜] F ↦ f.rTensor H :=
  LipschitzWith.of_dist_le_mul fun f f' ↦ by
    simpa [dist_eq_norm, ← ContinuousLinearMap.rTensor_sub] using
      ContinuousLinearMap.norm_rTensor_le (G := H) (f - f')

/-- Tensoring a continuous linear map with the identity on the left is a contraction, hence
continuous in the map. -/
theorem lipschitzWith_one_lTensor :
    LipschitzWith 1 fun f : E →L[𝕜] F ↦ f.lTensor H :=
  LipschitzWith.of_dist_le_mul fun f f' ↦ by
    simpa [dist_eq_norm, ← ContinuousLinearMap.lTensor_sub] using
      ContinuousLinearMap.norm_lTensor_le (G := H) (f - f')

section Sesquilinear

variable {W₁ W₂ : Type*} [AddCommGroup W₁] [Module 𝕜 W₁] [AddCommGroup W₂] [Module 𝕜 W₂]

/-- The inner product space core of a positive definite Hermitian form. -/
private noncomputable abbrev coreOfPos (h : W₁ →ₗ⋆[𝕜] W₁ →ₗ[𝕜] 𝕜) (hh : h.IsSymm)
    (hpos : ∀ x, x ≠ 0 → 0 < h x x) : InnerProductSpace.Core 𝕜 W₁ where
  inner x y := h x y
  conj_inner_symm x y := hh.eq y x
  re_inner_nonneg x := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact (RCLike.pos_iff.mp (hpos x hx)).1.le
  add_left x y z := by simp
  smul_left x y r := by simp
  definite x hx := by
    by_contra hne
    exact (hpos x hne).ne' hx

/-- **The tensor product of two positive definite Hermitian forms is positive definite.** A
sesquilinear form `H` on `W₁ ⊗[𝕜] W₂` with `H (a ⊗ b) (c ⊗ d) = h₁ a c * h₂ b d`, for positive
definite Hermitian forms `h₁` and `h₂`, is positive on every nonzero vector. -/
theorem apply_self_pos_of_apply_tmul_tmul {h₁ : W₁ →ₗ⋆[𝕜] W₁ →ₗ[𝕜] 𝕜}
    {h₂ : W₂ →ₗ⋆[𝕜] W₂ →ₗ[𝕜] 𝕜} {H : W₁ ⊗[𝕜] W₂ →ₗ⋆[𝕜] W₁ ⊗[𝕜] W₂ →ₗ[𝕜] 𝕜}
    (hH : ∀ a b c d, H (a ⊗ₜ b) (c ⊗ₜ d) = h₁ a c * h₂ b d) (hh₁ : h₁.IsSymm)
    (hh₂ : h₂.IsSymm) (hpos₁ : ∀ x, x ≠ 0 → 0 < h₁ x x) (hpos₂ : ∀ x, x ≠ 0 → 0 < h₂ x x)
    {x : W₁ ⊗[𝕜] W₂} (hx : x ≠ 0) : 0 < H x x := by
  -- Make `h₁` and `h₂` the inner products of `W₁` and `W₂`; then `H` is Mathlib's inner product
  -- on the tensor product, which is positive definite.
  let c₁ := coreOfPos h₁ hh₁ hpos₁
  let c₂ := coreOfPos h₂ hh₂ hpos₂
  let : NormedAddCommGroup W₁ := c₁.toNormedAddCommGroup
  let : NormedAddCommGroup W₂ := c₂.toNormedAddCommGroup
  let : InnerProductSpace 𝕜 W₁ := InnerProductSpace.ofCore c₁.toCore
  let : InnerProductSpace 𝕜 W₂ := InnerProductSpace.ofCore c₂.toCore
  have hinner : ∀ y z : W₁ ⊗[𝕜] W₂, H y z = inner 𝕜 y z := by
    intro y z
    induction y with
    | tmul a b =>
      induction z with
      | tmul c d =>
        rw [hH, TensorProduct.inner_tmul]
        -- The inner products of the two factors are `h₁` and `h₂` by construction.
        rfl
      | add z z' hz hz' => rw [map_add, hz, hz', inner_add_right]
    | add y y' hy hy' => rw [map_add, LinearMap.add_apply, hy, hy', inner_add_left]
  rw [hinner]
  exact RCLike.pos_iff.2 ⟨re_inner_self_pos.2 hx, inner_self_im x⟩

end Sesquilinear

end TauCeti

namespace TensorProduct

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The Hilbert tensor product of two finite-dimensional inner product spaces is complete, so
operators between such tensor products have adjoints. -/
instance instCompleteSpaceOfFiniteDimensional : CompleteSpace (E ⊗[𝕜] F) :=
  FiniteDimensional.complete 𝕜 _

end TensorProduct

namespace ContinuousLinearMap

variable {𝕜 X₀ X₁ Y₀ Y₁ : Type*} [RCLike 𝕜] [NormedAddCommGroup X₀] [InnerProductSpace 𝕜 X₀]
  [NormedAddCommGroup X₁] [InnerProductSpace 𝕜 X₁] [NormedAddCommGroup Y₀] [InnerProductSpace 𝕜 Y₀]
  [NormedAddCommGroup Y₁] [InnerProductSpace 𝕜 Y₁]

/-- `f ⊗ 1` and `1 ⊗ g` commute: the pointwise form of Mathlib's
`ContinuousLinearMap.rTensor_comp_lTensor` and `ContinuousLinearMap.lTensor_comp_rTensor`. -/
theorem rTensor_lTensor_apply_comm (f : X₀ →L[𝕜] X₁) (g : Y₀ →L[𝕜] Y₁) (x : X₀ ⊗[𝕜] Y₀) :
    f.rTensor Y₁ (g.lTensor X₀ x) = g.lTensor X₁ (f.rTensor Y₀ x) := by
  rw [← comp_apply, rTensor_comp_lTensor, ← comp_apply, lTensor_comp_rTensor]

end ContinuousLinearMap

namespace InnerProductSpace

variable (𝕜 E F : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The ordinary tensor metric on `F ⊗ E*`, using the Riesz-transported positive dual
metric. No norm or inner product instance on the algebraic dual is installed. -/
noncomputable def tensorDualMetric :
    F ⊗[𝕜] Module.Dual 𝕜 E →ₗ⋆[𝕜] F ⊗[𝕜] Module.Dual 𝕜 E →ₗ[𝕜] 𝕜 :=
  (TensorProduct.map₂ (innerₛₗ 𝕜) (dualMetric 𝕜 E)).compr₂ₛₗ
    (TensorProduct.lid 𝕜 𝕜).toLinearMap

/-- On pure tensors the tensor metric is the product of the two factor metrics. -/
@[simp]
theorem tensorDualMetric_tmul (x : F) (φ : Module.Dual 𝕜 E)
    (y : F) (ψ : Module.Dual 𝕜 E) :
    tensorDualMetric 𝕜 E F (x ⊗ₜ φ) (y ⊗ₜ ψ) =
      inner 𝕜 x y * dualMetric 𝕜 E φ ψ := by
  simp [tensorDualMetric]

/-- Evaluation identifies the ordinary tensor metric with the unnormalized Hilbert–Schmidt
pairing. The source and target spaces may be different, and either can be zero. -/
theorem tensorDualMetric_eq_trace [FiniteDimensional 𝕜 F]
    (a b : F ⊗[𝕜] Module.Dual 𝕜 E) :
    tensorDualMetric 𝕜 E F a b = LinearMap.trace 𝕜 E
      ((dualTensorHom 𝕜 E F (TensorProduct.comm 𝕜 F (Module.Dual 𝕜 E) a)).adjoint ∘ₗ
        dualTensorHom 𝕜 E F (TensorProduct.comm 𝕜 F (Module.Dual 𝕜 E) b)) := by
  induction a with
  | tmul x φ =>
    induction b with
    | tmul y ψ =>
      obtain ⟨v, rfl, _⟩ := φ.existsUnique_innerₛₗ_eq
      obtain ⟨w, rfl, _⟩ := ψ.existsUnique_innerₛₗ_eq
      let e := stdOrthonormalBasis 𝕜 E
      rw [tensorDualMetric_tmul, dualMetric_innerₛₗ, LinearMap.trace_eq_sum_inner _ e]
      simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right,
        TensorProduct.comm_tmul, dualTensorHom_apply, innerₛₗ_apply_apply, inner_smul_left,
        inner_smul_right]
      simp only [← inner_conj_symm v, starRingEnd_self_apply, ← mul_assoc]
      rw [← Finset.sum_mul, e.sum_inner_mul_inner, mul_comm]
    | add b c hb hc => simp [hb, hc, LinearMap.comp_add]
  | add a c ha hc => simp [ha, hc, LinearMap.add_comp]

/-- The ordinary tensor/dual metric is positive on every nonzero tensor. -/
theorem tensorDualMetric_self_pos {a : F ⊗[𝕜] Module.Dual 𝕜 E} (ha : a ≠ 0) :
    0 < tensorDualMetric 𝕜 E F a a := by
  have hinner : (innerₛₗ 𝕜 : F →ₗ⋆[𝕜] F →ₗ[𝕜] 𝕜).IsSymm :=
    ⟨fun x y => inner_conj_symm y x⟩
  apply TauCeti.apply_self_pos_of_apply_tmul_tmul
    (tensorDualMetric_tmul 𝕜 E F) hinner (isPosSemidef_dualMetric 𝕜 E).isSymm _ _ ha
  · intro x hx
    exact RCLike.pos_iff.2 ⟨re_inner_self_pos.2 hx, inner_self_im x⟩
  · intro φ hφ
    exact ((isPosSemidef_dualMetric 𝕜 E).nonneg φ).lt_of_ne' (by simpa using hφ)

/-- Definiteness of the ordinary tensor/dual metric. -/
@[simp]
theorem tensorDualMetric_self_eq_zero_iff (a : F ⊗[𝕜] Module.Dual 𝕜 E) :
    tensorDualMetric 𝕜 E F a a = 0 ↔ a = 0 :=
  ⟨not_imp_not.1 fun ha ↦ (tensorDualMetric_self_pos 𝕜 E F ha).ne', by rintro rfl; simp⟩

/-- The ordinary tensor/dual metric is Hermitian and positive semidefinite. -/
theorem isPosSemidef_tensorDualMetric : (tensorDualMetric 𝕜 E F).IsPosSemidef where
  eq a b := by
    induction a with
    | tmul x φ =>
      induction b with
      | tmul y ψ =>
        simp only [tensorDualMetric_tmul, map_mul, inner_conj_symm,
          (isPosSemidef_dualMetric 𝕜 E).eq]
      | add b c hb hc => simp [hb, hc]
    | add a c ha hc => simp [ha, hc]
  nonneg a := by
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · exact (tensorDualMetric_self_pos 𝕜 E F ha).le

end InnerProductSpace
