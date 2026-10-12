/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct

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

## Main statements

* `TauCeti.lipschitzWith_one_rTensor` and `TauCeti.lipschitzWith_one_lTensor`: tensoring with the
  identity, on either side, is `1`-Lipschitz in the operator.
* `TauCeti.apply_self_pos_of_apply_tmul_tmul`: the tensor product of two positive definite
  Hermitian forms is positive definite.
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
