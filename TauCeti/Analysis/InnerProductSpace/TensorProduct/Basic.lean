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
* `TensorProduct.norm_mapL` and `TensorProduct.denseRange_mapL`: the tensor product `f ⊗ g` of
  bounded operators has norm `‖f‖ * ‖g‖` and preserves dense range;
  `ContinuousLinearMap.norm_rTensor` and `ContinuousLinearMap.norm_lTensor` (`rTensorₗᵢ`,
  `lTensorₗᵢ`, `rTensor_inj`, `lTensor_inj`) are the cases `f ⊗ 1` and `1 ⊗ g` for a nonzero other
  factor (`rTensor_of_subsingleton`, `lTensor_of_subsingleton` on subsingletons).
* `TensorProduct.inner_mapL_left`: if `f'` and `g'` are formal adjoints of `f` and `g`, then
  `mapL f' g'` is a formal adjoint of `mapL f g`.
* `ContinuousLinearMap.rTensor_lTensor_apply_comm`: `f ⊗ 1` and `1 ⊗ g` commute.
* `ContinuousLinearMap.rTensor_adjoint_inner_left` and
  `ContinuousLinearMap.lTensor_adjoint_inner_left`, with their `_right` forms: `f† ⊗ 1` and
  `1 ⊗ g†` are formal adjoints of `f ⊗ 1` and `1 ⊗ g` on the algebraic tensor product, which
  need not be complete, so that Mathlib's `ContinuousLinearMap.adjoint_rTensor` does not apply.
* `rTensor_adjoint_comp_self_apply_add_lTensor_adjoint_comp_self_apply_eq_zero_iff`, in the
  `ContinuousLinearMap` namespace: the positive tensor sum `A†A ⊗ 1 + 1 ⊗ B†B` vanishes exactly
  on the common kernel of `A ⊗ 1` and `1 ⊗ B`.
* `ContinuousLinearMap.denseRange_rTensor` and `ContinuousLinearMap.denseRange_lTensor`: if `f` has
  dense range then so do `f ⊗ 1` and `1 ⊗ f`.
* `InnerProductSpace.tensorDualMetric_tmul`: on pure tensors, the metric on `F ⊗ E*` is the
  product of the inner product of `F` and the dual metric of `E`.
* `InnerProductSpace.tensorDualMetric_eq_trace`: evaluation carries this metric to the
  unnormalized Hilbert–Schmidt pairing `tr(A† B)`.
* `InnerProductSpace.isPosSemidef_tensorDualMetric` and
  `InnerProductSpace.tensorDualMetric_self_pos`: this metric is Hermitian and positive definite.
-/

public section

open scoped TensorProduct ComplexOrder InnerProductSpace

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

section mapL

variable {𝕜 E E' F F' : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F']

/-- The tensor product `f ⊗ g` of bounded operators has norm `‖f‖ * ‖g‖`, sharpening Mathlib's
`TensorProduct.norm_mapL_le`. -/
@[simp]
theorem norm_mapL (f : E →L[𝕜] E') (g : F →L[𝕜] F') : ‖mapL f g‖ = ‖f‖ * ‖g‖ := by
  refine le_antisymm (norm_mapL_le f g) ?_
  set C := ‖mapL f g‖
  have h (x : E) (y : F) : ‖f x‖ * ‖g y‖ ≤ C * ‖y‖ * ‖x‖ := by
    have := (mapL f g).le_opNorm (x ⊗ₜ[𝕜] y)
    simp only [mapL_tmul, norm_tmul] at this
    exact this.trans_eq (by ring)
  -- Testing on `x ⊗ₜ y` bounds `‖f‖ * ‖g y‖`, and then `‖f‖ * ‖g‖`.
  have hy (y : F) : ‖f‖ * ‖g y‖ ≤ C * ‖y‖ := by
    rcases (norm_nonneg (g y)).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]
      positivity
    · refine (le_div_iff₀ hpos).1 <| f.opNorm_le_bound (by positivity) fun x ↦ ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
      exact h x y
  rcases (norm_nonneg f).eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]
    positivity
  · rw [mul_comm ‖f‖]
    refine (le_div_iff₀ hpos).1 <| g.opNorm_le_bound (by positivity) fun y ↦ ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    exact (mul_comm _ _).trans_le (hy y)

/-- If `f'` and `g'` are formal adjoints of `f` and `g`, then `mapL f' g'` is a formal adjoint of
`mapL f g`. No completeness is needed. -/
theorem inner_mapL_left {f : E →L[𝕜] E'} {f' : E' →L[𝕜] E} {g : F →L[𝕜] F'} {g' : F' →L[𝕜] F}
    (hf : ∀ x y, ⟪f x, y⟫_𝕜 = ⟪x, f' y⟫_𝕜) (hg : ∀ x y, ⟪g x, y⟫_𝕜 = ⟪x, g' y⟫_𝕜)
    (u : E ⊗[𝕜] F) (v : E' ⊗[𝕜] F') : ⟪mapL f g u, v⟫_𝕜 = ⟪u, mapL f' g' v⟫_𝕜 := by
  induction u using TensorProduct.inductionOn with
  | add u₁ u₂ h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]
  | tmul x y =>
    induction v using TensorProduct.inductionOn with
    | add v₁ v₂ h₁ h₂ => simp only [map_add, inner_add_right, h₁, h₂]
    | tmul x' y' => simp [hf, hg]

/-- The tensor product of two bounded linear maps with dense range has dense range. -/
theorem denseRange_mapL {f : E →L[𝕜] E'} {g : F →L[𝕜] F'} (hf : DenseRange f) (hg : DenseRange g) :
    DenseRange (mapL f g) := by
  let R : Submodule 𝕜 (E' ⊗[𝕜] F') := LinearMap.range (mapL f g).toLinearMap
  have hmem (z : E' ⊗[𝕜] F') : z ∈ R.topologicalClosure := by
    induction z using TensorProduct.inductionOn with
    | tmul y w =>
      refine hf.induction_on y
        (R.isClosed_topologicalClosure.preimage ((mkL 𝕜 E' F').flip w).continuous)
        fun x ↦ hg.induction_on w
          (R.isClosed_topologicalClosure.preimage (mkL 𝕜 E' F' (f x)).continuous)
          fun z ↦ R.le_topologicalClosure ⟨x ⊗ₜ[𝕜] z, rfl⟩
    | add _ _ hz₁ hz₂ => exact add_mem hz₁ hz₂
  intro z
  have hz : z ∈ (R.topologicalClosure : Set (E' ⊗[𝕜] F')) := hmem z
  rwa [Submodule.topologicalClosure_coe, LinearMap.coe_range, ContinuousLinearMap.coe_coe] at hz

end mapL

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The Hilbert tensor product of two finite-dimensional inner product spaces is complete, so
operators between such tensor products have adjoints. -/
instance instCompleteSpaceOfFiniteDimensional : CompleteSpace (E ⊗[𝕜] F) :=
  FiniteDimensional.completeSpace 𝕜 _

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

/-- Tensoring with a nonzero space `Y₀` on the right preserves the operator norm, sharpening
Mathlib's `ContinuousLinearMap.norm_rTensor_le`. -/
@[simp]
theorem norm_rTensor [Nontrivial Y₀] (f : X₀ →L[𝕜] X₁) : ‖f.rTensor Y₀‖ = ‖f‖ := by
  rw [rTensor_eq_mapL, TensorProduct.norm_mapL, norm_id, mul_one]

/-- Tensoring with a nonzero space `X₀` on the left preserves the operator norm, sharpening
Mathlib's `ContinuousLinearMap.norm_lTensor_le`. -/
@[simp]
theorem norm_lTensor [Nontrivial X₀] (g : Y₀ →L[𝕜] Y₁) : ‖g.lTensor X₀‖ = ‖g‖ := by
  rw [lTensor_eq_mapL, TensorProduct.norm_mapL, norm_id, one_mul]

variable (𝕜 X₀ X₁ Y₀) in
/-- Tensoring on the right with the identity of a nontrivial space, as a linear isometry. -/
noncomputable def rTensorₗᵢ [Nontrivial Y₀] :
    (X₀ →L[𝕜] X₁) →ₗᵢ[𝕜] ((X₀ ⊗[𝕜] Y₀) →L[𝕜] (X₁ ⊗[𝕜] Y₀)) where
  toLinearMap := ⟨⟨fun f ↦ f.rTensor Y₀, rTensor_add Y₀⟩, rTensor_smul Y₀⟩
  norm_map' := norm_rTensor

@[simp]
theorem rTensorₗᵢ_apply [Nontrivial Y₀] (f : X₀ →L[𝕜] X₁) :
    rTensorₗᵢ 𝕜 X₀ X₁ Y₀ f = f.rTensor Y₀ := (rfl)

variable (𝕜 X₀ Y₀ Y₁) in
/-- Tensoring on the left with the identity of a nontrivial space, as a linear isometry. -/
noncomputable def lTensorₗᵢ [Nontrivial X₀] :
    (Y₀ →L[𝕜] Y₁) →ₗᵢ[𝕜] ((X₀ ⊗[𝕜] Y₀) →L[𝕜] (X₀ ⊗[𝕜] Y₁)) where
  toLinearMap := ⟨⟨fun g ↦ g.lTensor X₀, lTensor_add X₀⟩, lTensor_smul X₀⟩
  norm_map' := norm_lTensor

@[simp]
theorem lTensorₗᵢ_apply [Nontrivial X₀] (g : Y₀ →L[𝕜] Y₁) :
    lTensorₗᵢ 𝕜 X₀ Y₀ Y₁ g = g.lTensor X₀ := (rfl)

/-- Tensoring on the right with the identity of a nontrivial inner product space is injective. -/
@[simp]
theorem rTensor_inj [Nontrivial Y₀] {f g : X₀ →L[𝕜] X₁} :
    f.rTensor Y₀ = g.rTensor Y₀ ↔ f = g :=
  (rTensorₗᵢ 𝕜 X₀ X₁ Y₀).injective.eq_iff

/-- Tensoring on the left with the identity of a nontrivial inner product space is injective. -/
@[simp]
theorem lTensor_inj [Nontrivial X₀] {f g : Y₀ →L[𝕜] Y₁} :
    f.lTensor X₀ = g.lTensor X₀ ↔ f = g :=
  (lTensorₗᵢ 𝕜 X₀ Y₀ Y₁).injective.eq_iff

/-- Tensoring on the right with a subsingleton space produces the zero operator. -/
@[simp]
theorem rTensor_of_subsingleton [Subsingleton Y₀] (f : X₀ →L[𝕜] X₁) : f.rTensor Y₀ = 0 :=
  Subsingleton.elim _ _

/-- Tensoring on the left with a subsingleton space produces the zero operator. -/
@[simp]
theorem lTensor_of_subsingleton [Subsingleton X₀] (g : Y₀ →L[𝕜] Y₁) : g.lTensor X₀ = 0 :=
  Subsingleton.elim _ _

variable (Y₀) in
/-- If `f` has dense range then so does `f ⊗ 1`. -/
theorem denseRange_rTensor {f : X₀ →L[𝕜] X₁} (hf : DenseRange f) :
    DenseRange (f.rTensor Y₀) := by
  rw [rTensor_eq_mapL]
  exact TensorProduct.denseRange_mapL hf denseRange_id

variable (X₀) in
/-- If `g` has dense range then so does `1 ⊗ g`. -/
theorem denseRange_lTensor {g : Y₀ →L[𝕜] Y₁} (hg : DenseRange g) :
    DenseRange (g.lTensor X₀) := by
  rw [lTensor_eq_mapL]
  exact TensorProduct.denseRange_mapL denseRange_id hg

section Adjoint

open scoped InnerProductSpace

/-- `f† ⊗ 1` is a formal adjoint of `f ⊗ 1`, even when the tensor products are not complete. -/
theorem rTensor_adjoint_inner_left [CompleteSpace X₀] [CompleteSpace X₁] (f : X₀ →L[𝕜] X₁)
    (x : X₁ ⊗[𝕜] Y₀) (y : X₀ ⊗[𝕜] Y₀) :
    ⟪f.adjoint.rTensor Y₀ x, y⟫_𝕜 = ⟪x, f.rTensor Y₀ y⟫_𝕜 := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ => simp only [map_add, inner_add_right, h₁, h₂]
    | tmul c d => simp [adjoint_inner_left]

/-- `f† ⊗ 1` is a formal adjoint of `f ⊗ 1`, even when the tensor products are not complete. -/
theorem rTensor_adjoint_inner_right [CompleteSpace X₀] [CompleteSpace X₁] (f : X₀ →L[𝕜] X₁)
    (x : X₀ ⊗[𝕜] Y₀) (y : X₁ ⊗[𝕜] Y₀) :
    ⟪x, f.adjoint.rTensor Y₀ y⟫_𝕜 = ⟪f.rTensor Y₀ x, y⟫_𝕜 := by
  rw [← inner_conj_symm, rTensor_adjoint_inner_left, inner_conj_symm]

/-- `1 ⊗ g†` is a formal adjoint of `1 ⊗ g`, even when the tensor products are not complete. -/
theorem lTensor_adjoint_inner_left [CompleteSpace Y₀] [CompleteSpace Y₁] (g : Y₀ →L[𝕜] Y₁)
    (x : X₀ ⊗[𝕜] Y₁) (y : X₀ ⊗[𝕜] Y₀) :
    ⟪g.adjoint.lTensor X₀ x, y⟫_𝕜 = ⟪x, g.lTensor X₀ y⟫_𝕜 := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ => simp only [map_add, inner_add_right, h₁, h₂]
    | tmul c d => simp [adjoint_inner_left]

/-- `1 ⊗ g†` is a formal adjoint of `1 ⊗ g`, even when the tensor products are not complete. -/
theorem lTensor_adjoint_inner_right [CompleteSpace Y₀] [CompleteSpace Y₁] (g : Y₀ →L[𝕜] Y₁)
    (x : X₀ ⊗[𝕜] Y₀) (y : X₀ ⊗[𝕜] Y₁) :
    ⟪x, g.adjoint.lTensor X₀ y⟫_𝕜 = ⟪g.lTensor X₀ x, y⟫_𝕜 := by
  rw [← inner_conj_symm, lTensor_adjoint_inner_left, inner_conj_symm]

/-- The positive tensor sum `A†A ⊗ 1 + 1 ⊗ B†B` vanishes exactly on the common kernel of `A ⊗ 1`
and `1 ⊗ B`. The tensor products need not be complete. -/
theorem rTensor_adjoint_comp_self_apply_add_lTensor_adjoint_comp_self_apply_eq_zero_iff
    [CompleteSpace X₀] [CompleteSpace X₁] [CompleteSpace Y₀] [CompleteSpace Y₁]
    (A : X₀ →L[𝕜] X₁) (B : Y₀ →L[𝕜] Y₁) (x : X₀ ⊗[𝕜] Y₀) :
    (A.adjoint ∘L A).rTensor Y₀ x + (B.adjoint ∘L B).lTensor X₀ x = 0 ↔
      A.rTensor Y₀ x = 0 ∧ B.lTensor X₀ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [rTensor_comp, lTensor_comp, h.1, h.2]⟩
  -- Pairing with `x` gives `‖(A ⊗ 1) x‖ ^ 2 + ‖(1 ⊗ B) x‖ ^ 2 = 0`.
  have hx := congrArg (fun y ↦ RCLike.re ⟪y, x⟫_𝕜) h
  simp only [inner_add_left, map_add, rTensor_comp, lTensor_comp, comp_apply,
    rTensor_adjoint_inner_left, lTensor_adjoint_inner_left, inner_self_eq_norm_sq,
    inner_zero_left, map_zero] at hx
  obtain ⟨hA, hB⟩ := (add_eq_zero_iff_of_nonneg (by positivity) (by positivity)).mp hx
  exact ⟨by simpa using hA, by simpa using hB⟩

end Adjoint

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
