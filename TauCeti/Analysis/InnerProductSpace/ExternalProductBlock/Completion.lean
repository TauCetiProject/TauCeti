/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.Fredholm.Adjoint
public import TauCeti.Analysis.InnerProductSpace.ExternalProductBlock.Basic
public import TauCeti.Analysis.InnerProductSpace.TensorProduct.Kernel
import TauCeti.Analysis.Normed.Lp.ProdLp

/-!
# The external product block on completed tensor products and its index

Let `A : V₀ →L[𝕜] V₁` and `B : W₀ →L[𝕜] W₁` be operators between Hilbert spaces, and write
`V ⊗̂ W = UniformSpace.Completion (V ⊗[𝕜] W)` for the completed Hilbert tensor product. The
*external product block* of `A` and `B` is the operator

`D = [[A ⊗ 1, -(1 ⊗ B†)], [1 ⊗ B, A† ⊗ 1]] : (V₀ ⊗̂ W₀) ⊕ (V₁ ⊗̂ W₁) → (V₁ ⊗̂ W₀) ⊕ (V₀ ⊗̂ W₁)`

on the Hilbert sums (`ContinuousLinearMap.externalProductBlockCompletion`), built from the
amplifications `A ⊗ 1` and `1 ⊗ B` of `ContinuousLinearMap.rTensorCompletion` and
`ContinuousLinearMap.lTensorCompletion`. It is the even-to-odd part of the graded tensor product
`D_A ⊗ 1 + Γ ⊗ D_B` of `D_A = [[0, A†], [A, 0]]` and `D_B = [[0, B†], [B, 0]]`, and the completed
counterpart of `ContinuousLinearMap.externalProductBlock`, which uses the algebraic tensor product.
Atiyah and Singer use it to define the product of two elliptic operators.

The main result is that **the index is multiplicative**: if `A` and `B` are Fredholm, then so is
`D` (`ContinuousLinearMap.IsFredholm.externalProductBlockCompletion`), and

`index D = index A · index B`

(`ContinuousLinearMap.index_externalProductBlockCompletion`). More precisely, writing
`coker A ≅ ker A†`,

* `ker D ≅ (ker A ⊗ ker B) × (ker A† ⊗ ker B†)`
  (`ContinuousLinearMap.kerExternalProductBlockCompletionEquiv`), and
* `ker D† ≅ (ker A† ⊗ ker B) × (ker A ⊗ ker B†)`
  (`ContinuousLinearMap.kerAdjointExternalProductBlockCompletionEquiv`), where `ker D† ≅ coker D`
  because `D` has closed range when `A` and `B` do
  (`ContinuousLinearMap.isClosed_range_externalProductBlockCompletion`).

The cross terms of `D† D` cancel because the amplifications on the two factors commute, so `D† D`
is block diagonal with blocks `A†A ⊗ 1 + 1 ⊗ B†B` and `AA† ⊗ 1 + 1 ⊗ BB†`. In norms,

`‖D w‖² = ‖(A ⊗ 1) u‖² + ‖(1 ⊗ B) u‖² + ‖(A† ⊗ 1) v‖² + ‖(1 ⊗ B†) v‖²` for `w = (u, v)`

(`ContinuousLinearMap.norm_externalProductBlockCompletion_apply_sq`). Hence `D w = 0` exactly
when `u` lies in the common kernel of `A ⊗ 1` and `1 ⊗ B`, which is `ker A ⊗ ker B` for
finite-dimensional kernels (`ContinuousLinearMap.ker_rTensorCompletion_inf_ker_lTensorCompletion`),
and `v` in that of `A† ⊗ 1` and `1 ⊗ B†`. The adjoint of `D` is the block of `A†` and `-B`
(`ContinuousLinearMap.adjoint_externalProductBlockCompletion`), which gives `ker D†`. Closedness of
the range of `D` comes from the same identity: when `A` and `B` have closed range, each component
of `w` lies within `C ‖D w‖` of the corresponding common kernel
(`ContinuousLinearMap.exists_norm_sub_mapLCompletion_starProjection_apply_le`).

## Main declarations

* `ContinuousLinearMap.externalProductBlockCompletion`: the block operator `D`.
* `ContinuousLinearMap.externalProductBlockCompletion_apply_coe`: on the algebraic tensor products,
  `D` is `ContinuousLinearMap.externalProductBlock`.
* `ContinuousLinearMap.norm_externalProductBlockCompletion_apply_sq`: the norm identity above.
* `norm_add_norm_add_norm_add_norm_le_two_mul_norm_externalProductBlockCompletion_apply`, in the
  `ContinuousLinearMap` namespace: the four amplified norms add up to at most `2 ‖D w‖`.
* `ContinuousLinearMap.externalProductBlockCompletion_apply_eq_zero_iff`: the kernel of `D`.
* `ContinuousLinearMap.adjoint_externalProductBlockCompletion`: `D† = D(A†, -B)`.
* `ContinuousLinearMap.kerExternalProductBlockCompletionEquiv`,
  `ContinuousLinearMap.kerAdjointExternalProductBlockCompletionEquiv`: the kernels of `D` and `D†`
  for finite-dimensional kernels of `A`, `A†`, `B` and `B†`, with their dimensions
  `ContinuousLinearMap.finrank_ker_externalProductBlockCompletion` and
  `ContinuousLinearMap.finrank_ker_adjoint_externalProductBlockCompletion`.
* `ContinuousLinearMap.isClosed_range_externalProductBlockCompletion`: `D` has closed range when
  `A` and `B` do.
* `ContinuousLinearMap.IsFredholm.externalProductBlockCompletion`: `D` is Fredholm when `A` and
  `B` are.
* `ContinuousLinearMap.index_externalProductBlockCompletion`: `index D = index A · index B`.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §2, p. 490 (the external product of symbol complexes) and §9, pp. 526–530 (the product of two
  elliptic operators and the multiplicativity of the index).
-/

public section

noncomputable section

open UniformSpace TensorProduct
open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 V₀ V₁ W₀ W₁ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V₀] [InnerProductSpace 𝕜 V₀] [CompleteSpace V₀]
  [NormedAddCommGroup V₁] [InnerProductSpace 𝕜 V₁] [CompleteSpace V₁]
  [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀] [CompleteSpace W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [CompleteSpace W₁]

/-- The external product block of `A : V₀ →L[𝕜] V₁` and `B : W₀ →L[𝕜] W₁` on the completed
tensor products, the operator

`[[A ⊗ 1, -(1 ⊗ B†)], [1 ⊗ B, A† ⊗ 1]] : (V₀ ⊗̂ W₀) ⊕ (V₁ ⊗̂ W₁) → (V₁ ⊗̂ W₀) ⊕ (V₀ ⊗̂ W₁)`

on the Hilbert sums. It is the even-to-odd part of the graded tensor product
`D_A ⊗ 1 + Γ ⊗ D_B` of `D_A = [[0, A†], [A, 0]]` and `D_B = [[0, B†], [B, 0]]`. -/
def externalProductBlockCompletion (A : V₀ →L[𝕜] V₁) (B : W₀ →L[𝕜] W₁) :
    WithLp 2 (Completion (V₀ ⊗[𝕜] W₀) × Completion (V₁ ⊗[𝕜] W₁)) →L[𝕜]
      WithLp 2 (Completion (V₁ ⊗[𝕜] W₀) × Completion (V₀ ⊗[𝕜] W₁)) :=
  (WithLp.prodContinuousLinearEquiv 2 𝕜 _ _).symm.toContinuousLinearMap ∘L
    ((A.rTensorCompletion W₀ ∘L fst 𝕜 _ _ - B.adjoint.lTensorCompletion V₁ ∘L snd 𝕜 _ _).prod
      (B.lTensorCompletion V₀ ∘L fst 𝕜 _ _ + A.adjoint.rTensorCompletion W₁ ∘L snd 𝕜 _ _)) ∘L
    (WithLp.prodContinuousLinearEquiv 2 𝕜 _ _).toContinuousLinearMap

theorem externalProductBlockCompletion_apply (A : V₀ →L[𝕜] V₁) (B : W₀ →L[𝕜] W₁)
    (w : WithLp 2 (Completion (V₀ ⊗[𝕜] W₀) × Completion (V₁ ⊗[𝕜] W₁))) :
    externalProductBlockCompletion A B w = WithLp.toLp 2
      (A.rTensorCompletion W₀ w.fst - B.adjoint.lTensorCompletion V₁ w.snd,
        B.lTensorCompletion V₀ w.fst + A.adjoint.rTensorCompletion W₁ w.snd) :=
  (rfl)

@[simp]
theorem fst_externalProductBlockCompletion (A : V₀ →L[𝕜] V₁) (B : W₀ →L[𝕜] W₁)
    (w : WithLp 2 (Completion (V₀ ⊗[𝕜] W₀) × Completion (V₁ ⊗[𝕜] W₁))) :
    (externalProductBlockCompletion A B w).fst =
      A.rTensorCompletion W₀ w.fst - B.adjoint.lTensorCompletion V₁ w.snd :=
  (rfl)

@[simp]
theorem snd_externalProductBlockCompletion (A : V₀ →L[𝕜] V₁) (B : W₀ →L[𝕜] W₁)
    (w : WithLp 2 (Completion (V₀ ⊗[𝕜] W₀) × Completion (V₁ ⊗[𝕜] W₁))) :
    (externalProductBlockCompletion A B w).snd =
      B.lTensorCompletion V₀ w.fst + A.adjoint.rTensorCompletion W₁ w.snd :=
  (rfl)

/-- On the algebraic tensor products, the external product block on the completed tensor products
is `ContinuousLinearMap.externalProductBlock`. -/
@[simp]
theorem externalProductBlockCompletion_apply_coe (A : V₀ →L[𝕜] V₁) (B : W₀ →L[𝕜] W₁)
    (u : V₀ ⊗[𝕜] W₀) (v : V₁ ⊗[𝕜] W₁) :
    externalProductBlockCompletion A B
        (WithLp.toLp 2 ((u : Completion (V₀ ⊗[𝕜] W₀)), (v : Completion (V₁ ⊗[𝕜] W₁)))) =
      WithLp.toLp 2
        (((externalProductBlock A B (WithLp.toLp 2 (u, v))).fst : Completion (V₁ ⊗[𝕜] W₀)),
          ((externalProductBlock A B (WithLp.toLp 2 (u, v))).snd : Completion (V₀ ⊗[𝕜] W₁))) := by
  simp [externalProductBlockCompletion_apply, Completion.coe_sub, Completion.coe_add]

/-- **The cross terms cancel.** The norm of `D (u, v)` is computed from the four amplified
operators: `‖D (u, v)‖² = ‖(A ⊗ 1) u‖² + ‖(1 ⊗ B) u‖² + ‖(A† ⊗ 1) v‖² + ‖(1 ⊗ B†) v‖²`. -/
theorem norm_externalProductBlockCompletion_apply_sq (A : V₀ →L[𝕜] V₁) (B : W₀ →L[𝕜] W₁)
    (w : WithLp 2 (Completion (V₀ ⊗[𝕜] W₀) × Completion (V₁ ⊗[𝕜] W₁))) :
    ‖externalProductBlockCompletion A B w‖ ^ 2 =
      ‖A.rTensorCompletion W₀ w.fst‖ ^ 2 + ‖B.lTensorCompletion V₀ w.fst‖ ^ 2 +
        ‖A.adjoint.rTensorCompletion W₁ w.snd‖ ^ 2 +
          ‖B.adjoint.lTensorCompletion V₁ w.snd‖ ^ 2 := by
  -- Both cross terms equal `⟪(A ⊗ B) u, v⟫`, since `A ⊗ 1` and `1 ⊗ B` commute.
  have h₁ : ⟪A.rTensorCompletion W₀ w.fst, B.adjoint.lTensorCompletion V₁ w.snd⟫_𝕜 =
      ⟪mapLCompletion A B w.fst, w.snd⟫_𝕜 := by
    rw [← adjoint_lTensorCompletion, adjoint_inner_right, ← comp_apply,
      lTensorCompletion_comp_rTensorCompletion]
  have h₂ : ⟪B.lTensorCompletion V₀ w.fst, A.adjoint.rTensorCompletion W₁ w.snd⟫_𝕜 =
      ⟪mapLCompletion A B w.fst, w.snd⟫_𝕜 := by
    rw [← adjoint_rTensorCompletion, adjoint_inner_right, ← comp_apply,
      rTensorCompletion_comp_lTensorCompletion]
  rw [WithLp.prod_norm_sq_eq_of_L2, fst_externalProductBlockCompletion,
    snd_externalProductBlockCompletion, norm_sub_sq (𝕜 := 𝕜), norm_add_sq (𝕜 := 𝕜), h₁, h₂]
  ring

/-- **The kernel of the external product block.** `D (u, v) = 0` exactly when `A ⊗ 1` and `1 ⊗ B`
kill `u` and `A† ⊗ 1` and `1 ⊗ B†` kill `v`. -/
theorem externalProductBlockCompletion_apply_eq_zero_iff (A : V₀ →L[𝕜] V₁) (B : W₀ →L[𝕜] W₁)
    (w : WithLp 2 (Completion (V₀ ⊗[𝕜] W₀) × Completion (V₁ ⊗[𝕜] W₁))) :
    externalProductBlockCompletion A B w = 0 ↔
      (A.rTensorCompletion W₀ w.fst = 0 ∧ B.lTensorCompletion V₀ w.fst = 0) ∧
        A.adjoint.rTensorCompletion W₁ w.snd = 0 ∧ B.adjoint.lTensorCompletion V₁ w.snd = 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨⟨h₁, h₂⟩, h₃, h₄⟩ ↦ ?_⟩
  · -- A sum of four squares vanishes only if each square does.
    have hw := norm_externalProductBlockCompletion_apply_sq A B w
    rw [h, norm_zero] at hw
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> rw [← norm_eq_zero] <;>
      refine (pow_eq_zero_iff two_ne_zero).1 ?_ <;>
      nlinarith [sq_nonneg ‖A.rTensorCompletion W₀ w.fst‖,
        sq_nonneg ‖B.lTensorCompletion V₀ w.fst‖,
        sq_nonneg ‖A.adjoint.rTensorCompletion W₁ w.snd‖,
        sq_nonneg ‖B.adjoint.lTensorCompletion V₁ w.snd‖]
  · exact WithLp.ofLp_injective 2 <| Prod.ext (by simp [h₁, h₄]) (by simp [h₂, h₃])

/-- The adjoint of the external product block is the external product block of `A†` and `-B`,
that is `[[A† ⊗ 1, 1 ⊗ B†], [-(1 ⊗ B), A ⊗ 1]]`. -/
@[simp]
theorem adjoint_externalProductBlockCompletion (A : V₀ →L[𝕜] V₁) (B : W₀ →L[𝕜] W₁) :
    (externalProductBlockCompletion A B).adjoint =
      externalProductBlockCompletion A.adjoint (-B) := by
  refine (eq_adjoint_iff _ _ |>.2 fun x y ↦ ?_).symm
  simp only [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
    fst_externalProductBlockCompletion, snd_externalProductBlockCompletion, map_neg,
    adjoint_adjoint, lTensorCompletion_neg, neg_apply, inner_add_left, inner_sub_left,
    inner_neg_left, inner_add_right, inner_sub_right, ← adjoint_rTensorCompletion,
    ← adjoint_lTensorCompletion, adjoint_inner_left, adjoint_inner_right]
  ring

/-- **The kernel of the adjoint of the external product block.** `D† (x, y) = 0` exactly when
`A† ⊗ 1` and `1 ⊗ B` kill `x` and `A ⊗ 1` and `1 ⊗ B†` kill `y`. -/
theorem adjoint_externalProductBlockCompletion_apply_eq_zero_iff (A : V₀ →L[𝕜] V₁)
    (B : W₀ →L[𝕜] W₁) (w : WithLp 2 (Completion (V₁ ⊗[𝕜] W₀) × Completion (V₀ ⊗[𝕜] W₁))) :
    (externalProductBlockCompletion A B).adjoint w = 0 ↔
      (A.adjoint.rTensorCompletion W₀ w.fst = 0 ∧ B.lTensorCompletion V₁ w.fst = 0) ∧
        A.rTensorCompletion W₁ w.snd = 0 ∧ B.adjoint.lTensorCompletion V₀ w.snd = 0 := by
  rw [adjoint_externalProductBlockCompletion, externalProductBlockCompletion_apply_eq_zero_iff]
  simp

section Kernel

variable (A : V₀ →L[𝕜] V₁) (B : W₀ →L[𝕜] W₁)
  [FiniteDimensional 𝕜 A.ker] [FiniteDimensional 𝕜 B.ker] [FiniteDimensional 𝕜 A.adjoint.ker]
  [FiniteDimensional 𝕜 B.adjoint.ker]

/-- For finite-dimensional kernels, the kernel of the external product block is
`(ker A ⊗ ker B) ⊕ (ker A† ⊗ ker B†)`, embedded isometrically in the completed tensor products. -/
theorem externalProductBlockCompletion_apply_eq_zero_iff_mem_range
    (w : WithLp 2 (Completion (V₀ ⊗[𝕜] W₀) × Completion (V₁ ⊗[𝕜] W₁))) :
    externalProductBlockCompletion A B w = 0 ↔
      w.fst ∈ LinearMap.range
          (Completion.toComplₗᵢ.comp (mapInclIsometry A.ker B.ker)).toLinearMap ∧
        w.snd ∈ LinearMap.range
          (Completion.toComplₗᵢ.comp
            (mapInclIsometry A.adjoint.ker B.adjoint.ker)).toLinearMap := by
  rw [externalProductBlockCompletion_apply_eq_zero_iff,
    ← ker_rTensorCompletion_inf_ker_lTensorCompletion A B,
    ← ker_rTensorCompletion_inf_ker_lTensorCompletion A.adjoint B.adjoint]
  simp [Submodule.mem_inf]

/-- For finite-dimensional kernels, the kernel of the adjoint of the external product block is
`(ker A† ⊗ ker B) ⊕ (ker A ⊗ ker B†)`, embedded isometrically in the completed tensor products. -/
theorem adjoint_externalProductBlockCompletion_apply_eq_zero_iff_mem_range
    (w : WithLp 2 (Completion (V₁ ⊗[𝕜] W₀) × Completion (V₀ ⊗[𝕜] W₁))) :
    (externalProductBlockCompletion A B).adjoint w = 0 ↔
      w.fst ∈ LinearMap.range
          (Completion.toComplₗᵢ.comp (mapInclIsometry A.adjoint.ker B.ker)).toLinearMap ∧
        w.snd ∈ LinearMap.range
          (Completion.toComplₗᵢ.comp (mapInclIsometry A.ker B.adjoint.ker)).toLinearMap := by
  rw [adjoint_externalProductBlockCompletion_apply_eq_zero_iff,
    ← ker_rTensorCompletion_inf_ker_lTensorCompletion A.adjoint B,
    ← ker_rTensorCompletion_inf_ker_lTensorCompletion A B.adjoint]
  simp [Submodule.mem_inf]

/-- The kernel of the external product block, identified with
`(ker A ⊗ ker B) × (ker A† ⊗ ker B†)` through the inclusions of the kernels
(`ContinuousLinearMap.coe_kerExternalProductBlockCompletionEquiv_symm_apply`). -/
def kerExternalProductBlockCompletionEquiv :
    (externalProductBlockCompletion A B).ker ≃ₗ[𝕜]
      (A.ker ⊗[𝕜] B.ker) × (A.adjoint.ker ⊗[𝕜] B.adjoint.ker) :=
  kerEquivProdOfInjective _
    (Completion.toComplₗᵢ.comp (mapInclIsometry A.ker B.ker)).isometry.injective
    (Completion.toComplₗᵢ.comp (mapInclIsometry A.adjoint.ker B.adjoint.ker)).isometry.injective
    (externalProductBlockCompletion_apply_eq_zero_iff_mem_range A B)

/-- `kerExternalProductBlockCompletionEquiv` sends a pair of tensors of kernel vectors to the pair
of the corresponding tensors in the source of the external product block. -/
@[simp]
theorem coe_kerExternalProductBlockCompletionEquiv_symm_apply
    (p : (A.ker ⊗[𝕜] B.ker) × (A.adjoint.ker ⊗[𝕜] B.adjoint.ker)) :
    ((kerExternalProductBlockCompletionEquiv A B).symm p :
        WithLp 2 (Completion (V₀ ⊗[𝕜] W₀) × Completion (V₁ ⊗[𝕜] W₁))) =
      WithLp.toLp 2
        (((mapIncl A.ker B.ker p.1 : V₀ ⊗[𝕜] W₀) : Completion (V₀ ⊗[𝕜] W₀)),
          ((mapIncl A.adjoint.ker B.adjoint.ker p.2 : V₁ ⊗[𝕜] W₁) :
            Completion (V₁ ⊗[𝕜] W₁))) := by
  simp [kerExternalProductBlockCompletionEquiv]

/-- `kerExternalProductBlockCompletionEquiv` sends a kernel vector to the tensor of kernel
vectors whose inclusion is its first component. -/
@[simp]
theorem coe_mapIncl_kerExternalProductBlockCompletionEquiv_apply_fst
    (w : (externalProductBlockCompletion A B).ker) :
    ((mapIncl A.ker B.ker (kerExternalProductBlockCompletionEquiv A B w).1 :
        V₀ ⊗[𝕜] W₀) : Completion (V₀ ⊗[𝕜] W₀)) =
      (w : WithLp 2 (Completion (V₀ ⊗[𝕜] W₀) × Completion (V₁ ⊗[𝕜] W₁))).fst := by
  simpa [kerExternalProductBlockCompletionEquiv] using
    apply_kerEquivProdOfInjective_apply_fst _ _ _
      (externalProductBlockCompletion_apply_eq_zero_iff_mem_range A B) w

/-- `kerExternalProductBlockCompletionEquiv` sends a kernel vector to the tensor of kernel
vectors whose inclusion is its second component. -/
@[simp]
theorem coe_mapIncl_kerExternalProductBlockCompletionEquiv_apply_snd
    (w : (externalProductBlockCompletion A B).ker) :
    ((mapIncl A.adjoint.ker B.adjoint.ker (kerExternalProductBlockCompletionEquiv A B w).2 :
        V₁ ⊗[𝕜] W₁) : Completion (V₁ ⊗[𝕜] W₁)) =
      (w : WithLp 2 (Completion (V₀ ⊗[𝕜] W₀) × Completion (V₁ ⊗[𝕜] W₁))).snd := by
  simpa [kerExternalProductBlockCompletionEquiv] using
    apply_kerEquivProdOfInjective_apply_snd _ _ _
      (externalProductBlockCompletion_apply_eq_zero_iff_mem_range A B) w

/-- The kernel of the adjoint of the external product block, identified with
`(ker A† ⊗ ker B) × (ker A ⊗ ker B†)` through the inclusions of the kernels
(`ContinuousLinearMap.coe_kerAdjointExternalProductBlockCompletionEquiv_symm_apply`). When `D` has
closed range, for instance when `A` and `B` are Fredholm, this is the cokernel of `D`
(`ContinuousLinearMap.cokerEquivKerAdjoint`). -/
def kerAdjointExternalProductBlockCompletionEquiv :
    (externalProductBlockCompletion A B).adjoint.ker ≃ₗ[𝕜]
      (A.adjoint.ker ⊗[𝕜] B.ker) × (A.ker ⊗[𝕜] B.adjoint.ker) :=
  kerEquivProdOfInjective _
    (Completion.toComplₗᵢ.comp (mapInclIsometry A.adjoint.ker B.ker)).isometry.injective
    (Completion.toComplₗᵢ.comp (mapInclIsometry A.ker B.adjoint.ker)).isometry.injective
    (adjoint_externalProductBlockCompletion_apply_eq_zero_iff_mem_range A B)

/-- `kerAdjointExternalProductBlockCompletionEquiv` sends a pair of tensors of kernel vectors to
the pair of the corresponding tensors in the source of the adjoint of the external product
block. -/
@[simp]
theorem coe_kerAdjointExternalProductBlockCompletionEquiv_symm_apply
    (p : (A.adjoint.ker ⊗[𝕜] B.ker) × (A.ker ⊗[𝕜] B.adjoint.ker)) :
    ((kerAdjointExternalProductBlockCompletionEquiv A B).symm p :
        WithLp 2 (Completion (V₁ ⊗[𝕜] W₀) × Completion (V₀ ⊗[𝕜] W₁))) =
      WithLp.toLp 2
        (((mapIncl A.adjoint.ker B.ker p.1 : V₁ ⊗[𝕜] W₀) : Completion (V₁ ⊗[𝕜] W₀)),
          ((mapIncl A.ker B.adjoint.ker p.2 : V₀ ⊗[𝕜] W₁) : Completion (V₀ ⊗[𝕜] W₁))) := by
  simp [kerAdjointExternalProductBlockCompletionEquiv]

/-- `kerAdjointExternalProductBlockCompletionEquiv` sends a kernel vector to the tensor of kernel
vectors whose inclusion is its first component. -/
@[simp]
theorem coe_mapIncl_kerAdjointExternalProductBlockCompletionEquiv_apply_fst
    (w : (externalProductBlockCompletion A B).adjoint.ker) :
    ((mapIncl A.adjoint.ker B.ker (kerAdjointExternalProductBlockCompletionEquiv A B w).1 :
        V₁ ⊗[𝕜] W₀) : Completion (V₁ ⊗[𝕜] W₀)) =
      (w : WithLp 2 (Completion (V₁ ⊗[𝕜] W₀) × Completion (V₀ ⊗[𝕜] W₁))).fst := by
  simpa [kerAdjointExternalProductBlockCompletionEquiv] using
    apply_kerEquivProdOfInjective_apply_fst _ _ _
      (adjoint_externalProductBlockCompletion_apply_eq_zero_iff_mem_range A B) w

/-- `kerAdjointExternalProductBlockCompletionEquiv` sends a kernel vector to the tensor of kernel
vectors whose inclusion is its second component. -/
@[simp]
theorem coe_mapIncl_kerAdjointExternalProductBlockCompletionEquiv_apply_snd
    (w : (externalProductBlockCompletion A B).adjoint.ker) :
    ((mapIncl A.ker B.adjoint.ker (kerAdjointExternalProductBlockCompletionEquiv A B w).2 :
        V₀ ⊗[𝕜] W₁) : Completion (V₀ ⊗[𝕜] W₁)) =
      (w : WithLp 2 (Completion (V₁ ⊗[𝕜] W₀) × Completion (V₀ ⊗[𝕜] W₁))).snd := by
  simpa [kerAdjointExternalProductBlockCompletionEquiv] using
    apply_kerEquivProdOfInjective_apply_snd _ _ _
      (adjoint_externalProductBlockCompletion_apply_eq_zero_iff_mem_range A B) w

/-- The dimension of the kernel of the external product block is
`dim ker A · dim ker B + dim ker A† · dim ker B†`. -/
theorem finrank_ker_externalProductBlockCompletion :
    Module.finrank 𝕜 (externalProductBlockCompletion A B).ker =
      Module.finrank 𝕜 A.ker * Module.finrank 𝕜 B.ker +
        Module.finrank 𝕜 A.adjoint.ker * Module.finrank 𝕜 B.adjoint.ker := by
  rw [(kerExternalProductBlockCompletionEquiv A B).finrank_eq, Module.finrank_prod,
    Module.finrank_tensorProduct, Module.finrank_tensorProduct]

/-- The dimension of the kernel of the adjoint of the external product block is
`dim ker A† · dim ker B + dim ker A · dim ker B†`. -/
theorem finrank_ker_adjoint_externalProductBlockCompletion :
    Module.finrank 𝕜 (externalProductBlockCompletion A B).adjoint.ker =
      Module.finrank 𝕜 A.adjoint.ker * Module.finrank 𝕜 B.ker +
        Module.finrank 𝕜 A.ker * Module.finrank 𝕜 B.adjoint.ker := by
  rw [(kerAdjointExternalProductBlockCompletionEquiv A B).finrank_eq, Module.finrank_prod,
    Module.finrank_tensorProduct, Module.finrank_tensorProduct]

end Kernel

/-- The four amplified norms of the components of `w` add up to at most `2 ‖D w‖`. -/
theorem norm_add_norm_add_norm_add_norm_le_two_mul_norm_externalProductBlockCompletion_apply
    (A : V₀ →L[𝕜] V₁) (B : W₀ →L[𝕜] W₁)
    (w : WithLp 2 (Completion (V₀ ⊗[𝕜] W₀) × Completion (V₁ ⊗[𝕜] W₁))) :
    ‖A.rTensorCompletion W₀ w.fst‖ + ‖B.lTensorCompletion V₀ w.fst‖ +
        ‖A.adjoint.rTensorCompletion W₁ w.snd‖ + ‖B.adjoint.lTensorCompletion V₁ w.snd‖ ≤
      2 * ‖externalProductBlockCompletion A B w‖ := by
  have hd := norm_externalProductBlockCompletion_apply_sq A B w
  set a := ‖A.rTensorCompletion W₀ w.fst‖
  set b := ‖B.lTensorCompletion V₀ w.fst‖
  set c := ‖A.adjoint.rTensorCompletion W₁ w.snd‖
  set e := ‖B.adjoint.lTensorCompletion V₁ w.snd‖
  -- Cauchy–Schwarz for four terms: `(a + b + c + e)² ≤ 4 (a² + b² + c² + e²)`.
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - e), sq_nonneg (b - c),
    sq_nonneg (b - e), sq_nonneg (c - e)]

/-- If `A` and `B` have closed range, so does their external product block: every `w` lies within
`C ‖D w‖` of the kernel of `D`. -/
theorem isClosed_range_externalProductBlockCompletion {A : V₀ →L[𝕜] V₁} {B : W₀ →L[𝕜] W₁}
    (hA : IsClosed (A.range : Set V₁)) (hB : IsClosed (B.range : Set W₁)) :
    IsClosed ((externalProductBlockCompletion A B).range :
      Set (WithLp 2 (Completion (V₁ ⊗[𝕜] W₀) × Completion (V₀ ⊗[𝕜] W₁)))) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_sub_mapLCompletion_starProjection_apply_le A B hA hB
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_sub_mapLCompletion_starProjection_apply_le A.adjoint
    B.adjoint (isClosed_range_adjoint_of_isClosed_range A hA)
    (isClosed_range_adjoint_of_isClosed_range B hB)
  -- The candidate kernel vector projects each component onto the corresponding common kernel.
  refine (externalProductBlockCompletion A B).isClosed_range_of_forall_exists_mem_ker_norm_sub_le
    (C := 2 * (C₁ + C₂)) fun w ↦ ⟨WithLp.toLp 2
      (mapLCompletion A.ker.starProjection B.ker.starProjection w.fst,
        mapLCompletion A.adjoint.ker.starProjection B.adjoint.ker.starProjection w.snd), ?_, ?_⟩
  · rw [LinearMap.mem_ker, coe_coe, externalProductBlockCompletion_apply_eq_zero_iff]
    exact ⟨⟨rTensorCompletion_mapLCompletion_starProjection_apply_eq_zero A B _,
      lTensorCompletion_mapLCompletion_starProjection_apply_eq_zero A B _⟩,
      rTensorCompletion_mapLCompletion_starProjection_apply_eq_zero A.adjoint B.adjoint _,
      lTensorCompletion_mapLCompletion_starProjection_apply_eq_zero A.adjoint B.adjoint _⟩
  · have hsum :=
      norm_add_norm_add_norm_add_norm_le_two_mul_norm_externalProductBlockCompletion_apply A B w
    refine (WithLp.prod_norm_le_norm_fst_add_norm_snd _).trans ?_
    simp only [WithLp.sub_fst, WithLp.sub_snd, WithLp.toLp_fst, WithLp.toLp_snd]
    refine (add_le_add (h₁ w.fst) (h₂ w.snd)).trans ?_
    nlinarith [norm_nonneg (A.rTensorCompletion W₀ w.fst),
      norm_nonneg (B.lTensorCompletion V₀ w.fst),
      norm_nonneg (A.adjoint.rTensorCompletion W₁ w.snd),
      norm_nonneg (B.adjoint.lTensorCompletion V₁ w.snd)]

/-- **The external product block of two Fredholm operators is Fredholm.** -/
theorem IsFredholm.externalProductBlockCompletion {A : V₀ →L[𝕜] V₁} {B : W₀ →L[𝕜] W₁}
    (hA : A.IsFredholm) (hB : B.IsFredholm) : (externalProductBlockCompletion A B).IsFredholm := by
  have := hA.finite_ker
  have := hB.finite_ker
  have := hA.adjoint.finite_ker
  have := hB.adjoint.finite_ker
  have hclosed := isClosed_range_externalProductBlockCompletion hA.isClosed_range hB.isClosed_range
  exact .of_finite_ker_coker _
    (kerExternalProductBlockCompletionEquiv A B).symm.finiteDimensional
    ((cokerEquivKerAdjoint _ hclosed).toLinearEquiv.trans
      (kerAdjointExternalProductBlockCompletionEquiv A B)).symm.finiteDimensional

/-- **The index of the external product block is multiplicative**: for Fredholm `A` and `B`,
`index D = index A · index B`. -/
theorem index_externalProductBlockCompletion {A : V₀ →L[𝕜] V₁} {B : W₀ →L[𝕜] W₁}
    (hA : A.IsFredholm) (hB : B.IsFredholm) :
    (externalProductBlockCompletion A B).index = A.index * B.index := by
  have := hA.finite_ker
  have := hB.finite_ker
  have := hA.adjoint.finite_ker
  have := hB.adjoint.finite_ker
  have hclosed := isClosed_range_externalProductBlockCompletion hA.isClosed_range hB.isClosed_range
  rw [index_eq_finrank_sub, index_eq_finrank_sub, index_eq_finrank_sub,
    (cokerEquivKerAdjoint _ hclosed).toLinearEquiv.finrank_eq,
    (cokerEquivKerAdjoint _ hA.isClosed_range).toLinearEquiv.finrank_eq,
    (cokerEquivKerAdjoint _ hB.isClosed_range).toLinearEquiv.finrank_eq]
  rw [finrank_ker_externalProductBlockCompletion,
    finrank_ker_adjoint_externalProductBlockCompletion]
  push_cast
  ring

end ContinuousLinearMap
