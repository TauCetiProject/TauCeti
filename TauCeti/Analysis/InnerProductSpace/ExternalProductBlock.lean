/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.InnerProductSpace.OperatorIdentities
public import TauCeti.Analysis.InnerProductSpace.TensorProduct
import TauCeti.LinearAlgebra.TensorProduct.Intersection

/-!
# The external product block of two operators

Let `A : V₀ →L[𝕜] V₁` and `B : W₀ →L[𝕜] W₁` be operators between Hilbert spaces. Grade
`V₀ ⊕ V₁` and `W₀ ⊕ W₁` by `+` on the subscript `0` and `-` on the subscript `1`, and consider the
odd self-adjoint operators `D_A = [[0, A†], [A, 0]]` and `D_B = [[0, B†], [B, 0]]`. The graded
tensor product `D_A ⊗ 1 + Γ ⊗ D_B` is odd for the tensor grading, and its even-to-odd part is the
block operator

`[[A ⊗ 1, -(1 ⊗ B†)], [1 ⊗ B, A† ⊗ 1]] : (V₀ ⊗ W₀) ⊕ (V₁ ⊗ W₁) → (V₁ ⊗ W₀) ⊕ (V₀ ⊗ W₁)`,

`ContinuousLinearMap.externalProductBlock A B`, where `⊗` is the algebraic tensor product
`⊗[𝕜]` with Mathlib's inner product and both sums carry the Hilbert (`L²`) norm. Applied
pointwise to two principal symbols, this is the external product of symbols used for the index of
a product of elliptic operators.

When the four tensor products are complete, for example when the factors are finite-dimensional,
the adjoint is again such a block, `(externalProductBlock A B)† = externalProductBlock A† (-B)`.
The cross terms cancel in `externalProductBlock A† (-B) ∘ externalProductBlock A B`, because
`A ⊗ 1` and `1 ⊗ B` commute. So, under the same completeness assumption, the products with the
adjoint are block diagonal:

`(externalProductBlock A B)† ∘ externalProductBlock A B = (A†A ⊗ 1 + 1 ⊗ B†B) ⊕ (AA† ⊗ 1 + 1 ⊗ BB†)`

and similarly for the product in the other order. In particular, if `A†A = AA† = s` and
`B†B = BB† = t` are scalars, both products are the scalar `s + t`. For the principal symbols
`σ_P(ξ)` and `σ_Q(η)` of two operators normalized so that `σ_P* σ_P = σ_P σ_P* = ‖ξ‖²` and
likewise for `σ_Q`, the external product therefore satisfies `A* A = A A* = ‖ξ‖² + ‖η‖²`.

The kernel of the block is given by a Künneth formula, with no completeness assumption:

`ker (externalProductBlock A B) ≃ (ker A ⊗ ker B) × (ker A† ⊗ ker B†)`.

If `externalProductBlock A B (x, y) = 0`, then `(A ⊗ 1) x = (1 ⊗ B†) y` and
`(1 ⊗ B) x = -(A† ⊗ 1) y`, and pairing these with `(A ⊗ 1) x` and `(1 ⊗ B) x` gives
`‖(A ⊗ 1) x‖² + ‖(1 ⊗ B) x‖² = 0`, because `A ⊗ 1` and `1 ⊗ B` commute. So `x` lies in the common
kernel of `A ⊗ 1` and `1 ⊗ B`, which is `ker A ⊗ ker B` since every vector space is flat
(`LinearMap.ker_rTensor_inf_ker_lTensor`), and likewise for `y`. Since the adjoint of the block is
`externalProductBlock A† (-B)`, its kernel, the cokernel of the block when the range is closed, is
`(ker A† ⊗ ker B) × (ker A ⊗ ker B†)`. With `a, a', b, b'` the dimensions of `ker A`, `ker A†`,
`ker B` and `ker B†`, the two kernels have dimensions `a b + a' b'` and `a' b + a b'`, and so
the difference is `(a - a') (b - b')`: the index is multiplicative. These are the kernel and
cokernel identifications of the product of two elliptic operators in Atiyah–Singer §9, applied
here to the block on algebraic tensor products, for instance to the symbols.

## Main declarations

* `ContinuousLinearMap.externalProductBlock`: the block operator above.
* `ContinuousLinearMap.adjoint_externalProductBlock`: its adjoint is
  `externalProductBlock A† (-B)`.
* `ContinuousLinearMap.externalProductBlock_adjoint_neg_apply_externalProductBlock`: the block
  diagonal form of `externalProductBlock A† (-B) ∘ externalProductBlock A B`.
* `ContinuousLinearMap.adjoint_externalProductBlock_comp_self_of_eq_smul`,
  `ContinuousLinearMap.externalProductBlock_comp_adjoint_of_eq_smul` and
  `ContinuousLinearMap.norm_externalProductBlock_apply_sq_of_eq_smul`: the scalar case.
* `ContinuousLinearMap.externalProductBlock_eq_zero_iff`,
  `ContinuousLinearMap.adjoint_externalProductBlock_eq_zero_iff`: the kernels of the block and of
  its adjoint.
* `ContinuousLinearMap.kerExternalProductBlockEquiv`: the Künneth isomorphism
  `(ker A ⊗ ker B) × (ker A† ⊗ ker B†) ≃ ker (externalProductBlock A B)`.
* `ContinuousLinearMap.kerAdjointExternalProductBlockEquiv`: the Künneth isomorphism
  `(ker A† ⊗ ker B) × (ker A ⊗ ker B†) ≃ ker (externalProductBlock A B)†`.
* `ContinuousLinearMap.finrank_ker_externalProductBlock`,
  `ContinuousLinearMap.finrank_ker_adjoint_externalProductBlock` and
  `ContinuousLinearMap.finrank_ker_sub_finrank_ker_adjoint_externalProductBlock`: the dimensions
  of the two kernels and the multiplicativity of their difference.
* `ContinuousLinearMap.norm_externalProductBlock_le`: `‖externalProductBlock A B‖ ≤ 2 (‖A‖ + ‖B‖)`.
  Together with `ContinuousLinearMap.externalProductBlock_add` and
  `ContinuousLinearMap.externalProductBlock_ofReal_smul`, this makes the block a bounded real-linear
  function of the pair `(A, B)`. For complex Hilbert spaces it is therefore smooth over `ℝ`
  (`ContinuousLinearMap.contDiff_externalProductBlock`).

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §2, p. 490 (the external product of symbol complexes) and §9 (the product of two elliptic
  operators).
-/

public section

noncomputable section

open scoped TensorProduct InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 V₀ V₁ W₀ W₁ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V₀] [InnerProductSpace 𝕜 V₀] [CompleteSpace V₀]
  [NormedAddCommGroup V₁] [InnerProductSpace 𝕜 V₁] [CompleteSpace V₁]
  [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀] [CompleteSpace W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [CompleteSpace W₁]

/-- The external product block of `A : V₀ →L[𝕜] V₁` and `B : W₀ →L[𝕜] W₁`, the operator

`[[A ⊗ 1, -(1 ⊗ B†)], [1 ⊗ B, A† ⊗ 1]] : (V₀ ⊗ W₀) ⊕ (V₁ ⊗ W₁) → (V₁ ⊗ W₀) ⊕ (V₀ ⊗ W₁)`

on the Hilbert sums. It is the even-to-odd part of the graded tensor product
`D_A ⊗ 1 + Γ ⊗ D_B` of `D_A = [[0, A†], [A, 0]]` and `D_B = [[0, B†], [B, 0]]`. -/
def externalProductBlock (A : V₀ →L[𝕜] V₁) (B : W₀ →L[𝕜] W₁) :
    WithLp 2 ((V₀ ⊗[𝕜] W₀) × (V₁ ⊗[𝕜] W₁)) →L[𝕜] WithLp 2 ((V₁ ⊗[𝕜] W₀) × (V₀ ⊗[𝕜] W₁)) :=
  (WithLp.prodContinuousLinearEquiv 2 𝕜 _ _).symm.toContinuousLinearMap ∘L
    ((A.rTensor W₀ ∘L fst 𝕜 _ _ - B.adjoint.lTensor V₁ ∘L snd 𝕜 _ _).prod
      (B.lTensor V₀ ∘L fst 𝕜 _ _ + A.adjoint.rTensor W₁ ∘L snd 𝕜 _ _)) ∘L
    (WithLp.prodContinuousLinearEquiv 2 𝕜 _ _).toContinuousLinearMap

theorem externalProductBlock_apply (A : V₀ →L[𝕜] V₁) (B : W₀ →L[𝕜] W₁)
    (w : WithLp 2 ((V₀ ⊗[𝕜] W₀) × (V₁ ⊗[𝕜] W₁))) :
    externalProductBlock A B w = WithLp.toLp 2
      (A.rTensor W₀ w.fst - B.adjoint.lTensor V₁ w.snd,
        B.lTensor V₀ w.fst + A.adjoint.rTensor W₁ w.snd) :=
  (rfl)

@[simp]
theorem fst_externalProductBlock (A : V₀ →L[𝕜] V₁) (B : W₀ →L[𝕜] W₁)
    (w : WithLp 2 ((V₀ ⊗[𝕜] W₀) × (V₁ ⊗[𝕜] W₁))) :
    (externalProductBlock A B w).fst = A.rTensor W₀ w.fst - B.adjoint.lTensor V₁ w.snd :=
  (rfl)

@[simp]
theorem snd_externalProductBlock (A : V₀ →L[𝕜] V₁) (B : W₀ →L[𝕜] W₁)
    (w : WithLp 2 ((V₀ ⊗[𝕜] W₀) × (V₁ ⊗[𝕜] W₁))) :
    (externalProductBlock A B w).snd = B.lTensor V₀ w.fst + A.adjoint.rTensor W₁ w.snd :=
  (rfl)

@[simp]
theorem externalProductBlock_zero_zero :
    externalProductBlock (0 : V₀ →L[𝕜] V₁) (0 : W₀ →L[𝕜] W₁) = 0 := by
  ext w : 1
  exact WithLp.ofLp_injective 2 <| Prod.ext (by simp) (by simp)

/-- The external product block is additive in the pair `(A, B)`. -/
theorem externalProductBlock_add (A A' : V₀ →L[𝕜] V₁) (B B' : W₀ →L[𝕜] W₁) :
    externalProductBlock (A + A') (B + B') =
      externalProductBlock A B + externalProductBlock A' B' := by
  ext w : 1
  refine WithLp.ofLp_injective 2 <| Prod.ext ?_ ?_
  · simp only [WithLp.ofLp_fst, fst_externalProductBlock, map_add, rTensor_add, lTensor_add,
      add_apply, WithLp.add_fst]
    abel
  · simp only [WithLp.ofLp_snd, snd_externalProductBlock, map_add, rTensor_add, lTensor_add,
      add_apply, WithLp.add_snd]
    abel

/-- The external product block is homogeneous in the pair `(A, B)` for real scalars, written in
`𝕜`. It is not `𝕜`-homogeneous, since the adjoint is conjugate linear. -/
theorem externalProductBlock_ofReal_smul (r : ℝ) (A : V₀ →L[𝕜] V₁) (B : W₀ →L[𝕜] W₁) :
    externalProductBlock ((r : 𝕜) • A) ((r : 𝕜) • B) = (r : 𝕜) • externalProductBlock A B := by
  ext w : 1
  refine WithLp.ofLp_injective 2 <| Prod.ext ?_ ?_
  · simp [adjoint_ofReal_smul, smul_sub]
  · simp [adjoint_ofReal_smul, smul_add]

/-- The external product block is bounded by `2 (‖A‖ + ‖B‖)`. Together with
`externalProductBlock_add`, this makes it continuous in `(A, B)`. -/
theorem norm_externalProductBlock_le (A : V₀ →L[𝕜] V₁) (B : W₀ →L[𝕜] W₁) :
    ‖externalProductBlock A B‖ ≤ 2 * (‖A‖ + ‖B‖) := by
  refine opNorm_le_bound _ (by positivity) fun w ↦ ?_
  have h₁ := WithLp.norm_fst_le (x := w)
  have h₂ := WithLp.norm_snd_le (x := w)
  have hA₁ : ‖A.rTensor W₀ w.fst‖ ≤ ‖A‖ * ‖w‖ :=
    (le_opNorm_of_le _ h₁).trans (by gcongr; exact norm_rTensor_le _ _)
  have hA₂ : ‖A.adjoint.rTensor W₁ w.snd‖ ≤ ‖A‖ * ‖w‖ :=
    (le_opNorm_of_le _ h₂).trans
      (by gcongr; exact (norm_rTensor_le _ _).trans_eq (adjoint.norm_map A))
  have hB₁ : ‖B.lTensor V₀ w.fst‖ ≤ ‖B‖ * ‖w‖ :=
    (le_opNorm_of_le _ h₁).trans (by gcongr; exact norm_lTensor_le _ _)
  have hB₂ : ‖B.adjoint.lTensor V₁ w.snd‖ ≤ ‖B‖ * ‖w‖ :=
    (le_opNorm_of_le _ h₂).trans
      (by gcongr; exact (norm_lTensor_le _ _).trans_eq (adjoint.norm_map B))
  have hX : ‖(externalProductBlock A B w).fst‖ ≤ (‖A‖ + ‖B‖) * ‖w‖ := by
    rw [fst_externalProductBlock]
    linarith [norm_sub_le (A.rTensor W₀ w.fst) (B.adjoint.lTensor V₁ w.snd)]
  have hY : ‖(externalProductBlock A B w).snd‖ ≤ (‖A‖ + ‖B‖) * ‖w‖ := by
    rw [snd_externalProductBlock]
    linarith [norm_add_le (B.lTensor V₀ w.fst) (A.adjoint.rTensor W₁ w.snd)]
  have hsq := WithLp.prod_norm_sq_eq_of_L2 (externalProductBlock A B w)
  have hc : 0 ≤ (‖A‖ + ‖B‖) * ‖w‖ := by positivity
  nlinarith [norm_nonneg (externalProductBlock A B w),
    norm_nonneg (externalProductBlock A B w).fst, norm_nonneg (externalProductBlock A B w).snd]

/-- The cross terms cancel: `externalProductBlock A† (-B) ∘ externalProductBlock A B` is the
block diagonal operator `(A†A ⊗ 1 + 1 ⊗ B†B) ⊕ (AA† ⊗ 1 + 1 ⊗ BB†)`. -/
theorem externalProductBlock_adjoint_neg_apply_externalProductBlock (A : V₀ →L[𝕜] V₁)
    (B : W₀ →L[𝕜] W₁) (w : WithLp 2 ((V₀ ⊗[𝕜] W₀) × (V₁ ⊗[𝕜] W₁))) :
    externalProductBlock A.adjoint (-B) (externalProductBlock A B w) = WithLp.toLp 2
      ((A.adjoint ∘L A).rTensor W₀ w.fst + (B.adjoint ∘L B).lTensor V₀ w.fst,
        (A ∘L A.adjoint).rTensor W₁ w.snd + (B ∘L B.adjoint).lTensor V₁ w.snd) := by
  refine WithLp.ofLp_injective 2 <| Prod.ext ?_ ?_
  · simp only [WithLp.ofLp_fst, fst_externalProductBlock, snd_externalProductBlock, map_neg,
      map_sub, map_add, lTensor_neg, neg_apply, rTensor_comp, lTensor_comp, comp_apply,
      rTensor_lTensor_apply_comm A.adjoint B.adjoint]
    abel
  · simp only [WithLp.ofLp_snd, fst_externalProductBlock, snd_externalProductBlock, map_sub,
      map_add, lTensor_neg, neg_apply, adjoint_adjoint, rTensor_comp, lTensor_comp, comp_apply,
      rTensor_lTensor_apply_comm A B]
    abel

section Kernel

variable {X₀ X₁ Y₀ Y₁ : Type*}
  [NormedAddCommGroup X₀] [InnerProductSpace 𝕜 X₀] [NormedAddCommGroup X₁] [InnerProductSpace 𝕜 X₁]
  [NormedAddCommGroup Y₀] [InnerProductSpace 𝕜 Y₀] [NormedAddCommGroup Y₁] [InnerProductSpace 𝕜 Y₁]

/-- **The kernel of the external product block.** `externalProductBlock A B` kills `(x, y)` exactly
when `A ⊗ 1` and `1 ⊗ B` both kill `x` and `A† ⊗ 1` and `1 ⊗ B†` both kill `y`. The tensor
products need not be complete. -/
theorem externalProductBlock_eq_zero_iff {A : V₀ →L[𝕜] V₁} {B : W₀ →L[𝕜] W₁}
    {w : WithLp 2 ((V₀ ⊗[𝕜] W₀) × (V₁ ⊗[𝕜] W₁))} :
    externalProductBlock A B w = 0 ↔
      (A.rTensor W₀ w.fst = 0 ∧ B.lTensor V₀ w.fst = 0) ∧
        A.adjoint.rTensor W₁ w.snd = 0 ∧ B.adjoint.lTensor V₁ w.snd = 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨⟨h₁, h₂⟩, h₃, h₄⟩ ↦ WithLp.ofLp_injective 2 <| Prod.ext
    (by simp [h₁, h₄]) (by simp [h₂, h₃])⟩
  have h₁ : A.rTensor W₀ w.fst = B.adjoint.lTensor V₁ w.snd := by
    simpa [sub_eq_zero] using congrArg (fun z ↦ z.fst) h
  have h₂ : B.lTensor V₀ w.fst = -A.adjoint.rTensor W₁ w.snd := by
    simpa [add_eq_zero_iff_eq_neg] using congrArg (fun z ↦ z.snd) h
  -- Pairing `h₁` with `(A ⊗ 1) x` and `h₂` with `(1 ⊗ B) x` gives the same cross term
  -- `⟪(1 ⊗ B) (A ⊗ 1) x, y⟫` with opposite signs, since `A ⊗ 1` and `1 ⊗ B` commute.
  have hsum : ‖A.rTensor W₀ w.fst‖ ^ 2 + ‖B.lTensor V₀ w.fst‖ ^ 2 = 0 := by
    have e₁ : inner 𝕜 (A.rTensor W₀ w.fst) (A.rTensor W₀ w.fst) =
        inner 𝕜 (B.lTensor V₁ (A.rTensor W₀ w.fst)) w.snd :=
      (congrArg (inner 𝕜 _) h₁).trans (adjoint_lTensor_inner_right B _ _)
    have e₂ : inner 𝕜 (B.lTensor V₀ w.fst) (B.lTensor V₀ w.fst) =
        -inner 𝕜 (B.lTensor V₁ (A.rTensor W₀ w.fst)) w.snd := by
      rw [congrArg (inner 𝕜 _) h₂, inner_neg_right, adjoint_rTensor_inner_right,
        rTensor_lTensor_apply_comm]
    have : ((‖A.rTensor W₀ w.fst‖ ^ 2 + ‖B.lTensor V₀ w.fst‖ ^ 2 : ℝ) : 𝕜) = 0 := by
      rw [RCLike.ofReal_add, RCLike.ofReal_pow, RCLike.ofReal_pow, ← inner_self_eq_norm_sq_to_K,
        ← inner_self_eq_norm_sq_to_K, e₁, e₂, add_neg_cancel]
    exact_mod_cast this
  obtain ⟨hA, hB⟩ := (add_eq_zero_iff_of_nonneg (by positivity) (by positivity)).1 hsum
  rw [sq_eq_zero_iff, norm_eq_zero] at hA hB
  exact ⟨⟨hA, hB⟩, by rwa [hB, eq_comm, neg_eq_zero] at h₂, by rwa [hA, eq_comm] at h₁⟩

/-- The inclusion `(p ⊗ q) × (p' ⊗ q') → (X₀ ⊗ Y₀) × (X₁ ⊗ Y₁)` of tensor products of
subspaces. For the kernels of `A`, `B`, `A†` and `B†`, its range is the kernel of the external
product block, and for the kernels of `A†`, `B`, `A` and `B†` that of its adjoint. -/
private noncomputable def tensorInclusion (p : Submodule 𝕜 X₀) (q : Submodule 𝕜 Y₀)
    (p' : Submodule 𝕜 X₁) (q' : Submodule 𝕜 Y₁) :
    ((p ⊗[𝕜] q) × (p' ⊗[𝕜] q')) →ₗ[𝕜] WithLp 2 ((X₀ ⊗[𝕜] Y₀) × (X₁ ⊗[𝕜] Y₁)) :=
  (WithLp.linearEquiv 2 𝕜 ((X₀ ⊗[𝕜] Y₀) × (X₁ ⊗[𝕜] Y₁))).symm.toLinearMap ∘ₗ
    (TensorProduct.mapIncl p q).prodMap (TensorProduct.mapIncl p' q')

private theorem tensorInclusion_apply (p : Submodule 𝕜 X₀) (q : Submodule 𝕜 Y₀)
    (p' : Submodule 𝕜 X₁) (q' : Submodule 𝕜 Y₁)
    (st : (p ⊗[𝕜] q) × (p' ⊗[𝕜] q')) :
    tensorInclusion p q p' q' st =
      WithLp.toLp 2 (TensorProduct.mapIncl _ _ st.1, TensorProduct.mapIncl _ _ st.2) :=
  rfl

private theorem injective_tensorInclusion (p : Submodule 𝕜 X₀) (q : Submodule 𝕜 Y₀)
    (p' : Submodule 𝕜 X₁) (q' : Submodule 𝕜 Y₁) :
    Function.Injective (tensorInclusion p q p' q') := by
  intro st st' h
  rw [tensorInclusion_apply, tensorInclusion_apply] at h
  have h' := congrArg WithLp.ofLp h
  simp only [Prod.mk.injEq] at h'
  exact Prod.ext ((TensorProduct.mapInclIsometry _ _).injective h'.1)
    ((TensorProduct.mapInclIsometry _ _).injective h'.2)

private theorem mem_range_tensorInclusion (p : Submodule 𝕜 X₀) (q : Submodule 𝕜 Y₀)
    (p' : Submodule 𝕜 X₁) (q' : Submodule 𝕜 Y₁)
    (w : WithLp 2 ((X₀ ⊗[𝕜] Y₀) × (X₁ ⊗[𝕜] Y₁))) :
    w ∈ LinearMap.range (tensorInclusion p q p' q') ↔
      w.fst ∈ LinearMap.range (TensorProduct.mapIncl p q) ∧
        w.snd ∈ LinearMap.range (TensorProduct.mapIncl p' q') := by
  constructor
  · rintro ⟨st, rfl⟩
    simp [tensorInclusion_apply]
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    exact ⟨(s, t), WithLp.ofLp_injective 2 <| Prod.ext hs ht⟩

private theorem range_kerTensorInclusion (A : V₀ →L[𝕜] V₁) (B : W₀ →L[𝕜] W₁) :
    LinearMap.range (tensorInclusion (LinearMap.ker (A : V₀ →ₗ[𝕜] V₁))
        (LinearMap.ker (B : W₀ →ₗ[𝕜] W₁)) (LinearMap.ker (A.adjoint : V₁ →ₗ[𝕜] V₀))
        (LinearMap.ker (B.adjoint : W₁ →ₗ[𝕜] W₀))) =
      LinearMap.ker (externalProductBlock A B :
        WithLp 2 ((V₀ ⊗[𝕜] W₀) × (V₁ ⊗[𝕜] W₁)) →ₗ[𝕜] WithLp 2 ((V₁ ⊗[𝕜] W₀) × (V₀ ⊗[𝕜] W₁))) := by
  ext w
  -- Each component condition is membership in the common kernel of `f ⊗ 1` and `1 ⊗ g`.
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, externalProductBlock_eq_zero_iff,
    mem_range_tensorInclusion]
  simp only [rTensor_apply, lTensor_apply, ← LinearMap.mem_ker, ← Submodule.mem_inf,
    LinearMap.ker_rTensor_inf_ker_lTensor]

/-- **The Künneth isomorphism for the kernel of the external product block**:
`(ker A ⊗ ker B) × (ker A† ⊗ ker B†) ≃ ker (externalProductBlock A B)`, given by the inclusions of
the tensor products of the kernels. The tensor products need not be complete. -/
noncomputable def kerExternalProductBlockEquiv (A : V₀ →L[𝕜] V₁) (B : W₀ →L[𝕜] W₁) :
    ((LinearMap.ker (A : V₀ →ₗ[𝕜] V₁) ⊗[𝕜] LinearMap.ker (B : W₀ →ₗ[𝕜] W₁)) ×
        (LinearMap.ker (A.adjoint : V₁ →ₗ[𝕜] V₀) ⊗[𝕜]
          LinearMap.ker (B.adjoint : W₁ →ₗ[𝕜] W₀))) ≃ₗ[𝕜]
      LinearMap.ker (externalProductBlock A B :
        WithLp 2 ((V₀ ⊗[𝕜] W₀) × (V₁ ⊗[𝕜] W₁)) →ₗ[𝕜] WithLp 2 ((V₁ ⊗[𝕜] W₀) × (V₀ ⊗[𝕜] W₁))) :=
  (LinearEquiv.ofInjective _ (injective_tensorInclusion _ _ _ _)).trans
    (LinearEquiv.ofEq _ _ (range_kerTensorInclusion A B))

@[simp]
theorem coe_kerExternalProductBlockEquiv_apply (A : V₀ →L[𝕜] V₁) (B : W₀ →L[𝕜] W₁)
    (st : (LinearMap.ker (A : V₀ →ₗ[𝕜] V₁) ⊗[𝕜] LinearMap.ker (B : W₀ →ₗ[𝕜] W₁)) ×
      (LinearMap.ker (A.adjoint : V₁ →ₗ[𝕜] V₀) ⊗[𝕜] LinearMap.ker (B.adjoint : W₁ →ₗ[𝕜] W₀))) :
    (kerExternalProductBlockEquiv A B st : WithLp 2 ((V₀ ⊗[𝕜] W₀) × (V₁ ⊗[𝕜] W₁))) =
      WithLp.toLp 2 (TensorProduct.mapIncl _ _ st.1, TensorProduct.mapIncl _ _ st.2) := by
  simp [kerExternalProductBlockEquiv, tensorInclusion_apply]

/-- The dimension of the kernel of the external product block is
`dim ker A · dim ker B + dim ker A† · dim ker B†`. -/
theorem finrank_ker_externalProductBlock (A : V₀ →L[𝕜] V₁) (B : W₀ →L[𝕜] W₁)
    [FiniteDimensional 𝕜 (LinearMap.ker (A : V₀ →ₗ[𝕜] V₁))]
    [FiniteDimensional 𝕜 (LinearMap.ker (B : W₀ →ₗ[𝕜] W₁))]
    [FiniteDimensional 𝕜 (LinearMap.ker (A.adjoint : V₁ →ₗ[𝕜] V₀))]
    [FiniteDimensional 𝕜 (LinearMap.ker (B.adjoint : W₁ →ₗ[𝕜] W₀))] :
    Module.finrank 𝕜 (LinearMap.ker (externalProductBlock A B :
        WithLp 2 ((V₀ ⊗[𝕜] W₀) × (V₁ ⊗[𝕜] W₁)) →ₗ[𝕜] WithLp 2 ((V₁ ⊗[𝕜] W₀) × (V₀ ⊗[𝕜] W₁)))) =
      Module.finrank 𝕜 (LinearMap.ker (A : V₀ →ₗ[𝕜] V₁)) *
          Module.finrank 𝕜 (LinearMap.ker (B : W₀ →ₗ[𝕜] W₁)) +
        Module.finrank 𝕜 (LinearMap.ker (A.adjoint : V₁ →ₗ[𝕜] V₀)) *
          Module.finrank 𝕜 (LinearMap.ker (B.adjoint : W₁ →ₗ[𝕜] W₀)) := by
  rw [← (kerExternalProductBlockEquiv A B).finrank_eq, Module.finrank_prod,
    Module.finrank_tensorProduct, Module.finrank_tensorProduct]

end Kernel

section Adjoint

variable [CompleteSpace (V₀ ⊗[𝕜] W₀)] [CompleteSpace (V₁ ⊗[𝕜] W₁)]
  [CompleteSpace (V₁ ⊗[𝕜] W₀)] [CompleteSpace (V₀ ⊗[𝕜] W₁)]

/-- The adjoint of an external product block is the external product block of `A†` and `-B`,
that is `[[A† ⊗ 1, 1 ⊗ B†], [-(1 ⊗ B), A ⊗ 1]]`. -/
@[simp]
theorem adjoint_externalProductBlock (A : V₀ →L[𝕜] V₁) (B : W₀ →L[𝕜] W₁) :
    (externalProductBlock A B).adjoint = externalProductBlock A.adjoint (-B) := by
  refine (eq_adjoint_iff _ _ |>.2 fun x y ↦ ?_).symm
  simp only [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
    fst_externalProductBlock, snd_externalProductBlock, map_neg, adjoint_adjoint,
    lTensor_neg, neg_apply, inner_add_left, inner_sub_left, inner_neg_left, inner_add_right,
    inner_sub_right, ← adjoint_rTensor, ← adjoint_lTensor, adjoint_inner_left,
    adjoint_inner_right]
  ring

/-- `(externalProductBlock A B)† ∘ externalProductBlock A B` is block diagonal, with blocks
`A†A ⊗ 1 + 1 ⊗ B†B` and `AA† ⊗ 1 + 1 ⊗ BB†`. -/
theorem adjoint_externalProductBlock_apply_externalProductBlock (A : V₀ →L[𝕜] V₁)
    (B : W₀ →L[𝕜] W₁) (w : WithLp 2 ((V₀ ⊗[𝕜] W₀) × (V₁ ⊗[𝕜] W₁))) :
    (externalProductBlock A B).adjoint (externalProductBlock A B w) = WithLp.toLp 2
      ((A.adjoint ∘L A).rTensor W₀ w.fst + (B.adjoint ∘L B).lTensor V₀ w.fst,
        (A ∘L A.adjoint).rTensor W₁ w.snd + (B ∘L B.adjoint).lTensor V₁ w.snd) := by
  rw [adjoint_externalProductBlock, externalProductBlock_adjoint_neg_apply_externalProductBlock]

/-- `externalProductBlock A B ∘ (externalProductBlock A B)†` is block diagonal, with blocks
`AA† ⊗ 1 + 1 ⊗ B†B` and `A†A ⊗ 1 + 1 ⊗ BB†`. -/
theorem externalProductBlock_apply_adjoint_externalProductBlock (A : V₀ →L[𝕜] V₁)
    (B : W₀ →L[𝕜] W₁) (w : WithLp 2 ((V₁ ⊗[𝕜] W₀) × (V₀ ⊗[𝕜] W₁))) :
    externalProductBlock A B ((externalProductBlock A B).adjoint w) = WithLp.toLp 2
      ((A ∘L A.adjoint).rTensor W₀ w.fst + (B.adjoint ∘L B).lTensor V₁ w.fst,
        (A.adjoint ∘L A).rTensor W₁ w.snd + (B ∘L B.adjoint).lTensor V₀ w.snd) := by
  have h := externalProductBlock_adjoint_neg_apply_externalProductBlock A.adjoint (-B) w
  simp only [adjoint_adjoint, neg_neg, map_neg, comp_neg, neg_comp, neg_neg] at h
  rw [adjoint_externalProductBlock, h]

/-- **The kernel of the adjoint of the external product block**, which is its cokernel when the
range is closed: `(externalProductBlock A B)†` kills `(x, y)` exactly when `A† ⊗ 1` and `1 ⊗ B`
both kill `x` and `A ⊗ 1` and `1 ⊗ B†` both kill `y`. -/
theorem adjoint_externalProductBlock_eq_zero_iff {A : V₀ →L[𝕜] V₁} {B : W₀ →L[𝕜] W₁}
    {w : WithLp 2 ((V₁ ⊗[𝕜] W₀) × (V₀ ⊗[𝕜] W₁))} :
    (externalProductBlock A B).adjoint w = 0 ↔
      (A.adjoint.rTensor W₀ w.fst = 0 ∧ B.lTensor V₁ w.fst = 0) ∧
        A.rTensor W₁ w.snd = 0 ∧ B.adjoint.lTensor V₀ w.snd = 0 := by
  simp [adjoint_externalProductBlock, externalProductBlock_eq_zero_iff]

private theorem range_kerAdjointTensorInclusion (A : V₀ →L[𝕜] V₁) (B : W₀ →L[𝕜] W₁) :
    LinearMap.range (tensorInclusion (LinearMap.ker (A.adjoint : V₁ →ₗ[𝕜] V₀))
        (LinearMap.ker (B : W₀ →ₗ[𝕜] W₁)) (LinearMap.ker (A : V₀ →ₗ[𝕜] V₁))
        (LinearMap.ker (B.adjoint : W₁ →ₗ[𝕜] W₀))) =
      LinearMap.ker ((externalProductBlock A B).adjoint :
        WithLp 2 ((V₁ ⊗[𝕜] W₀) × (V₀ ⊗[𝕜] W₁)) →ₗ[𝕜] WithLp 2 ((V₀ ⊗[𝕜] W₀) × (V₁ ⊗[𝕜] W₁))) := by
  ext w
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, adjoint_externalProductBlock_eq_zero_iff,
    mem_range_tensorInclusion]
  simp only [rTensor_apply, lTensor_apply, ← LinearMap.mem_ker, ← Submodule.mem_inf,
    LinearMap.ker_rTensor_inf_ker_lTensor]

/-- **The Künneth isomorphism for the kernel of the adjoint of the external product block**, which
is its cokernel when the range is closed: `(ker A† ⊗ ker B) × (ker A ⊗ ker B†) ≃
ker (externalProductBlock A B)†`, given by the inclusions of the tensor products of the
kernels. -/
noncomputable def kerAdjointExternalProductBlockEquiv (A : V₀ →L[𝕜] V₁) (B : W₀ →L[𝕜] W₁) :
    ((LinearMap.ker (A.adjoint : V₁ →ₗ[𝕜] V₀) ⊗[𝕜] LinearMap.ker (B : W₀ →ₗ[𝕜] W₁)) ×
        (LinearMap.ker (A : V₀ →ₗ[𝕜] V₁) ⊗[𝕜] LinearMap.ker (B.adjoint : W₁ →ₗ[𝕜] W₀))) ≃ₗ[𝕜]
      LinearMap.ker ((externalProductBlock A B).adjoint :
        WithLp 2 ((V₁ ⊗[𝕜] W₀) × (V₀ ⊗[𝕜] W₁)) →ₗ[𝕜] WithLp 2 ((V₀ ⊗[𝕜] W₀) × (V₁ ⊗[𝕜] W₁))) :=
  (LinearEquiv.ofInjective _ (injective_tensorInclusion _ _ _ _)).trans
    (LinearEquiv.ofEq _ _ (range_kerAdjointTensorInclusion A B))

@[simp]
theorem coe_kerAdjointExternalProductBlockEquiv_apply (A : V₀ →L[𝕜] V₁) (B : W₀ →L[𝕜] W₁)
    (st : (LinearMap.ker (A.adjoint : V₁ →ₗ[𝕜] V₀) ⊗[𝕜] LinearMap.ker (B : W₀ →ₗ[𝕜] W₁)) ×
      (LinearMap.ker (A : V₀ →ₗ[𝕜] V₁) ⊗[𝕜] LinearMap.ker (B.adjoint : W₁ →ₗ[𝕜] W₀))) :
    (kerAdjointExternalProductBlockEquiv A B st : WithLp 2 ((V₁ ⊗[𝕜] W₀) × (V₀ ⊗[𝕜] W₁))) =
      WithLp.toLp 2 (TensorProduct.mapIncl _ _ st.1, TensorProduct.mapIncl _ _ st.2) := by
  simp [kerAdjointExternalProductBlockEquiv, tensorInclusion_apply]

/-- The dimension of the kernel of the adjoint of the external product block is
`dim ker A† · dim ker B + dim ker A · dim ker B†`. -/
theorem finrank_ker_adjoint_externalProductBlock (A : V₀ →L[𝕜] V₁) (B : W₀ →L[𝕜] W₁)
    [FiniteDimensional 𝕜 (LinearMap.ker (A : V₀ →ₗ[𝕜] V₁))]
    [FiniteDimensional 𝕜 (LinearMap.ker (B : W₀ →ₗ[𝕜] W₁))]
    [FiniteDimensional 𝕜 (LinearMap.ker (A.adjoint : V₁ →ₗ[𝕜] V₀))]
    [FiniteDimensional 𝕜 (LinearMap.ker (B.adjoint : W₁ →ₗ[𝕜] W₀))] :
    Module.finrank 𝕜 (LinearMap.ker ((externalProductBlock A B).adjoint :
        WithLp 2 ((V₁ ⊗[𝕜] W₀) × (V₀ ⊗[𝕜] W₁)) →ₗ[𝕜] WithLp 2 ((V₀ ⊗[𝕜] W₀) × (V₁ ⊗[𝕜] W₁)))) =
      Module.finrank 𝕜 (LinearMap.ker (A.adjoint : V₁ →ₗ[𝕜] V₀)) *
          Module.finrank 𝕜 (LinearMap.ker (B : W₀ →ₗ[𝕜] W₁)) +
        Module.finrank 𝕜 (LinearMap.ker (A : V₀ →ₗ[𝕜] V₁)) *
          Module.finrank 𝕜 (LinearMap.ker (B.adjoint : W₁ →ₗ[𝕜] W₀)) := by
  rw [← (kerAdjointExternalProductBlockEquiv A B).finrank_eq, Module.finrank_prod,
    Module.finrank_tensorProduct, Module.finrank_tensorProduct]

/-- **Multiplicativity of the index for the external product block.** The dimension of the kernel
minus the dimension of the kernel of the adjoint, which is the index when the range is closed, is
the product of the corresponding differences for `A` and `B`. -/
theorem finrank_ker_sub_finrank_ker_adjoint_externalProductBlock (A : V₀ →L[𝕜] V₁)
    (B : W₀ →L[𝕜] W₁) [FiniteDimensional 𝕜 (LinearMap.ker (A : V₀ →ₗ[𝕜] V₁))]
    [FiniteDimensional 𝕜 (LinearMap.ker (B : W₀ →ₗ[𝕜] W₁))]
    [FiniteDimensional 𝕜 (LinearMap.ker (A.adjoint : V₁ →ₗ[𝕜] V₀))]
    [FiniteDimensional 𝕜 (LinearMap.ker (B.adjoint : W₁ →ₗ[𝕜] W₀))] :
    (Module.finrank 𝕜 (LinearMap.ker (externalProductBlock A B :
        WithLp 2 ((V₀ ⊗[𝕜] W₀) × (V₁ ⊗[𝕜] W₁)) →ₗ[𝕜] WithLp 2 ((V₁ ⊗[𝕜] W₀) × (V₀ ⊗[𝕜] W₁)))) :
        ℤ) -
      Module.finrank 𝕜 (LinearMap.ker ((externalProductBlock A B).adjoint :
        WithLp 2 ((V₁ ⊗[𝕜] W₀) × (V₀ ⊗[𝕜] W₁)) →ₗ[𝕜] WithLp 2 ((V₀ ⊗[𝕜] W₀) × (V₁ ⊗[𝕜] W₁)))) =
      ((Module.finrank 𝕜 (LinearMap.ker (A : V₀ →ₗ[𝕜] V₁)) : ℤ) -
          Module.finrank 𝕜 (LinearMap.ker (A.adjoint : V₁ →ₗ[𝕜] V₀))) *
        ((Module.finrank 𝕜 (LinearMap.ker (B : W₀ →ₗ[𝕜] W₁)) : ℤ) -
          Module.finrank 𝕜 (LinearMap.ker (B.adjoint : W₁ →ₗ[𝕜] W₀))) := by
  rw [finrank_ker_externalProductBlock, finrank_ker_adjoint_externalProductBlock]
  push_cast
  ring

variable {A : V₀ →L[𝕜] V₁} {B : W₀ →L[𝕜] W₁}

/-- If `A†A = AA† = s` and `B†B = BB† = t` are scalars, then
`(externalProductBlock A B)† ∘ externalProductBlock A B = s + t`. -/
theorem adjoint_externalProductBlock_comp_self_of_eq_smul {s t : 𝕜}
    (hA : A.adjoint ∘L A = s • 1) (hA' : A ∘L A.adjoint = s • 1)
    (hB : B.adjoint ∘L B = t • 1) (hB' : B ∘L B.adjoint = t • 1) :
    (externalProductBlock A B).adjoint ∘L externalProductBlock A B = (s + t) • 1 := by
  ext w : 1
  rw [comp_apply, adjoint_externalProductBlock_apply_externalProductBlock, hA, hA', hB, hB']
  exact WithLp.ofLp_injective 2 <| Prod.ext (by simp [add_smul]) (by simp [add_smul])

/-- If `A†A = AA† = s` and `B†B = BB† = t` are scalars, then
`externalProductBlock A B ∘ (externalProductBlock A B)† = s + t`. -/
theorem externalProductBlock_comp_adjoint_of_eq_smul {s t : 𝕜}
    (hA : A.adjoint ∘L A = s • 1) (hA' : A ∘L A.adjoint = s • 1)
    (hB : B.adjoint ∘L B = t • 1) (hB' : B ∘L B.adjoint = t • 1) :
    externalProductBlock A B ∘L (externalProductBlock A B).adjoint = (s + t) • 1 := by
  ext w : 1
  rw [comp_apply, externalProductBlock_apply_adjoint_externalProductBlock, hA, hA', hB, hB']
  exact WithLp.ofLp_injective 2 <| Prod.ext (by simp [add_smul]) (by simp [add_smul])

/-- If `A†A = AA† = s` and `B†B = BB† = t` for real scalars `s` and `t`, the external product
block multiplies norms squared by `s + t`. -/
theorem norm_externalProductBlock_apply_sq_of_eq_smul {s t : ℝ}
    (hA : A.adjoint ∘L A = (s : 𝕜) • 1) (hA' : A ∘L A.adjoint = (s : 𝕜) • 1)
    (hB : B.adjoint ∘L B = (t : 𝕜) • 1) (hB' : B ∘L B.adjoint = (t : 𝕜) • 1)
    (w : WithLp 2 ((V₀ ⊗[𝕜] W₀) × (V₁ ⊗[𝕜] W₁))) :
    ‖externalProductBlock A B w‖ ^ 2 = (s + t) * ‖w‖ ^ 2 :=
  norm_apply_sq_of_adjoint_comp_eq_smul (by
    rw [adjoint_externalProductBlock_comp_self_of_eq_smul hA hA' hB hB', RCLike.ofReal_add]) w

/-- If `A†A = AA† = s` and `B†B = BB† = t` for real scalars `s` and `t`, the adjoint of the
external product block multiplies norms squared by `s + t`. -/
theorem norm_adjoint_externalProductBlock_apply_sq_of_eq_smul {s t : ℝ}
    (hA : A.adjoint ∘L A = (s : 𝕜) • 1) (hA' : A ∘L A.adjoint = (s : 𝕜) • 1)
    (hB : B.adjoint ∘L B = (t : 𝕜) • 1) (hB' : B ∘L B.adjoint = (t : 𝕜) • 1)
    (w : WithLp 2 ((V₁ ⊗[𝕜] W₀) × (V₀ ⊗[𝕜] W₁))) :
    ‖(externalProductBlock A B).adjoint w‖ ^ 2 = (s + t) * ‖w‖ ^ 2 :=
  norm_apply_sq_of_adjoint_comp_eq_smul (by
    rw [adjoint_adjoint, externalProductBlock_comp_adjoint_of_eq_smul hA hA' hB hB',
      RCLike.ofReal_add]) w

end Adjoint

section Complex

variable {V₀ V₁ W₀ W₁ : Type*} [NormedAddCommGroup V₀] [InnerProductSpace ℂ V₀] [CompleteSpace V₀]
  [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁] [CompleteSpace V₁] [NormedAddCommGroup W₀]
  [InnerProductSpace ℂ W₀] [CompleteSpace W₀] [NormedAddCommGroup W₁] [InnerProductSpace ℂ W₁]
  [CompleteSpace W₁]

/-- The external product block is a bounded real-linear, hence smooth, function of the pair of
operators. -/
theorem contDiff_externalProductBlock {n : WithTop ℕ∞} :
    ContDiff ℝ n fun AB : (V₀ →L[ℂ] V₁) × (W₀ →L[ℂ] W₁) ↦ externalProductBlock AB.1 AB.2 :=
  -- The real module structure on the space of block operators is passed explicitly: instance
  -- search for it also explores the real module structures of the tensor factors, and times out.
  IsBoundedLinearMap.contDiff
    (@IsBoundedLinearMap.mk ℝ _ _ _ _ _ _ _ _
      (@IsLinearMap.mk ℝ _ _ _ _ _ _ NormedSpace.complexToReal.toModule _
        (fun _ _ ↦ externalProductBlock_add _ _ _ _)
        (fun r AB ↦ by
          rw [Prod.smul_fst, Prod.smul_snd, ← Complex.coe_smul, ← Complex.coe_smul,
            ← Complex.coe_smul, ← RCLike.ofReal_eq_complex_ofReal]
          exact externalProductBlock_ofReal_smul r AB.1 AB.2))
      ⟨4, by norm_num, fun AB ↦ (norm_externalProductBlock_le _ _).trans (by
        linarith [norm_fst_le AB, norm_snd_le AB])⟩)

end Complex

end ContinuousLinearMap
