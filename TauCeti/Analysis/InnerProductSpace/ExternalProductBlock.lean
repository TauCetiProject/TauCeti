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

/-!
# The external product block of two operators

Let `A : V₀ →L[𝕜] V₁` and `B : W₀ →L[𝕜] W₁` be operators between Hilbert spaces. Grade
`V₀ ⊕ V₁` and `W₀ ⊕ W₁` by `+` on the subscript `0` and `-` on the subscript `1`, and consider the
odd self-adjoint operators `D_A = [[0, A†], [A, 0]]` and `D_B = [[0, B†], [B, 0]]`. The graded
tensor product `D_A ⊗ 1 + Γ ⊗ D_B` is odd for the tensor grading, and its even-to-odd part is the
block operator

`[[A ⊗ 1, -(1 ⊗ B†)], [1 ⊗ B, A† ⊗ 1]] : (V₀ ⊗ W₀) ⊕ (V₁ ⊗ W₁) → (V₁ ⊗ W₀) ⊕ (V₀ ⊗ W₁)`,

`ContinuousLinearMap.externalProductBlock A B`, where both sums carry the Hilbert (`L²`) norm.
Applied pointwise to two principal symbols, this is the external product of symbols used for the
index of a product of elliptic operators.

Its adjoint is again such a block, `(externalProductBlock A B)† = externalProductBlock A† (-B)`,
and the cross terms cancel in both products with the adjoint, because `A ⊗ 1` and `1 ⊗ B`
commute. So the products are block diagonal:

`(externalProductBlock A B)† ∘ externalProductBlock A B = (A†A ⊗ 1 + 1 ⊗ B†B) ⊕ (AA† ⊗ 1 + 1 ⊗ BB†)`

and similarly for the product in the other order. In particular, if `A†A = AA† = s` and
`B†B = BB† = t` are scalars, both products are the scalar `s + t`. For the principal symbols
`σ_P(ξ)` and `σ_Q(η)` of two operators normalized so that `σ_P* σ_P = σ_P σ_P* = ‖ξ‖²` and
likewise for `σ_Q`, the external product therefore satisfies `A* A = A A* = ‖ξ‖² + ‖η‖²`.

## Main declarations

* `ContinuousLinearMap.externalProductBlock`: the block operator above.
* `ContinuousLinearMap.adjoint_externalProductBlock`: its adjoint is
  `externalProductBlock A† (-B)`.
* `ContinuousLinearMap.externalProductBlock_adjoint_neg_apply_externalProductBlock`: the block
  diagonal form of `externalProductBlock A† (-B) ∘ externalProductBlock A B`.
* `ContinuousLinearMap.adjoint_externalProductBlock_comp_self_of_eq_smul`,
  `ContinuousLinearMap.externalProductBlock_comp_adjoint_of_eq_smul` and
  `ContinuousLinearMap.norm_externalProductBlock_apply_sq_of_eq_smul`: the scalar case.
* `ContinuousLinearMap.norm_externalProductBlock_le`: `‖externalProductBlock A B‖ ≤ 2 (‖A‖ + ‖B‖)`.
  Together with `ContinuousLinearMap.externalProductBlock_add` and
  `ContinuousLinearMap.externalProductBlock_ofReal_smul`, this makes the block a bounded real-linear
  function of the pair `(A, B)`, hence smooth over `ℂ`
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

/-- The external product block is bounded by `2 (‖A‖ + ‖B‖)`; in particular it depends
continuously on `(A, B)`. -/
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
