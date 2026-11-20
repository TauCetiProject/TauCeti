/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# The norm of a multilinear map from its values on a basis

On a finite-dimensional space with a basis `b`, a continuous multilinear map `T` in `n` variables
is determined by its values `T (b σ₁, …, b σₙ)` on tuples of basis vectors, and its operator norm
is controlled by them:

`‖T‖ ≤ ‖b.equivFunL‖ ^ n ∑_σ ‖T (b ∘ σ)‖`,

where `b.equivFunL` is the coordinate isomorphism. This is the multilinear counterpart of
`Module.Basis.opNorm_le`. For the iterated derivative `D^n u (x)` of a function it bounds the full
derivative by its partial derivatives along the basis directions.

## Main results

* `ContinuousMultilinearMap.norm_le_pow_mul_sum_norm_apply_basis`: the bound above.
-/

public section

namespace ContinuousMultilinearMap

variable {𝕜 E G ι : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [Fintype ι]

/-- The operator norm of a continuous multilinear map is at most `‖b.equivFunL‖ ^ n` times the sum
of the norms of its values on all `n`-tuples of vectors of the basis `b`. -/
theorem norm_le_pow_mul_sum_norm_apply_basis {n : ℕ} (b : Module.Basis ι 𝕜 E)
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ E) G) :
    ‖T‖ ≤ ‖b.equivFunL.toContinuousLinearMap‖ ^ n * ∑ σ : Fin n → ι, ‖T (fun l ↦ b (σ l))‖ := by
  classical
  refine T.opNorm_le_bound
    (mul_nonneg (pow_nonneg (norm_nonneg _) _) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _))
    fun m ↦ ?_
  have hm : T m = ∑ σ : Fin n → ι, (∏ l, b.equivFun (m l) (σ l)) • T (fun l ↦ b (σ l)) := by
    conv_lhs => rw [show m = fun l ↦ ∑ i, b.equivFun (m l) i • b i from
      funext fun l ↦ (b.sum_equivFun (m l)).symm]
    rw [T.map_sum]
    simp_rw [T.map_smul_univ]
  rw [hm]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun σ _ ↦ ?_
  rw [norm_smul, norm_prod]
  have hc : ∀ l, ‖b.equivFun (m l) (σ l)‖ ≤ ‖b.equivFunL.toContinuousLinearMap‖ * ‖m l‖ :=
    fun l ↦ (norm_le_pi_norm (b.equivFun (m l)) (σ l)).trans
      ((b.equivFunL.toContinuousLinearMap).le_opNorm (m l))
  calc (∏ l, ‖b.equivFun (m l) (σ l)‖) * ‖T (fun l ↦ b (σ l))‖
      ≤ (∏ l, (‖b.equivFunL.toContinuousLinearMap‖ * ‖m l‖)) * ‖T (fun l ↦ b (σ l))‖ := by
        gcongr with l; exact hc l
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        ring

end ContinuousMultilinearMap
