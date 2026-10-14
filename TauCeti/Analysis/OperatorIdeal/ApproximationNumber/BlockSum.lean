/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.ProdLp
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax
public import TauCeti.Analysis.OperatorIdeal.DecreasingMerge

/-!
# Approximation numbers of orthogonal block sums

The orthogonal block sum of bounded maps `T₁ : E₁ →L[𝕜] F₁` and `T₂ : E₂ →L[𝕜] F₂` is the map
`T₁ ⊕ T₂ = T₁.withLpProdMap 2 T₂` acting componentwise on the `L²` products
`WithLp 2 (E₁ × E₂) → WithLp 2 (F₁ × F₂)`. Its approximation numbers are the generalized decreasing
merge of those of the blocks:

`aₙ(T₁ ⊕ T₂) = (a(T₁) ⊔↓ a(T₂))ₙ`.

The same holds for the block sum `T₁.withLpProdMap p T₂` on the `ℓ^p` products, for every
`1 ≤ p ≤ ∞`, and the results below are stated in that generality.

For compact blocks this says that the approximation numbers of `T₁ ⊕ T₂` list the positive
approximation numbers of `T₁` and `T₂` together in decreasing order with multiplicity, followed by
zeros only when there are finitely many positive ones. In general the merge is the generalized
order statistic `TauCeti.decreasingMerge`, which need not enumerate every approximation number of
the blocks: infinitely many approximation numbers of one block that all exceed some value hide
every approximation number of the other block below that value. For instance, an infinite plateau
of a noncompact block hides everything below it, and an infinite-rank compact block hides the
zeros of a finite-rank one.

The two inequalities hold separately at greater generality.

* **Upper bound.** For `aᵢ(T₁) < s` and `aⱼ(T₂) < s` with `i + j ≤ n`, the block sum of near-best
  approximants of ranks `i` and `j` has rank at most `n` and lies within `s` of `T₁ ⊕ T₂`, because
  the operator norm of an `ℓ^p` block sum is the larger of the two block norms. This needs neither
  an inner product nor completeness.
* **Lower bound.** Splitting `n + 1 = i + j` so that the first `i` approximation numbers of `T₁`
  and the first `j` of `T₂` exceed `t`, coercive subspaces of ranks `i` and `j` for the blocks
  combine into a subspace of rank `n + 1` on which `T₁ ⊕ T₂` is `t`-coercive. This needs the
  converse min–max localization `TauCeti.HasMinMaxLowerBound` for each block, which holds for
  complete inner product source spaces.

## Main results

* `ContinuousLinearMap.singularValue_withLpProdMap_le`: `aₙ(T₁ ⊕ T₂) ≤ (a(T₁) ⊔↓ a(T₂))ₙ`.
* `ContinuousLinearMap.decreasingMerge_le_singularValue_withLpProdMap`: the reverse inequality,
  for blocks with the converse min–max localization property.
* `ContinuousLinearMap.singularValue_withLpProdMap`: `aₙ(T₁ ⊕ T₂) = (a(T₁) ⊔↓ a(T₂))ₙ` for blocks
  with complete inner product source spaces.

## References

* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), Chapter 2.
* I. C. Gohberg, M. G. Krein, *Introduction to the Theory of Linear Nonselfadjoint Operators*,
  Translations of Mathematical Monographs 18, AMS (1969), Chapter II.
-/

public section

open scoped ENNReal NNReal

open TauCeti

namespace ContinuousLinearMap

section Upper

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {𝕜 E₁ E₂ F₁ F₂ : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [SeminormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [SeminormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [SeminormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]

/-- **Upper bound for block sums.** The approximation numbers of an `ℓ^p` block sum are at most the
generalized decreasing merge of those of the blocks. -/
theorem singularValue_withLpProdMap_le (T₁ : E₁ →L[𝕜] F₁) (T₂ : E₂ →L[𝕜] F₂) (n : ℕ) :
    (T₁.withLpProdMap p T₂).singularValue n ≤
      decreasingMerge T₁.singularValue T₂.singularValue n := by
  refine le_of_forall_gt_imp_ge_of_dense fun s hs ↦ ?_
  obtain ⟨i, j, hij, h₁, h₂⟩ :=
    (decreasingMerge_lt_iff T₁.antitone_singularValue T₂.antitone_singularValue).mp hs
  obtain ⟨R₁, hR₁, hTR₁⟩ := exists_rank_le_nnnorm_sub_lt h₁
  obtain ⟨R₂, hR₂, hTR₂⟩ := exists_rank_le_nnnorm_sub_lt h₂
  have hR : (R₁.withLpProdMap p R₂).rank ≤ n := by
    rw [rank_withLpProdMap]
    calc _ ≤ Cardinal.lift (i : Cardinal) + Cardinal.lift (j : Cardinal) :=
          add_le_add (Cardinal.lift_le.mpr hR₁) (Cardinal.lift_le.mpr hR₂)
      _ ≤ n := by
          rw [Cardinal.lift_natCast, Cardinal.lift_natCast]
          exact_mod_cast hij
  calc _ ≤ ‖T₁.withLpProdMap p T₂ - R₁.withLpProdMap p R₂‖₊ := singularValue_le_nnnorm_sub _ hR
    _ = max ‖T₁ - R₁‖₊ ‖T₂ - R₂‖₊ := by rw [← withLpProdMap_sub, nnnorm_withLpProdMap]
    _ ≤ s := max_le hTR₁.le hTR₂.le

end Upper

section Lower

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {𝕜 E₁ E₂ F₁ F₂ : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [SeminormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [SeminormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]

/-- **Lower bound for block sums.** If both blocks have the converse min–max localization
property, the approximation numbers of their `ℓ^p` block sum are at least the generalized decreasing
merge of those of the blocks. -/
theorem decreasingMerge_le_singularValue_withLpProdMap (h₁ : HasMinMaxLowerBound 𝕜 E₁ F₁)
    (h₂ : HasMinMaxLowerBound 𝕜 E₂ F₂) (T₁ : E₁ →L[𝕜] F₁) (T₂ : E₂ →L[𝕜] F₂) (n : ℕ) :
    decreasingMerge T₁.singularValue T₂.singularValue n ≤
      (T₁.withLpProdMap p T₂).singularValue n := by
  refine le_of_forall_lt_imp_le_of_dense fun t ht ↦ ?_
  -- Split `n + 1 = i + j` so that `t` lies below the first `i` approximation numbers of `T₁` and
  -- the first `j` of `T₂`, and take coercive subspaces of ranks `i` and `j`.
  obtain ⟨i, j, hij, hi, hj⟩ :=
    (le_decreasingMerge_iff T₁.antitone_singularValue T₂.antitone_singularValue).mp le_rfl
  obtain ⟨V₁, hV₁, hc₁⟩ := h₁.exists_rank_eq_coercive T₁ t.coe_nonneg fun k hk ↦
    NNReal.coe_lt_coe.mpr (ht.trans_le (hi k hk))
  obtain ⟨V₂, hV₂, hc₂⟩ := h₂.exists_rank_eq_coercive T₂ t.coe_nonneg fun k hk ↦
    NNReal.coe_lt_coe.mpr (ht.trans_le (hj k hk))
  -- Their product is a subspace of rank `n + 1` on which `T₁ ⊕ T₂` is `t`-coercive.
  set V := (V₁.prod V₂).map
    ((WithLp.linearEquiv p 𝕜 (E₁ × E₂)).symm : E₁ × E₂ →ₗ[𝕜] WithLp p (E₁ × E₂))
  have hV : (n : Cardinal) < Module.rank 𝕜 V := by
    have hn : n < i + j := by omega
    rw [LinearEquiv.rank_map_eq, Submodule.rank_prod, hV₁, hV₂, Cardinal.lift_natCast,
      Cardinal.lift_natCast]
    exact_mod_cast hn
  refine NNReal.coe_le_coe.mp ((T₁.withLpProdMap p T₂).le_singularValue_of_lt_rank hV
    fun x hx ↦ ?_)
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm, WithLp.coe_linearEquiv] at hx
  simpa using WithLp.prod_mul_norm_le_mul_norm t.coe_nonneg zero_le_one (x := x)
    (y := T₁.withLpProdMap p T₂ x) (by simpa using hc₁ _ hx.1) (by simpa using hc₂ _ hx.2)

end Lower

section RCLike

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {𝕜 E₁ E₂ F₁ F₂ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [CompleteSpace E₂]
  [SeminormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
  [SeminormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]

/-- **Approximation numbers of an orthogonal block sum.** For bounded maps out of complete inner
product spaces, the approximation numbers of the orthogonal block sum `T₁ ⊕ T₂` are the generalized
decreasing merge of those of the blocks: `aₙ(T₁ ⊕ T₂) = (a(T₁) ⊔↓ a(T₂))ₙ`. The same holds for the
block sum on the `ℓ^p` products, for every `1 ≤ p ≤ ∞`. -/
theorem singularValue_withLpProdMap (T₁ : E₁ →L[𝕜] F₁) (T₂ : E₂ →L[𝕜] F₂) (n : ℕ) :
    (T₁.withLpProdMap p T₂).singularValue n =
      decreasingMerge T₁.singularValue T₂.singularValue n :=
  (singularValue_withLpProdMap_le T₁ T₂ n).antisymm <|
    decreasingMerge_le_singularValue_withLpProdMap .of_completeSpace .of_completeSpace T₁ T₂ n

end RCLike

end ContinuousLinearMap
