/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.BlockSum
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Diagonal
public import TauCeti.Analysis.OperatorIdeal.Family.SymmetricGauge

/-!
# Symmetric-gauge ideals of orthogonal block sums

For a symmetric gauge `Φ` and bounded maps `T₁ : E₁ →L[𝕜] F₁` and `T₂ : E₂ →L[𝕜] F₂`, this file
computes the induced gauge `Φ(T₁ ⊕ T₂) = Φ∞(n ↦ aₙ(T₁ ⊕ T₂))` of the block sum
`T₁ ⊕ T₂ = T₁.withLpProdMap p T₂`, and bounds it by the gauges of the blocks:

`max Φ(T₁) Φ(T₂) ≤ Φ(T₁ ⊕ T₂) ≤ Φ(T₁) + Φ(T₂)`.

In particular, `T₁ ⊕ T₂` has finite gauge, that is, lies in the operator ideal attached to `Φ`,
exactly when both blocks do.

* **Block formula.** On Hilbert blocks, the approximation numbers of `T₁ ⊕ T₂` are the generalized
  decreasing merge `a(T₁) ⊔↓ a(T₂)` of those of the blocks
  (`ContinuousLinearMap.singularValue_withLpProdMap`), so `Φ(T₁ ⊕ T₂)` is the extended gauge of
  that merge. As this does not depend on the exponent `p`, neither does `Φ(T₁ ⊕ T₂)`.
* **Lower bound.** Each block is the compression of `T₁ ⊕ T₂` by the contractive inclusion of a
  factor and the contractive projection onto a factor, so its gauge is at most `Φ(T₁ ⊕ T₂)` by the
  ideal inequality. This holds for bounded maps between arbitrary seminormed spaces, as does the
  identity `Φ(T₁ ⊕ 0) = Φ(T₁)`.
* **Upper bound.** For decreasing sequences, `Φ∞(a ⊔↓ b) ≤ Φ∞(a) + Φ∞(b)`: realising `a` and `b`
  as the approximation numbers of diagonal operators on `ℓ²`, the orthogonal block sum of these
  is the sum `(D₁ ⊕ 0) + (0 ⊕ D₂)` of maps between Hilbert spaces, so subadditivity of the induced
  gauge applies. As the approximation numbers of `T₁ ⊕ T₂` are always at most the merge of those
  of the blocks, the bound `Φ(T₁ ⊕ T₂) ≤ Φ(T₁) + Φ(T₂)` holds for bounded maps between arbitrary
  seminormed spaces.

## Main results

* `TauCeti.SymmetricGauge.opGauge_withLpProdMap`: `Φ(T₁ ⊕ T₂) = Φ∞(a(T₁) ⊔↓ a(T₂))`.
* `TauCeti.SymmetricGauge.opGauge_le_opGauge_withLpProdMap_left`,
  `TauCeti.SymmetricGauge.opGauge_le_opGauge_withLpProdMap_right`: `Φ(Tᵢ) ≤ Φ(T₁ ⊕ T₂)`.
* `TauCeti.SymmetricGauge.opGauge_withLpProdMap_zero_right`,
  `TauCeti.SymmetricGauge.opGauge_withLpProdMap_zero_left`: `Φ(T₁ ⊕ 0) = Φ(T₁)` and
  `Φ(0 ⊕ T₂) = Φ(T₂)`.
* `TauCeti.SymmetricGauge.extend_decreasingMerge_le`: `Φ∞(a ⊔↓ b) ≤ Φ∞(a) + Φ∞(b)`.
* `TauCeti.SymmetricGauge.opGauge_withLpProdMap_le_add`: `Φ(T₁ ⊕ T₂) ≤ Φ(T₁) + Φ(T₂)`.

## References

* I. C. Gohberg, M. G. Krein, *Introduction to the Theory of Linear Nonselfadjoint Operators in
  Hilbert Space*, Translations of Mathematical Monographs 18, AMS (1969), Chapter III.
* B. Simon, *Trace Ideals and Their Applications*, 2nd ed., Mathematical Surveys and Monographs
  120, AMS (2005), Chapter 1.
-/

public section

open ContinuousLinearMap
open scoped ENNReal NNReal lp

namespace TauCeti

namespace SymmetricGauge

variable (Φ : SymmetricGauge) {p : ℝ≥0∞} [Fact (1 ≤ p)]

section Seminormed

variable {𝕜 E₁ E₂ F₁ F₂ : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [SeminormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [SeminormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [SeminormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]

/-- **Lower bound by the first block.** The gauge of the first block is at most that of the block
sum: `Φ(T₁) ≤ Φ(T₁ ⊕ T₂)`. -/
theorem opGauge_le_opGauge_withLpProdMap_left (T₁ : E₁ →L[𝕜] F₁) (T₂ : E₂ →L[𝕜] F₂) :
    Φ.opGauge T₁ ≤ Φ.opGauge (T₁.withLpProdMap p T₂) := by
  -- `T₁` is the compression of `T₁ ⊕ T₂` to the first factors.
  have h : T₁ = WithLp.fstL p 𝕜 F₁ F₂ ∘L T₁.withLpProdMap p T₂ ∘L
      ((WithLp.prodContinuousLinearEquiv p 𝕜 E₁ E₂).symm.toContinuousLinearMap ∘L
        ContinuousLinearMap.inl 𝕜 E₁ E₂) := by
    ext x
    simp
  conv_lhs => rw [h]
  exact Φ.opGauge_comp_comp_le_self (WithLp.norm_fstL_le_one ..) _
    (WithLp.norm_prodContinuousLinearEquiv_symm_comp_inl_le_one ..)

/-- **Lower bound by the second block.** The gauge of the second block is at most that of the block
sum: `Φ(T₂) ≤ Φ(T₁ ⊕ T₂)`. -/
theorem opGauge_le_opGauge_withLpProdMap_right (T₁ : E₁ →L[𝕜] F₁) (T₂ : E₂ →L[𝕜] F₂) :
    Φ.opGauge T₂ ≤ Φ.opGauge (T₁.withLpProdMap p T₂) := by
  -- `T₂` is the compression of `T₁ ⊕ T₂` to the second factors.
  have h : T₂ = WithLp.sndL p 𝕜 F₁ F₂ ∘L T₁.withLpProdMap p T₂ ∘L
      ((WithLp.prodContinuousLinearEquiv p 𝕜 E₁ E₂).symm.toContinuousLinearMap ∘L
        ContinuousLinearMap.inr 𝕜 E₁ E₂) := by
    ext x
    simp
  conv_lhs => rw [h]
  exact Φ.opGauge_comp_comp_le_self (WithLp.norm_sndL_le_one ..) _
    (WithLp.norm_prodContinuousLinearEquiv_symm_comp_inr_le_one ..)

/-- A block sum with a zero second block has the gauge of its first block:
`Φ(T₁ ⊕ 0) = Φ(T₁)`. -/
@[simp]
theorem opGauge_withLpProdMap_zero_right (T₁ : E₁ →L[𝕜] F₁) :
    Φ.opGauge (T₁.withLpProdMap p (0 : E₂ →L[𝕜] F₂)) = Φ.opGauge T₁ := by
  refine le_antisymm ?_ (Φ.opGauge_le_opGauge_withLpProdMap_left T₁ 0)
  -- `T₁ ⊕ 0` factors through `T₁` by projecting onto and including the first factors.
  have h : T₁.withLpProdMap p (0 : E₂ →L[𝕜] F₂) =
      ((WithLp.prodContinuousLinearEquiv p 𝕜 F₁ F₂).symm.toContinuousLinearMap ∘L
        ContinuousLinearMap.inl 𝕜 F₁ F₂) ∘L T₁ ∘L WithLp.fstL p 𝕜 E₁ E₂ := by
    ext x
    simp
  rw [h]
  exact Φ.opGauge_comp_comp_le_self
    (WithLp.norm_prodContinuousLinearEquiv_symm_comp_inl_le_one ..) _ (WithLp.norm_fstL_le_one ..)

/-- A block sum with a zero first block has the gauge of its second block:
`Φ(0 ⊕ T₂) = Φ(T₂)`. -/
@[simp]
theorem opGauge_withLpProdMap_zero_left (T₂ : E₂ →L[𝕜] F₂) :
    Φ.opGauge ((0 : E₁ →L[𝕜] F₁).withLpProdMap p T₂) = Φ.opGauge T₂ := by
  refine le_antisymm ?_ (Φ.opGauge_le_opGauge_withLpProdMap_right 0 T₂)
  -- `0 ⊕ T₂` factors through `T₂` by projecting onto and including the second factors.
  have h : (0 : E₁ →L[𝕜] F₁).withLpProdMap p T₂ =
      ((WithLp.prodContinuousLinearEquiv p 𝕜 F₁ F₂).symm.toContinuousLinearMap ∘L
        ContinuousLinearMap.inr 𝕜 F₁ F₂) ∘L T₂ ∘L WithLp.sndL p 𝕜 E₁ E₂ := by
    ext x
    simp
  rw [h]
  exact Φ.opGauge_comp_comp_le_self
    (WithLp.norm_prodContinuousLinearEquiv_symm_comp_inr_le_one ..) _ (WithLp.norm_sndL_le_one ..)

end Seminormed

section InnerProductSpace

variable {𝕜 E₁ E₂ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [CompleteSpace E₂]

/-- **Symmetric-gauge block formula.** For bounded maps from Hilbert spaces into inner product
spaces, the gauge of the block sum is the extended gauge of the generalized decreasing merge of the
approximation numbers of the blocks: `Φ(T₁ ⊕ T₂) = Φ∞(a(T₁) ⊔↓ a(T₂))`. -/
theorem opGauge_withLpProdMap {F₁ F₂ : Type*}
    [SeminormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
    [SeminormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]
    (T₁ : E₁ →L[𝕜] F₁) (T₂ : E₂ →L[𝕜] F₂) :
    Φ.opGauge (T₁.withLpProdMap p T₂) =
      Φ.extend fun n ↦ (decreasingMerge T₁.singularValue T₂.singularValue n : ℝ≥0∞) := by
  simp only [opGauge_def, singularValue_withLpProdMap]

/-- **Extended gauge of a decreasing merge.** For decreasing sequences `a` and `b`, the extended
gauge of their generalized decreasing merge is at most the sum of their extended gauges:
`Φ∞(a ⊔↓ b) ≤ Φ∞(a) + Φ∞(b)`. -/
theorem extend_decreasingMerge_le {a b : ℕ → ℝ≥0} (ha : Antitone a) (hb : Antitone b) :
    Φ.extend (fun n ↦ (decreasingMerge a b n : ℝ≥0∞)) ≤
      Φ.extend (fun n ↦ (a n : ℝ≥0∞)) + Φ.extend (fun n ↦ (b n : ℝ≥0∞)) := by
  -- Realise `a` and `b` as the approximation numbers of diagonal operators on real `ℓ²`.
  obtain ⟨d₁, rfl⟩ := lp.exists_singularValue_diagonalCLM_eq (𝕜 := ℝ) (p := 2) ha
  obtain ⟨d₂, rfl⟩ := lp.exists_singularValue_diagonalCLM_eq (𝕜 := ℝ) (p := 2) hb
  set D₁ : ℓ²(ℕ, ℝ) →L[ℝ] ℓ²(ℕ, ℝ) := lp.diagonalCLM d₁
  set D₂ : ℓ²(ℕ, ℝ) →L[ℝ] ℓ²(ℕ, ℝ) := lp.diagonalCLM d₂
  -- The orthogonal block sum of the diagonal operators is the sum `(D₁ ⊕ 0) + (0 ⊕ D₂)` of maps
  -- between Hilbert spaces, so subadditivity of the induced gauge applies.
  rw [← Φ.opGauge_withLpProdMap (p := 2), ← opGauge_def, ← opGauge_def]
  calc Φ.opGauge (D₁.withLpProdMap 2 D₂)
      = Φ.opGauge (D₁.withLpProdMap 2 (0 : ℓ²(ℕ, ℝ) →L[ℝ] ℓ²(ℕ, ℝ)) +
          (0 : ℓ²(ℕ, ℝ) →L[ℝ] ℓ²(ℕ, ℝ)).withLpProdMap 2 D₂) := by
        rw [← withLpProdMap_add, add_zero, zero_add]
    _ ≤ Φ.opGauge (D₁.withLpProdMap 2 (0 : ℓ²(ℕ, ℝ) →L[ℝ] ℓ²(ℕ, ℝ))) +
          Φ.opGauge ((0 : ℓ²(ℕ, ℝ) →L[ℝ] ℓ²(ℕ, ℝ)).withLpProdMap 2 D₂) :=
        Φ.opGauge_add_le _ _
    _ = Φ.opGauge D₁ + Φ.opGauge D₂ := by simp

end InnerProductSpace

section UpperBound

variable {𝕜 E₁ E₂ F₁ F₂ : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [SeminormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [SeminormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [SeminormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]

/-- **Upper bound for block sums.** The gauge of the block sum is at most the sum of the gauges of
the blocks: `Φ(T₁ ⊕ T₂) ≤ Φ(T₁) + Φ(T₂)`. -/
theorem opGauge_withLpProdMap_le_add (T₁ : E₁ →L[𝕜] F₁) (T₂ : E₂ →L[𝕜] F₂) :
    Φ.opGauge (T₁.withLpProdMap p T₂) ≤ Φ.opGauge T₁ + Φ.opGauge T₂ := by
  simp only [opGauge_def]
  exact (Φ.extend_mono fun n ↦ ENNReal.coe_le_coe.2 (singularValue_withLpProdMap_le T₁ T₂ n)).trans
    (Φ.extend_decreasingMerge_le T₁.antitone_singularValue T₂.antitone_singularValue)

end UpperBound

end SymmetricGauge

end TauCeti
