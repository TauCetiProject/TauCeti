/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.BlockSum
public import TauCeti.Analysis.OperatorIdeal.Family.SymmetricGauge

/-!
# Symmetric-gauge ideals of orthogonal block sums

For a symmetric gauge `Φ` and bounded maps `T₁ : E₁ →L[𝕜] F₁` and `T₂ : E₂ →L[𝕜] F₂`, this file
computes the induced gauge `Φ(T₁ ⊕ T₂) = Φ∞(n ↦ aₙ(T₁ ⊕ T₂))` of the block sum
`T₁ ⊕ T₂ = T₁.withLpProdMap p T₂`, and bounds it by the gauges of the blocks:

`max Φ(T₁) Φ(T₂) ≤ Φ(T₁ ⊕ T₂) ≤ Φ(T₁) + Φ(T₂)`.

In particular, for maps from Hilbert spaces into inner product spaces, `T₁ ⊕ T₂` has finite gauge,
that is, lies in the operator ideal attached to `Φ`, exactly when both blocks do.

* **Block formula.** On Hilbert blocks, the approximation numbers of `T₁ ⊕ T₂` are the generalized
  decreasing merge `a(T₁) ⊔↓ a(T₂)` of those of the blocks
  (`ContinuousLinearMap.singularValue_withLpProdMap`), so `Φ(T₁ ⊕ T₂)` is the extended gauge of
  that merge. As this does not depend on the exponent `p`, neither does `Φ(T₁ ⊕ T₂)`.
* **Lower bound.** Each block is the compression of `T₁ ⊕ T₂` by the contractive inclusion of a
  factor and the contractive projection onto a factor, so its gauge is at most `Φ(T₁ ⊕ T₂)` by the
  ideal inequality. This holds for bounded maps between arbitrary seminormed spaces, as does the
  identity `Φ(T₁ ⊕ 0) = Φ(T₁)`.
* **Upper bound.** For `p = 2`, the block sum is the sum `(T₁ ⊕ 0) + (0 ⊕ T₂)` of maps between
  Hilbert spaces, so subadditivity of the induced gauge applies; the block formula transfers the
  bound to every `p`.

## Main results

* `TauCeti.SymmetricGauge.opGauge_withLpProdMap`: `Φ(T₁ ⊕ T₂) = Φ∞(a(T₁) ⊔↓ a(T₂))`.
* `TauCeti.SymmetricGauge.opGauge_le_opGauge_withLpProdMap_left`,
  `TauCeti.SymmetricGauge.opGauge_le_opGauge_withLpProdMap_right`: `Φ(Tᵢ) ≤ Φ(T₁ ⊕ T₂)`.
* `TauCeti.SymmetricGauge.opGauge_withLpProdMap_zero_right`,
  `TauCeti.SymmetricGauge.opGauge_withLpProdMap_zero_left`: `Φ(T₁ ⊕ 0) = Φ(T₁)` and
  `Φ(0 ⊕ T₂) = Φ(T₂)`.
* `TauCeti.SymmetricGauge.opGauge_withLpProdMap_le_add`: `Φ(T₁ ⊕ T₂) ≤ Φ(T₁) + Φ(T₂)`.

## References

* I. C. Gohberg, M. G. Krein, *Introduction to the Theory of Linear Nonselfadjoint Operators in
  Hilbert Space*, Translations of Mathematical Monographs 18, AMS (1969), Chapter III.
* B. Simon, *Trace Ideals and Their Applications*, 2nd ed., Mathematical Surveys and Monographs
  120, AMS (2005), Chapter 1.
-/

public section

open ContinuousLinearMap
open scoped ENNReal NNReal

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
  exact Φ.opGauge_comp_comp_le_self
    (opNorm_le_bound _ zero_le_one fun y ↦ by simpa using WithLp.norm_fst_le (x := y)) _
    (opNorm_le_bound _ zero_le_one fun x ↦ by simp)

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
  exact Φ.opGauge_comp_comp_le_self
    (opNorm_le_bound _ zero_le_one fun y ↦ by simpa using WithLp.norm_snd_le (x := y)) _
    (opNorm_le_bound _ zero_le_one fun x ↦ by simp)

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
  exact Φ.opGauge_comp_comp_le_self (opNorm_le_bound _ zero_le_one fun y ↦ by simp) _
    (opNorm_le_bound _ zero_le_one fun x ↦ by simpa using WithLp.norm_fst_le (x := x))

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
  exact Φ.opGauge_comp_comp_le_self (opNorm_le_bound _ zero_le_one fun y ↦ by simp) _
    (opNorm_le_bound _ zero_le_one fun x ↦ by simpa using WithLp.norm_snd_le (x := x))

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

variable {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]

/-- **Upper bound for block sums.** For bounded maps from Hilbert spaces into inner product spaces,
the gauge of the block sum is at most the sum of the gauges of the blocks:
`Φ(T₁ ⊕ T₂) ≤ Φ(T₁) + Φ(T₂)`. -/
theorem opGauge_withLpProdMap_le_add (T₁ : E₁ →L[𝕜] F₁) (T₂ : E₂ →L[𝕜] F₂) :
    Φ.opGauge (T₁.withLpProdMap p T₂) ≤ Φ.opGauge T₁ + Φ.opGauge T₂ := by
  -- By the block formula the gauge does not depend on `p`, so it suffices to treat the orthogonal
  -- block sum `p = 2`, which is a sum of two maps between Hilbert spaces.
  rw [Φ.opGauge_withLpProdMap, ← Φ.opGauge_withLpProdMap (p := 2)]
  calc Φ.opGauge (T₁.withLpProdMap 2 T₂)
      = Φ.opGauge (T₁.withLpProdMap 2 (0 : E₂ →L[𝕜] F₂) +
          (0 : E₁ →L[𝕜] F₁).withLpProdMap 2 T₂) := by
        rw [← withLpProdMap_add, add_zero, zero_add]
    _ ≤ Φ.opGauge (T₁.withLpProdMap 2 (0 : E₂ →L[𝕜] F₂)) +
          Φ.opGauge ((0 : E₁ →L[𝕜] F₁).withLpProdMap 2 T₂) :=
        Φ.opGauge_add_le _ _
    _ = Φ.opGauge T₁ + Φ.opGauge T₂ := by simp

end InnerProductSpace

end SymmetricGauge

end TauCeti
