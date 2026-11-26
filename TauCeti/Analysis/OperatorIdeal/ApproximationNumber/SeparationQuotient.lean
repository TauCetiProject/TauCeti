/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.SeparationQuotient
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic

/-!
# Approximation numbers on separation quotients

Over any nontrivially normed scalar field `𝕜` and between arbitrary seminormed spaces `E` and `F` in
independent universes, passing to the normed separation quotient on either the domain or the
codomain preserves every approximation number `aₙ(T)`:

* `aₙ(T ∘L outCLM 𝕜 E) = aₙ(T)` (`ContinuousLinearMap.singularValue_comp_outCLM`);
* `aₙ(mkCLM 𝕜 F ∘L T) = aₙ(T)` (`ContinuousLinearMap.singularValue_mkCLM_comp`).

In contrast to extension to uniform completions
(`TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Completion`), no completeness hypothesis on `𝕜`
is needed: `SeparationQuotient.mkCLM` and `SeparationQuotient.outCLM` are contractions on `E` and
`F` themselves, and factoring `T` through `outCLM` and `mkCLM` changes `T` only by an operator of
norm zero.

## Main declarations

* `ContinuousLinearMap.singularValue_comp_outCLM`:
  `(T ∘L SeparationQuotient.outCLM 𝕜 E).singularValue n = T.singularValue n`.
* `ContinuousLinearMap.singularValue_mkCLM_comp`:
  `(SeparationQuotient.mkCLM 𝕜 F ∘L T).singularValue n = T.singularValue n`.
-/

public section

open scoped NNReal

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Precomposing a bounded linear map with `SeparationQuotient.outCLM` preserves all approximation
numbers. -/
@[simp]
theorem singularValue_comp_outCLM (T : E →L[𝕜] F) (n : ℕ) :
    (T ∘L SeparationQuotient.outCLM 𝕜 E).singularValue n = T.singularValue n := by
  let q := SeparationQuotient.mkCLM 𝕜 E
  let T' := T ∘L SeparationQuotient.outCLM 𝕜 E
  refine le_antisymm
    ((T.singularValue_comp_le_right _ n).trans
      (mul_le_of_le_one_right' SeparationQuotient.nnNorm_outCLM_le)) ?_
  calc
    T.singularValue n ≤ (T' ∘L q).singularValue n + ‖T - T' ∘L q‖₊ := by
      simpa only [add_sub_cancel] using (T' ∘L q).singularValue_add_le (T - T' ∘L q) n
    _ = (T' ∘L q).singularValue n := by simp [T.nnNorm_sub_comp_outCLM_comp_mkCLM, T', q]
    _ ≤ T'.singularValue n :=
      (T'.singularValue_comp_le_right q n).trans
        (mul_le_of_le_one_right' SeparationQuotient.nnNorm_mkCLM_le)

/-- Postcomposing a bounded linear map with `SeparationQuotient.mkCLM` preserves all approximation
numbers. -/
@[simp]
theorem singularValue_mkCLM_comp (T : E →L[𝕜] F) (n : ℕ) :
    (SeparationQuotient.mkCLM 𝕜 F ∘L T).singularValue n = T.singularValue n := by
  let s := SeparationQuotient.outCLM 𝕜 F
  let T' := SeparationQuotient.mkCLM 𝕜 F ∘L T
  refine le_antisymm
    (((SeparationQuotient.mkCLM 𝕜 F).singularValue_comp_le_left T n).trans
      (mul_le_of_le_one_left' SeparationQuotient.nnNorm_mkCLM_le)) ?_
  calc
    T.singularValue n ≤ (s ∘L T').singularValue n + ‖T - s ∘L T'‖₊ := by
      simpa only [add_sub_cancel] using (s ∘L T').singularValue_add_le (T - s ∘L T') n
    _ = (s ∘L T').singularValue n := by simp [T.nnNorm_sub_outCLM_comp_mkCLM_comp, T', s]
    _ ≤ T'.singularValue n :=
      (s.singularValue_comp_le_left T' n).trans
        (mul_le_of_le_one_left' SeparationQuotient.nnNorm_outCLM_le)

end ContinuousLinearMap
