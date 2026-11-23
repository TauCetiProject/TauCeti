/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import TauCeti.Analysis.InnerProductSpace.Gram.Factor
import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Completion
import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax

/-!
# Scalar factorization of operators through Euclidean space

For every bounded operator `T : H₁ →L[𝕜] H₂` between seminormed inner product spaces over `ℝ` or
`ℂ` and every scalar `0 ≤ c < aₙ(T)` strictly below the `n`-th approximation number, the scalar
multiple `c • id` on `EuclideanSpace 𝕜 (Fin (n + 1))` factors through `T` via contractions:
`B ∘L T ∘L A = c • id` with `‖A‖ ≤ 1` and `‖B‖ ≤ 1`. Neither `H₁` nor `H₂` needs to be complete
or separated.

This factorization isolates the geometric content of approximation numbers on inner product spaces
independently of abstract s-number axioms. In particular, it drives the uniqueness theorem showing
that every s-number sequence coincides with the approximation numbers on inner product spaces
(`TauCeti.SNumbers.IsSNumberSequence.eq_singularValue`), as well as lower bounds comparing
approximation numbers with other ideal norms and s-number families.

## Main declarations

* `ContinuousLinearMap.exists_comp_comp_eq_smul_id`: for `0 ≤ c < aₙ(T)` between seminormed inner
  product spaces, `B ∘L T ∘L A = c • id` on `EuclideanSpace 𝕜 (Fin (n + 1))` with `‖A‖ ≤ 1` and
  `‖B‖ ≤ 1`.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), Theorem 8.2.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), Theorem 2.11.9.
* M. Ullrich, Lean-SNumbers (Apache-2.0), <https://github.com/mario-ullrich/Lean-SNumbers>,
  `SNumbers/Uniqueness.lean`: an earlier Lean formalization of the scalar-factorization step on
  Hilbert spaces.
-/

public section

open UniformSpace

namespace ContinuousLinearMap

/-- **Scalar factorization through Euclidean space.** For every bounded linear map
`T : H₁ →L[𝕜] H₂` between seminormed inner product spaces over `ℝ` or `ℂ` and every
`0 ≤ c < aₙ(T)` there exist contractions `A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁` and
`B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))` such that `B ∘L T ∘L A = c • id`. Neither `H₁` nor
`H₂` needs to be complete or separated. -/
theorem exists_comp_comp_eq_smul_id {𝕜 H₁ H₂ : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
    [SeminormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    (T : H₁ →L[𝕜] H₂) (n : ℕ) {c : ℝ} (hc0 : 0 ≤ c) (hc : c < T.singularValue n) :
    ∃ (A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁)
      (B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ B ∘L T ∘L A = (c : 𝕜) • ContinuousLinearMap.id 𝕜 _ := by
  rcases hc0.eq_or_lt with rfl | hc_pos
  · exact ⟨0, 0, by simp, by simp, by ext; simp⟩
  -- Step 1: Pass to `T.completion` and apply converse min–max localization to parameterize an
  -- `(n + 1)`-dimensional subspace on which `T.completion` is `s`-coercive (`s > c`).
  have hc' : c < T.completion.singularValue n := by rwa [T.singularValue_completion]
  obtain ⟨s, hcs, v, hv, hs⟩ :=
    TauCeti.hasMinMaxLowerBound_iff.mp TauCeti.HasMinMaxLowerBound.of_completeSpace
      T.completion n hc0 hc'
  set V : Submodule 𝕜 (Completion H₁) := Submodule.span 𝕜 (Set.range v)
  have : FiniteDimensional 𝕜 V := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
  have hdim : Module.finrank 𝕜 V = n + 1 := by rw [finrank_span_eq_card hv, Fintype.card_fin]
  let e : OrthonormalBasis (Fin (n + 1)) 𝕜 V := (stdOrthonormalBasis 𝕜 V).reindex (finCongr hdim)
  let Aᵢ : EuclideanSpace 𝕜 (Fin (n + 1)) →ₗᵢ[𝕜] Completion H₁ :=
    V.subtypeₗᵢ.comp e.repr.symm.toLinearIsometry
  have hA' (u : EuclideanSpace 𝕜 (Fin (n + 1))) :
      s * ‖u‖ ≤ ‖T.completion (Aᵢ.toContinuousLinearMap u)‖ := by
    rw [LinearIsometry.coe_toContinuousLinearMap, ← Aᵢ.norm_map u]
    exact hs (Aᵢ u) (e.repr.symm u).property
  -- Step 2: Pull `Aᵢ` back from `Completion H₁` into `H₁` as a contraction making `T ∘L A`
  -- `c`-coercive.
  obtain ⟨A, hA_norm, hA_coercive⟩ :=
    T.exists_norm_le_and_mul_norm_le_norm_apply_of_completion hcs hA'
  -- Step 3: Factor `c • id` through `toComplL ∘L T ∘L A` in `Completion H₂` via `factorThru`,
  -- then precompose with `toComplL : H₂ →L[𝕜] Completion H₂`.
  let ι₂ : H₂ →L[𝕜] Completion H₂ := Completion.toComplL
  set F : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] Completion H₂ := ι₂ ∘L T ∘L A with hF
  set C_id : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) :=
    (c : 𝕜) • ContinuousLinearMap.id 𝕜 _
  have hbound (u : EuclideanSpace 𝕜 (Fin (n + 1))) : ‖C_id u‖ ≤ 1 * ‖F u‖ := by
    calc ‖C_id u‖ = c * ‖u‖ := by simp [C_id, norm_smul, abs_of_pos hc_pos]
      _ ≤ ‖T (A u)‖ := hA_coercive u
      _ = 1 * ‖F u‖ := by simp [F, ι₂]
  refine ⟨A, (C_id.factorThru F) ∘L ι₂, hA_norm.trans Aᵢ.norm_toContinuousLinearMap_le, ?_, ?_⟩
  · exact (opNorm_comp_le _ _).trans <|
      (mul_le_mul (norm_factorThru_le zero_le_one hbound)
        (Completion.toComplₗᵢ : H₂ →ₗᵢ[𝕜] Completion H₂).norm_toContinuousLinearMap_le
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · rw [comp_assoc, ← hF]
    exact factorThru_comp ⟨1, hbound⟩

end ContinuousLinearMap
