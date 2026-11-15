/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.SNumbers.Kolmogorov
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
public import TauCeti.Analysis.Normed.Module.Ball.Summation
import TauCeti.Analysis.Normed.Group.BallSphere
import TauCeti.Analysis.Normed.Lp.Basic

/-!
# Pietsch's lifting identity

The Kolmogorov numbers of `T : E →L[𝕜] F` are the approximation numbers of `T ∘L Q`, where
`Q = TauCeti.unitClosedBallSummation 𝕜 E` is the canonical summation map from `ℓ¹` on the closed
unit ball of `E` onto `E`. Thus Kolmogorov numbers become approximation numbers after lifting the
domain to its canonical projective `ℓ¹` cover, dual to Pietsch's embedding identity for Gelfand
numbers in `TauCeti.Analysis.Normed.Operator.SNumbers.Embedding`.

The lower bound holds for precomposition with any bounded linear map lifting open balls around the
origin to open balls of the same radius, over any nontrivially normed field and between seminormed
spaces: open-ball lifting prevents quotient norms from decreasing, and Kolmogorov numbers are
bounded above by approximation numbers.

For the reverse bound, let `e : lp (fun _ : ι ↦ E) ∞` be any bounded family in a Banach space `E`
and let `V ≤ F` have rank at most `n`. Choosing near-minimal representatives in the quotient `F ⧸ V`
yields a bounded family in `V`, which is complete whenever `𝕜` is complete because `V` is
finite-dimensional. Composing `lp.linearCombination` of this family with `V.subtypeL` produces an
operator `R : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] F` of rank at most `n` with
`‖T ∘L lp.linearCombination 𝕜 e - R‖ ≤ ‖V.mkQL ∘L T‖ * ‖e‖ + δ`. The codomain `F` need not be
complete, and only the open-ball lifting step uses density of the norm on `𝕜`.

## Main results

* `ContinuousLinearMap.kolmogorovNumber_le_singularValue`: `dₙ(T) ≤ aₙ(T)` between seminormed
  spaces over any nontrivially normed field.
* `ContinuousLinearMap.kolmogorovNumber_comp_eq_of_ball_subset`: metric-quotient invariance of
  Kolmogorov numbers.
* `ContinuousLinearMap.kolmogorovNumber_le_singularValue_comp`: `dₙ(T) ≤ aₙ(T ∘L Q)` whenever `Q`
  lifts open balls around the origin.
* `ContinuousLinearMap.singularValue_comp_linearCombination_le`:
  `aₙ(T ∘L lp.linearCombination 𝕜 e) ≤ dₙ(T) * ‖e‖₊` over a complete scalar field.
* `ContinuousLinearMap.singularValue_comp_unitClosedBallSummation`: **Pietsch's lifting identity**
  `aₙ(T ∘L TauCeti.unitClosedBallSummation 𝕜 E) = dₙ(T)`.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), §4.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), Chapter 2.
* M. Ullrich, Lean-SNumbers (Apache-2.0), <https://github.com/mario-ullrich/Lean-SNumbers>,
  `SNumbers/KolmogorovLifting.lean`: an earlier Lean formalization of Pietsch's lifting identity.
-/

public section

open scoped ENNReal NNReal

namespace ContinuousLinearMap

section LowerBound

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Every Kolmogorov number is bounded above by the corresponding approximation number, without
completeness or separation assumptions on the spaces or scalar field. -/
theorem kolmogorovNumber_le_singularValue (T : E →L[𝕜] F) (n : ℕ) :
    T.kolmogorovNumber n ≤ T.singularValue n := by
  refine le_singularValue_iff.mpr fun R hR ↦ (T.kolmogorovNumber_le hR).trans ?_
  have hsub : R.range.mkQL ∘L T = R.range.mkQL ∘L (T - R) := by
    ext x
    exact (Submodule.Quotient.eq R.range).mpr ⟨x, by simp⟩
  exact hsub ▸ R.range.nnnorm_mkQL_comp_le (T - R)

/-- Kolmogorov numbers do not decrease under precomposition with an operator that lifts every open
ball around the origin to the open ball of the same radius. -/
theorem kolmogorovNumber_le_kolmogorovNumber_comp (T : F →L[𝕜] G) {Q : E →L[𝕜] F}
    (hQ : ∀ r, Metric.ball (0 : F) r ⊆ Q '' Metric.ball 0 r) (n : ℕ) :
    T.kolmogorovNumber n ≤ (T ∘L Q).kolmogorovNumber n := by
  refine le_kolmogorovNumber_iff.mpr fun V hV ↦ (T.kolmogorovNumber_le hV).trans ?_
  exact_mod_cast (V.mkQL ∘L T).opNorm_le_bound (norm_nonneg _) fun y ↦
    le_of_forall_pos_le_add fun δ hδ ↦ by
      set S := V.mkQL ∘L (T ∘L Q)
      have hdenom : 0 < ‖S‖ + 1 := add_pos_of_nonneg_of_pos (norm_nonneg _) one_pos
      obtain ⟨x, rfl, hx⟩ := TauCeti.exists_apply_eq_norm_lt_add hQ y (div_pos hδ hdenom)
      calc ‖(V.mkQL ∘L T) (Q x)‖ = ‖S x‖ := rfl
        _ ≤ ‖S‖ * ‖x‖ := S.le_opNorm x
        _ ≤ ‖S‖ * (‖Q x‖ + δ / (‖S‖ + 1)) :=
            mul_le_mul_of_nonneg_left hx.le (norm_nonneg _)
        _ = ‖S‖ * ‖Q x‖ + ‖S‖ * (δ / (‖S‖ + 1)) := mul_add _ _ _
        _ ≤ ‖S‖ * ‖Q x‖ + (‖S‖ + 1) * (δ / (‖S‖ + 1)) := by
            gcongr
            exact le_add_of_nonneg_right zero_le_one
        _ = ‖S‖ * ‖Q x‖ + δ := by rw [mul_div_cancel₀ _ hdenom.ne']

/-- **Metric-quotient invariance of Kolmogorov numbers.** Precomposing with a contraction that
lifts open balls around the origin preserves every Kolmogorov number. -/
theorem kolmogorovNumber_comp_eq_of_ball_subset (T : F →L[𝕜] G) {Q : E →L[𝕜] F}
    (hQ₁ : ‖Q‖ ≤ 1) (hQ : ∀ r, Metric.ball (0 : F) r ⊆ Q '' Metric.ball 0 r) (n : ℕ) :
    (T ∘L Q).kolmogorovNumber n = T.kolmogorovNumber n :=
  le_antisymm
    ((T.kolmogorovNumber_comp_le_right Q n).trans (mul_le_of_le_one_right' (mod_cast hQ₁)))
    (T.kolmogorovNumber_le_kolmogorovNumber_comp hQ n)

/-- Kolmogorov numbers are bounded by approximation numbers after precomposition with any operator
that lifts open balls around the origin. -/
theorem kolmogorovNumber_le_singularValue_comp (T : F →L[𝕜] G) {Q : E →L[𝕜] F}
    (hQ : ∀ r, Metric.ball (0 : F) r ⊆ Q '' Metric.ball 0 r) (n : ℕ) :
    T.kolmogorovNumber n ≤ (T ∘L Q).singularValue n :=
  (T.kolmogorovNumber_le_kolmogorovNumber_comp hQ n).trans
    ((T ∘L Q).kolmogorovNumber_le_singularValue n)

end LowerBound

section UpperBound

variable {𝕜 ι E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Over a complete scalar field, precomposing `T : E →L[𝕜] F` with `lp.linearCombination 𝕜 e`
gives approximation numbers bounded by `T.kolmogorovNumber n * ‖e‖₊`. Completeness of `F` is not
required. -/
theorem singularValue_comp_linearCombination_le (T : E →L[𝕜] F)
    (e : lp (fun _ : ι ↦ E) ∞) (n : ℕ) :
    (T ∘L lp.linearCombination 𝕜 e).singularValue n ≤ T.kolmogorovNumber n * ‖e‖₊ := by
  have : Nonempty {V : Submodule 𝕜 F // Module.rank 𝕜 V ≤ n} := ⟨⟨⊥, by simp⟩⟩
  rw [kolmogorovNumber_def, NNReal.iInf_mul]
  refine le_ciInf fun ⟨V, hV⟩ ↦ ?_
  have : FiniteDimensional 𝕜 V :=
    Module.rank_lt_aleph0_iff.mp (hV.trans_lt Cardinal.natCast_lt_aleph0)
  have : CompleteSpace V := FiniteDimensional.completeSpace 𝕜 V
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnNorm, coe_nnNorm]
  refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
  -- Lift each `T (e i)` in `F ⧸ V` within `δ` of its quotient norm to get a bounded family in `V`.
  have hlift (i : ι) :
      ∃ v : V, ‖T (e i) - (v : F)‖ ≤ ‖V.mkQL ∘L T‖ * ‖e‖ + δ := by
    obtain ⟨m, hm, hmn⟩ := Submodule.Quotient.norm_mk_lt (V.mkQL (T (e i))) hδ
    have hmem : T (e i) - m ∈ V := (Submodule.Quotient.eq V).mp hm.symm
    refine ⟨⟨T (e i) - m, hmem⟩, ?_⟩
    have hquot : ‖V.mkQL (T (e i))‖ ≤ ‖V.mkQL ∘L T‖ * ‖e‖ :=
      ((V.mkQL ∘L T).le_opNorm (e i)).trans
        (mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm ENNReal.top_ne_zero e i)
          (norm_nonneg _))
    simpa only [Submodule.coe_mk, sub_sub_cancel] using hmn.le.trans (add_le_add_left hquot δ)
  choose v hv using hlift
  have hv_mem : Memℓp v ∞ := by
    refine memℓp_infty ⟨‖T‖ * ‖e‖ + (‖V.mkQL ∘L T‖ * ‖e‖ + δ), ?_⟩
    rintro _ ⟨i, rfl⟩
    have hTe : ‖T (e i)‖ ≤ ‖T‖ * ‖e‖ :=
      (T.le_opNorm (e i)).trans
        (mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm ENNReal.top_ne_zero e i)
          (norm_nonneg _))
    calc ‖v i‖ = ‖(v i : F)‖ := rfl
      _ = ‖T (e i) - (T (e i) - (v i : F))‖ := by rw [sub_sub_cancel]
      _ ≤ ‖T (e i)‖ + ‖T (e i) - (v i : F)‖ := norm_sub_le _ _
      _ ≤ ‖T‖ * ‖e‖ + (‖V.mkQL ∘L T‖ * ‖e‖ + δ) := add_le_add hTe (hv i)
  let vLp : lp (fun _ : ι ↦ V) ∞ := ⟨v, hv_mem⟩
  let R : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] F := V.subtypeL ∘L lp.linearCombination 𝕜 vLp
  have hR_range : R.range ≤ V := by
    rintro _ ⟨a, rfl⟩
    exact (lp.linearCombination 𝕜 vLp a).2
  have hR : R.rank ≤ n := (Submodule.rank_mono hR_range).trans hV
  refine (NNReal.coe_le_coe.mpr
    ((T ∘L lp.linearCombination 𝕜 e).singularValue_le_nnnorm_sub hR)).trans ?_
  rw [coe_nnNorm]
  refine (T ∘L lp.linearCombination 𝕜 e - R).opNorm_le_bound (by positivity) fun a ↦ ?_
  have hsum₁ : HasSum (fun i ↦ a i • T (e i)) ((T ∘L lp.linearCombination 𝕜 e) a) := by
    simpa only [Function.comp_def, comp_apply, map_smul] using
      (lp.hasSum_linearCombination e a).map T T.continuous
  have hsum₂ : HasSum (fun i ↦ a i • (v i : F)) (R a) := by
    simpa only [R, vLp, Function.comp_def, comp_apply, Submodule.coe_subtypeL,
      Submodule.coe_subtype, SetLike.val_smul] using
      (lp.hasSum_linearCombination vLp a).map V.subtypeL V.subtypeL.continuous
  have hdiff : HasSum (fun i ↦ a i • (T (e i) - (v i : F)))
      ((T ∘L lp.linearCombination 𝕜 e - R) a) := by
    simpa only [sub_apply, smul_sub] using hsum₁.sub hsum₂
  refine hdiff.norm_le_of_bounded
    ((lp.hasSum_norm_one a).mul_left (‖V.mkQL ∘L T‖ * ‖e‖ + δ)) fun i ↦ ?_
  calc ‖a i • (T (e i) - (v i : F))‖
      = ‖a i‖ * ‖T (e i) - (v i : F)‖ := norm_smul _ _
    _ ≤ ‖a i‖ * (‖V.mkQL ∘L T‖ * ‖e‖ + δ) :=
        mul_le_mul_of_nonneg_left (hv i) (norm_nonneg _)
    _ = (‖V.mkQL ∘L T‖ * ‖e‖ + δ) * ‖a i‖ := mul_comm _ _

/-- Over a complete scalar field, the approximation numbers of
`T ∘L TauCeti.unitClosedBallSummation 𝕜 E` are bounded above by the Kolmogorov numbers of `T`. -/
theorem singularValue_comp_unitClosedBallSummation_le (T : E →L[𝕜] F) (n : ℕ) :
    (T ∘L TauCeti.unitClosedBallSummation 𝕜 E).singularValue n ≤ T.kolmogorovNumber n := by
  rw [TauCeti.unitClosedBallSummation_eq_linearCombination]
  exact (T.singularValue_comp_linearCombination_le (TauCeti.unitClosedBallFamily E) n).trans
    (mul_le_of_le_one_right' (TauCeti.nnNorm_unitClosedBallFamily_le E))

end UpperBound

section DenselyNormedField

variable {𝕜 E F : Type*} [DenselyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- Precomposing with `TauCeti.unitClosedBallSummation 𝕜 E` leaves Kolmogorov numbers unchanged. -/
@[simp]
theorem kolmogorovNumber_comp_unitClosedBallSummation
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] (T : E →L[𝕜] F) (n : ℕ) :
    (T ∘L TauCeti.unitClosedBallSummation 𝕜 E).kolmogorovNumber n = T.kolmogorovNumber n :=
  T.kolmogorovNumber_comp_eq_of_ball_subset (TauCeti.norm_unitClosedBallSummation_le 𝕜 E)
    (TauCeti.ball_subset_image_unitClosedBallSummation_ball 𝕜 E) n

/-- **Pietsch's lifting identity.** Over a complete densely normed field, the Kolmogorov numbers of
an operator out of a Banach space `E` equal the approximation numbers obtained after precomposing
with `TauCeti.unitClosedBallSummation 𝕜 E`. The target space `F` need not be complete. -/
theorem singularValue_comp_unitClosedBallSummation [CompleteSpace 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (T : E →L[𝕜] F) (n : ℕ) :
    (T ∘L TauCeti.unitClosedBallSummation 𝕜 E).singularValue n = T.kolmogorovNumber n :=
  le_antisymm (T.singularValue_comp_unitClosedBallSummation_le n)
    (T.kolmogorovNumber_le_singularValue_comp
      (TauCeti.ball_subset_image_unitClosedBallSummation_ball 𝕜 E) n)

end DenselyNormedField

end ContinuousLinearMap
