/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.SNumbers.Entropy
public import TauCeti.Analysis.Normed.Operator.SNumbers.Gelfand
public import TauCeti.Analysis.Normed.Operator.SNumbers.Kolmogorov
import TauCeti.Analysis.Normed.Operator.Compact.Basic
import TauCeti.Analysis.Normed.Operator.Compact.Finite.Codimension
import TauCeti.Topology.MetricSpace.CoveringNumbers

/-!
# Covering estimates and compactness criteria for Gelfand and Kolmogorov numbers

If the image `T(B_E)` of the closed unit ball under `T : E →L[𝕜] F` is covered by `k` closed
`ε`-balls with centres `y₁, …, y_k`, then the Kolmogorov number satisfies `d_k(T) ≤ ε`: the
quotient by `span {yᵢ}` moves every point of `T(B_E)` to within `ε` of the origin. Over `ℝ` or
`ℂ` the Gelfand number satisfies `c_k(T) ≤ 2ε`: if `φᵢ` are norming functionals of the
centres, then on the subspace `⋂ ker (φᵢ ∘ T)`, of codimension at most `k`, every `T x` with
`‖x‖ ≤ 1` lies within `ε` of a centre `yᵢ` of norm `φᵢ (yᵢ - T x) ≤ ε`. With the covers by
`2 ^ n` balls defining the entropy numbers this gives `d_{2^n}(T) ≤ eₙ(T)` and
`c_{2^n}(T) ≤ 2 eₙ(T)`.

As a consequence the Gelfand and the Kolmogorov numbers both detect compactness: `cₙ(T) → 0`
and `dₙ(T) → 0` each hold exactly when `T(B_E)` is totally bounded. For the converse
implications, a subspace `V` of finite dimension with `‖π_V ∘ T‖ < ε` puts `T(B_E)` within `ε` of
a bounded piece of `V`, and a closed subspace `M` of finite codimension with `‖T|_M‖ < ε` lets a
finite net of the image of `B_E` in `E ⧸ M` lift to a net of `T(B_E)`. No projection onto `M` is
used, so the codimension of `M` does not enter the estimate. Both arguments use that bounded sets
of finite-dimensional spaces are totally bounded, which requires a locally compact scalar field.
When `F` is complete, `T` is a compact operator exactly when `cₙ(T) → 0`, and exactly when
`dₙ(T) → 0`.

## Hypotheses

* The quantitative Kolmogorov estimate `d_k(T) ≤ ‖c‖ ε` for a scalar `c` with `1 < ‖c‖`, and
  therefore `dₙ(T) → 0` for every compact `T`, hold over any `NontriviallyNormedField 𝕜`. The
  sharp estimate `d_k(T) ≤ ε` and the comparison with entropy numbers need a
  `DenselyNormedField 𝕜`.
* The Gelfand estimate uses the Hahn–Banach theorem and is stated over `RCLike 𝕜`.
* The implications from `cₙ(T) → 0` or `dₙ(T) → 0` to total boundedness hold over any locally
  compact nontrivially normed field. Over a complete field `𝕜` that is not locally compact, such
  as `𝔽₂(u)((t))`, they fail: the identity of `𝕜` has `dₙ = cₙ = 0` for `n ≥ 1`, but its closed
  unit ball is closed and not compact, hence not totally bounded.
* The converse Kolmogorov implication takes a `NormedAddCommGroup` codomain, so that its
  finite-dimensional subspaces are proper spaces. The converse Gelfand implication needs no such
  hypothesis: the quotient of a seminormed space by a closed subspace is already normed.

## Main declarations

* `ContinuousLinearMap.kolmogorovNumber_le_of_isCover`,
  `ContinuousLinearMap.gelfandNumber_le_two_mul_of_isCover`: the covering estimates
  `d_k(T) ≤ ε` and `c_k(T) ≤ 2ε`.
* `ContinuousLinearMap.kolmogorovNumber_two_pow_le_entropyNumber`,
  `ContinuousLinearMap.gelfandNumber_two_pow_le_two_mul_entropyNumber`: `d_{2^n}(T) ≤ eₙ(T)` and
  `c_{2^n}(T) ≤ 2 eₙ(T)`.
* `ContinuousLinearMap.tendsto_kolmogorovNumber_atTop_nhds_zero_iff_totallyBounded`,
  `ContinuousLinearMap.tendsto_gelfandNumber_atTop_nhds_zero_iff_totallyBounded`: total
  boundedness of `T(B_E)` via `dₙ(T) → 0` and via `cₙ(T) → 0`.
* `ContinuousLinearMap.isCompactOperator_iff_tendsto_kolmogorovNumber`,
  `ContinuousLinearMap.isCompactOperator_iff_tendsto_gelfandNumber`: compactness for a complete
  codomain.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), Theorem 9.3,
  for the compactness criteria.
* A. Pietsch, *Operator Ideals*, North-Holland Mathematical Library 20, North-Holland (1980),
  Chapter 12, for entropy numbers and their comparison with Gelfand and Kolmogorov numbers.
* M. Ullrich, Lean-SNumbers (Apache-2.0), <https://github.com/mario-ullrich/Lean-SNumbers>,
  `AddOns/Compact.lean`: an earlier Lean formalization of the compactness criteria.
-/

public section

open Filter Metric Set
open scoped NNReal Topology

namespace ContinuousLinearMap

/-! ### Kolmogorov numbers -/

section Kolmogorov

section NontriviallyNormedField

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Covering estimate over a nontrivially normed field.** If `T(B_E)` is covered by at most
`k` closed `ε`-balls, then `d_k(T) ≤ ‖c‖ ε` for every scalar `c` with `1 < ‖c‖`. -/
theorem kolmogorovNumber_le_nnnorm_mul_of_isCover (T : E →L[𝕜] F) {k : ℕ} {ε : ℝ≥0}
    {N : Finset F} (hcard : N.card ≤ k) (hN : IsCover ε ((T : E → F) '' closedBall 0 1) N)
    {c : 𝕜} (hc : 1 < ‖c‖) : T.kolmogorovNumber k ≤ ‖c‖₊ * ε := by
  -- Quotient by the span of the centres.
  have hV : Module.rank 𝕜 (Submodule.span 𝕜 (N : Set F)) ≤ k :=
    (rank_span_finset_le N).trans (by exact_mod_cast hcard)
  refine (T.kolmogorovNumber_le hV).trans ?_
  rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_mul, coe_nnNorm]
  exact T.norm_mkQL_span_comp_le_of_isCover hN hc

/-- If `T(B_E)` is totally bounded, the Kolmogorov numbers of `T` tend to zero. -/
theorem tendsto_kolmogorovNumber_atTop_nhds_zero_of_totallyBounded {T : E →L[𝕜] F}
    (hT : TotallyBounded ((T : E → F) '' closedBall 0 1)) :
    Tendsto T.kolmogorovNumber atTop (𝓝 0) := by
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  exact T.antitone_kolmogorovNumber.tendsto_atTop_nhds_zero_of_isCover hT
    fun _ _ hN ↦ T.kolmogorovNumber_le_nnnorm_mul_of_isCover le_rfl hN hc

/-- Every compact operator has Kolmogorov numbers tending to zero. -/
theorem _root_.IsCompactOperator.tendsto_kolmogorovNumber {T : E →L[𝕜] F}
    (hT : IsCompactOperator T) : Tendsto T.kolmogorovNumber atTop (𝓝 0) :=
  tendsto_kolmogorovNumber_atTop_nhds_zero_of_totallyBounded
    (hT.totallyBounded_image_closedBall 1)

end NontriviallyNormedField

section DenselyNormedField

variable {𝕜 E F : Type*} [DenselyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Covering estimate.** Over a densely normed field, if `T(B_E)` is covered by at most `k`
closed `ε`-balls, then `d_k(T) ≤ ε`. -/
theorem kolmogorovNumber_le_of_isCover (T : E →L[𝕜] F) {k : ℕ} {ε : ℝ≥0} {N : Finset F}
    (hcard : N.card ≤ k) (hN : IsCover ε ((T : E → F) '' closedBall 0 1) N) :
    T.kolmogorovNumber k ≤ ε := by
  obtain rfl | hε := eq_zero_or_pos ε
  · obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
    simpa using T.kolmogorovNumber_le_nnnorm_mul_of_isCover hcard hN hc
  refine le_of_forall_gt_imp_ge_of_dense fun a ha ↦ ?_
  -- Use a scalar `c` with `1 < ‖c‖ < a / ε`.
  obtain ⟨c, hc₁, hca⟩ := NormedField.exists_lt_nnNorm_lt 𝕜 ((one_lt_div hε).2 ha)
  refine (T.kolmogorovNumber_le_nnnorm_mul_of_isCover hcard hN
    (c := c) (by exact_mod_cast hc₁)).trans ?_
  exact ((lt_div_iff₀ hε).1 hca).le

/-- **Kolmogorov numbers below entropy numbers.** Over a densely normed field,
`d_{2^n}(T) ≤ eₙ(T)`. -/
theorem kolmogorovNumber_two_pow_le_entropyNumber (T : E →L[𝕜] F) (n : ℕ) :
    T.kolmogorovNumber (2 ^ n) ≤ T.entropyNumber n :=
  le_of_forall_gt_imp_ge_of_dense fun _ ha ↦
    let ⟨_, hcard, hN⟩ := exists_isCover_of_entropyNumber_lt ha
    T.kolmogorovNumber_le_of_isCover hcard hN

end DenselyNormedField

section LocallyCompactField

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Over a locally compact field, if the Kolmogorov numbers of `T` tend to zero, then `T(B_E)`
is totally bounded. -/
theorem totallyBounded_of_tendsto_kolmogorovNumber_atTop_nhds_zero {T : E →L[𝕜] F}
    (hT : Tendsto T.kolmogorovNumber atTop (𝓝 0)) :
    TotallyBounded ((T : E → F) '' closedBall 0 1) := by
  rw [Metric.totallyBounded_iff]
  intro r hr
  -- A subspace `V` of finite dimension with `‖π_V ∘ T‖ < r / 2`.
  have hη : (0 : ℝ≥0) < (r / 2).toNNReal := Real.toNNReal_pos.2 (half_pos hr)
  obtain ⟨n, hn⟩ := (hT.eventually (gt_mem_nhds hη)).exists
  obtain ⟨V, hV, hVT⟩ := exists_nnnorm_mkQL_comp_lt_of_kolmogorovNumber_lt hn
  have : FiniteDimensional 𝕜 V :=
    Module.rank_lt_aleph0_iff.mp (hV.trans_lt Cardinal.natCast_lt_aleph0)
  have : ProperSpace V := FiniteDimensional.proper 𝕜 V
  -- The points of `V` of norm at most `‖T‖ + r / 2` form a compact set.
  have hK : IsCompact (((↑) : V → F) '' closedBall 0 (‖T‖ + r / 2)) :=
    (isCompact_closedBall _ _).image continuous_subtypeVal
  obtain ⟨t, -, htfin, hcov⟩ :=
    finite_approx_of_totallyBounded hK.totallyBounded (r / 2) (half_pos hr)
  refine ⟨t, htfin, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  -- `T x` lies within `r / 2` of a point `v ∈ V`, which has norm at most `‖T‖ + r / 2`.
  have hdist : infDist (T x) (V : Set F) < r / 2 := by
    rw [← V.norm_mkQL_apply]
    calc ‖V.mkQL (T x)‖ = ‖(V.mkQL ∘L T) x‖ := rfl
      _ ≤ ‖V.mkQL ∘L T‖ * ‖x‖ := le_opNorm _ _
      _ ≤ ‖V.mkQL ∘L T‖ * 1 := by gcongr; exact mem_closedBall_zero_iff.1 hx
      _ < r / 2 := by rw [mul_one]; exact Real.lt_toNNReal_iff_coe_lt.1 hVT
  obtain ⟨v, hv, hxv⟩ := (infDist_lt_iff ⟨0, V.zero_mem⟩).1 hdist
  have hvK : v ∈ ((↑) : V → F) '' closedBall 0 (‖T‖ + r / 2) := by
    refine ⟨⟨v, hv⟩, mem_closedBall_zero_iff.2 ?_, rfl⟩
    calc ‖(⟨v, hv⟩ : V)‖ = ‖v‖ := rfl
      _ ≤ ‖T x‖ + dist (T x) v := by
        rw [dist_eq_norm]; exact norm_le_norm_add_norm_sub (T x) v
      _ ≤ ‖T‖ + r / 2 := by
        gcongr
        · exact T.unit_le_opNorm x (mem_closedBall_zero_iff.1 hx)
  obtain ⟨y, hy, hvy⟩ := mem_iUnion₂.1 (hcov hvK)
  exact mem_iUnion₂.2 ⟨y, hy, mem_ball.2 <| (dist_triangle _ v _).trans_lt <| by
    linarith [mem_ball.1 hvy]⟩

/-- Over a locally compact field, the Kolmogorov numbers of `T` tend to zero if and only if
`T(B_E)` is totally bounded. -/
theorem tendsto_kolmogorovNumber_atTop_nhds_zero_iff_totallyBounded (T : E →L[𝕜] F) :
    Tendsto T.kolmogorovNumber atTop (𝓝 0) ↔ TotallyBounded ((T : E → F) '' closedBall 0 1) :=
  ⟨totallyBounded_of_tendsto_kolmogorovNumber_atTop_nhds_zero,
    tendsto_kolmogorovNumber_atTop_nhds_zero_of_totallyBounded⟩

/-- Over a locally compact field and for a complete codomain, `T` is compact if and only if its
Kolmogorov numbers tend to zero. -/
theorem isCompactOperator_iff_tendsto_kolmogorovNumber [CompleteSpace F] (T : E →L[𝕜] F) :
    IsCompactOperator T ↔ Tendsto T.kolmogorovNumber atTop (𝓝 0) :=
  (isCompactOperator_iff_totallyBounded_image_closedBall T.toLinearMap one_pos).trans
    T.tendsto_kolmogorovNumber_atTop_nhds_zero_iff_totallyBounded.symm

end LocallyCompactField

end Kolmogorov

/-! ### Gelfand numbers -/

section Gelfand

section RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Covering estimate.** If `T(B_E)` is covered by at most `k` closed `ε`-balls, then
`c_k(T) ≤ 2ε`. -/
theorem gelfandNumber_le_two_mul_of_isCover (T : E →L[𝕜] F) {k : ℕ} {ε : ℝ≥0} {N : Finset F}
    (hcard : N.card ≤ k) (hN : IsCover ε ((T : E → F) '' closedBall 0 1) N) :
    T.gelfandNumber k ≤ 2 * ε := by
  obtain ⟨M, -, hM, hTM⟩ := T.exists_norm_comp_subtypeL_le_two_mul_of_isCover hN
  refine (T.gelfandNumber_le (hM.trans (by exact_mod_cast hcard))).trans ?_
  rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_mul, NNReal.coe_two]
  exact hTM

/-- **Gelfand numbers below entropy numbers.** `c_{2^n}(T) ≤ 2 eₙ(T)`. -/
theorem gelfandNumber_two_pow_le_two_mul_entropyNumber (T : E →L[𝕜] F) (n : ℕ) :
    T.gelfandNumber (2 ^ n) ≤ 2 * T.entropyNumber n := by
  refine le_of_forall_gt_imp_ge_of_dense fun a ha ↦ ?_
  have ha' : T.entropyNumber n < a / 2 := by
    rwa [lt_div_iff₀ two_pos, mul_comm]
  obtain ⟨N, hcard, hN⟩ := exists_isCover_of_entropyNumber_lt ha'
  exact (T.gelfandNumber_le_two_mul_of_isCover hcard hN).trans_eq (mul_div_cancel₀ _ two_ne_zero)

/-- If `T(B_E)` is totally bounded, the Gelfand numbers of `T` tend to zero. -/
theorem tendsto_gelfandNumber_atTop_nhds_zero_of_totallyBounded {T : E →L[𝕜] F}
    (hT : TotallyBounded ((T : E → F) '' closedBall 0 1)) :
    Tendsto T.gelfandNumber atTop (𝓝 0) :=
  T.antitone_gelfandNumber.tendsto_atTop_nhds_zero_of_isCover hT
    fun _ _ hN ↦ T.gelfandNumber_le_two_mul_of_isCover le_rfl hN

/-- Every compact operator has Gelfand numbers tending to zero. -/
theorem _root_.IsCompactOperator.tendsto_gelfandNumber {T : E →L[𝕜] F}
    (hT : IsCompactOperator T) : Tendsto T.gelfandNumber atTop (𝓝 0) :=
  tendsto_gelfandNumber_atTop_nhds_zero_of_totallyBounded (hT.totallyBounded_image_closedBall 1)

end RCLike

section NontriviallyNormedField

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If `‖x‖, ‖v‖ ≤ 1` and the class of `x - v` modulo `M` has norm below `δ ≤ 1`, then `T x` and
`T v` are within `3 ‖T|_M‖ + ‖T‖ δ` of each other. -/
private theorem dist_le_of_norm_mk_sub_lt (T : E →L[𝕜] F) (M : Submodule 𝕜 E) {x v : E}
    (hx : ‖x‖ ≤ 1) (hv : ‖v‖ ≤ 1) {δ : ℝ} (hδ : δ ≤ 1)
    (h : ‖(Submodule.Quotient.mk (x - v) : E ⧸ M)‖ < δ) :
    dist (T x) (T v) ≤ 3 * ‖T ∘L M.subtypeL‖ + ‖T‖ * δ := by
  -- Write `x - v = m + w` with `m ∈ M` and `‖w‖ < δ`, so that `‖m‖ ≤ 3`.
  obtain ⟨w, hw, hwδ⟩ :=
    Submodule.Quotient.norm_mk_lt (Submodule.Quotient.mk (x - v) : E ⧸ M) (sub_pos.2 h)
  have hm : x - v - w ∈ M := (Submodule.Quotient.eq M).1 hw.symm
  have hm3 : ‖x - v - w‖ ≤ 3 := by linarith [norm_sub_le (x - v) w, norm_sub_le x v]
  calc dist (T x) (T v) = ‖T (x - v - w) + T w‖ := by
        rw [dist_eq_norm, ← map_sub, ← map_add, sub_add_cancel]
    _ ≤ ‖T ∘L M.subtypeL‖ * ‖x - v - w‖ + ‖T‖ * ‖w‖ := (norm_add_le _ _).trans
      (add_le_add ((T ∘L M.subtypeL).le_opNorm ⟨x - v - w, hm⟩) (T.le_opNorm w))
    _ ≤ ‖T ∘L M.subtypeL‖ * 3 + ‖T‖ * δ := by gcongr; linarith
    _ = 3 * ‖T ∘L M.subtypeL‖ + ‖T‖ * δ := by ring

end NontriviallyNormedField

section LocallyCompactField

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Over a locally compact field, if the Gelfand numbers of `T` tend to zero, then `T(B_E)` is
totally bounded. -/
theorem totallyBounded_of_tendsto_gelfandNumber_atTop_nhds_zero {T : E →L[𝕜] F}
    (hT : Tendsto T.gelfandNumber atTop (𝓝 0)) :
    TotallyBounded ((T : E → F) '' closedBall 0 1) := by
  rw [Metric.totallyBounded_iff]
  intro r hr
  set δ : ℝ := min 1 (r / (4 * (‖T‖ + 1)))
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hTδ : ‖T‖ * δ ≤ r / 4 :=
    calc ‖T‖ * δ ≤ ‖T‖ * (r / (4 * (‖T‖ + 1))) := by gcongr; exact min_le_right _ _
      _ ≤ r / 4 := by
        rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) four_pos]
        nlinarith [norm_nonneg T]
  -- A closed subspace `M` of finite codimension with `‖T|_M‖ < r / 4`.
  have hη : (0 : ℝ≥0) < (r / 4).toNNReal := Real.toNNReal_pos.2 (div_pos hr four_pos)
  obtain ⟨n, hn⟩ := (hT.eventually (gt_mem_nhds hη)).exists
  obtain ⟨M, hMc, hM, hTM⟩ := exists_nnnorm_comp_subtypeL_lt hn
  have hTM' : ‖T ∘L M.subtypeL‖ < r / 4 := Real.lt_toNNReal_iff_coe_lt.1 hTM
  have : IsClosed (M : Set E) := hMc
  have : FiniteDimensional 𝕜 (E ⧸ M) :=
    Module.rank_lt_aleph0_iff.mp (hM.trans_lt Cardinal.natCast_lt_aleph0)
  have : ProperSpace (E ⧸ M) := FiniteDimensional.proper 𝕜 (E ⧸ M)
  -- The image of `B_E` in `E ⧸ M` lies in the compact unit ball, and has a finite `δ`-net
  -- consisting of images of points `u ∈ B_E`; their images under `T` form an `r`-net.
  have hK : TotallyBounded (M.mkQ '' closedBall (0 : E) 1) := by
    refine (isCompact_closedBall (0 : E ⧸ M) 1).totallyBounded.subset ?_
    rintro _ ⟨x, hx, rfl⟩
    exact mem_closedBall_zero_iff.2 ((Submodule.Quotient.norm_mk_le M x).trans
      (mem_closedBall_zero_iff.1 hx))
  obtain ⟨u, hu, hufin, hucov⟩ := exists_subset_image_finite_and.1
    (finite_approx_of_totallyBounded hK δ hδ)
  refine ⟨T '' u, hufin.image _, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨_, ⟨v, hv, rfl⟩, hxv⟩ := mem_iUnion₂.1 (hucov (mem_image_of_mem _ hx))
  refine mem_iUnion₂.2 ⟨T v, mem_image_of_mem _ hv, mem_ball.2 ?_⟩
  refine (dist_le_of_norm_mk_sub_lt T M (mem_closedBall_zero_iff.1 hx)
    (mem_closedBall_zero_iff.1 (hu hv)) (min_le_left _ _) ?_).trans_lt (by linarith)
  simpa only [mem_ball, dist_eq_norm, Submodule.mkQ_apply, Submodule.Quotient.mk_sub] using hxv

end LocallyCompactField

section RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The Gelfand numbers of `T` tend to zero if and only if `T(B_E)` is totally bounded. -/
theorem tendsto_gelfandNumber_atTop_nhds_zero_iff_totallyBounded (T : E →L[𝕜] F) :
    Tendsto T.gelfandNumber atTop (𝓝 0) ↔ TotallyBounded ((T : E → F) '' closedBall 0 1) :=
  ⟨totallyBounded_of_tendsto_gelfandNumber_atTop_nhds_zero,
    tendsto_gelfandNumber_atTop_nhds_zero_of_totallyBounded⟩

/-- For a complete codomain, `T` is compact if and only if its Gelfand numbers tend to zero. -/
theorem isCompactOperator_iff_tendsto_gelfandNumber [CompleteSpace F] (T : E →L[𝕜] F) :
    IsCompactOperator T ↔ Tendsto T.gelfandNumber atTop (𝓝 0) :=
  (isCompactOperator_iff_totallyBounded_image_closedBall T.toLinearMap one_pos).trans
    T.tendsto_gelfandNumber_atTop_nhds_zero_iff_totallyBounded.symm

end RCLike

end Gelfand

end ContinuousLinearMap
