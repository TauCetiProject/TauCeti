/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Topology.MetricSpace.Cover
public import TauCeti.Analysis.Normed.Operator.SNumbers.Gelfand
public import TauCeti.Analysis.Normed.Operator.SNumbers.Kolmogorov
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.Algebra.SeparationQuotient.FiniteDimensional
import TauCeti.Analysis.Normed.Operator.Compact.Basic

/-!
# Covering estimates, total boundedness, and compactness for Gelfand and Kolmogorov numbers

Unlike approximation numbers—whose decay to zero requires the approximation property on general
Banach targets—both the Kolmogorov numbers `dₙ(T)` and the Gelfand numbers `cₙ(T)` detect total
boundedness of `T(B_E)` and, when the target is complete, compactness of `T` without any geometric
assumption on the spaces.

* **Covering upper bounds.** An `ε`-cover of `T(B_E)` of cardinality at most `n` bounds `dₙ(T)` by
  `ε * ‖c‖₊` for every scalar `c` with `1 < ‖c‖` (taking the span of the centres), hence by `ε`
  over a densely normed field. Over `ℝ` or `ℂ`, intersecting the kernels of `φᵢ ∘ T` for norming
  functionals `φᵢ` of the centres gives a closed subspace of codimension at most `n` on which
  `‖T x‖ ≤ 2 ε ‖x‖`, refining
  `IsCompactOperator.exists_finiteDimensional_quotient_norm_comp_subtype_le` to the quantitative
  bound `cₙ(T) ≤ 2 ε`.
* **Total boundedness from decay.** Over a locally compact scalar field, `dₙ(T) → 0` implies that
  `T(B_E)` is totally bounded: when `dₙ(T) < δ`, each point of `T(B_E)` lies within `δ` of a
  bounded ball in an at-most-`n`-dimensional subspace `V`, whose separation quotient is proper.
  Likewise, `cₙ(T) → 0` implies that `T(B_E)` is totally bounded without choosing any projection
  onto a finite-codimension subspace `M`: lifting a finite `δ`-net of the image of `B_E` in the
  proper quotient `E ⧸ M` back to `B_E` decomposes differences as `r + m` with `‖r‖ < δ`,
  `m ∈ M`, and `‖m‖ < 2 + δ` independent of codimension.
* **Compactness criteria.** Combining the covering bounds with total boundedness yields
  `TotallyBounded (T '' closedBall 0 1) ↔ dₙ(T) → 0` (over locally compact fields) and
  `TotallyBounded (T '' closedBall 0 1) ↔ cₙ(T) → 0` (over `RCLike`), and, when the target is
  complete, `IsCompactOperator T ↔ cₙ(T) → 0 ↔ dₙ(T) → 0`.

## Main declarations

* `ContinuousLinearMap.kolmogorovNumber_le_mul_of_isCover`,
  `ContinuousLinearMap.kolmogorovNumber_le_of_isCover`: covering bounds `dₙ(T) ≤ ε * ‖c‖₊` (over any
  nontrivially normed field) and `dₙ(T) ≤ ε` (over a densely normed field).
* `ContinuousLinearMap.gelfandNumber_le_two_mul_of_isCover`: covering bound `cₙ(T) ≤ 2 * ε` over an
  `RCLike` scalar field.
* `IsCompactOperator.tendsto_kolmogorovNumber`, `IsCompactOperator.tendsto_gelfandNumber`: compact
  operators have `dₙ(T) → 0` and `cₙ(T) → 0` without completeness of either space.
* `ContinuousLinearMap.totallyBounded_image_closedBall_iff_tendsto_kolmogorovNumber`: over a
  locally compact field, `T(B_E)` is totally bounded iff `dₙ(T) → 0`.
* `ContinuousLinearMap.totallyBounded_image_closedBall_iff_tendsto_gelfandNumber`: over an `RCLike`
  field, `T(B_E)` is totally bounded iff `cₙ(T) → 0`.
* `ContinuousLinearMap.tendsto_gelfandNumber_iff_tendsto_kolmogorovNumber`: over an `RCLike` field,
  `cₙ(T) → 0 ↔ dₙ(T) → 0`.
* `ContinuousLinearMap.isCompactOperator_iff_tendsto_kolmogorovNumber`,
  `ContinuousLinearMap.isCompactOperator_iff_tendsto_gelfandNumber`: compactness characterizations
  when the target space is complete.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), Theorem 9.3.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), §§2.4–2.5.
* B. Carl, I. Stephani, *Entropy, Compactness and the Approximation of Operators*, Cambridge Tracts
  in Mathematics 98, Cambridge University Press (1990), Chapters 1–2.
* M. Ullrich, Lean-SNumbers (Apache-2.0), <https://github.com/mario-ullrich/Lean-SNumbers>,
  `AddOns/Compact.lean`: an earlier Lean formalization of compactness via Gelfand and Kolmogorov
  numbers.
-/

public section

open Filter Metric Set
open scoped NNReal Topology

section KolmogorovCover

variable {𝕜 E F : Type*}

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Covering bound for Kolmogorov numbers.** If `T(B_E)` admits an `ε`-cover `C` of cardinality
at most `n`, then for every scalar `c` with `1 < ‖c‖` we have `dₙ(T) ≤ ε * ‖c‖₊`: quotienting the
target by `span 𝕜 C` kills the centres and bounds the quotient norm on the shell
`‖c‖⁻¹ ≤ ‖x‖ < 1`. -/
theorem ContinuousLinearMap.kolmogorovNumber_le_mul_of_isCover {T : E →L[𝕜] F} {n : ℕ} {ε : ℝ≥0}
    {C : Set F} (hC : C.encard ≤ n) (hcover : Metric.IsCover ε (T '' Metric.closedBall 0 1) C)
    {c : 𝕜} (hc : 1 < ‖c‖) :
    T.kolmogorovNumber n ≤ ε * ‖c‖₊ := by
  have hfin : C.Finite := encard_lt_top_iff.mp (hC.trans_lt (WithTop.coe_lt_top n))
  set V : Submodule 𝕜 F := Submodule.span 𝕜 C
  have hcard : hfin.toFinset.card ≤ n := by
    exact_mod_cast hfin.encard_eq_coe_toFinset_card.symm.trans_le hC
  have hV : Module.rank 𝕜 V ≤ n := by
    rw [show V = Submodule.span 𝕜 (hfin.toFinset : Set F) by simp [V]]
    exact (rank_span_finset_le hfin.toFinset).trans (Nat.cast_le.mpr hcard)
  refine (T.kolmogorovNumber_le hV).trans ?_
  rw [← NNReal.coe_le_coe]
  push_cast
  have _ : 0 < ‖c‖ := one_pos.trans hc
  refine ContinuousLinearMap.opNorm_le_of_shell one_pos (by positivity) hc fun x hx₁ hx₂ ↦ ?_
  have hTx : T x ∈ T '' Metric.closedBall 0 1 :=
    ⟨x, mem_closedBall_zero_iff.mpr hx₂.le, rfl⟩
  obtain ⟨y, hyC, hxy⟩ :=
    Metric.isCover_iff_subset_iUnion_closedBall.mp hcover hTx |> mem_iUnion₂.mp
  have hy0 : (Submodule.Quotient.mk y : F ⧸ V) = 0 :=
    (Submodule.Quotient.mk_eq_zero V).mpr (Submodule.subset_span hyC)
  calc ‖(V.mkQL ∘L T) x‖ = ‖V.mkQL (T x - y)‖ := by simp [hy0]
    _ ≤ ‖T x - y‖ := Submodule.Quotient.norm_mk_le V _
    _ ≤ ε := by simpa [Metric.mem_closedBall, dist_eq_norm] using hxy
    _ = ((ε : ℝ) * ‖c‖) * (1 / ‖c‖) := by field_simp
    _ ≤ ((ε : ℝ) * ‖c‖) * ‖x‖ := by gcongr

/-- **Total boundedness implies Kolmogorov decay.** Over any nontrivially normed field, if `T` maps
the closed unit ball to a totally bounded set, then `dₙ(T) → 0`. Neither space needs to be
complete. -/
theorem ContinuousLinearMap.tendsto_kolmogorovNumber_of_totallyBounded_image_closedBall
    {T : E →L[𝕜] F} (hT : TotallyBounded (T '' Metric.closedBall 0 1)) :
    Tendsto T.kolmogorovNumber atTop (𝓝 0) := by
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  have hc₀ : (0 : ℝ≥0) < ‖c‖₊ := zero_lt_one.trans (by exact_mod_cast hc)
  refine tendsto_order.mpr ⟨fun _ ha ↦ (not_lt_zero ha).elim, fun b hb ↦ ?_⟩
  have hδ : b / (2 * ‖c‖₊) ≠ 0 := by positivity
  obtain ⟨C, -, hfin, hcover⟩ := Metric.exists_finite_isCover_of_totallyBounded hδ hT
  refine eventually_atTop.mpr ⟨hfin.toFinset.card, fun n hn ↦ ?_⟩
  have hC : C.encard ≤ n := by
    rw [hfin.encard_eq_coe_toFinset_card]
    exact_mod_cast hn
  calc T.kolmogorovNumber n ≤ b / (2 * ‖c‖₊) * ‖c‖₊ :=
        T.kolmogorovNumber_le_mul_of_isCover hC hcover hc
    _ = b / 2 := by
        rw [div_eq_mul_inv, mul_inv, mul_assoc, inv_mul_cancel_right₀ hc₀.ne', ← div_eq_mul_inv]
    _ < b := NNReal.half_lt_self hb.ne'

/-- **Compactness implies Kolmogorov decay.** A compact operator between seminormed spaces over any
nontrivially normed field has `dₙ(T) → 0`. -/
theorem IsCompactOperator.tendsto_kolmogorovNumber {T : E →L[𝕜] F} (hT : IsCompactOperator T) :
    Tendsto T.kolmogorovNumber atTop (𝓝 0) :=
  T.tendsto_kolmogorovNumber_of_totallyBounded_image_closedBall
    (hT.totallyBounded_image_closedBall 1)

end NontriviallyNormedField

section DenselyNormedField

variable [DenselyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Sharp covering bound for Kolmogorov numbers.** Over a densely normed field, an `ε`-cover of
`T(B_E)` of cardinality at most `n` forces `dₙ(T) ≤ ε`. -/
theorem ContinuousLinearMap.kolmogorovNumber_le_of_isCover {T : E →L[𝕜] F} {n : ℕ} {ε : ℝ≥0}
    {C : Set F} (hC : C.encard ≤ n) (hcover : Metric.IsCover ε (T '' Metric.closedBall 0 1) C) :
    T.kolmogorovNumber n ≤ ε := by
  rcases eq_or_ne ε 0 with rfl | hε
  · obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
    simpa using T.kolmogorovNumber_le_mul_of_isCover hC hcover hc
  · refine le_of_forall_gt fun δ hδ ↦ ?_
    have hε_pos : (0 : ℝ) < ε := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hε)
    have h1 : (1 : ℝ) < (δ : ℝ) / (ε : ℝ) := (one_lt_div hε_pos).mpr (NNReal.coe_lt_coe.mpr hδ)
    obtain ⟨c, hc₁, hc₂⟩ := NormedField.exists_lt_norm_lt 𝕜 zero_le_one h1
    refine (T.kolmogorovNumber_le_mul_of_isCover hC hcover hc₁).trans_lt ?_
    rw [← NNReal.coe_lt_coe]
    push_cast
    exact mul_comm (ε : ℝ) ‖c‖ ▸ (lt_div_iff₀ hε_pos).mp hc₂

/-- **Finite-ball covering bound for Kolmogorov numbers.** Over a densely normed field, if `T(B_E)`
is covered by `s.card ≤ n` closed balls of radius `ε`, then `dₙ(T) ≤ ε`. -/
theorem ContinuousLinearMap.kolmogorovNumber_le_of_subset_biUnion_closedBall {T : E →L[𝕜] F}
    {n : ℕ} {ε : ℝ≥0} {s : Finset F} (hs : s.card ≤ n)
    (hcover : T '' Metric.closedBall 0 1 ⊆ ⋃ y ∈ s, Metric.closedBall y ε) :
    T.kolmogorovNumber n ≤ ε := by
  refine T.kolmogorovNumber_le_of_isCover (C := (s : Set F)) ?_
    (Metric.IsCover.of_subset_iUnion_closedBall (by simpa using hcover))
  rw [encard_coe_eq_coe_finsetCard]
  exact_mod_cast hs

end DenselyNormedField

end KolmogorovCover

section LocallyCompactField

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Kolmogorov decay implies total boundedness.** Over a locally compact scalar field, `dₙ(T) → 0`
implies that `T` maps the closed unit ball to a totally bounded set. -/
theorem ContinuousLinearMap.totallyBounded_image_closedBall_of_tendsto_kolmogorovNumber
    {T : E →L[𝕜] F} (h : Tendsto T.kolmogorovNumber atTop (𝓝 0)) :
    TotallyBounded (T '' Metric.closedBall 0 1) := by
  refine Metric.totallyBounded_iff.mpr fun ε hε ↦ ?_
  obtain ⟨n, hn⟩ :=
    ((tendsto_order.mp h).2 ⟨ε / 3, by positivity⟩
      (by exact_mod_cast div_pos hε (by norm_num))).exists
  obtain ⟨V, hV, hTV⟩ := T.exists_nnnorm_mkQL_comp_lt_of_kolmogorovNumber_lt hn
  have : FiniteDimensional 𝕜 V :=
    Module.rank_lt_aleph0_iff.mp (hV.trans_lt Cardinal.natCast_lt_aleph0)
  have : FiniteDimensional 𝕜 (SeparationQuotient V) := SeparationQuotient.instModuleFinite
  have : ProperSpace (SeparationQuotient V) := FiniteDimensional.proper 𝕜 (SeparationQuotient V)
  -- Pull total boundedness of the closed ball in `SeparationQuotient V` back to `V`.
  set R : ℝ := ‖T‖ + ε / 3
  have hball : TotallyBounded (Metric.closedBall (0 : V) R) := by
    have hpre : Metric.closedBall (0 : V) R =
        SeparationQuotient.mk ⁻¹' Metric.closedBall (0 : SeparationQuotient V) R := by
      ext v
      simp [Metric.mem_closedBall, dist_zero_right]
    rw [hpre]
    exact totallyBounded_preimage SeparationQuotient.isUniformInducing_mk
      (isCompact_closedBall (0 : SeparationQuotient V) R).totallyBounded
  obtain ⟨t, -, ht, hcov⟩ := Metric.finite_approx_of_totallyBounded hball (ε / 3) (by positivity)
  refine ⟨Subtype.val '' t, ht.image Subtype.val, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  have hquot : ‖V.mkQL (T x)‖ < ε / 3 :=
    (((V.mkQL ∘L T).le_opNorm x).trans
      (mul_le_of_le_one_right (norm_nonneg _) hx1)).trans_lt (by exact_mod_cast hTV)
  obtain ⟨u, hu_mk, hu_norm⟩ :=
    Submodule.Quotient.norm_mk_lt (V.mkQL (T x)) (sub_pos.mpr hquot)
  have hvV : T x - u ∈ V := (Submodule.Quotient.mk_eq_zero V).mp <| by
    rw [← Submodule.mkQ_apply, map_sub, Submodule.mkQ_apply, Submodule.mkQ_apply, hu_mk]
    simp
  have hv_ball : (⟨T x - u, hvV⟩ : V) ∈ Metric.closedBall (0 : V) R := by
    simp only [mem_closedBall_zero_iff, ← Submodule.norm_coe, R]
    have hTx : ‖T x‖ ≤ ‖T‖ :=
      (T.le_opNorm x).trans (mul_le_of_le_one_right (norm_nonneg T) hx1)
    linarith [norm_sub_le (T x) u]
  obtain ⟨w, hwt, hvw⟩ := mem_iUnion₂.mp (hcov hv_ball)
  rw [biUnion_image]
  refine mem_iUnion₂.mpr ⟨w, hwt, Metric.mem_ball.mpr ?_⟩
  have hw_dist : ‖(T x - u) - (w : F)‖ < ε / 3 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hvw
  rw [dist_eq_norm]
  calc ‖T x - (w : F)‖ = ‖((T x - u) - (w : F)) + u‖ := by abel_nf
    _ ≤ ‖(T x - u) - (w : F)‖ + ‖u‖ := norm_add_le _ _
    _ < ε := by linarith

/-- **Kolmogorov characterization of total boundedness.** Over a locally compact scalar field,
`T(B_E)` is totally bounded if and only if `dₙ(T) → 0`. -/
theorem ContinuousLinearMap.totallyBounded_image_closedBall_iff_tendsto_kolmogorovNumber
    {T : E →L[𝕜] F} :
    TotallyBounded (T '' Metric.closedBall 0 1) ↔ Tendsto T.kolmogorovNumber atTop (𝓝 0) :=
  ⟨tendsto_kolmogorovNumber_of_totallyBounded_image_closedBall,
    totallyBounded_image_closedBall_of_tendsto_kolmogorovNumber⟩

/-- **Kolmogorov decay implies compactness.** Over a locally compact scalar field, a bounded
operator into a complete space with `dₙ(T) → 0` is compact. -/
theorem ContinuousLinearMap.isCompactOperator_of_tendsto_kolmogorovNumber [CompleteSpace F]
    {T : E →L[𝕜] F} (h : Tendsto T.kolmogorovNumber atTop (𝓝 0)) : IsCompactOperator T :=
  (isCompactOperator_iff_totallyBounded_image_closedBall T.toLinearMap one_pos).mpr
    (totallyBounded_image_closedBall_of_tendsto_kolmogorovNumber h)

/-- **Kolmogorov characterization of compact operators.** Over a locally compact scalar field, a
bounded operator into a complete space is compact if and only if `dₙ(T) → 0`. -/
theorem ContinuousLinearMap.isCompactOperator_iff_tendsto_kolmogorovNumber [CompleteSpace F]
    {T : E →L[𝕜] F} :
    IsCompactOperator T ↔ Tendsto T.kolmogorovNumber atTop (𝓝 0) :=
  ⟨IsCompactOperator.tendsto_kolmogorovNumber, isCompactOperator_of_tendsto_kolmogorovNumber⟩

/-- **Gelfand decay implies total boundedness.** Over a locally compact scalar field, `cₙ(T) → 0`
implies that `T` maps the closed unit ball to a totally bounded set. The proof lifts a finite net
from the finite-dimensional quotient `E ⧸ M` directly to `B_E`, avoiding any linear projection. -/
theorem ContinuousLinearMap.totallyBounded_image_closedBall_of_tendsto_gelfandNumber
    {T : E →L[𝕜] F} (h : Tendsto T.gelfandNumber atTop (𝓝 0)) :
    TotallyBounded (T '' Metric.closedBall 0 1) := by
  refine Metric.totallyBounded_iff.mpr fun r hr ↦ ?_
  set ε : ℝ := r / 6
  set δ : ℝ := min 1 (r / (4 * (‖T‖ + 1)))
  have hε : 0 < ε := by positivity
  have hδ : 0 < δ := lt_min one_pos (div_pos hr (by positivity))
  obtain ⟨n, hn⟩ := ((tendsto_order.mp h).2 ⟨ε, hε.le⟩ (by exact_mod_cast hε)).exists
  obtain ⟨M, hM_closed, hM_rank, hTM⟩ := T.exists_nnnorm_comp_subtypeL_lt hn
  have : IsClosed (M : Set E) := hM_closed
  have : FiniteDimensional 𝕜 (E ⧸ M) :=
    Module.rank_lt_aleph0_iff.mp (hM_rank.trans_lt Cardinal.natCast_lt_aleph0)
  have : ProperSpace (E ⧸ M) := FiniteDimensional.proper 𝕜 (E ⧸ M)
  have hQ_tb : TotallyBounded (M.mkQL '' Metric.closedBall (0 : E) 1) :=
    (isCompact_closedBall (0 : E ⧸ M) 1).totallyBounded.subset <| by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_closedBall_zero_iff] at hx ⊢
      exact (Submodule.Quotient.norm_mk_le M x).trans hx
  obtain ⟨t, ht_sub, ht_fin, ht_cov⟩ := Metric.finite_approx_of_totallyBounded hQ_tb δ hδ
  let : Fintype t := ht_fin.fintype
  choose u hu_ball hu_mk using fun z : t ↦ ht_sub z.2
  refine ⟨range (fun z : t ↦ T (u z)), finite_range _, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  obtain ⟨z, hzt, hxz⟩ := mem_iUnion₂.mp (ht_cov ⟨x, hx, rfl⟩)
  let j : t := ⟨z, hzt⟩
  have hquot : ‖M.mkQL (x - u j)‖ < δ := by
    simpa [Metric.mem_ball, dist_eq_norm, map_sub, hu_mk j] using hxz
  obtain ⟨v, hv_mk, hv_norm⟩ :=
    Submodule.Quotient.norm_mk_lt (M.mkQL (x - u j)) (sub_pos.mpr hquot)
  have hmM : (x - u j) - v ∈ M := (Submodule.Quotient.mk_eq_zero M).mp <| by
    rw [← Submodule.mkQ_apply, map_sub, Submodule.mkQ_apply, Submodule.mkQ_apply, hv_mk]
    simp
  have hv_lt : ‖v‖ < δ := by linarith
  have hm_le : ‖(x - u j) - v‖ ≤ 2 + δ := by
    have hu1 : ‖u j‖ ≤ 1 := mem_closedBall_zero_iff.mp (hu_ball j)
    linarith [norm_sub_le (x - u j) v, norm_sub_le x (u j)]
  have hTm : ‖T ((x - u j) - v)‖ ≤ ε * (2 + δ) :=
    ((T ∘L M.subtypeL).le_opNorm ⟨(x - u j) - v, hmM⟩).trans
      (mul_le_mul (le_of_lt (by exact_mod_cast hTM)) hm_le (norm_nonneg _) hε.le)
  refine mem_iUnion₂.mpr ⟨T (u j), ⟨j, rfl⟩, Metric.mem_ball.mpr ?_⟩
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hTδ : ‖T‖ * δ ≤ r / 4 := by
    have hδ2 : δ ≤ r / (4 * (‖T‖ + 1)) := min_le_right _ _
    have hle : 4 * (‖T‖ + 1) * δ ≤ r := (le_div_iff₀' (by positivity)).mp hδ2
    nlinarith [norm_nonneg T, hδ.le]
  have hε_eq : ε = r / 6 := rfl
  rw [dist_eq_norm, ← map_sub]
  calc ‖T (x - u j)‖ = ‖T (((x - u j) - v) + v)‖ := by rw [sub_add_cancel]
    _ ≤ ‖T ((x - u j) - v)‖ + ‖T v‖ := by rw [map_add]; exact norm_add_le _ _
    _ ≤ ε * (2 + δ) + ‖T‖ * δ := by
        gcongr
        exact (T.le_opNorm v).trans (mul_le_mul_of_nonneg_left hv_lt.le (norm_nonneg T))
    _ < r := by nlinarith

/-- **Gelfand decay implies compactness.** Over a locally compact scalar field, a bounded operator
into a complete space with `cₙ(T) → 0` is compact. -/
theorem ContinuousLinearMap.isCompactOperator_of_tendsto_gelfandNumber [CompleteSpace F]
    {T : E →L[𝕜] F} (h : Tendsto T.gelfandNumber atTop (𝓝 0)) : IsCompactOperator T :=
  (isCompactOperator_iff_totallyBounded_image_closedBall T.toLinearMap one_pos).mpr
    (totallyBounded_image_closedBall_of_tendsto_gelfandNumber h)

end LocallyCompactField

section RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Covering bound for Gelfand numbers.** Over an `RCLike` scalar field, an `ε`-cover of `T(B_E)`
of cardinality at most `n` forces `cₙ(T) ≤ 2 * ε`: intersecting `ker (φ_y ∘ T)` over Hahn–Banach
norming functionals `φ_y` of the centres gives a subspace `M` of codimension at most `n` on which
`‖T x‖ ≤ 2 * ε * ‖x‖`. -/
theorem ContinuousLinearMap.gelfandNumber_le_two_mul_of_isCover {T : E →L[𝕜] F} {n : ℕ} {ε : ℝ≥0}
    {C : Set F} (hC : C.encard ≤ n) (hcover : Metric.IsCover ε (T '' Metric.closedBall 0 1) C) :
    T.gelfandNumber n ≤ 2 * ε := by
  have hfin : C.Finite := encard_lt_top_iff.mp (hC.trans_lt (WithTop.coe_lt_top n))
  let : Fintype C := hfin.fintype
  have hcard : Fintype.card C ≤ n := by
    rw [← Set.toFinset_card]
    exact_mod_cast hfin.encard_eq_coe_toFinset_card.symm.trans_le hC
  choose φ hφ hφ_apply using fun y : C ↦ exists_dual_vector'' 𝕜 (y : F)
  let A : E →L[𝕜] (C → 𝕜) := ContinuousLinearMap.pi fun y ↦ (φ y).comp T
  have hrank : Module.rank 𝕜 (E ⧸ LinearMap.ker A.toLinearMap) ≤ n := by
    have h1 := A.toLinearMap.quotKerEquivRange.lift_rank_eq
    have h2 : Module.rank 𝕜 (LinearMap.range A.toLinearMap) ≤ n := by
      refine (Submodule.rank_le _).trans ?_
      rw [rank_fun']
      exact Nat.cast_le.mpr hcard
    exact Cardinal.lift_le_nat_iff.mp (h1.trans_le (Cardinal.lift_le_nat_iff.mpr h2))
  refine (T.gelfandNumber_le hrank).trans ?_
  rw [← NNReal.coe_le_coe]
  push_cast
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ ?_
  by_cases hx0 : ‖(x : E)‖ = 0
  · have hTx0 : ‖T (x : E)‖ ≤ 0 := by simpa [hx0] using T.le_opNorm (x : E)
    simpa [← Submodule.norm_coe, hx0] using hTx0
  · -- Rescale `x` onto the unit sphere so `T u` lies in the covered image `T(B_E)`.
    let u : E := (‖(x : E)‖⁻¹ : 𝕜) • (x : E)
    have hu_norm : ‖u‖ = 1 := by
      simp [u, norm_smul, inv_mul_cancel₀ hx0]
    have hTu : T u ∈ T '' Metric.closedBall 0 1 :=
      ⟨u, mem_closedBall_zero_iff.mpr hu_norm.le, rfl⟩
    obtain ⟨y, hyC, huy⟩ :=
      Metric.isCover_iff_subset_iUnion_closedBall.mp hcover hTu |> mem_iUnion₂.mp
    let j : C := ⟨y, hyC⟩
    have hzero : φ j (T u) = 0 := by
      have hx_ker : A (x : E) = 0 := x.2
      have hu_ker : A u = 0 := by simp [u, hx_ker]
      exact congrFun hu_ker j
    have hy_le : ‖y‖ ≤ ‖T u - y‖ := by
      calc ‖y‖ = ‖φ j (y - T u)‖ := by rw [map_sub, hzero, sub_zero, hφ_apply]; simp [j]
        _ ≤ ‖φ j‖ * ‖y - T u‖ := (φ j).le_opNorm _
        _ ≤ ‖y - T u‖ := mul_le_of_le_one_left (norm_nonneg _) (hφ j)
        _ = ‖T u - y‖ := norm_sub_rev _ _
    have hdist : ‖T u - y‖ ≤ ε := by simpa [Metric.mem_closedBall, dist_eq_norm] using huy
    have hTu_le : ‖T u‖ ≤ 2 * (ε : ℝ) := by
      calc ‖T u‖ ≤ ‖T u - y‖ + ‖y‖ := by
            simpa only [sub_add_cancel] using norm_add_le (T u - y) y
        _ ≤ 2 * (ε : ℝ) := by linarith
    have hxu : (x : E) = (‖(x : E)‖ : 𝕜) • u := by
      have hne : (‖(x : E)‖ : 𝕜) ≠ 0 := by exact_mod_cast hx0
      simp [u, smul_smul, mul_inv_cancel₀ hne]
    calc ‖(T ∘L (LinearMap.ker A.toLinearMap).subtypeL) x‖ = ‖T ((‖(x : E)‖ : 𝕜) • u)‖ := by
          simp [← hxu]
      _ = ‖x‖ * ‖T u‖ := by simp [map_smul, norm_smul]
      _ ≤ 2 * (ε : ℝ) * ‖x‖ := by
          rw [mul_comm ‖x‖]
          exact mul_le_mul_of_nonneg_right hTu_le (norm_nonneg x)

/-- **Finite-ball covering bound for Gelfand numbers.** Over an `RCLike` scalar field, if `T(B_E)`
is covered by `s.card ≤ n` closed balls of radius `ε`, then `cₙ(T) ≤ 2 * ε`. -/
theorem ContinuousLinearMap.gelfandNumber_le_two_mul_of_subset_biUnion_closedBall {T : E →L[𝕜] F}
    {n : ℕ} {ε : ℝ≥0} {s : Finset F} (hs : s.card ≤ n)
    (hcover : T '' Metric.closedBall 0 1 ⊆ ⋃ y ∈ s, Metric.closedBall y ε) :
    T.gelfandNumber n ≤ 2 * ε := by
  refine T.gelfandNumber_le_two_mul_of_isCover (C := (s : Set F)) ?_
    (Metric.IsCover.of_subset_iUnion_closedBall (by simpa using hcover))
  rw [encard_coe_eq_coe_finsetCard]
  exact_mod_cast hs

/-- **Total boundedness implies Gelfand decay.** Over an `RCLike` scalar field, if `T` maps the
closed unit ball to a totally bounded set, then `cₙ(T) → 0`. Neither space needs to be complete. -/
theorem ContinuousLinearMap.tendsto_gelfandNumber_of_totallyBounded_image_closedBall
    {T : E →L[𝕜] F} (hT : TotallyBounded (T '' Metric.closedBall 0 1)) :
    Tendsto T.gelfandNumber atTop (𝓝 0) := by
  refine tendsto_order.mpr ⟨fun _ ha ↦ (not_lt_zero ha).elim, fun b hb ↦ ?_⟩
  have hδ : b / 4 ≠ 0 := by positivity
  obtain ⟨C, -, hfin, hcover⟩ := Metric.exists_finite_isCover_of_totallyBounded hδ hT
  refine eventually_atTop.mpr ⟨hfin.toFinset.card, fun n hn ↦ ?_⟩
  have hC : C.encard ≤ n := by
    rw [hfin.encard_eq_coe_toFinset_card]
    exact_mod_cast hn
  calc T.gelfandNumber n ≤ 2 * (b / 4) := T.gelfandNumber_le_two_mul_of_isCover hC hcover
    _ = b / 2 := by rw [← NNReal.coe_inj]; push_cast; ring
    _ < b := NNReal.half_lt_self hb.ne'

/-- **Compactness implies Gelfand decay.** Over an `RCLike` scalar field, a compact operator
between seminormed spaces has `cₙ(T) → 0`. -/
theorem IsCompactOperator.tendsto_gelfandNumber {T : E →L[𝕜] F} (hT : IsCompactOperator T) :
    Tendsto T.gelfandNumber atTop (𝓝 0) :=
  T.tendsto_gelfandNumber_of_totallyBounded_image_closedBall (hT.totallyBounded_image_closedBall 1)

/-- **Gelfand characterization of total boundedness.** Over an `RCLike` scalar field, `T(B_E)` is
totally bounded if and only if `cₙ(T) → 0`. -/
theorem ContinuousLinearMap.totallyBounded_image_closedBall_iff_tendsto_gelfandNumber
    {T : E →L[𝕜] F} :
    TotallyBounded (T '' Metric.closedBall 0 1) ↔ Tendsto T.gelfandNumber atTop (𝓝 0) :=
  ⟨tendsto_gelfandNumber_of_totallyBounded_image_closedBall,
    totallyBounded_image_closedBall_of_tendsto_gelfandNumber⟩

/-- **Equivalence of Gelfand and Kolmogorov decay.** Over an `RCLike` scalar field, `cₙ(T) → 0` if
and only if `dₙ(T) → 0`, with no completeness assumption on either space. -/
theorem ContinuousLinearMap.tendsto_gelfandNumber_iff_tendsto_kolmogorovNumber {T : E →L[𝕜] F} :
    Tendsto T.gelfandNumber atTop (𝓝 0) ↔ Tendsto T.kolmogorovNumber atTop (𝓝 0) :=
  T.totallyBounded_image_closedBall_iff_tendsto_gelfandNumber.symm.trans
    T.totallyBounded_image_closedBall_iff_tendsto_kolmogorovNumber

/-- **Gelfand characterization of compact operators.** Over an `RCLike` scalar field, a bounded
operator into a complete space is compact if and only if `cₙ(T) → 0`. -/
theorem ContinuousLinearMap.isCompactOperator_iff_tendsto_gelfandNumber [CompleteSpace F]
    {T : E →L[𝕜] F} :
    IsCompactOperator T ↔ Tendsto T.gelfandNumber atTop (𝓝 0) :=
  ⟨IsCompactOperator.tendsto_gelfandNumber, isCompactOperator_of_tendsto_gelfandNumber⟩

end RCLike
