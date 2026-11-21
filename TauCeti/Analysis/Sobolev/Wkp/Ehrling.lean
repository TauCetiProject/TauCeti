/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Compact.Ehrling
public import TauCeti.Analysis.Sobolev.Wkp.Local.Compactness
import TauCeti.Topology.Sets.Opens

/-!
# Rellich compactness and Ehrling's inequality with a common compact support

Let `Ω` be an open subset of a finite-dimensional real inner product space, let `1 ≤ p ≤ ∞` and
let `l < k` be orders. This file proves the Euclidean Rellich theorem and Ehrling's inequality for
the weak Sobolev spaces `W^{k,p}(Ω)`, for functions with a common compact support and, on a
relatively compact open subdomain `V`, with no support condition at all.

* On `V`, restriction followed by forgetting the derivatives of order above `l` is compact from
  `W^{k,p}(Ω)` to `W^{l,p}(V)` (`TauCeti.Wkp.isCompactOperator_restrictL_toOrderL`), and
  `‖u‖_{W^{l,p}(V)} ≤ ε ‖u‖_{W^{k,p}(Ω)} + C_ε ‖u‖_{Lᵖ(V)}`
  (`TauCeti.Wkp.exists_norm_restrictL_toOrderL_le`).
* For a compact `K ⊆ Ω`, a bounded sequence in `W^{k,p}(Ω)` vanishing off `K` has a subsequence
  converging in `W^{l,p}(Ω)` (`TauCeti.Wkp.exists_subseq_tendsto_toOrderL_of_isCompact`), and
  every `u ∈ W^{k,p}(Ω)` vanishing off `K` satisfies
  `‖u‖_{W^{l,p}(Ω)} ≤ ε ‖u‖_{W^{k,p}(Ω)} + C_ε ‖u‖_{Lᵖ(Ω)}`, with `C_ε` depending on `K` but
  not on `u` (`TauCeti.Wkp.exists_norm_toOrderL_le_of_isCompact`).

The support condition cannot be dropped on unbounded domains: on `ℝⁿ`, `n ≥ 1`, the translates of a
fixed nonzero test function are bounded in `W^{k,p}` and have no subsequence converging in `Lᵖ`.

The compactness input is the local Rellich theorem
`TauCeti.Wkp.isCompactOperator_restrictL_lowerOrderL`, and Ehrling's inequality follows from it by
the abstract `IsCompactOperator.exists_norm_le_mul_norm_add_mul_norm`. A function vanishing off
`K ⊆ V` has the same norm on `V` as on `Ω` (`TauCeti.Wkp.norm_restrictL_eq_of_isClosed`), which
transfers both statements from `V` to `Ω`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 9.16.
* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 6.3.
* J.-L. Lions, *Quelques méthodes de résolution des problèmes aux limites non linéaires*,
  Dunod, 1969, Chapitre 1, Lemme 5.1.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega V : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-! ### Interior statements on a relatively compact subdomain -/

/-- **Local Rellich compactness to every lower order.** For orders `l < k`, restriction to a
relatively compact open subdomain `V` followed by truncation to order `l` is compact from
`W^{k,p}(Ω)` to `W^{l,p}(V)`, for every `1 ≤ p ≤ ∞`. -/
theorem isCompactOperator_restrictL_toOrderL
    (hVc : IsCompact (closure (V : Set E))) (hVO : closure (V : Set E) ⊆ Omega)
    {l k : ℕ} (hlk : l < k) :
    IsCompactOperator ((restrictL (mu := mu) (p := p) (SetLike.coe_subset_coe.mp
      (subset_closure.trans hVO)) l).comp (toOrderL hlk.le)) := by
  rw [← lowerOrderL_comp_toOrderL hlk, ← ContinuousLinearMap.comp_assoc]
  exact (isCompactOperator_restrictL_lowerOrderL hVc hVO l).comp_clm _

/-- **Interior Ehrling inequality.** For orders `l < k`, a relatively compact open subdomain `V`
of `Ω` and `ε > 0`, there is `C ≥ 0` with
`‖u‖_{W^{l,p}(V)} ≤ ε ‖u‖_{W^{k,p}(Ω)} + C ‖u‖_{Lᵖ(V)}` for every `u ∈ W^{k,p}(Ω)`. -/
theorem exists_norm_restrictL_toOrderL_le
    (hVc : IsCompact (closure (V : Set E))) (hVO : closure (V : Set E) ⊆ Omega)
    {l k : ℕ} (hlk : l < k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ u : Wkp mu Omega p k,
      ‖restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hVO)) l (toOrderL hlk.le u)‖ ≤
        ε * ‖u‖ + C * ‖value k (restrictL (SetLike.coe_subset_coe.mp
          (subset_closure.trans hVO)) k u)‖ := by
  obtain ⟨C, hC, h⟩ := IsCompactOperator.exists_norm_le_mul_norm_add_mul_norm
    (isCompactOperator_restrictL_toOrderL (mu := mu) (p := p) hVc hVO hlk) (j := valueL l)
    (fun v w hvw ↦ ext l (by simpa only [valueL_apply] using hvw)) hε
  refine ⟨C, hC, fun u ↦ ?_⟩
  simpa only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, valueL_apply,
    ← toOrderL_restrictL, value_toOrderL] using h u

/-! ### Functions with a common compact support -/

/-- Truncation keeps a function vanishing off `K` vanishing off `K`. -/
private theorem ae_value_toOrderL_eq_zero {K : Set E} {l k : ℕ} (hlk : l ≤ k)
    {u : Wkp mu Omega p k} (hu : ∀ᵐ x ∂mu.restrict (Omega : Set E), x ∉ K → value k u x = 0) :
    ∀ᵐ x ∂mu.restrict (Omega : Set E), x ∉ K → value l (toOrderL hlk u) x = 0 := by
  simpa only [value_toOrderL] using hu

/-- **Rellich compactness with a common compact support.** For a compact `K ⊆ Ω` and orders
`l < k`, every bounded sequence in `W^{k,p}(Ω)` whose members vanish off `K` has a subsequence
converging in `W^{l,p}(Ω)`, for every `1 ≤ p ≤ ∞`. -/
theorem exists_subseq_tendsto_toOrderL_of_isCompact {K : Set E} (hK : IsCompact K)
    (hKO : K ⊆ Omega) {l k : ℕ} (hlk : l < k) {u : ℕ → Wkp mu Omega p k} {R : ℝ}
    (hu : ∀ n, ‖u n‖ ≤ R)
    (hK0 : ∀ n, ∀ᵐ x ∂mu.restrict (Omega : Set E), x ∉ K → value k (u n) x = 0) :
    ∃ w : Wkp mu Omega p l, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n ↦ toOrderL hlk.le (u (φ n))) atTop (𝓝 w) := by
  obtain ⟨V, hKV, hVO, hVc⟩ := Opens.exists_between_and_isCompact_closure hK hKO
  have hV : V ≤ Omega := SetLike.coe_subset_coe.mp (subset_closure.trans hVO)
  obtain ⟨w, φ, hφ, hw⟩ :=
    (isCompactOperator_restrictL_toOrderL (mu := mu) (p := p) hVc hVO hlk).exists_subseq_tendsto
      hu
  -- The truncated subsequence is Cauchy in `W^{l,p}(Ω)`: its differences vanish off `K ⊆ V`, so
  -- their norms are those of the convergent restrictions to `V`.
  have hcauchy : CauchySeq fun n ↦ toOrderL hlk.le (u (φ n)) := by
    refine Metric.cauchySeq_iff.2 fun δ hδ ↦
      (Metric.cauchySeq_iff.1 hw.cauchySeq δ hδ).imp fun N hN m hm n hn ↦ ?_
    have hsub : ∀ᵐ x ∂mu.restrict (Omega : Set E), x ∉ K →
        value l (toOrderL hlk.le (u (φ m)) - toOrderL hlk.le (u (φ n))) x = 0 := by
      rw [value_sub]
      filter_upwards [Lp.coeFn_sub (value l (toOrderL hlk.le (u (φ m))))
          (value l (toOrderL hlk.le (u (φ n)))), ae_value_toOrderL_eq_zero hlk.le (hK0 (φ m)),
        ae_value_toOrderL_eq_zero hlk.le (hK0 (φ n))] with x hx hxm hxn hxK
      rw [hx, Pi.sub_apply, hxm hxK, hxn hxK, sub_zero]
    rw [dist_eq_norm, ← norm_restrictL_eq_of_isClosed hV hK.isClosed
      (inter_subset_right.trans hKV) l hsub, map_sub, ← dist_eq_norm]
    simpa only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply] using hN m hm n hn
  obtain ⟨w', hw'⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨w', φ, hφ, hw'⟩

/-- **Ehrling's inequality with a common compact support.** For a compact `K ⊆ Ω`, orders
`l < k` and `ε > 0`, there is `C ≥ 0` with
`‖u‖_{W^{l,p}(Ω)} ≤ ε ‖u‖_{W^{k,p}(Ω)} + C ‖u‖_{Lᵖ(Ω)}` for every `u ∈ W^{k,p}(Ω)` vanishing off
`K`, for every `1 ≤ p ≤ ∞`. -/
theorem exists_norm_toOrderL_le_of_isCompact {K : Set E} (hK : IsCompact K) (hKO : K ⊆ Omega)
    {l k : ℕ} (hlk : l < k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ u : Wkp mu Omega p k,
      (∀ᵐ x ∂mu.restrict (Omega : Set E), x ∉ K → value k u x = 0) →
        ‖toOrderL hlk.le u‖ ≤ ε * ‖u‖ + C * ‖value k u‖ := by
  obtain ⟨V, hKV, hVO, hVc⟩ := Opens.exists_between_and_isCompact_closure hK hKO
  have hV : V ≤ Omega := SetLike.coe_subset_coe.mp (subset_closure.trans hVO)
  obtain ⟨C, hC, h⟩ :=
    exists_norm_restrictL_toOrderL_le (mu := mu) (p := p) hVc hVO hlk hε
  refine ⟨C, hC, fun u hu ↦ ?_⟩
  rw [← norm_restrictL_eq_of_isClosed hV hK.isClosed (inter_subset_right.trans hKV) l
    (ae_value_toOrderL_eq_zero hlk.le hu),
    ← norm_value_restrictL_eq hV (inter_subset_right.trans hKV) k hu]
  exact h u

end TauCeti.Wkp
