/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Compactoid
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete

/-!
# Compactoid subsets of the model spaces `C₀(I, K)`

For a discrete index `I` and a normed field `K`, a subset `S` of the model space
`C₀(I, K)` is compactoid exactly when it is bounded and its coordinates decay uniformly: for every
`ε > 0` there is a finite `T ⊆ I` with `‖x i‖ < ε` for all `x ∈ S` and `i ∉ T`
(`TauCeti.isCompactoidSet_iff_isBounded_and_exists_finset_forall_norm_lt`).

Applied to the image of the closed unit ball under an operator between model spaces, uniform
coordinate decay is decay of the row norms of its matrix, so this is the set-level half of the
identification of operators with compactoid image with operators whose matrix rows tend to zero.
Neither completeness, nor discreteness of the valuation, nor the ultrametric inequality is used.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §3.
* W. H. Schikhof, *Banach spaces over nonarchimedean valued fields*, Topology Proceedings **24**
  (1999), 547–581, §2.15.
-/

public section

open Filter Topology ZeroAtInftyContinuousMap
open scoped ZeroAtInfty

namespace TauCeti

variable {K I : Type*} [TopologicalSpace I] [DiscreteTopology I]

section NormedField

variable [NormedField K]

/-- The coordinates of a compactoid subset of `C₀(I, K)` decay uniformly: for every `ε > 0` there
is a finite `T` with `‖x i‖ < ε` for all `x ∈ S` and `i ∉ T`. -/
theorem IsCompactoidSet.exists_finset_forall_norm_lt {S : Set C₀(I, K)}
    (hS : IsCompactoidSet K S) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset I, ∀ x ∈ S, ∀ i ∉ T, ‖x i‖ < ε := by
  obtain ⟨n, v, hv⟩ := isCompactoidSet_iff.1 hS (ε / 2) (half_pos hε)
  set δ := ε / (2 * (n + 1)) with hδ
  have hδ₀ : 0 < δ := by positivity
  -- Off a finite set, every one of the finitely many approximating vectors is `δ`-small.
  have hfin : {i | ¬∀ k, ‖v k i‖ < δ}.Finite := eventually_cofinite.1 <|
    eventually_all.2 fun k ↦
      (v k).tendsto_cofinite.norm.eventually (gt_mem_nhds (by rwa [norm_zero]))
  refine ⟨hfin.toFinset, fun x hx i hi ↦ ?_⟩
  have hsmall : ∀ k, ‖v k i‖ < δ := by simpa using hi
  obtain ⟨a, ha, hx⟩ := hv x hx
  have hsum : ‖∑ k, a k * v k i‖ ≤ n * δ :=
    (norm_sum_le _ _).trans <| by
      simpa using Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) ↦
        (norm_mul_le _ _).trans <| (mul_le_of_le_one_left (norm_nonneg _) (ha k)).trans
          (hsmall k).le
  have hnδ : n * δ < ε / 2 := by
    rw [hδ, mul_div_assoc', div_lt_div_iff₀ (by positivity) two_pos]
    nlinarith
  have hi' : x i = (x - ∑ k, a k • v k) i + ∑ k, a k * v k i := by
    simp [coe_sum, Finset.sum_apply]
  calc ‖x i‖ ≤ ‖(x - ∑ k, a k • v k) i‖ + ‖∑ k, a k * v k i‖ := hi' ▸ norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le
        ((norm_coe_le_norm _ i).trans_lt hx) (hsum.trans hnδ.le)
    _ = ε := add_halves ε

/-- **Compactoid subsets of `C₀(I, K)`**: a set is compactoid if and only if it is bounded and its
coordinates decay uniformly, i.e. for every `ε > 0` there is a finite `T` with `‖x i‖ < ε` for all
`x ∈ S` and `i ∉ T`. -/
theorem isCompactoidSet_iff_isBounded_and_exists_finset_forall_norm_lt {S : Set C₀(I, K)} :
    IsCompactoidSet K S ↔
      Bornology.IsBounded S ∧ ∀ ε : ℝ, 0 < ε → ∃ T : Finset I, ∀ x ∈ S, ∀ i ∉ T, ‖x i‖ < ε := by
  classical
  refine ⟨fun hS ↦ ⟨hS.isBounded, fun ε hε ↦ hS.exists_finset_forall_norm_lt hε⟩, ?_⟩
  rintro ⟨hb, hdecay⟩
  -- A nonzero scalar `c` dominating every coordinate: one of large norm if the norm on `K` is
  -- nontrivial, and `1` otherwise, since then every scalar has norm at most `1`.
  obtain ⟨c, hc₀, hc⟩ : ∃ c : K, c ≠ 0 ∧ ∀ x ∈ S, ∀ i, ‖x i‖ ≤ ‖c‖ := by
    by_cases hK : ∃ a : K, 1 < ‖a‖
    · let : NontriviallyNormedField K := { ‹NormedField K› with non_trivial := hK }
      obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hb
      obtain ⟨c, hc⟩ := NormedField.exists_lt_norm K (max M 0)
      exact ⟨c, norm_pos_iff.1 <| (le_max_right M 0).trans_lt hc, fun x hx i ↦
        (norm_coe_le_norm x i).trans <| (hM x hx).trans <| (le_max_left M 0).trans hc.le⟩
    · push Not at hK
      exact ⟨1, one_ne_zero, fun x _ i ↦ (hK (x i)).trans norm_one.ge⟩
  -- Approximate `x` by its truncation `∑ i ∈ T, (c⁻¹ * x i) • single i c` to the finite set `T`.
  refine isCompactoidSet_of_forall_exists_finset (fun i ↦ single i c) fun ε hε ↦ ?_
  obtain ⟨T, hT⟩ := hdecay (ε / 2) (half_pos hε)
  refine ⟨T, fun x hx ↦ ⟨fun i ↦ c⁻¹ * x i, fun i ↦ ?_, ?_⟩⟩
  · rw [norm_mul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.2 hc₀), mul_one]
    exact hc x hx i
  · have htrunc : ∑ i ∈ T, (c⁻¹ * x i) • single i c = ∑ i ∈ T, single i (x i) :=
      Finset.sum_congr rfl fun i _ ↦ by
        rw [← single_smul, smul_eq_mul, mul_assoc, mul_comm (x i) c, inv_mul_cancel_left₀ hc₀]
    rw [htrunc]
    refine ((norm_le (half_pos hε).le).2 fun j ↦ ?_).trans_lt (half_lt_self hε)
    by_cases hj : j ∈ T
    · simp [hj, (half_pos hε).le]
    · simpa [sum_single_apply, hj] using (hT x hx j hj).le

end NormedField

end TauCeti
