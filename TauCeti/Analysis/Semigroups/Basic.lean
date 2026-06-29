/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# Strongly continuous semigroups

This file contains the foundational C₀-semigroup structures, the nonnegative-time API
(`map_zero`, `map_add`, and their apply forms), the `realOperator` real-time shim,
operator-norm local boundedness, and strong continuity within the nonnegative half-line.

## References
Ported and adapted (Apache 2.0) from `mrdouglasny/hille-yosida`; references include
Engel--Nagel, Linares, Pazy, Hille, and Yosida.
-/

public section

noncomputable section

open scoped Topology NNReal

namespace TauCeti.Semigroups

/-! ## Strongly Continuous Semigroups -/

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]


/-- A strongly continuous one-parameter semigroup (C₀-semigroup) on a Banach space.

The semigroup is indexed by nonnegative real time. The axioms are `S 0 = Id`,
`S (s + t) = S s ∘ S t`, and strong continuity at `0`. -/
structure StronglyContinuousSemigroup where
  /-- The semigroup operator at time `t : ℝ≥0`. -/
  toFun : ℝ≥0 → X →L[ℝ] X
  /-- `S 0 = Id`. -/
  map_zero' : toFun 0 = ContinuousLinearMap.id ℝ X
  /-- `S (s + t) = S s ∘ S t`. -/
  map_add' : ∀ s t : ℝ≥0, toFun (s + t) = (toFun s).comp (toFun t)
  /-- Strong continuity at 0. -/
  continuousAt_zero' : ∀ x : X, ContinuousAt (fun t : ℝ≥0 => toFun t x) 0

variable {X}

namespace StronglyContinuousSemigroup

omit [CompleteSpace X] in
instance instFunLike : FunLike (StronglyContinuousSemigroup X) ℝ≥0 (X →L[ℝ] X) where
  coe := toFun
  coe_injective := by
    intro S T h
    cases S
    cases T
    congr

omit [CompleteSpace X] in
@[ext]
theorem ext {S T : StronglyContinuousSemigroup X} (h : ∀ t, S t = T t) : S = T :=
  DFunLike.ext _ _ h

omit [CompleteSpace X] in
/-- The native nonnegative-time operator at zero is the identity. -/
@[simp]
theorem map_zero (S : StronglyContinuousSemigroup X) :
    S 0 = ContinuousLinearMap.id ℝ X :=
  S.map_zero'

omit [CompleteSpace X] in
/-- Pointwise form of `StronglyContinuousSemigroup.map_zero`. -/
@[simp]
theorem map_zero_apply (S : StronglyContinuousSemigroup X) (x : X) :
    S 0 x = x := by
  rw [S.map_zero]
  rfl

omit [CompleteSpace X] in
/-- The native nonnegative-time semigroup law. -/
@[simp]
theorem map_add (S : StronglyContinuousSemigroup X) (s t : ℝ≥0) :
    S (s + t) = (S s).comp (S t) :=
  S.map_add' s t

omit [CompleteSpace X] in
/-- Pointwise form of `StronglyContinuousSemigroup.map_add`. -/
@[simp]
theorem map_add_apply (S : StronglyContinuousSemigroup X) (s t : ℝ≥0) (x : X) :
    S (s + t) x = S s (S t x) := by
  rw [S.map_add]
  rfl

omit [CompleteSpace X] in
/-- The semigroup as a function of real time, extended by `id` for `t < 0`. -/
noncomputable def realOperator (S : StronglyContinuousSemigroup X) (t : ℝ) : X →L[ℝ] X :=
  S t.toNNReal

omit [CompleteSpace X] in
@[simp]
lemma realOperator_coe (S : StronglyContinuousSemigroup X) (t : ℝ≥0) :
    S.realOperator t = S t := by
  rw [realOperator, Real.toNNReal_coe]

omit [CompleteSpace X] in
/-- The real-time operator at zero is the identity: `S.realOperator 0 = id`. -/
theorem at_zero (S : StronglyContinuousSemigroup X) :
    S.realOperator 0 = ContinuousLinearMap.id ℝ X := by
  rw [realOperator, Real.toNNReal_zero]
  exact S.map_zero'

omit [CompleteSpace X] in
/-- The real-time shim satisfies the semigroup law at nonnegative real times. -/
theorem semigroup (S : StronglyContinuousSemigroup X) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    S.realOperator (s + t) = (S.realOperator s).comp (S.realOperator t) := by
  rw [realOperator, realOperator, realOperator, Real.toNNReal_add hs ht]
  exact S.map_add' s.toNNReal t.toNNReal

omit [CompleteSpace X] in
/-- Strong continuity at zero of `t ↦ S.realOperator t x` along `0 ≤ t`. -/
theorem strong_cont (S : StronglyContinuousSemigroup X) (x : X) :
    Filter.Tendsto (fun t => S.realOperator t x) (nhdsWithin 0 (Set.Ici 0)) (nhds x) := by
  have h_toNNReal : Filter.Tendsto Real.toNNReal (nhdsWithin 0 (Set.Ici (0 : ℝ))) (nhds 0) := by
    simpa [Real.toNNReal_zero] using
      (continuous_real_toNNReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
        Filter.Tendsto Real.toNNReal (nhdsWithin 0 (Set.Ici (0 : ℝ))) (nhds (Real.toNNReal 0)))
  have h_orbit : Filter.Tendsto (fun t : ℝ≥0 => S.toFun t x) (nhds 0) (nhds x) := by
    have h := (S.continuousAt_zero' x).tendsto
    rw [S.map_zero'] at h
    simpa using h
  exact (h_orbit.comp h_toNNReal).congr' (by
    filter_upwards with t
    simp only [realOperator, Function.comp_apply]
    rfl)

end StronglyContinuousSemigroup

variable (X)

/-- A contraction semigroup: `‖S(t)‖ ≤ 1` for all `t ≥ 0`
([EN] Def. I.5.6, [Linares] Def. 3). Has the growth estimate `M = 1`, `ω = 0`. -/
structure ContractionSemigroup extends StronglyContinuousSemigroup X where
  /-- `‖S(t)‖ ≤ 1` for all `t : ℝ≥0`. -/
  contracting : ∀ t : ℝ≥0, ‖toFun t‖ ≤ 1

variable {X}

/-! ## Basic Properties -/

omit [CompleteSpace X] in
/-- A contraction semigroup is contractive at nonnegative real times. -/
theorem ContractionSemigroup.contracting_real (S : ContractionSemigroup X)
    (t : ℝ) (ht : 0 ≤ t) : ‖S.realOperator t‖ ≤ 1 := by
  have ht_coe : ((t.toNNReal : ℝ) = t) := Real.coe_toNNReal t ht
  rw [← ht_coe, StronglyContinuousSemigroup.realOperator_coe]
  exact S.contracting t.toNNReal

omit [CompleteSpace X] in
/-- `S(t) x` at `t = 0` equals `x`, pointwise version. -/
@[simp]
theorem StronglyContinuousSemigroup.realOperatorZeroApply
    (S : StronglyContinuousSemigroup X) (x : X) :
    S.realOperator 0 x = x := by
  rw [S.at_zero, ContinuousLinearMap.id_apply]

omit [CompleteSpace X] in
/-- Pointwise boundedness on `[0, 1]`, the hypothesis needed for Banach-Steinhaus. -/
private theorem StronglyContinuousSemigroup.pointwiseBoundedOnUnitInterval
    (S : StronglyContinuousSemigroup X) :
    ∀ x : X, ∃ C, ∀ (i : Set.Icc (0 : ℝ) 1),
      ‖(fun j : Set.Icc (0 : ℝ) 1 => S.realOperator j.val) i x‖ ≤ C := by
  intro x
  have hsc := S.strong_cont x
  rw [Metric.tendsto_nhdsWithin_nhds] at hsc
  obtain ⟨δ, hδ_pos, hδ⟩ := hsc 1 one_pos
  have h_near : ∀ t : ℝ, 0 ≤ t → t < δ → ‖S.realOperator t x‖ ≤ ‖x‖ + 1 := by
    intro t ht0 htδ
    have h1 := hδ ht0 (by rwa [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht0])
    rw [dist_eq_norm] at h1
    linarith [norm_le_insert' (S.realOperator t x) x]
  set L := max ‖S.realOperator δ‖ 1
  set B := ‖x‖ + 1
  set N := Nat.ceil (1 / δ)
  have h_claim : ∀ (k : ℕ), ∀ t : ℝ, 0 ≤ t → t < (↑k + 1) * δ →
      ‖S.realOperator t x‖ ≤ L ^ k * B := by
    intro k; induction k with
    | zero =>
      intro t ht0 htδ
      simp only [Nat.cast_zero, zero_add, one_mul] at htδ
      simp only [pow_zero, one_mul]
      exact h_near t ht0 htδ
    | succ k ih =>
      intro t ht0 ht_ub
      by_cases hk : t < (↑k + 1) * δ
      · calc ‖S.realOperator t x‖ ≤ L ^ k * B := ih t ht0 hk
          _ ≤ L ^ (k + 1) * B := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact pow_le_pow_right₀ (le_max_right _ _) (Nat.le_succ k)
      · push Not at hk
        have htd_nn : 0 ≤ t - δ := by
          have : δ ≤ (↑k + 1) * δ :=
            le_mul_of_one_le_left (le_of_lt hδ_pos)
              (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ ↑k); linarith)
          linarith
        have htd_lt : t - δ < (↑k + 1) * δ := by
          push_cast [Nat.succ_eq_add_one] at ht_ub; linarith
        have h_sg := S.semigroup δ (t - δ) (le_of_lt hδ_pos) htd_nn
        have h_delta_add_sub : δ + (t - δ) = t := by ring
        rw [h_delta_add_sub] at h_sg
        calc ‖S.realOperator t x‖
            = ‖S.realOperator δ (S.realOperator (t - δ) x)‖ := by
              simp only [h_sg, ContinuousLinearMap.comp_apply]
          _ ≤ ‖S.realOperator δ‖ * ‖S.realOperator (t - δ) x‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ L * (L ^ k * B) := by
              apply mul_le_mul (le_max_left _ _) (ih _ htd_nn htd_lt)
                (by positivity) (by positivity)
          _ = L ^ (k + 1) * B := by ring
  have hNδ : 1 < (↑N + 1) * δ := by
    have hN : (1 : ℝ) / δ ≤ ↑N := Nat.le_ceil _
    have : 1 ≤ ↑N * δ := by rwa [div_le_iff₀ hδ_pos] at hN
    linarith
  exact ⟨L ^ N * B, fun ⟨t, ht0, ht1⟩ => by
    simp only; exact h_claim N t ht0 (by linarith)⟩

/-- The operator norm of a C₀-semigroup is bounded on `[0, 1]`.

One direction of [EN] Prop. I.5.3: strong continuity implies uniform boundedness
on compact intervals. -/
theorem StronglyContinuousSemigroup.normBoundedOnUnitInterval
    (S : StronglyContinuousSemigroup X) :
    ∃ (M : ℝ), 1 ≤ M ∧
      ∀ (t : ℝ), 0 ≤ t → t ≤ 1 → ‖S.realOperator t‖ ≤ M := by
  obtain ⟨C, hC⟩ := banach_steinhaus S.pointwiseBoundedOnUnitInterval
  exact ⟨max C 1, le_max_right _ _, fun t ht0 ht1 =>
    (hC ⟨t, ht0, ht1⟩).trans (le_max_left _ _)⟩

/-- The operator norm of a C₀-semigroup is bounded on `[0, n]` for any `n : ℕ`. -/
private theorem StronglyContinuousSemigroup.normBoundedOnInterval
    (S : StronglyContinuousSemigroup X) (n : ℕ) :
    ∃ (C : ℝ), 0 < C ∧
      ∀ (t : ℝ), 0 ≤ t → t ≤ n → ‖S.realOperator t‖ ≤ C := by
  -- Induction on `n`: on `(k, k+1]` write `t = (t-k) + k` with `t-k ∈ [0,1]`, so
  -- `S(t) = S(t-k) ∘ S(k)` and `‖S(t)‖ ≤ M · M^k = M^(k+1)`.
  obtain ⟨M, hM1, hMbound⟩ := S.normBoundedOnUnitInterval
  have hM_pos : (0 : ℝ) < M := by linarith
  induction n with
  | zero =>
    refine ⟨1, one_pos, fun t ht htn => ?_⟩
    simp only [Nat.cast_zero] at htn
    have : t = 0 := le_antisymm htn ht
    rw [this, S.at_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ k ih =>
    obtain ⟨C_k, hC_k_pos, hC_k_bound⟩ := ih
    refine ⟨M * C_k, mul_pos hM_pos hC_k_pos, fun t ht htn => ?_⟩
    by_cases hk : t ≤ ↑k
    · calc ‖S.realOperator t‖ ≤ C_k := hC_k_bound t ht hk
        _ ≤ M * C_k := le_mul_of_one_le_left (le_of_lt hC_k_pos) hM1
    · -- t ∈ (k, k+1], decompose: t = (t - k) + k
      push Not at hk
      have htk_nn : 0 ≤ t - ↑k := by linarith
      have htk_le : t - ↑k ≤ 1 := by
        push_cast [Nat.succ_eq_add_one] at htn; linarith
      have hk_nn : (0 : ℝ) ≤ ↑k := Nat.cast_nonneg k
      have h_eq : t = (t - ↑k) + ↑k := by ring
      have h_sg := S.semigroup (t - ↑k) ↑k htk_nn hk_nn
      rw [← h_eq] at h_sg
      rw [h_sg]
      calc ‖(S.realOperator (t - ↑k)).comp (S.realOperator ↑k)‖
          ≤ ‖S.realOperator (t - ↑k)‖ * ‖S.realOperator ↑k‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ M * C_k :=
            mul_le_mul (hMbound _ htk_nn htk_le) (hC_k_bound ↑k hk_nn le_rfl)
              (norm_nonneg _) (le_of_lt hM_pos)

private theorem StronglyContinuousSemigroup.strongContWithinAt_left
    (S : StronglyContinuousSemigroup X) (x : X) (t₀ : ℝ) (_ht₀ : 0 ≤ t₀) :
    Filter.Tendsto (fun t => S.realOperator t x)
      (nhdsWithin t₀ (Set.Icc 0 t₀)) (nhds (S.realOperator t₀ x)) := by
  have h_norm_bound : ∃ C > 0,
      ∀ t : ℝ, 0 ≤ t → t ≤ t₀ → ‖S.realOperator t‖ ≤ C := by
    obtain ⟨C, hC, hCb⟩ := S.normBoundedOnInterval (Nat.ceil t₀)
    exact ⟨C, hC, fun t ht ht' => hCb t ht (ht'.trans (Nat.le_ceil t₀))⟩
  obtain ⟨C, hC_pos, hC_bound⟩ := h_norm_bound
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have h_sc := S.strong_cont x
  rw [Metric.tendsto_nhdsWithin_nhds] at h_sc
  obtain ⟨δ, hδ_pos, hδ_spec⟩ := h_sc (ε / C) (div_pos hε hC_pos)
  refine ⟨δ, hδ_pos, fun t ht_mem ht_dist => ?_⟩
  simp only [Set.mem_Icc] at ht_mem
  have ht₀t_nn : 0 ≤ t₀ - t := by linarith [ht_mem.2]
  have h_sg_eq : S.realOperator t₀ = (S.realOperator t).comp (S.realOperator (t₀ - t)) := by
    have := S.semigroup t (t₀ - t) ht_mem.1 ht₀t_nn
    rwa [add_sub_cancel] at this
  have h_diff : S.realOperator t x - S.realOperator t₀ x =
      S.realOperator t (x - S.realOperator (t₀ - t) x) := by
    conv_rhs => rw [map_sub]
    congr 1
    rw [h_sg_eq, ContinuousLinearMap.comp_apply]
  rw [dist_eq_norm, h_diff]
  calc ‖S.realOperator t (x - S.realOperator (t₀ - t) x)‖
      ≤ ‖S.realOperator t‖ * ‖x - S.realOperator (t₀ - t) x‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * ‖x - S.realOperator (t₀ - t) x‖ :=
        mul_le_mul_of_nonneg_right (hC_bound t ht_mem.1 ht_mem.2) (norm_nonneg _)
    _ = C * dist (S.realOperator (t₀ - t) x) x := by
        rw [dist_eq_norm, ← norm_neg, neg_sub]
    _ < C * (ε / C) := by
        apply mul_lt_mul_of_pos_left _ hC_pos
        apply hδ_spec ht₀t_nn
        simp only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht₀t_nn]
        rw [Real.dist_eq, abs_sub_comm] at ht_dist
        rwa [abs_of_nonneg ht₀t_nn] at ht_dist
    _ = ε := mul_div_cancel₀ ε (ne_of_gt hC_pos)

omit [CompleteSpace X] in
private theorem StronglyContinuousSemigroup.strongContWithinAt_right
    (S : StronglyContinuousSemigroup X) (x : X) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    Filter.Tendsto (fun t => S.realOperator t x)
      (nhdsWithin t₀ (Set.Ici t₀)) (nhds (S.realOperator t₀ x)) := by
  have h_sub_tendsto : Filter.Tendsto (fun t => t - t₀)
      (nhdsWithin t₀ (Set.Ici t₀)) (nhdsWithin 0 (Set.Ici 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Filter.Tendsto (fun t => t - t₀) (nhds t₀) (nhds 0) := by
        have h := Filter.Tendsto.sub_const (Filter.tendsto_id (α := ℝ).mono_left
          (le_refl (nhds t₀))) t₀
        simp only [id, sub_self] at h; exact h
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_Ici] at ht ⊢; linarith
  have h_inner : Filter.Tendsto (fun t => S.realOperator (t - t₀) x)
      (nhdsWithin t₀ (Set.Ici t₀)) (nhds x) :=
    (S.strong_cont x).comp h_sub_tendsto
  have h_outer : Filter.Tendsto (fun t => S.realOperator t₀ (S.realOperator (t - t₀) x))
      (nhdsWithin t₀ (Set.Ici t₀)) (nhds (S.realOperator t₀ x)) :=
    ((S.realOperator t₀).cont.tendsto x).comp h_inner
  apply h_outer.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [Set.mem_Ici] at ht
  have ht_nn : 0 ≤ t - t₀ := by linarith
  have h_sg := S.semigroup t₀ (t - t₀) ht₀ ht_nn
  have h_add_sub_t0 : t₀ + (t - t₀) = t := by ring
  rw [h_add_sub_t0] at h_sg
  rw [h_sg, ContinuousLinearMap.comp_apply]

/-- Strong continuity at every `t₀ ≥ 0`, not just at 0
([EN] Prop. I.5.3, [Linares] Cor. 1).

Strong continuity holds at every `t₀ ≥ 0`, not only at `0`. -/
theorem StronglyContinuousSemigroup.strongContWithinAt
    (S : StronglyContinuousSemigroup X) (x : X) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    Filter.Tendsto (fun t => S.realOperator t x)
      (nhdsWithin t₀ (Set.Ici 0)) (nhds (S.realOperator t₀ x)) := by
  have h_Ici_split : Set.Ici (0 : ℝ) =
      (Set.Ici 0 ∩ Set.Iic t₀) ∪ (Set.Ici 0 ∩ Set.Ici t₀) := by
    rw [← Set.inter_union_distrib_left, Set.Iic_union_Ici, Set.inter_univ]
  rw [h_Ici_split]
  rw [nhdsWithin_union, Filter.tendsto_sup]
  have h_right_set : Set.Ici (0 : ℝ) ∩ Set.Ici t₀ = Set.Ici t₀ := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_Ici]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨le_trans ht₀ h, h⟩⟩
  have h_left_set : Set.Ici (0 : ℝ) ∩ Set.Iic t₀ = Set.Icc 0 t₀ :=
    Set.Ici_inter_Iic
  rw [h_left_set, h_right_set]
  constructor
  · exact S.strongContWithinAt_left x t₀ ht₀
  · exact S.strongContWithinAt_right x t₀ ht₀

end TauCeti.Semigroups

end
