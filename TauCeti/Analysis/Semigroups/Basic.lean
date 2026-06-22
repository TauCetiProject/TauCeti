/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals


/-!
# Strongly continuous semigroups and the Hille–Yosida resolvent

Strongly continuous one-parameter semigroups (C₀-semigroups) on a real Banach space `X`,
their infinitesimal generators with domain, the resolvent as the Laplace transform of
the semigroup, and the resolvent identities of the Hille–Yosida theory.

## Main definitions

* `TauCeti.Semigroups.StronglyContinuousSemigroup`: a family `S t` of bounded operators for
  `t ≥ 0` with `S 0 = id`, `S (s + t) = S s ∘ S t`, and strong continuity at `0`.
* `TauCeti.Semigroups.ContractionSemigroup`: the subclass of contraction semigroups
  (`‖S t‖ ≤ 1`); the growth-bound case `M = 1`, `ω = 0`.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.generator`: the generator `A` as an
  unbounded operator (`LinearPMap`, `X →ₗ.[ℝ] X`) on its domain `D(A)`.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.resolvent`: `R λ x = ∫₀^∞ e^{-λ t} S t x dt`
  (pointwise Bochner integral) for a growth bound `(ω, M)` and `λ > ω`; `ContractionSemigroup`
  gets the `M = 1`, `ω = 0` case.

## Main results

* `StronglyContinuousSemigroup.existsGrowthBound`: `‖S t‖ ≤ M e^{ω t}` for some `M ≥ 1`, `ω`.
* `StronglyContinuousSemigroup.strongContAt`: strong continuity at every `t₀ ≥ 0`.
* `StronglyContinuousSemigroup.resolvent_norm_le`: `‖R λ‖ ≤ M/(λ-ω)` for `λ > ω`; the
  contraction corollary is `‖R λ‖ ≤ 1/λ`.
* `StronglyContinuousSemigroup.resolvent_mem_domain`: `R λ x ∈ D(A)`.
* `StronglyContinuousSemigroup.resolventRightInv`: `(λ - A) R λ = I` on the domain.

## Implementation notes

Ported and adapted (Apache 2.0) from the AI-authored development
[`mrdouglasny/hille-yosida`](https://github.com/mrdouglasny/hille-yosida) (design choices
recorded in that repo's `docs/DESIGN.md`):

* **Generator as `LinearPMap`.** The unbounded generator is `X →ₗ.[ℝ] X`, Mathlib's
  partially-defined-operator type, so it composes with the existing unbounded-operator API
  (graph, closure, adjoint) instead of a bespoke domain + map pair.
* **Time is total `ℝ`, guarded by `t ≥ 0`.** `operator : ℝ → X →L[ℝ] X` is total, with every
  law and the continuity hypothesis quantified over `t ≥ 0`; `S t` for `t < 0` is unconstrained
  and carries no information. This keeps `t` a plain real for the analytic lemmas (integrals
  over `Set.Ioi 0`, the FTC) and avoids an `ℝ≥0 → ℝ` coercion on every estimate. It does not
  affect any stated result, all of which assume `t ≥ 0`. (The alternative, indexing by `ℝ≥0`,
  makes extensional equality on `[0,∞)` automatic at that coercion cost.)
* **Resolvent.** A pointwise `X`-valued Bochner integral (since `t ↦ S t` is only strongly
  continuous, not norm-measurable as an operator-valued map), defined at the general
  growth-bound `(ω, M)` level with the contraction case as a corollary.

The generation theorem (Yosida approximation / Lumer–Phillips) is a separate roadmap
milestone, not in this file.

## References

* [EN] K.-J. Engel, R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  GTM 194, Springer (2000): Ch. I §5, Ch. II §1, Ch. II §3.
* [Linares] F. Linares, *The Hille–Yosida Theorem*, IMPA lecture notes (2021):
  Defs. 1–3, Thm. 1, and eqs. 0.13–0.16 (resolvent construction).
* A. Pazy, *Semigroups of Linear Operators and Applications to PDE*, Springer (1983).
* E. Hille, *Functional Analysis and Semi-Groups* (1948); K. Yosida (1948).
-/

noncomputable section

open scoped Topology NNReal

namespace TauCeti.Semigroups

/-! ## Strongly Continuous Semigroups -/

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]


/-- A strongly continuous one-parameter semigroup (C₀-semigroup) on a Banach space
([EN] Def. I.5.1, [Linares] Def. 1).

`S(t)` is a bounded linear operator for each `t ≥ 0`, satisfying:
1. `S(0) = Id`
2. `S(s + t) = S(s) ∘ S(t)` for all `s, t ≥ 0`
3. `t ↦ S(t) x` is continuous at `t = 0` for each `x : X`

By the semigroup property + continuity at 0, condition 3 is equivalent to
`t ↦ S(t) x` being continuous on all of `[0, ∞)`. -/
structure StronglyContinuousSemigroup where
  /-- The semigroup operator at time `t`. -/
  operator : ℝ → X →L[ℝ] X
  /-- `S(0) = Id` -/
  at_zero : operator 0 = ContinuousLinearMap.id ℝ X
  /-- `S(s + t) = S(s) ∘ S(t)` for `s, t ≥ 0` -/
  semigroup : ∀ (s t : ℝ), 0 ≤ s → 0 ≤ t →
    operator (s + t) = (operator s).comp (operator t)
  /-- Strong continuity: `t ↦ S(t) x` is continuous at 0 for each `x` -/
  strong_cont : ∀ (x : X), Filter.Tendsto
    (fun t => operator t x) (nhdsWithin 0 (Set.Ici 0)) (nhds x)

/-- A contraction semigroup: `‖S(t)‖ ≤ 1` for all `t ≥ 0`
([EN] Def. I.5.6, [Linares] Def. 3). Has the growth estimate `M = 1`, `ω = 0`. -/
structure ContractionSemigroup extends StronglyContinuousSemigroup X where
  /-- `‖S(t)‖ ≤ 1` for all `t ≥ 0`. -/
  contracting : ∀ (t : ℝ), 0 ≤ t → ‖operator t‖ ≤ 1

variable {X}

/-! ## Basic Properties -/

omit [CompleteSpace X] in
/-- `S(t) x` at `t = 0` equals `x`, pointwise version. -/
@[simp]
theorem StronglyContinuousSemigroup.operatorZeroApply
    (S : StronglyContinuousSemigroup X) (x : X) :
    S.operator 0 x = x := by
  rw [S.at_zero, ContinuousLinearMap.id_apply]

/-- The operator norm of a C₀-semigroup is bounded on `[0, 1]`.

One direction of [EN] Prop. I.5.3: strong continuity implies uniform boundedness
on compact intervals. -/
private theorem StronglyContinuousSemigroup.normBoundedOnUnitInterval
    (S : StronglyContinuousSemigroup X) :
    ∃ (M : ℝ), 1 ≤ M ∧ ∀ (t : ℝ), 0 ≤ t → t ≤ 1 → ‖S.operator t‖ ≤ M := by
  -- Banach–Steinhaus (uniform boundedness) on `{S(t) : t ∈ [0,1]}`, using strong
  -- continuity at 0 and the semigroup property for the pointwise bounds.
  -- Step 1: For each x, the orbit {S(t)x : t ∈ [0, 1]} is pointwise bounded.
  have h_ptwise : ∀ x : X, ∃ C, ∀ (i : Set.Icc (0 : ℝ) 1),
      ‖(fun j : Set.Icc (0 : ℝ) 1 => S.operator j.val) i x‖ ≤ C := by
    intro x
    -- By strong continuity at 0: S(t)x → x, so ‖S(t)x‖ bounded near 0
    have hsc := S.strong_cont x
    rw [Metric.tendsto_nhdsWithin_nhds] at hsc
    obtain ⟨δ, hδ_pos, hδ⟩ := hsc 1 one_pos
    -- ‖S(t)x‖ ≤ ‖x‖ + 1 for t ∈ [0, δ)
    have h_near : ∀ t : ℝ, 0 ≤ t → t < δ → ‖S.operator t x‖ ≤ ‖x‖ + 1 := by
      intro t ht0 htδ
      have h1 := hδ ht0 (by rwa [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht0])
      rw [dist_eq_norm] at h1
      linarith [norm_le_insert' (S.operator t x) x]
    -- Extend to [0, 1] using semigroup property and operator norm of S(δ)
    set L := max ‖S.operator δ‖ 1
    set B := ‖x‖ + 1
    set N := Nat.ceil (1 / δ)
    -- Claim: ∀ k, t ∈ [0, (k+1)δ) → ‖S(t)x‖ ≤ L^k * B
    have h_claim : ∀ (k : ℕ), ∀ t : ℝ, 0 ≤ t → t < (↑k + 1) * δ →
        ‖S.operator t x‖ ≤ L ^ k * B := by
      intro k; induction k with
      | zero =>
        intro t ht0 htδ
        simp only [Nat.cast_zero, zero_add, one_mul] at htδ
        simp only [pow_zero, one_mul]
        exact h_near t ht0 htδ
      | succ k ih =>
        intro t ht0 ht_ub
        by_cases hk : t < (↑k + 1) * δ
        · -- Earlier interval: use IH + L ≥ 1
          calc ‖S.operator t x‖ ≤ L ^ k * B := ih t ht0 hk
            _ ≤ L ^ (k + 1) * B := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                exact pow_le_pow_right₀ (le_max_right _ _) (Nat.le_succ k)
        · -- New interval: S(t)x = S(δ)(S(t-δ)x)
          push Not at hk
          have htd_nn : 0 ≤ t - δ := by
            have : δ ≤ (↑k + 1) * δ :=
              le_mul_of_one_le_left (le_of_lt hδ_pos)
                (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ ↑k); linarith)
            linarith
          have htd_lt : t - δ < (↑k + 1) * δ := by
            push_cast [Nat.succ_eq_add_one] at ht_ub; linarith
          have h_sg := S.semigroup δ (t - δ) (le_of_lt hδ_pos) htd_nn
          rw [show δ + (t - δ) = t from by ring] at h_sg
          calc ‖S.operator t x‖
              = ‖S.operator δ (S.operator (t - δ) x)‖ := by
                simp only [h_sg, ContinuousLinearMap.comp_apply]
            _ ≤ ‖S.operator δ‖ * ‖S.operator (t - δ) x‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ ≤ L * (L ^ k * B) := by
                apply mul_le_mul (le_max_left _ _) (ih _ htd_nn htd_lt)
                  (by positivity) (by positivity)
            _ = L ^ (k + 1) * B := by ring
    -- For t ∈ [0, 1]: use claim with k = N, since 1 < (N+1)δ
    have hNδ : 1 < (↑N + 1) * δ := by
      have hN : (1 : ℝ) / δ ≤ ↑N := Nat.le_ceil _
      have : 1 ≤ ↑N * δ := by rwa [div_le_iff₀ hδ_pos] at hN
      linarith
    exact ⟨L ^ N * B, fun ⟨t, ht0, ht1⟩ => by
      simp only; exact h_claim N t ht0 (by linarith)⟩
  -- Step 2: Apply Banach-Steinhaus for uniform bound
  obtain ⟨C, hC⟩ := banach_steinhaus h_ptwise
  exact ⟨max C 1, le_max_right _ _, fun t ht0 ht1 =>
    (hC ⟨t, ht0, ht1⟩).trans (le_max_left _ _)⟩

/-- The operator norm of a C₀-semigroup is bounded on `[0, n]` for any `n : ℕ`. -/
private theorem StronglyContinuousSemigroup.normBoundedOnInterval
    (S : StronglyContinuousSemigroup X) (n : ℕ) :
    ∃ (C : ℝ), 0 < C ∧ ∀ (t : ℝ), 0 ≤ t → t ≤ n → ‖S.operator t‖ ≤ C := by
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
    · calc ‖S.operator t‖ ≤ C_k := hC_k_bound t ht hk
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
      calc ‖(S.operator (t - ↑k)).comp (S.operator ↑k)‖
          ≤ ‖S.operator (t - ↑k)‖ * ‖S.operator ↑k‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ M * C_k :=
            mul_le_mul (hMbound _ htk_nn htk_le) (hC_k_bound ↑k hk_nn le_rfl)
              (norm_nonneg _) (le_of_lt hM_pos)

/-- Strong continuity at every `t₀ ≥ 0`, not just at 0
([EN] Prop. I.5.3, [Linares] Cor. 1).

Strong continuity holds at every `t₀ ≥ 0`, not only at `0`. -/
theorem StronglyContinuousSemigroup.strongContAt
    (S : StronglyContinuousSemigroup X) (x : X) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    Filter.Tendsto (fun t => S.operator t x)
      (nhdsWithin t₀ (Set.Ici 0)) (nhds (S.operator t₀ x)) := by
  -- Decompose nhdsWithin t₀ (Ici 0) using Iic/Ici splitting at t₀.
  -- nhdsWithin t₀ (Ici 0) = nhdsWithin t₀ (Ici 0 ∩ Iic t₀) ⊔ nhdsWithin t₀ (Ici 0 ∩ Ici t₀)
  rw [show Set.Ici (0 : ℝ) = (Set.Ici 0 ∩ Set.Iic t₀) ∪ (Set.Ici 0 ∩ Set.Ici t₀) from by
    rw [← Set.inter_union_distrib_left, Set.Iic_union_Ici, Set.inter_univ]]
  rw [nhdsWithin_union, Filter.tendsto_sup]
  -- Simplify the intersection sets
  have h_right_set : Set.Ici (0 : ℝ) ∩ Set.Ici t₀ = Set.Ici t₀ := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_Ici]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨le_trans ht₀ h, h⟩⟩
  have h_left_set : Set.Ici (0 : ℝ) ∩ Set.Iic t₀ = Set.Icc 0 t₀ :=
    Set.Ici_inter_Iic
  rw [h_left_set, h_right_set]
  constructor
  · -- Left continuity: nhdsWithin t₀ (Icc 0 t₀)
    -- For 0 ≤ t ≤ t₀: S(t₀)x = S(t)(S(t₀-t)x), so
    -- S(t)x - S(t₀)x = S(t)(x - S(t₀-t)x).
    -- ‖S(t)(x - S(t₀-t)x)‖ ≤ ‖S(t)‖·‖x - S(t₀-t)x‖ → 0
    -- since ‖S(t)‖ is bounded on [0, t₀] and ‖S(t₀-t)x - x‖ → 0.
    -- The operator norm bound on [0, t₀] follows from normBoundedOnUnitInterval
    -- (itself proved via the uniform boundedness principle) + the semigroup property.
    -- We state this bound as a local fact.
    have h_norm_bound : ∃ C > 0, ∀ t : ℝ, 0 ≤ t → t ≤ t₀ → ‖S.operator t‖ ≤ C := by
      obtain ⟨C, hC, hCb⟩ := S.normBoundedOnInterval (Nat.ceil t₀)
      exact ⟨C, hC, fun t ht ht' => hCb t ht (ht'.trans (Nat.le_ceil t₀))⟩
    obtain ⟨C, hC_pos, hC_bound⟩ := h_norm_bound
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    -- Extract δ from strong_cont: for h ∈ [0, δ), ‖S(h)x - x‖ < ε/C
    have h_sc := S.strong_cont x
    rw [Metric.tendsto_nhdsWithin_nhds] at h_sc
    obtain ⟨δ, hδ_pos, hδ_spec⟩ := h_sc (ε / C) (div_pos hε hC_pos)
    refine ⟨δ, hδ_pos, fun t ht_mem ht_dist => ?_⟩
    simp only [Set.mem_Icc] at ht_mem
    -- Key: S(t₀)x = S(t)(S(t₀ - t)x) by semigroup
    have ht₀t_nn : 0 ≤ t₀ - t := by linarith [ht_mem.2]
    have h_sg_eq : S.operator t₀ = (S.operator t).comp (S.operator (t₀ - t)) := by
      have := S.semigroup t (t₀ - t) ht_mem.1 ht₀t_nn
      rwa [add_sub_cancel] at this
    -- S(t)x - S(t₀)x = S(t)(x - S(t₀-t)x)
    have h_diff : S.operator t x - S.operator t₀ x =
        S.operator t (x - S.operator (t₀ - t) x) := by
      conv_rhs => rw [map_sub]
      congr 1
      rw [h_sg_eq, ContinuousLinearMap.comp_apply]
    rw [dist_eq_norm, h_diff]
    calc ‖S.operator t (x - S.operator (t₀ - t) x)‖
        ≤ ‖S.operator t‖ * ‖x - S.operator (t₀ - t) x‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * ‖x - S.operator (t₀ - t) x‖ :=
          mul_le_mul_of_nonneg_right (hC_bound t ht_mem.1 ht_mem.2) (norm_nonneg _)
      _ = C * dist (S.operator (t₀ - t) x) x := by
          rw [dist_eq_norm, ← norm_neg, neg_sub]
      _ < C * (ε / C) := by
          apply mul_lt_mul_of_pos_left _ hC_pos
          apply hδ_spec ht₀t_nn
          simp only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht₀t_nn]
          rw [Real.dist_eq, abs_sub_comm] at ht_dist
          rwa [abs_of_nonneg ht₀t_nn] at ht_dist
      _ = ε := mul_div_cancel₀ ε (ne_of_gt hC_pos)
  · -- Right continuity: nhdsWithin t₀ (Ici t₀)
    -- For t ≥ t₀: S(t)x = S(t₀)(S(t - t₀)x) and S(t-t₀)x → x by strong_cont.
    -- S(t₀) is a CLM, hence continuous, so S(t₀)(S(t-t₀)x) → S(t₀)x.
    -- The map t ↦ t - t₀ sends nhdsWithin t₀ (Ici t₀) to nhdsWithin 0 (Ici 0)
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
    -- So S(t - t₀)x → x
    have h_inner : Filter.Tendsto (fun t => S.operator (t - t₀) x)
        (nhdsWithin t₀ (Set.Ici t₀)) (nhds x) := (S.strong_cont x).comp h_sub_tendsto
    -- And S(t₀)(S(t - t₀)x) → S(t₀)x by continuity of the CLM S(t₀)
    have h_outer : Filter.Tendsto (fun t => S.operator t₀ (S.operator (t - t₀) x))
        (nhdsWithin t₀ (Set.Ici t₀)) (nhds (S.operator t₀ x)) :=
      ((S.operator t₀).cont.tendsto x).comp h_inner
    -- It suffices to show S(t)x = S(t₀)(S(t - t₀)x) for t ≥ t₀
    apply h_outer.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Set.mem_Ici] at ht
    have ht_nn : 0 ≤ t - t₀ := by linarith
    -- S(t₀ + (t - t₀)) = S(t₀) ∘ S(t - t₀) by semigroup, and t₀ + (t - t₀) = t
    have h_sg := S.semigroup t₀ (t - t₀) ht₀ ht_nn
    rw [show t₀ + (t - t₀) = t from by ring] at h_sg
    rw [h_sg, ContinuousLinearMap.comp_apply]

/-! ## The Infinitesimal Generator -/

/-- The generator difference quotient `(S t x - x)/t`; its `t → 0⁺` limit (when it
exists) is the generator value at `x`. -/
private def StronglyContinuousSemigroup.genQuot (S : StronglyContinuousSemigroup X)
    (x : X) (t : ℝ) : X := (1 / t) • (S.operator t x - x)

/-- Membership predicate for the generator's domain: the difference quotient
`(S t x - x)/t` converges as `t → 0⁺` ([EN] Def. II.1.2, [Linares] Def. 2).
Equivalently `x ∈ S.domain`; the generator itself is the `LinearPMap`
`StronglyContinuousSemigroup.generator`. -/
def StronglyContinuousSemigroup.IsInGeneratorDomain (S : StronglyContinuousSemigroup X)
    (x : X) : Prop :=
  ∃ Ax : X, Filter.Tendsto (S.genQuot x) (nhdsWithin 0 (Set.Ioi 0)) (nhds Ax)

omit [CompleteSpace X] in
/-- The generator difference quotient is additive in the limit. -/
private theorem StronglyContinuousSemigroup.genQuot_tendsto_add
    (S : StronglyContinuousSemigroup X) {x y Ax Ay : X}
    (hx : Filter.Tendsto (S.genQuot x) (nhdsWithin 0 (Set.Ioi 0)) (nhds Ax))
    (hy : Filter.Tendsto (S.genQuot y) (nhdsWithin 0 (Set.Ioi 0)) (nhds Ay)) :
    Filter.Tendsto (S.genQuot (x + y)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (Ax + Ay)) := by
  have heq : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      S.genQuot (x + y) t = S.genQuot x t + S.genQuot y t := by
    filter_upwards with t
    simp only [StronglyContinuousSemigroup.genQuot]
    rw [map_add, add_sub_add_comm, smul_add]
  exact (hx.add hy).congr' (heq.mono (fun _ h => h.symm))

omit [CompleteSpace X] in
/-- The generator difference quotient is `ℝ`-homogeneous in the limit. -/
private theorem StronglyContinuousSemigroup.genQuot_tendsto_smul
    (S : StronglyContinuousSemigroup X) (c : ℝ) {x Ax : X}
    (hx : Filter.Tendsto (S.genQuot x) (nhdsWithin 0 (Set.Ioi 0)) (nhds Ax)) :
    Filter.Tendsto (S.genQuot (c • x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (c • Ax)) := by
  have heq : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      S.genQuot (c • x) t = c • S.genQuot x t := by
    filter_upwards with t
    simp only [StronglyContinuousSemigroup.genQuot, map_smul, smul_sub, smul_comm c (1 / t)]
  exact (hx.const_smul c).congr' (heq.mono (fun _ h => h.symm))

/-- The domain `D(A)` of the generator, as a `ℝ`-submodule of `X`. -/
def StronglyContinuousSemigroup.domain (S : StronglyContinuousSemigroup X) :
    Submodule ℝ X where
  carrier := { x | S.IsInGeneratorDomain x }
  add_mem' := by
    rintro x y ⟨Ax, hAx⟩ ⟨Ay, hAy⟩
    exact ⟨Ax + Ay, S.genQuot_tendsto_add hAx hAy⟩
  zero_mem' := by
    refine ⟨0, ?_⟩
    have h0 : S.genQuot (0 : X) = fun _ => (0 : X) := by
      ext t; simp [StronglyContinuousSemigroup.genQuot]
    rw [h0]; exact tendsto_const_nhds
  smul_mem' := by
    rintro c x ⟨Ax, hAx⟩
    exact ⟨c • Ax, S.genQuot_tendsto_smul c hAx⟩

/-- The underlying linear map of the generator, on its domain submodule.
Implementation detail of `generator`; not part of the public API. -/
private noncomputable def StronglyContinuousSemigroup.genMap
    (S : StronglyContinuousSemigroup X) : S.domain →ₗ[ℝ] X where
  toFun := fun x => Classical.choose x.property
  map_add' := fun x y =>
    tendsto_nhds_unique (Classical.choose_spec (x + y).property)
      (S.genQuot_tendsto_add (Classical.choose_spec x.property)
        (Classical.choose_spec y.property))
  map_smul' := fun c x =>
    tendsto_nhds_unique (Classical.choose_spec (c • x).property)
      (S.genQuot_tendsto_smul c (Classical.choose_spec x.property))

/-- The infinitesimal generator `A` as an unbounded operator (`LinearPMap`),
`A x = lim_{t→0⁺} (S t x - x)/t` on the domain `D(A)` where the limit exists
([EN] Def. II.1.2). Modelled as `X →ₗ.[ℝ] X` so it composes with Mathlib's
unbounded-operator API. -/
noncomputable def StronglyContinuousSemigroup.generator
    (S : StronglyContinuousSemigroup X) : X →ₗ.[ℝ] X where
  domain := S.domain
  toFun := S.genMap

omit [CompleteSpace X] in
/-- Domain membership unfolds to the generator-domain predicate. -/
@[simp] theorem StronglyContinuousSemigroup.mem_domain_iff
    (S : StronglyContinuousSemigroup X) (x : X) :
    x ∈ S.domain ↔ S.IsInGeneratorDomain x := Iff.rfl

omit [CompleteSpace X] in
/-- `S.generator.domain` is the generator domain submodule. -/
@[simp] theorem StronglyContinuousSemigroup.generator_domain
    (S : StronglyContinuousSemigroup X) : S.generator.domain = S.domain := rfl

omit [CompleteSpace X] in
/-- A vector lies in the generator domain iff its difference quotient `(S t x - x)/t`
converges as `t → 0⁺` ([EN] Def. II.1.2). -/
theorem StronglyContinuousSemigroup.mem_domain_iff_tendsto
    (S : StronglyContinuousSemigroup X) (x : X) :
    x ∈ S.domain ↔ ∃ y, Filter.Tendsto (fun t => (1 / t) • (S.operator t x - x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds y) :=
  Iff.rfl

omit [CompleteSpace X] in
/-- Characteristic property of the generator: for `x` in the domain, the difference
quotient `(S t x - x)/t` converges to `S.generator x` as `t → 0⁺` ([EN] Def. II.1.2). -/
theorem StronglyContinuousSemigroup.generator_tendsto
    (S : StronglyContinuousSemigroup X) (x : S.domain) :
    Filter.Tendsto (fun t => (1 / t) • (S.operator t (x : X) - (x : X)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (S.generator x)) :=
  Classical.choose_spec x.property

omit [CompleteSpace X] in
/-- Eliminator for the generator: if the difference quotient `(S t x - x)/t` of an
`x ∈ D(A)` converges to `y`, then `A x = y` (by uniqueness of limits). -/
theorem StronglyContinuousSemigroup.generator_eq_of_tendsto
    (S : StronglyContinuousSemigroup X) {x : X} (hx : x ∈ S.domain) {y : X}
    (h : Filter.Tendsto (fun t => (1 / t) • (S.operator t x - x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds y)) :
    S.generator ⟨x, hx⟩ = y :=
  tendsto_nhds_unique (S.generator_tendsto ⟨x, hx⟩) h

/-! ## Exponential growth bounds -/

/-- A C₀-semigroup has exponential growth bound `(ω, M)`: `‖S t‖ ≤ M e^{ω t}` for `t ≥ 0`,
with `M ≥ 1` ([EN] eq. I.(5.1)). The infimal admissible `ω` is the growth bound `ω₀`. -/
def StronglyContinuousSemigroup.HasGrowthBound
    (S : StronglyContinuousSemigroup X) (ω : ℝ) (M : ℝ) : Prop :=
  1 ≤ M ∧ ∀ (t : ℝ), 0 ≤ t → ‖S.operator t‖ ≤ M * Real.exp (ω * t)

omit [CompleteSpace X] in
/-- A contraction semigroup has growth bound `(0, 1)`. -/
theorem ContractionSemigroup.hasGrowthBound (S : ContractionSemigroup X) :
    S.toStronglyContinuousSemigroup.HasGrowthBound 0 1 :=
  ⟨le_rfl, fun t ht => by simpa using S.contracting t ht⟩

/-! ## The Resolvent (for Contraction Semigroups) -/

open MeasureTheory

omit [CompleteSpace X] in
/-- The growth-bound estimate for the Laplace-transform integrand:
`‖e^{-λt} S(t) x‖ ≤ M ‖x‖ e^{-(λ-ω)t}` for `t > 0`. Shared by the integrability of the
integrand and the norm bound on the resolvent. -/
private lemma StronglyContinuousSemigroup.norm_resolvent_integrand_le
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M)
    (lambda : ℝ) (x : X) {t : ℝ} (ht : 0 < t) :
    ‖Real.exp (-(lambda * t)) • S.operator t x‖ ≤ M * ‖x‖ * Real.exp (-(lambda - ω) * t) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-(lambda * t)) * ‖(S.operator t) x‖
      ≤ Real.exp (-(lambda * t)) * (M * Real.exp (ω * t) * ‖x‖) := by
        gcongr
        exact le_trans (ContinuousLinearMap.le_opNorm _ _)
          (by gcongr; exact hb.2 t ht.le)
    _ = M * ‖x‖ * Real.exp (-(lambda - ω) * t) := by
        rw [show -(lambda - ω) * t = -(lambda * t) + ω * t from by ring, Real.exp_add]
        ring

/-- The Laplace-transform integrand `e^{-λt} S(t) x` is integrable on `(0, ∞)` whenever
`ω < λ`: by the growth bound `‖e^{-λt} S(t) x‖ ≤ M ‖x‖ e^{-(λ-ω)t}`, which is integrable. -/
lemma StronglyContinuousSemigroup.integrable_resolvent_integrand
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M)
    (lambda : ℝ) (hlam : ω < lambda) (x : X) :
    IntegrableOn (fun t => Real.exp (-(lambda * t)) • S.operator t x) (Set.Ioi 0) := by
  have hpos : 0 < lambda - ω := by linarith
  unfold MeasureTheory.IntegrableOn
  apply MeasureTheory.Integrable.mono'
    ((exp_neg_integrableOn_Ioi 0 hpos).smul (M * ‖x‖))
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply ContinuousOn.smul
    · exact (Real.continuous_exp.comp
        ((continuous_const.mul continuous_id).neg)).continuousOn
    · have h_cont : ContinuousOn (fun t => S.operator t x) (Set.Ici 0) :=
        fun t₀ ht₀ => S.strongContAt x t₀ ht₀
      exact h_cont.mono Set.Ioi_subset_Ici_self
  · apply (ae_restrict_mem measurableSet_Ioi).mono
    intro t (ht : 0 < t)
    simpa only [Pi.smul_apply, smul_eq_mul] using S.norm_resolvent_integrand_le hb lambda x ht

/-- The resolvent `R(λ) x = ∫₀^∞ e^{-λt} S(t)x dt` of a C₀-semigroup with growth bound
`(ω, M)`, for `λ > ω`. A pointwise `X`-valued Bochner integral (so it is well-defined for
the merely strongly continuous `t ↦ S t`), with built-in norm bound `‖R λ‖ ≤ M/(λ-ω)`. -/
noncomputable def StronglyContinuousSemigroup.resolvent
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M)
    (lambda : ℝ) (hlam : ω < lambda) : X →L[ℝ] X :=
  LinearMap.mkContinuous
    { toFun := fun x =>
        ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(lambda * t)) • S.operator t x
      map_add' := fun x y => by
        simp only [map_add, smul_add]
        exact integral_add
          (S.integrable_resolvent_integrand hb lambda hlam x)
          (S.integrable_resolvent_integrand hb lambda hlam y)
      map_smul' := fun c x => by
        simp only [RingHom.id_apply, map_smul]
        have h : ∀ t : ℝ, Real.exp (-(lambda * t)) • c • (S.operator t) x =
            c • (Real.exp (-(lambda * t)) • (S.operator t) x) :=
          fun t => smul_comm _ c _
        simp_rw [h]
        exact integral_smul (μ := volume.restrict (Set.Ioi (0 : ℝ))) c
          (fun t => Real.exp (-(lambda * t)) • (S.operator t) x) }
    (M / (lambda - ω))
    (by
      have hpos : 0 < lambda - ω := by linarith
      intro x; simp only [LinearMap.coe_mk, AddHom.coe_mk]
      calc ‖∫ t in Set.Ioi 0, Real.exp (-(lambda * t)) • (S.operator t) x‖
          ≤ ∫ t in Set.Ioi 0, M * ‖x‖ * Real.exp (-(lambda - ω) * t) := by
            apply MeasureTheory.norm_integral_le_of_norm_le
            · exact (exp_neg_integrableOn_Ioi 0 hpos).integrable.const_mul (M * ‖x‖)
            · apply (ae_restrict_mem measurableSet_Ioi).mono
              intro t (ht : 0 < t)
              exact S.norm_resolvent_integrand_le hb lambda x ht
        _ = M / (lambda - ω) * ‖x‖ := by
            rw [show (fun t => M * ‖x‖ * Real.exp (-(lambda - ω) * t)) =
                (fun t => (M * ‖x‖) • Real.exp (-(lambda - ω) * t)) from by
                  ext t; simp [smul_eq_mul]]
            rw [integral_smul (μ := volume.restrict (Set.Ioi (0 : ℝ)))]
            have h_eval : ∫ t in Set.Ioi 0, Real.exp (-(lambda - ω) * t) = (lambda - ω)⁻¹ := by
              have h := integral_comp_mul_left_Ioi (fun t => Real.exp (-t)) 0 hpos
              simp only [mul_zero] at h
              simp only [neg_mul]
              rw [h, integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one]
            rw [smul_eq_mul, h_eval, div_eq_mul_inv]; ring)

/-- The resolvent in integral form (characteristic lemma). -/
theorem StronglyContinuousSemigroup.resolvent_apply
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M)
    (lambda : ℝ) (hlam : ω < lambda) (x : X) :
    S.resolvent hb lambda hlam x
      = ∫ t in Set.Ioi 0, Real.exp (-(lambda * t)) • S.operator t x := rfl

/-! ## Resolvent-Generator Interface

The proofs of `resolvent_mem_domain` and `resolventRightInv` use the integral
shift trick from [EN] Thm. II.1.10(i) / [Linares] eq. 0.15. We first establish
helper lemmas for the key computation. -/

omit [CompleteSpace X] in
/-- Translation of set integral: `∫_{Ioi 0} f(t + h) = ∫_{Ioi h} f(u)`.
Follows from translation invariance of Lebesgue measure. -/
private lemma integral_comp_add_right_Ioi (f : ℝ → X) (h : ℝ) :
    ∫ t in Set.Ioi 0, f (t + h) = ∫ u in Set.Ioi h, f u := by
  -- Express set integrals as full integrals with indicators
  simp_rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
  -- Key: indicator_{Ioi 0}(fun t => f(t+h))(t) = indicator_{Ioi h}(f)(t+h)
  have key : ∀ t, Set.indicator (Set.Ioi 0) (fun t => f (t + h)) t =
      Set.indicator (Set.Ioi h) f (t + h) := by
    intro t; simp only [Set.indicator, Set.mem_Ioi]
    split_ifs with h1 h2 h2 <;> [rfl; linarith; linarith; rfl]
  simp_rw [key]
  -- Apply translation invariance of Lebesgue measure
  exact MeasureTheory.integral_add_right_eq_self _ h

omit [CompleteSpace X] in
/-- Splitting `∫_{Ioi 0} = ∫_{Ioc 0 h} + ∫_{Ioi h}` for `h > 0`. -/
private lemma integral_Ioi_eq_Ioc_add_Ioi (f : ℝ → X) {h : ℝ} (hh : 0 < h)
    (hf : IntegrableOn f (Set.Ioi 0) volume) :
    ∫ t in Set.Ioi 0, f t = (∫ t in Set.Ioc 0 h, f t) + ∫ t in Set.Ioi h, f t := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (le_of_lt hh)]
  have hd : Disjoint (Set.Ioc 0 h) (Set.Ioi h) :=
    Set.disjoint_left.mpr (fun _ ht1 ht2 => not_le.mpr ht2 ht1.2)
  exact MeasureTheory.setIntegral_union hd measurableSet_Ioi
    (hf.mono_set Set.Ioc_subset_Ioi_self)
    (hf.mono_set (Set.Ioi_subset_Ioi (le_of_lt hh)))

/-- The integral shift identity ([EN] Thm. II.1.10(i), [Linares] eq. 0.15):
`S(h)(R(λ)x) - R(λ)x = (e^{λh} - 1) • R(λ)x - e^{λh} • ∫_{(0,h]} e^{-λu} S(u)x du`, for `h > 0`. -/
private theorem StronglyContinuousSemigroup.resolvent_shift_identity
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M)
    (lambda : ℝ) (hlam : ω < lambda) (x : X) {h : ℝ} (hh : 0 < h) :
    S.operator h (S.resolvent hb lambda hlam x) - S.resolvent hb lambda hlam x =
      (Real.exp (lambda * h) - 1) • S.resolvent hb lambda hlam x -
      Real.exp (lambda * h) • ∫ u in Set.Ioc 0 h, Real.exp (-(lambda * u)) • S.operator u x := by
  set Rlx := S.resolvent hb lambda hlam x
  set f := fun t => Real.exp (-(lambda * t)) • S.operator t x
  -- Step 1: push `S(h)` inside the integral via the semigroup property
  have h_push : S.operator h Rlx = Real.exp (lambda * h) • ∫ u in Set.Ioi h, f u := by
    have hRlx : Rlx = ∫ t in Set.Ioi 0, f t := S.resolvent_apply hb lambda hlam x
    rw [hRlx, ← ContinuousLinearMap.integral_comp_comm _
      (S.integrable_resolvent_integrand hb lambda hlam x)]
    have h_eq : ∀ t ∈ Set.Ioi (0 : ℝ),
        (S.operator h) (f t) = Real.exp (lambda * h) • f (t + h) := by
      intro t ht
      simp only [f, ContinuousLinearMap.map_smul]
      rw [← ContinuousLinearMap.comp_apply,
          ← S.semigroup h t (le_of_lt hh) (le_of_lt (Set.mem_Ioi.mp ht)),
          show h + t = t + h from add_comm h t]
      symm; rw [← mul_smul, ← Real.exp_add]; congr 1; ring
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h_eq]
    rw [integral_smul (μ := volume.restrict (Set.Ioi (0 : ℝ)))]
    congr 1
    exact integral_comp_add_right_Ioi f h
  -- Step 2: split `∫_{Ioi h} = Rlx - ∫_{Ioc 0 h} f`
  have h_split : ∫ u in Set.Ioi h, f u = Rlx - ∫ u in Set.Ioc 0 h, f u := by
    have hsplit := integral_Ioi_eq_Ioc_add_Ioi f hh
      (S.integrable_resolvent_integrand hb lambda hlam x)
    have hRlx : Rlx = ∫ t in Set.Ioi 0, f t := S.resolvent_apply hb lambda hlam x
    rw [hRlx, hsplit]; abel
  -- Step 3: combine into the key identity
  rw [h_push, h_split]
  simp only [smul_sub, sub_smul, one_smul]
  abel

/-- The integral average `(1/t) • ∫_{(0,t]} e^{-λu} S(u)x du` tends to `x` as `t → 0⁺`: the
integrand `e^{-λu} S(u)x` is continuous at `0` with value `x` (strong continuity), so the
fundamental theorem of calculus gives the Cesàro limit. -/
private theorem StronglyContinuousSemigroup.tendsto_average_resolvent_integrand
    (S : StronglyContinuousSemigroup X) (lambda : ℝ) (x : X) :
    Filter.Tendsto
      (fun t => (1 / t) • ∫ u in Set.Ioc 0 t, Real.exp (-(lambda * u)) • S.operator u x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds x) := by
  set f := fun t => Real.exp (-(lambda * t)) • S.operator t x
  -- Modify `f` for `t < 0` so the FTC sees two-sided continuity at `0`
  set g : ℝ → X := fun t => if 0 ≤ t then f t else x with hg_def
  -- `g` is continuous at `0` (right: strong continuity; left: constant `x`)
  have hg_cont : Filter.Tendsto g (nhds 0) (nhds x) := by
    rw [← nhdsLT_sup_nhdsGE (0 : ℝ)]
    apply Filter.Tendsto.sup
    · exact (tendsto_const_nhds (x := x)).congr' (by
        filter_upwards [self_mem_nhdsWithin] with t (ht : t < 0)
        simp only [g, if_neg (not_le.mpr ht)])
    · exact (show Filter.Tendsto f (nhdsWithin 0 (Set.Ici 0)) (nhds x) from by
        have h1 : Filter.Tendsto (fun t => Real.exp (-(lambda * t)))
            (nhdsWithin 0 (Set.Ici 0)) (nhds 1) := by
          have hca : ContinuousAt (fun t => Real.exp (-(lambda * t))) 0 :=
            Real.continuous_exp.continuousAt.comp
              ((continuousAt_const.mul continuousAt_id).neg)
          have := hca.tendsto
          simp [mul_zero, Real.exp_zero] at this
          exact this.mono_left nhdsWithin_le_nhds
        have h2 := S.strong_cont x
        simpa [one_smul] using h1.smul h2).congr' (by
        filter_upwards [self_mem_nhdsWithin] with t (ht : 0 ≤ t)
        simp only [g, if_pos ht])
  -- `g` agrees with `f` on `(0, ∞)`, so the set integrals match
  have hg_eq : ∀ t, 0 < t →
      ∫ u in Set.Ioc 0 t, g u = ∫ u in Set.Ioc 0 t, f u := by
    intro t ht
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro u hu; simp [hg_def, hu.1.le]
  -- `g` is continuous (piecewise of continuous pieces matching at `0`)
  have hg_continuous : Continuous g := by
    change Continuous (Set.piecewise (Set.Ici 0) f (fun _ => x))
    apply continuous_piecewise
    · intro t ht
      have := frontier_Ici_subset (a := (0:ℝ)) ht
      simp only [Set.mem_singleton_iff] at this; subst this
      simp [f, S.at_zero, Real.exp_zero]
    · rw [closure_Ici]
      exact ContinuousOn.smul
        ((Real.continuous_exp.comp (continuous_neg.comp
          (Continuous.mul continuous_const continuous_id))).continuousOn)
        (fun t₀ ht₀ => S.strongContAt x t₀ ht₀)
    · exact continuousOn_const
  -- FTC for `g`: `HasDerivAt (fun u => ∫₀ᵘ g) x 0`
  have h_ftc : HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, g t) x 0 :=
    intervalIntegral.integral_hasDerivAt_of_tendsto_ae_right
      IntervalIntegrable.refl
      (hg_continuous.stronglyMeasurableAtFilter volume (nhds 0))
      (hg_cont.mono_left inf_le_left)
  have h_slope := h_ftc.tendsto_slope_zero_right
  simp only [zero_add, intervalIntegral.integral_same, sub_zero] at h_slope
  -- convert the interval integral to a set integral and `g` back to `f`
  exact h_slope.congr' (by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [one_div, intervalIntegral.integral_of_le (le_of_lt ht), hg_eq t ht])

private theorem StronglyContinuousSemigroup.intervalIntegrable_orbit
    (S : StronglyContinuousSemigroup X) (x : X) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun u => S.operator u x) volume a b := by
  have h_cont : ContinuousOn (fun u => S.operator u x) (Set.Ici 0) :=
    fun u hu => S.strongContAt x u hu
  exact (h_cont.mono fun u hu => by
    exact (le_inf ha hb).trans hu.1).intervalIntegrable

private theorem StronglyContinuousSemigroup.local_integral_shift_identity
    (S : StronglyContinuousSemigroup X) (x : X) {t h : ℝ} (ht : 0 < t) (hh : 0 < h) :
    S.operator h (∫ u in (0 : ℝ)..t, S.operator u x) -
        ∫ u in (0 : ℝ)..t, S.operator u x =
      (∫ u in t..t + h, S.operator u x) - ∫ u in (0 : ℝ)..h, S.operator u x := by
  set f := fun u => S.operator u x
  have hf_zero_t : IntervalIntegrable f volume (0 : ℝ) t :=
    S.intervalIntegrable_orbit x le_rfl ht.le
  have hf_h_th : IntervalIntegrable f volume h (t + h) :=
    S.intervalIntegrable_orbit x hh.le (by linarith)
  have hf_zero_h : IntervalIntegrable f volume (0 : ℝ) h :=
    S.intervalIntegrable_orbit x le_rfl hh.le
  have hf_h_zero : IntervalIntegrable f volume h (0 : ℝ) := hf_zero_h.symm
  have h_push : S.operator h (∫ u in (0 : ℝ)..t, f u) = ∫ u in h..t + h, f u := by
    rw [← (S.operator h).intervalIntegral_comp_comm hf_zero_t]
    rw [intervalIntegral.integral_congr (g := fun u => f (u + h))]
    · simp [zero_add]
    · intro u hu
      have hu_nonneg : 0 ≤ u := by
        rw [Set.uIcc_of_le ht.le] at hu
        exact hu.1
      -- unfold the local `f := fun u => S.operator u x` so the semigroup law applies
      change S.operator h (S.operator u x) = S.operator (u + h) x
      rw [← ContinuousLinearMap.comp_apply, ← S.semigroup h u hh.le hu_nonneg, add_comm]
  have h_sub :
      (∫ u in h..t + h, f u) - ∫ u in (0 : ℝ)..t, f u =
        (∫ u in t..t + h, f u) - ∫ u in (0 : ℝ)..h, f u := by
    exact intervalIntegral.integral_interval_sub_interval_comm'
      hf_h_th hf_zero_t hf_h_zero
  rw [h_push, h_sub]

private theorem StronglyContinuousSemigroup.tendsto_average_orbit_at
    (S : StronglyContinuousSemigroup X) (x : X) {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto (fun h => (1 / h) • ∫ u in t..t + h, S.operator u x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (S.operator t x)) := by
  set f := fun u => S.operator u x
  have h_cont_at : ContinuousAt f t := by
    have h := S.strongContAt x t ht.le
    rwa [nhdsWithin_eq_nhds.2 (Ici_mem_nhds ht)] at h
  have h_ftc : HasDerivAt (fun u => ∫ z in t..u, f z) (f t) t :=
    intervalIntegral.integral_hasDerivAt_right
      IntervalIntegrable.refl
      ((ContinuousAt.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioi
        (s := Set.Ioi (0 : ℝ)) (f := f) (by
          intro u hu
          have h := S.strongContAt x u hu.le
          rwa [nhdsWithin_eq_nhds.2 (Ici_mem_nhds hu)] at h)) t ht)
      h_cont_at
  have h_slope := h_ftc.tendsto_slope_zero_right
  simpa [f, one_div, intervalIntegral.integral_same] using h_slope

private theorem StronglyContinuousSemigroup.integral_orbit_mem_domain
    (S : StronglyContinuousSemigroup X) (x : X) {t : ℝ} (ht : 0 < t) :
    (∫ u in Set.Ioc 0 t, S.operator u x) ∈ S.domain := by
  rw [S.mem_domain_iff_tendsto]
  refine ⟨S.operator t x - x, ?_⟩
  set y := ∫ u in (0 : ℝ)..t, S.operator u x
  have h_zero : Filter.Tendsto
      (fun h => (1 / h) • ∫ u in (0 : ℝ)..h, S.operator u x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds x) := by
    have h := S.tendsto_average_resolvent_integrand 0 x
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [intervalIntegral.integral_of_le hh.le]
    simp
  have h_t : Filter.Tendsto
      (fun h => (1 / h) • ∫ u in t..t + h, S.operator u x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (S.operator t x)) :=
    S.tendsto_average_orbit_at x ht
  have h_lim := h_t.sub h_zero
  have h_interval : Filter.Tendsto
      (fun h => (1 / h) • (S.operator h y - y))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (S.operator t x - x)) := by
    refine h_lim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [StronglyContinuousSemigroup.local_integral_shift_identity S x ht hh]
    rw [smul_sub]
  simpa [y, intervalIntegral.integral_of_le ht.le] using h_interval

/-- The generator domain of a strongly continuous semigroup is dense
([EN] Lemma II.1.3 and its density corollary). -/
theorem StronglyContinuousSemigroup.dense_domain
    (S : StronglyContinuousSemigroup X) : Dense (S.domain : Set X) := by
  intro x
  refine mem_closure_of_tendsto
    (f := fun t => (1 / t) • ∫ u in Set.Ioc 0 t, S.operator u x)
    (b := nhdsWithin 0 (Set.Ioi (0 : ℝ))) ?_ ?_
  · simpa using S.tendsto_average_resolvent_integrand 0 x
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact S.domain.smul_mem (1 / t) (S.integral_orbit_mem_domain x ht)

/-- The generator difference quotient for `R(λ)x` converges to `λ R(λ)x - x`.
This is the core computation shared by `resolvent_mem_domain` and `resolventRightInv`. -/
private theorem StronglyContinuousSemigroup.resolvent_generator_tendsto
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M)
    (lambda : ℝ) (hlam : ω < lambda) (x : X) :
    Filter.Tendsto (fun t => (1 / t) • (S.operator t (S.resolvent hb lambda hlam x) -
      S.resolvent hb lambda hlam x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (lambda • S.resolvent hb lambda hlam x - x)) := by
  -- the slope `(e^{λt}-1)/t → λ` from the derivative of `exp` at `0`
  have hderiv : HasDerivAt (fun t => Real.exp (lambda * t)) lambda 0 := by
    have h := (Real.hasDerivAt_exp (lambda * 0)).comp (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).const_mul lambda)
    simp only [Real.exp_zero, mul_zero, one_mul, mul_one, Function.comp_def] at h
    exact h
  -- rewrite via the shift identity, then take the limit term by term
  apply Filter.Tendsto.congr'
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [S.resolvent_shift_identity hb lambda hlam x ht, smul_sub, smul_smul, smul_smul]
  · set Rlx := S.resolvent hb lambda hlam x
    set f := fun t => Real.exp (-(lambda * t)) • S.operator t x
    apply Filter.Tendsto.sub
    · -- `(1/t * (e^{λt}-1)) • Rlx → λ • Rlx`
      apply Filter.Tendsto.smul _ tendsto_const_nhds
      have := hderiv.tendsto_slope_zero_right
      simp only [zero_add, Real.exp_zero, mul_zero] at this
      exact this.congr (fun t => by simp only [smul_eq_mul]; ring)
    · -- `(1/t * e^{λt}) • ∫_{Ioc 0 t} f → 1 • x = x`
      rw [show x = (1 : ℝ) • x from (one_smul ℝ x).symm]
      simp_rw [show ∀ t, (1 / t * Real.exp (lambda * t)) • ∫ u in Set.Ioc 0 t, f u =
          Real.exp (lambda * t) • ((1 / t) • ∫ u in Set.Ioc 0 t, f u) from
        fun t => by rw [show 1 / t * Real.exp (lambda * t) =
          Real.exp (lambda * t) * (1 / t) from by ring, mul_smul]]
      apply Filter.Tendsto.smul
      · have hexp_cont : Filter.Tendsto (fun t => Real.exp (lambda * t))
            (nhds 0) (nhds 1) := by
          have := hderiv.continuousAt.tendsto
          simpa using this
        exact hexp_cont.mono_left nhdsWithin_le_nhds
      · exact S.tendsto_average_resolvent_integrand lambda x

/-- The resolvent maps all of `X` into the domain of the generator
([EN] Thm. II.1.10(i), [Linares] eq. 0.15). -/
theorem StronglyContinuousSemigroup.resolvent_mem_domain
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M)
    (lambda : ℝ) (hlam : ω < lambda) (x : X) :
    (S.resolvent hb lambda hlam x) ∈ S.domain :=
  ⟨_, S.resolvent_generator_tendsto hb lambda hlam x⟩

/-- The fundamental resolvent identity: `(λI - A) R(λ) x = x`.

This is the right-inverse half of eq. 0.16 in [Linares]: `(λI - A) R(λ) x = x`
for every `x`. The left inverse / injectivity (hence `R λ = (λI - A)⁻¹` and
`(0, ∞) ⊆ ρ(A)`) is not proved here; it belongs to the deferred generation
theorem. -/
theorem StronglyContinuousSemigroup.resolventRightInv
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M)
    (lambda : ℝ) (hlam : ω < lambda) (x : X) :
    lambda • S.resolvent hb lambda hlam x
      - S.generator
          ⟨S.resolvent hb lambda hlam x, S.resolvent_mem_domain hb lambda hlam x⟩ = x := by
  -- `A (R λ x) = λ • R λ x - x` reads off the generator value from the known limit.
  rw [S.generator_eq_of_tendsto (S.resolvent_mem_domain hb lambda hlam x)
    (S.resolvent_generator_tendsto hb lambda hlam x)]
  abel

/-- **Hille–Yosida resolvent bound** (forward direction): `‖R λ‖ ≤ M/(λ-ω)` for a C₀
semigroup with growth bound `(ω, M)` and `λ > ω` (Hille 1948, Yosida 1948; Engel–Nagel
Ch. II). The full theorem (an operator generates such a semigroup iff the iterated bounds
hold) needs the converse via the Yosida approximation. -/
theorem StronglyContinuousSemigroup.resolvent_norm_le
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M)
    (lambda : ℝ) (hlam : ω < lambda) :
    ‖S.resolvent hb lambda hlam‖ ≤ M / (lambda - ω) :=
  LinearMap.mkContinuous_norm_le _
    (div_nonneg (by linarith [hb.1]) (by linarith)) _

/-! ## Contraction-semigroup specializations (`M = 1`, `ω = 0`) -/

/-- The resolvent of a contraction semigroup, the `(0, 1)` case. -/
noncomputable def ContractionSemigroup.resolvent (S : ContractionSemigroup X)
    (lambda : ℝ) (hlam : 0 < lambda) : X →L[ℝ] X :=
  S.toStronglyContinuousSemigroup.resolvent S.hasGrowthBound lambda (by simpa using hlam)

/-- The contraction resolvent unfolds to the Laplace-transform integral
`R(λ) x = ∫₀^∞ e^{-λt} S(t)x dt`, the `(0, 1)` case. -/
theorem ContractionSemigroup.resolvent_apply (S : ContractionSemigroup X)
    (lambda : ℝ) (hlam : 0 < lambda) (x : X) :
    S.resolvent lambda hlam x
      = ∫ t in Set.Ioi 0, Real.exp (-(lambda * t)) • S.operator t x := rfl

/-- The contraction resolvent maps into the generator domain. -/
theorem ContractionSemigroup.resolvent_mem_domain (S : ContractionSemigroup X)
    (lambda : ℝ) (hlam : 0 < lambda) (x : X) :
    (S.resolvent lambda hlam x) ∈ S.toStronglyContinuousSemigroup.domain :=
  S.toStronglyContinuousSemigroup.resolvent_mem_domain S.hasGrowthBound lambda
    (by simpa using hlam) x

/-- The contraction resolvent right-inverse identity `(λI - A) R(λ) x = x`, the `(0, 1)` case
(cf. `StronglyContinuousSemigroup.resolventRightInv`). -/
theorem ContractionSemigroup.resolventRightInv (S : ContractionSemigroup X)
    (lambda : ℝ) (hlam : 0 < lambda) (x : X) :
    lambda • S.resolvent lambda hlam x
      - S.toStronglyContinuousSemigroup.generator
          ⟨S.resolvent lambda hlam x, S.resolvent_mem_domain lambda hlam x⟩ = x :=
  S.toStronglyContinuousSemigroup.resolventRightInv S.hasGrowthBound lambda
    (by simpa using hlam) x

/-- The contraction resolvent bound `‖R λ‖ ≤ 1/λ`, the `(0, 1)` case. -/
theorem ContractionSemigroup.resolvent_norm_le (S : ContractionSemigroup X)
    (lambda : ℝ) (hlam : 0 < lambda) :
    ‖S.resolvent lambda hlam‖ ≤ 1 / lambda := by
  have h := S.toStronglyContinuousSemigroup.resolvent_norm_le S.hasGrowthBound lambda
    (by simpa using hlam)
  rw [sub_zero] at h
  exact h

/-! ## Growth Bounds and Exponential Type -/

/-- Every C₀-semigroup has a finite exponential growth bound
([EN] Prop. I.5.5, [Linares] Thm. 1). -/
theorem StronglyContinuousSemigroup.existsGrowthBound
    (S : StronglyContinuousSemigroup X) :
    ∃ (ω : ℝ) (M : ℝ), S.HasGrowthBound ω M := by
  obtain ⟨M, hM1, hMbound⟩ := S.normBoundedOnUnitInterval
  have hM_pos : 0 < M := by linarith
  refine ⟨Real.log M, M, hM1, fun t ht => ?_⟩
  -- Integer-time operator norm bound by induction: ‖S(k)‖ ≤ M^k
  have h_int_bound : ∀ (k : ℕ), ‖S.operator (↑k : ℝ)‖ ≤ M ^ k := by
    intro k; induction k with
    | zero =>
      simp only [Nat.cast_zero, S.at_zero]
      exact ContinuousLinearMap.norm_id_le
    | succ k ih =>
      have : (↑(k + 1) : ℝ) = 1 + ↑k := by push_cast; ring
      rw [this, S.semigroup 1 ↑k (by linarith) (Nat.cast_nonneg k)]
      calc ‖(S.operator 1).comp (S.operator ↑k)‖
          ≤ ‖S.operator 1‖ * ‖S.operator ↑k‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ M * M ^ k :=
            mul_le_mul (hMbound 1 (by linarith) le_rfl) ih (norm_nonneg _) (by linarith)
        _ = M ^ (k + 1) := by ring
  -- Decompose t = (t - ⌊t⌋₊) + ⌊t⌋₊ where 0 ≤ t - ⌊t⌋₊ ≤ 1
  set n := ⌊t⌋₊ with hn_def
  have hn_le : (↑n : ℝ) ≤ t := Nat.floor_le ht
  have hfrac_nn : 0 ≤ t - ↑n := sub_nonneg.mpr hn_le
  have hfrac_le1 : t - ↑n ≤ 1 := by
    have := Nat.lt_floor_add_one t; linarith
  -- Use semigroup property: S(t) = S(t - n) ∘ S(n)
  have h_eq : (t - ↑n) + ↑n = t := by ring
  have h_sg := S.semigroup (t - ↑n) ↑n hfrac_nn (Nat.cast_nonneg n)
  rw [h_eq] at h_sg
  rw [h_sg]
  -- ‖S(t-n) ∘ S(n)‖ ≤ ‖S(t-n)‖ · ‖S(n)‖ ≤ M · M^n ≤ M · exp(log M · t)
  calc ‖(S.operator (t - ↑n)).comp (S.operator ↑n)‖
      ≤ ‖S.operator (t - ↑n)‖ * ‖S.operator ↑n‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ M * M ^ n :=
        mul_le_mul (hMbound _ hfrac_nn hfrac_le1) (h_int_bound n) (norm_nonneg _) (by linarith)
    _ ≤ M * Real.exp (Real.log M * t) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        calc (M : ℝ) ^ n
            = Real.exp (↑n * Real.log M) := by
              rw [Real.exp_nat_mul, Real.exp_log hM_pos]
          _ ≤ Real.exp (Real.log M * t) := by
              apply Real.exp_le_exp.mpr
              calc ↑n * Real.log M ≤ t * Real.log M :=
                    mul_le_mul_of_nonneg_right hn_le (Real.log_nonneg hM1)
                _ = Real.log M * t := by ring

end TauCeti.Semigroups

end
