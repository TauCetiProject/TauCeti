/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# Strongly continuous semigroups

This file contains the foundational C₀-semigroup structures, the nonnegative-time API
(`map_zero`, `map_add`, `continuousAt_zero`, and their pointwise/tendsto forms),
the `realOperator` real-time shim,
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

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A strongly continuous one-parameter semigroup (C₀-semigroup) on a normed space `X`.

The semigroup is indexed by nonnegative real time. The axioms are `S 0 = Id`,
`S (s + t) = S s ∘ S t`, and strong continuity at `0`. Note that the C₀-semigroup theory
proper (uniform boundedness, continuity of orbits at positive times) additionally
needs `X` complete. -/
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

instance instFunLike : FunLike (StronglyContinuousSemigroup X) ℝ≥0 (X →L[ℝ] X) where
  coe := toFun
  coe_injective := by
    rintro ⟨⟩ ⟨⟩ h
    congr

@[ext]
theorem ext {S T : StronglyContinuousSemigroup X} (h : ∀ t, S t = T t) : S = T :=
  DFunLike.ext _ _ h

/-- The native nonnegative-time operator at zero is the identity. -/
@[simp]
theorem map_zero (S : StronglyContinuousSemigroup X) :
    S 0 = ContinuousLinearMap.id ℝ X :=
  S.map_zero'

/-- Pointwise form of `StronglyContinuousSemigroup.map_zero`. -/
theorem map_zero_apply (S : StronglyContinuousSemigroup X) (x : X) :
    S 0 x = x := by
  rw [S.map_zero]
  rfl

/-- The native nonnegative-time semigroup law. -/
@[simp]
theorem map_add (S : StronglyContinuousSemigroup X) (s t : ℝ≥0) :
    S (s + t) = (S s).comp (S t) :=
  S.map_add' s t

/-- **The operator at a natural multiple of a time is a power.** `S (k • t) = (S t) ^ k`.

Not a `simp` lemma: `nsmul_eq_mul` rewrites the left-hand side to `S (↑k * t)`, so tagging this
would put it out of simp normal form (`simpNF`). -/
theorem map_nsmul (S : StronglyContinuousSemigroup X) (t : ℝ≥0) (k : ℕ) :
    S (k • t) = (S t) ^ k := by
  induction k with
  | zero => rw [zero_smul, S.map_zero, pow_zero, ContinuousLinearMap.one_def]
  | succ k ih =>
    rw [succ_nsmul', S.map_add, ih, pow_succ', ContinuousLinearMap.mul_def]

/-- **The power identity in simp normal form.** `S (↑k * t) = (S t) ^ k`.

This is `map_nsmul` with the left-hand side normalised: `nsmul_eq_mul` rewrites `k • t` to
`↑k * t`, so this spelling is the one `simp` can reach. -/
@[simp]
theorem map_natCast_mul (S : StronglyContinuousSemigroup X) (t : ℝ≥0) (k : ℕ) :
    S ((k : ℝ≥0) * t) = (S t) ^ k := by
  simpa [nsmul_eq_mul] using S.map_nsmul t k

/-- **The multi-step operator-norm bound.** If `‖S t‖ ≤ M`, then `‖S (k • t)‖ ≤ M ^ k` at every
natural multiple of `t`. -/
theorem norm_map_nsmul_le_pow (S : StronglyContinuousSemigroup X) (t : ℝ≥0) {M : ℝ}
    (hMt : ‖S t‖ ≤ M) (k : ℕ) : ‖S (k • t)‖ ≤ M ^ k := by
  rw [S.map_nsmul]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa [ContinuousLinearMap.one_def] using ContinuousLinearMap.norm_id_le
  · exact (norm_pow_le' _ hk).trans (pow_le_pow_left₀ (norm_nonneg _) hMt k)

/-- Pointwise form of `StronglyContinuousSemigroup.map_add`. -/
theorem map_add_apply (S : StronglyContinuousSemigroup X) (s t : ℝ≥0) (x : X) :
    S (s + t) x = S s (S t x) := by
  rw [S.map_add]
  rfl

/-- **The increment of a semigroup over `[a, b]` factors through its value at `a`.** -/
theorem sub_eq_comp_sub_one_of_le (S : StronglyContinuousSemigroup X) {a b : ℝ≥0} (hab : a ≤ b) :
    S b - S a = (S a).comp (S (b - a) - 1) := by
  have hmap := S.map_add a (b - a)
  rw [add_tsub_cancel_of_le hab] at hmap
  rw [hmap, ContinuousLinearMap.comp_sub, ContinuousLinearMap.one_def,
    ContinuousLinearMap.comp_id]

/-- Submultiplicativity of the native nonnegative-time operator norm. -/
theorem norm_map_add_le (S : StronglyContinuousSemigroup X) (s t : ℝ≥0) :
    ‖S (s + t)‖ ≤ ‖S s‖ * ‖S t‖ := by
  rw [S.map_add]
  exact ContinuousLinearMap.opNorm_comp_le _ _

/-- Strong continuity at zero for the native nonnegative-time action. -/
theorem continuousAt_zero (S : StronglyContinuousSemigroup X) (x : X) :
    ContinuousAt (fun t : ℝ≥0 => S t x) 0 :=
  S.continuousAt_zero' x

/-- Tendsto form of `StronglyContinuousSemigroup.continuousAt_zero`. -/
theorem continuousAt_zero_tendsto (S : StronglyContinuousSemigroup X) (x : X) :
    Filter.Tendsto (fun t : ℝ≥0 => S t x) (nhds 0) (nhds x) := by
  simpa using (S.continuousAt_zero x).tendsto

/-- The semigroup as a function of real time, extended by `id` for `t < 0`. -/
noncomputable def realOperator (S : StronglyContinuousSemigroup X) (t : ℝ) : X →L[ℝ] X :=
  S t.toNNReal

/-- The real-time operator is the native semigroup operator at the nonnegative part of `t`.

This is not a `simp` lemma: the simp normal form keeps `realOperator` folded, so that the more
specific lemmas `realOperator_coe`, `realOperator_zero` and `realOperator_derivWithin_zero` fire. -/
theorem realOperator_def (S : StronglyContinuousSemigroup X) (t : ℝ) :
    S.realOperator t = S t.toNNReal :=
  (rfl)

/-- At a nonnegative real time `t : ℝ≥0`, the real-time operator is the native operator. -/
@[simp]
lemma realOperator_coe (S : StronglyContinuousSemigroup X) (t : ℝ≥0) :
    S.realOperator t = S t := by
  rw [realOperator, Real.toNNReal_coe]

/-- The real-time operator at zero is the identity: `S.realOperator 0 = id`. -/
@[simp]
theorem realOperator_zero (S : StronglyContinuousSemigroup X) :
    S.realOperator 0 = ContinuousLinearMap.id ℝ X := by
  rw [realOperator, Real.toNNReal_zero, S.map_zero]

/-- At a nonpositive real time the real-time operator is the identity: `realOperator` extends the
semigroup to `ℝ` by `id` for `t ≤ 0`. -/
theorem realOperator_of_nonpos (S : StronglyContinuousSemigroup X) {t : ℝ} (ht : t ≤ 0) :
    S.realOperator t = ContinuousLinearMap.id ℝ X := by
  rw [realOperator, Real.toNNReal_of_nonpos ht, S.map_zero]

/-- The real-time operator at `t` is the one at the nonnegative part `max t 0`. -/
theorem realOperator_max_zero (S : StronglyContinuousSemigroup X) (t : ℝ) :
    S.realOperator (max t 0) = S.realOperator t := by
  rcases le_total t 0 with ht | ht
  · rw [max_eq_right ht, S.realOperator_zero, S.realOperator_of_nonpos ht]
  · rw [max_eq_left ht]

/-- At a nonpositive real time the real-time operator fixes every vector. -/
theorem realOperator_of_nonpos_apply (S : StronglyContinuousSemigroup X) {t : ℝ} (ht : t ≤ 0)
    (x : X) : S.realOperator t x = x := by
  rw [S.realOperator_of_nonpos ht, ContinuousLinearMap.id_apply]

/-- The real-time shim satisfies the semigroup law at nonnegative real times. -/
theorem realOperator_add (S : StronglyContinuousSemigroup X) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    S.realOperator (s + t) = (S.realOperator s).comp (S.realOperator t) := by
  rw [realOperator, realOperator, realOperator, Real.toNNReal_add hs ht, S.map_add]

/-- The semigroup law at nonnegative real times, applied to a vector. -/
theorem realOperator_add_apply (S : StronglyContinuousSemigroup X) (s t : ℝ) (hs : 0 ≤ s)
    (ht : 0 ≤ t) (x : X) : S.realOperator (s + t) x = S.realOperator s (S.realOperator t x) := by
  rw [S.realOperator_add s t hs ht, ContinuousLinearMap.comp_apply]

/-- Submultiplicativity of the real-time operator norm at nonnegative times: the semigroup law
`S.realOperator (s + t) = S.realOperator s ∘ S.realOperator t` bounds the norm of the composite
by the product of the norms. -/
theorem norm_realOperator_add_le (S : StronglyContinuousSemigroup X) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ‖S.realOperator (s + t)‖ ≤ ‖S.realOperator s‖ * ‖S.realOperator t‖ := by
  rw [realOperator, realOperator, realOperator, Real.toNNReal_add hs ht]
  exact S.norm_map_add_le s.toNNReal t.toNNReal

/-- Strong continuity at zero of the real-time orbit `t ↦ S.realOperator t x`. As the orbit is
constant for `t ≤ 0`, this is continuity at `0` in `ℝ`, not merely along `0 ≤ t`. -/
theorem realOperator_continuousAt_zero (S : StronglyContinuousSemigroup X) (x : X) :
    ContinuousAt (fun t => S.realOperator t x) 0 := by
  simp only [realOperator_def]
  exact (S.continuousAt_zero x).comp_of_eq continuous_real_toNNReal.continuousAt Real.toNNReal_zero

end StronglyContinuousSemigroup

variable (X)

/-- A contraction semigroup: `‖S(t)‖ ≤ 1` for all `t ≥ 0`
([EN] Def. I.5.6, [Linares] Def. 3). Has the growth estimate `M = 1`, `ω = 0`. -/
structure ContractionSemigroup extends StronglyContinuousSemigroup X where
  /-- `‖S(t)‖ ≤ 1` for all `t : ℝ≥0`. -/
  contracting : ∀ t : ℝ≥0, ‖toFun t‖ ≤ 1

variable {X}

namespace ContractionSemigroup

instance instFunLike : FunLike (ContractionSemigroup X) ℝ≥0 (X →L[ℝ] X) where
  coe S := S.toStronglyContinuousSemigroup
  coe_injective := by
    intro S T h
    cases S with
    | mk S hS =>
      cases T with
      | mk T hT =>
        have hST : S = T := DFunLike.ext S T (fun t => congrFun h t)
        cases hST
        congr

@[ext]
theorem ext {S T : ContractionSemigroup X} (h : ∀ t, S t = T t) : S = T :=
  DFunLike.ext _ _ h

@[simp]
theorem toStronglyContinuousSemigroup_apply (S : ContractionSemigroup X) (t : ℝ≥0) :
    S.toStronglyContinuousSemigroup t = S t :=
  rfl

end ContractionSemigroup

/-! ## Basic Properties -/

/-- A contraction semigroup is contractive at every real time (at negative times the real-time
operator is the identity). -/
theorem ContractionSemigroup.contracting_real (S : ContractionSemigroup X) (t : ℝ) :
    ‖S.realOperator t‖ ≤ 1 := by
  rw [StronglyContinuousSemigroup.realOperator_def]
  exact S.contracting t.toNNReal

/-- `S(t) x` at `t = 0` equals `x`, pointwise version. -/
theorem StronglyContinuousSemigroup.realOperator_zero_apply
    (S : StronglyContinuousSemigroup X) (x : X) :
    S.realOperator 0 x = x := by
  rw [S.realOperator_zero, ContinuousLinearMap.id_apply]

/-- A pointwise orbit bound `‖S.realOperator t x‖ ≤ B` valid on the initial interval `[0, δ)`
propagates, via the semigroup law, to the geometric bound `(max ‖S.realOperator δ‖ 1) ^ k * B`
on `[0, (k + 1) * δ)`. -/
private theorem StronglyContinuousSemigroup.norm_realOperator_apply_le_pow_mul_of_near_zero
    (S : StronglyContinuousSemigroup X) (x : X) {δ B : ℝ} (hδ_pos : 0 < δ)
    (h_near : ∀ t : ℝ, 0 ≤ t → t < δ → ‖S.realOperator t x‖ ≤ B) :
    ∀ (k : ℕ) (t : ℝ), 0 ≤ t → t < (↑k + 1) * δ →
      ‖S.realOperator t x‖ ≤ (max ‖S.realOperator δ‖ 1) ^ k * B := by
  set L := max ‖S.realOperator δ‖ 1
  have hB : 0 ≤ B := (norm_nonneg _).trans (h_near 0 le_rfl hδ_pos)
  intro k
  induction k with
  | zero =>
    -- Base interval `[0, δ)`: this is exactly the near-zero bound.
    intro t ht0 htδ
    simp only [Nat.cast_zero, zero_add, one_mul] at htδ
    simp only [pow_zero, one_mul]
    exact h_near t ht0 htδ
  | succ k ih =>
    intro t ht0 ht_ub
    by_cases hk : t < (↑k + 1) * δ
    · -- Previous interval: reuse the induction hypothesis and enlarge `L^k` to `L^(k+1)`.
      calc ‖S.realOperator t x‖ ≤ L ^ k * B := ih t ht0 hk
        _ ≤ L ^ (k + 1) * B :=
            mul_le_mul_of_nonneg_right
              (pow_le_pow_right₀ (le_max_right _ _) (Nat.le_succ k)) hB
    · -- New strip `[(k+1)δ, (k+2)δ)`: write `t = δ + (t - δ)` and use the semigroup law.
      push Not at hk
      have htd_nn : 0 ≤ t - δ := by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      have htd_lt : t - δ < (↑k + 1) * δ := by
        push_cast [Nat.succ_eq_add_one] at ht_ub; linarith
      calc ‖S.realOperator t x‖
          = ‖S.realOperator δ (S.realOperator (t - δ) x)‖ := by
            rw [← S.realOperator_add_apply δ (t - δ) hδ_pos.le htd_nn, add_sub_cancel]
        _ ≤ ‖S.realOperator δ‖ * ‖S.realOperator (t - δ) x‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ L * (L ^ k * B) := by
            apply mul_le_mul (le_max_left _ _) (ih _ htd_nn htd_lt)
              (by positivity) (by positivity)
        _ = L ^ (k + 1) * B := by ring

/-- Pointwise boundedness on `[0, 1]`, the hypothesis needed for Banach-Steinhaus. -/
private theorem StronglyContinuousSemigroup.exists_norm_realOperator_apply_le_on_unitInterval
    (S : StronglyContinuousSemigroup X) :
    ∀ x : X, ∃ C, ∀ (i : Set.Icc (0 : ℝ) 1),
      ‖(fun j : Set.Icc (0 : ℝ) 1 => S.realOperator j.val) i x‖ ≤ C := by
  intro x
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    Metric.continuousAt_iff.mp (S.realOperator_continuousAt_zero x) 1 one_pos
  have h_near : ∀ t : ℝ, 0 ≤ t → t < δ →
      ‖S.realOperator t x‖ ≤ ‖x‖ + 1 := by
    intro t ht0 htδ
    have h1 := hδ (x := t) (by rwa [Real.dist_0_eq_abs, abs_of_nonneg ht0])
    rw [S.realOperator_zero_apply, dist_eq_norm] at h1
    linarith [norm_le_insert' (S.realOperator t x) x]
  -- Cover `[0, 1]` by `N + 1` intervals of length `δ` (`N = ⌈1/δ⌉`); as `1 < (N + 1) * δ`,
  -- the geometric growth bound at `k = N` controls the whole interval.
  set N := Nat.ceil (1 / δ)
  have hNδ : 1 < (↑N + 1) * δ := by
    have hN : (1 : ℝ) / δ ≤ ↑N := Nat.le_ceil _
    have : 1 ≤ ↑N * δ := by rwa [div_le_iff₀ hδ_pos] at hN
    linarith
  refine ⟨(max ‖S.realOperator δ‖ 1) ^ N * (‖x‖ + 1), ?_⟩
  rintro ⟨t, ht0, ht1⟩
  exact S.norm_realOperator_apply_le_pow_mul_of_near_zero x hδ_pos h_near N t ht0 (by linarith)

/-- Right continuity of the real-time orbit at a nonnegative time `t₀`, from strong continuity at
`0` and the semigroup law `S (t₀ + (t - t₀)) = S t₀ ∘ S (t - t₀)`. -/
private theorem StronglyContinuousSemigroup.realOperator_continuousWithinAt_Ici
    (S : StronglyContinuousSemigroup X) (x : X) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    ContinuousWithinAt (fun t => S.realOperator t x) (Set.Ici t₀) t₀ := by
  have h : ContinuousAt (fun t => S.realOperator t₀ (S.realOperator (t - t₀) x)) t₀ :=
    (S.realOperator t₀).continuous.continuousAt.comp
      ((S.realOperator_continuousAt_zero x).comp_of_eq (continuous_sub_right t₀).continuousAt
        (sub_self t₀))
  refine (h.continuousWithinAt.congr (fun t (ht : t₀ ≤ t) => ?_) ?_)
  · rw [← S.realOperator_add_apply t₀ (t - t₀) ht₀ (sub_nonneg.mpr ht), add_sub_cancel]
  · rw [sub_self, S.realOperator_zero_apply]

/-! ## Results requiring completeness

When `X` is complete, pointwise boundedness on `[0, 1]` implies uniform operator-norm
boundedness on `[0, 1]` via the Banach--Steinhaus theorem. From this, uniform boundedness on
compact intervals and left-continuity (and thus full continuity) of orbits follow. -/

section CompleteSpace

variable [CompleteSpace X]

/-- The operator norm of a C₀-semigroup is bounded on `[0, 1]`.

One direction of [EN] Prop. I.5.3: strong continuity implies uniform boundedness
on compact intervals. This rests on the Banach--Steinhaus theorem and therefore
requires `X` to be complete. -/
theorem StronglyContinuousSemigroup.exists_norm_realOperator_le_on_unitInterval
    (S : StronglyContinuousSemigroup X) :
    ∃ (M : ℝ), 1 ≤ M ∧
      ∀ (t : ℝ), 0 ≤ t → t ≤ 1 → ‖S.realOperator t‖ ≤ M := by
  obtain ⟨C, hC⟩ := banach_steinhaus S.exists_norm_realOperator_apply_le_on_unitInterval
  exact ⟨max C 1, le_max_right _ _, fun t ht0 ht1 =>
    (hC ⟨t, ht0, ht1⟩).trans (le_max_left _ _)⟩

/-- The operator norm of a C₀-semigroup is bounded on `[0, n]` for any `n : ℕ`. -/
private theorem StronglyContinuousSemigroup.exists_norm_realOperator_le_of_le_natCast
    (S : StronglyContinuousSemigroup X) (n : ℕ) :
    ∃ (C : ℝ), 0 < C ∧
      ∀ (t : ℝ), 0 ≤ t → t ≤ n → ‖S.realOperator t‖ ≤ C := by
  -- Induction on `n`: on `(k, k+1]` write `t = (t-k) + k` with `t-k ∈ [0,1]`, so
  -- `S(t) = S(t-k) ∘ S(k)` and `‖S(t)‖ ≤ M · M^k = M^(k+1)`.
  obtain ⟨M, hM1, hMbound⟩ := S.exists_norm_realOperator_le_on_unitInterval
  have hM_pos : (0 : ℝ) < M := by linarith
  induction n with
  | zero =>
    refine ⟨1, one_pos, fun t ht htn => ?_⟩
    simp only [Nat.cast_zero] at htn
    have : t = 0 := le_antisymm htn ht
    rw [this, S.realOperator_zero]
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
      calc ‖S.realOperator t‖
          = ‖S.realOperator ((t - ↑k) + ↑k)‖ := by
            rw [sub_add_cancel]
        _ ≤ ‖S.realOperator (t - ↑k)‖ * ‖S.realOperator ↑k‖ :=
            S.norm_realOperator_add_le _ _ htk_nn hk_nn
        _ ≤ M * C_k :=
            mul_le_mul (hMbound _ htk_nn htk_le) (hC_k_bound ↑k hk_nn le_rfl)
              (norm_nonneg _) (le_of_lt hM_pos)

/-- Left continuity of the real-time orbit at `t₀` within `[0, t₀]`: the semigroup law gives
`S t x - S t₀ x = S t (x - S (t₀ - t) x)`, and `‖S t‖` is uniformly bounded for `t ∈ [0, t₀]`. -/
private theorem StronglyContinuousSemigroup.realOperator_continuousWithinAt_Icc
    (S : StronglyContinuousSemigroup X) (x : X) (t₀ : ℝ) :
    ContinuousWithinAt (fun t => S.realOperator t x) (Set.Icc 0 t₀) t₀ := by
  obtain ⟨C, hC_pos, hC_bound⟩ := S.exists_norm_realOperator_le_of_le_natCast ⌈t₀⌉₊
  have h_sc : Filter.Tendsto (fun t => S.realOperator t x) (𝓝 0) (𝓝 x) := by
    simpa only [S.realOperator_zero_apply] using (S.realOperator_continuousAt_zero x).tendsto
  rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ_spec⟩ := Metric.tendsto_nhds_nhds.mp h_sc (ε / C) (div_pos hε hC_pos)
  refine ⟨δ, hδ_pos, fun t ⟨ht0, htt₀⟩ ht_dist => ?_⟩
  have h_diff : S.realOperator t x - S.realOperator t₀ x =
      S.realOperator t (x - S.realOperator (t₀ - t) x) := by
    rw [map_sub, ← S.realOperator_add_apply t (t₀ - t) ht0 (sub_nonneg.mpr htt₀), add_sub_cancel]
  rw [dist_eq_norm, h_diff]
  calc ‖S.realOperator t (x - S.realOperator (t₀ - t) x)‖
      ≤ ‖S.realOperator t‖ * ‖x - S.realOperator (t₀ - t) x‖ := (S.realOperator t).le_opNorm _
    _ ≤ C * ‖x - S.realOperator (t₀ - t) x‖ :=
        mul_le_mul_of_nonneg_right (hC_bound t ht0 (htt₀.trans (Nat.le_ceil t₀)))
          (norm_nonneg _)
    _ = C * dist (S.realOperator (t₀ - t) x) x := by rw [dist_comm, dist_eq_norm]
    _ < C * (ε / C) := by
        refine mul_lt_mul_of_pos_left (hδ_spec ?_) hC_pos
        rwa [Real.dist_0_eq_abs, abs_sub_comm, ← Real.dist_eq]
    _ = ε := mul_div_cancel₀ ε hC_pos.ne'

/-- Strong continuity at every `t₀ ≥ 0` within the nonnegative half-line
([EN] Prop. I.5.3, [Linares] Cor. 1). -/
theorem StronglyContinuousSemigroup.realOperator_continuousWithinAt
    (S : StronglyContinuousSemigroup X) (x : X) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    ContinuousWithinAt (fun t => S.realOperator t x) (Set.Ici 0) t₀ := by
  rw [← Set.Icc_union_Ici_eq_Ici ht₀]
  exact (S.realOperator_continuousWithinAt_Icc x t₀).union
    (S.realOperator_continuousWithinAt_Ici x ht₀)

/-- The real-time orbit of a strongly continuous semigroup is continuous on the
nonnegative half-line. -/
theorem StronglyContinuousSemigroup.realOperator_continuousOn_Ici
    (S : StronglyContinuousSemigroup X) (x : X) :
    ContinuousOn (fun t : ℝ => S.realOperator t x) (Set.Ici 0) := by
  intro t ht
  exact S.realOperator_continuousWithinAt x t ht

/-- The real-time orbit is continuous on all of `ℝ`, using the constant extension at negative
times. -/
theorem StronglyContinuousSemigroup.continuous_realOperator_apply
    (S : StronglyContinuousSemigroup X) (x : X) :
    Continuous (fun t : ℝ => S.realOperator t x) := by
  have hneg : ContinuousOn (fun t : ℝ => S.realOperator t x) (Set.Iic 0) := by
    apply (continuousOn_const : ContinuousOn (fun _ : ℝ => x) (Set.Iic 0)).congr
    intro t ht
    exact S.realOperator_of_nonpos_apply ht x
  have h := hneg.union_of_isClosed (S.realOperator_continuousOn_Ici x)
    isClosed_Iic isClosed_Ici
  simpa [Set.Iic_union_Ici] using h

end CompleteSpace

end TauCeti.Semigroups

end
