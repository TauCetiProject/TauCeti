/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Extr
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import TauCeti.Analysis.SpecificLimits.HalfPowSucc
import TauCeti.Topology.Algebra.InfiniteSum.Real

/-!
# Simons' inequality

Let `x n : β → ℝ` be a sequence of real functions, uniformly bounded on a set `s : Set β`. A
*σ-convex combination* of the sequence is a pointwise series `∑' n, w n * x n`, where the
weights `w n` are nonnegative and sum to one. **Simons' inequality** says that if every
σ-convex combination attains its supremum on `s`, then
`inf_w sup_b ∑' n, w n * x n b ≤ sup_b limsup_n x n b`,
the infimum being over all σ-convex combinations.

We state it in the form used for James's theorem: if every σ-convex combination attains its
supremum on `s` and that supremum is at least `c`, then for every `ε > 0` there is a point
`b ∈ s` with `c - ε < x n b` for infinitely many `n`
(`TauCeti.exists_frequently_sub_lt_of_isMaxOn_tsum`).

## Proof

Write `λᵢ = 2⁻⁽ⁱ⁺¹⁾`, so that the weights `λₙ, λₙ₊₁, …` of the tail have total mass `μₙ = 2⁻ⁿ`.
Recursively choose σ-convex weights `νₙ` supported on `[n, ∞)` such that, with
`sₙ = ∑ i < n, λᵢ νᵢ`, the supremum of the combination `sₙ + μₙ νₙ` is within `δₙ` of its
infimum over all such tail weights. Let `ζ = ∑ λᵢ νᵢ` and let `b` be a point where the combination
`ζ` attains its supremum. Writing `yᵢ` for the value at `b` of the combination `νᵢ` and
`Tₙ = ∑ i ≥ n, λᵢ yᵢ`, comparing `ζ` with the near-minimizing `sₙ + μₙ νₙ` gives
`μₙ yₙ ≤ Tₙ + δₙ`. Since `Tₙ₊₁ = Tₙ - λₙ yₙ`, the normalized tails `Tₙ / μₙ` almost do not
decrease, and the first one, the value of `ζ` at `b`, is at least `c`. A tail average of the
values `x m b`, `m ≥ n`, close to `c` for every `n` forces `x m b` to be close to `c` for
infinitely many `m`.

## References

* S. Simons, *A convergence theorem with boundary*, Pacific J. Math. **40** (1972), 703–708.
-/

public section

open Filter Finset

namespace TauCeti

variable {β : Type*} {x : ℕ → β → ℝ} {M : ℝ}

/-- The σ-convex weights supported on `[n, ∞)`. -/
private def tailWeights (n : ℕ) : Set (ℕ → ℝ) :=
  {w | (∀ m, 0 ≤ w m) ∧ (∀ m < n, w m = 0) ∧ HasSum w 1}

private lemma single_mem_tailWeights (n : ℕ) : Pi.single n 1 ∈ tailWeights n := by
  refine ⟨fun m ↦ ?_, fun m hm ↦ ?_, hasSum_pi_single n 1⟩
  · rw [Pi.single_apply]
    split_ifs <;> norm_num
  · simp [hm.ne]

/-- The value at `b` of the combination with weights `w`. -/
private noncomputable def comb (x : ℕ → β → ℝ) (w : ℕ → ℝ) (b : β) : ℝ :=
  ∑' m, w m * x m b

/-- The supremum over `β` of the combination with weights `w`. -/
private noncomputable def supComb (x : ℕ → β → ℝ) (w : ℕ → ℝ) : ℝ :=
  ⨆ b, comb x w b

/-- The partial mixture `∑ i < n, 2⁻⁽ⁱ⁺¹⁾ ν i` of a sequence of weights. -/
private noncomputable def partialMix (ν : ℕ → ℕ → ℝ) (n : ℕ) : ℕ → ℝ :=
  fun m ↦ ∑ i ∈ range n, (1 / 2) ^ (i + 1) * ν i m

/-- The mixture `∑ i, 2⁻⁽ⁱ⁺¹⁾ ν (i + n)` of the weights from index `n` on. -/
private noncomputable def tailMix (ν : ℕ → ℕ → ℝ) (n : ℕ) : ℕ → ℝ :=
  fun m ↦ ∑' i, (1 / 2) ^ (i + 1) * ν (i + n) m

private lemma partialMix_nonneg {ν : ℕ → ℕ → ℝ} (hν : ∀ n, ν n ∈ tailWeights n)
    (n m : ℕ) : 0 ≤ partialMix ν n m :=
  sum_nonneg fun i _ ↦ mul_nonneg (by positivity) ((hν i).1 m)

private lemma summable_partialMix {ν : ℕ → ℕ → ℝ} (hν : ∀ n, ν n ∈ tailWeights n)
    (n : ℕ) : Summable (partialMix ν n) :=
  summable_sum fun i _ ↦ (hν i).2.2.summable.mul_left _

private lemma tailMix_mem_tailWeights {ν : ℕ → ℕ → ℝ} (hν : ∀ n, ν n ∈ tailWeights n)
    (n : ℕ) : tailMix ν n ∈ tailWeights n := by
  refine ⟨fun m ↦ tsum_nonneg fun i ↦ mul_nonneg (by positivity) ((hν _).1 m), fun m hm ↦ ?_,
    hasSum_half_pow_succ.tsum_mul_of_hasSum_one (fun _ ↦ by positivity)
      (fun i ↦ (hν (i + n)).1) fun i ↦ (hν (i + n)).2.2⟩
  refine (tsum_congr fun i ↦ ?_).trans tsum_zero
  rw [(hν (i + n)).2.1 m (by omega), mul_zero]

private lemma half_pow_add_succ (i n : ℕ) :
    (1 / 2 : ℝ) ^ (i + n + 1) = (1 / 2) ^ n * (1 / 2) ^ (i + 1) := by
  ring

/-- The full mixture `tailMix ν 0` splits into the partial mixture and the scaled tail mixture. -/
private lemma partialMix_add_smul_tailMix {ν : ℕ → ℕ → ℝ} (hν : ∀ n, ν n ∈ tailWeights n)
    (n : ℕ) :
    partialMix ν n + (1 / 2 : ℝ) ^ n • tailMix ν n = tailMix ν 0 := by
  -- The columns of the mixture of the weights from index `n` on are summable.
  have hcol (n m : ℕ) : Summable fun i ↦ (1 / 2 : ℝ) ^ (i + 1) * ν (i + n) m :=
    (hasSum_half_pow_succ.summable.prod_mul_of_hasSum_one (fun _ ↦ by positivity)
      (fun i ↦ (hν (i + n)).1) fun i ↦ (hν (i + n)).2.2).prod_symm.prod_factor m
  funext m
  have hcol₀ : Summable fun i ↦ (1 / 2 : ℝ) ^ (i + 1) * ν i m := by simpa using hcol 0 m
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, partialMix, tailMix, add_zero]
  rw [← hcol₀.sum_add_tsum_nat_add n, ← (hcol n m).tsum_mul_left]
  simp only [half_pow_add_succ, mul_assoc]

section Bounded

variable (hM : ∀ n b, |x n b| ≤ M)
include hM

private lemma abs_comb_le {w : ℕ → ℝ} (hw0 : ∀ m, 0 ≤ w m) (hw : Summable w) (b : β) :
    |comb x w b| ≤ (∑' m, w m) * M := by
  rw [comb, ← Real.norm_eq_abs]
  refine tsum_of_norm_bounded (hw.hasSum.mul_right M) fun m ↦ ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 m)]
  exact mul_le_mul_of_nonneg_left (hM m b) (hw0 m)

private lemma bddAbove_range_comb {w : ℕ → ℝ} (hw0 : ∀ m, 0 ≤ w m) (hw : Summable w) :
    BddAbove (Set.range (comb x w)) :=
  ⟨(∑' m, w m) * M, by
    rintro _ ⟨b, rfl⟩
    exact (le_abs_self _).trans (abs_comb_le hM hw0 hw b)⟩

private lemma comb_le_supComb {w : ℕ → ℝ} (hw0 : ∀ m, 0 ≤ w m) (hw : Summable w) (b : β) :
    comb x w b ≤ supComb x w :=
  le_ciSup (bddAbove_range_comb hM hw0 hw) b

private lemma comb_add_smul {s ν : ℕ → ℝ} (hs : Summable s) (hν : Summable ν) (μ : ℝ) (b : β) :
    comb x (s + μ • ν) b = comb x s b + μ * comb x ν b := by
  simp only [comb, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc]
  rw [(hs.mul_of_abs_le (hM · b)).tsum_add ((hν.mul_of_abs_le (hM · b)).mul_left μ),
    (hν.mul_of_abs_le (hM · b)).tsum_mul_left]

/-- The combination of a mixture of σ-convex weights is the mixture of the combinations. -/
private lemma comb_mix {a : ℕ → ℝ} {A : ℝ} (ha0 : ∀ i, 0 ≤ a i) (ha : HasSum a A)
    {ν : ℕ → ℕ → ℝ} (hν0 : ∀ i m, 0 ≤ ν i m) (hν : ∀ i, HasSum (ν i) 1) (b : β) :
    comb x (fun m ↦ ∑' i, a i * ν i m) b = ∑' i, a i * comb x (ν i) b := by
  have hh := ha.summable.prod_mul_of_hasSum_one ha0 hν0 hν
  have hcol (m : ℕ) : Summable fun i ↦ a i * ν i m := hh.prod_symm.prod_factor m
  set f : ℕ → ℕ → ℝ := fun i m ↦ a i * ν i m * x m b
  have hf : Summable (Function.uncurry f) := hh.mul_of_abs_le fun p ↦ hM p.2 b
  have hfswap : Summable fun p : ℕ × ℕ ↦ Function.uncurry f p.swap := hf.prod_symm
  calc comb x (fun m ↦ ∑' i, a i * ν i m) b = ∑' m, ∑' i, f i m := by
        refine tsum_congr fun m ↦ ?_
        rw [(hcol m).tsum_mul_right]
    _ = ∑' i, ∑' m, f i m :=
        Summable.tsum_comm' hf (fun i ↦ hf.prod_factor i) fun m ↦ hfswap.prod_factor m
    _ = ∑' i, a i * comb x (ν i) b := by
        refine tsum_congr fun i ↦ ?_
        simp only [f, comb, mul_assoc]
        exact ((hν i).summable.mul_of_abs_le (hM · b)).tsum_mul_left (a i)

/-- For nonnegative summable weights `s`, some tail weights `ν` make the supremum of `s + μ • ν`
minimal up to `δ`. -/
private lemma exists_supComb_le_add [Nonempty β] (n : ℕ) {μ δ : ℝ} (hμ : 0 ≤ μ) (hδ : 0 < δ)
    (s : ℕ → ℝ) : ∃ ν ∈ tailWeights n, (∀ m, 0 ≤ s m) → Summable s →
      ∀ ν' ∈ tailWeights n, supComb x (s + μ • ν) ≤ supComb x (s + μ • ν') + δ := by
  by_cases hs : (∀ m, 0 ≤ s m) ∧ Summable s
  swap
  · exact ⟨_, single_mem_tailWeights n, fun h0 h ↦ absurd ⟨h0, h⟩ hs⟩
  obtain ⟨hs0, hs⟩ := hs
  let f : tailWeights n → ℝ := fun ν ↦ supComb x (s + μ • (ν : ℕ → ℝ))
  obtain ⟨b₀⟩ := ‹Nonempty β›
  have hbdd : BddBelow (Set.range f) := by
    refine ⟨comb x s b₀ - μ * M, ?_⟩
    rintro _ ⟨⟨ν, hν0, -, hν⟩, rfl⟩
    -- The combination of `ν` at `b₀` is at least `-M`, as `ν` is a probability weight.
    have hνb := abs_comb_le hM hν0 hν.summable b₀
    rw [hν.tsum_eq, one_mul] at hνb
    have hle := comb_le_supComb (w := s + μ • ν) hM
      (fun m ↦ add_nonneg (hs0 m) (mul_nonneg hμ (hν0 m)))
      (hs.add (hν.summable.mul_left μ)) b₀
    rw [comb_add_smul hM hs hν.summable] at hle
    have := mul_le_mul_of_nonneg_left (neg_le_of_abs_le hνb) hμ
    simp only [f]
    linarith
  have : Nonempty (tailWeights n) := ⟨⟨_, single_mem_tailWeights n⟩⟩
  obtain ⟨ν, hν⟩ := exists_lt_of_ciInf_lt (lt_add_of_pos_right (⨅ ν, f ν) hδ)
  refine ⟨ν, ν.property, fun _ _ ν' hν' ↦ ?_⟩
  have := ciInf_le hbdd ⟨ν', hν'⟩
  simp only [f] at hν this
  linarith

/-- A sequence of tail weights `ν n`, each nearly minimizing, up to `δ n`, the supremum of the
combination `partialMix ν n + 2⁻ⁿ • ν n`. -/
private lemma exists_seq_tailWeights [Nonempty β] {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) :
    ∃ ν : ℕ → ℕ → ℝ, (∀ n, ν n ∈ tailWeights n) ∧ ∀ n, ∀ ν' ∈ tailWeights n,
      supComb x (partialMix ν n + (1 / 2 : ℝ) ^ n • ν n) ≤
        supComb x (partialMix ν n + (1 / 2 : ℝ) ^ n • ν') + δ n := by
  choose ν hνw hνmin using fun n s ↦
    exists_supComb_le_add (x := x) hM n (μ := (1 / 2 : ℝ) ^ n) (by positivity) (hδ n) s
  -- Choose `ν n` from the partial mixture `s n` of the earlier choices.
  let s : ℕ → ℕ → ℝ := fun n ↦ Nat.rec 0 (fun k t ↦ t + (1 / 2 : ℝ) ^ (k + 1) • ν k t) n
  set ν' : ℕ → ℕ → ℝ := fun n ↦ ν n (s n)
  have hs_succ (n : ℕ) : s (n + 1) = s n + (1 / 2 : ℝ) ^ (n + 1) • ν' n := rfl
  have hs : ∀ n, s n = partialMix ν' n := by
    intro n
    induction n with
    | zero => funext m; simp [s, partialMix]
    | succ n ih => funext m; simp [hs_succ, ih, partialMix, sum_range_succ]
  have hν'w : ∀ n, ν' n ∈ tailWeights n := fun n ↦ hνw n (s n)
  refine ⟨ν', hν'w, fun n ν'' hν'' ↦ ?_⟩
  rw [← hs]
  exact hνmin n (s n) (hs n ▸ partialMix_nonneg hν'w n) (hs n ▸ summable_partialMix hν'w n)
    ν'' hν''

private lemma comb_tailMix_zero {ν : ℕ → ℕ → ℝ} (hν : ∀ n, ν n ∈ tailWeights n)
    (b : β) :
    comb x (tailMix ν 0) b = ∑' i, (1 / 2) ^ (i + 1) * comb x (ν i) b := by
  have h : tailMix ν 0 = fun m ↦ ∑' i, (1 / 2 : ℝ) ^ (i + 1) * ν i m := by
    funext m
    simp only [tailMix, add_zero]
  rw [h]
  exact comb_mix hM (fun _ ↦ by positivity) hasSum_half_pow_succ (fun i ↦ (hν i).1)
    (fun i ↦ (hν i).2.2) b

private lemma comb_partialMix {ν : ℕ → ℕ → ℝ} (hν : ∀ n, ν n ∈ tailWeights n)
    (n : ℕ) (b : β) :
    comb x (partialMix ν n) b = ∑ i ∈ range n, (1 / 2) ^ (i + 1) * comb x (ν i) b := by
  simp only [comb, partialMix, sum_mul, mul_assoc]
  rw [Summable.tsum_finsetSum fun i _ ↦
    ((hν i).2.2.summable.mul_of_abs_le (hM · b)).mul_left _]
  exact sum_congr rfl fun i _ ↦ ((hν i).2.2.summable.mul_of_abs_le (hM · b)).tsum_mul_left _

/-- A value of a combination with tail weights from `i` on exceeding `a` forces a value
`x m b`, `m ≥ i`, exceeding `a`. -/
private lemma exists_le_lt_of_lt_comb {ν : ℕ → ℕ → ℝ} (hν : ∀ n, ν n ∈ tailWeights n)
    {i : ℕ} {a : ℝ} {b : β} (h : a < comb x (ν i) b) :
    ∃ m ≥ i, a < x m b := by
  by_contra! hle
  have hν1 := (hν i).2.2
  refine h.not_ge ?_
  calc comb x (ν i) b ≤ ∑' m, ν i m * a :=
        (hν1.summable.mul_of_abs_le (hM · b)).tsum_le_tsum (fun m ↦ ?_)
          (hν1.summable.mul_right _)
    _ = a := by rw [hν1.summable.tsum_mul_right, hν1.tsum_eq, one_mul]
  by_cases hm : m < i
  · simp [(hν i).2.1 m hm]
  · exact mul_le_mul_of_nonneg_left (hle m (not_lt.1 hm)) ((hν i).1 m)

end Bounded

/-- The real-sequence core of Simons' inequality. Let `Tₙ = ∑ i ≥ n, 2⁻⁽ⁱ⁺¹⁾ yᵢ`. If `c ≤ T₀`
and `2⁻ⁿ yₙ ≤ Tₙ + ε 4⁻ⁿ / 4` for all `n`, then `c - ε < yᵢ` for infinitely many `i`. -/
private lemma frequently_sub_lt_of_le_tsum {y : ℕ → ℝ} {c ε : ℝ} (hε : 0 < ε)
    (hy : Summable fun i ↦ (1 / 2 : ℝ) ^ (i + 1) * y i)
    (h₀ : c ≤ ∑' i, (1 / 2 : ℝ) ^ (i + 1) * y i)
    (hkey : ∀ n, (1 / 2 : ℝ) ^ n * y n ≤
      ∑' i, (1 / 2 : ℝ) ^ (i + n + 1) * y (i + n) + ε / 4 * ((1 / 2) ^ n) ^ 2) :
    ∃ᶠ i in atTop, c - ε < y i := by
  set T : ℕ → ℝ := fun n ↦ ∑' i, (1 / 2 : ℝ) ^ (i + n + 1) * y (i + n) with hT
  have hT_succ : ∀ n, T n = (1 / 2) ^ (n + 1) * y n + T (n + 1) := fun n ↦ by
    have hsh : Summable fun i ↦ (1 / 2 : ℝ) ^ (i + n + 1) * y (i + n) :=
      (summable_nat_add_iff n).2 hy
    simp only [hT]
    rw [hsh.tsum_eq_zero_add, zero_add]
    congr 1
    refine tsum_congr fun i ↦ ?_
    rw [show i + 1 + n = i + (n + 1) by omega]
  -- The normalized tails `2ⁿ Tₙ` stay above `c - ε / 2`.
  have hT_lower : ∀ n, (1 / 2) ^ n * (c - ε / 2 + ε / 2 * (1 / 2) ^ n) ≤ T n := by
    intro n
    induction n with
    | zero => simpa [hT] using h₀
    | succ n ih =>
      have h₁ := hkey n
      have h₂ := hT_succ n
      rw [pow_succ] at h₂ ⊢
      nlinarith
  -- If `y i ≤ c - ε` for all `i ≥ N`, then `T N ≤ 2⁻ᴺ (c - ε)`.
  by_contra hfreq
  obtain ⟨N, hN⟩ := eventually_atTop.1 (not_frequently.1 hfreq)
  have hlN : Summable fun i ↦ (1 / 2 : ℝ) ^ (i + N + 1) :=
    (summable_nat_add_iff N).2 hasSum_half_pow_succ.summable
  have hTle : T N ≤ (1 / 2) ^ N * (c - ε) :=
    calc T N ≤ ∑' i, (1 / 2 : ℝ) ^ (i + N + 1) * (c - ε) :=
          Summable.tsum_le_tsum
            (fun i ↦ mul_le_mul_of_nonneg_left (not_lt.1 (hN _ (by omega))) (by positivity))
            ((summable_nat_add_iff N).2 hy) (hlN.mul_right _)
      _ = (1 / 2) ^ N * (c - ε) := by rw [hlN.tsum_mul_right, tsum_half_pow_add_succ]
  have h₁ := hT_lower N
  have h₂ : 0 < (1 / 2 : ℝ) ^ N * ε := by positivity
  have h₃ : 0 < ((1 / 2 : ℝ) ^ N) ^ 2 * ε := by positivity
  nlinarith

/-- Simons' inequality on the whole of `β`. -/
private lemma exists_frequently_sub_lt_of_isMaxOn_univ_tsum {x : ℕ → β → ℝ} {M c ε : ℝ}
    (hM : ∀ n b, |x n b| ≤ M)
    (hmax : ∀ w : ℕ → ℝ, (∀ n, 0 ≤ w n) → HasSum w 1 →
      ∃ b, IsMaxOn (fun b ↦ ∑' n, w n * x n b) Set.univ b)
    (hc : ∀ w : ℕ → ℝ, (∀ n, 0 ≤ w n) → HasSum w 1 → ∃ b, c ≤ ∑' n, w n * x n b)
    (hε : 0 < ε) : ∃ b, ∃ᶠ n in atTop, c - ε < x n b := by
  obtain ⟨b₀, -⟩ := hc _ (single_mem_tailWeights 0).1 (single_mem_tailWeights 0).2.2
  have : Nonempty β := ⟨b₀⟩
  -- Near-minimizing tail weights `ν n`, their mixture `ζ`, and a point `b` where the
  -- combination `ζ` attains its supremum.
  obtain ⟨ν, hν, hνmin⟩ := exists_seq_tailWeights (x := x) hM
    (δ := fun n ↦ ε / 4 * ((1 / 2) ^ n) ^ 2) fun n ↦ by positivity
  obtain ⟨hζ0, -, hζ1⟩ := tailMix_mem_tailWeights hν 0
  obtain ⟨b, hb⟩ := hmax _ hζ0 hζ1
  have hbmax : ∀ b', comb x (tailMix ν 0) b' ≤ comb x (tailMix ν 0) b :=
    fun b' ↦ hb (Set.mem_univ b')
  have hsup : supComb x (tailMix ν 0) = comb x (tailMix ν 0) b :=
    le_antisymm (ciSup_le hbmax) (comb_le_supComb hM hζ0 hζ1.summable b)
  -- The values `y i` at `b` of the combinations `ν i`.
  set y : ℕ → ℝ := fun i ↦ comb x (ν i) b
  have hy : Summable fun i ↦ (1 / 2 : ℝ) ^ (i + 1) * y i :=
    hasSum_half_pow_succ.summable.mul_of_abs_le fun i ↦ by
      simpa [(hν i).2.2.tsum_eq] using abs_comb_le hM (hν i).1 (hν i).2.2.summable b
  have hcomb : ∀ n, comb x (tailMix ν 0) b = ∑ i ∈ range n, (1 / 2) ^ (i + 1) * y i +
      ∑' i, (1 / 2 : ℝ) ^ (i + n + 1) * y (i + n) := fun n ↦ by
    rw [comb_tailMix_zero hM hν, ← hy.sum_add_tsum_nat_add n]
  -- Comparing the mixture with the near-minimizing combination `partialMix ν n + 2⁻ⁿ • ν n`.
  have hkey : ∀ n, (1 / 2 : ℝ) ^ n * y n ≤
      ∑' i, (1 / 2 : ℝ) ^ (i + n + 1) * y (i + n) + ε / 4 * ((1 / 2) ^ n) ^ 2 := fun n ↦ by
    have h₁ := comb_le_supComb (w := partialMix ν n + (1 / 2 : ℝ) ^ n • ν n) hM
      (fun m ↦ add_nonneg (partialMix_nonneg hν n m) (mul_nonneg (by positivity) ((hν n).1 m)))
      ((summable_partialMix hν n).add ((hν n).2.2.summable.mul_left _)) b
    have h₂ := hνmin n _ (tailMix_mem_tailWeights hν n)
    rw [partialMix_add_smul_tailMix hν, hsup, hcomb n] at h₂
    rw [comb_add_smul hM (summable_partialMix hν n) (hν n).2.2.summable,
      comb_partialMix hM hν] at h₁
    linarith
  obtain ⟨b', hb'⟩ := hc _ hζ0 hζ1
  have hfreq := frequently_sub_lt_of_le_tsum hε hy
    ((comb_tailMix_zero hM hν b).symm.trans_ge (hb'.trans (hbmax b'))) hkey
  refine ⟨b, frequently_atTop.2 fun N ↦ ?_⟩
  obtain ⟨i, hiN, hi⟩ := frequently_atTop.1 hfreq N
  obtain ⟨m, hmi, hm⟩ := exists_le_lt_of_lt_comb hM hν hi
  exact ⟨m, hiN.trans hmi, hm⟩

/-- **Simons' inequality.** Let `x n` be a sequence of real functions on `β`, uniformly bounded on
a set `s`. Suppose that every σ-convex combination `∑' n, w n * x n` (with `w n ≥ 0` and
`∑ w n = 1`) attains its supremum on `s`, and that this supremum is at least `c`. Then for every
`ε > 0` there is a point `b ∈ s` with `c - ε < x n b` for infinitely many `n`. In other words,
`sup_{b ∈ s} limsup_n x n b` is at least the infimum over σ-convex combinations of their suprema
on `s`. -/
theorem exists_frequently_sub_lt_of_isMaxOn_tsum {s : Set β} {x : ℕ → β → ℝ} {M c ε : ℝ}
    (hM : ∀ n, ∀ b ∈ s, |x n b| ≤ M)
    (hmax : ∀ w : ℕ → ℝ, (∀ n, 0 ≤ w n) → HasSum w 1 →
      ∃ b ∈ s, IsMaxOn (fun b ↦ ∑' n, w n * x n b) s b)
    (hc : ∀ w : ℕ → ℝ, (∀ n, 0 ≤ w n) → HasSum w 1 → ∃ b ∈ s, c ≤ ∑' n, w n * x n b)
    (hε : 0 < ε) : ∃ b ∈ s, ∃ᶠ n in atTop, c - ε < x n b := by
  obtain ⟨b, hb⟩ := exists_frequently_sub_lt_of_isMaxOn_univ_tsum
    (x := fun n (b : s) ↦ x n b) (fun n b ↦ hM n b b.property)
    (fun w hw0 hw ↦ (hmax w hw0 hw).elim fun b ⟨hb, hbmax⟩ ↦
      ⟨⟨b, hb⟩, fun b' _ ↦ hbmax b'.property⟩)
    (fun w hw0 hw ↦ (hc w hw0 hw).elim fun b ⟨hb, hcb⟩ ↦ ⟨⟨b, hb⟩, hcb⟩) hε
  exact ⟨b, b.property, hb⟩

end TauCeti
