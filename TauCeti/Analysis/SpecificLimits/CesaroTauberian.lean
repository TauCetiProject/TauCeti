/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Module

/-!
# The Hardy–Landau Tauberian theorem for Cesàro means

Convergence of a sequence implies convergence of its Cesàro means to the same limit
(`Filter.Tendsto.cesaro`, `Filter.Tendsto.cesaro_smul`). This file proves the Tauberian converse
of Hardy and Landau: if the partial sums `S_N = ∑_{n < N} a_n` of a series have Cesàro means
`N⁻¹ ∑_{i < N} S_i` converging to `S`, and the terms satisfy `n a_n ≥ -K`, then `S_N → S`. For
sequences in a real normed space the same holds under the two-sided condition `n ‖a_n‖ ≤ K`; no
completeness is needed, since the limit `S` is given.

Both theorems follow from a statement about the partial sums alone. A real sequence `s` is
*slowly decreasing* in Landau's sense if `s j - s k ≤ K (k - j) / j` whenever `0 < j ≤ k`; if its
Cesàro means converge to `S`, then so does `s`. The proof is Landau's: Cesàro convergence makes
the averages of `s` over a window `[N, N + m)` or `[N - m, N)` of length `m ≍ N / q` converge to
`S` (`TauCeti.tendsto_inv_smul_sum_Ico_of_cesaro`), while on such a window the slow decrease keeps
`s` within `K / q` (up to a bounded factor) of `s N` from one side. Letting `q → ∞` gives the
limit. In a normed space the two-sided condition `‖s k - s j‖ ≤ K (k - j) / j` needs only the
forward window.

## Main results

* `TauCeti.tendsto_inv_smul_sum_Icc_floor`: real-cutoff Cesàro mean for convergent sequences.
* `TauCeti.tendsto_inv_smul_sum_Ico_of_cesaro`: Cesàro convergence implies convergence of the
  averages over windows whose length is a fixed proportion of their right end.
* `TauCeti.tendsto_of_cesaro_of_sub_le`: Landau's theorem for slowly decreasing real sequences.
* `TauCeti.tendsto_of_cesaro_of_norm_sub_le`: its two-sided form in a real normed space.
* `TauCeti.tendsto_of_cesaro_of_mul_ge`: the Hardy–Landau theorem, one-sided form `n a_n ≥ -K`.
* `TauCeti.tendsto_of_cesaro_of_norm_mul_le`: the Hardy–Landau theorem in a real normed space,
  under `n ‖a_n‖ ≤ K`.

## References

* G. H. Hardy, *Divergent Series*, Oxford (1949), the Tauberian theorems for Cesàro means.
* E. Landau, *Über die Bedeutung einiger neuer Grenzwertsätze der Herren Hardy und Axer*,
  Prace Mat.-Fiz. 21 (1910), 97–177.
-/

public section

open Filter Finset Topology

namespace TauCeti

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- A sequence in a normed space converging to `l` has real-cutoff Cesàro mean
`x⁻¹ • ∑ n ∈ Icc 1 ⌊x⌋₊, a n → l`. -/
theorem tendsto_inv_smul_sum_Icc_floor {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a : ℕ → F} {l : F} (ha : Tendsto a atTop (𝓝 l)) :
    Tendsto (fun x : ℝ ↦ x⁻¹ • ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) atTop (𝓝 l) := by
  have hces : Tendsto (fun x : ℝ ↦ (⌊x⌋₊ : ℝ)⁻¹ • ∑ n ∈ Finset.range ⌊x⌋₊, a (n + 1))
      atTop (𝓝 l) :=
    (ha.comp (tendsto_add_atTop_nat 1)).cesaro_smul.comp tendsto_nat_floor_atTop
  have hprod : Tendsto (fun x : ℝ ↦
      ((⌊x⌋₊ : ℝ) / x) • ((⌊x⌋₊ : ℝ)⁻¹ • ∑ n ∈ Finset.range ⌊x⌋₊, a (n + 1))) atTop (𝓝 l) := by
    simpa using (tendsto_nat_floor_div_atTop (R := ℝ)).smul hces
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hfl : (⌊x⌋₊ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.floor_pos.mpr hx).ne'
  have hsum_eq : ∑ n ∈ Finset.range ⌊x⌋₊, a (n + 1) = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    exact Finset.sum_congr rfl fun n _ ↦ by rw [add_comm]
  rw [hsum_eq, smul_smul, div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ hfl, one_mul]

/-- **Window averages of a Cesàro convergent sequence.** If the Cesàro means of `u` converge to
`l`, then so do the averages of `u` over windows `[a, a + m)` whose left end `a` tends to infinity
and whose length `m` is at least a fixed proportion `C⁻¹` of their right end `a + m`. -/
theorem tendsto_inv_smul_sum_Ico_of_cesaro {ι : Type*} {F : Filter ι} {u : ℕ → E} {l : E}
    (hc : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • ∑ i ∈ range n, u i) atTop (𝓝 l))
    {a m : ι → ℕ} (ha : Tendsto a F atTop) {C : ℝ}
    (hC : ∀ᶠ x in F, (a x + m x : ℝ) ≤ C * m x) :
    Tendsto (fun x ↦ (m x : ℝ)⁻¹ • ∑ k ∈ Ico (a x) (a x + m x), u k) F (𝓝 l) := by
  set σ : ℕ → E := fun n ↦ (n : ℝ)⁻¹ • ∑ i ∈ range n, u i
  have hσ (n : ℕ) : (n : ℝ) • σ n = ∑ i ∈ range n, u i := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [σ, smul_smul, hn]
  have hσl := tendsto_iff_norm_sub_tendsto_zero.1 hc
  have ham : Tendsto (fun x ↦ a x + m x) F atTop :=
    tendsto_atTop_mono (fun x ↦ Nat.le_add_right _ _) ha
  have hlim : Tendsto (fun x ↦ C * (‖σ (a x + m x) - l‖ + ‖σ (a x) - l‖)) F (𝓝 0) := by
    simpa using ((hσl.comp ham).add (hσl.comp ha)).const_mul C
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero_norm' ?_ hlim)
  filter_upwards [hC, ha.eventually_ge_atTop 1] with x hx ha1
  have hm : (0 : ℝ) < m x := by
    rcases Nat.eq_zero_or_pos (m x) with h | h
    · simp only [h, Nat.cast_zero, add_zero, mul_zero, Nat.cast_nonpos] at hx
      omega
    · exact_mod_cast h
  set A : ℝ := ((a x + m x : ℕ) : ℝ)
  have hA : A ≤ C * m x := by simpa [A] using hx
  have heq : (m x : ℝ)⁻¹ • ∑ k ∈ Ico (a x) (a x + m x), u k - l =
      (m x : ℝ)⁻¹ • (A • (σ (a x + m x) - l) - (a x : ℝ) • (σ (a x) - l)) := by
    rw [sum_Ico_eq_sub _ (Nat.le_add_right _ _), ← hσ, ← hσ]
    conv_lhs => rw [← inv_smul_smul₀ hm.ne' l]
    rw [← smul_sub]
    congr 1
    simp only [A, Nat.cast_add]
    module
  rw [norm_norm, heq, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hm.le)]
  have haA : (a x : ℝ) ≤ A := by simp [A]
  calc (m x : ℝ)⁻¹ * ‖A • (σ (a x + m x) - l) - (a x : ℝ) • (σ (a x) - l)‖
      ≤ (m x : ℝ)⁻¹ * (A * (‖σ (a x + m x) - l‖ + ‖σ (a x) - l‖)) := by
        gcongr
        refine (norm_sub_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
          Real.norm_of_nonneg (by positivity), mul_add]
        gcongr
    _ ≤ C * (‖σ (a x + m x) - l‖ + ‖σ (a x) - l‖) := by
        rw [← mul_assoc]
        gcongr
        rwa [inv_mul_le_iff₀ hm, mul_comm]

/-- For `N ≥ p + 2`, the length `m = ⌊N / (p + 2)⌋` of the windows used below satisfies
`N ≤ 2 (p + 2) m`. -/
private lemma le_two_mul_mul_div {p N : ℕ} (hN : p + 2 ≤ N) :
    (N : ℝ) ≤ 2 * (p + 2) * (N / (p + 2) : ℕ) := by
  have h1 : 1 ≤ N / (p + 2) := (Nat.one_le_div_iff (by omega)).2 hN
  have h2 := Nat.div_add_mod N (p + 2)
  have h3 := Nat.mod_lt N (show 0 < p + 2 by omega)
  have : N ≤ 2 * (p + 2) * (N / (p + 2)) := by nlinarith
  exact_mod_cast this

/-- Cesàro convergence gives convergence of the averages over the forward windows
`[N, N + ⌊N / (p + 2)⌋)`. -/
private lemma tendsto_forward_window {u : ℕ → E} {l : E}
    (hc : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • ∑ i ∈ range n, u i) atTop (𝓝 l)) (p : ℕ) :
    Tendsto (fun N : ℕ ↦ ((N / (p + 2) : ℕ) : ℝ)⁻¹ • ∑ k ∈ Ico N (N + N / (p + 2)), u k)
      atTop (𝓝 l) := by
  refine tendsto_inv_smul_sum_Ico_of_cesaro hc tendsto_id (C := 2 * (p + 2) + 1) ?_
  filter_upwards [eventually_ge_atTop (p + 2)] with N hN
  have := le_two_mul_mul_div hN
  linarith

/-- Cesàro convergence gives convergence of the averages over the backward windows
`[N - ⌊N / (p + 2)⌋, N)`. -/
private lemma tendsto_backward_window {u : ℕ → E} {l : E}
    (hc : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • ∑ i ∈ range n, u i) atTop (𝓝 l)) (p : ℕ) :
    Tendsto (fun N : ℕ ↦ ((N / (p + 2) : ℕ) : ℝ)⁻¹ • ∑ k ∈ Ico (N - N / (p + 2)) N, u k)
      atTop (𝓝 l) := by
  have ha : Tendsto (fun N : ℕ ↦ N - N / (p + 2)) atTop atTop := by
    refine tendsto_atTop_atTop.2 fun b ↦ ⟨2 * b, fun N hN ↦ ?_⟩
    have : N / (p + 2) ≤ N / 2 := Nat.div_le_div_left (by omega) (by omega)
    omega
  have h := tendsto_inv_smul_sum_Ico_of_cesaro hc ha (m := fun N ↦ N / (p + 2))
    (C := 2 * (p + 2)) <| by
      filter_upwards [eventually_ge_atTop (p + 2)] with N hN
      have hle : N / (p + 2) ≤ N := Nat.div_le_self _ _
      rw [← Nat.cast_add, Nat.sub_add_cancel hle]
      exact le_two_mul_mul_div hN
  refine h.congr fun N ↦ ?_
  rw [Nat.sub_add_cancel (Nat.div_le_self _ _)]

/-- On a window `[a, a + m)` of positive length, the average of `u` is at most any upper bound
for its values. -/
private lemma inv_mul_sum_Ico_le {u : ℕ → ℝ} {c : ℝ} {a m : ℕ} (hm : 0 < m)
    (h : ∀ k ∈ Ico a (a + m), u k ≤ c) :
    (m : ℝ)⁻¹ • ∑ k ∈ Ico a (a + m), u k ≤ c := by
  simpa [expect_eq_sum_div_card, div_eq_inv_mul] using
    expect_le (nonempty_Ico.2 (Nat.lt_add_of_pos_right hm)) h

/-- On a window `[a, a + m)` of positive length, the average of `u` is at least any lower bound
for its values. -/
private lemma le_inv_mul_sum_Ico {u : ℕ → ℝ} {c : ℝ} {a m : ℕ} (hm : 0 < m)
    (h : ∀ k ∈ Ico a (a + m), c ≤ u k) :
    c ≤ (m : ℝ)⁻¹ • ∑ k ∈ Ico a (a + m), u k := by
  simpa [expect_eq_sum_div_card, div_eq_inv_mul] using
    le_expect (nonempty_Ico.2 (Nat.lt_add_of_pos_right hm)) h

/-- Some `p` makes `K / (p + 1)` smaller than a given `ε > 0`. -/
private lemma exists_div_add_one_lt (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℕ, K / (p + 1) < ε := by
  have h := (tendsto_const_div_atTop_nhds_zero_nat K).comp (tendsto_add_atTop_nat 1)
  obtain ⟨p, hp⟩ := (h.eventually (gt_mem_nhds hε)).exists
  exact ⟨p, by simpa using hp⟩

/-- On a window where `k - j` is at most `j / (p + 1)`, the slow-decrease bound
`K (k - j) / j` is at most `max K 0 / (p + 1)`. -/
private lemma mul_sub_div_le_max_div {K : ℝ} {p j k : ℕ} (hj : 0 < j) (hjk : j ≤ k)
    (hkj : ((k : ℝ) - j) * (p + 1) ≤ j) :
    K * (k - j) / j ≤ max K 0 / (p + 1) := by
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hkjR : (0 : ℝ) ≤ k - j := by simp [hjk]
  rw [div_le_div_iff₀ hjR (by positivity)]
  calc K * (k - j) * (p + 1) ≤ max K 0 * (((k : ℝ) - j) * (p + 1)) := by
        rw [← mul_assoc]; gcongr; exact le_max_left _ _
    _ ≤ max K 0 * j := by gcongr

/-- On the forward window `[N, N + ⌊N / (p + 2)⌋)`, the distance `k - N` is at most
`N / (p + 1)`. -/
private lemma sub_mul_le_of_mem_Ico_add {p N k : ℕ} (hk : k ∈ Ico N (N + N / (p + 2))) :
    ((k : ℝ) - N) * (p + 1) ≤ N := by
  rw [mem_Ico] at hk
  have hkN : (k : ℝ) < N + (N / (p + 2) : ℕ) := by exact_mod_cast hk.2
  have hmR : ((N / (p + 2) : ℕ) : ℝ) * (p + 2) ≤ N := by
    exact_mod_cast Nat.div_mul_le_self N (p + 2)
  nlinarith

/-- On the backward window `[N - ⌊N / (p + 2)⌋, N)`, the distance `N - k` is at most
`k / (p + 1)`. -/
private lemma sub_mul_le_of_mem_Ico_sub {p N k : ℕ} (hk : k ∈ Ico (N - N / (p + 2)) N) :
    ((N : ℝ) - k) * (p + 1) ≤ k := by
  rw [mem_Ico] at hk
  have hk' : ((N - N / (p + 2) : ℕ) : ℝ) ≤ k := by exact_mod_cast hk.1
  rw [Nat.cast_sub (Nat.div_le_self _ _)] at hk'
  have hmR : ((N / (p + 2) : ℕ) : ℝ) * (p + 2) ≤ N := by
    exact_mod_cast Nat.div_mul_le_self N (p + 2)
  nlinarith

/-- The lower half of Landau's theorem: comparing `s N` with its averages over the backward
windows `[N - m, N)`, a slowly decreasing sequence is eventually above every `b < S`. -/
private lemma eventually_lt_of_cesaro_of_sub_le {s : ℕ → ℝ} {S K b : ℝ}
    (hc : Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹ • ∑ i ∈ range N, s i) atTop (𝓝 S))
    (hs : ∀ j k : ℕ, 0 < j → j ≤ k → s j - s k ≤ K * (k - j) / j) (hb : b < S) :
    ∀ᶠ N in atTop, b < s N := by
  obtain ⟨p, hp⟩ := exists_div_add_one_lt (max K 0) (show 0 < (S - b) / 2 by linarith)
  filter_upwards [(tendsto_backward_window hc p).eventually
      (lt_mem_nhds (show b + (S - b) / 2 < S by linarith)),
    eventually_ge_atTop (p + 2)] with N hW hN
  set m := N / (p + 2)
  have hm : 0 < m := Nat.div_pos hN (by omega)
  have hle : N - m + m = N := Nat.sub_add_cancel (Nat.div_le_self _ _)
  have hm2 : 2 * m ≤ N := by
    have : m * (p + 2) ≤ N := Nat.div_mul_le_self N (p + 2)
    nlinarith
  have havg : (m : ℝ)⁻¹ • ∑ k ∈ Ico (N - m) (N - m + m), s k ≤ s N + max K 0 / (p + 1) :=
    inv_mul_sum_Ico_le hm fun k hk ↦ by
      rw [hle] at hk
      have hk' := mem_Ico.1 hk
      have := (hs k N (by omega) hk'.2.le).trans
        (mul_sub_div_le_max_div (p := p) (by omega) hk'.2.le (sub_mul_le_of_mem_Ico_sub hk))
      linarith
  rw [hle] at havg
  linarith

/-- The upper half of Landau's theorem: comparing `s N` with its averages over the forward
windows `[N, N + m)`, a slowly decreasing sequence is eventually below every `b > S`. -/
private lemma eventually_gt_of_cesaro_of_sub_le {s : ℕ → ℝ} {S K b : ℝ}
    (hc : Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹ • ∑ i ∈ range N, s i) atTop (𝓝 S))
    (hs : ∀ j k : ℕ, 0 < j → j ≤ k → s j - s k ≤ K * (k - j) / j) (hb : S < b) :
    ∀ᶠ N in atTop, s N < b := by
  obtain ⟨p, hp⟩ := exists_div_add_one_lt (max K 0) (show 0 < (b - S) / 2 by linarith)
  filter_upwards [(tendsto_forward_window hc p).eventually
      (gt_mem_nhds (show S < b - (b - S) / 2 by linarith)),
    eventually_ge_atTop (p + 2)] with N hW hN
  set m := N / (p + 2)
  have hm : 0 < m := Nat.div_pos hN (by omega)
  have havg : s N - max K 0 / (p + 1) ≤ (m : ℝ)⁻¹ • ∑ k ∈ Ico N (N + m), s k :=
    le_inv_mul_sum_Ico hm fun k hk ↦ by
      have := (hs N k (by omega) (mem_Ico.1 hk).1).trans
        (mul_sub_div_le_max_div (p := p) (by omega) (mem_Ico.1 hk).1 (sub_mul_le_of_mem_Ico_add hk))
      linarith
  linarith

/-- **Landau's Tauberian theorem for slowly decreasing sequences.** If the Cesàro means of a real
sequence `s` converge to `S` and `s j - s k ≤ K (k - j) / j` whenever `0 < j ≤ k`, then `s`
converges to `S`. -/
theorem tendsto_of_cesaro_of_sub_le {s : ℕ → ℝ} {S K : ℝ}
    (hc : Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹ * ∑ i ∈ range N, s i) atTop (𝓝 S))
    (hs : ∀ j k : ℕ, 0 < j → j ≤ k → s j - s k ≤ K * (k - j) / j) :
    Tendsto s atTop (𝓝 S) := by
  have hc' : Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹ • ∑ i ∈ range N, s i) atTop (𝓝 S) := by
    simpa only [smul_eq_mul] using hc
  exact tendsto_order.2 ⟨fun _ hb ↦ eventually_lt_of_cesaro_of_sub_le hc' hs hb,
    fun _ hb ↦ eventually_gt_of_cesaro_of_sub_le hc' hs hb⟩

/-- **Landau's Tauberian theorem in a real normed space.** If the Cesàro means of `s : ℕ → E`
converge to `S` and `‖s k - s j‖ ≤ K (k - j) / j` whenever `0 < j ≤ k`, then `s` converges
to `S`. -/
theorem tendsto_of_cesaro_of_norm_sub_le {s : ℕ → E} {S : E} {K : ℝ}
    (hc : Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹ • ∑ i ∈ range N, s i) atTop (𝓝 S))
    (hs : ∀ j k : ℕ, 0 < j → j ≤ k → ‖s k - s j‖ ≤ K * (k - j) / j) :
    Tendsto s atTop (𝓝 S) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨p, hp⟩ := exists_div_add_one_lt (max K 0) (half_pos hε)
  filter_upwards [Metric.tendsto_nhds.1 (tendsto_forward_window hc p) _ (half_pos hε),
    eventually_ge_atTop (p + 2)] with N hW hN
  set m := N / (p + 2)
  have hm : 0 < m := Nat.div_pos hN (by omega)
  have hmR' : (0 : ℝ) < m := by exact_mod_cast hm
  -- Each value on the window `[N, N + m)` lies within `max K 0 / (p + 1)` of `s N`.
  have hterm : ∀ k ∈ Ico N (N + m), ‖s N - s k‖ ≤ max K 0 / (p + 1) := by
    intro k hk
    rw [norm_sub_rev]
    exact (hs N k (by omega) (mem_Ico.1 hk).1).trans
      (mul_sub_div_le_max_div (p := p) (by omega) (mem_Ico.1 hk).1 (sub_mul_le_of_mem_Ico_add hk))
  have hdiff : s N - (m : ℝ)⁻¹ • ∑ k ∈ Ico N (N + m), s k =
      (m : ℝ)⁻¹ • ∑ k ∈ Ico N (N + m), (s N - s k) := by
    simp [sum_sub_distrib, smul_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hmR'.ne']
  have hclose : dist (s N) ((m : ℝ)⁻¹ • ∑ k ∈ Ico N (N + m), s k) ≤ max K 0 / (p + 1) := by
    rw [dist_eq_norm, hdiff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hmR'.le),
      inv_mul_le_iff₀ hmR']
    refine (norm_sum_le _ _).trans ?_
    simpa [Nat.card_Ico] using sum_le_card_nsmul _ _ _ hterm
  calc dist (s N) S ≤ dist (s N) ((m : ℝ)⁻¹ • ∑ k ∈ Ico N (N + m), s k) +
        dist ((m : ℝ)⁻¹ • ∑ k ∈ Ico N (N + m), s k) S := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (hclose.trans hp.le) hW
    _ = ε := add_halves ε

/-- A sum of terms `b n` with `n b n ≤ K` over `j ≤ n < k`, `0 < j`, is at most
`K (k - j) / j`. -/
private lemma sum_Ico_le_of_mul_le {b : ℕ → ℝ} {K : ℝ} (hb : ∀ n : ℕ, n * b n ≤ K) {j k : ℕ}
    (hj : 0 < j) (hjk : j ≤ k) :
    ∑ n ∈ Ico j k, b n ≤ K * (k - j) / j := by
  have hK : 0 ≤ K := by simpa using hb 0
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hterm : ∀ n ∈ Ico j k, b n ≤ K / j := by
    intro n hn
    have hnj : (j : ℝ) ≤ n := by exact_mod_cast (mem_Ico.1 hn).1
    calc b n ≤ K / n := by rw [le_div_iff₀' (hjR.trans_le hnj)]; exact hb n
      _ ≤ K / j := div_le_div_of_nonneg_left hK hjR hnj
  refine (sum_le_card_nsmul _ _ _ hterm).trans_eq ?_
  rw [Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hjk]
  ring

/-- **The Hardy–Landau Tauberian theorem.** If the Cesàro means `N⁻¹ ∑_{i < N} S_i` of the
partial sums `S_N = ∑_{n < N} a_n` of a real sequence converge to `S`, and `n a_n ≥ -K` for every
`n`, then the partial sums converge to `S`. -/
theorem tendsto_of_cesaro_of_mul_ge {a : ℕ → ℝ} {S K : ℝ}
    (hc : Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹ * ∑ i ∈ range N, ∑ n ∈ range i, a n)
      atTop (𝓝 S))
    (ha : ∀ n : ℕ, -K ≤ n * a n) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ range N, a n) atTop (𝓝 S) := by
  refine tendsto_of_cesaro_of_sub_le (K := K) hc fun j k hj hjk ↦ ?_
  have h := sum_Ico_le_of_mul_le (b := fun n ↦ -a n) (K := K)
    (fun n ↦ by simpa using neg_le_neg (ha n)) hj hjk
  simp only [sum_Ico_eq_sub _ hjk, sum_neg_distrib] at h
  linarith

/-- **The Hardy–Landau Tauberian theorem in a real normed space.** If the Cesàro means of the
partial sums of `a : ℕ → E` converge to `S` and `n ‖a n‖ ≤ K` for every `n`, then the partial
sums converge to `S`. -/
theorem tendsto_of_cesaro_of_norm_mul_le {a : ℕ → E} {S : E} {K : ℝ}
    (hc : Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹ • ∑ i ∈ range N, ∑ n ∈ range i, a n)
      atTop (𝓝 S))
    (ha : ∀ n : ℕ, n * ‖a n‖ ≤ K) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ range N, a n) atTop (𝓝 S) := by
  refine tendsto_of_cesaro_of_norm_sub_le (K := K) hc fun j k hj hjk ↦ ?_
  rw [← sum_Ico_eq_sub _ hjk]
  exact (norm_sum_le _ _).trans (sum_Ico_le_of_mul_le ha hj hjk)

end TauCeti
