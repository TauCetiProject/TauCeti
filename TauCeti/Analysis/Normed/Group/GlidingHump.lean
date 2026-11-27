/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# A gliding hump lemma for absolutely summable rows

Let `a : ℕ → ℕ → E` be an infinite matrix with entries in a Banach space whose rows are absolutely
summable. Suppose that the row sums over every set of columns tend to zero:
`∑ₖ∈A a j k → 0` as `j → ∞` for every `A ⊆ ℕ`. Then the diagonal tends to zero:
`a j j → 0` (`TauCeti.tendsto_diag_zero_of_forall_tendsto_tsum_indicator`).

This is the diagonal form of the Hahn–Schur theorem. It is the combinatorial step in the
Orlicz–Pettis theorem, where `a j k = x*ⱼ (uₖ)` for a weak-star null sequence of functionals `x*ⱼ`
and a weakly subseries summable sequence `uₖ`.

The proof is the classical *gliding hump* argument. If `‖a j j‖ ≥ ε` for infinitely many `j`, one
chooses rows `j₀ < j₁ < ⋯` among them such that row `jᵢ` is small on the earlier columns
`j₀, …, jᵢ₋₁` (possible because each column tends to zero, as the case of a singleton `A` shows)
and has small tail beyond `jᵢ₊₁` (possible because the rows are absolutely summable). On the set
`A = {j₀, j₁, …}` the sum of row `jᵢ` then stays within `ε / 2` of the diagonal entry `a jᵢ jᵢ`,
contradicting the hypothesis for this `A`.

## References

* J. Diestel, *Sequences and Series in Banach Spaces*, Graduate Texts in Mathematics 92,
  Springer, 1984, Chapter VII (the gliding hump and the Hahn–Schur theorem).
* J. Diestel and J. J. Uhl, Jr., *Vector Measures*, Mathematical Surveys 15, American
  Mathematical Society, 1977, Chapter I, §4.
-/

public section

open Filter Finset Set Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E]

/-- The rows of the gliding hump: if every column tends to zero and the diagonal entries are at
least `ε` infinitely often, then there are rows `j 0 < j 1 < ⋯` with diagonal entries at least
`ε`, whose entries in the earlier chosen columns have norm sum below `δ`, and each lying beyond
the cut-offs `N (j l)` of the earlier ones. -/
private theorem exists_strictMono_glidingHump {a : ℕ → ℕ → E} {ε δ : ℝ} (hδ : 0 < δ)
    (hcol : ∀ k, Tendsto (fun j ↦ a j k) atTop (𝓝 0)) (hfreq : ∃ᶠ j in atTop, ε ≤ ‖a j j‖)
    (N : ℕ → ℕ) :
    ∃ j : ℕ → ℕ, StrictMono j ∧ (∀ i, ε ≤ ‖a (j i) (j i)‖) ∧
      (∀ i, ∑ l ∈ range i, ‖a (j i) (j l)‖ < δ) ∧ ∀ l i, l < i → N (j l) ≤ j i := by
  -- Each new row `y` lies beyond the earlier rows `x` and their cut-offs `N x`, and its entry in
  -- column `x` is below `δ / 4 * (1 / 2) ^ x`; this is possible since every column tends to zero.
  obtain ⟨j, hdiag, hr⟩ := exists_seq_of_forall_finset_exists (fun y ↦ ε ≤ ‖a y y‖)
    (fun x y ↦ x < y ∧ N x ≤ y ∧ ‖a y x‖ < δ / 4 * (1 / 2) ^ x) fun S _ ↦ by
      have h : ∀ᶠ y in atTop, ∀ x ∈ S, x < y ∧ N x ≤ y ∧ ‖a y x‖ < δ / 4 * (1 / 2) ^ x :=
        S.eventually_all.2 fun x _ ↦ (eventually_gt_atTop x).and ((eventually_ge_atTop (N x)).and
          ((hcol x).norm.eventually (gt_mem_nhds (by rw [norm_zero]; positivity))))
      exact (hfreq.and_eventually h).exists
  have hj : StrictMono j := fun l i hli ↦ (hr l i hli).1
  refine ⟨j, hj, hdiag, fun i ↦ ?_, fun l i hli ↦ (hr l i hli).2.1⟩
  calc ∑ l ∈ range i, ‖a (j i) (j l)‖ ≤ ∑ l ∈ range i, δ / 4 * (1 / 2) ^ l := by
        refine sum_le_sum fun l hl ↦ (hr l i (mem_range.1 hl)).2.2.le.trans ?_
        exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num)
          (hj.id_le l)) (by positivity)
    _ = δ / 4 * ∑ l ∈ range i, (1 / 2 : ℝ) ^ l := (mul_sum _ _ _).symm
    _ ≤ δ / 4 * 2 := by gcongr; exact sum_geometric_two_le i
    _ < δ := by linarith

/-- A subfamily of a row indexed beyond the cut-off `N` is bounded by the tail of the row from
`N` on. -/
private theorem norm_tsum_comp_le_tsum_norm_add {r : ℕ → E} (hr : Summable fun k ↦ ‖r k‖)
    {φ : ℕ → ℕ} (hφ : Function.Injective φ) {N : ℕ} (hN : ∀ l, N ≤ φ l) :
    ‖∑' l, r (φ l)‖ ≤ ∑' k, ‖r (k + N)‖ := by
  have hrφ : Summable fun l ↦ ‖r (φ l)‖ := hr.comp_injective hφ
  have hinj : Function.Injective fun l ↦ φ l - N := fun l l' h ↦
    hφ (by have := hN l; have := hN l'; simp only at h; omega)
  refine (norm_tsum_le_tsum_norm hrφ).trans (hrφ.tsum_le_tsum_of_inj _ hinj
    (fun _ _ ↦ norm_nonneg _) (fun l ↦ by rw [Nat.sub_add_cancel (hN l)]) ?_)
  exact (summable_nat_add_iff (f := fun k ↦ ‖r k‖) N).2 hr

/-- **Gliding hump lemma.** If the rows of a matrix with entries in a Banach space are absolutely
summable and the row sums over every fixed set of columns tend to zero, then the diagonal entries
tend to zero. -/
theorem tendsto_diag_zero_of_forall_tendsto_tsum_indicator [CompleteSpace E] {a : ℕ → ℕ → E}
    (ha : ∀ j, Summable fun k ↦ ‖a j k‖)
    (h : ∀ A : Set ℕ, Tendsto (fun j ↦ ∑' k, A.indicator (a j) k) atTop (𝓝 0)) :
    Tendsto (fun j ↦ a j j) atTop (𝓝 0) := by
  by_contra hne
  obtain ⟨ε, hε, hfreq⟩ : ∃ ε > 0, ∃ᶠ j in atTop, ε ≤ ‖a j j‖ := by
    obtain ⟨s, hs, hfs⟩ := not_tendsto_iff_exists_frequently_notMem.1 hne
    obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 hs
    exact ⟨ε, hε, hfs.mono fun j hj ↦ not_lt.1 fun hlt ↦ hj (hεs (mem_ball_zero_iff.2 hlt))⟩
  -- Each column tends to zero: take `A` to be a singleton.
  have hcol (k : ℕ) : Tendsto (fun j ↦ a j k) atTop (𝓝 0) := by
    simpa using h {k}
  -- The tail of row `j` from `N j` on has norm sum below `ε / 4`.
  have htail (j : ℕ) : ∃ N, ∑' k, ‖a j (k + N)‖ < ε / 4 :=
    ((tendsto_sum_nat_add fun k ↦ ‖a j k‖).eventually (gt_mem_nhds (by positivity))).exists
  choose N hN using htail
  obtain ⟨j, hj, hdiag, hhead, hNj⟩ :=
    exists_strictMono_glidingHump (by positivity : 0 < ε / 4) hcol hfreq N
  -- On `A = range j`, the sum of row `j i` is the diagonal entry `a (j i) (j i)` plus the
  -- contributions `F` of the earlier and `T` of the later columns, each of norm below `ε / 4`.
  have hbig (i : ℕ) : ε / 2 ≤ ‖∑' k, (range j).indicator (a (j i)) k‖ := by
    rw [← _root_.tsum_subtype, tsum_range _ hj.injective]
    have hb : Summable fun l ↦ ‖a (j i) (j l)‖ := (ha (j i)).comp_injective hj.injective
    rw [← hb.of_norm.sum_add_tsum_nat_add (i + 1), sum_range_succ]
    set F := ∑ l ∈ range i, a (j i) (j l)
    set T := ∑' l, a (j i) (j (l + (i + 1)))
    have hF : ‖F‖ < ε / 4 := (norm_sum_le _ _).trans_lt (hhead i)
    have hT : ‖T‖ < ε / 4 :=
      (norm_tsum_comp_le_tsum_norm_add (ha (j i)) (hj.injective.comp (add_left_injective _))
        fun l ↦ hNj i (l + (i + 1)) (by omega)).trans_lt (hN (j i))
    have htri : ‖a (j i) (j i)‖ ≤ ‖F + a (j i) (j i) + T‖ + ‖F‖ + ‖T‖ := by
      calc ‖a (j i) (j i)‖ = ‖F + a (j i) (j i) + T - F - T‖ := by congr 1; abel
        _ ≤ ‖F + a (j i) (j i) + T - F‖ + ‖T‖ := norm_sub_le _ _
        _ ≤ ‖F + a (j i) (j i) + T‖ + ‖F‖ + ‖T‖ := by gcongr; exact norm_sub_le _ _
    linarith [hdiag i]
  have hlim := ((h (range j)).comp hj.tendsto_atTop).norm
  rw [norm_zero] at hlim
  obtain ⟨i, hi⟩ := (hlim.eventually (gt_mem_nhds (half_pos hε))).exists
  exact (hbig i).not_gt hi

end TauCeti
