/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.RCLike.Basic
import TauCeti.Algebra.Order.Field.RatioMonotone
import TauCeti.Analysis.Normed.Operator.Norming

/-!
# Basic subsequences of weakly null sequences

Let `u` be a sequence in a real or complex normed space which is weakly null, meaning that
`f (u k) → 0` for every continuous linear functional `f`, but which is not norm null. Then `u` has
a subsequence `v` which is a *basic sequence with basis constant at most `2`*: initial segments of
finite combinations are dominated by the whole combination,

`‖∑ i ∈ range m, a i • v i‖ ≤ 2 * ‖∑ i ∈ range n, a i • v i‖` for `m ≤ n`

(`TauCeti.exists_strictMono_norm_sum_range_le_two_mul`). The subsequence can moreover be chosen
with norms bounded below by any `ε` with `ε ≤ ‖u k‖` for infinitely many `k`.

The selection rests on **Mazur's lemma** (`TauCeti.exists_ge_norm_le_mul_norm_add_smul`): for a
finite-dimensional subspace `F`, a loss `B > 1` and any cutoff `N`, there is a term `u k` with
`k ≥ N` and norm at least `ε` such that `‖y‖ ≤ B * ‖y + c • u k‖` for all `y ∈ F` and scalars `c`.
Indeed `F` is normed, up to a small loss, by finitely many functionals, and these are almost zero
at late terms. Choosing the losses `Bⱼ = bⱼ / bⱼ₊₁` with `bⱼ = 1 + (1 / 2) ^ j` makes
`‖∑ i ∈ range n, a i • v i‖ / bₙ` increasing in `n`
(`TauCeti.le_div_mul_of_forall_le_div_mul_succ`), which gives the constant `b₀ / 1 = 2`.

If moreover the finite subsums of the selected subsequence are uniformly bounded, its closed
linear span is isomorphic to `c₀`; this is the Bessaga–Pełczyński argument of
`TauCeti.summable_of_forall_not_antilipschitzWith`.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Theorem 1.5.6 (Mazur's
  construction of basic sequences) and Proposition 1.5.4.
* J. Diestel, *Sequences and Series in Banach Spaces*, Chapter V.
-/

public section

open Filter Finset Topology

namespace TauCeti

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- **Mazur's lemma.** Let `u` be a weakly null sequence with `ε ≤ ‖u k‖` for infinitely many `k`.
For a finite-dimensional subspace `F` and a loss `B > 1`, beyond any index `N` there is a term
`u k` with `ε ≤ ‖u k‖` such that `‖y‖ ≤ B * ‖y + c • u k‖` for all `y ∈ F` and all scalars `c`. -/
theorem exists_ge_norm_le_mul_norm_add_smul {u : ℕ → X}
    (hu : ∀ f : StrongDual 𝕜 X, Tendsto (fun k ↦ f (u k)) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε)
    (huε : ∃ᶠ k in atTop, ε ≤ ‖u k‖) (F : Submodule 𝕜 X) [FiniteDimensional 𝕜 F] {B : ℝ}
    (hB : 1 < B) (N : ℕ) :
    ∃ k ≥ N, ε ≤ ‖u k‖ ∧ ∀ y ∈ F, ∀ c : 𝕜, ‖y‖ ≤ B * ‖y + c • u k‖ := by
  obtain ⟨A, hA, hAB⟩ := exists_between hB
  have hA0 : 0 < A := zero_lt_one.trans hA
  obtain ⟨t, ht, hnorm⟩ := F.exists_finset_strongDual_norming hA
  -- The tests norming `F` are small at late terms.
  set η := ε * (B - A) / (2 * A * B) with hη
  have hη0 : 0 < η := by rw [hη]; have := sub_pos.2 hAB; positivity
  have hsmall : ∀ᶠ k in atTop, ∀ g ∈ t, ‖g (u k)‖ ≤ η :=
    (eventually_all_finset t).2 fun g _ ↦
      (tendsto_zero_iff_norm_tendsto_zero.1 (hu g)).eventually (eventually_le_nhds hη0)
  obtain ⟨k, hεk, hk, hNk⟩ := (huε.and_eventually (hsmall.and (eventually_ge_atTop N))).exists
  refine ⟨k, hNk, hεk, fun y hy c ↦ ?_⟩
  rcases le_or_gt (2 * ‖y‖) (‖c‖ * ‖u k‖) with hc | hc
  · -- A large coefficient dominates `y`.
    have : ‖c • u k‖ ≤ ‖y + c • u k‖ + ‖y‖ := by simpa using norm_sub_le (y + c • u k) y
    rw [norm_smul] at this
    nlinarith [norm_nonneg y, norm_nonneg (y + c • u k)]
  · -- Otherwise a norming test sees `y` through the perturbation.
    obtain ⟨g, hgt, hyg⟩ := hnorm y hy
    have hgy : ‖g y‖ ≤ ‖y + c • u k‖ + ‖c‖ * η := by
      have hsplit : g y = g (y + c • u k) - c * g (u k) := by simp
      calc ‖g y‖ ≤ ‖g (y + c • u k)‖ + ‖c * g (u k)‖ := by rw [hsplit]; exact norm_sub_le _ _
        _ ≤ ‖y + c • u k‖ + ‖c‖ * η := by
          rw [norm_mul]
          gcongr
          · exact (g.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (ht g hgt))
          · exact hk g hgt
    have hcε : ‖c‖ * ε ≤ 2 * ‖y‖ := (mul_le_mul_of_nonneg_left hεk (norm_nonneg c)).trans hc.le
    have hB0 : 0 < B := hA0.trans hAB
    have hcη : A * (‖c‖ * η) ≤ (1 - A / B) * ‖y‖ := by
      rw [hη, one_sub_div hB0.ne']
      calc A * (‖c‖ * (ε * (B - A) / (2 * A * B))) = (‖c‖ * ε) * ((B - A) / B) / 2 := by
            field_simp
        _ ≤ (2 * ‖y‖) * ((B - A) / B) / 2 := by gcongr
        _ = (B - A) / B * ‖y‖ := by ring
    have key : A / B * ‖y‖ ≤ A * ‖y + c • u k‖ := by nlinarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hB0] at key
    nlinarith

/-- **Basic subsequences of weakly null sequences.** A weakly null sequence `u` with `ε ≤ ‖u k‖`
for infinitely many `k` has a subsequence `u ∘ φ`, all of whose terms have norm at least `ε`,
which is a basic sequence with basis constant at most `2`: for all scalars `a` and `m ≤ n`,
`‖∑ i ∈ range m, a i • u (φ i)‖ ≤ 2 * ‖∑ i ∈ range n, a i • u (φ i)‖`. -/
theorem exists_strictMono_norm_sum_range_le_two_mul {u : ℕ → X}
    (hu : ∀ f : StrongDual 𝕜 X, Tendsto (fun k ↦ f (u k)) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε)
    (huε : ∃ᶠ k in atTop, ε ≤ ‖u k‖) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ j, ε ≤ ‖u (φ j)‖) ∧
      ∀ (a : ℕ → 𝕜) {m n : ℕ}, m ≤ n →
        ‖∑ i ∈ range m, a i • u (φ i)‖ ≤ 2 * ‖∑ i ∈ range n, a i • u (φ i)‖ := by
  classical
  -- The loss allowed at step `j` is `b j / b (j + 1) > 1`, for weights `b j` decreasing to `1`.
  set b : ℕ → ℝ := fun j ↦ 1 + (1 / 2 : ℝ) ^ j with hb
  have hloss (j : ℕ) : 1 < b j / b (j + 1) := by
    rw [one_lt_div (by positivity)]
    simp only [hb, pow_succ]
    have : 0 < (1 / 2 : ℝ) ^ j := by positivity
    linarith
  have hstep (j : ℕ) (s : Finset ℕ) (N : ℕ) : ∃ k ≥ N, ε ≤ ‖u k‖ ∧
      ∀ y ∈ Submodule.span 𝕜 (u '' s), ∀ c : 𝕜, ‖y‖ ≤ b j / b (j + 1) * ‖y + c • u k‖ := by
    have := FiniteDimensional.span_of_finite 𝕜 (s.finite_toSet.image u)
    exact exists_ge_norm_le_mul_norm_add_smul hu hε huε _ (hloss j) N
  choose next hge hnorm hnext using hstep
  -- Record the indices chosen so far and the next admissible index.
  let q : ℕ → Finset ℕ × ℕ :=
    Nat.rec (∅, 0) fun j p ↦ (insert (next j p.1 p.2) p.1, next j p.1 p.2 + 1)
  let φ : ℕ → ℕ := fun j ↦ next j (q j).1 (q j).2
  have hq (j : ℕ) : q (j + 1) = (insert (φ j) (q j).1, φ j + 1) := rfl
  have hq₁ (j : ℕ) : (q j).1 = (range j).image φ := by
    induction j with
    | zero => rfl
    | succ j ih => rw [hq, ih, range_add_one, image_insert]
  have hφ : StrictMono φ := strictMono_nat_of_lt_succ fun j ↦ by
    have := hge (j + 1) (q (j + 1)).1 (q (j + 1)).2
    rw [hq] at this
    exact this
  refine ⟨φ, hφ, fun j ↦ hnorm _ _ _, fun a m n hmn ↦ ?_⟩
  -- Each partial sum lies in the span of the terms chosen before the next one.
  have hw (n : ℕ) : ‖∑ i ∈ range n, a i • u (φ i)‖ ≤
      b n / b (n + 1) * ‖∑ i ∈ range (n + 1), a i • u (φ i)‖ := by
    have hmem : ∑ i ∈ range n, a i • u (φ i) ∈ Submodule.span 𝕜 (u '' ((q n).1 : Set ℕ)) := by
      refine Submodule.sum_mem _ fun i hi ↦ Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      rw [hq₁]
      exact ⟨φ i, by simpa using mem_image_of_mem φ hi, rfl⟩
    rw [sum_range_succ]
    exact hnext n (q n).1 (q n).2 _ hmem (a n)
  -- The weights lie between `1` and `2`, so the accumulated loss is at most `2`.
  have hb1 (j : ℕ) : 1 ≤ b j := le_add_of_nonneg_right (by positivity)
  have hb2 : b m ≤ 2 * b n := by
    have : (1 / 2 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith [hb1 n]
  refine (le_div_mul_of_forall_le_div_mul_succ (fun j ↦ by positivity) hw hmn).trans ?_
  gcongr
  exact (div_le_iff₀ (zero_lt_one.trans_le (hb1 n))).2 hb2

end TauCeti
