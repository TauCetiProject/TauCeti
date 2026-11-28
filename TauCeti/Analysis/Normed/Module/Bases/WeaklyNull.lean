/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.RCLike.Basic
import TauCeti.Algebra.Order.Field.RatioMonotone
import TauCeti.Analysis.Normed.Module.Dual.Norming

/-!
# Basic subsequences of weakly null sequences

Let `u` be a sequence in a real or complex normed space which is weakly null, meaning that
`f (u k) → 0` for every continuous linear functional `f`, but which is not norm null: for some
`ε > 0`, `ε ≤ ‖u k‖` for infinitely many `k`. Then for every `B > 1`, `u` has a subsequence `v`,
all of whose terms have norm at least `ε`, which is a *basic sequence with basis constant at most
`B`*: initial segments of finite combinations are dominated by the whole combination,

`‖∑ i ∈ range m, a i • v i‖ ≤ B * ‖∑ i ∈ range n, a i • v i‖` for `m ≤ n`

(`TauCeti.exists_strictMono_norm_sum_range_le_mul`). In such a sequence each term of a
combination is controlled by every later partial sum,
`‖a m • v m‖ ≤ 2 * B * ‖∑ i ∈ range n, a i • v i‖` for `m < n`
(`TauCeti.norm_smul_le_two_mul_mul_norm_sum_range`).

The selection rests on **Mazur's lemma** (`TauCeti.exists_ge_norm_le_mul_norm_add_smul`): for
`ε > 0`, a finite-dimensional subspace `F`, a loss `A > 1` and any cutoff `N`, there is a term
`u k` with `k ≥ N` and norm at least `ε` such that `‖y‖ ≤ A * ‖y + c • u k‖` for all `y ∈ F` and
scalars `c`. Indeed `F` is normed, up to a small loss, by finitely many functionals
(`Submodule.exists_finset_strongDual_norming`), and these are almost zero at late terms. Choosing
the losses `Aⱼ = bⱼ / bⱼ₊₁` with `bⱼ = 1 + (B - 1) * (1 / 2) ^ j` makes
`‖∑ i ∈ range n, a i • v i‖ / bₙ` increasing in `n`
(`TauCeti.le_div_mul_of_forall_le_div_mul_succ`), which gives the constant `b₀ / 1 = B`.

If moreover the ambient space is complete and the finite subsums of the selected subsequence are
uniformly bounded, its closed linear span is isomorphic to `c₀`
(`ZeroAtInftyContinuousMap.antilipschitzWith_linearCombinationOfBoundedSubsums`); this is the
Bessaga–Pełczyński argument of `TauCeti.summable_of_forall_not_antilipschitzWith`.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Theorem 1.5.6 (Mazur's
  construction of basic sequences) and Proposition 1.5.4.
* J. Diestel, *Sequences and Series in Banach Spaces*, Chapter V.
-/

public section

open Filter Finset Topology

namespace TauCeti

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- **Mazur's lemma.** Let `u` be a weakly null sequence with `ε ≤ ‖u k‖` for infinitely many `k`,
where `ε > 0`. For a finite-dimensional subspace `F` and a loss `B > 1`, beyond any index `N` there
is a term `u k` with `ε ≤ ‖u k‖` such that `‖y‖ ≤ B * ‖y + c • u k‖` for all `y ∈ F` and all
scalars `c`. -/
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

/-- **Basic subsequences of weakly null sequences.** Let `u` be a weakly null sequence with
`ε ≤ ‖u k‖` for infinitely many `k`, where `ε > 0`. For every `B > 1`, `u` has a subsequence
`u ∘ φ`, all of whose terms have norm at least `ε`, which is a basic sequence with basis constant
at most `B`: for all scalars `a` and `m ≤ n`,
`‖∑ i ∈ range m, a i • u (φ i)‖ ≤ B * ‖∑ i ∈ range n, a i • u (φ i)‖`. -/
theorem exists_strictMono_norm_sum_range_le_mul {u : ℕ → X}
    (hu : ∀ f : StrongDual 𝕜 X, Tendsto (fun k ↦ f (u k)) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε)
    (huε : ∃ᶠ k in atTop, ε ≤ ‖u k‖) {B : ℝ} (hB : 1 < B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ j, ε ≤ ‖u (φ j)‖) ∧
      ∀ (a : ℕ → 𝕜) {m n : ℕ}, m ≤ n →
        ‖∑ i ∈ range m, a i • u (φ i)‖ ≤ B * ‖∑ i ∈ range n, a i • u (φ i)‖ := by
  classical
  -- The loss allowed at step `j` is `b j / b (j + 1) > 1`, for weights `b j` decreasing from `B`
  -- to `1`.
  set b : ℕ → ℝ := fun j ↦ 1 + (B - 1) * (1 / 2 : ℝ) ^ j with hb
  have hB1 : 0 < B - 1 := sub_pos.2 hB
  have hb1 (j : ℕ) : 1 ≤ b j := le_add_of_nonneg_right (by positivity)
  have hb0 (j : ℕ) : 0 < b j := zero_lt_one.trans_le (hb1 j)
  have hloss (j : ℕ) : 1 < b j / b (j + 1) := by
    rw [one_lt_div (hb0 _)]
    simp only [hb, pow_succ]
    have : 0 < (B - 1) * (1 / 2 : ℝ) ^ j := by positivity
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
  -- The weights lie between `1` and `B`, so the accumulated loss is at most `B`.
  have hbB : b m ≤ B * b n := by
    have : (B - 1) * (1 / 2 : ℝ) ^ m ≤ B - 1 :=
      mul_le_of_le_one_right hB1.le (pow_le_one₀ (by norm_num) (by norm_num))
    nlinarith [hb1 n]
  refine (le_div_mul_of_forall_le_div_mul_succ hb0 hw hmn).trans ?_
  gcongr
  exact (div_le_iff₀ (hb0 n)).2 hbB

/-- In a basic sequence with basis constant at most `B`, each term of a combination is controlled
by every later partial sum: if `‖∑ i ∈ range m, a i • v i‖ ≤ B * ‖∑ i ∈ range n, a i • v i‖`
whenever `m ≤ n`, then `‖a m • v m‖ ≤ 2 * B * ‖∑ i ∈ range n, a i • v i‖` whenever `m < n`. -/
theorem norm_smul_le_two_mul_mul_norm_sum_range {R V : Type*} [Semiring R]
    [SeminormedAddCommGroup V] [Module R V] {v : ℕ → V} {a : ℕ → R} {B : ℝ}
    (hbasic : ∀ {m n : ℕ}, m ≤ n → ‖∑ i ∈ range m, a i • v i‖ ≤ B * ‖∑ i ∈ range n, a i • v i‖)
    {m n : ℕ} (hmn : m < n) : ‖a m • v m‖ ≤ 2 * B * ‖∑ i ∈ range n, a i • v i‖ :=
  calc ‖a m • v m‖ = ‖∑ i ∈ range (m + 1), a i • v i - ∑ i ∈ range m, a i • v i‖ := by
        rw [sum_range_succ_sub_sum]
    _ ≤ ‖∑ i ∈ range (m + 1), a i • v i‖ + ‖∑ i ∈ range m, a i • v i‖ := norm_sub_le _ _
    _ ≤ B * ‖∑ i ∈ range n, a i • v i‖ + B * ‖∑ i ∈ range n, a i • v i‖ :=
        add_le_add (hbasic hmn) (hbasic hmn.le)
    _ = 2 * B * ‖∑ i ∈ range n, a i • v i‖ := by ring

end TauCeti
