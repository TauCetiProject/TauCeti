/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Separated words for theta-lift chains

The inner entries of a weight word are obtained by shifting a common baseline by either zero or
one letter step, after subtracting a half. The same bit is used at all places: two distinct words
therefore differ at a common index at every place. Counting these words gives enough copies of
the full source spaces to meet the redundancy bound used in the frame comparison.

The choice of inner weights and the use of the sum of full source ranks follow Levent Alpöge's
`Formalism.MainNotions.S.StandingNumericalData` and `Formalism.MainNotions.Lnk.frame_at_of`
(<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open Filter Real
open scoped BigOperators

namespace TauCeti

/-- The inner weight at position `i` and place `τ`, before attaching the two fixed end weights. -/
noncomputable def thetaChainInnerWeight {ι : Type*} {n : ℕ} (v : Fin n → ι → ℝ) (Δ : ℝ)
    (w : Fin n → Bool) (i : Fin n) (τ : ι) : ℝ :=
  v i τ - 1 / 2 - (if w i then Δ else 0)

/-- The weight is the common baseline less a half and, for bit `true`, one letter step. -/
theorem thetaChainInnerWeight_def {ι : Type*} {n : ℕ} (v : Fin n → ι → ℝ) (Δ : ℝ)
    (w : Fin n → Bool) (i : Fin n) (τ : ι) :
    thetaChainInnerWeight v Δ w i τ = v i τ - 1 / 2 - (if w i then Δ else 0) := (rfl)

/-- Distinct words are a letter step apart at some common index at every place. -/
theorem exists_abs_thetaChainInnerWeight_sub_eq {ι : Type*} {n : ℕ} {v : Fin n → ι → ℝ}
    {Δ : ℝ} {w w' : Fin n → Bool} (hΔ : 0 ≤ Δ) (hw : w ≠ w') :
    ∃ i, ∀ τ, |thetaChainInnerWeight v Δ w i τ - thetaChainInnerWeight v Δ w' i τ| = Δ := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ w' i := not_forall.mp (fun h ↦ hw (funext h))
  refine ⟨i, fun τ ↦ ?_⟩
  cases h : w i <;> cases h' : w' i
  · exact (hi (h.trans h'.symm)).elim
  · simp [thetaChainInnerWeight_def, h, h', abs_of_nonneg hΔ]
  · rw [abs_sub_comm]
    simp [thetaChainInnerWeight_def, h, h', abs_of_nonneg hΔ]
  · exact (hi (h.trans h'.symm)).elim

/-- A baseline gap of at least four steps leaves a gap of at least three steps in every word. -/
theorem three_mul_le_thetaChainInnerWeight_sub {ι : Type*} {n : ℕ} {v : Fin n → ι → ℝ}
    {Δ : ℝ} (hΔ : 0 ≤ Δ) (w : Fin n → Bool) {i j : Fin n} {τ : ι}
    (hv : 4 * Δ ≤ v i τ - v j τ) :
    3 * Δ ≤ thetaChainInnerWeight v Δ w i τ - thetaChainInnerWeight v Δ w j τ := by
  cases h : w i <;> cases h' : w j <;> simp [thetaChainInnerWeight_def, h, h'] <;> linarith

/-- The exact capacity of the inner binary words of a rank-`k` chain, in logarithmic form. -/
theorem exists_thetaChainWordCode_iff {k : ℕ} {C₀ Γ x c : ℝ}
    (hC₀ : 0 < C₀) (hΓ : Γ ≠ 0) (hx : 0 < x) :
    (∃ W : Finset (Fin (k - 2) → Bool), W.card = ⌈C₀ * Γ ^ 2 * x ^ c⌉₊) ↔
      log C₀ + 2 * log Γ + c * log x ≤ ((k - 2 : ℕ) : ℝ) * log 2 := by
  classical
  have hexists : (∃ W : Finset (Fin (k - 2) → Bool), W.card = ⌈C₀ * Γ ^ 2 * x ^ c⌉₊) ↔
      ⌈C₀ * Γ ^ 2 * x ^ c⌉₊ ≤ 2 ^ (k - 2) := by
    simpa using (Finset.le_card_iff_exists_subset_card
      (s := Finset.univ (α := Fin (k - 2) → Bool)) (n := ⌈C₀ * Γ ^ 2 * x ^ c⌉₊)).symm
  rw [hexists, Nat.ceil_le, Nat.cast_pow, Nat.cast_ofNat]
  have hpos : 0 < C₀ * Γ ^ 2 := mul_pos hC₀ (sq_pos_of_ne_zero hΓ)
  rw [← log_le_log_iff (mul_pos hpos (rpow_pos_of_pos hx _)) (by positivity),
    log_mul hpos.ne' (rpow_pos_of_pos hx _).ne', log_mul hC₀.ne' (pow_ne_zero _ hΓ),
    log_pow, log_rpow hx, log_pow, Nat.cast_ofNat]

/-- The word count follows eventually from the rank budget `SizeW`. The quantity dominating
`x ^ ε` is `q = m ^ 5 * |A| * x ^ ε`, and the frame parameter is `exp (2 * CΓ * q)`. The
threshold is independent of `q` and the chosen rank `k`. -/
theorem eventually_exists_thetaChainWordCode {ε C₀ CΓ Cw c : ℝ}
    (hε : 0 < ε) (hCw : 4 * CΓ / log 2 < Cw) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℝ) (k : ℕ), x ^ ε ≤ q → Cw * q ≤ (k : ℝ) →
      ∃ W : Finset (Fin (k - 2) → Bool), W.card = ⌈C₀ * exp (2 * CΓ * q) ^ 2 * x ^ c⌉₊ := by
  let d := Cw * log 2 - 4 * CΓ
  have hlog : 0 < log 2 := log_pos (by norm_num)
  have hd : 0 < d := sub_pos.mpr ((div_lt_iff₀ hlog).mp hCw)
  have hsmall : (fun x : ℝ ↦ log C₀ + 2 * log 2 + c * log x) =o[atTop] fun x ↦ x ^ ε :=
    (Asymptotics.isLittleO_const_left.mpr
      (Or.inr (tendsto_norm_atTop_atTop.comp (tendsto_rpow_atTop hε)))).add
      ((isLittleO_log_rpow_atTop hε).const_mul_left c)
  filter_upwards [eventually_gt_atTop (0 : ℝ), hsmall.bound hd] with x hx hb
  intro q k hq hk
  by_cases hC₀ : 0 < C₀
  · apply (exists_thetaChainWordCode_iff hC₀ (exp_pos _).ne' hx).2
    have hcost : log C₀ + 2 * log 2 + c * log x ≤ d * q := calc
      _ ≤ ‖log C₀ + 2 * log 2 + c * log x‖ := le_abs_self _
      _ ≤ d * x ^ ε := by simpa only [Real.norm_eq_abs, abs_of_pos (rpow_pos_of_pos hx _)] using hb
      _ ≤ d * q := mul_le_mul_of_nonneg_left hq hd.le
    have hrank := mul_le_mul_of_nonneg_right hk hlog.le
    have hsub : (k : ℝ) - 2 ≤ ((k - 2 : ℕ) : ℝ) := by
      have h : k ≤ (k - 2) + 2 := by omega
      exact sub_le_iff_le_add.mpr (by exact_mod_cast h)
    rw [log_exp]
    calc
      _ ≤ ((k : ℝ) - 2) * log 2 := by dsimp only [d] at hcost; nlinarith only [hcost, hrank]
      _ ≤ _ := mul_le_mul_of_nonneg_right hsub hlog.le
  · refine ⟨∅, ?_⟩
    rw [Finset.card_empty, eq_comm, Nat.ceil_eq_zero]
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hC₀) (sq_nonneg _)) (by positivity)

/-- The per-word full-rank lower bound supplies at least `r * D` total rank when the code has
at least `⌈C₀ * Γ ^ 2 * r⌉₊` words. For the chain frame, `r` is `x ^ c`. -/
theorem mul_le_sum_thetaChainWordRanks {k : ℕ} {C₀ Γ r D : ℝ}
    (W : Finset (Fin (k - 2) → Bool)) (d : (Fin (k - 2) → Bool) → ℕ)
    (hscale : 0 < C₀ * Γ ^ 2) (hD : 0 ≤ D) (hW : ⌈C₀ * Γ ^ 2 * r⌉₊ ≤ W.card)
    (hd : ∀ w ∈ W, D / (C₀ * Γ ^ 2) ≤ (d w : ℝ)) :
    r * D ≤ ∑ w ∈ W, (d w : ℝ) := calc
  r * D = (C₀ * Γ ^ 2 * r) * (D / (C₀ * Γ ^ 2)) := by
    rw [mul_comm (C₀ * Γ ^ 2) r, mul_assoc, mul_div_cancel₀ _ hscale.ne']
  _ ≤ (W.card : ℝ) * (D / (C₀ * Γ ^ 2)) :=
    mul_le_mul_of_nonneg_right ((Nat.le_ceil _).trans (by exact_mod_cast hW))
      (div_nonneg hD hscale.le)
  _ = ∑ _w ∈ W, D / (C₀ * Γ ^ 2) := by simp
  _ ≤ _ := Finset.sum_le_sum hd

end TauCeti
