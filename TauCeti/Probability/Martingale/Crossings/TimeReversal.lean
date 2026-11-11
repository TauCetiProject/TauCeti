/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Probability.Martingale.Upcrossing

/-!
# Time-reversal crossing bound

Reverse-martingale infrastructure bounding the completion time of upcrossings in a time-reversed,
negated process. This is a combinatorial ingredient of the reverse-martingale upcrossing argument.

## Main definitions

- `revProcess`: time reversal of a stochastic process up to a horizon `N`.

## Main results

- `MeasureTheory.upperCrossingTime_neg_revProcess_le`: for a process `X` with `k`
  upcrossings `[a→b]` completing before time `N`, the time-reversed negated process
  `-(revProcess X N)` has its `k`-th upcrossing `[-b→-a]` completing at time `≤ N`.

Adapted from `cameronfreer/exchangeability` (`Probability/TimeReversalCrossing.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`). Written Mathlib-shaped for eventual upstreaming.
-/

public section

namespace MeasureTheory

variable {Ω α : Type*}

/-- Time reversal of a stochastic process up to time `N`, using Mathlib's horizon reversal
`Polynomial.revAt`. For `n ≤ N` this is `X (N - n)`; see `revProcess_apply_of_le`. -/
def revProcess (X : ℕ → Ω → α) (N : ℕ) : ℕ → Ω → α :=
  fun n ω => X (Polynomial.revAt N n) ω

/-- Defining equation for `revProcess` (whose body is deliberately not `@[expose]`d). -/
@[simp]
lemma revProcess_apply (X : ℕ → Ω → α) (N n : ℕ) (ω : Ω) :
    revProcess X N n ω = X (Polynomial.revAt N n) ω := by rfl

/-- Below the horizon, `Polynomial.revAt N` is genuine subtraction, so `revProcess` reverses. -/
lemma revProcess_apply_of_le (X : ℕ → Ω → α) {N n : ℕ} (h : n ≤ N) (ω : Ω) :
    revProcess X N n ω = X (N - n) ω := by simp [h]

/-- Inductive step of `upperCrossingTime_neg_revProcess_le_strong`.

Fix a crossing index `i` and a count `m'`, and assume:
* `hσ_lt_N`: `X`'s `(i + 1)`-th upper crossing completes strictly before `N`;
* `ih'`: the reversed process satisfies the bound at count `m'` (endpoint index `i + 1`).

Then the bound holds for `m' + 1`, with reflected endpoint `N - lowerCrossingTime a b X N i ω`. -/
private lemma upperCrossingTime_neg_revProcess_succ_le
    (X : ℕ → Ω → ℝ) (a b : ℝ) (N m' i : ℕ) (ω : Ω)
    (hσ_lt_N : upperCrossingTime a b X N (i + 1) ω < N)
    (ih' : upperCrossingTime (-b) (-a) (-(revProcess X N)) (N + 1) m' ω
      ≤ N - lowerCrossingTime a b X N (i + 1) ω) :
    upperCrossingTime (-b) (-a) (-(revProcess X N)) (N + 1) (m' + 1) ω
      ≤ N - lowerCrossingTime a b X N i ω := by
  set Y := -(revProcess X N)
  -- `X` reaches `≥ b` at its `(i+1)`-th upper crossing and `≤ a` at its `i`-th lower crossing,
  -- which comes no later. (Stated on explicit terms, then folded to `σ`, `τ` by `set`.)
  have hτ_le_σ : lowerCrossingTime a b X N i ω ≤ upperCrossingTime a b X N (i + 1) ω :=
    lowerCrossingTime_le_upperCrossingTime_succ
  -- The `i`-th lower crossing precedes the `(i+1)`-th upper, so it too completes before `N`.
  have hτ_lt_N : lowerCrossingTime a b X N i ω < N := hτ_le_σ.trans_lt hσ_lt_N
  have hX_σ_ge_b : b ≤ X (upperCrossingTime a b X N (i + 1) ω) ω :=
    stoppedValue_upperCrossingTime hσ_lt_N.ne
  have hX_τ_le_a : X (lowerCrossingTime a b X N i ω) ω ≤ a :=
    stoppedValue_lowerCrossingTime hτ_lt_N.ne
  have h_lct_ge : upperCrossingTime a b X N (i + 1) ω ≤ lowerCrossingTime a b X N (i + 1) ω :=
    upperCrossingTime_le_lowerCrossingTime
  set σ := upperCrossingTime a b X N (i + 1) ω
  set τ := lowerCrossingTime a b X N i ω
  -- The reflected process `Y` mirrors these levels at the reflected times `N - σ` and `N - τ`.
  have hY_Nσ_le_negb : Y (N - σ) ω ≤ -b := by
    simpa [Y, revProcess_apply_of_le X (Nat.sub_le N σ), Nat.sub_sub_self hσ_lt_N.le] using
      hX_σ_ge_b
  have hY_Nτ_ge_nega : -a ≤ Y (N - τ) ω := by
    simpa [Y, revProcess_apply_of_le X (Nat.sub_le N τ), Nat.sub_sub_self hτ_lt_N.le] using
      hX_τ_le_a
  -- Advance `Y`'s crossing count: the induction hypothesis bounds `Y`'s `m'`-th upper crossing by
  -- `N - σ`, hence its `m'`-th lower crossing too; the `(m'+1)`-th upper crossing then lands by
  -- `N - τ`, the reflection of `X`'s crossing start.
  have h_lctY_le_Nσ : lowerCrossingTime (-b) (-a) Y (N + 1) m' ω ≤ N - σ := by
    rw [lowerCrossingTime]
    exact hittingBtwn_le_of_mem (ih'.trans (Nat.sub_le_sub_left h_lct_ge N))
      (Nat.le_succ_of_le (Nat.sub_le N σ)) hY_Nσ_le_negb
  rw [upperCrossingTime_succ_eq]
  exact hittingBtwn_le_of_mem (h_lctY_le_Nσ.trans (Nat.sub_le_sub_left hτ_le_σ N))
    (Nat.le_succ_of_le (Nat.sub_le N τ)) hY_Nτ_ge_nega

/-- Strong version tracking the bijection explicitly.

For `m ≤ k` with `X`'s `k`-th crossing completing before `N`:
  `upperCrossingTime Y (N + 1) m ≤ N - lowerCrossingTime X (k - m)`.

This captures that `Y`'s `m`-th crossing corresponds to `X`'s `(k - m + 1)`-th crossing (reversed
order), with `Y`'s crossing ending at time `N - τ` where `τ` is the start of `X`'s crossing. -/
private lemma upperCrossingTime_neg_revProcess_le_strong
    (X : ℕ → Ω → ℝ) (a b : ℝ) (N k m : ℕ) (ω : Ω) (hm : m ≤ k)
    (h_k : upperCrossingTime a b X N k ω < N) :
    upperCrossingTime (-b) (-a) (-(revProcess X N)) (N + 1) m ω
      ≤ N - lowerCrossingTime a b X N (k - m) ω := by
  induction m with
  | zero => simp
  | succ m' ih =>
    -- `Y`'s `(m'+1)`-th crossing reflects `X`'s `(k-m')`-th; set `i = k-(m'+1)`, so `k-m' = i+1`.
    have hik : k - m' = k - (m' + 1) + 1 := by omega
    refine upperCrossingTime_neg_revProcess_succ_le X a b N m' (k - (m' + 1)) ω ?_ ?_ <;>
      rw [← hik]
    · exact (upperCrossingTime_mono (Nat.sub_le k m')).trans_lt h_k
    · exact ih (by omega)

/-- **Time-reversal crossing bound.**

For a process `X` with `k` upcrossings `[a→b]` completing before time `N`, the time-reversed
negated process `-(revProcess X N)` has its `k`-th upcrossing `[-b→-a]` completing at
time `≤ N`. No ordering of the levels `a`, `b` is needed. -/
lemma upperCrossingTime_neg_revProcess_le
    (X : ℕ → Ω → ℝ) (a b : ℝ) (N k : ℕ) (ω : Ω)
    (h_k : upperCrossingTime a b X N k ω < N) :
    upperCrossingTime (-b) (-a) (-(revProcess X N)) (N + 1) k ω ≤ N :=
  -- The `strong` version bounds this by `N - lowerCrossingTime …` via the bijection
  -- `(τ, σ) ↦ (N - σ, N - τ)`; discard the subtraction with `Nat.sub_le`.
  (upperCrossingTime_neg_revProcess_le_strong X a b N k k ω le_rfl h_k).trans (Nat.sub_le N _)

end MeasureTheory
