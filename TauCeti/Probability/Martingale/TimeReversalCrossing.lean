module

public import Mathlib.Probability.Martingale.Upcrossing

/-!
# Time-reversal crossing bound

This file proves that upcrossings in a time-reversed and negated process complete within the
expected time bound, a key combinatorial ingredient for the reverse-martingale convergence proof.

## Main definitions

- `negProcess`: negation of a stochastic process.
- `revProcess`: time reversal of a stochastic process up to a horizon `N`.

## Main results

- `timeReversal_crossing_bound`: for a process `X` with `k` upcrossings `[a→b]` completing before
  time `N`, the time-reversed negated process `Y = negProcess (revProcess X N)` has its `k`
  upcrossings `[-b→-a]` completing at time `≤ N`.

The bijection `(τ, σ) ↦ (N - σ, N - τ)` maps upcrossings of `X` to upcrossings of `Y` in reverse
order; the completion times are bounded via `hittingBtwn_le_of_mem`.

Adapted from `cameronfreer/exchangeability` (`Probability/TimeReversalCrossing.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`). Written Mathlib-shaped for eventual upstreaming.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

/-- Negation of a stochastic process. -/
def negProcess {Ω : Type*} (X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n ω => -X n ω

/-- Time reversal of a stochastic process up to time `N`. -/
def revProcess {Ω : Type*} (X : ℕ → Ω → ℝ) (N : ℕ) : ℕ → Ω → ℝ :=
  fun n ω => X (N - n) ω

/-- Strict inequality between lower and upper crossing times when the crossing completes before
`N`. -/
private lemma lowerCrossingTime_lt_upperCrossingTime_succ' {Ω : Type*} {a b : ℝ} {f : ℕ → Ω → ℝ}
    {N n : ℕ} {ω : Ω} (hab : a < b)
    (h : upperCrossingTime a b f N (n + 1) ω < N) :
    lowerCrossingTime a b f N n ω < upperCrossingTime a b f N (n + 1) ω := by
  have h_neq : upperCrossingTime a b f N (n + 1) ω ≠ N := Nat.ne_of_lt h
  have h_le : lowerCrossingTime a b f N n ω ≤ upperCrossingTime a b f N (n + 1) ω :=
    lowerCrossingTime_le_upperCrossingTime_succ
  by_contra hge
  push Not at hge
  have h_eq : lowerCrossingTime a b f N n ω = upperCrossingTime a b f N (n + 1) ω :=
    le_antisymm h_le hge
  have h_neq' : lowerCrossingTime a b f N n ω ≠ N := h_eq ▸ h_neq
  have h_le_a := stoppedValue_lowerCrossingTime (f := f) h_neq'
  have h_ge_b := stoppedValue_upperCrossingTime (f := f) h_neq
  simp only [stoppedValue] at h_le_a h_ge_b
  rw [h_eq] at h_le_a
  linarith

/-- Strong version tracking the bijection explicitly.

For `m ≤ k` with `X`'s `k`-th crossing completing before `N`:
  `upperCrossingTime Y (N + 1) m ≤ N - lowerCrossingTime X (k - m)`.

This captures that `Y`'s `m`-th crossing corresponds to `X`'s `(k - m + 1)`-th crossing (reversed
order), with `Y`'s crossing ending at time `N - τ` where `τ` is the start of `X`'s crossing. -/
private lemma timeReversal_crossing_bound_strong
    {Ω : Type*} (X : ℕ → Ω → ℝ) (a b : ℝ) (hab : a < b) (N k m : ℕ) (ω : Ω)
    (hm : m ≤ k)
    (h_k : upperCrossingTime a b X N k ω < N) :
    upperCrossingTime (-b) (-a) (negProcess (revProcess X N)) (N + 1) m ω
      ≤ N - lowerCrossingTime a b X N (k - m) ω := by
  set Y := negProcess (revProcess X N) with hY_def
  -- All of X's crossing times are < N
  have h_j : ∀ j ≤ k, upperCrossingTime a b X N j ω < N := by
    intro j hj
    calc upperCrossingTime a b X N j ω
        ≤ upperCrossingTime a b X N k ω := upperCrossingTime_mono hj
      _ < N := h_k
  have h_τ_lt : ∀ j < k, lowerCrossingTime a b X N j ω < N := by
    intro j hj
    have h_j1 : j + 1 ≤ k := hj
    have h_uct : upperCrossingTime a b X N (j + 1) ω < N := h_j (j + 1) h_j1
    exact lt_trans (lowerCrossingTime_lt_upperCrossingTime_succ' hab h_uct) h_uct
  induction m with
  | zero =>
    simp only [upperCrossingTime_zero, Nat.sub_zero]
    exact Nat.zero_le _
  | succ m' ih =>
    have hm'_lt_k : m' < k := Nat.lt_of_succ_le hm
    have hm' : m' ≤ k := Nat.le_of_lt hm'_lt_k
    set j := k - m' with hj_def
    have hj_pos : 1 ≤ j := by omega
    have hj_le_k : j ≤ k := Nat.sub_le k m'
    have h_km1_eq : k - (m' + 1) = j - 1 := by omega
    have ih' := ih hm'
    -- X's j-th crossing times
    set σ := upperCrossingTime a b X N j ω with hσ_def
    set τ := lowerCrossingTime a b X N (j - 1) ω with hτ_def
    have hσ_lt_N : σ < N := h_j j hj_le_k
    have hτ_lt_N : τ < N := by
      have h : j - 1 < k := by omega
      exact h_τ_lt (j - 1) h
    -- τ < σ : lowerCrossingTime (j - 1) < upperCrossingTime j
    have hτ_lt_σ : τ < σ := by
      have h_j_eq : j = (j - 1) + 1 := by omega
      have h_uct_lt : upperCrossingTime a b X N ((j - 1) + 1) ω < N := by
        simp only [← h_j_eq]; exact hσ_lt_N
      have := lowerCrossingTime_lt_upperCrossingTime_succ' hab h_uct_lt
      simp only [← hτ_def, ← hσ_def, ← h_j_eq] at this
      exact this
    rw [h_km1_eq]
    -- X's level conditions
    have h_neq_σ : σ ≠ N := Nat.ne_of_lt hσ_lt_N
    have h_neq_τ : τ ≠ N := Nat.ne_of_lt hτ_lt_N
    have hX_σ_ge_b : b ≤ X σ ω := by
      have h_j_eq : j = (j - 1) + 1 := by omega
      have h_neq_σ' : upperCrossingTime a b X N ((j - 1) + 1) ω ≠ N := by
        simp only [← h_j_eq]; exact h_neq_σ
      have h2 := stoppedValue_upperCrossingTime (f := X) (n := j - 1) h_neq_σ'
      rw [← h_j_eq] at h2
      exact h2
    have hX_τ_le_a : X τ ω ≤ a :=
      stoppedValue_lowerCrossingTime (f := X) (n := j - 1) h_neq_τ
    -- Y's level conditions at bijected times
    have hY_Nσ_le_negb : Y (N - σ) ω ≤ -b := by
      simp only [hY_def, negProcess, revProcess, Nat.sub_sub_self (Nat.le_of_lt hσ_lt_N)]
      linarith
    have hY_Nτ_ge_nega : Y (N - τ) ω ≥ -a := by
      simp only [hY_def, negProcess, revProcess, Nat.sub_sub_self (Nat.le_of_lt hτ_lt_N)]
      linarith
    -- lowerCrossingTime X j ≥ σ (hitting starts from σ)
    have h_lct_ge : lowerCrossingTime a b X N j ω ≥ σ := by
      simpa [lowerCrossingTime, hσ_def] using le_hittingBtwn (Nat.le_of_lt hσ_lt_N) ω
    -- From IH: upperCrossingTime Y m' ≤ N - lowerCrossingTime X j ≤ N - σ
    have h_uct_le_Nσ : upperCrossingTime (-b) (-a) Y (N + 1) m' ω ≤ N - σ := by
      calc upperCrossingTime (-b) (-a) Y (N + 1) m' ω
          ≤ N - lowerCrossingTime a b X N j ω := ih'
        _ ≤ N - σ := Nat.sub_le_sub_left h_lct_ge N
    -- lowerCrossingTime Y m' ≤ N - σ (by hittingBtwn_le_of_mem)
    have h_Nσ_le_N1 : N - σ ≤ N + 1 := Nat.le_succ_of_le (Nat.sub_le N σ)
    have hY_Nσ_in_Iic : Y (N - σ) ω ∈ Set.Iic (-b) := hY_Nσ_le_negb
    have h_lctY_le_Nσ : lowerCrossingTime (-b) (-a) Y (N + 1) m' ω ≤ N - σ := by
      simpa [lowerCrossingTime] using
        hittingBtwn_le_of_mem h_uct_le_Nσ h_Nσ_le_N1 hY_Nσ_in_Iic
    -- N - σ < N - τ and lowerCrossingTime Y m' < N - τ
    have hNσ_lt_Nτ : N - σ < N - τ := Nat.sub_lt_sub_left hτ_lt_N hτ_lt_σ
    have h_lctY_le_Nτ : lowerCrossingTime (-b) (-a) Y (N + 1) m' ω ≤ N - τ :=
      Nat.le_of_lt (lt_of_le_of_lt h_lctY_le_Nσ hNσ_lt_Nτ)
    have h_Nτ_le_N1 : N - τ ≤ N + 1 := Nat.le_succ_of_le (Nat.sub_le N τ)
    have hY_Nτ_in_Ici : Y (N - τ) ω ∈ Set.Ici (-a) := hY_Nτ_ge_nega
    -- Final: upperCrossingTime Y (m' + 1) ≤ N - τ
    calc upperCrossingTime (-b) (-a) Y (N + 1) (m' + 1) ω
        = hittingBtwn Y (Set.Ici (-a)) (lowerCrossingTime (-b) (-a) Y (N + 1) m' ω) (N + 1) ω := by
          simp only [upperCrossingTime, lowerCrossingTime]; rfl
      _ ≤ N - τ := hittingBtwn_le_of_mem h_lctY_le_Nτ h_Nτ_le_N1 hY_Nτ_in_Ici

/-- **Time-reversal crossing bound.**

For a process `X` with `k` upcrossings `[a→b]` completing before time `N`, the time-reversed
negated process `Y = negProcess (revProcess X N)` has its `k` upcrossings `[-b→-a]` completing at
time `≤ N`.

The proof uses the bijection `(τ, σ) ↦ (N - σ, N - τ)` which maps `X`'s crossings to `Y`'s
crossings in reverse order. The greedy upcrossing algorithm finds these crossings with completion
times bounded by `hittingBtwn_le_of_mem`. -/
lemma timeReversal_crossing_bound
    {Ω : Type*} (X : ℕ → Ω → ℝ) (a b : ℝ) (hab : a < b) (N k : ℕ) (ω : Ω)
    (h_k : upperCrossingTime a b X N k ω < N) :
    upperCrossingTime (-b) (-a) (negProcess (revProcess X N)) (N + 1) k ω ≤ N := by
  have h := timeReversal_crossing_bound_strong X a b hab N k k ω le_rfl h_k
  exact le_trans (by simpa using h) (Nat.sub_le N _)

end ProbabilityTheory
