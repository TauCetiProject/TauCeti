module

public import TauCeti.Probability.Martingale.Crossings.TimeReversal

/-!
# Crossings: pathwise reversal lemmas

Pathwise reversal lemmas relating upcrossings of a process to downcrossings of its time reversal.
No filtration / integrability content here — this is the purely combinatorial / pathwise layer.

## Main definitions

- `downcrossingsBefore`: downcrossings before time `N`.
- `downcrossings`: total downcrossings (supremum over all time horizons).

## Main results

- `upcrossings_neg_flip_eq_downcrossings`: `up(-b, -a, -X) = down(a, b, X)`.
- `upcrossingsBefore_le_downcrossingsBefore_revProcess_succ`: the upcrossing–downcrossing
  inequality with shifted horizon.

Adapted from `cameronfreer/exchangeability` (`Probability/Martingale/Crossings/Pathwise.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`). Written Mathlib-shaped for eventual upstreaming.
-/

public section

noncomputable section

open MeasureTheory Set

open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {𝔽 : ℕ → MeasurableSpace Ω}

/-- Downcrossings before `N`: defined as upcrossings of the negated process with flipped interval.
Returns a random variable `Ω → ℕ`. -/
noncomputable def downcrossingsBefore {Ω : Type*} (a b : ℝ) (X : ℕ → Ω → ℝ) (N : ℕ) :
    Ω → ℕ :=
  upcrossingsBefore (-b) (-a) (negProcess X) N

/-- Total downcrossings: supremum over all time horizons. -/
noncomputable def downcrossings {Ω : Type*} (a b : ℝ) (X : ℕ → Ω → ℝ) : Ω → ℝ≥0∞ :=
  fun ω => ⨆ N, ((downcrossingsBefore a b X N ω : ℕ) : ℝ≥0∞)

/-- Defining equation for `downcrossingsBefore` (whose body is deliberately not `@[expose]`d). -/
lemma downcrossingsBefore_eq {Ω : Type*} (a b : ℝ) (X : ℕ → Ω → ℝ) (N : ℕ) :
    downcrossingsBefore a b X N = upcrossingsBefore (-b) (-a) (negProcess X) N := by rfl

/-- **Identity 1:** upcrossings of the negated process = downcrossings of the original.
Negation flips crossing direction: `up(-b, -a, -X) = down(a, b, X)`. -/
lemma upcrossings_neg_flip_eq_downcrossings {Ω : Type*} (a b : ℝ) (X : ℕ → Ω → ℝ) :
    upcrossings (-b) (-a) (negProcess X) = downcrossings a b X := by rfl

/-- Double negation is identity (used by `simp` below). -/
@[simp] private lemma negProcess_negProcess {Ω : Type*} (X : ℕ → Ω → ℝ) :
    negProcess (negProcess X) = X := by funext n ω; simp only [negProcess_apply, neg_neg]

/-- **Identity 2:** downcrossings of the negated process = upcrossings of the original.
Negation flips crossing direction: `down(-b, -a, -X) = up(a, b, X)`. -/
private lemma downcrossings_neg_flip_eq_upcrossings {Ω : Type*} (a b : ℝ) (X : ℕ → Ω → ℝ) :
    downcrossings (-b) (-a) (negProcess X) = upcrossings a b X := by
  unfold downcrossings downcrossingsBefore upcrossings; simp

/-- Helper: hitting respects pointwise equality on `[n, m]`. -/
private lemma hitting_congr {Ω β : Type*} {u v : ℕ → Ω → β} {s : Set β} {n m : ℕ} {ω : Ω}
    (h : ∀ k, n ≤ k → k ≤ m → u k ω = v k ω) :
    hittingBtwn u s n m ω = hittingBtwn v s n m ω := by
  simp only [hittingBtwn]
  by_cases hex : ∃ j ∈ Set.Icc n m, u j ω ∈ s
  · have hex' : ∃ j ∈ Set.Icc n m, v j ω ∈ s := by
      obtain ⟨j, hj, hj_mem⟩ := hex
      refine ⟨j, hj, ?_⟩
      rw [← h j hj.1 hj.2]
      exact hj_mem
    simp only [if_pos hex, if_pos hex']
    congr 1
    ext k
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro ⟨hk_Icc, hk_mem⟩
      refine ⟨hk_Icc, ?_⟩
      rw [← h k hk_Icc.1 hk_Icc.2]
      exact hk_mem
    · intro ⟨hk_Icc, hk_mem⟩
      refine ⟨hk_Icc, ?_⟩
      rw [h k hk_Icc.1 hk_Icc.2]
      exact hk_mem
  · have hex' : ¬∃ j ∈ Set.Icc n m, v j ω ∈ s := by
      intro ⟨j, hj, hj_mem⟩
      apply hex
      refine ⟨j, hj, ?_⟩
      rw [h j hj.1 hj.2]
      exact hj_mem
    simp only [if_neg hex, if_neg hex']

/-- Helper: `upperCrossingTime` respects pointwise equality on `[0, N]`. -/
private lemma upperCrossingTime_congr {Ω : Type*} {a b : ℝ} {f g : ℕ → Ω → ℝ} {N : ℕ} {ω : Ω}
    (h : ∀ n ≤ N, f n ω = g n ω) :
    ∀ k, upperCrossingTime a b f N k ω = upperCrossingTime a b g N k ω := by
  intro k
  induction k with
  | zero =>
    simp [upperCrossingTime_zero]
  | succ n ih =>
    simp only [upperCrossingTime_succ_eq]
    have lct_eq : lowerCrossingTime a b f N n ω = lowerCrossingTime a b g N n ω := by
      simp only [lowerCrossingTime]
      rw [ih]
      apply hitting_congr
      intros k _ hk_ub
      exact h k hk_ub
    rw [lct_eq]
    apply hitting_congr
    intros k _ hk_ub
    exact h k hk_ub

/-- Helper: `upcrossingsBefore` is invariant under pointwise equality on `[0, N]`. -/
lemma upcrossingsBefore_congr {Ω : Type*} {a b : ℝ} {f g : ℕ → Ω → ℝ} {N : ℕ} {ω : Ω}
    (h : ∀ n ≤ N, f n ω = g n ω) :
    upcrossingsBefore a b f N ω = upcrossingsBefore a b g N ω := by
  simp [upcrossingsBefore, upperCrossingTime_congr h]

/-- Index is bounded by completion time when `upperCrossingTime < N`.
If the `n`-th crossing completes before time `N`, then `n < N`. -/
private lemma upperCrossingTime_lt_imp_index_lt {Ω : Type*} {a b : ℝ} {f : ℕ → Ω → ℝ}
    {N n : ℕ} {ω : Ω} (hab : a < b) (h : upperCrossingTime a b f N n ω < N) :
    n < N := by
  -- `upperCrossingTime` is strictly increasing on `{k | upperCrossingTime k < N}`, so `k ≤
  -- upperCrossingTime k` there, giving `k < N`. Prove `n ≤ upperCrossingTime n` by induction.
  suffices h_le : n ≤ upperCrossingTime a b f N n ω by omega
  induction n with
  | zero =>
    simp only [upperCrossingTime_zero, Pi.bot_apply, bot_eq_zero', le_refl]
  | succ n ih =>
    have h_neN : upperCrossingTime a b f N (n + 1) ω ≠ N := ne_of_lt h
    have h_strict : upperCrossingTime a b f N n ω < upperCrossingTime a b f N (n + 1) ω :=
      upperCrossingTime_lt_succ hab h_neN
    have h_n_lt : upperCrossingTime a b f N n ω < N := lt_trans h_strict h
    have ih_n : n ≤ upperCrossingTime a b f N n ω := ih h_n_lt
    omega

/-- One-way inequality: the upcrossings of `X` on `[a, b]` before time `N` are bounded by the
downcrossings of the time-reversed process `revProcess X N` before time `N + 1`. The extra `N + 1`
horizon on the reversed side is what makes crossings completing exactly at time `N` count. -/
-- Via the bijection `(τ, σ) ↦ (N - σ, N - τ)` mapping `X` upcrossings to reversed-process
-- upcrossings: when `τ = 0` the reversed crossing completes at time `N`, which the `N + 1` horizon
-- includes since `N < N + 1`.
lemma upcrossingsBefore_le_downcrossingsBefore_revProcess_succ
    {Ω : Type*} (X : ℕ → Ω → ℝ) (a b : ℝ) (hab : a < b) (N : ℕ) :
    (fun ω => upcrossingsBefore a b X N ω)
      ≤ (fun ω => downcrossingsBefore a b (revProcess X N) (N + 1) ω) := by
  classical
  intro ω
  simp only [downcrossingsBefore, upcrossingsBefore]
  by_cases hN : N = 0
  · simp [hN]
  by_cases hemp : {n | upperCrossingTime a b X N n ω < N}.Nonempty
  · have hbdd1 : BddAbove {n | upperCrossingTime a b X N n ω < N} := by
      use N
      simp only [mem_upperBounds, Set.mem_setOf_eq]
      intro n hn
      exact Nat.le_of_lt (upperCrossingTime_lt_imp_index_lt hab hn)
    have hbdd2 : BddAbove
        {n | upperCrossingTime (-b) (-a) (negProcess (revProcess X N)) (N + 1) n ω < N + 1} := by
      use N + 1
      simp only [mem_upperBounds, Set.mem_setOf_eq]
      intro n hn
      exact Nat.le_of_lt (upperCrossingTime_lt_imp_index_lt (by linarith) hn)
    have hsub : {n | upperCrossingTime a b X N n ω < N} ⊆
        {n | upperCrossingTime (-b) (-a) (negProcess (revProcess X N)) (N + 1) n ω < N + 1} := by
      intro n hn
      simp only [Set.mem_setOf_eq] at hn ⊢
      -- With horizon `N + 1` the bijection works: crossings completing at time `N` are now counted
      -- since `N < N + 1`.
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        match n with
        | 0 =>
          simp only [upperCrossingTime_zero]
          exact Nat.zero_lt_succ N
        | k + 1 =>
          -- `hn` says `X` has `k + 1` complete crossings before time `N`; the bijection
          -- `(τ, σ) ↦ (N - σ, N - τ)` maps these to `Y` crossings completing by time `N`.
          have h_bound : upperCrossingTime (-b) (-a)
              (negProcess (revProcess X N)) (N + 1) (k + 1) ω ≤ N :=
            upperCrossingTime_negProcess_revProcess_le X a b hab N (k + 1) ω hn
          exact Nat.lt_succ_of_le h_bound
    exact csSup_le_csSup hbdd2 hemp hsub
  · rw [Set.not_nonempty_iff_eq_empty] at hemp
    simp [hemp]

end ProbabilityTheory
