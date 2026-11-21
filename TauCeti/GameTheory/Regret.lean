/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.Pi
import TauCeti.Analysis.Convex.StdSimplex

/-!
# External and swap regret

We set up the full-information online protocol over a finite action set `ι`. A mixed strategy is a
point of `simplex ι`, the weight vectors of `Convexity.StdSimplex ℝ ι`. A payoff sequence is
`u : ℕ → ι → ℝ`; players maximize. An `OnlineAlgorithm` chooses its strategy at time `t` from the
payoffs before `t`, and `OnlineAlgorithm.play` runs it against a payoff sequence.

For plays `p : ℕ → ι → ℝ`, `regret p u T a` is the regret against action `a` after `T` rounds and
`swapRegret p u T` is the regret against the best swap `φ : ι → ι` of actions. A payoff sequence
has range `Δ` (`HasRange u Δ`) when at each time its values lie in an interval of length `Δ`; the
interval may move with time, so the payoffs need not be bounded.

## Main results

* `TauCeti.sum_sub_eq_sum_mul_regret`: the regret against a mixed comparator `q` is the
  `q`-weighted sum of the regrets against single actions.
* `TauCeti.regret_eq_sum_sum_mul`, `TauCeti.regret_le_swapRegret`: the regret against an action
  is the gain of a constant swap, so external regret is at most swap regret.
* `TauCeti.swapRegret_nonneg`, `TauCeti.regret_zero`, `TauCeti.swapRegret_zero`: swap regret is
  nonnegative, and both regrets vanish after zero rounds.
* `TauCeti.abs_instRegret_le`: the instantaneous regret is bounded by the range.
* `TauCeti.regret_const`, `TauCeti.regret_eq_zero_of_subsingleton`: regret vanishes against
  payoffs that do not depend on the action, in particular with a single action.
* `TauCeti.OnlineAlgorithm.play_congr`: an online algorithm plays causally.

## References

* N. Cesa-Bianchi, G. Lugosi, *Prediction, Learning, and Games*, Cambridge University Press
  (2006), Sections 2.1 and 4.4.
* A. Blum, Y. Mansour, *From external to internal regret*, J. Mach. Learn. Res. 8 (2007),
  Section 2.
-/

public section

open Finset Matrix

namespace TauCeti

variable {ι : Type*}

/-- The probability simplex on `ι`, as a set of weight vectors: the weights of Mathlib's
`Convexity.StdSimplex ℝ ι`. -/
def simplex (ι : Type*) : Set (ι → ℝ) :=
  Set.range fun p : Convexity.StdSimplex ℝ ι ↦ ⇑p.weights

theorem simplex_def (ι : Type*) :
    simplex ι = Set.range fun p : Convexity.StdSimplex ℝ ι ↦ ⇑p.weights :=
  (rfl)

/-- A vector lies in the simplex if and only if it is nonnegative with coordinate sum one. -/
theorem mem_simplex_iff [Fintype ι] {q : ι → ℝ} :
    q ∈ simplex ι ↔ (∀ a, 0 ≤ q a) ∧ ∑ a, q a = 1 :=
  Convexity.StdSimplex.mem_range_toFun_comp_weights_iff

/-- A deterministic online algorithm: the strategy at time `t` as a function of the payoffs
at the times before `t`. -/
abbrev OnlineAlgorithm (ι : Type*) := (t : ℕ) → (Fin t → ι → ℝ) → (ι → ℝ)

/-- The strategies an online algorithm plays against the payoff sequence `u`. -/
def OnlineAlgorithm.play (A : OnlineAlgorithm ι) (u : ℕ → ι → ℝ) (t : ℕ) : ι → ℝ :=
  A t fun s ↦ u s

theorem OnlineAlgorithm.play_def (A : OnlineAlgorithm ι) (u : ℕ → ι → ℝ) (t : ℕ) :
    A.play u t = A t fun s ↦ u s :=
  (rfl)

/-- An online algorithm plays causally: its strategy at time `t` depends only on the payoffs
before `t`. -/
theorem OnlineAlgorithm.play_congr (A : OnlineAlgorithm ι) {u v : ℕ → ι → ℝ} {t : ℕ}
    (h : ∀ s < t, u s = v s) : A.play u t = A.play v t := by
  simp only [play_def]
  congr 1
  funext s
  exact h s s.isLt

/-- The first strategy of an online algorithm does not depend on the payoffs. -/
theorem OnlineAlgorithm.play_zero_eq (A : OnlineAlgorithm ι) (u v : ℕ → ι → ℝ) :
    A.play u 0 = A.play v 0 :=
  A.play_congr fun _ hs ↦ absurd hs (Nat.not_lt_zero _)

/-- A payoff sequence `u` has range `Δ`: at each time its values lie in an interval of
length `Δ`. The interval may depend on the time. -/
def HasRange (u : ℕ → ι → ℝ) (Δ : ℝ) : Prop :=
  ∃ c : ℕ → ℝ, ∀ t a, c t ≤ u t a ∧ u t a ≤ c t + Δ

theorem hasRange_iff {u : ℕ → ι → ℝ} {Δ : ℝ} :
    HasRange u Δ ↔ ∃ c : ℕ → ℝ, ∀ t a, c t ≤ u t a ∧ u t a ≤ c t + Δ :=
  Iff.rfl

/-- On a nonempty action set, a range is nonnegative. -/
theorem HasRange.nonneg [Nonempty ι] {u : ℕ → ι → ℝ} {Δ : ℝ} (hu : HasRange u Δ) : 0 ≤ Δ := by
  obtain ⟨c, hc⟩ := hu
  obtain ⟨a⟩ := ‹Nonempty ι›
  linarith [hc 0 a]

/-- A payoff sequence that is constant across actions at each time has range `0`. -/
theorem hasRange_const (c : ℕ → ℝ) : HasRange (fun t (_ : ι) ↦ c t) 0 :=
  ⟨c, fun _ _ ↦ by simp⟩

variable [Fintype ι]

/-- The regret of the plays `p` against the action `a` after `T` rounds of the payoffs `u`. -/
def regret (p u : ℕ → ι → ℝ) (T : ℕ) (a : ι) : ℝ :=
  ∑ t ∈ range T, (u t a - p t ⬝ᵥ u t)

theorem regret_def (p u : ℕ → ι → ℝ) (T : ℕ) (a : ι) :
    regret p u T a = ∑ t ∈ range T, (u t a - p t ⬝ᵥ u t) :=
  (rfl)

@[simp]
theorem regret_zero (p u : ℕ → ι → ℝ) (a : ι) : regret p u 0 a = 0 := by
  simp [regret_def]

theorem regret_succ (p u : ℕ → ι → ℝ) (T : ℕ) (a : ι) :
    regret p u (T + 1) a = regret p u T a + (u T a - p T ⬝ᵥ u T) := by
  rw [regret_def, regret_def, sum_range_succ]

/-- The swap regret of the plays `p` after `T` rounds of the payoffs `u`: the largest gain from
replacing every action `a` by `φ a`, over all `φ : ι → ι`. -/
noncomputable def swapRegret (p u : ℕ → ι → ℝ) (T : ℕ) : ℝ :=
  ⨆ φ : ι → ι, ∑ t ∈ range T, ∑ a, p t a * (u t (φ a) - u t a)

theorem swapRegret_def (p u : ℕ → ι → ℝ) (T : ℕ) :
    swapRegret p u T = ⨆ φ : ι → ι, ∑ t ∈ range T, ∑ a, p t a * (u t (φ a) - u t a) :=
  (rfl)

/-- The gain of every swap is at most the swap regret. -/
theorem le_swapRegret (p u : ℕ → ι → ℝ) (T : ℕ) (φ : ι → ι) :
    ∑ t ∈ range T, ∑ a, p t a * (u t (φ a) - u t a) ≤ swapRegret p u T := by
  rw [swapRegret_def]
  apply le_ciSup (Finite.bddAbove_range _) φ

/-- The swap regret is at most `c` if and only if the gain of every swap is. -/
theorem swapRegret_le_iff {p u : ℕ → ι → ℝ} {T : ℕ} {c : ℝ} :
    swapRegret p u T ≤ c ↔ ∀ φ : ι → ι, ∑ t ∈ range T, ∑ a, p t a * (u t (φ a) - u t a) ≤ c :=
  haveI : Nonempty (ι → ι) := ⟨id⟩
  swapRegret_def p u T ▸ ciSup_le_iff (Finite.bddAbove_range _)

/-- The swap regret is attained by some swap. -/
theorem exists_eq_swapRegret (p u : ℕ → ι → ℝ) (T : ℕ) :
    ∃ φ : ι → ι, ∑ t ∈ range T, ∑ a, p t a * (u t (φ a) - u t a) = swapRegret p u T :=
  haveI : Nonempty (ι → ι) := ⟨id⟩
  swapRegret_def p u T ▸ exists_eq_ciSup_of_finite

/-- The swap regret is nonnegative: the identity swap gains nothing. -/
theorem swapRegret_nonneg (p u : ℕ → ι → ℝ) (T : ℕ) : 0 ≤ swapRegret p u T := by
  simpa using le_swapRegret p u T id

@[simp]
theorem swapRegret_zero (p u : ℕ → ι → ℝ) : swapRegret p u 0 = 0 :=
  le_antisymm (swapRegret_le_iff.2 fun _ ↦ by simp) (swapRegret_nonneg p u 0)

/-- The regret against a mixed comparator `q` of total weight one, such as a point of the simplex,
is the `q`-weighted sum of the regrets against single actions. -/
theorem sum_sub_eq_sum_mul_regret (p u : ℕ → ι → ℝ) {q : ι → ℝ} (hq : ∑ a, q a = 1)
    (T : ℕ) :
    ∑ t ∈ range T, (q ⬝ᵥ u t - p t ⬝ᵥ u t) = ∑ a, q a * regret p u T a := by
  simp_rw [regret_def, mul_sum, mul_sub]
  rw [sum_comm]
  refine sum_congr rfl fun t _ ↦ ?_
  rw [sum_sub_distrib, ← sum_mul, hq, one_mul]
  simp only [dotProduct]

/-- The regret against an action `a` is the gain of the constant swap to `a`. -/
theorem regret_eq_sum_sum_mul (p u : ℕ → ι → ℝ) (T : ℕ) (hp : ∀ t < T, ∑ a, p t a = 1) (a : ι) :
    regret p u T a = ∑ t ∈ range T, ∑ b, p t b * (u t a - u t b) := by
  refine sum_congr rfl fun t ht ↦ ?_
  simp_rw [mul_sub, sum_sub_distrib, ← sum_mul, hp t (mem_range.1 ht), one_mul]
  simp only [dotProduct]

/-- External regret is at most swap regret. -/
theorem regret_le_swapRegret (p u : ℕ → ι → ℝ) (T : ℕ) (hp : ∀ t < T, ∑ a, p t a = 1) (a : ι) :
    regret p u T a ≤ swapRegret p u T := by
  rw [regret_eq_sum_sum_mul p u T hp]
  exact le_swapRegret p u T fun _ ↦ a

/-- The instantaneous regret `u t a - ⟨p t, u t⟩` of a mixed strategy is bounded in absolute
value by the range of the payoffs. -/
theorem abs_instRegret_le (p u : ℕ → ι → ℝ) {t : ℕ} (hp : p t ∈ simplex ι) {Δ : ℝ}
    (hu : HasRange u Δ) (a : ι) : |u t a - p t ⬝ᵥ u t| ≤ Δ := by
  obtain ⟨c, hc⟩ := hu
  obtain ⟨hp0, hp1⟩ := mem_simplex_iff.1 hp
  have hlo : c t ≤ p t ⬝ᵥ u t := by
    calc c t = ∑ b, p t b * c t := by rw [← sum_mul, hp1, one_mul]
      _ ≤ p t ⬝ᵥ u t := sum_le_sum fun b _ ↦ mul_le_mul_of_nonneg_left (hc t b).1 (hp0 b)
  have hhi : p t ⬝ᵥ u t ≤ c t + Δ := by
    calc p t ⬝ᵥ u t ≤ ∑ b, p t b * (c t + Δ) :=
          sum_le_sum fun b _ ↦ mul_le_mul_of_nonneg_left (hc t b).2 (hp0 b)
      _ = c t + Δ := by rw [← sum_mul, hp1, one_mul]
  rw [abs_le]
  constructor <;> linarith [hc t a]

/-- Against payoffs that are constant across actions at each time, every regret is `0`. Only
total weight one is required, and only during the rounds being summed. -/
theorem regret_const (p : ℕ → ι → ℝ) (c : ℕ → ℝ) (T : ℕ)
    (hp : ∀ t < T, ∑ a, p t a = 1) (a : ι) : regret p (fun t _ ↦ c t) T a = 0 := by
  apply sum_eq_zero
  intro t ht
  simp [dotProduct, ← sum_mul, hp t (mem_range.1 ht)]

/-- With a single action, every regret is `0`. Only total weight one during the rounds being
summed is required. -/
theorem regret_eq_zero_of_subsingleton [Subsingleton ι] (p u : ℕ → ι → ℝ) (T : ℕ)
    (hp : ∀ t < T, ∑ a, p t a = 1) (a : ι) : regret p u T a = 0 := by
  have hu : u = fun t _ ↦ u t a := funext fun t ↦ funext fun b ↦ by rw [Subsingleton.elim b a]
  rw [hu]
  exact regret_const p _ T hp a

end TauCeti
