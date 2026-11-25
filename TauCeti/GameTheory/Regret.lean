/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.StdSimplex.DotProduct
import TauCeti.Data.Matrix.DotProduct
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Order
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Linarith

/-!
# Regret in online decision problems

In an online decision problem over finitely many actions `ι`, a player chooses a mixed strategy
`p t` in each round `t` and then sees the payoff `u t a` of every action `a`. This file sets up the
full-information protocol and the two notions of regret that measure the player against fixed
comparators.

The mixed strategies over `ι` are the points of the probability simplex `TauCeti.simplex ι`,
the nonnegative vectors of sum `1`.

* `TauCeti.OnlineAlgorithm ι` and `TauCeti.OnlineAlgorithm.play`: a deterministic online
  algorithm maps the payoffs of the past rounds to a strategy, and `play` runs it against a
  payoff sequence. The strategy at time `t` depends only on the payoffs before `t`
  (`TauCeti.OnlineAlgorithm.play_congr`).
* `TauCeti.HasRange u Δ`: at each time all payoffs lie in one interval of length `Δ`; this says
  that any two payoffs at the same time differ by at most `Δ` (`TauCeti.hasRange_iff`).
* `TauCeti.regret p u T a`: the total payoff of the action `a` over the first `T` rounds minus the
  total expected payoff `∑ t, p t ⬝ᵥ u t` of the plays. The external regret is
  `⨆ a, regret p u T a`.
* `TauCeti.swapRegret p u T`: the largest gain over the first `T` rounds from replacing each action
  by its image under a fixed map `φ : ι → ι`.

## Main results

* `TauCeti.sum_sub_eq_sum_mul_regret`: the regret against a mixed comparator `q` is the
  `q`-average of the regrets against the actions.
* `TauCeti.isGreatest_sum_sub_image_simplex`: so the largest regret against a mixed comparator is
  the external regret.
* `TauCeti.regret_le_swapRegret`: the external regret is at most the swap regret, the constant
  maps `φ` giving the regrets against single actions.
* `TauCeti.abs_instRegret_le`: for payoffs of range `Δ`, the instantaneous regret
  `u t a - p t ⬝ᵥ u t` of a mixed strategy has absolute value at most `Δ`.

Regret here is that of the mixed strategies, measured by expected payoffs, and players maximize
payoffs.

## References

* N. Cesa-Bianchi and G. Lugosi, *Prediction, learning, and games*, Cambridge University Press,
  2006, Sections 2.1 and 4.4.
* A. Blum and Y. Mansour, *From external to internal regret*, J. Mach. Learn. Res. **8** (2007),
  1307–1324, Section 2.
-/

public section

open Finset Matrix Convexity

namespace TauCeti

variable {ι : Type*}

/-! ### Online algorithms -/

/-- A deterministic online algorithm over the actions `ι`: at time `t` it maps the payoff vectors
of the rounds `s < t` to the strategy it plays. -/
abbrev OnlineAlgorithm (ι : Type*) := (t : ℕ) → (Fin t → ι → ℝ) → (ι → ℝ)

namespace OnlineAlgorithm

/-- The strategies the online algorithm `A` plays against the payoff sequence `u`: at time `t`,
the output of `A` on the payoffs `u s` for `s < t`. -/
def play (A : OnlineAlgorithm ι) (u : ℕ → ι → ℝ) (t : ℕ) : ι → ℝ :=
  A t fun s ↦ u s

/-- The strategy played at time `t` is the output of the algorithm on the payoffs before `t`. -/
theorem play_def (A : OnlineAlgorithm ι) (u : ℕ → ι → ℝ) (t : ℕ) :
    A.play u t = A t fun s ↦ u s :=
  (rfl)

/-- The strategy played at time `t` depends only on the payoffs before `t`. -/
theorem play_congr (A : OnlineAlgorithm ι) {u v : ℕ → ι → ℝ} {t : ℕ}
    (h : ∀ s < t, u s = v s) : A.play u t = A.play v t := by
  simp only [play_def]
  congr 1
  funext s
  exact h s s.isLt

/-- The first strategy does not depend on the payoffs. -/
@[simp]
theorem play_zero (A : OnlineAlgorithm ι) (u : ℕ → ι → ℝ) : A.play u 0 = A 0 Fin.elim0 := by
  rw [play_def]
  congr 1
  funext s
  exact s.elim0

end OnlineAlgorithm

/-! ### Payoff ranges -/

section Range

/-- The payoff sequence `u` has range `Δ`: at each time `t`, all payoffs `u t a` lie in one
interval `[c t, c t + Δ]` of length `Δ`. -/
def HasRange (u : ℕ → ι → ℝ) (Δ : ℝ) : Prop :=
  ∃ c : ℕ → ℝ, ∀ t a, c t ≤ u t a ∧ u t a ≤ c t + Δ

/-- Two payoffs at the same time differ by at most the range. -/
theorem HasRange.sub_le {u : ℕ → ι → ℝ} {Δ : ℝ} (hu : HasRange u Δ) (t : ℕ) (a b : ι) :
    u t a - u t b ≤ Δ := by
  obtain ⟨c, hc⟩ := hu
  linarith [(hc t a).2, (hc t b).1]

/-- A payoff sequence has range `Δ` exactly when any two payoffs at the same time differ by at
most `Δ`. -/
theorem hasRange_iff {u : ℕ → ι → ℝ} {Δ : ℝ} :
    HasRange u Δ ↔ ∀ t a b, u t a - u t b ≤ Δ := by
  refine ⟨HasRange.sub_le, fun h ↦ ⟨fun t ↦ ⨅ b, u t b, fun t a ↦ ?_⟩⟩
  have hbdd : BddBelow (Set.range (u t)) :=
    ⟨u t a - Δ, by rintro _ ⟨b, rfl⟩; linarith [h t a b]⟩
  have : Nonempty ι := ⟨a⟩
  have : u t a - Δ ≤ ⨅ b, u t b := le_ciInf fun b ↦ by linarith [h t a b]
  exact ⟨ciInf_le hbdd a, by linarith⟩

/-- With at least one action, no payoff sequence has a negative range. -/
theorem HasRange.nonneg [Nonempty ι] {u : ℕ → ι → ℝ} {Δ : ℝ} (hu : HasRange u Δ) : 0 ≤ Δ := by
  obtain ⟨a⟩ := ‹Nonempty ι›
  simpa using hu.sub_le 0 a a

/-- A payoff sequence of range `Δ` has every larger range. -/
theorem HasRange.mono {u : ℕ → ι → ℝ} {Δ Δ' : ℝ} (hu : HasRange u Δ) (hΔ : Δ ≤ Δ') :
    HasRange u Δ' := by
  obtain ⟨c, hc⟩ := hu
  exact ⟨c, fun t a ↦ ⟨(hc t a).1, (hc t a).2.trans (by linarith)⟩⟩

end Range

/-! ### External regret -/

section Regret

variable [Fintype ι]

/-- The regret of the plays `p` against the action `a` after `T` rounds of the payoffs `u`: the
total payoff of `a` minus the total expected payoff `p t ⬝ᵥ u t` of the plays. -/
def regret (p u : ℕ → ι → ℝ) (T : ℕ) (a : ι) : ℝ :=
  ∑ t ∈ range T, (u t a - p t ⬝ᵥ u t)

/-- The regret is the sum of the instantaneous regrets `u t a - p t ⬝ᵥ u t` over `t < T`. -/
theorem regret_def (p u : ℕ → ι → ℝ) (T : ℕ) (a : ι) :
    regret p u T a = ∑ t ∈ range T, (u t a - p t ⬝ᵥ u t) :=
  (rfl)

/-- Before any round, every regret is `0`. -/
@[simp]
theorem regret_zero (p u : ℕ → ι → ℝ) (a : ι) : regret p u 0 a = 0 := by
  simp [regret_def]

/-- One more round adds its instantaneous regret. -/
theorem regret_succ (p u : ℕ → ι → ℝ) (T : ℕ) (a : ι) :
    regret p u (T + 1) a = regret p u T a + (u T a - p T ⬝ᵥ u T) := by
  simp only [regret_def, sum_range_succ]

/-- The regret against a mixed comparator `q` is the `q`-average of the regrets against the
actions. Only the total weight of `q` matters, so `q` need not be nonnegative. -/
theorem sum_sub_eq_sum_mul_regret (p u : ℕ → ι → ℝ) {q : ι → ℝ} (hq : ∑ a, q a = 1) (T : ℕ) :
    ∑ t ∈ range T, (q ⬝ᵥ u t - p t ⬝ᵥ u t) = ∑ a, q a * regret p u T a := by
  simp only [regret_def, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun t _ ↦ (sum_mul_sub_eq_dotProduct_sub hq (u t) _).symm

/-- The largest regret against a mixed comparator is the external regret, the largest regret
against a single action. -/
theorem isGreatest_sum_sub_image_simplex [Nonempty ι] (p u : ℕ → ι → ℝ) (T : ℕ) :
    IsGreatest ((fun q ↦ ∑ t ∈ range T, (q ⬝ᵥ u t - p t ⬝ᵥ u t)) '' simplex ι)
      (⨆ a, regret p u T a) := by
  classical
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha⟩ := exists_eq_ciSup_of_finite (f := regret p u T)
    refine ⟨Pi.single a 1, single_mem_simplex a, ?_⟩
    rw [← ha, regret_def]
    simp
  · rintro _ ⟨q, hq, rfl⟩
    dsimp only
    rw [sum_sub_eq_sum_mul_regret p u (mem_simplex_iff.1 hq).2]
    exact dotProduct_le_of_mem_simplex hq fun a ↦ le_ciSup (Finite.bddAbove_range _) a

/-- If every play has total weight `1` (for instance, is a mixed strategy) and the payoffs at each
time are equal across actions, every regret is `0`. -/
theorem regret_const {p : ℕ → ι → ℝ} {T : ℕ} (hp : ∀ t < T, ∑ i, p t i = 1) (c : ℕ → ℝ)
    (a : ι) : regret p (fun t _ ↦ c t) T a = 0 := by
  rw [regret_def]
  refine sum_eq_zero fun t ht ↦ ?_
  rw [← sum_mul_sub_eq_sub_dotProduct (hp t (mem_range.1 ht))]
  simp

/-- With a single action, every regret of plays of total weight `1` is `0`. -/
theorem regret_eq_zero_of_subsingleton [Subsingleton ι] {p : ℕ → ι → ℝ} {T : ℕ}
    (hp : ∀ t < T, ∑ i, p t i = 1) (u : ℕ → ι → ℝ) (a : ι) : regret p u T a = 0 := by
  have hu : u = fun t _ ↦ u t a := funext₂ fun t b ↦ by rw [Subsingleton.elim b a]
  rw [hu]
  exact regret_const hp _ a

/-- For payoffs of range `Δ`, the instantaneous regret `u t a - p t ⬝ᵥ u t` of a mixed strategy
`p t` has absolute value at most `Δ`. -/
theorem abs_instRegret_le {p u : ℕ → ι → ℝ} {t : ℕ} (hp : p t ∈ simplex ι) {Δ : ℝ}
    (hu : HasRange u Δ) (a : ι) : |u t a - p t ⬝ᵥ u t| ≤ Δ := by
  obtain ⟨c, hc⟩ := hu
  have h₁ := le_dotProduct_of_mem_simplex hp fun i ↦ (hc t i).1
  have h₂ := dotProduct_le_of_mem_simplex hp fun i ↦ (hc t i).2
  rw [abs_sub_le_iff]
  constructor <;> linarith [hc t a]

end Regret

/-! ### Swap regret -/

section SwapRegret

variable [Fintype ι]

/-- The swap regret of the plays `p` after `T` rounds of the payoffs `u`: the largest gain, over
the maps `φ : ι → ι`, from playing `φ a` whenever the plays put weight on `a`. -/
noncomputable def swapRegret (p u : ℕ → ι → ℝ) (T : ℕ) : ℝ :=
  ⨆ φ : ι → ι, ∑ t ∈ range T, ∑ a, p t a * (u t (φ a) - u t a)

/-- The swap regret is the largest gain from a fixed map of the actions. -/
theorem swapRegret_def (p u : ℕ → ι → ℝ) (T : ℕ) :
    swapRegret p u T = ⨆ φ : ι → ι, ∑ t ∈ range T, ∑ a, p t a * (u t (φ a) - u t a) :=
  (rfl)

/-- The gain from each map of the actions is at most the swap regret. -/
theorem le_swapRegret (p u : ℕ → ι → ℝ) (T : ℕ) (φ : ι → ι) :
    ∑ t ∈ range T, ∑ a, p t a * (u t (φ a) - u t a) ≤ swapRegret p u T := by
  rw [swapRegret_def]
  exact le_ciSup (f := fun φ : ι → ι ↦ ∑ t ∈ range T, ∑ a, p t a * (u t (φ a) - u t a))
    (Finite.bddAbove_range _) φ

/-- The swap regret is attained by some map of the actions. -/
theorem exists_eq_swapRegret (p u : ℕ → ι → ℝ) (T : ℕ) :
    ∃ φ : ι → ι, ∑ t ∈ range T, ∑ a, p t a * (u t (φ a) - u t a) = swapRegret p u T := by
  have : Nonempty (ι → ι) := ⟨id⟩
  rw [swapRegret_def]
  exact exists_eq_ciSup_of_finite

/-- The swap regret is at most `c` exactly when the gain from every map of the actions is. -/
theorem swapRegret_le_iff {p u : ℕ → ι → ℝ} {T : ℕ} {c : ℝ} :
    swapRegret p u T ≤ c ↔ ∀ φ : ι → ι, ∑ t ∈ range T, ∑ a, p t a * (u t (φ a) - u t a) ≤ c := by
  have : Nonempty (ι → ι) := ⟨id⟩
  rw [swapRegret_def]
  exact ciSup_le_iff (Finite.bddAbove_range _)

/-- The swap regret is nonnegative: the identity map gains nothing. -/
theorem swapRegret_nonneg (p u : ℕ → ι → ℝ) (T : ℕ) : 0 ≤ swapRegret p u T := by
  simpa using le_swapRegret p u T id

/-- Before any round, the swap regret is `0`. -/
@[simp]
theorem swapRegret_zero (p u : ℕ → ι → ℝ) : swapRegret p u 0 = 0 := by
  have : Nonempty (ι → ι) := ⟨id⟩
  simp [swapRegret_def]

/-- The external regret is at most the swap regret when every play has total weight `1`, for
instance is a mixed strategy: the regret against `a` is the gain from the constant map at `a`. -/
theorem regret_le_swapRegret {p : ℕ → ι → ℝ} (u : ℕ → ι → ℝ) {T : ℕ}
    (hp : ∀ t < T, ∑ i, p t i = 1) (a : ι) : regret p u T a ≤ swapRegret p u T := by
  rw [regret_def]
  exact le_of_eq_of_le
    (sum_congr rfl fun t ht ↦ (sum_mul_sub_eq_sub_dotProduct (hp t (mem_range.1 ht)) _ _).symm)
    (le_swapRegret p u T fun _ ↦ a)

end SwapRegret

end TauCeti
