/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Positivity

/-!
# Geometric rejection of trial steps

An adaptive one-step method tries a step, computes an error indicator for it, and accepts the
step when the indicator is at most a threshold. A rejected trial step is multiplied by a fixed
factor `θ ∈ (0, 1)`, so the trials that start from a proposal `H` are `θ ^ k * H` for
`k = 0, 1, 2, ...`. This file studies the first accepted trial of this rejection loop for an
arbitrary indicator `indicator : ℝ → ℝ`. No monotonicity or continuity of the indicator is
assumed: the only input is that all sufficiently small admissible steps are accepted.

## Main definitions

* `TauCeti.FirstAccepted indicator threshold θ H k`: trial `k` is accepted and each earlier
  trial is rejected.

## Main results

* `TauCeti.FirstAccepted.indicator_le`, `TauCeti.FirstAccepted.lt_indicator`: the two parts of
  `FirstAccepted`.
* `TauCeti.FirstAccepted.unique`: the first accepted trial is unique.
* `TauCeti.firstAccepted_iff_nat_find_eq`, `TauCeti.firstAccepted_nat_find`,
  `TauCeti.exists_firstAccepted_iff`: the first accepted trial is the least accepted index, and it
  exists exactly when some trial is accepted.
* `TauCeti.exists_firstAccepted`: if every admissible step `0 < h ≤ min H δ` is accepted for some
  `δ > 0`, then the rejection loop terminates.
* `TauCeti.FirstAccepted.le_of_pow_mul_le`: under the same hypothesis, the first accepted trial
  comes no later than any index `m` with `θ ^ m * H ≤ δ`.
* `TauCeti.FirstAccepted.min_le_pow_mul`: under the same hypothesis, the first accepted step is
  at least `min H (θ * δ)`.
* `TauCeti.exists_pos_forall_le_of_le_mul_pow`,
  `TauCeti.exists_pos_forall_le_mul_of_le_mul_pow`: an indicator bound `η h ≤ C * h ^ r` gives the
  small-step hypothesis, for an absolute threshold when `r ≠ 0` and for a threshold proportional
  to the step (error per unit time) when `2 ≤ r`.
* `TauCeti.exists_firstAccepted_of_le_mul_pow`: the rejection loop terminates for an indicator
  with such a power bound and a positive absolute threshold.

## References

* E. Süli, *B6.1 Numerical Solution of Differential Equations I: Initial-value problems*,
  lecture notes, University of Oxford, 25 February 2022, Section 5: embedded error estimates and
  local step-size proposals. <https://people.maths.ox.ac.uk/suli/nsde.pdf>
-/

public section

namespace TauCeti

variable {indicator : ℝ → ℝ} {threshold θ H δ : ℝ} {k m : ℕ}

/-- The trial `θ ^ k * H` of a geometric rejection loop that starts from the proposal `H` is the
first accepted one: its indicator is at most `threshold`, and the indicator of each earlier trial
`θ ^ j * H`, `j < k`, is larger than `threshold`. -/
def FirstAccepted (indicator : ℝ → ℝ) (threshold θ H : ℝ) (k : ℕ) : Prop :=
  indicator (θ ^ k * H) ≤ threshold ∧ ∀ j < k, threshold < indicator (θ ^ j * H)

/-- Unfold `FirstAccepted`. -/
theorem firstAccepted_iff :
    FirstAccepted indicator threshold θ H k ↔
      indicator (θ ^ k * H) ≤ threshold ∧ ∀ j < k, threshold < indicator (θ ^ j * H) :=
  Iff.rfl

/-- The first accepted trial is accepted. -/
theorem FirstAccepted.indicator_le (hk : FirstAccepted indicator threshold θ H k) :
    indicator (θ ^ k * H) ≤ threshold :=
  hk.1

/-- Each trial before the first accepted one is rejected. -/
theorem FirstAccepted.lt_indicator (hk : FirstAccepted indicator threshold θ H k) {j : ℕ}
    (hj : j < k) : threshold < indicator (θ ^ j * H) :=
  hk.2 j hj

/-- The first accepted trial comes no later than any accepted trial. -/
theorem FirstAccepted.le_of_indicator_le (hk : FirstAccepted indicator threshold θ H k)
    (hm : indicator (θ ^ m * H) ≤ threshold) : k ≤ m :=
  not_lt.mp fun hmk => (hk.lt_indicator hmk).not_ge hm

/-- The first accepted trial is unique. -/
theorem FirstAccepted.unique (hk : FirstAccepted indicator threshold θ H k)
    (hm : FirstAccepted indicator threshold θ H m) : k = m :=
  (hk.le_of_indicator_le hm.indicator_le).antisymm (hm.le_of_indicator_le hk.indicator_le)

/-- The first accepted trial is the least accepted index. -/
theorem firstAccepted_iff_nat_find_eq
    [DecidablePred fun k : ℕ => indicator (θ ^ k * H) ≤ threshold]
    (h : ∃ k : ℕ, indicator (θ ^ k * H) ≤ threshold) :
    FirstAccepted indicator threshold θ H k ↔ Nat.find h = k := by
  simp only [Nat.find_eq_iff, not_le, firstAccepted_iff]

/-- The least accepted index is the first accepted trial. -/
theorem firstAccepted_nat_find [DecidablePred fun k : ℕ => indicator (θ ^ k * H) ≤ threshold]
    (h : ∃ k : ℕ, indicator (θ ^ k * H) ≤ threshold) :
    FirstAccepted indicator threshold θ H (Nat.find h) :=
  (firstAccepted_iff_nat_find_eq h).mpr rfl

/-- A first accepted trial exists exactly when some trial is accepted. -/
theorem exists_firstAccepted_iff :
    (∃ k, FirstAccepted indicator threshold θ H k) ↔
      ∃ k : ℕ, indicator (θ ^ k * H) ≤ threshold := by
  classical
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.indicator_le⟩, fun h => ⟨_, firstAccepted_nat_find h⟩⟩

/-- Local termination of geometric rejection: if every admissible step `0 < h ≤ H` with `h ≤ δ`
is accepted for some `δ > 0`, then the rejection loop that starts from `H > 0` and reduces by
`θ ∈ (0, 1)` has a first accepted trial. -/
theorem exists_firstAccepted (hθ : 0 < θ) (hθ1 : θ < 1) (hH : 0 < H) (hδ : 0 < δ)
    (hsmall : ∀ h, 0 < h → h ≤ H → h ≤ δ → indicator h ≤ threshold) :
    ∃ k, FirstAccepted indicator threshold θ H k := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hδ hH) hθ1
  refine exists_firstAccepted_iff.mpr ⟨m, hsmall _ (by positivity) ?_ ?_⟩
  · exact mul_le_of_le_one_left hH.le (pow_le_one₀ hθ.le hθ1.le)
  · exact ((lt_div_iff₀ hH).mp hm).le

/-- If every admissible step `0 < h ≤ H` with `h ≤ δ` is accepted, then the first accepted trial
comes no later than any index `m` with `θ ^ m * H ≤ δ`. -/
theorem FirstAccepted.le_of_pow_mul_le (hk : FirstAccepted indicator threshold θ H k)
    (hθ : 0 ≤ θ) (hH : 0 ≤ H)
    (hsmall : ∀ h, 0 < h → h ≤ H → h ≤ δ → indicator h ≤ threshold) (hm : θ ^ m * H ≤ δ) :
    k ≤ m := by
  by_contra! hmk
  rcases (mul_nonneg (pow_nonneg hθ m) hH).eq_or_lt with h0 | hpos
  · -- A zero trial `θ ^ m * H = 0` forces `θ ^ k * H = 0` for the later index `k`, so trial `k`
    -- equals the rejected trial `m`.
    have hk0 : θ ^ k * H = θ ^ m * H := by
      rw [← h0]
      rcases mul_eq_zero.mp h0.symm with hθm | hH0
      · simp [pow_eq_zero_of_le hmk.le hθm]
      · simp [hH0]
    exact (hk.lt_indicator hmk).not_ge (hk0 ▸ hk.indicator_le)
  rcases le_or_gt (θ ^ m * H) H with hmH | hHm
  · exact (hk.lt_indicator hmk).not_ge (hsmall _ hpos hmH hm)
  · -- For `θ > 1` the trial `θ ^ m * H` exceeds `H`; then `H ≤ δ`, so trial `0` is accepted.
    have hH0 : 0 < H := hH.lt_of_ne (by rintro rfl; simp at hHm)
    exact (hk.lt_indicator (j := 0) (by omega)).not_ge <|
      hsmall _ (by simpa using hH0) (by simp) (by simpa using hHm.le.trans hm)

/-- The first accepted step is not much smaller than `δ`: if every admissible step `0 < h ≤ H`
with `h ≤ δ` is accepted, then the first accepted trial is at least `min H (θ * δ)`. -/
theorem FirstAccepted.min_le_pow_mul (hk : FirstAccepted indicator threshold θ H k)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hsmall : ∀ h, 0 < h → h ≤ H → h ≤ δ → indicator h ≤ threshold) :
    min H (θ * δ) ≤ θ ^ k * H := by
  have hpow : ∀ j : ℕ, θ ^ j ≤ 1 := fun _ => pow_le_one₀ hθ hθ1
  rcases le_or_gt H 0 with hH | hH
  · exact (min_le_left _ _).trans (by nlinarith [hpow k])
  cases k with
  | zero => simp
  | succ j =>
    rcases hθ.eq_or_lt with rfl | hθ
    · simp
    -- Trial `j` is rejected, so it is larger than `δ`.
    have hj : δ < θ ^ j * H := by
      by_contra hle
      exact (hk.lt_indicator j.lt_succ_self).not_ge <|
        hsmall _ (by positivity) (mul_le_of_le_one_left hH.le (hpow j)) (not_lt.mp hle)
    calc min H (θ * δ) ≤ θ * δ := min_le_right _ _
      _ ≤ θ * (θ ^ j * H) := by gcongr
      _ = θ ^ (j + 1) * H := by ring

/-- A power bound `η h ≤ C * h ^ r` with `r ≠ 0` on the admissible steps `0 < h ≤ H` gives the
small-step hypothesis for a positive absolute threshold `tol`: there is `δ > 0` such that
`η h ≤ tol` for every admissible step `h ≤ δ`. -/
theorem exists_pos_forall_le_of_le_mul_pow {η : ℝ → ℝ} {C tol : ℝ} {r : ℕ} (hr : r ≠ 0)
    (htol : 0 < tol) (hη : ∀ h, 0 < h → h ≤ H → η h ≤ C * h ^ r) :
    ∃ δ, 0 < δ ∧ ∀ h, 0 < h → h ≤ H → h ≤ δ → η h ≤ tol := by
  rcases le_or_gt C 0 with hC | hC
  · -- For `C ≤ 0` the bound is nonpositive and every `δ` works.
    refine ⟨1, one_pos, fun h hh hhH _ => (hη h hh hhH).trans ?_⟩
    exact (mul_nonpos_of_nonpos_of_nonneg hC (by positivity)).trans htol.le
  · refine ⟨min 1 (tol / C), by positivity, fun h hh hhH hhδ => (hη h hh hhH).trans ?_⟩
    calc C * h ^ r ≤ C * h := by
          gcongr
          exact pow_le_of_le_one hh.le (hhδ.trans (min_le_left _ _)) hr
      _ ≤ tol := (le_div_iff₀' hC).mp (hhδ.trans (min_le_right _ _))

/-- A power bound `η h ≤ C * h ^ r` with `2 ≤ r` on the admissible steps `0 < h ≤ H` gives the
small-step hypothesis for an error-per-unit-time threshold: there is `δ > 0` such that
`η h ≤ tol * h` for every admissible step `h ≤ δ`. -/
theorem exists_pos_forall_le_mul_of_le_mul_pow {η : ℝ → ℝ} {C tol : ℝ} {r : ℕ} (hr : 2 ≤ r)
    (htol : 0 < tol) (hη : ∀ h, 0 < h → h ≤ H → η h ≤ C * h ^ r) :
    ∃ δ, 0 < δ ∧ ∀ h, 0 < h → h ≤ H → h ≤ δ → η h ≤ tol * h := by
  have hη' : ∀ h, 0 < h → h ≤ H → η h / h ≤ C * h ^ (r - 1) := fun h hh hhH => by
    rw [div_le_iff₀ hh, mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega)]
    exact hη h hh hhH
  obtain ⟨δ, hδ, hle⟩ := exists_pos_forall_le_of_le_mul_pow (by omega) htol hη'
  exact ⟨δ, hδ, fun h hh hhH hhδ => (div_le_iff₀ hh).mp (hle h hh hhH hhδ)⟩

/-- Local termination of geometric rejection for an indicator with a power bound
`indicator h ≤ C * h ^ r`, `r ≠ 0`, on the admissible steps `0 < h ≤ H`, and a positive absolute
threshold. -/
theorem exists_firstAccepted_of_le_mul_pow {C : ℝ} {r : ℕ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hH : 0 < H) (hr : r ≠ 0) (hthreshold : 0 < threshold)
    (hbound : ∀ h, 0 < h → h ≤ H → indicator h ≤ C * h ^ r) :
    ∃ k, FirstAccepted indicator threshold θ H k := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_pos_forall_le_of_le_mul_pow hr hthreshold hbound
  exact exists_firstAccepted hθ hθ1 hH hδ hsmall

end TauCeti
