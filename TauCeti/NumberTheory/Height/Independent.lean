/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Height.NumberField
public import TauCeti.Order.Northcott.Sequence

/-!
# Sequences of rapidly growing height

Roth's theorem is proved by contradiction from an infinite set of solutions, and the proof needs
from that set a tuple of solutions whose heights are spread out: the first height is at least a
large `L`, so that the error terms of the auxiliary polynomial are small against every height,
and each height is at least `M` times the previous one, so that the partial degrees
`d j ≈ D / h (β j)` drop fast enough for Roth's lemma. Such a sequence is called
`(L, M)`-independent. By Northcott's theorem every infinite subset of a number field contains one,
for all `L` and `M`.

The heights are Mathlib's relative logarithmic heights `Height.logHeight₁`; since `M` is a ratio
of heights and `L` is arbitrary, the notion is the same for the absolute heights.

## Main results

* `TauCeti.IsHeightIndependent`: `(L, M)`-independence of a sequence.
* `Set.Infinite.exists_isHeightIndependent`: every infinite set in a field with the Northcott
  property contains an `(L, M)`-independent sequence.
* `TauCeti.IsHeightIndependent.strictMono_logHeight₁` and `TauCeti.IsHeightIndependent.injective`:
  for `0 < L` and `1 < M` the heights strictly increase and the terms are distinct.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), 6.4.4.
* The statements follow Ralf Stephan's formalization
  `DiophantineApproximation/IndependentHeights.lean` in `rwst/Subspace-Theorems` (Apache 2.0).
-/

public section

open Height

namespace TauCeti

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

/-- A sequence `β` is **`(L, M)`-independent** if its first term has logarithmic height at least
`L` and each term has logarithmic height at least `M` times that of its predecessor. -/
def IsHeightIndependent (L M : ℝ) (β : ℕ → K) : Prop :=
  L ≤ logHeight₁ (β 0) ∧ ∀ j, M * logHeight₁ (β j) ≤ logHeight₁ (β (j + 1))

theorem isHeightIndependent_iff {L M : ℝ} {β : ℕ → K} :
    IsHeightIndependent L M β ↔
      L ≤ logHeight₁ (β 0) ∧ ∀ j, M * logHeight₁ (β j) ≤ logHeight₁ (β (j + 1)) :=
  Iff.rfl

namespace IsHeightIndependent

variable {L M : ℝ} {β : ℕ → K}

theorem le_logHeight₁_zero (hβ : IsHeightIndependent L M β) : L ≤ logHeight₁ (β 0) :=
  hβ.1

theorem mul_logHeight₁_le (hβ : IsHeightIndependent L M β) (j : ℕ) :
    M * logHeight₁ (β j) ≤ logHeight₁ (β (j + 1)) :=
  hβ.2 j

/-- The logarithmic heights of an `(L, M)`-independent sequence with `0 < L` and `1 < M` are
strictly increasing. -/
theorem strictMono_logHeight₁ (hβ : IsHeightIndependent L M β) (hL : 0 < L) (hM : 1 < M) :
    StrictMono fun j ↦ logHeight₁ (β j) := by
  have hpos : ∀ j, 0 < logHeight₁ (β j) := by
    intro j
    induction j with
    | zero => exact hL.trans_le hβ.1
    | succ j ih => exact (by nlinarith : 0 < M * logHeight₁ (β j)).trans_le (hβ.2 j)
  refine strictMono_nat_of_lt_succ fun j ↦ lt_of_lt_of_le ?_ (hβ.2 j)
  nlinarith [hpos j]

/-- The terms of an `(L, M)`-independent sequence with `0 < L` and `1 < M` are distinct. -/
theorem injective (hβ : IsHeightIndependent L M β) (hL : 0 < L) (hM : 1 < M) :
    Function.Injective β :=
  fun _ _ h ↦ (hβ.strictMono_logHeight₁ hL hM).injective (congrArg logHeight₁ h)

end IsHeightIndependent

end TauCeti

namespace Set.Infinite

open TauCeti

variable {K : Type*} [Field K] [AdmissibleAbsValues K] [Northcott (logHeight₁ (K := K))]

/-- **Every infinite set contains an `(L, M)`-independent sequence**, in a field whose logarithmic
height has the Northcott property, such as a number field. -/
theorem exists_isHeightIndependent {X : Set K} (hX : X.Infinite) (L M : ℝ) :
    ∃ β : ℕ → K, (∀ j, β j ∈ X) ∧ IsHeightIndependent L M β := by
  obtain ⟨β, hβX, h₀, hβ⟩ := Northcott.exists_seq_mem_lt logHeight₁ (M * ·) hX L
  exact ⟨β, hβX, h₀.le, fun j ↦ (hβ j).le⟩

end Set.Infinite

/-! ### Tests -/

/-- Over `ℚ` there is a sequence of strictly increasing height. -/
example : ∃ β : ℕ → ℚ, StrictMono fun j ↦ logHeight₁ (β j) := by
  obtain ⟨β, -, hβ⟩ := Set.infinite_univ.exists_isHeightIndependent (K := ℚ) 1 2
  exact ⟨β, hβ.strictMono_logHeight₁ one_pos one_lt_two⟩

/-- The infinitude of `X` is needed: every element of `{0, 1}` has height `0`, so no sequence in
it is `(1, 2)`-independent. -/
example : ¬ ∃ β : ℕ → ℚ, (∀ j, β j ∈ ({0, 1} : Set ℚ)) ∧ TauCeti.IsHeightIndependent 1 2 β := by
  rintro ⟨β, hβX, hβ⟩
  have h₀ := hβ.le_logHeight₁_zero
  rcases hβX 0 with h | h <;> rw [h] at h₀ <;> norm_num at h₀
