/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import TauCeti.Dynamics.Entropy.Language
public import TauCeti.Dynamics.SymbolicDynamics.FiniteType
import TauCeti.Analysis.Asymptotics.ExpGrowth
import TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Growth

/-!
# Topological entropy of one-step subshifts of finite type

For a finite alphabet `α` and any relation `A : α → α → Bool`, the one-sided one-step subshift of
finite type `TauCeti.sftOneSided A ⊆ ℕ → α` consists of the sequences `x` with `A (x k) (x (k + 1))`
for every `k`. Its topological entropy under the shift is `log` of the spectral radius of the
`0`-`1` transition matrix `M` of `A`:

```text
coverEntropy (shift 1) (sftOneSided A) = log (spectralRadius ℝ M).
```

No symbol needs a successor, and symbols without successors need not be pruned first. The proof
compares the language counts `L n` of `sftOneSided A` with the counts `N n` of admissible words of
length `n + 1`. The path weights `∏ k, M (w k) (w (k + 1))` (`Matrix.pathWeight`) are the
indicators of admissibility, so `N n = ∑ i, (M ^ n *ᵥ 1) i`. Every word of `sftOneSided A` is
admissible, so `L (n + 1) ≤ N n`; conversely, the prefix of length `n + 1` of an admissible word of
length `n + card α + 1` closes a cycle and is a word of `sftOneSided A`, so
`N (n + card α) ≤ card α ^ card α * L (n + 1)`. Since `L` is monotone, `L` and `N` have the same
exponential growth rate, which is `log ρ` by `Matrix.expGrowthSup_sum_pow_mulVec_eq` (Gelfand's
formula and the Perron–Frobenius theorem). The subshift, its transition matrix and the word
comparisons are in `TauCeti.Dynamics.SymbolicDynamics.FiniteType`.

## Main results

* `TauCeti.languageCount_sftOneSided`: if every symbol has a successor, the number of words of
  length `n + 1` read off `sftOneSided A` is `∑ i, (M ^ n *ᵥ 1) i`.
* `TauCeti.coverEntropy_shift_sftOneSided`: the entropy formula, for every relation `A`.
* `TauCeti.coverEntropyInf_shift_sftOneSided`: the same formula for the `liminf` entropy.

## References

* D. Lind and B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, Cambridge University
  Press, 1995, §4.1 and Theorem 4.3.1.
* P. Walters, *An Introduction to Ergodic Theory*, Graduate Texts in Mathematics 79, Springer,
  1982, Theorem 7.13.
-/

public section

open Dynamics Set ExpGrowth SymbolicDynamics.FullShift
open scoped Matrix ENNReal

namespace TauCeti

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- If every symbol has a successor, the words of length `n + 1` read off `sftOneSided A` are
counted by `∑ i, (M ^ n *ᵥ 1) i` for the transition matrix `M` of `A`. -/
theorem languageCount_sftOneSided {R : Type*} [CommSemiring R] {A : α → α → Bool}
    (hrow : ∀ i, ∃ j, A i j) (n : ℕ) :
    (languageCount (sftOneSided A) (n + 1) : R) = ∑ i, (sftTransitionMatrix R A ^ n *ᵥ 1) i := by
  have hwords : wordsOf (sftOneSided A) (n + 1) = (sftAdmissibleWords A n : Set _) := by
    ext w
    simp [mem_wordsOf_sftOneSided hrow]
  rw [languageCount_def, hwords, ncard_coe_finset, card_sftAdmissibleWords]

omit [DecidableEq α] in
/-- **Entropy of a subshift of finite type.** For a finite discrete alphabet and any relation `A`,
the one-sided subshift of finite type `sftOneSided A` has topological entropy
`log (spectralRadius ℝ M)` for the `0`-`1` transition matrix `M` of `A`. Symbols without
successors need not be pruned first: the language counts and the counts of admissible words
differ by at most the factor `card α ^ card α` after a shift of `card α`. -/
theorem coverEntropy_shift_sftOneSided [UniformSpace α] [DiscreteUniformity α]
    (A : α → α → Bool) :
    coverEntropy (shift (1 : ℕ)) (sftOneSided A) =
      ENNReal.log (spectralRadius ℝ (sftTransitionMatrix ℝ A)) := by
  classical
  set c := Fintype.card α
  set L : ℕ → ℝ≥0∞ := fun n ↦ (languageCount (sftOneSided A) n : ℝ≥0∞)
  set N : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal (∑ i, (sftTransitionMatrix ℝ A ^ n *ᵥ 1) i)
  have hmono : Monotone L := fun _ _ h ↦ Nat.cast_le.2 (languageCount_mono _ h)
  -- The two comparisons between the language counts `L` and the admissible counts `N`.
  have hLN (n : ℕ) : L (n + 1) ≤ N n := by
    simp only [L, N, ← card_sftAdmissibleWords (R := ℝ), ENNReal.ofReal_natCast, Nat.cast_le]
    exact languageCount_sftOneSided_le A n
  have hNL (n : ℕ) : N (n + c) ≤ ((c ^ c : ℕ) : ℝ≥0∞) * L (n + c + 1) := by
    simp only [N, ← card_sftAdmissibleWords (R := ℝ), ENNReal.ofReal_natCast]
    calc _ ≤ ((c ^ c * languageCount (sftOneSided A) (n + 1) : ℕ) : ℝ≥0∞) :=
          Nat.cast_le.2 (card_sftAdmissibleWords_le_mul_languageCount A n)
      _ ≤ ((c ^ c : ℕ) : ℝ≥0∞) * L (n + c + 1) := by
          rw [Nat.cast_mul]
          gcongr
          exact hmono (by omega)
  rw [coverEntropy_shift_nat_eq_expGrowthSup, ← hmono.expGrowthSup_comp_add 1,
    ← Matrix.expGrowthSup_sum_pow_mulVec_eq (sftTransitionMatrix_nonneg A)]
  refine le_antisymm (expGrowthSup_monotone hLN)
    (expGrowthSup_le_of_eventually_le (b := (c ^ c : ℕ)) (ENNReal.natCast_ne_top _)
      (Filter.eventually_atTop.2 ⟨c, fun m hm ↦ ?_⟩))
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hm
  exact hNL n

omit [DecidableEq α] in
/-- The `liminf` topological entropy of a subshift of finite type is also
`log (spectralRadius ℝ M)`. -/
theorem coverEntropyInf_shift_sftOneSided [UniformSpace α] [DiscreteUniformity α]
    (A : α → α → Bool) :
    coverEntropyInf (shift (1 : ℕ)) (sftOneSided A) =
      ENNReal.log (spectralRadius ℝ (sftTransitionMatrix ℝ A)) :=
  (coverEntropyInf_eq_coverEntropy _ (mapsTo_shift_sftOneSided A)).trans
    (coverEntropy_shift_sftOneSided A)

end TauCeti
