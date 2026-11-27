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

For a finite alphabet `α` and a relation `A : α → α → Bool`, the one-sided one-step subshift of
finite type `TauCeti.sftOneSided A ⊆ ℕ → α` consists of the sequences `x` with `A (x k) (x (k + 1))`
for every `k`. If every symbol has a successor, its topological entropy under the shift is `log` of
the spectral radius of the `0`-`1` transition matrix `M` of `A`:

```text
coverEntropy (shift 1) (sftOneSided A) = log (spectralRadius ℝ M).
```

The proof counts admissible words by entries of powers of `M`. The path weights
`∏ k, M (w k) (w (k + 1))` (`Matrix.pathWeight`) over words `w` of length `n + 1` starting at `i`
sum to `(M ^ n *ᵥ 1) i`, and for the `0`-`1` matrix `M` such a product is the indicator of
admissibility; if every symbol has a successor, every admissible word extends to a point of
`sftOneSided A`, so the number of words of length `n + 1` read off `sftOneSided A` is
`∑ i, (M ^ n *ᵥ 1) i`. These sums have exponential growth rate `log ρ` by
`Matrix.expGrowthSup_sum_pow_mulVec_eq` (Gelfand's formula and the Perron–Frobenius theorem).
The subshift and its transition matrix are defined in
`TauCeti.Dynamics.SymbolicDynamics.FiniteType`.

## Main results

* `TauCeti.languageCount_sftOneSided`: the number of words of length `n + 1` read off
  `sftOneSided A` is `∑ i, (M ^ n *ᵥ 1) i`.
* `TauCeti.coverEntropy_shift_sftOneSided`: the entropy formula.
-/

public section

open Dynamics Set ExpGrowth SymbolicDynamics.FullShift
open scoped Matrix ENNReal

namespace TauCeti

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The admissible words of length `n + 1` are counted by `∑ i, (M ^ n *ᵥ 1) i` for the transition
matrix `M` of `A`. -/
theorem card_admissible_eq_sum {R : Type*} [CommSemiring R] (A : α → α → Bool) (n : ℕ) :
    ((Finset.univ.filter fun w : Fin (n + 1) → α ↦
      ∀ k : Fin n, A (w k.castSucc) (w k.succ)).card : R) =
        ∑ i, (sftTransitionMatrix R A ^ n *ᵥ 1) i := by
  rw [← Matrix.sum_pathWeight, Finset.card_filter]
  push_cast
  exact Finset.sum_congr rfl fun w _ ↦ (pathWeight_sftTransitionMatrix A w).symm

/-- If every symbol has a successor, the words of length `n + 1` read off `sftOneSided A` are
counted by `∑ i, (M ^ n *ᵥ 1) i` for the transition matrix `M` of `A`. -/
theorem languageCount_sftOneSided {R : Type*} [CommSemiring R] {A : α → α → Bool}
    (hrow : ∀ i, ∃ j, A i j) (n : ℕ) :
    (languageCount (sftOneSided A) (n + 1) : R) = ∑ i, (sftTransitionMatrix R A ^ n *ᵥ 1) i := by
  have hwords : wordsOf (sftOneSided A) (n + 1) =
      ((Finset.univ.filter fun w : Fin (n + 1) → α ↦
        ∀ k : Fin n, A (w k.castSucc) (w k.succ) : Finset _) : Set (Fin (n + 1) → α)) := by
    ext w
    simp [mem_wordsOf_sftOneSided hrow]
  rw [languageCount_def, hwords, ncard_coe_finset, card_admissible_eq_sum]

omit [DecidableEq α] in
/-- The words of length `n + 1` read off `sftOneSided A` are at most the admissible ones. -/
theorem languageCount_sftOneSided_le (A : α → α → Bool) (n : ℕ) :
    languageCount (sftOneSided A) (n + 1) ≤ (Finset.univ.filter fun w : Fin (n + 1) → α ↦
      ∀ k : Fin n, A (w k.castSucc) (w k.succ)).card := by
  rw [languageCount_def, ← ncard_coe_finset]
  refine ncard_le_ncard (fun w hw ↦ ?_) (Finset.finite_toSet _)
  simpa using admissible_of_mem_wordsOf_sftOneSided hw

omit [DecidableEq α] in
/-- **Pruning, counting form.** The admissible words of length `m + 1` are at most
`card α ^ card α` times the words of length `m - card α + 1` read off `sftOneSided A`: such a word
is its prefix of length `n + 1`, a word of `sftOneSided A`, followed by `card α` symbols. -/
theorem card_admissible_le_mul_languageCount (A : α → α → Bool) (n : ℕ) :
    (Finset.univ.filter fun w : Fin (n + Fintype.card α + 1) → α ↦
      ∀ k : Fin (n + Fintype.card α), A (w k.castSucc) (w k.succ)).card ≤
        languageCount (sftOneSided A) (n + 1) * Fintype.card α ^ Fintype.card α := by
  set c := Fintype.card α
  let f : (Fin (n + c + 1) → α) → (Fin (n + 1) → α) × (Fin c → α) := fun w ↦
    (fun i ↦ w (Fin.castLE (by omega) i), fun j ↦ w ⟨n + 1 + j, by omega⟩)
  have hf : Function.Injective f := fun w w' h ↦ by
    simp only [f, Prod.mk.injEq, funext_iff] at h
    funext i
    rcases lt_or_ge (i : ℕ) (n + 1) with hi | hi
    · simpa using h.1 ⟨i, hi⟩
    · simpa [show n + 1 + (i - (n + 1)) = i by omega] using h.2 ⟨i - (n + 1), by omega⟩
  rw [← ncard_coe_finset, languageCount_def,
    show c ^ c = (univ : Set (Fin c → α)).ncard by simp [c], ← ncard_prod]
  refine ncard_le_ncard_of_injOn f (fun w hw ↦ ⟨?_, mem_univ _⟩) hf.injOn
    ((toFinite _).prod (toFinite _))
  exact mem_wordsOf_sftOneSided_of_admissible le_rfl (by simpa using hw)

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
  have hN (n : ℕ) : N n = ((Finset.univ.filter fun w : Fin (n + 1) → α ↦
      ∀ k : Fin n, A (w k.castSucc) (w k.succ)).card : ℝ≥0∞) := by
    simp only [N, ← card_admissible_eq_sum (R := ℝ), ENNReal.ofReal_natCast]
  rw [coverEntropy_shift_nat_eq_expGrowthSup, ← hmono.expGrowthSup_comp_add 1,
    ← Matrix.expGrowthSup_sum_pow_mulVec_eq (sftTransitionMatrix_nonneg A)]
  refine le_antisymm (expGrowthSup_monotone fun n ↦ ?_)
    (expGrowthSup_le_of_eventually_le (b := (c ^ c : ℕ)) (ENNReal.natCast_ne_top _)
      (Filter.eventually_atTop.2 ⟨c, fun m hm ↦ ?_⟩))
  · change L (n + 1) ≤ N n
    rw [hN]
    exact Nat.cast_le.2 (languageCount_sftOneSided_le A n)
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hm
    change N (n + c) ≤ ((c ^ c : ℕ) : ℝ≥0∞) * L (n + c + 1)
    rw [hN, mul_comm]
    calc _ ≤ ((languageCount (sftOneSided A) (n + 1) * c ^ c : ℕ) : ℝ≥0∞) :=
          Nat.cast_le.2 (card_admissible_le_mul_languageCount A n)
      _ ≤ L (n + c + 1) * ((c ^ c : ℕ) : ℝ≥0∞) := by
          rw [Nat.cast_mul]
          gcongr
          exact hmono (by omega)

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
