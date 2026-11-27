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

/-- If every symbol has a successor, the words of length `n + 1` read off `sftOneSided A` are
counted by `∑ i, (M ^ n *ᵥ 1) i` for the transition matrix `M` of `A`. -/
theorem languageCount_sftOneSided {R : Type*} [CommSemiring R] {A : α → α → Bool}
    (hrow : ∀ i, ∃ j, A i j) (n : ℕ) :
    (languageCount (sftOneSided A) (n + 1) : R) = ∑ i, (sftTransitionMatrix R A ^ n *ᵥ 1) i := by
  have hwords : wordsOf (sftOneSided A) (n + 1) =
      ((Finset.univ.filter fun w : Fin (n + 1) → α ↦
        ∀ k : Fin n, A (w k.castSucc) (w k.succ) : Finset _) : Set (Fin (n + 1) → α)) := by
    ext w
    simp only [mem_wordsOf, Finset.coe_filter, Finset.mem_univ, true_and, mem_ofPred_eq]
    refine ⟨fun ⟨x, hx, hxw⟩ k ↦ ?_, fun hw ↦ exists_mem_sftOneSided_of_admissible hrow hw⟩
    rw [← hxw, ← hxw]
    simpa using mem_sftOneSided.1 hx k
  rw [languageCount_def, hwords, ncard_coe_finset, ← Matrix.sum_pathWeight, Finset.card_filter]
  push_cast
  exact Finset.sum_congr rfl fun w _ ↦ (pathWeight_sftTransitionMatrix A w).symm

omit [DecidableEq α] in
/-- **Entropy of a subshift of finite type.** For a finite discrete alphabet and a relation `A`
in which every symbol has a successor, the one-sided subshift of finite type `sftOneSided A` has
topological entropy `log (spectralRadius ℝ M)` for the `0`-`1` transition matrix `M` of `A`. -/
theorem coverEntropy_shift_sftOneSided [UniformSpace α] [DiscreteUniformity α]
    {A : α → α → Bool} (hrow : ∀ i, ∃ j, A i j) :
    coverEntropy (shift (1 : ℕ)) (sftOneSided A) =
      ENNReal.log (spectralRadius ℝ (sftTransitionMatrix ℝ A)) := by
  classical
  have hmono : Monotone fun n ↦ (languageCount (sftOneSided A) n : ℝ≥0∞) :=
    fun _ _ h ↦ Nat.cast_le.2 (languageCount_mono _ h)
  have hL : (fun n ↦ (languageCount (sftOneSided A) (n + 1) : ℝ≥0∞)) =
      fun n ↦ ENNReal.ofReal (∑ i, (sftTransitionMatrix ℝ A ^ n *ᵥ 1) i) := by
    funext n
    rw [← languageCount_sftOneSided hrow n, ENNReal.ofReal_natCast]
  rw [coverEntropy_shift_nat_eq_expGrowthSup, ← hmono.expGrowthSup_comp_add 1, hL,
    Matrix.expGrowthSup_sum_pow_mulVec_eq (sftTransitionMatrix_nonneg A)]

omit [DecidableEq α] in
/-- The `liminf` topological entropy of a subshift of finite type is also
`log (spectralRadius ℝ M)`. -/
theorem coverEntropyInf_shift_sftOneSided [UniformSpace α] [DiscreteUniformity α]
    {A : α → α → Bool} (hrow : ∀ i, ∃ j, A i j) :
    coverEntropyInf (shift (1 : ℕ)) (sftOneSided A) =
      ENNReal.log (spectralRadius ℝ (sftTransitionMatrix ℝ A)) :=
  (coverEntropyInf_eq_coverEntropy _ (mapsTo_shift_sftOneSided A)).trans
    (coverEntropy_shift_sftOneSided hrow)

end TauCeti
