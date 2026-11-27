/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import TauCeti.Dynamics.Entropy.Language
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

The proof counts admissible words by entries of powers of `M`. The products
`∏ k, M (w k) (w (k + 1))` over words `w` of length `n + 1` starting at `i` sum to `(M ^ n *ᵥ 1) i`,
and for the `0`-`1` matrix `M` such a product is the indicator of admissibility; if every symbol has
a successor, every admissible word extends to a point of `sftOneSided A`, so the number of words of
length `n + 1` read off `sftOneSided A` is `∑ i, (M ^ n *ᵥ 1) i`. These sums have exponential
growth rate `log ρ` by `Matrix.expGrowthSup_sum_pow_mulVec_eq` (Gelfand's formula and the
Perron–Frobenius theorem).

## Main definitions

* `Matrix.pathWeight M w`: the product `∏ k, M (w k) (w (k + 1))` along a word `w`.
* `TauCeti.transitionMatrix R A`: the `0`-`1` matrix of a relation `A`, with entries in `R`.
* `TauCeti.sftOneSided A`: the one-sided one-step subshift of finite type of `A`.

## Main results

* `Matrix.sum_pathWeight_cons`: the path weights of words starting at `i` sum to `(M ^ n *ᵥ 1) i`.
* `TauCeti.languageCount_sftOneSided`: the number of words of length `n + 1` read off
  `sftOneSided A` is `∑ i, (M ^ n *ᵥ 1) i`.
* `TauCeti.coverEntropy_shift_sftOneSided`: the entropy formula.
-/

public section

open Dynamics Set ExpGrowth SymbolicDynamics.FullShift
open scoped Matrix ENNReal

namespace Matrix

variable {α R : Type*}

section CommMonoid

variable [CommMonoid R]

/-- The product `∏ k, M (w k) (w (k + 1))` of the entries of `M` along a word `w` of length
`n + 1`. -/
def pathWeight (M : Matrix α α R) {n : ℕ} (w : Fin (n + 1) → α) : R :=
  ∏ k : Fin n, M (w k.castSucc) (w k.succ)

theorem pathWeight_def (M : Matrix α α R) {n : ℕ} (w : Fin (n + 1) → α) :
    M.pathWeight w = ∏ k : Fin n, M (w k.castSucc) (w k.succ) :=
  (rfl)

theorem pathWeight_cons (M : Matrix α α R) {n : ℕ} (i : α) (w : Fin (n + 1) → α) :
    M.pathWeight (Fin.cons i w : Fin (n + 2) → α) = M i (w 0) * M.pathWeight w := by
  simp only [pathWeight_def, Fin.prod_univ_succ]
  congr 1

end CommMonoid

variable [Fintype α] [DecidableEq α] [CommSemiring R]

/-- The path weights of the words of length `n + 1` starting at `i` sum to `(M ^ n *ᵥ 1) i`. -/
theorem sum_pathWeight_cons (M : Matrix α α R) (n : ℕ) (i : α) :
    ∑ w : Fin n → α, M.pathWeight (Fin.cons i w : Fin (n + 1) → α) = (M ^ n *ᵥ 1) i := by
  induction n generalizing i with
  | zero => simp [pathWeight_def]
  | succ n ih =>
    rw [pow_succ', ← mulVec_mulVec, mulVec, dotProduct,
      ← Fintype.sum_equiv (Fin.consEquiv fun _ ↦ α) (fun p ↦ M.pathWeight
        (Fin.cons i (Fin.cons p.1 p.2 : Fin (n + 1) → α) : Fin (n + 2) → α)) _ fun _ ↦ rfl,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [pathWeight_cons, Fin.cons_zero, ← Finset.mul_sum, ih]

/-- All path weights of words of length `n + 1` sum to `∑ i, (M ^ n *ᵥ 1) i`. -/
theorem sum_pathWeight (M : Matrix α α R) (n : ℕ) :
    ∑ w : Fin (n + 1) → α, M.pathWeight w = ∑ i, (M ^ n *ᵥ 1) i := by
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ ↦ α) (fun p ↦ M.pathWeight
      (Fin.cons p.1 p.2 : Fin (n + 1) → α)) _ fun _ ↦ rfl, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ ↦ sum_pathWeight_cons M n i

end Matrix

namespace TauCeti

variable {α : Type*}

section TransitionMatrix

variable (R : Type*)

/-- The `0`-`1` transition matrix of a relation `A`: its `(i, j)` entry is `1` if `A i j` holds
and `0` otherwise. -/
def transitionMatrix [Zero R] [One R] (A : α → α → Bool) : Matrix α α R :=
  Matrix.of fun i j ↦ if A i j then 1 else 0

@[simp]
theorem transitionMatrix_apply [Zero R] [One R] (A : α → α → Bool) (i j : α) :
    transitionMatrix R A i j = if A i j then 1 else 0 :=
  (rfl)

variable {R}

/-- The entries of a transition matrix are nonnegative. -/
theorem transitionMatrix_nonneg [Zero R] [One R] [Preorder R] [ZeroLEOneClass R]
    (A : α → α → Bool) (i j : α) : 0 ≤ transitionMatrix R A i j := by
  rw [transitionMatrix_apply]
  split_ifs
  exacts [zero_le_one, le_rfl]

/-- The path weight of a word for a transition matrix is the indicator of its admissibility. -/
theorem pathWeight_transitionMatrix [CommMonoidWithZero R] (A : α → α → Bool) {n : ℕ}
    (w : Fin (n + 1) → α) :
    (transitionMatrix R A).pathWeight w =
      if ∀ k : Fin n, A (w k.castSucc) (w k.succ) then 1 else 0 := by
  split_ifs with h
  · exact Finset.prod_eq_one fun k _ ↦ by simp [h k]
  · push Not at h
    obtain ⟨k, hk⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])

end TransitionMatrix

/-- The one-sided one-step subshift of finite type of a relation `A`: the sequences `x` with
`A (x k) (x (k + 1))` for every `k`. -/
def sftOneSided (A : α → α → Bool) : Set (ℕ → α) :=
  {x | ∀ k, A (x k) (x (k + 1))}

@[simp]
theorem mem_sftOneSided {A : α → α → Bool} {x : ℕ → α} :
    x ∈ sftOneSided A ↔ ∀ k, A (x k) (x (k + 1)) :=
  Iff.rfl

/-- The shift maps a subshift of finite type into itself. -/
theorem mapsTo_shift_sftOneSided (A : α → α → Bool) :
    MapsTo (shift (1 : ℕ)) (sftOneSided A) (sftOneSided A) := by
  intro x hx
  rw [mem_sftOneSided] at hx ⊢
  intro k
  simpa [shift_apply, add_assoc] using hx (1 + k)

/-- If every symbol has a successor, every admissible word extends to a point of
`sftOneSided A`. -/
theorem exists_mem_sftOneSided_of_admissible {A : α → α → Bool} (hrow : ∀ i, ∃ j, A i j)
    {n : ℕ} {w : Fin (n + 1) → α} (hw : ∀ k : Fin n, A (w k.castSucc) (w k.succ)) :
    ∃ x ∈ sftOneSided A, ∀ i : Fin (n + 1), x i = w i := by
  choose f hf using hrow
  let x : ℕ → α := fun k ↦
    if h : k ≤ n then w ⟨k, Nat.lt_succ_of_le h⟩ else f^[k - n] (w (Fin.last n))
  have hxw (k : ℕ) (hk : k ≤ n) : x k = w ⟨k, Nat.lt_succ_of_le hk⟩ := by
    simp [x, hk]
  have hx (k : ℕ) (hk : n ≤ k) : x k = f^[k - n] (w (Fin.last n)) := by
    rcases hk.eq_or_lt with rfl | hk
    · simp [hxw n le_rfl, Fin.last]
    · simp [x, hk.not_ge]
  refine ⟨x, mem_sftOneSided.2 fun k ↦ ?_, fun i ↦ by simpa using hxw i i.is_le⟩
  rcases lt_or_ge k n with hk | hk
  · rw [hxw k hk.le, hxw (k + 1) hk]
    simpa using hw ⟨k, hk⟩
  · rw [hx k hk, hx (k + 1) (by omega), show k + 1 - n = k - n + 1 by omega,
      Function.iterate_succ_apply']
    exact hf _

variable [Fintype α] [DecidableEq α]

/-- If every symbol has a successor, the words of length `n + 1` read off `sftOneSided A` are
counted by `∑ i, (M ^ n *ᵥ 1) i` for the transition matrix `M` of `A`. -/
theorem languageCount_sftOneSided {R : Type*} [CommSemiring R] {A : α → α → Bool}
    (hrow : ∀ i, ∃ j, A i j) (n : ℕ) :
    (languageCount (sftOneSided A) (n + 1) : R) = ∑ i, (transitionMatrix R A ^ n *ᵥ 1) i := by
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
  exact Finset.sum_congr rfl fun w _ ↦ (pathWeight_transitionMatrix A w).symm

omit [DecidableEq α] in
/-- **Entropy of a subshift of finite type.** For a finite discrete alphabet and a relation `A`
in which every symbol has a successor, the one-sided subshift of finite type `sftOneSided A` has
topological entropy `log (spectralRadius ℝ M)` for the `0`-`1` transition matrix `M` of `A`. -/
theorem coverEntropy_shift_sftOneSided [UniformSpace α] [DiscreteUniformity α]
    {A : α → α → Bool} (hrow : ∀ i, ∃ j, A i j) :
    coverEntropy (shift (1 : ℕ)) (sftOneSided A) =
      ENNReal.log (spectralRadius ℝ (transitionMatrix ℝ A)) := by
  classical
  have hmono : Monotone fun n ↦ (languageCount (sftOneSided A) n : ℝ≥0∞) :=
    fun _ _ h ↦ Nat.cast_le.2 (languageCount_mono _ h)
  have hL : (fun n ↦ (languageCount (sftOneSided A) (n + 1) : ℝ≥0∞)) =
      fun n ↦ ENNReal.ofReal (∑ i, (transitionMatrix ℝ A ^ n *ᵥ 1) i) := by
    funext n
    rw [← languageCount_sftOneSided hrow n, ENNReal.ofReal_natCast]
  rw [coverEntropy_shift_nat_eq_expGrowthSup, ← hmono.expGrowthSup_comp_add 1, hL,
    Matrix.expGrowthSup_sum_pow_mulVec_eq (transitionMatrix_nonneg A)]

omit [DecidableEq α] in
/-- The `liminf` topological entropy of a subshift of finite type is also
`log (spectralRadius ℝ M)`. -/
theorem coverEntropyInf_shift_sftOneSided [UniformSpace α] [DiscreteUniformity α]
    {A : α → α → Bool} (hrow : ∀ i, ∃ j, A i j) :
    coverEntropyInf (shift (1 : ℕ)) (sftOneSided A) =
      ENNReal.log (spectralRadius ℝ (transitionMatrix ℝ A)) :=
  (coverEntropyInf_eq_coverEntropy _ (mapsTo_shift_sftOneSided A)).trans
    (coverEntropy_shift_sftOneSided hrow)

end TauCeti
