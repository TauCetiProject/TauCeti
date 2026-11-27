/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Dynamics.Entropy.FullShift
import TauCeti.Analysis.Asymptotics.ExpGrowth

/-!
# Topological entropy of the one-sided shift on a set of sequences

For a finite alphabet `α` with the discrete uniformity and any set `F ⊆ ℕ → α`, the topological
entropy of the one-sided shift on `F` is the exponential growth rate of the number of words of
length `n` read off points of `F` at the coordinates `0, …, n - 1`:

```text
coverEntropy (shift 1) F = limsup_{n → ∞} (1/n) log #{(x 0, …, x (n - 1)) | x ∈ F}.
```

Agreeing on a finite set of coordinates inside `{0, …, c - 1}` for `n` steps of the shift is
implied by agreeing on `{0, …, n + c - 1}`, so one point of `F` for each word of length `n + c`
gives a dynamical cover; agreeing at the coordinate `0` for `n` steps is agreeing on
`{0, …, n - 1}`, so every dynamical cover has a point for each word of length `n`. The word counts
are monotone, so the shift by `c` does not change their growth rate.

## Main definitions

* `TauCeti.wordsOf F n`: the words `(x 0, …, x (n - 1))` of points `x ∈ F`.
* `TauCeti.languageCount F n`: their number.

## Main results

* `TauCeti.languageCount_mono`: the word counts are monotone in `n`.
* `TauCeti.coverMincard_shift_le_languageCount`,
  `TauCeti.languageCount_le_coverMincard_shift`: the two comparisons above.
* `TauCeti.coverEntropy_shift_nat_eq_expGrowthSup`: the entropy formula.

Used to compute the entropy of subshifts of finite type (`TauCeti.Dynamics.Entropy.FiniteType`).
-/

public section

namespace TauCeti

open Dynamics Set Filter ExpGrowth SymbolicDynamics.FullShift
open scoped Uniformity ENNReal

variable {α : Type*}

/-- The words of length `n` read off points of `F` at the coordinates `0, …, n - 1`. -/
def wordsOf (F : Set (ℕ → α)) (n : ℕ) : Set (Fin n → α) :=
  (fun x i ↦ x i) '' F

@[simp]
theorem mem_wordsOf {F : Set (ℕ → α)} {n : ℕ} {w : Fin n → α} :
    w ∈ wordsOf F n ↔ ∃ x ∈ F, ∀ i : Fin n, x i = w i := by
  simp [wordsOf, funext_iff]

/-- The number of words of length `n` read off points of `F`. -/
noncomputable def languageCount (F : Set (ℕ → α)) (n : ℕ) : ℕ :=
  (wordsOf F n).ncard

theorem languageCount_def (F : Set (ℕ → α)) (n : ℕ) :
    languageCount F n = (wordsOf F n).ncard :=
  (rfl)

variable [Finite α] (F : Set (ℕ → α))

/-- The number of words read off `F` is monotone in their length. -/
theorem languageCount_mono : Monotone (languageCount F) := by
  intro m n hmn
  have h : wordsOf F m = (fun w : Fin n → α ↦ fun i : Fin m ↦ w (Fin.castLE hmn i)) ''
      wordsOf F n := by
    simp only [wordsOf, image_image, Fin.val_castLE]
  rw [languageCount_def, languageCount_def, h]
  exact ncard_image_le (toFinite _)

/-- If the coordinates `S` lie in `{0, …, c - 1}`, the minimal dynamical covers of `F` for
agreement on `S` over `n` steps of the shift have at most as many points as there are words of
length `n + c` read off `F`. -/
theorem coverMincard_shift_le_languageCount {S : Set ℕ} {c : ℕ} (hS : S ⊆ Iio c) (n : ℕ) :
    coverMincard (shift (1 : ℕ)) F (agreeOn S : SetRel (ℕ → α) (ℕ → α)) n ≤
      languageCount F (n + c) := by
  classical
  rcases F.eq_empty_or_nonempty with rfl | ⟨x₀, -⟩
  · simp [coverMincard_empty]
  have : Nonempty (ℕ → α) := ⟨x₀⟩
  set r : (ℕ → α) → Fin (n + c) → α := fun x i ↦ x i
  have hfin : (wordsOf F (n + c)).Finite := toFinite _
  let g : (Fin (n + c) → α) → ℕ → α := Function.invFunOn r F
  have hcov : IsDynCoverOf (shift (1 : ℕ)) F (agreeOn S) n
      ((hfin.toFinset.image g : Finset (ℕ → α)) : Set (ℕ → α)) := by
    intro x hx
    have hw : r x ∈ r '' F := mem_image_of_mem r hx
    refine ⟨g (r x), Finset.mem_coe.2 (Finset.mem_image_of_mem g (hfin.mem_toFinset.2 hw)), ?_⟩
    refine agreeOn_window_subset_dynEntourage_shift (a := 0) (c := c)
      (fun i hi ↦ ⟨i, hS hi, add_zero i⟩) n ?_
    rintro _ ⟨j, hj, rfl⟩
    have := congrFun (Function.invFunOn_eq hw) ⟨j, hj⟩
    simpa [r, g] using this.symm
  calc coverMincard (shift (1 : ℕ)) F (agreeOn S) n ≤ (hfin.toFinset.image g).card :=
        hcov.coverMincard_le_card
    _ ≤ hfin.toFinset.card := by exact_mod_cast Finset.card_image_le
    _ = languageCount F (n + c) := by rw [languageCount_def, ncard_eq_toFinset_card _ hfin]

omit [Finite α] in
/-- Every dynamical cover of `F` for agreement at the coordinate `0` over `n` steps of the shift
has at least as many points as there are words of length `n` read off `F`. -/
theorem languageCount_le_coverMincard_shift (n : ℕ) :
    (languageCount F n : ℕ∞) ≤
      coverMincard (shift (1 : ℕ)) F (agreeOn {0} : SetRel (ℕ → α) (ℕ → α)) n := by
  classical
  refine le_iInf₂ fun s hs ↦ ?_
  let r : (ℕ → α) → Fin n → α := fun x i ↦ x i
  have hsub : wordsOf F n ⊆ ((s.image r : Finset (Fin n → α)) : Set (Fin n → α)) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hs hx
    rw [dynEntourage_shift_agreeOn_singleton_zero] at hxy
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨y, hy, funext fun i ↦ ?_⟩)
    exact (hxy i ⟨i, i.isLt, rfl⟩).symm
  have := (ncard_le_ncard hsub (Finset.finite_toSet _)).trans_eq (ncard_coe_finset _)
  exact_mod_cast this.trans Finset.card_image_le

variable [UniformSpace α] [DiscreteUniformity α]

/-- **Entropy of the shift on a set of sequences.** For a finite discrete alphabet, the
topological entropy of the one-sided shift on any `F ⊆ ℕ → α` is the exponential growth rate of
the number of words of length `n` read off `F`. -/
theorem coverEntropy_shift_nat_eq_expGrowthSup :
    coverEntropy (shift (1 : ℕ)) F = expGrowthSup fun n ↦ (languageCount F n : ℝ≥0∞) := by
  have hmono : Monotone fun n ↦ (languageCount F n : ℝ≥0∞) :=
    fun _ _ h ↦ Nat.cast_le.2 (languageCount_mono F h)
  rw [coverEntropy_eq_iSup_basis Pi.hasBasis_uniformity_of_discreteUniformity]
  refine le_antisymm (iSup₂_le fun S hS ↦ ?_) ?_
  · obtain ⟨c, hc⟩ := hS.bddAbove
    calc coverEntropyEntourage (shift (1 : ℕ)) F (agreeOn S)
        ≤ expGrowthSup fun n ↦ (languageCount F (n + (c + 1)) : ℝ≥0∞) :=
          expGrowthSup_monotone fun n ↦ (ENat.toENNReal_mono
            (coverMincard_shift_le_languageCount F (c := c + 1)
              (fun i hi ↦ Nat.lt_add_one_of_le (hc hi)) n)).trans_eq (by simp)
      _ = _ := hmono.expGrowthSup_comp_add (c + 1)
  · refine le_iSup₂_of_le {0} (finite_singleton 0) ?_
    exact expGrowthSup_monotone fun n ↦
      (ENat.toENNReal_mono (languageCount_le_coverMincard_shift F n)).trans_eq' (by simp)

end TauCeti
