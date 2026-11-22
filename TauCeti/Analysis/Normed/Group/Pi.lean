/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Data.Fin.VecNotation

/-!
# The norm on a finite product

The norm on a nonempty finite product of seminormed groups is the maximum of the coordinate norms,
so it is attained at some coordinate (`Pi.exists_norm_apply_eq_norm`). Hence for every positive
exponent `n` its `n`-th power is at most the sum of the `n`-th powers of the coordinate norms
(`Pi.norm_pow_le_sum_norm_pow`), and prepending an entry or forming a pair gives the coordinate
maximum (`Pi.norm_vecCons`, `Pi.norm_pair`).
-/

public section

/-- The norm on a nonempty finite product of seminormed groups is attained at some coordinate. -/
theorem Pi.exists_norm_apply_eq_norm {ι : Type*} [Fintype ι] [Nonempty ι] {E : ι → Type*}
    [∀ i, SeminormedAddGroup (E i)] (f : ∀ i, E i) : ∃ i, ‖f i‖ = ‖f‖ := by
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty fun i ↦ ‖f i‖₊
  exact ⟨i, by rw [Pi.norm_def, hi, coe_nnNorm]⟩

/-- The `n`-th power of the norm on a finite product is at most the sum of the `n`-th powers of
the coordinate norms, for every positive exponent `n`. -/
theorem Pi.norm_pow_le_sum_norm_pow {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, SeminormedAddGroup (E i)] (f : ∀ i, E i) {n : ℕ} (hn : n ≠ 0) :
    ‖f‖ ^ n ≤ ∑ i, ‖f i‖ ^ n := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Subsingleton.elim f 0, hn]
  obtain ⟨i, hi⟩ := Pi.exists_norm_apply_eq_norm f
  rw [← hi]
  exact Finset.single_le_sum (f := fun i ↦ ‖f i‖ ^ n) (fun _ _ ↦ by positivity)
    (Finset.mem_univ i)

/-- The norm of prepending an entry `a` to `v : Fin n → E` in the product sup-norm is
`max ‖a‖ ‖v‖`. -/
@[simp]
theorem Pi.norm_vecCons {n : ℕ} {E : Type*} [SeminormedAddGroup E] (a : E) (v : Fin n → E) :
    ‖Matrix.vecCons a v‖ = max ‖a‖ ‖v‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg a))).mpr ?_)
    (max_le (by simpa using norm_le_pi_norm (Matrix.vecCons a v) 0)
      ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i ↦ by
        simpa using norm_le_pi_norm (Matrix.vecCons a v) i.succ))
  intro k
  refine Fin.cases (le_max_left _ _) (fun i ↦ ?_) k
  simpa using le_max_of_le_right (norm_le_pi_norm v i)

/-- The norm of a two-entry vector `![a, b]` in the product sup-norm is `max ‖a‖ ‖b‖`. -/
theorem Pi.norm_pair {E : Type*} [SeminormedAddGroup E] (a b : E) :
    ‖![a, b]‖ = max ‖a‖ ‖b‖ := by
  simp [Subsingleton.elim (Matrix.vecEmpty : Fin 0 → E) 0]
