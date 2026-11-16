/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Powers of the norm on a finite product

The norm on a finite product of seminormed groups is the maximum of the coordinate norms, so for
every positive exponent `n` its `n`-th power is at most the sum of the `n`-th powers of the
coordinate norms (`Pi.norm_pow_le_sum_norm_pow`).
-/

public section

/-- The `n`-th power of the norm on a finite product is at most the sum of the `n`-th powers of
the coordinate norms, for every positive exponent `n`. -/
theorem Pi.norm_pow_le_sum_norm_pow {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, SeminormedAddGroup (E i)] (f : ∀ i, E i) {n : ℕ} (hn : n ≠ 0) :
    ‖f‖ ^ n ≤ ∑ i, ‖f i‖ ^ n := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Subsingleton.elim f 0, hn]
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty fun i ↦ ‖f i‖₊
  have hf : ‖f‖ = ‖f i‖ := by rw [← coe_nnNorm, Pi.nnNorm_def, hi, coe_nnNorm]
  rw [hf]
  exact Finset.single_le_sum (f := fun i ↦ ‖f i‖ ^ n) (fun _ _ ↦ by positivity)
    (Finset.mem_univ i)
