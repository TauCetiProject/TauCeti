/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Topology.Algebra.Module.Equiv.Pi

/-!
# The norm on a finite product

The norm on a nonempty finite product of seminormed groups is the maximum of the coordinate norms,
so it is attained at some coordinate (`Pi.exists_norm_apply_eq_norm`). Hence for every positive
exponent `n` its `n`-th power is at most the sum of the `n`-th powers of the coordinate norms
(`Pi.norm_pow_le_sum_norm_pow`). On `Fin 2 → E` it is the norm of the product `E × E`
(`ContinuousLinearEquiv.norm_finTwoArrow`).
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

/-- `ContinuousLinearEquiv.finTwoArrow` preserves the sup norm: the norms on `Fin 2 → E` and
`E × E` are both the maximum of the two coordinate norms. -/
theorem ContinuousLinearEquiv.norm_finTwoArrow (R : Type*) {E : Type*} [Semiring R]
    [SeminormedAddCommGroup E] [Module R E] (v : Fin 2 → E) :
    ‖ContinuousLinearEquiv.finTwoArrow R E v‖ = ‖v‖ := by
  rw [ContinuousLinearEquiv.finTwoArrow_apply, Prod.norm_def]
  refine le_antisymm (max_le (norm_le_pi_norm v 0) (norm_le_pi_norm v 1))
    ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_)
  fin_cases i
  exacts [le_max_left _ _, le_max_right _ _]
