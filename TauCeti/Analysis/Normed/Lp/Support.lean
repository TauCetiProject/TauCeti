/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Countable support of `ℓᵖ` sequences

Every sequence in `ℓᵖ` at a finite exponent `p < ∞` vanishes outside a countable set of indices
(`Memℓp.countable_dsupport`, `lp.countable_dsupport`): for `p = 0` its support is finite by
definition, and for `0 < p < ∞` the `p`-th powers of the coordinate norms form a summable
nonnegative family, whose support is countable.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., §I.4.
-/

public section

open scoped ENNReal

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] {p : ℝ≥0∞}

/-- Every sequence in `ℓᵖ` for `p ≠ ∞` has countable support. -/
theorem Memℓp.countable_dsupport {f : ∀ i, E i} (hf : Memℓp f p) (hp : p ≠ ∞) :
    {i | f i ≠ 0}.Countable := by
  rcases eq_or_ne p 0 with rfl | hp₀
  · exact hf.finite_dsupport.countable
  · have hpr : 0 < p.toReal := ENNReal.toReal_pos hp₀ hp
    refine (hf.summable hpr).countable_support.mono fun i hi ↦ ?_
    exact (Real.rpow_pos_of_pos (norm_pos_iff.2 hi) p.toReal).ne'

/-- Every element of `lp E p` for `p ≠ ∞` has countable support. -/
theorem lp.countable_dsupport (f : lp E p) (hp : p ≠ ∞) :
    {i | f i ≠ 0}.Countable :=
  (lp.memℓp f).countable_dsupport hp
