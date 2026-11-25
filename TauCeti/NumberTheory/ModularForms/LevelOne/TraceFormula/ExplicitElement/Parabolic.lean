/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement.Basic
import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement.Translation

/-!
# The repeated-root trace fibres of Popa–Zagier's element

For an integer `a`, the sum of Popa–Zagier's integer weights on the matrices of
trace `2a` and determinant `a²` is `2` if `a > 0` and `0` if `a ≤ 0`.
These are all the discriminant-zero fibres; for `a ≠ 0` they contain both scalar and nonscalar
parabolic matrices. The result evaluates the boundary contribution in the ambient binary-form
trace; it does not assert that individual nonscalar matrices have weight zero.

The asymmetry in the sign of the trace comes from the choice of representatives in the
explicit element. For `a ≠ 0`, the two fibres of traces `±2a` together have weight `2`,
corresponding to coefficient `1/6` before the passage from the ambient trace to the cusp-form
trace.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §4, eq. (15).
-/

public section

open Matrix

namespace TauCeti.PopaZagier

/-- **The repeated-root trace fibres of Popa–Zagier's element.** At zero discriminant, the total
integer weight is `2` for positive trace and zero for nonpositive trace. The sum includes scalar
and nonscalar matrices, not just conjugacy representatives. -/
theorem finsum_weight_traceDetFiber_of_discrim_eq_zero {t n : ℤ} (hdisc : t ^ 2 - 4 * n = 0) :
    ∑ᶠ M : traceDetFiber (Fin 2) t n, weight M.val = if 0 < t then 2 else 0 := by
  rcases le_or_gt t 0 with ht | ht
  · rw [ite_eq_right (by omega)]
    exact finsum_weight_traceDetFiber_eq_zero_of_trace_nonpos ht (by linarith)
  rw [ite_eq_left ht]
  obtain ⟨t', n', hD', hn', ht', e⟩ :=
    exists_finsum_weight_traceDetFiber_eq ht (by nlinarith) (by linarith)
  obtain rfl : n' = 1 := by nlinarith
  obtain rfl : t' = 2 := by nlinarith
  simpa using e.trans (finsum_weight_traceDetFiber_of_det_lt_trace hn' ht')

end TauCeti.PopaZagier
