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

private theorem eq_one_of_det_one_trace_sq_four_weight_ne_zero
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hd : M.det = 1) (ht : M.trace ^ 2 = 4)
    (hw : weight M ≠ 0) : M = 1 := by
  -- The support bound reduces both signs of the trace to the same finite calculation.
  have ha := abs_le_of_weight_ne_zero hw 0 0
  have hb := abs_le_of_weight_ne_zero hw 0 1
  have hc := abs_le_of_weight_ne_zero hw 1 0
  have he := abs_le_of_weight_ne_zero hw 1 1
  rw [hd] at ha hb hc he
  simp only [det_fin_two] at hd
  simp only [trace_fin_two] at ht
  simp only [weight] at hw
  generalize ea : M 0 0 = a at *
  generalize eb : M 0 1 = b at *
  generalize ec : M 1 0 = c at *
  generalize ed : M 1 1 = d at *
  rcases abs_le.mp ha with ⟨ha₁, ha₂⟩
  rcases abs_le.mp hb with ⟨hb₁, hb₂⟩
  rcases abs_le.mp hc with ⟨hc₁, hc₂⟩
  generalize es : a + d = s at ht
  have hs : s = 2 ∨ s = -2 := sq_eq_sq_iff_eq_or_eq_neg.mp (by nlinarith [ht])
  have ed' : d = s - a := by omega
  rw [ed'] at hd hw he ed
  -- Trace determines the last entry; reject impossible determinants before evaluating weights.
  rcases hs with rfl | rfl <;>
    interval_cases a <;> norm_num at he <;>
    interval_cases b <;> norm_num at hd <;> interval_cases c <;> norm_num at hd <;>
    norm_num [weight₁, weight₂, weight₃, weight₄, chainWeight₃, chainWeight₄] at hw
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ea, eb, ec, ed]

private theorem finsum_weight_trace_two_det_one :
    ∑ᶠ M : traceDetFiber (Fin 2) 2 1, weight M.val = 2 := by
  let I : traceDetFiber (Fin 2) (2 : ℤ) 1 := ⟨1, mem_traceDetFiber_fin_two.mpr (by norm_num)⟩
  rw [finsum_eq_single _ I (fun M hM ↦ ?_)]
  · norm_num [I, weight, weight₁, weight₂, weight₃, weight₄, chainWeight₃]
  · by_contra hw
    obtain ⟨ht, hd⟩ := mem_traceDetFiber.mp M.property
    exact hM (Subtype.ext (eq_one_of_det_one_trace_sq_four_weight_ne_zero M.val hd
      (by rw [ht]; norm_num) hw))

/-- **The repeated-root trace fibres of Popa–Zagier's element.** At zero discriminant, the total
integer weight is `2` for positive trace and zero for nonpositive trace. The sum includes scalar
and nonscalar matrices, not just conjugacy representatives. -/
theorem finsum_weight_traceDetFiber_of_discrim_eq_zero {t n : ℤ} (hdisc : t ^ 2 - 4 * n = 0) :
    ∑ᶠ M : traceDetFiber (Fin 2) t n, weight M.val = if 0 < t then 2 else 0 := by
  rcases le_or_gt t 0 with ht | ht
  · rw [ite_eq_right (by omega)]
    exact finsum_weight_traceDetFiber_eq_zero_of_trace_nonpos ht (by linarith)
  rw [ite_eq_left ht]
  obtain ⟨t', n', hD', hn', h', e⟩ :=
    exists_finsum_weight_traceDetFiber_eq ht (by nlinarith) (by linarith)
  obtain rfl : n' = 1 := by nlinarith
  obtain rfl : t' = 2 := by nlinarith
  exact e.trans finsum_weight_trace_two_det_one

end TauCeti.PopaZagier
