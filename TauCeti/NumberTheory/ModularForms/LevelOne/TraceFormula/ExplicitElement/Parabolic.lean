/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement.ClassNumber

/-!
# The repeated-root trace fibres of Popa–Zagier's element

For a nonzero integer `a`, the sum of Popa–Zagier's integer weights on the matrices of
trace `2a` and determinant `a²` is `2` if `a > 0` and `0` if `a < 0`.
These are the discriminant-zero fibres, containing both scalar and nonscalar parabolic
matrices. The result evaluates the boundary contribution in the ambient binary-form trace;
it does not assert that individual nonscalar matrices have weight zero.

The asymmetry in the sign of the trace comes from the choice of representatives in the
explicit element. Together, the two fibres have weight `2`, corresponding to coefficient
`1/6` before the passage from the ambient trace to the cusp-form trace.

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
    ∑ᶠ M : traceDetFiber (Fin 2) 2 1, weight M.1 = 2 := by
  let I : traceDetFiber (Fin 2) (2 : ℤ) 1 := ⟨1, mem_traceDetFiber_fin_two.mpr (by norm_num)⟩
  rw [finsum_eq_single _ I (fun M hM ↦ ?_)]
  · norm_num [I, weight, weight₁, weight₂, weight₃, weight₄, chainWeight₃]
  · by_contra hw
    obtain ⟨ht, hd⟩ := mem_traceDetFiber.mp M.2
    exact hM (Subtype.ext (eq_one_of_det_one_trace_sq_four_weight_ne_zero M.1 hd
      (by rw [ht]; norm_num) hw))

private theorem finsum_weight_trace_neg_two_det_one :
    ∑ᶠ M : traceDetFiber (Fin 2) (-2) 1, weight M.1 = 0 := by
  refine finsum_eq_zero_of_forall_eq_zero fun M ↦ ?_
  by_contra hw
  obtain ⟨ht, hd⟩ := mem_traceDetFiber.mp M.2
  have hM := eq_one_of_det_one_trace_sq_four_weight_ne_zero M.1 hd
    (by rw [ht]; norm_num) hw
  simp [hM] at ht

private theorem finsum_weight_traceDetFiber_two_mul_sq_step {a : ℤ} (ha : a ≠ 0) :
    ∑ᶠ M : traceDetFiber (Fin 2) (2 * (a + 1)) ((a + 1) ^ 2), weight M.1 =
      ∑ᶠ M : traceDetFiber (Fin 2) (2 * a) (a ^ 2), weight M.1 := by
  have ht : 2 * a + 2 = 2 * (a + 1) := by ring
  have hn : a ^ 2 + 2 * a + 1 = (a + 1) ^ 2 := by ring
  have h := finsum_weight_traceDetFiber_add_two (t := 2 * a) (sq_pos_of_ne_zero ha)
  rw [ht, hn] at h
  exact h

/-- The discriminant-zero fibre with positive trace has total integer weight `2`. -/
private theorem finsum_weight_traceDetFiber_two_mul_sq_of_pos {a : ℤ} (ha : 0 < a) :
    ∑ᶠ M : traceDetFiber (Fin 2) (2 * a) (a ^ 2), weight M.1 = 2 := by
  have ha' : 1 ≤ a := by omega
  clear ha
  induction a, ha' using Int.leInduction with
  | base => simpa using finsum_weight_trace_two_det_one
  | succ a ha ih =>
    exact (finsum_weight_traceDetFiber_two_mul_sq_step (by omega)).trans ih

/-- The discriminant-zero fibre with negative trace has total integer weight zero. -/
private theorem finsum_weight_traceDetFiber_two_mul_sq_of_neg {a : ℤ} (ha : a < 0) :
    ∑ᶠ M : traceDetFiber (Fin 2) (2 * a) (a ^ 2), weight M.1 = 0 := by
  have ha' : a ≤ -1 := by omega
  clear ha
  induction a, ha' using Int.leInductionDown with
  | base => simpa using finsum_weight_trace_neg_two_det_one
  | pred a ha ih =>
    have h := finsum_weight_traceDetFiber_two_mul_sq_step (a := a - 1) (by omega)
    rw [sub_add_cancel] at h
    exact h.symm.trans ih

/-- **The repeated-root trace fibres of Popa–Zagier's element.** At positive determinant and
zero discriminant, the total integer weight is `2` for positive trace and zero for negative
trace. The sum includes scalar and nonscalar matrices, not just conjugacy representatives. -/
theorem finsum_weight_traceDetFiber_of_discrim_eq_zero {t n : ℤ} (hn : 0 < n)
    (hdisc : t ^ 2 - 4 * n = 0) :
    ∑ᶠ M : traceDetFiber (Fin 2) t n, weight M.1 = if 0 < t then 2 else 0 := by
  have he : Even (t ^ 2) := ⟨2 * n, by linarith⟩
  obtain ⟨a, ha⟩ := (Int.even_pow.mp he).1
  have ht : t = 2 * a := by omega
  clear ha
  subst t
  have hn' : n = a ^ 2 := by nlinarith
  subst n
  by_cases ha' : 0 < a
  · rw [ite_eq_left (by omega)]
    exact finsum_weight_traceDetFiber_two_mul_sq_of_pos ha'
  · have hneg : a < 0 := by
      have : a ≠ 0 := by rintro rfl; simp at hn
      omega
    rw [ite_eq_right (by omega)]
    exact finsum_weight_traceDetFiber_two_mul_sq_of_neg hneg

end TauCeti.PopaZagier
