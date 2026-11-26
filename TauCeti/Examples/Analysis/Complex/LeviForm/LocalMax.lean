/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.QuadraticLeviForm

/-!
# Examples: the sign of `i∂∂bar u` at a maximum has no converse

At a local maximum of a real `C²` function `u` the Hermitian form `H_{i∂∂bar u} = 2 L_u` of
`i∂∂bar u` is nonpositive (`TauCeti.re_leviForm_nonpos_of_isLocalMax`). On `ℂⁿ` the function
`u = -|z|²` has its maximum at `0`, with `H_{i∂∂bar u} = -2h ≤ 0`. The saddle
`u = x₁² - y₁² = Re z₁²` is pluriharmonic, so `H_{i∂∂bar u}(0) = 0 ≤ 0` as well (the vanishing of
its Levi form, `TauCeti.leviForm_re_eq_zero`, is checked in
`TauCeti.Examples.Analysis.Complex.LeviForm.Laplacian`), but `0` is not a local maximum:
`u(t, 0, …, 0) = t²` for real `t`. So the sign condition at a maximum has no converse.
-/

public section

open Complex

namespace TauCeti.LeviFormLocalMaxExamples

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **`-|z|²` has a maximum at `0`, where `H_{i∂∂bar u} = -2h ≤ 0`.** Its Levi form is `-h`, by
`leviForm_neg` and `leviForm_norm_sq`. -/
example (v : E) :
    IsLocalMax (fun z : E ↦ -‖z‖ ^ 2) 0 ∧
      (2 * leviForm (fun z : E ↦ -‖z‖ ^ 2) 0 v v).re = -2 * ‖v‖ ^ 2 ∧
      (2 * leviForm (fun z : E ↦ -‖z‖ ^ 2) 0 v v).re ≤ 0 := by
  have hre : (2 * leviForm (fun z : E ↦ -‖z‖ ^ 2) 0 v v).re = -2 * ‖v‖ ^ 2 := by
    rw [← Pi.neg_def, leviForm_neg, leviForm_norm_sq]
    simp [← Complex.ofReal_pow]
  refine ⟨Filter.Eventually.of_forall fun z ↦ ?_, hre, ?_⟩
  · simp
  · rw [hre]
    nlinarith [sq_nonneg ‖v‖]

variable {n : ℕ}

/-- **The saddle `x₁² - y₁² = Re z₁²` is not a local maximum**, although its Levi form vanishes:
`Re z₁²` takes the value `t²` at `(t, 0, …, 0)`. -/
example : ¬ IsLocalMax (fun z : EuclideanSpace ℂ (Fin (n + 1)) ↦ (z 0 ^ 2).re) 0 := by
  intro hmax
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1 hmax
  have hz : dist (EuclideanSpace.single 0 ((ε / 2 : ℝ) : ℂ) : EuclideanSpace ℂ (Fin (n + 1)))
      0 < ε := by
    rw [dist_zero_right]
    simp [abs_of_pos hε]
    linarith
  have h' := h hz
  have hsq : ((ε / 2 : ℝ) : ℂ) ^ 2 = ((ε / 2) ^ 2 : ℝ) := by push_cast; ring
  simp only [PiLp.single_apply, ite_true, PiLp.zero_apply, hsq, Complex.ofReal_re] at h'
  norm_num at h'
  nlinarith [h']

end TauCeti.LeviFormLocalMaxExamples
