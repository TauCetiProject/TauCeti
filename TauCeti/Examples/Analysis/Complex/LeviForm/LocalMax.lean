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
`u = x₁² - y₁² = Re z₁²` is pluriharmonic, so `H_{i∂∂bar u}(0) = 0 ≤ 0` as well, but `0` is not a
local maximum: `u(t, 0, …, 0) = t²` for real `t`. So the sign condition at a maximum has no
converse.
-/

public section

open Complex

namespace TauCeti.LeviFormLocalMaxExamples

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The Levi form of `-|z|²` is `-h`, so `H_{i∂∂bar (-|z|²)} = -2h`. -/
example (x : E) : leviForm (fun z : E ↦ -‖z‖ ^ 2) x = -innerₛₗ ℂ := by
  rw [show (fun z : E ↦ -‖z‖ ^ 2) = -fun z ↦ ‖z‖ ^ 2 from rfl, leviForm_neg, leviForm_norm_sq]

/-- **`-|z|²` has a maximum at `0`, where `H_{i∂∂bar u} = -2h ≤ 0`.** -/
example (v : E) :
    IsLocalMax (fun z : E ↦ -‖z‖ ^ 2) 0 ∧
      (2 * leviForm (fun z : E ↦ -‖z‖ ^ 2) 0 v v).re = -2 * ‖v‖ ^ 2 ∧
      (2 * leviForm (fun z : E ↦ -‖z‖ ^ 2) 0 v v).re ≤ 0 := by
  have hL : leviForm (fun z : E ↦ -‖z‖ ^ 2) 0 = -innerₛₗ ℂ := by
    rw [show (fun z : E ↦ -‖z‖ ^ 2) = -fun z ↦ ‖z‖ ^ 2 from rfl, leviForm_neg, leviForm_norm_sq]
  have hre : (2 * leviForm (fun z : E ↦ -‖z‖ ^ 2) 0 v v).re = -2 * ‖v‖ ^ 2 := by
    rw [hL]
    simp [← Complex.ofReal_pow]
  refine ⟨Filter.Eventually.of_forall fun z ↦ ?_, hre, ?_⟩
  · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero,
      Left.neg_nonpos_iff]
    positivity
  · rw [hre]
    nlinarith [sq_nonneg ‖v‖]

variable {n : ℕ}

/-- **The saddle `x₁² - y₁² = Re z₁²` has `H_{i∂∂bar u} = 0 ≤ 0` at `0`.** It is pluriharmonic, so
its Levi form vanishes. -/
example : leviForm (fun z : EuclideanSpace ℂ (Fin (n + 1)) ↦ (z 0 ^ 2).re) 0 = 0 :=
  leviForm_re_eq_zero
    (((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin (n + 1))).contDiff.pow 2).contDiffAt)

/-- **The saddle is not a local maximum**: `Re z₁²` takes the value `t²` at `(t, 0, …, 0)`. -/
example : ¬ IsLocalMax (fun z : EuclideanSpace ℂ (Fin (n + 1)) ↦ (z 0 ^ 2).re) 0 := by
  intro hmax
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1 hmax
  have hz : dist (EuclideanSpace.single 0 ((ε / 2 : ℝ) : ℂ) : EuclideanSpace ℂ (Fin (n + 1)))
      0 < ε := by
    rw [dist_zero_right, EuclideanSpace.norm_eq]
    simp only [PiLp.single_apply, apply_ite (fun c : ℂ ↦ ‖c‖ ^ 2), norm_zero,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [Finset.sum_eq_single 0 (fun b _ hb ↦ by simp [hb]) (by simp)]
    simp only [↓reduceIte]
    rw [Real.sqrt_sq (by positivity)]
    linarith
  have h' := h hz
  have hsq : ((ε / 2 : ℝ) : ℂ) ^ 2 = ((ε / 2) ^ 2 : ℝ) := by push_cast; ring
  simp only [PiLp.single_apply, ite_true, PiLp.zero_apply, hsq, Complex.ofReal_re] at h'
  norm_num at h'
  nlinarith [h']

end TauCeti.LeviFormLocalMaxExamples
