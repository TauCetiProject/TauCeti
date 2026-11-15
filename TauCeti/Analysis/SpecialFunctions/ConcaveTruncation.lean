/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# A smooth concave truncation

For `a < b`, the function `TauCeti.concaveTruncation a b : ℝ → ℝ` is smooth, nondecreasing and
concave, equal to the identity on `(-∞, a]` and constant on `[b, ∞)`: a smooth concave substitute
for a truncation `s ↦ min s c`. It is the primitive, equal to `a` at `a`, of
`s ↦ 1 - ψ ((s - a) / (b - a))`, where `ψ` is `Real.smoothTransition`; its derivative therefore
decreases from `1` on `(-∞, a]` to `0` on `[b, ∞)`.

Composing a positive harmonic function `h` with such a truncation gives a superharmonic function
that agrees with `h` where `h ≤ a` and is constant where `h ≥ b`. This is how Lohkamp makes a
conformally flat metric `h ^ (4 / (n - 2)) δ` exactly Euclidean outside a compact set while keeping
its scalar curvature nonnegative, which reduces the positive mass theorem to the nonexistence of
metrics of positive scalar curvature on a torus. The harmonic side of that argument is in
`TauCeti/Analysis/InnerProductSpace/Harmonic/ConcaveTruncation.lean`.

## Main declarations

* `TauCeti.concaveTruncation`: the truncation.
* `TauCeti.contDiff_concaveTruncation`, `TauCeti.monotone_concaveTruncation`,
  `TauCeti.concaveOn_concaveTruncation`: it is smooth, nondecreasing and concave.
* `TauCeti.concaveTruncation_of_le_left`, `TauCeti.concaveTruncation_of_right_le`: it is the
  identity on `(-∞, a]` and constant on `[b, ∞)`.
* `TauCeti.deriv_concaveTruncation_of_le_left`, `TauCeti.deriv_concaveTruncation_of_right_le`: its
  derivative is `1` on `(-∞, a]` and `0` on `[b, ∞)`.
* `TauCeti.deriv_deriv_concaveTruncation_nonpos`: its second derivative is nonpositive.
* `TauCeti.concaveTruncation_le_self`, `TauCeti.min_le_concaveTruncation`,
  `TauCeti.concaveTruncation_pos`: it lies between `min s a` and `s`, so it is positive on `(0, ∞)`
  when `a > 0`.

## References

* J. Lohkamp, *Scalar curvature and hammocks*, Math. Ann. 313 (1999), 385–407,
  Proposition 6.1.
* R. Schoen and S.-T. Yau, *Positive scalar curvature and minimal hypersurface singularities*,
  arXiv:1704.05490, Proposition 5.4.
-/

public section

noncomputable section

open Real Set
open scoped ContDiff

namespace TauCeti

/-- The **smooth concave truncation** between the levels `a` and `b`: the primitive, equal to `a`
at `a`, of `s ↦ 1 - ψ ((s - a) / (b - a))`, where `ψ` is the smooth transition function. For
`a < b` it is smooth, nondecreasing and concave, the identity on `(-∞, a]` and constant on
`[b, ∞)`. -/
def concaveTruncation (a b s : ℝ) : ℝ :=
  a + ∫ t in a..s, (1 - smoothTransition ((t - a) / (b - a)))

variable {a b s : ℝ}

/-- Unfolding lemma for `TauCeti.concaveTruncation`. -/
theorem concaveTruncation_def (a b s : ℝ) :
    concaveTruncation a b s = a + ∫ t in a..s, (1 - smoothTransition ((t - a) / (b - a))) :=
  (rfl)

private theorem continuous_one_sub_smoothTransition (a b : ℝ) :
    Continuous fun t ↦ 1 - smoothTransition ((t - a) / (b - a)) := by
  fun_prop

/-- The derivative of the concave truncation is `1 - ψ ((s - a) / (b - a))`. -/
theorem hasDerivAt_concaveTruncation (a b s : ℝ) :
    HasDerivAt (concaveTruncation a b) (1 - smoothTransition ((s - a) / (b - a))) s :=
  (((continuous_one_sub_smoothTransition a b).integral_hasStrictDerivAt a s).hasDerivAt).const_add
    a

/-- The derivative of the concave truncation is `1 - ψ ((s - a) / (b - a))`. -/
@[simp]
theorem deriv_concaveTruncation (a b s : ℝ) :
    deriv (concaveTruncation a b) s = 1 - smoothTransition ((s - a) / (b - a)) :=
  (hasDerivAt_concaveTruncation a b s).deriv

/-- The concave truncation is differentiable. -/
theorem differentiable_concaveTruncation (a b : ℝ) : Differentiable ℝ (concaveTruncation a b) :=
  fun s ↦ (hasDerivAt_concaveTruncation a b s).differentiableAt

/-- The concave truncation is smooth. -/
theorem contDiff_concaveTruncation (a b : ℝ) : ContDiff ℝ ∞ (concaveTruncation a b) := by
  refine contDiff_infty_iff_deriv.2 ⟨differentiable_concaveTruncation a b, ?_⟩
  rw [funext (deriv_concaveTruncation a b)]
  exact contDiff_const.sub (smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const _))

/-- The concave truncation is nondecreasing. -/
theorem monotone_concaveTruncation (a b : ℝ) : Monotone (concaveTruncation a b) :=
  monotone_of_deriv_nonneg (differentiable_concaveTruncation a b) fun s ↦ by
    rw [deriv_concaveTruncation]
    exact sub_nonneg.2 (smoothTransition.le_one _)

/-- Below `a`, the argument `(t - a) / (b - a)` of the smooth transition is nonpositive. -/
private theorem div_nonpos_of_le (hab : a ≤ b) {t : ℝ} (ht : t ≤ a) : (t - a) / (b - a) ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 ht) (sub_nonneg.2 hab)

/-- Above `b`, the argument `(t - a) / (b - a)` of the smooth transition is at least `1`. -/
private theorem one_le_div_of_le (hab : a < b) {t : ℝ} (ht : b ≤ t) : 1 ≤ (t - a) / (b - a) :=
  (one_le_div (sub_pos.2 hab)).2 (by linarith)

/-- The derivative of the concave truncation is `1` on `(-∞, a]`. -/
theorem deriv_concaveTruncation_of_le_left (hab : a ≤ b) (hs : s ≤ a) :
    deriv (concaveTruncation a b) s = 1 := by
  rw [deriv_concaveTruncation, smoothTransition.zero_of_nonpos (div_nonpos_of_le hab hs), sub_zero]

/-- The derivative of the concave truncation is `0` on `[b, ∞)`. -/
theorem deriv_concaveTruncation_of_right_le (hab : a < b) (hs : b ≤ s) :
    deriv (concaveTruncation a b) s = 0 := by
  rw [deriv_concaveTruncation, smoothTransition.one_of_one_le (one_le_div_of_le hab hs), sub_self]

/-- For `a ≤ b`, the derivative of the concave truncation is nonincreasing. -/
theorem antitone_deriv_concaveTruncation (hab : a ≤ b) :
    Antitone (deriv (concaveTruncation a b)) := by
  intro s t hst
  simp only [deriv_concaveTruncation]
  exact sub_le_sub_left (smoothTransition.monotone
    (div_le_div_of_nonneg_right (sub_le_sub_right hst a) (sub_nonneg.2 hab))) 1

/-- For `a ≤ b`, the second derivative of the concave truncation is nonpositive. -/
theorem deriv_deriv_concaveTruncation_nonpos (hab : a ≤ b) (s : ℝ) :
    deriv (deriv (concaveTruncation a b)) s ≤ 0 :=
  (antitone_deriv_concaveTruncation hab).deriv_nonpos

/-- For `a ≤ b`, the concave truncation is concave. -/
theorem concaveOn_concaveTruncation (hab : a ≤ b) : ConcaveOn ℝ univ (concaveTruncation a b) :=
  (antitone_deriv_concaveTruncation hab).antitoneOn _ |>.concaveOn_of_deriv convex_univ
    (differentiable_concaveTruncation a b).continuous.continuousOn
    (differentiable_concaveTruncation a b).differentiableOn

/-- The concave truncation takes the value `a` at `a`. -/
@[simp]
theorem concaveTruncation_left (a b : ℝ) : concaveTruncation a b a = a := by
  simp [concaveTruncation_def]

/-- For `a ≤ b`, the concave truncation is the identity on `(-∞, a]`. -/
theorem concaveTruncation_of_le_left (hab : a ≤ b) (hs : s ≤ a) : concaveTruncation a b s = s := by
  rw [concaveTruncation_def, intervalIntegral.integral_congr (g := fun _ ↦ (1 : ℝ)),
    intervalIntegral.integral_const, smul_eq_mul, mul_one, add_sub_cancel]
  intro t ht
  rw [uIcc_of_ge hs] at ht
  dsimp only
  rw [smoothTransition.zero_of_nonpos (div_nonpos_of_le hab ht.2), sub_zero]

/-- For `a < b`, the concave truncation is constant on `[b, ∞)`. -/
theorem concaveTruncation_of_right_le (hab : a < b) (hs : b ≤ s) :
    concaveTruncation a b s = concaveTruncation a b b := by
  have hi (u v : ℝ) := (continuous_one_sub_smoothTransition a b).intervalIntegrable
    (μ := MeasureTheory.volume) u v
  rw [concaveTruncation_def, concaveTruncation_def,
    ← intervalIntegral.integral_add_adjacent_intervals (hi a b) (hi b s),
    intervalIntegral.integral_congr (a := b) (b := s) (g := fun _ ↦ (0 : ℝ)),
    intervalIntegral.integral_zero, add_zero]
  intro t ht
  rw [uIcc_of_le hs] at ht
  dsimp only
  rw [smoothTransition.one_of_one_le (one_le_div_of_le hab ht.1), sub_self]

/-- The difference `s - concaveTruncation a b s` is nondecreasing: the derivative of the
truncation is at most `1`. -/
private theorem monotone_sub_concaveTruncation (a b : ℝ) :
    Monotone fun t ↦ t - concaveTruncation a b t :=
  monotone_of_deriv_nonneg (fun t ↦ ((hasDerivAt_id' t).fun_sub
    (hasDerivAt_concaveTruncation a b t)).differentiableAt) fun t ↦ by
      rw [((hasDerivAt_id' t).fun_sub (hasDerivAt_concaveTruncation a b t)).deriv]
      linarith [smoothTransition.nonneg ((t - a) / (b - a))]

/-- For `a ≤ b`, the concave truncation lies below the identity. -/
theorem concaveTruncation_le_self (hab : a ≤ b) (s : ℝ) : concaveTruncation a b s ≤ s := by
  rcases le_total s a with hs | hs
  · exact (concaveTruncation_of_le_left hab hs).le
  · have := monotone_sub_concaveTruncation a b hs
    simp only [concaveTruncation_left, sub_self] at this
    linarith

/-- The concave truncation is at least `min s a`. -/
theorem min_le_concaveTruncation (a b s : ℝ) : min s a ≤ concaveTruncation a b s := by
  rcases le_total s a with hs | hs
  · have := monotone_sub_concaveTruncation a b hs
    simp only [concaveTruncation_left, sub_self] at this
    rw [min_eq_left hs]
    linarith
  · rw [min_eq_right hs]
    exact (concaveTruncation_left a b).symm.le.trans (monotone_concaveTruncation a b hs)

/-- For `0 < a`, the concave truncation is positive on `(0, ∞)`. -/
theorem concaveTruncation_pos (ha : 0 < a) (hs : 0 < s) : 0 < concaveTruncation a b s :=
  (lt_min hs ha).trans_le (min_le_concaveTruncation a b s)

end TauCeti
