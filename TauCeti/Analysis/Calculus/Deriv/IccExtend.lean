/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Order.Interval.Set.ProjIcc
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# `C²` extension from a closed interval

Let `v : ℝ → E` be `C¹`, with values in a real Banach space, and suppose that on `(a, b)` its
derivative has a derivative `h` that extends continuously to `[a, b]`. Then `v` is `C²` on the
closed interval in the strongest sense: it agrees on `[a, b]`, together with its derivative, with a
`C²` function `w` on `ℝ` whose second derivative is the constant extension `h ∘ projIcc a b` of
`h`. So any modulus of continuity of `h` on `[a, b]`, such as a Hölder bound, is a global modulus
of continuity of `w''`, since `projIcc a b` is `1`-Lipschitz.

The function `w` is obtained by integrating `h ∘ projIcc a b` twice, starting from `v a` and
`v' a`; the fundamental theorem of calculus on `[a, b]` identifies the integrals with `v` and `v'`
there.

## Main declarations

* `TauCeti.exists_contDiff_two_eqOn_and_deriv_deriv_eq`: the extension `w`.
-/

public section

open Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **`C²` extension from a closed interval.** Let `v : ℝ → E` be `C¹`, and let `h` be continuous
on `[a, b]` with `h t` the derivative of `v'` at every `t ∈ (a, b)`. Then there is a `C²` function
`w` on `ℝ` with `w = v` and `w' = v'` on `[a, b]`, whose second derivative is
`w'' t = h (projIcc a b t)` everywhere. -/
theorem exists_contDiff_two_eqOn_and_deriv_deriv_eq {a b : ℝ} (hab : a ≤ b) {v h : ℝ → E}
    (hv : ContDiff ℝ 1 v) (hd : ∀ t ∈ Ioo a b, HasDerivAt (deriv v) (h t) t)
    (hh : ContinuousOn h (Icc a b)) :
    ∃ w : ℝ → E, ContDiff ℝ 2 w ∧ EqOn v w (Icc a b) ∧ EqOn (deriv v) (deriv w) (Icc a b) ∧
      deriv (deriv w) = fun t => h (projIcc a b hab t) := by
  set hₑ : ℝ → E := fun t => h (projIcc a b hab t)
  have hhₑ : Continuous hₑ :=
    hh.comp_continuous continuous_projIcc.subtype_val fun t => (projIcc a b hab t).2
  -- `w₂ = v' a + ∫ hₑ` is `v'` on `[a, b]`.
  set w₂ : ℝ → E := fun t => deriv v a + ∫ s in a..t, hₑ s with hw₂_def
  have hw₂ : ∀ t, HasDerivAt w₂ (hₑ t) t := fun t =>
    (hhₑ.integral_hasStrictDerivAt a t).hasDerivAt.const_add _
  have hw₂v : ∀ t ∈ Icc a b, w₂ t = deriv v t := fun t ht => by
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f' := hₑ) ht.1
      (hv.continuous_deriv le_rfl).continuousOn (fun s hs =>
        (hd s ⟨hs.1, hs.2.trans_le ht.2⟩).congr_deriv
          (by simp [hₑ, projIcc_of_mem hab ⟨hs.1.le, hs.2.le.trans ht.2⟩]))
      (hhₑ.intervalIntegrable _ _)
    rw [hw₂_def]
    beta_reduce
    rw [hint, add_sub_cancel]
  -- `w = v a + ∫ w₂` is `v` on `[a, b]`.
  have hw₂c : Continuous w₂ := continuous_iff_continuousAt.2 fun t => (hw₂ t).continuousAt
  set w : ℝ → E := fun t => v a + ∫ s in a..t, w₂ s with hw_def
  have hw : ∀ t, HasDerivAt w (w₂ t) t := fun t =>
    (hw₂c.integral_hasStrictDerivAt a t).hasDerivAt.const_add _
  have hdw : deriv w = w₂ := funext fun t => (hw t).deriv
  have hdw₂ : deriv w₂ = hₑ := funext fun t => (hw₂ t).deriv
  refine ⟨w, (contDiff_succ_iff_deriv (n := 1)).2 ⟨fun t => (hw t).differentiableAt, by simp,
    hdw ▸ contDiff_one_iff_deriv.2 ⟨fun t => (hw₂ t).differentiableAt, hdw₂ ▸ hhₑ⟩⟩,
    fun t ht => ?_, fun t ht => by rw [hdw, hw₂v t ht], by rw [hdw, hdw₂]⟩
  have h₁ : ∫ s in a..t, w₂ s = ∫ s in a..t, deriv v s :=
    intervalIntegral.integral_congr fun s hs => by
      rw [uIcc_of_le ht.1] at hs
      exact hw₂v s ⟨hs.1, hs.2.trans ht.2⟩
  have h₂ : ∫ s in a..t, deriv v s = v t - v a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => (hv.differentiable one_ne_zero s).hasDerivAt)
      ((hv.continuous_deriv le_rfl).intervalIntegrable _ _)
  rw [hw_def]
  beta_reduce
  rw [h₁, h₂, add_sub_cancel]

end TauCeti
