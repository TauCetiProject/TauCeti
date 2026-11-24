/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Darboux

/-!
# Change of variables on an interval with a nonvanishing derivative

Mathlib's one-dimensional change of variables formula
`MeasureTheory.integral_image_eq_integral_abs_deriv_smul` asks for `f` to be injective on the set
of integration. On a convex subset `s` of `ℝ`, a derivative that never vanishes already forces
this: by Darboux's theorem the derivative has a constant sign on `s`, so `f` is strictly monotone
there. Hence the integral of `g` over `f '' s` is the integral of `|f'| • g ∘ f` over `s`
(`MeasureTheory.integral_image_eq_integral_abs_deriv_smul_of_ne_zero`). No continuity of the
derivative is needed.

If moreover `f` runs on `[t₁, t₂]` from one of `a`, `b` to the other while staying strictly
between them, then `f` maps `(t₁, t₂)` onto `(a, b)`, and the integral of `g` from `a` to `b` is
the integral of `|f'| • g ∘ f` over `(t₁, t₂)`
(`intervalIntegral.integral_eq_integral_Ioo_abs_deriv_smul_of_ne_zero`). This is the step
`dt = dx / |x'|` of the time quadratures of one-dimensional motions.
-/

public section

open Set

namespace MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set ℝ} {f f' : ℝ → ℝ}

/-- **Change of variables for a nonvanishing derivative.** If `f` has a nonvanishing derivative
`f'` within a convex set `s ⊆ ℝ` at each point of `s`, then the integral of `g` over `f '' s` is
the integral of `|f'| • g ∘ f` over `s`. -/
theorem integral_image_eq_integral_abs_deriv_smul_of_ne_zero (hs : Convex ℝ s)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf'0 : ∀ x ∈ s, f' x ≠ 0) (g : ℝ → F) :
    ∫ x in f '' s, g x = ∫ x in s, |f' x| • g (f x) := by
  have hc : ContinuousOn f s := fun x hx ↦ (hf' x hx).continuousWithinAt
  have hi (x : ℝ) (hx : x ∈ interior s) : HasDerivWithinAt f (f' x) (interior s) x :=
    (hf' x (interior_subset hx)).mono interior_subset
  have hinj : InjOn f s := by
    rcases hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne hs hf' hf'0 with hneg | hpos
    · exact (strictAntiOn_of_hasDerivWithinAt_neg hs hc hi
        fun x hx ↦ hneg x (interior_subset hx)).injOn
    · exact (strictMonoOn_of_hasDerivWithinAt_pos hs hc hi
        fun x hx ↦ hpos x (interior_subset hx)).injOn
  exact integral_image_eq_integral_abs_deriv_smul hs.ordConnected.measurableSet hf' hinj g

end MeasureTheory

namespace intervalIntegral

open MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f f' : ℝ → ℝ} {a b t₁ t₂ : ℝ}

/-- **Change of variables along a monotone passage.** Let `f` be continuous on `[t₁, t₂]` with a
nonvanishing derivative `f'` on `(t₁, t₂)`, run from one of `a`, `b` to the other on `[t₁, t₂]` and
stay strictly between them on `(t₁, t₂)`. Then the integral of `g` from `a` to `b` is the integral
of `|f'| • g ∘ f` over `(t₁, t₂)`. -/
theorem integral_eq_integral_Ioo_abs_deriv_smul_of_ne_zero (ht : t₁ ≤ t₂)
    (hf : ContinuousOn f (Icc t₁ t₂))
    (hf' : ∀ t ∈ Ioo t₁ t₂, HasDerivWithinAt f (f' t) (Ioo t₁ t₂) t)
    (hf'0 : ∀ t ∈ Ioo t₁ t₂, f' t ≠ 0) (hends : f t₁ = a ∧ f t₂ = b ∨ f t₁ = b ∧ f t₂ = a)
    (hmaps : MapsTo f (Ioo t₁ t₂) (Ioo a b)) (g : ℝ → F) :
    ∫ x in a..b, g x = ∫ t in Ioo t₁ t₂, |f' t| • g (f t) := by
  have himage : f '' Ioo t₁ t₂ = Ioo a b := by
    refine hmaps.image_subset.antisymm ?_
    rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · simpa only [h₁, h₂] using intermediate_value_Ioo ht hf
    · simpa only [h₁, h₂] using intermediate_value_Ioo' ht hf
  have hab : a ≤ b := by
    rcases ht.eq_or_lt with rfl | ht'
    · rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [← h₁, ← h₂]
    · obtain ⟨h₁, h₂⟩ := hmaps ⟨left_lt_add_div_two.2 ht', add_div_two_lt_right.2 ht'⟩
      exact (h₁.trans h₂).le
  rw [integral_of_le hab, integral_Ioc_eq_integral_Ioo, ← himage,
    integral_image_eq_integral_abs_deriv_smul_of_ne_zero (convex_Ioo t₁ t₂) hf' hf'0 g]

end intervalIntegral
