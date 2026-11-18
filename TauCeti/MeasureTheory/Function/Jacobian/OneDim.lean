/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Darboux
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.IntermediateValue

/-!
# Change of variables on an interval with a nonvanishing derivative

Mathlib's one-dimensional change of variables formula
`MeasureTheory.integral_image_eq_integral_abs_deriv_smul` asks for `f` to be injective on the set
of integration. On a convex subset `s` of `ℝ`, a derivative that never vanishes already forces
this: by Darboux's theorem the derivative has a constant sign on `s`, so `f` is strictly monotone
there. Hence the integral of `g` over `f '' s` is the integral of `|f'| • g ∘ f` over `s`
(`MeasureTheory.integral_image_eq_integral_abs_deriv_smul_of_ne_zero`). No continuity of the
derivative is needed.

Along a *leg* of a motion `f` on `[t₁, t₂]`, running from one of `a₁`, `a₂` to the other and
staying strictly between them meanwhile, the image of `(t₁, t₂)` is `(a₁, a₂)` by the intermediate
value theorem. This gives the interval-integral form
`MeasureTheory.integral_eq_integral_abs_deriv_smul_of_mapsTo`, and the quadrature
`MeasureTheory.sub_eq_integral_div_of_mapsTo` of a function `φ` with `φ' = ω ∘ f` when
`|f'| = v ∘ f`: `φ(t₂) - φ(t₁) = ∫_{a₁}^{a₂} ω / v`. For `φ = id` and `ω = 1` this is the elapsed
time `t₂ - t₁ = ∫_{a₁}^{a₂} 1 / v` of a one-dimensional motion between turning points.
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

variable {t₁ t₂ a₁ a₂ : ℝ}

/-- **Change of variables along a leg.** Let `f` be continuous on `[t₁, t₂]` with a nonvanishing
derivative `f'` on `(t₁, t₂)`, and suppose that `f` runs from one of `a₁`, `a₂` to the other,
staying strictly between them on `(t₁, t₂)`. Then the integral of `g` from `a₁` to `a₂` is the
integral of `|f'| • g ∘ f` from `t₁` to `t₂`. -/
theorem integral_eq_integral_abs_deriv_smul_of_mapsTo (ht : t₁ ≤ t₂)
    (hc : ContinuousOn f (Icc t₁ t₂)) (hf' : ∀ t ∈ Ioo t₁ t₂, HasDerivAt f (f' t) t)
    (hf'0 : ∀ t ∈ Ioo t₁ t₂, f' t ≠ 0) (hends : f t₁ = a₁ ∧ f t₂ = a₂ ∨ f t₁ = a₂ ∧ f t₂ = a₁)
    (hmem : MapsTo f (Ioo t₁ t₂) (Ioo a₁ a₂)) (g : ℝ → F) :
    ∫ x in a₁..a₂, g x = ∫ t in t₁..t₂, |f' t| • g (f t) := by
  have himage : f '' Ioo t₁ t₂ = Ioo a₁ a₂ := by
    refine hmem.image_subset.antisymm ?_
    rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · simpa only [h₁, h₂] using intermediate_value_Ioo ht hc
    · simpa only [h₁, h₂] using intermediate_value_Ioo' ht hc
  have ha : a₁ ≤ a₂ := by
    rcases ht.eq_or_lt with rfl | ht'
    · rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> linarith
    · obtain ⟨h₁, h₂⟩ := hmem ⟨left_lt_add_div_two.2 ht', add_div_two_lt_right.2 ht'⟩
      exact (h₁.trans h₂).le
  rw [intervalIntegral.integral_of_le ha, integral_Ioc_eq_integral_Ioo, ← himage,
    integral_image_eq_integral_abs_deriv_smul_of_ne_zero (convex_Ioo t₁ t₂)
      (fun t ht ↦ (hf' t ht).hasDerivWithinAt) hf'0 g, intervalIntegral.integral_of_le ht,
    integral_Ioc_eq_integral_Ioo]

/-- **Quadrature along a leg.** Under the hypotheses of
`MeasureTheory.integral_eq_integral_abs_deriv_smul_of_mapsTo`, let `|f'(t)| = v (f t)` on
`(t₁, t₂)`, and let `φ` have the derivative `ω (f t)`, continuous in `t`, on `[t₁, t₂]`. Then
`φ(t₂) - φ(t₁) = ∫_{a₁}^{a₂} ω / v`. -/
theorem sub_eq_integral_div_of_mapsTo {φ ω v : ℝ → ℝ} (ht : t₁ ≤ t₂)
    (hc : ContinuousOn f (Icc t₁ t₂)) (hf' : ∀ t ∈ Ioo t₁ t₂, HasDerivAt f (f' t) t)
    (hf'0 : ∀ t ∈ Ioo t₁ t₂, f' t ≠ 0) (hends : f t₁ = a₁ ∧ f t₂ = a₂ ∨ f t₁ = a₂ ∧ f t₂ = a₁)
    (hmem : MapsTo f (Ioo t₁ t₂) (Ioo a₁ a₂)) (hv : ∀ t ∈ Ioo t₁ t₂, |f' t| = v (f t))
    (hφ : ∀ t ∈ Icc t₁ t₂, HasDerivAt φ (ω (f t)) t)
    (hω : ContinuousOn (fun t ↦ ω (f t)) (Icc t₁ t₂)) :
    φ t₂ - φ t₁ = ∫ x in a₁..a₂, ω x / v x := by
  rw [integral_eq_integral_abs_deriv_smul_of_mapsTo ht hc hf' hf'0 hends hmem,
    ← intervalIntegral.integral_eq_sub_of_hasDerivAt (by rwa [uIcc_of_le ht])
      (hω.intervalIntegrable_of_Icc ht), intervalIntegral.integral_of_le ht,
    intervalIntegral.integral_of_le ht, integral_Ioc_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ?_
  have hv0 : v (f t) ≠ 0 := hv t ht ▸ abs_ne_zero.2 (hf'0 t ht)
  rw [smul_eq_mul, hv t ht, mul_div_cancel₀ _ hv0]

end MeasureTheory
