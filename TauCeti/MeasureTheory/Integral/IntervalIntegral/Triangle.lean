/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Fubini's theorem on a triangle

For a function `g` integrable on the square with opposite corners `(c, c)` and `(d, d)`, the two
iterated integrals over the triangle between the diagonal and the side `w = c` agree:

`∫ v in c..d, ∫ w in c..v, g v w = ∫ w in c..d, ∫ v in w..d, g v w`.

## Main results

* `intervalIntegral.integral_integral_swap_triangle`: Fubini's theorem on a triangle.
-/

public section

open MeasureTheory Set

namespace intervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An interval integral over `c..v` with `v ≤ d` is the integral over `Ioc c d` of the restriction
to `w ≤ v`. -/
private theorem integral_eq_integral_indicator_le {c d v : ℝ} (hc : c ≤ v) (hd : v ≤ d)
    (f : ℝ → E) :
    ∫ w in c..v, f w = ∫ w in Ioc c d, (Iic v).indicator f w := by
  rw [integral_of_le hc, MeasureTheory.integral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioc_of_le hd]

/-- An interval integral over `w..d` with `c ≤ w` is the integral over `Ioc c d` of the
restriction to `w ≤ v`. -/
private theorem integral_eq_integral_indicator_ge {c d w : ℝ} (hc : c < w) (hd : w ≤ d)
    (f : ℝ → E) :
    ∫ v in w..d, f v = ∫ v in Ioc c d, (Ici w).indicator f v := by
  have h : Ici w ∩ Ioc c d = Icc w d :=
    Set.ext fun x ↦ ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hc.trans_le h.1, h.2⟩⟩
  rw [integral_of_le hd, MeasureTheory.integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici, h, integral_Icc_eq_integral_Ioc]

/-- Fubini's theorem on a triangle, for `c ≤ d`. -/
private theorem integral_integral_swap_triangle_of_le {g : ℝ → ℝ → E} {c d : ℝ} (hcd : c ≤ d)
    (hg : IntegrableOn (Function.uncurry g) (Icc c d ×ˢ Icc c d)) :
    ∫ v in c..d, ∫ w in c..v, g v w = ∫ w in c..d, ∫ v in w..d, g v w := by
  have hT : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} := measurableSet_le measurable_snd measurable_fst
  set h := {p : ℝ × ℝ | p.2 ≤ p.1}.indicator (Function.uncurry g) with h_def
  have hint : Integrable (Function.uncurry (Function.curry h))
      ((volume.restrict (Ioc c d)).prod (volume.restrict (Ioc c d))) := by
    rw [Function.uncurry_curry, Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hg.mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)).indicator hT
  have hl : ∫ v in c..d, ∫ w in c..v, g v w = ∫ v in Ioc c d, ∫ w in Ioc c d, h (v, w) := by
    rw [integral_of_le hcd]
    refine setIntegral_congr_fun measurableSet_Ioc fun v hv ↦ ?_
    simp only [integral_eq_integral_indicator_le hv.1.le hv.2, h_def, indicator_apply, mem_Iic,
      mem_ofPred_eq, Function.uncurry_apply_pair]
  have hr : ∫ w in c..d, ∫ v in w..d, g v w = ∫ w in Ioc c d, ∫ v in Ioc c d, h (v, w) := by
    rw [integral_of_le hcd]
    refine setIntegral_congr_fun measurableSet_Ioc fun w hw ↦ ?_
    simp only [integral_eq_integral_indicator_ge hw.1 hw.2, h_def, indicator_apply, mem_Ici,
      mem_ofPred_eq, Function.uncurry_apply_pair]
  rw [hl, hr]
  exact integral_integral_swap hint

/-- Reversing the orientation of both iterated integrals over a triangle. -/
private theorem integral_integral_symm (f : ℝ → ℝ → E) (c d : ℝ) :
    ∫ v in c..d, ∫ w in c..v, f v w = ∫ v in d..c, ∫ w in v..c, f v w := by
  rw [integral_symm d c, ← integral_neg]
  exact integral_congr fun v _ ↦ by rw [integral_symm v c, neg_neg]

/-- **Fubini's theorem on a triangle.** For `g` integrable on the square with opposite corners
`(c, c)` and `(d, d)`, `∫ v in c..d, ∫ w in c..v, g v w = ∫ w in c..d, ∫ v in w..d, g v w`. -/
theorem integral_integral_swap_triangle {g : ℝ → ℝ → E} {c d : ℝ}
    (hg : IntegrableOn (Function.uncurry g) (uIcc c d ×ˢ uIcc c d)) :
    ∫ v in c..d, ∫ w in c..v, g v w = ∫ w in c..d, ∫ v in w..d, g v w := by
  rcases le_total c d with h | h
  · rw [uIcc_of_le h] at hg
    exact integral_integral_swap_triangle_of_le h hg
  · -- Reverse both orientations and apply the first case to `(v, w) ↦ g w v`.
    rw [uIcc_of_ge h] at hg
    calc ∫ v in c..d, ∫ w in c..v, g v w = ∫ v in d..c, ∫ w in v..c, g v w :=
          integral_integral_symm g c d
      _ = ∫ v in d..c, ∫ w in d..v, g w v :=
          (integral_integral_swap_triangle_of_le (g := fun v w ↦ g w v) h hg.swap).symm
      _ = ∫ w in c..d, ∫ v in w..d, g v w :=
          integral_integral_symm (fun w v ↦ g v w) d c

end intervalIntegral
