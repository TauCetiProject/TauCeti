/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Integrals over a strip of functions periodic in the second variable

Let `f : α × ℝ → E` be periodic in its second variable with period `c`, and integrate against
`μ.prod volume`. The translation `(x, t) ↦ (x, t + c)` preserves this measure and fixes `f`, so the
integrability and the integral of `f` over the period band `s ×ˢ [a - c, a)` are those over the next
band `s ×ˢ [a, a + c)` (`TauCeti.integrableOn_prod_Ico_sub_of_periodic`,
`TauCeti.setIntegral_prod_Ico_sub_of_periodic`). Hence `f` is integrable over two periods
`s ×ˢ [a - c, a + c)` as soon as it is integrable over one, and its integral there is twice the
integral over one period (`TauCeti.integrableOn_prod_Ico_sub_add_of_periodic`,
`TauCeti.setIntegral_prod_Ico_sub_add_of_periodic`).

For the energy density of a map on the cylinder `ℝ × S¹`, lifted to a map on `ℝ × ℝ` that is
`1`-periodic in `t`, this bounds the energy over a disc of radius `1` about a point of the strip
`ℝ × [0, 1)` by twice the energy over the strip.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ] [NormedAddCommGroup E]
  {f : α × ℝ → E} {s : Set α} {a c : ℝ}

/-- A function periodic in the second variable with period `c` is integrable over the band
`s ×ˢ [a - c, a)` when it is integrable over the next band `s ×ˢ [a, a + c)`. -/
theorem integrableOn_prod_Ico_sub_of_periodic (hf : ∀ x t, f (x, t + c) = f (x, t))
    (h : IntegrableOn f (s ×ˢ Ico a (a + c)) (μ.prod volume)) :
    IntegrableOn f (s ×ˢ Ico (a - c) a) (μ.prod volume) := by
  have he : MeasurableEmbedding (Prod.map id (· + c) : α × ℝ → α × ℝ) :=
    MeasurableEmbedding.id.prodMap (measurableEmbedding_addRight c)
  have h' := (((MeasurePreserving.id μ).prod (measurePreserving_add_right volume c)
    ).integrableOn_comp_preimage he).2 h
  have hfc : f ∘ Prod.map id (· + c) = f := funext fun z ↦ hf z.1 z.2
  rwa [hfc, preimage_prod_map_prod, preimage_id, preimage_add_const_Ico, add_sub_cancel_right]
    at h'

/-- A function periodic in the second variable with period `c` and integrable over one period
`s ×ˢ [a, a + c)` is integrable over two periods `s ×ˢ [a - c, a + c)`. -/
theorem integrableOn_prod_Ico_sub_add_of_periodic (hf : ∀ x t, f (x, t + c) = f (x, t))
    (h : IntegrableOn f (s ×ˢ Ico a (a + c)) (μ.prod volume)) :
    IntegrableOn f (s ×ˢ Ico (a - c) (a + c)) (μ.prod volume) := by
  rcases lt_or_ge c 0 with hc | hc
  · rw [Ico_eq_empty (by linarith), prod_empty]
    exact integrableOn_empty
  rw [← Ico_union_Ico_eq_Ico (b := a) (by linarith) (by linarith), prod_union]
  exact (integrableOn_prod_Ico_sub_of_periodic hf h).union h

variable [NormedSpace ℝ E]

/-- A function periodic in the second variable with period `c` has the same integral over the
band `s ×ˢ [a - c, a)` as over the next band `s ×ˢ [a, a + c)`. No integrability or measurability
hypothesis is needed. -/
theorem setIntegral_prod_Ico_sub_of_periodic (hf : ∀ x t, f (x, t + c) = f (x, t)) :
    ∫ z in s ×ˢ Ico (a - c) a, f z ∂μ.prod volume =
      ∫ z in s ×ˢ Ico a (a + c), f z ∂μ.prod volume := by
  have he : MeasurableEmbedding (Prod.map id (· + c) : α × ℝ → α × ℝ) :=
    MeasurableEmbedding.id.prodMap (measurableEmbedding_addRight c)
  have h := ((MeasurePreserving.id μ).prod (measurePreserving_add_right volume c)
    ).setIntegral_preimage_emb he f (s ×ˢ Ico a (a + c))
  have hfc (z : α × ℝ) : f (Prod.map id (· + c) z) = f z := hf z.1 z.2
  rw [preimage_prod_map_prod, preimage_id, preimage_add_const_Ico, add_sub_cancel_right] at h
  simpa only [hfc] using h

/-- The integral of a function periodic in the second variable with period `c` over two periods
`s ×ˢ [a - c, a + c)` is twice its integral over one period `s ×ˢ [a, a + c)`, if it is integrable
over one period. -/
theorem setIntegral_prod_Ico_sub_add_of_periodic (hs : MeasurableSet s)
    (hf : ∀ x t, f (x, t + c) = f (x, t))
    (h : IntegrableOn f (s ×ˢ Ico a (a + c)) (μ.prod volume)) :
    ∫ z in s ×ˢ Ico (a - c) (a + c), f z ∂μ.prod volume =
      2 • ∫ z in s ×ˢ Ico a (a + c), f z ∂μ.prod volume := by
  rcases lt_or_ge c 0 with hc | hc
  · rw [Ico_eq_empty (by linarith), Ico_eq_empty (by linarith), prod_empty]
    simp
  rw [← Ico_union_Ico_eq_Ico (b := a) (by linarith) (by linarith), prod_union,
    setIntegral_union (disjoint_prod.2 (Or.inr Ico_disjoint_Ico_same))
      (hs.prod measurableSet_Ico) (integrableOn_prod_Ico_sub_of_periodic hf h) h,
    setIntegral_prod_Ico_sub_of_periodic hf, two_nsmul]

end TauCeti
