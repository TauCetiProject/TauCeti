/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Planar area of coordinate lines

The level sets of the real and imaginary coordinates have zero planar Lebesgue measure.
-/

public section

open MeasureTheory Set

namespace Complex

/-- A vertical coordinate line has zero planar area. -/
theorem volume_setOf_re_eq (c : ℝ) : volume {z : ℂ | z.re = c} = 0 := by
  have ht := volume_preserving_equiv_real_prod.measure_preimage_equiv
    ({c} ×ˢ (univ : Set ℝ))
  have hzero : (volume.prod volume) ({c} ×ˢ (univ : Set ℝ)) = 0 := by simp
  convert ht.trans hzero using 2
  ext z
  simp only [mem_preimage, measurableEquivRealProd_apply, mem_prod,
    mem_singleton_iff, mem_univ, and_true, mem_ofPred_eq]

/-- A horizontal coordinate line has zero planar area. -/
theorem volume_setOf_im_eq (c : ℝ) : volume {z : ℂ | z.im = c} = 0 := by
  have ht := volume_preserving_equiv_real_prod.measure_preimage_equiv
    ((univ : Set ℝ) ×ˢ {c})
  have hzero : (volume.prod volume) ((univ : Set ℝ) ×ˢ {c}) = 0 := by simp
  convert ht.trans hzero using 2
  ext z
  simp only [mem_preimage, measurableEquivRealProd_apply, mem_prod,
    mem_singleton_iff, mem_univ, true_and, mem_ofPred_eq]

end Complex
