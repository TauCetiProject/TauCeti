/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.Analysis.Complex.Coordinates
import Mathlib.Topology.Order.Compact

/-!
# Planar area of coordinate lines and graphs

Coordinate lines and continuous graphs over compact intervals have zero planar Lebesgue measure.
Interchanging the real and imaginary coordinates preserves planar area.
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

/-- A continuous graph over a compact interval has zero planar area. -/
theorem volume_setOf_re_mem_Icc_im_eq {a b : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
    volume {z : ℂ | z.re ∈ Icc a b ∧ z.im = f z.re} = 0 := by
  let S := {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2 = f p.1}
  have hS : MeasurableSet S := by
    have hc : IsClosed {p : ℝ × ℝ | p.1 ∈ Icc a b} :=
      isClosed_Icc.preimage continuous_fst
    have hf' : ContinuousOn (fun p : ℝ × ℝ ↦ f p.1) {p : ℝ × ℝ | p.1 ∈ Icc a b} :=
      hf.comp continuous_fst.continuousOn (fun _ hx ↦ hx)
    exact (hc.isClosed_eq continuous_snd.continuousOn hf').measurableSet
  have hzero : (volume.prod volume) S = 0 := by
    apply Measure.measure_prod_null_of_ae_null hS
    apply Filter.Eventually.of_forall
    intro x
    simp only [S, Set.preimage_ofPred_eq, Pi.zero_apply]
    by_cases hx : x ∈ Icc a b
    · simp only [hx, true_and, Set.ofPred_eq_eq_singleton, measure_singleton]
    · simp only [hx, false_and, Set.ofPred_false, measure_empty]
  have ht := Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv S
  simpa only [S, preimage_ofPred_eq, Complex.measurableEquivRealProd_apply] using ht.trans hzero

/-- Interchanging the coordinates preserves planar area. -/
theorem measurePreserving_coordinateSwapCLE :
    MeasurePreserving coordinateSwapCLE (volume : Measure ℂ) volume := by
  have heq : (coordinateSwapCLE : ℂ → ℂ) =
      measurableEquivRealProd.symm ∘ Prod.swap ∘ measurableEquivRealProd := by
    funext z
    simp only [Function.comp_apply, coordinateSwapCLE_apply, measurableEquivRealProd_apply,
      Prod.swap_prod_mk, measurableEquivRealProd_symm_apply]
  rw [heq]
  exact Complex.volume_preserving_equiv_real_prod.symm.comp
    (Measure.measurePreserving_swap.comp Complex.volume_preserving_equiv_real_prod)

end Complex
