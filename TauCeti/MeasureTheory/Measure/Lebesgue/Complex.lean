/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.Analysis.Complex.Coordinates
public import TauCeti.Analysis.Complex.Euclidean.Space
import Mathlib.Topology.Order.Compact

/-!
# Planar area of coordinate lines, graphs and rectangles

Coordinate lines and continuous graphs over compact intervals have zero planar Lebesgue measure.
Interchanging the real and imaginary coordinates preserves planar area. On a rectangle
`s ×ℂ t`, a function of the real or imaginary part integrates by Fubini as the length of the other
side times its one-dimensional integral (`Complex.setLIntegral_reProdIm_comp_re`,
`Complex.setLIntegral_reProdIm_comp_im`).
Splitting complex vectors into real and imaginary blocks preserves product volume, using
Mathlib's `Complex.volume_preserving_equiv_real_prod` coordinatewise and
`PiLp.volume_preserving_toLp` for the Euclidean volume normalization.
-/

public section

open MeasureTheory Set
open scoped ENNReal

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

/-- On a rectangle `s ×ℂ t`, a function of the real part integrates as `volume t` times its
integral over `s`. -/
theorem setLIntegral_reProdIm_comp_re (s t : Set ℝ) {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z in s ×ℂ t, F z.re = volume t * ∫⁻ x in s, F x := by
  have h := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding (fun q : ℝ × ℝ => F q.1) (s ×ˢ t)
  have h2 := lintegral_prod_mul (μ := volume.restrict s) (ν := volume.restrict t) (f := F)
    (g := fun _ => 1) hF.aemeasurable aemeasurable_const
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h2
  simp only [mul_one, one_mul, lintegral_const, Measure.restrict_apply_univ] at h2
  rw [mul_comm, ← h2, ← h]
  rfl

/-- On a rectangle `s ×ℂ t`, a function of the imaginary part integrates as `volume s` times its
integral over `t`. -/
theorem setLIntegral_reProdIm_comp_im (s t : Set ℝ) {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z in s ×ℂ t, F z.im = volume s * ∫⁻ y in t, F y := by
  have h := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding (fun q : ℝ × ℝ => F q.2) (s ×ˢ t)
  have h2 := lintegral_prod_mul (μ := volume.restrict s) (ν := volume.restrict t)
    (f := fun _ => 1) (g := F) aemeasurable_const hF.aemeasurable
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h2
  simp only [one_mul, lintegral_const, Measure.restrict_apply_univ] at h2
  rw [← h2, ← h]
  rfl

end Complex

namespace TauCeti

/-- Splitting complex coordinates into their real and imaginary blocks preserves volume,
including on an empty coordinate type. -/
theorem volume_preserving_complexToRealEuclidean {ι : Type*} [Fintype ι] :
    MeasurePreserving (complexToRealEuclidean ι) volume volume := by
  have h₁ := volume_preserving_pi (fun _ : ι ↦ Complex.volume_preserving_equiv_real_prod)
  have h₂ := volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι
  have h₃ := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : ι ⊕ ι ↦ ℝ)
  have h₄ := PiLp.volume_preserving_toLp (ι ⊕ ι)
  rw [volume_pi] at h₄
  exact (h₄.comp (h₃.comp (h₂.comp h₁))).congr (by fun_prop) (ae_of_all _ fun z ↦ by
    ext j
    cases j <;> simp [Function.comp_def, MeasurableEquiv.sumPiEquivProdPi,
      MeasurableEquiv.arrowProdEquivProdArrow])

end TauCeti
