/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.Analysis.Complex.Coordinates
public import TauCeti.Analysis.Complex.Euclidean.Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Order.Compact

/-!
# Planar area of coordinate lines, graphs and rectangles

The set `s ×ℂ t = {z | z.re ∈ s ∧ z.im ∈ t}` is measurable when `s` and `t` are
(`MeasurableSet.reProdIm`).
Coordinate lines and continuous graphs over compact intervals have zero planar Lebesgue measure.
Interchanging the real and imaginary coordinates preserves planar area. On a rectangle
`s ×ℂ t`, planar measure is the product of the restrictions to the sides, so a function of the
imaginary part integrable on a rectangle of positive width is integrable on the vertical side,
and a function of the real or imaginary part integrates by Fubini as the length of the other
side times its one-dimensional integral (`Complex.setLIntegral_reProdIm_comp_re`,
`Complex.setLIntegral_reProdIm_comp_im`).
Splitting complex vectors into real and imaginary blocks preserves product volume, using
Mathlib's `Complex.volume_preserving_equiv_real_prod` coordinatewise and
`PiLp.volume_preserving_toLp` for the Euclidean volume normalization.
-/

public section

open MeasureTheory Set
open scoped ENNReal

/-- The set `s ×ℂ t` is measurable when `s` and `t` are. -/
theorem MeasurableSet.reProdIm {s t : Set ℝ} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    MeasurableSet (s ×ℂ t) := by
  rw [Complex.reProdIm]
  exact (Complex.continuous_re.measurable hs).inter (Complex.continuous_im.measurable ht)

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

/-- A horizontal line has zero area, so the closed and open half-planes above it agree almost
everywhere. -/
theorem setOf_le_im_ae_eq (c : ℝ) : {z : ℂ | c ≤ z.im} =ᵐ[volume] {z : ℂ | c < z.im} := by
  refine (ae_eq_set).2 ⟨measure_mono_null (fun z hz => ?_) (volume_setOf_im_eq c),
    measure_mono_null (fun z hz => ?_) (volume_setOf_im_eq c)⟩
  · have h1 : c ≤ z.im := hz.1
    have h2 : ¬ c < z.im := hz.2
    exact le_antisymm (not_lt.1 h2) h1
  · have h1 : c < z.im := hz.1
    exact absurd h1.le hz.2

/-- Restricted to a rectangle, planar Lebesgue measure is the product of the restrictions to its
sides. -/
theorem measurePreserving_measurableEquivRealProd_reProdIm {s t : Set ℝ} (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    MeasurePreserving measurableEquivRealProd (volume.restrict (s ×ℂ t))
      ((volume.restrict s).prod (volume.restrict t)) := by
  have h := volume_preserving_equiv_real_prod.restrict_preimage (hs.prod ht)
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at h
  exact h

/-- A function of the imaginary part integrable on a rectangle of positive width is integrable
on the vertical side. -/
theorem integrableOn_of_integrableOn_comp_im_reProdIm {E : Type*} [NormedAddCommGroup E]
    {s t : Set ℝ} (hs : MeasurableSet s) (ht : MeasurableSet t) (hs0 : volume s ≠ 0) {g : ℝ → E}
    (h : IntegrableOn (fun z : ℂ => g z.im) (s ×ℂ t)) : IntegrableOn g t := by
  refine Integrable.of_comp_snd (μ := volume.restrict s) ?_ (by simpa using hs0)
  refine ((measurePreserving_measurableEquivRealProd_reProdIm hs ht).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _) (g := fun q : ℝ × ℝ => g q.2)).1 ?_
  simpa only [Function.comp_def, measurableEquivRealProd_apply, IntegrableOn] using h

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
