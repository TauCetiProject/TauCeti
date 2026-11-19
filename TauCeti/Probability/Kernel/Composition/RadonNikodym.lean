/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Radon–Nikodym derivatives under kernel composition

This file supplements `Mathlib.Probability.Kernel.Composition.RadonNikodym` with identities
relating the Radon–Nikodym derivative `μ.rnDeriv ν` of two base measures on `α` to the
Radon–Nikodym derivative `(κ ∘ₘ μ).rnDeriv (κ ∘ₘ ν)` of their pushforwards along a kernel
`κ : Kernel α β`, integrated against the composition-product `ν ⊗ₘ κ`.

## Main statements

* `MeasureTheory.Measure.lintegral_compProd_rnDeriv_mul`: for an s-finite measure `ν`, an s-finite
  kernel `κ`, a measure `μ ≪ ν` with a Lebesgue decomposition with respect to `ν`, and a
  `(κ ∘ₘ ν)`-a.e. measurable `f : β → ℝ≥0∞`, integrating `μ.rnDeriv ν z.1 * f z.2` against
  `ν ⊗ₘ κ` recovers `∫⁻ y, f y ∂(κ ∘ₘ μ)`.
* `MeasureTheory.Measure.lintegral_compProd_rnDeriv_mul_eq_lintegral_rnDeriv_comp`: under an
  additional Lebesgue decomposition for `κ ∘ₘ μ` with respect to `κ ∘ₘ ν`, the same integral equals
  `∫⁻ y, (κ ∘ₘ μ).rnDeriv (κ ∘ₘ ν) y * f y ∂(κ ∘ₘ ν)`.
* `MeasureTheory.Measure.ae_compProd_rnDeriv_eq_zero_of_rnDeriv_comp_eq_zero`: assuming only
  `(κ ∘ₘ μ).HaveLebesgueDecomposition (κ ∘ₘ ν)`, almost everywhere under `ν ⊗ₘ κ`, vanishing of
  `(κ ∘ₘ μ).rnDeriv (κ ∘ₘ ν)` at `z.2` forces `μ.rnDeriv ν` to vanish at `z.1`. No `μ ≪ ν`,
  `SFinite ν`, `IsSFiniteKernel κ`, or `μ.HaveLebesgueDecomposition ν` assumption is needed: when
  `ν` or `κ` is not s-finite, `ν ⊗ₘ κ = 0`, and otherwise the absolutely continuous part
  `ν.withDensity (μ.rnDeriv ν) ≤ μ` pushes forward to a measure dominated by both `κ ∘ₘ μ` and
  `κ ∘ₘ ν`.
-/

public section

open ProbabilityTheory Set
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- For an s-finite measure `ν`, an s-finite kernel `κ`, a measure `μ ≪ ν` with a Lebesgue
decomposition with respect to `ν`, and a `(κ ∘ₘ ν)`-a.e. measurable `f : β → ℝ≥0∞`, integrating
`(dμ/dν)(z.1) * f(z.2)` against the composition-product `ν ⊗ₘ κ` recovers the integral of `f`
against `κ ∘ₘ μ`. -/
theorem lintegral_compProd_rnDeriv_mul (μ ν : Measure α) [SFinite ν] (κ : Kernel α β)
    [IsSFiniteKernel κ] [μ.HaveLebesgueDecomposition ν] (hμν : μ ≪ ν)
    {f : β → ℝ≥0∞} (hf : AEMeasurable f (κ ∘ₘ ν)) :
    ∫⁻ z, μ.rnDeriv ν z.1 * f z.2 ∂(ν ⊗ₘ κ) = ∫⁻ y, f y ∂(κ ∘ₘ μ) := by
  let g : β → ℝ≥0∞ := hf.mk f
  have hg : Measurable g := hf.measurable_mk
  have hfg : f =ᵐ[κ ∘ₘ ν] g := hf.ae_eq_mk
  have hfg_compProd : (fun z : α × β => μ.rnDeriv ν z.1 * f z.2) =ᵐ[ν ⊗ₘ κ]
      fun z => μ.rnDeriv ν z.1 * g z.2 := by
    have hsnd : (ν ⊗ₘ κ).map Prod.snd = κ ∘ₘ ν := Measure.snd_compProd ν κ
    have hmap : ∀ᵐ z ∂(ν ⊗ₘ κ), f z.2 = g z.2 :=
      ae_of_ae_map measurable_snd.aemeasurable (by rw [hsnd]; exact hfg)
    filter_upwards [hmap] with z hz
    rw [hz]
  rw [lintegral_congr_ae hfg_compProd, lintegral_congr_ae ((hμν.comp_right κ).ae_eq hfg)]
  have hm : Measurable (fun z : α × β => μ.rnDeriv ν z.1 * g z.2) :=
    ((measurable_rnDeriv μ ν).comp measurable_fst).mul (hg.comp measurable_snd)
  rw [lintegral_compProd hm]
  simp_rw [lintegral_const_mul _ hg]
  rw [lintegral_rnDeriv_mul hμν hg.lintegral_kernel.aemeasurable,
    ← lintegral_bind κ.aemeasurable hg.aemeasurable]

/-- For an s-finite measure `ν`, an s-finite kernel `κ`, a measure `μ ≪ ν` with Lebesgue
decompositions before and after pushing forward through `κ`, and a `(κ ∘ₘ ν)`-a.e. measurable
`f : β → ℝ≥0∞`, integrating `(dμ/dν)(z.1) * f(z.2)` against `ν ⊗ₘ κ` equals integrating
`(d(κ ∘ₘ μ)/d(κ ∘ₘ ν))(y) * f(y)` against `κ ∘ₘ ν`. -/
theorem lintegral_compProd_rnDeriv_mul_eq_lintegral_rnDeriv_comp (μ ν : Measure α) [SFinite ν]
    (κ : Kernel α β) [IsSFiniteKernel κ] [μ.HaveLebesgueDecomposition ν]
    [(κ ∘ₘ μ).HaveLebesgueDecomposition (κ ∘ₘ ν)] (hμν : μ ≪ ν)
    {f : β → ℝ≥0∞} (hf : AEMeasurable f (κ ∘ₘ ν)) :
    ∫⁻ z, μ.rnDeriv ν z.1 * f z.2 ∂(ν ⊗ₘ κ) =
      ∫⁻ y, (κ ∘ₘ μ).rnDeriv (κ ∘ₘ ν) y * f y ∂(κ ∘ₘ ν) := by
  rw [lintegral_compProd_rnDeriv_mul μ ν κ hμν hf,
    ← lintegral_rnDeriv_mul (hμν.comp_right κ) hf]

/-- Assuming `(κ ∘ₘ μ).HaveLebesgueDecomposition (κ ∘ₘ ν)`, almost everywhere under `ν ⊗ₘ κ`,
vanishing of the pushed-forward Radon–Nikodym derivative `d(κ ∘ₘ μ)/d(κ ∘ₘ ν)` at the second
coordinate forces `dμ/dν` to vanish at the first coordinate. -/
theorem ae_compProd_rnDeriv_eq_zero_of_rnDeriv_comp_eq_zero (μ ν : Measure α) (κ : Kernel α β)
    [(κ ∘ₘ μ).HaveLebesgueDecomposition (κ ∘ₘ ν)] :
    ∀ᵐ z ∂(ν ⊗ₘ κ), (κ ∘ₘ μ).rnDeriv (κ ∘ₘ ν) z.2 = 0 → μ.rnDeriv ν z.1 = 0 := by
  by_cases hν : SFinite ν
  swap
  · rw [compProd_of_not_sfinite _ _ hν]
    simp
  by_cases hκ : IsSFiniteKernel κ
  swap
  · rw [compProd_of_not_isSFiniteKernel _ _ hκ]
    simp
  set s : Set β := {y | (κ ∘ₘ μ).rnDeriv (κ ∘ₘ ν) y = 0}
  have hs : MeasurableSet s := measurable_rnDeriv (κ ∘ₘ μ) (κ ∘ₘ ν) (measurableSet_singleton 0)
  set μ_ac : Measure α := ν.withDensity (μ.rnDeriv ν)
  have hle : κ ∘ₘ μ_ac ≤ κ ∘ₘ μ := Measure.le_iff.2 fun t ht => by
    rw [bind_apply ht κ.aemeasurable, bind_apply ht κ.aemeasurable]
    exact lintegral_mono' (withDensity_rnDeriv_le μ ν) le_rfl
  have hac : κ ∘ₘ μ_ac ≪ κ ∘ₘ ν := (withDensity_absolutelyContinuous ν (μ.rnDeriv ν)).comp_right κ
  obtain ⟨t, ht, hsing, hνtc⟩ := mutuallySingular_singularPart (κ ∘ₘ μ) (κ ∘ₘ ν)
  have hzero_inter : (κ ∘ₘ μ_ac) (s ∩ t) = 0 := by
    refine le_antisymm ?_ zero_le
    calc (κ ∘ₘ μ_ac) (s ∩ t) ≤ (κ ∘ₘ μ) (s ∩ t) := hle (s ∩ t)
      _ = (κ ∘ₘ μ).singularPart (κ ∘ₘ ν) (s ∩ t) +
          (κ ∘ₘ ν).withDensity ((κ ∘ₘ μ).rnDeriv (κ ∘ₘ ν)) (s ∩ t) := by
          conv_lhs => rw [haveLebesgueDecomposition_add (κ ∘ₘ μ) (κ ∘ₘ ν)]
          rw [add_apply]
      _ = 0 := by
          have h1 : (κ ∘ₘ μ).singularPart (κ ∘ₘ ν) (s ∩ t) = 0 :=
            measure_mono_null inter_subset_right hsing
          have h2 : (κ ∘ₘ ν).withDensity ((κ ∘ₘ μ).rnDeriv (κ ∘ₘ ν)) (s ∩ t) = 0 := by
            rw [withDensity_apply _ (hs.inter ht)]
            exact setLIntegral_eq_zero (hs.inter ht) fun _ hy => hy.1
          rw [h1, h2, zero_add]
  have hzero_compl : (κ ∘ₘ μ_ac) (s ∩ tᶜ) = 0 :=
    hac (measure_mono_null inter_subset_right hνtc)
  have hzero : (κ ∘ₘ μ_ac) s = 0 := by
    rw [← Set.inter_union_compl s t]
    exact measure_union_null hzero_inter hzero_compl
  have hm : Measurable (fun z : α × β =>
      (Set.univ ×ˢ s).indicator (fun w : α × β => μ.rnDeriv ν w.1) z) :=
    ((measurable_rnDeriv μ ν).comp measurable_fst).indicator (MeasurableSet.univ.prod hs)
  have hlint :
      ∫⁻ z, (Set.univ ×ˢ s).indicator (fun w : α × β => μ.rnDeriv ν w.1) z ∂(ν ⊗ₘ κ) = 0 := by
    rw [lintegral_compProd hm]
    have hinner : ∀ x, ∫⁻ y, (Set.univ ×ˢ s).indicator (fun w : α × β => μ.rnDeriv ν w.1)
        (x, y) ∂κ x = μ.rnDeriv ν x * κ x s := fun x => by
      have hind : (fun y => (Set.univ ×ˢ s).indicator (fun w : α × β => μ.rnDeriv ν w.1) (x, y)) =
          s.indicator (fun _ => μ.rnDeriv ν x) := by
        ext y; by_cases hy : y ∈ s <;> simp [hy]
      rw [hind, lintegral_indicator hs, setLIntegral_const]
    simp_rw [hinner, ← Pi.mul_apply (μ.rnDeriv ν) (fun x => κ x s)]
    rw [← lintegral_withDensity_eq_lintegral_mul ν (measurable_rnDeriv μ ν) (κ.measurable_coe hs),
      ← bind_apply hs κ.aemeasurable]
    exact hzero
  filter_upwards [(lintegral_eq_zero_iff hm).1 hlint] with z hz hzs
  have hmem : z ∈ Set.univ ×ˢ s := ⟨trivial, hzs⟩
  simpa only [Pi.zero_apply, Set.indicator_of_mem hmem] using hz

end MeasureTheory.Measure
