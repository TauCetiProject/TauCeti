/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.Disintegration.CDFToKernel

import Mathlib.Probability.Kernel.Disintegration.CondCDF
import TauCeti.Probability.Kernel.Composition.MeasureCompProd

/-!
# Markov kernels and disintegration from rational conditional CDFs

This file complements Mathlib's `Mathlib/Probability/Kernel/Disintegration/CDFToKernel.lean`,
`MeasurableStieltjes.lean`, and `CondCDF.lean` with tools for building a single Markov kernel
directly from a measurable rational family `f : α → ℚ → ℝ` and verifying that it disintegrates a
given kernel or finite measure.

In Mathlib, `ProbabilityTheory.IsCondKernelCDF.toKernel` constructs a kernel from an
`IsCondKernelCDF` witness tied to a specific joint kernel `κ`. Here
`ProbabilityTheory.kernelOfMeasurableRat` builds the Markov kernel from `stieltjesOfMeasurableRat`
alone, so the same kernel can be verified to disintegrate a whole family of measures simultaneously.

## Main definitions

* `ProbabilityTheory.kernelOfMeasurableRat`: Markov kernel `Kernel α ℝ` sending `a` to the
  Stieltjes measure of `stieltjesOfMeasurableRat f hf a`.

## Main statements

* `ProbabilityTheory.isRatCondKernelCDF_of_forall_setIntegral_eq`: a measurable rational family
  matching the set integrals `(κ a).real (s ×ˢ Iic q)` for a slicewise-finite kernel `κ` agrees
  `(κ.fst a)`-almost everywhere with `preCDF (κ a)` and is therefore an `IsRatCondKernelCDF`.
* `ProbabilityTheory.compProd_kernelOfMeasurableRat`: if `hf : IsRatCondKernelCDF f κ ν`, then
  `ν ⊗ₖ kernelOfMeasurableRat f hf.measurable = κ`.
* `ProbabilityTheory.compProd_fst_kernelOfMeasurableRat_of_forall_setIntegral_eq`: measure-level
  disintegration `ρ.fst ⊗ₘ kernelOfMeasurableRat f hf = ρ` from the rational set-integral identity.
-/

public section

noncomputable section

open MeasureTheory Set

namespace ProbabilityTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Markov kernel into `ℝ` built from a measurable rational family `f : α → ℚ → ℝ` via
`stieltjesOfMeasurableRat`, without requiring an `IsCondKernelCDF` witness for a specific joint
kernel or measure. -/
def kernelOfMeasurableRat (f : α → ℚ → ℝ) (hf : Measurable f) : Kernel α ℝ where
  toFun a := (stieltjesOfMeasurableRat f hf a).measure
  measurable' := measurable_measure_stieltjesOfMeasurableRat hf

/-- Evaluating `kernelOfMeasurableRat f hf` at a point `a` gives the Stieltjes measure of
`stieltjesOfMeasurableRat f hf a`. -/
@[simp]
theorem kernelOfMeasurableRat_apply (f : α → ℚ → ℝ) (hf : Measurable f) (a : α) :
    kernelOfMeasurableRat f hf a = (stieltjesOfMeasurableRat f hf a).measure :=
  (rfl)

/-- `kernelOfMeasurableRat f hf` is a Markov kernel. -/
instance instIsMarkovKernel_kernelOfMeasurableRat (f : α → ℚ → ℝ) (hf : Measurable f) :
    IsMarkovKernel (kernelOfMeasurableRat f hf) :=
  ⟨instIsProbabilityMeasure_stieltjesOfMeasurableRat hf⟩

/-- A measurable rational family `f : α × β → ℚ → ℝ` matching the set integrals of
`(κ a).real (s ×ˢ Iic q)` for a slicewise-finite kernel `κ : Kernel α (β × ℝ)` agrees
`(κ.fst a)`-almost everywhere with `preCDF (κ a)` and therefore defines an `IsRatCondKernelCDF`
of `κ` with respect to `κ.fst`. -/
theorem isRatCondKernelCDF_of_forall_setIntegral_eq {κ : Kernel α (β × ℝ)}
    [∀ a, IsFiniteMeasure (κ a)] {f : α × β → ℚ → ℝ} (hf : Measurable f)
    (hint : ∀ a q, Integrable (fun b ↦ f (a, b) q) (κ.fst a))
    (hsetInt : ∀ a {s : Set β}, MeasurableSet s → ∀ q : ℚ,
      ∫ b in s, f (a, b) q ∂(κ.fst a) = (κ a).real (s ×ˢ Iic (q : ℝ))) :
    IsRatCondKernelCDF f κ κ.fst := by
  refine
    { measurable := hf
      isRatStieltjesPoint_ae := fun a ↦ ?_
      integrable := hint
      setIntegral := hsetInt }
  have hpre : IsRatCondKernelCDF (fun p r ↦ (preCDF (κ a) r p.2).toReal)
      (Kernel.const Unit (κ a)) (Kernel.const Unit (κ a).fst) :=
    isRatCondKernelCDF_preCDF (κ a)
  have hfst : κ.fst a = (κ a).fst := by rw [Kernel.fst_apply, Measure.fst]
  rw [hfst]
  have hae_eq_pre : ∀ᵐ b ∂(κ a).fst, ∀ q : ℚ, f (a, b) q = (preCDF (κ a) q b).toReal := by
    rw [ae_all_iff]
    intro q
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (μ := (κ a).fst)
      (fun _ _ _ ↦ (hfst ▸ hint a q).integrableOn)
      (fun _ _ _ ↦ (hpre.integrable () q).integrableOn) (fun s hs _ ↦ ?_)
    have hset : ∫ b in s, f (a, b) q ∂(κ a).fst = (κ a).real (s ×ˢ Iic (q : ℝ)) := by
      rw [← hfst]
      exact hsetInt a hs q
    rw [hset]
    simpa [Kernel.const_apply] using (hpre.setIntegral () hs q).symm
  filter_upwards [hae_eq_pre, hpre.isRatStieltjesPoint_ae ()] with b hbeq hsp
  have hf_eq : f (a, b) = fun q ↦ (preCDF (κ a) q b).toReal := funext hbeq
  refine ⟨hf_eq ▸ hsp.mono, hf_eq ▸ hsp.tendsto_atTop_one,
    hf_eq ▸ hsp.tendsto_atBot_zero, fun t ↦ ?_⟩
  simpa only [hbeq] using hsp.iInf_rat_gt_eq t

/-- If `f : α × β → ℚ → ℝ` is a rational conditional kernel CDF of a finite kernel `κ` with
respect to an s-finite kernel `ν`, then `kernelOfMeasurableRat f hf.measurable` disintegrates `κ`
over `ν`. -/
theorem compProd_kernelOfMeasurableRat {κ : Kernel α (β × ℝ)} [IsFiniteKernel κ]
    {ν : Kernel α β} [IsSFiniteKernel ν] {f : α × β → ℚ → ℝ}
    (hf : IsRatCondKernelCDF f κ ν) :
    ν ⊗ₖ kernelOfMeasurableRat f hf.measurable = κ := by
  have hCond := isCondKernelCDF_stieltjesOfMeasurableRat hf
  have htoK : hCond.toKernel (stieltjesOfMeasurableRat f hf.measurable) =
      kernelOfMeasurableRat f hf.measurable := by
    ext p : 1
    rw [IsCondKernelCDF.toKernel_apply, kernelOfMeasurableRat_apply]
  rw [← htoK]
  exact compProd_toKernel hCond

/-- For a finite measure `ρ : Measure (β × ℝ)`, if a measurable rational family `f : β → ℚ → ℝ`
is `ρ.fst`-integrable and satisfies `∫ b in s, f b q ∂ρ.fst = ρ.real (s ×ˢ Iic q)` for every
measurable `s` and rational `q`, then `kernelOfMeasurableRat f hf` disintegrates `ρ` over
`ρ.fst`. -/
theorem compProd_fst_kernelOfMeasurableRat_of_forall_setIntegral_eq {ρ : Measure (β × ℝ)}
    [IsFiniteMeasure ρ] {f : β → ℚ → ℝ} (hf : Measurable f)
    (hint : ∀ q, Integrable (fun b ↦ f b q) ρ.fst)
    (hsetInt : ∀ {s : Set β}, MeasurableSet s → ∀ q : ℚ,
      ∫ b in s, f b q ∂ρ.fst = ρ.real (s ×ˢ Iic (q : ℝ))) :
    ρ.fst ⊗ₘ kernelOfMeasurableRat f hf = ρ := by
  have hRat : IsRatCondKernelCDF (fun (p : Unit × β) ↦ f p.2)
      (Kernel.const Unit ρ) (Kernel.const Unit ρ).fst := by
    rw [Kernel.fst_const]
    exact isRatCondKernelCDF_of_forall_setIntegral_eq (hf.comp measurable_snd)
      (fun _ q ↦ by simpa using hint q)
      (fun _ _ hs q ↦ by simpa using hsetInt hs q)
  have hcp := compProd_kernelOfMeasurableRat hRat
  have hprod : kernelOfMeasurableRat (fun (p : Unit × β) ↦ f p.2) (hf.comp measurable_snd) =
      (kernelOfMeasurableRat f hf).prodMkLeft Unit := by
    ext ⟨⟨⟩, b⟩ : 1
    rw [kernelOfMeasurableRat_apply, Kernel.prodMkLeft_apply, kernelOfMeasurableRat_apply,
      stieltjesOfMeasurableRat_unit_prod]
  simp only [Kernel.fst_const, hprod, Kernel.const_compProd_prodMkLeft] at hcp
  simpa using congrArg (fun k ↦ k ()) hcp

end ProbabilityTheory
