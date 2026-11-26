/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Fubini on sigma-finite supports

Fubini's theorem applies to arbitrary measures when the integrand vanishes outside a
rectangle on which both restricted measures are sigma-finite. In particular, a countable
union of rectangles whose two sides have finite measure supplies such a support.
The integrability criterion uses an extended nonnegative norm integral, so a divergent
section cannot be hidden by the default value of the Bochner integral.

These local forms allow integration of functions on product spaces without requiring
sigma-finiteness away from their support.

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*,
  Volume I, §1.2, Remark 1.2.8.

The proofs apply Mathlib's `lintegral_prod` and `integral_integral_swap` to the restricted
measures. The ambient native product measure is not used: it is defined to be zero when
the second measure is not s-finite.
-/

public section

open MeasureTheory Set Function Filter
open scoped ENNReal

namespace MeasureTheory.Integrable

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] {μ : Measure α} {ν : Measure β}
    {s : Set α} {t : Set β} {f : α × β → E}

/-- Integrability on a supporting rectangle gives integrability of almost every ambient
section, even when the ambient measures are not s-finite. -/
theorem prod_right_ae_of_support_subset
    [SFinite (μ.restrict s)] [SFinite (ν.restrict t)]
    (hf : Integrable f ((μ.restrict s).prod (ν.restrict t)))
    (hs : MeasurableSet s) (hfs : support f ⊆ s ×ˢ t) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ f (x, y)) ν := by
  have hzero : ∀ z, z ∉ s ×ˢ t → f z = 0 := support_subset_iff'.1 hfs
  refine ae_of_ae_restrict_of_ae_restrict_compl s ?_ ?_
  · filter_upwards [hf.prod_right_ae] with x hx
    exact IntegrableOn.integrable_of_forall_notMem_eq_zero hx fun y hy ↦
      hzero (x, y) (fun h ↦ hy h.2)
  · apply (ae_restrict_iff' hs.compl).2
    exact .of_forall fun x hx ↦ by
      simp [fun y ↦ hzero (x, y) (fun h ↦ hx h.1)]

/-- The integral of the ambient sections is integrable when the integrand is integrable
on a supporting rectangle with s-finite restricted measures. -/
theorem integral_prod_left_of_support_subset [NormedSpace ℝ E]
    [SFinite (ν.restrict t)]
    (hf : Integrable f ((μ.restrict s).prod (ν.restrict t)))
    (hfs : support f ⊆ s ×ˢ t) : Integrable (fun x ↦ ∫ y, f (x, y) ∂ν) μ := by
  have hzero : ∀ z, z ∉ s ×ˢ t → f z = 0 := support_subset_iff'.1 hfs
  have hinner (x : α) : ∫ y in t, f (x, y) ∂ν = ∫ y, f (x, y) ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦
      hzero (x, y) (fun h ↦ hy h.2)
  have h := hf.integral_prod_left
  simp_rw [hinner] at h
  exact IntegrableOn.integrable_of_forall_notMem_eq_zero h fun x hx ↦ by
    simp [fun y ↦ hzero (x, y) (fun h ↦ hx h.1)]

end MeasureTheory.Integrable

namespace TauCeti

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {s : Set α} {t : Set β}

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Fubini's formula on a supporting rectangle, expressed using ambient iterated integrals.
Only the restrictions to the supporting sets need be s-finite. -/
theorem integral_integral_swap_of_support_subset {f : α × β → E}
    (hfs : support f ⊆ s ×ˢ t) [SFinite (μ.restrict s)] [SFinite (ν.restrict t)]
    (hf : Integrable f ((μ.restrict s).prod (ν.restrict t))) :
    ∫ x, ∫ y, f (x, y) ∂ν ∂μ = ∫ y, ∫ x, f (x, y) ∂μ ∂ν := by
  have hzero : ∀ z, z ∉ s ×ˢ t → f z = 0 := support_subset_iff'.1 hfs
  have hright (x : α) : ∫ y in t, f (x, y) ∂ν = ∫ y, f (x, y) ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦
      hzero (x, y) (fun h ↦ hy h.2)
  have hleft (y : β) : ∫ x in s, f (x, y) ∂μ = ∫ x, f (x, y) ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦
      hzero (x, y) (fun h ↦ hx h.1)
  have houter_right : ∀ x, x ∉ s → (∫ y, f (x, y) ∂ν) = 0 := by
    intro x hx
    simp [fun y ↦ hzero (x, y) (fun h ↦ hx h.1)]
  have houter_left : ∀ y, y ∉ t → (∫ x, f (x, y) ∂μ) = 0 := by
    intro y hy
    simp [fun x ↦ hzero (x, y) (fun h ↦ hy h.2)]
  have h := integral_integral_swap (f := fun x y ↦ f (x, y)) hf
  simp_rw [hright, hleft] at h
  simpa only [setIntegral_eq_integral_of_forall_compl_eq_zero houter_right,
    setIntegral_eq_integral_of_forall_compl_eq_zero houter_left] using h

/-- Localized Fubini for arbitrary measures. A countable finite-measure rectangle support
and finiteness of either iterated extended norm integral give integrable sections almost
everywhere, integrable section integrals in both orders, and equality of the iterated
Bochner integrals. -/
theorem _root_.MeasureTheory.StronglyMeasurable.fubini_of_countable_rectangles
    {f : α × β → E} (hf : StronglyMeasurable f)
    (s : ℕ → Set α) (t : ℕ → Set β)
    (hs : ∀ n, MeasurableSet (s n)) (ht : ∀ n, MeasurableSet (t n))
    (hμ : ∀ n, μ (s n) < ∞) (hν : ∀ n, ν (t n) < ∞)
    (hfs : support f ⊆ ⋃ n, s n ×ˢ t n)
    (hfin : (∫⁻ x, ∫⁻ y, ‖f (x, y)‖ₑ ∂ν ∂μ < ∞) ∨
      (∫⁻ y, ∫⁻ x, ‖f (x, y)‖ₑ ∂μ ∂ν < ∞)) :
    (∀ᵐ x ∂μ, Integrable (fun y ↦ f (x, y)) ν) ∧
      (∀ᵐ y ∂ν, Integrable (fun x ↦ f (x, y)) μ) ∧
      Integrable (fun x ↦ ∫ y, f (x, y) ∂ν) μ ∧
      Integrable (fun y ↦ ∫ x, f (x, y) ∂μ) ν ∧
      (∫ x, ∫ y, f (x, y) ∂ν ∂μ) = ∫ y, ∫ x, f (x, y) ∂μ ∂ν := by
  let := μ.sigmaFinite_restrict_iUnion s hs hμ
  let := ν.sigmaFinite_restrict_iUnion t ht hν
  have hsupport : support f ⊆ (⋃ n, s n) ×ˢ (⋃ n, t n) := by
    intro z hz
    obtain ⟨n, hn⟩ := mem_iUnion.1 (hfs hz)
    exact ⟨mem_iUnion.2 ⟨n, hn.1⟩, mem_iUnion.2 ⟨n, hn.2⟩⟩
  have hI : Integrable f ((μ.restrict (⋃ n, s n)).prod (ν.restrict (⋃ n, t n))) := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_eNorm]
    rcases hfin with hfin | hfin
    · rw [lintegral_prod _ hf.eNorm.aemeasurable]
      exact lt_of_le_of_lt ((setLIntegral_le_lintegral _ _).trans
        (lintegral_mono fun x ↦ setLIntegral_le_lintegral _ _)) hfin
    · rw [lintegral_prod_symm _ hf.eNorm.aemeasurable]
      exact lt_of_le_of_lt ((setLIntegral_le_lintegral _ _).trans
        (lintegral_mono fun y ↦ setLIntegral_le_lintegral _ _)) hfin
  have hswap : support (f ∘ Prod.swap) ⊆ (⋃ n, t n) ×ˢ (⋃ n, s n) := by
    intro z hz
    exact ⟨(hsupport hz).2, (hsupport hz).1⟩
  exact ⟨hI.prod_right_ae_of_support_subset (MeasurableSet.iUnion hs) hsupport,
    hI.swap.prod_right_ae_of_support_subset (MeasurableSet.iUnion ht) hswap,
    hI.integral_prod_left_of_support_subset hsupport,
    hI.swap.integral_prod_left_of_support_subset hswap,
    integral_integral_swap_of_support_subset hsupport hI⟩

end TauCeti
