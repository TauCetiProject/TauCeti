/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Function.L2Space

/-!
# Pairing a function with a bounded kernel integral

Let `k` be a scalar kernel on an additive group `G`, and let `f` and `g` be integrable functions
with values in an inner product space. If `k (x - y)` is bounded wherever `g x ≠ 0` and
`f y ≠ 0`, then the pairing of `g` with the kernel integral `x ↦ ∫ k (x - y) • f y dy` is the
integral of `k (x - y) ⟪g x, f y⟫` over the product (`TauCeti.integral_inner_integral_smul`).
No integrability of `k` itself is needed, so this applies to singular kernels paired against
functions with separated supports.

Without a kernel, the pairing `⟪u x, v y⟫` of two integrable functions is integrable on the
product (`MeasureTheory.Integrable.inner_fst_snd`), and Fubini's theorem writes the pairing of their
integrals as its integral, `⟪∫ u, ∫ v⟫ = ∫∫ ⟪u x, v y⟫`
(`TauCeti.inner_integral_integral_eq_integral_prod`).
-/

public section

open scoped InnerProductSpace

namespace MeasureTheory

variable {α β 𝕜 V : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α}
  {ν : Measure β} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- The pairing `⟪u x, v y⟫` of two integrable functions is integrable on the product. -/
theorem Integrable.inner_fst_snd {u : α → V} {v : β → V} (hu : Integrable u μ)
    (hv : Integrable v ν) : Integrable (fun z : α × β ↦ ⟪u z.1, v z.2⟫_𝕜) (μ.prod ν) :=
  hu.op_fst_snd (op := fun x y ↦ ⟪x, y⟫_𝕜) continuous_inner
    ⟨1, fun x y ↦ by simpa using norm_inner_le_norm x y⟩ hv

end MeasureTheory

namespace TauCeti

open MeasureTheory

section Inner

variable {α β 𝕜 V : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α}
  {ν : Measure β} [SFinite μ] [SFinite ν] [RCLike 𝕜] [NormedAddCommGroup V]
  [InnerProductSpace 𝕜 V] [NormedSpace ℝ V] [CompleteSpace V]

/-- **Fubini's theorem for a pairing of integrals**: the pairing of the integrals of two
integrable functions is the integral of their pairings over the product,
`⟪∫ u, ∫ v⟫ = ∫∫ ⟪u x, v y⟫`. -/
theorem inner_integral_integral_eq_integral_prod {u : α → V} {v : β → V} (hu : Integrable u μ)
    (hv : Integrable v ν) :
    ⟪∫ x, u x ∂μ, ∫ y, v y ∂ν⟫_𝕜 = ∫ z, ⟪u z.1, v z.2⟫_𝕜 ∂(μ.prod ν) := by
  rw [integral_prod _ (hu.inner_fst_snd hv)]
  simp_rw [integral_inner hv]
  exact (integral_inner_left hu _).symm

end Inner

variable {G 𝕜 F : Type*} [MeasurableSpace G] [AddGroup G] [MeasurableSub₂ G]
  {μ ν : Measure G} [SFinite μ] [SFinite ν] [RCLike 𝕜] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Pairing `g` with a kernel integral of `f` is the integral of the kernel against
`⟪g x, f y⟫` over the product, as soon as the kernel is bounded where `g x ≠ 0` and `f y ≠ 0`. -/
theorem integral_inner_integral_smul {k : G → 𝕜} (hk : Measurable k) {f g : G → F}
    (hf : Integrable f ν) (hg : Integrable g μ) {B : ℝ}
    (hB : ∀ x y, g x ≠ 0 → f y ≠ 0 → ‖k (x - y)‖ ≤ B) :
    ∫ x, inner 𝕜 (g x) (∫ y, k (x - y) • f y ∂ν) ∂μ =
      ∫ p, k (p.1 - p.2) * inner 𝕜 (g p.1) (f p.2) ∂μ.prod ν := by
  have hB' : ∀ x y, ‖k (x - y) * inner 𝕜 (g x) (f y)‖ ≤ B * (‖g x‖ * ‖f y‖) := fun x y ↦ by
    by_cases hx : g x = 0
    · simp [hx]
    by_cases hy : f y = 0
    · simp [hy]
    rw [norm_mul]
    exact mul_le_mul (hB x y hx hy) (norm_inner_le_norm _ _) (norm_nonneg _)
      ((norm_nonneg _).trans (hB x y hx hy))
  have hint : Integrable (fun p : G × G ↦ k (p.1 - p.2) * inner 𝕜 (g p.1) (f p.2)) (μ.prod ν) := by
    refine ((hg.norm.mul_prod hf.norm).const_mul B).mono' ?_ (.of_forall fun p ↦ hB' p.1 p.2)
    exact ((hk.comp (by fun_prop)).aestronglyMeasurable).mul
      (hg.1.comp_fst.inner hf.1.comp_snd)
  rw [integral_prod _ hint]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  by_cases hx : g x = 0
  · simp [hx]
  have hxint : Integrable (fun y ↦ k (x - y) • f y) ν := by
    refine (hf.norm.const_mul B).mono' ((hk.comp (by fun_prop)).aestronglyMeasurable.smul hf.1)
      (.of_forall fun y ↦ ?_)
    by_cases hy : f y = 0
    · simp [hy]
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hB x y hx hy) (norm_nonneg _)
  simp only
  rw [← integral_inner hxint]
  simp_rw [inner_smul_right]

end TauCeti
