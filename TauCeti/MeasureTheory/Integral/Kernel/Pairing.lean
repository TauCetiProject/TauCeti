/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Pairing a function with a bounded kernel integral

Let `k` be a scalar kernel on an additive group `G`, and let `f` and `g` be integrable functions
with values in an inner product space. If `k (x - y)` is bounded wherever `g x ≠ 0` and
`f y ≠ 0`, then the pairing of `g` with the kernel integral `x ↦ ∫ k (x - y) • f y dy` is the
integral of `k (x - y) ⟪g x, f y⟫` over the product (`TauCeti.integral_inner_integral_smul`).
No integrability of `k` itself is needed, so this applies to singular kernels paired against
functions with separated supports.
-/

public section

namespace TauCeti

open MeasureTheory

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
